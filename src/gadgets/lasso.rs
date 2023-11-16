use std::collections::BTreeMap;

use bellpepper_core::{num::AllocatedNum, ConstraintSystem, LinearCombination, SynthesisError};

use crate::constants::NUM_CHALLENGE_BITS;
use crate::gadgets::nonnative::util::Num;
use crate::gadgets::utils::alloc_const;
use crate::traits::{ROCircuitTrait, TranscriptEngineTrait};
use crate::traits::{Group, ROConstantsCircuit};
use ff::{Field};
use crate::spartan::sumcheck::{CompressedUniPoly};
use crate::spartan::polynomial::{EqPolynomial, SparsePolynomial};
use crate::errors::NovaError;

use super::utils::{add_allocated_num, alloc_one, conditionally_select2, le_bits_to_num};

/* There are three main phases of Lasso verification
 Lasso's goal is to prove an opening of the Sparse Matrix Polynomial.
 It does it with:

 1. A primary sum-check.
    M (Indices) . T (Table) = A (lookup results) 
    Check the correctness of A using sum-check.

    P: But M is too big.
    A: turn M into EQ(j,r) . T[NZ_(j)] = A(r)
     EQ(x, e) = (1 if x = e; 0 otherwise.) eq is an MLE.

    P: T might still be too big.
    A: Decompoise T into subtables.
    EQ(j,r) . g(T[NZ_i(j)]...) = a(r)

    NZ_i[J] are turned into MLE DIM_i(j)
    Which is then turned into polynomial
    E_i(j)

 2. (Combined eval proof for E_i(r_z)). 
    E_i = values read from subtable.
    r_z chosen by veritfier over sum-check
    via (DotProductProof).

    dot(x, y) = Σ xi * yi
    Prover convinces Verifier that it knows two vectors x and y,
    for public value v.
    r is where the poly is evaluated.
    let eq = EqPolynomial::new(r.to_vec());
    let (L, R) = eq.compute_factored_evals();
    L and R are x and y in the dot product.

 3. Memory check that uses an adapted GKR protocol.
    P: How do we know that E_i encodes the value reads from Ti.
    A: Use memory checking on E_i/T_i/DIM_i

    Checks E_i, counter_polynomials (read, final), dim_i (chuncked lookup indices)
    Commits to values that make up most of the layers. 
    Does tha13 for values near inputs (most of the gates).
*/


/// Circuit gadget that implements the sumcheck verifier
#[derive(Clone)]
pub struct PrimarySumcheck<G: Group> {
  pub compressed_polys: Vec<CompressedUniPoly<G::Scalar>>,
  pub num_rounds: usize,
  pub degree_bound: usize,
  //pub proof_derefs: CombinedTableEvalProof<G>,
}

#[allow(unused)]
impl<G: Group> PrimarySumcheck<G> {
  fn verify_sumcheck(
    &self,
    claim: G::Scalar,
    transcript: &mut G::TE,
  ) -> Result<(G::Scalar, Vec<G::Scalar>), NovaError>  {
    let mut e = claim;
    let mut r: Vec<G::Scalar> = Vec::new();

    // Check that there is a univariate polynomial for each round
    assert_eq!(self.compressed_polys.len(), self.num_rounds);
    for i in 0..self.compressed_polys.len() {
      let poly = self.compressed_polys[i].decompress(&e);

      // Check degree bound
      assert_eq!(poly.degree(), self.degree_bound);

      // poly(0) + poly(1) = e does not need to be checked as it is checked in decompress.
      debug_assert_eq!(poly.eval_at_zero() + poly.eval_at_one(), e);

      // append the prover's message to the transcript
      transcript.absorb(b"p", &poly);

      // derive the verifier's challenge for the next round
      let r_i = transcript.squeeze(b"c")?;

      r.push(r_i);

      // evaluate the claimed degree-ell polynomial at r_i
      e = poly.evaluate(&r_i);

    }
    Ok((e, r))
  }
}

impl From<NovaError> for SynthesisError {
  fn from(_err: NovaError) -> Self {
     SynthesisError::AssignmentMissing
  }
}

#[derive(Debug, Clone)]
pub struct PolyCommitment<G: Group> {
  poly: Vec<G::Scalar>,
}

#[allow(unused)]
impl<G: Group> PolyCommitment<G> {
  fn append_to_transcript<CS: ConstraintSystem<G::Scalar>>(
    self,
    cs: &mut CS,
    transcript: &mut G::TE   
  ) -> Result<
    (),
    SynthesisError
  > {

    let _commitments: Vec<_> = self.poly.iter()
    .map(|p| {

      transcript.absorb(b"alloc C", p);

      AllocatedNum::alloc(
          cs.namespace(|| "poly commit"),
          || Ok(*p)
      )
      .expect("allocated comm C")

    })
    .collect();

    Ok(())
  }
}

#[derive(Debug, Clone)]
pub struct SparsePolynomialCommitment<G: Group> {
  pub l_variate_polys_commitment: PolyCommitment<G>,
  pub log_m_variate_polys_commitment: PolyCommitment<G>,
  pub sparsity: usize,
  pub log_m: usize,
  pub m: usize,
}

#[allow(unused)]
impl<G: Group> SparsePolynomialCommitment<G> {
  fn append_to_transcript<CS: ConstraintSystem<G::Scalar>>(
    self,
    cs: &mut CS,
    transcript: &mut G::TE   
  ) -> Result<
    (),
    SynthesisError
  > {

    let _commitments_l_v: Vec<_> = self.l_variate_polys_commitment.poly.iter()
    .map(|p| {
      transcript.absorb(b"alloc l_variate_polys_commitment", p);

      AllocatedNum::alloc_input(
          cs.namespace(|| "l_variate_polys_commitment"),
          || Ok(*p)
      )
      .expect("allocated l_variate_polys_commitment")

    })
    .collect();

    let _commitments_log_m: Vec<_> = self.log_m_variate_polys_commitment.poly.iter()
    .map(|p| {
      transcript.absorb(b"alloc log_m_variate_polys_commitment", p);
      
      AllocatedNum::alloc_input(
        cs.namespace(|| "l_variate_polys_commitment"),
          || Ok(*p)
      )
      .expect("allocated l_variate_polys_commitment")

    })
    .collect();

    let alloc_s = AllocatedNum::alloc_input(
      cs.namespace(|| "alloc sparsity"), || Ok(G::Scalar::from(self.sparsity.try_into().unwrap()))
   )?;
    let alloc_log_m = AllocatedNum::alloc_input(
      cs.namespace(|| "alloc log_m"), || Ok(G::Scalar::from(self.log_m.try_into().unwrap()))
   )?;
    let alloc_m = AllocatedNum::alloc_input(
      cs.namespace(|| "alloc m"), || Ok(G::Scalar::from(self.m.try_into().unwrap()))
   )?;

    transcript.absorb(b"sparsity", &alloc_s.get_value().unwrap());
    transcript.absorb(b"log_m", &alloc_log_m.get_value().unwrap());
    transcript.absorb(b"m", &alloc_m.get_value().unwrap());

    Ok(())
  }
}

/*pub struct SparsePolyCommitmentGens<G: Group> {
  pub gens_combined_l_variate: PolyCommitmentGens<G>,
  pub gens_combined_log_m_variate: PolyCommitmentGens<G>,
  pub gens_derefs: PolyCommitmentGens<G>,
}

impl<G: Group> SparsePolyCommitmentGens<G> {
  pub fn new(
    label: &'static [u8],
    c: usize,
    s: usize,
    num_memories: usize,
    log_m: usize,
  ) -> SparsePolyCommitmentGens<G> {
    // dim_1, ... dim_c, read_1, ..., read_c
    // log_2(cs + cs)
    let num_vars_combined_l_variate = (2 * c * s).next_power_of_two().log_2();
    // final
    // log_2(cm) = log_2(c) + log_2(m)
    let num_vars_combined_log_m_variate = c.next_power_of_two().log_2() + log_m;
    // E_1, ..., E_alpha
    // log_2(alpha * s)
    let num_vars_derefs = (num_memories * s).next_power_of_two().log_2();

    let gens_combined_l_variate = PolyCommitmentGens::new(num_vars_combined_l_variate, label);
    let gens_combined_log_m_variate =
      PolyCommitmentGens::new(num_vars_combined_log_m_variate, label);
    let gens_derefs = PolyCommitmentGens::new(num_vars_derefs, label);
    SparsePolyCommitmentGens {
      gens_combined_l_variate,
      gens_combined_log_m_variate,
      gens_derefs,
    }
  }
}*/

/*#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct PolyEvalProof<G: CurveGroup> {
  proof: DotProductProofLog<G>,
}*/

#[derive(Clone)]
pub struct LassoCircuit<G: Group> {
  pub num_cons: usize,
  pub commitment: SparsePolynomialCommitment<G>,
  pub comm_derefs: PolyCommitment<G>,
  pub input: Vec<G::Scalar>,
  pub input_as_sparse_poly: SparsePolynomial<G::Scalar>,
  pub claimed_evaluation: G::Scalar,
  pub subtable_eval_deref: G::Scalar,
  pub primary_sumcheck: PrimarySumcheck<G>,
  // The random points at which the polynomial was evaluated, commited to for the eval checks.
  pub claimed_rz: Vec<G::Scalar>,
  pub eq_randomness: Vec<G::Scalar>,
  pub claimed_transcript_sat_state: G::Scalar,
}

impl<G: Group> LassoCircuit<G> {
  #[allow(unused)]
  pub fn new(config: &VerifierConfig<G>) -> Self {
    Self {
      num_cons: config.num_cons.clone(),
      commitment: 
        SparsePolynomialCommitment { 
          l_variate_polys_commitment: config.commitment.l_variate_polys_commitment.clone(),
          log_m_variate_polys_commitment: config.commitment.log_m_variate_polys_commitment.clone(),
          sparsity: config.commitment.sparsity,
          log_m: config.commitment.log_m,
          m: config.commitment.m,
      },
      comm_derefs: PolyCommitment { 
        poly: config.comm_derefs.poly.clone(),
      },
      input: config.input.clone(),
      input_as_sparse_poly: config.input_as_sparse_poly.clone(),
      claimed_evaluation: config.claimed_evaluation,
      subtable_eval_deref: config.subtable_eval_deref,
      primary_sumcheck: PrimarySumcheck {
        compressed_polys: config.polys_sc1.clone(),
        num_rounds: config.num_rounds,
        degree_bound: config.degree_bound,
      },
      claimed_rz: config.rz.clone(),
      eq_randomness: config.eq_randomness.clone(),
      claimed_transcript_sat_state: config.transcript_sat_state,
    }
  }

  #[allow(unused)]
  pub fn synthesize<CS: ConstraintSystem<G::Scalar>>(
    self,
    cs: &mut CS,
    transcript: &mut G::TE   
  ) -> Result<
    (),
    SynthesisError
  > {

    //START 1. Combined eval proof.

    // Allocate inputs. Non-deterministic choices of the prover (comm_derefs)
    // CombinedTableCommitment in Lasso is a PolyComm.
    let _commitments = self.comm_derefs.append_to_transcript(cs, transcript);

    let _input_vars: Vec<_> = self.input.iter()
    .map(|p| {

      transcript.absorb(b"p", p);

      AllocatedNum::alloc_input(
          cs.namespace(|| "input"),
          || Ok(*p)
      )
      .expect("allocated input")

    })
    .collect();


    //START 2. Primary Sum-check
  
    //allocate input for the challange var.
    let initial_challenge = self.claimed_evaluation;
    let initial_challenge_var = AllocatedNum::alloc_input(
       cs.namespace(|| "initial challenge"), || Ok(initial_challenge)
    )?;

    transcript.absorb(b"initial_challenge_var", &initial_challenge_var.get_value().unwrap());
     
    //allocate poly witness for sum-check
    let _poly_sc1_vars: Vec<_> = self.primary_sumcheck.compressed_polys.iter()
      .map(|p| {
  
        let poly = p.decompress(&initial_challenge);
        poly.coeffs.into_iter().map(|coeff| {
          AllocatedNum::alloc(
             cs.namespace(|| "poly_coeff1"),
             || Ok(coeff)
          )
          .expect("allocated coeff")
        })
        .collect::<Vec<_>>() 
  
      })
      .collect();

    //allocate prover evals z
    let claimed_rz_vars: Vec<_> = self.claimed_rz.iter()
    .map(|p| {

      AllocatedNum::alloc_input(
          cs.namespace(|| "claimed_rz"),
          || Ok(*p)
      )
      .expect("allocated claimed_rz")

    })
    .collect();

    let claim_phase1_var = AllocatedNum::alloc(cs.namespace(|| "claim_phase1_var"), || Ok(initial_challenge))?;

    let result = self.primary_sumcheck.verify_sumcheck(claim_phase1_var.get_value().unwrap(), transcript);
    let (claim_last, rz) = result.map_err(|e| SynthesisError::from(e))?;

    let rz_vars: Vec<_> = rz.iter()
    .map(|p| {

      AllocatedNum::alloc(
          cs.namespace(|| "rz_vars"),
          || Ok(*p)
      )
      .expect("allocated rz_vars")

    })
    .collect();


    // Constraints ensure that this is indeed the result from
    // the round of sumcheck.
    for (i, claimed_rz_var) in claimed_rz_vars.iter().enumerate() {

      cs.enforce(
        || "check rx",
        |lc| lc + rz_vars[i].get_variable(), 
        |lc| lc + claimed_rz_var.get_variable(),
        |lc| lc + CS::one()
      );
    
    }

    // Verify that eq(r, r_z) * g(E_1(r_z) * ... * E_c(r_z)) = claim_last
    let eq_eval = EqPolynomial::new(self.eq_randomness.clone()).evaluate(&rz);
    assert_eq!(
      eq_eval * self.subtable_eval_deref, // combine_lookups function result is given as input (eval_derefs).
      claim_last,
      "Primary sumcheck check failed."
    );

    let _comm_eq_eval = AllocatedNum::alloc(
        cs.namespace(|| "comm eq_eval"), || Ok(eq_eval)
    )?;

    let _comm_subtable_eval_deref = AllocatedNum::alloc_input(
        cs.namespace(|| "comm self.subtable_eval_deref"), || Ok(self.subtable_eval_deref)
    )?;
    
    let comm_eq_equal = AllocatedNum::alloc(
        cs.namespace(|| "comm self.subtable_eval_deref"), || Ok(eq_eval * self.subtable_eval_deref)
    )?;

    let comm_claim_last = AllocatedNum::alloc(
        cs.namespace(|| "comm self.subtable_eval_deref"), || Ok(claim_last)
    )?;

    cs.enforce(
      || "verify eq",
      |lc| lc + comm_claim_last.get_variable(), 
      |lc| lc + comm_eq_equal.get_variable(),
      |lc| lc + CS::one()
    );

    // END Primary Sum-check CONTINUE EVAL PROOF

    /*self.primary_sumcheck.proof_derefs.verify(
      &rz,
      &self.subtable_eval_deref,
      &gens.gens_derefs,
      &self.comm_derefs,
      transcript,
    )?;*/


    // 3. START MEM-CHECK

    let expected_transcript_state_var = AllocatedNum::alloc(
      cs.namespace(|| "expected_claim_post_phase2_var"), || Ok(transcript.squeeze(b"fin")?)
    )?;
    let claimed_transcript_state_var = AllocatedNum::alloc_input(
      cs.namespace(|| "claimed_transcript_state_var"), || Ok(self.claimed_transcript_sat_state)
    )?;

    cs.enforce(
      || "check transcripts",
      |lc| lc + expected_transcript_state_var.get_variable(), 
      |lc| lc + claimed_transcript_state_var.get_variable(),
      |lc| lc + CS::one()
    );

    Ok(())
    
  }
}

#[derive(Clone)]
pub struct VerifierConfig<G: Group> {
  pub num_rounds: usize,
  pub num_cons: usize,
  pub commitment: SparsePolynomialCommitment<G>,
  pub comm_derefs: PolyCommitment<G>,
  pub degree_bound: usize,
  pub input: Vec<G::Scalar>,
  pub input_as_sparse_poly: SparsePolynomial<G::Scalar>,
  pub claimed_evaluation: G::Scalar,
  pub subtable_eval_deref: G::Scalar,
  pub polys_sc1: Vec<CompressedUniPoly<G::Scalar>>,
  pub rz: Vec<G::Scalar>,
  pub eq_randomness: Vec<G::Scalar>,
  pub transcript_sat_state: G::Scalar,
  pub log_m_variate_polys_commitment: PolyCommitment<G>,
  pub l_variate_polys_commitment: PolyCommitment<G>,
  pub sparsity: usize,
  pub log_m: usize,
  pub s: usize,
}

/// rw trace
pub enum RWTrace<G: Group> {
  /// read
  Read(AllocatedNum<G::Base>, AllocatedNum<G::Base>),
  /// write
  Write(AllocatedNum<G::Base>, AllocatedNum<G::Base>),
}

/// for starting a transaction
pub struct LassoTransaction<'a, G: Group> {
  lookup: &'a mut Lookup<G>,
  rw_trace: Vec<RWTrace<G>>,
  map_aux: BTreeMap<G::Base, (G::Base, G::Base)>,
}

impl<'a, G: Group> LassoTransaction<'a, G> {
  fn start_transaction(lookup: &'a mut Lookup<G>) -> LassoTransaction<'a, G> {
    LassoTransaction {
      lookup,
      rw_trace: vec![],
      map_aux: BTreeMap::new(),
    }
  }

  fn read<CS: ConstraintSystem<<G as Group>::Base>>(
    &mut self,
    mut cs: CS,
    addr: &AllocatedNum<G::Base>,
  ) -> Result<AllocatedNum<G::Base>, SynthesisError>
  where
    <G as Group>::Base: std::cmp::Ord,
  {
    let key = &addr.get_value().unwrap();
    let (value, _) = self.map_aux.entry(*key).or_insert_with(|| {
      self
        .lookup
        .map_aux
        .get(key)
        .cloned()
        .unwrap_or_else(|| (G::Base::from(0), G::Base::from(0)))
    });
    let read_value = AllocatedNum::alloc(cs.namespace(|| "read_value"), || Ok(*value))?;
    self
      .rw_trace
      .push(RWTrace::Read(addr.clone(), read_value.clone())); // append read trace
    Ok(read_value)
  }

  fn write(
    &mut self,
    addr: &AllocatedNum<G::Base>,
    value: &AllocatedNum<G::Base>,
  ) -> Result<(), SynthesisError>
  where
    <G as Group>::Base: std::cmp::Ord,
  {
    let _ = self.map_aux.insert(
      addr.get_value().ok_or(SynthesisError::AssignmentMissing)?,
      (
        value.get_value().ok_or(SynthesisError::AssignmentMissing)?,
        G::Base::ZERO, // zero counter doens't matter, real counter will be computed inside lookup table
      ),
    );
    self
      .rw_trace
      .push(RWTrace::Write(addr.clone(), value.clone())); // append read trace
    Ok(())
  }

  /// commit rw_trace to lookup
  fn commit<CS: ConstraintSystem<<G as Group>::Base>>(
    &mut self,
    mut cs: CS,
    ro_const: ROConstantsCircuit<G>,
    prev_intermediate_gamma: &AllocatedNum<G::Base>,
    gamma: &AllocatedNum<G::Base>,
    prev_R: &AllocatedNum<G::Base>,
    prev_W: &AllocatedNum<G::Base>,
    prev_rw_counter: &AllocatedNum<G::Base>,
  ) -> Result<
    (
      AllocatedNum<G::Base>,
      AllocatedNum<G::Base>,
      AllocatedNum<G::Base>,
      AllocatedNum<G::Base>,
    ),
    SynthesisError,
  >
  where
    <G as Group>::Base: std::cmp::Ord,
  {
    // let ro_consts1: ROConstantsCircuit<PastaG2> = PoseidonConstantsCircuit::new();
    let mut ro = G::ROCircuit::new(
      ro_const,
      1 + 3 * self.rw_trace.len(), // claimed_evaluation + [(address, value, counter)]
    );
    ro.absorb(prev_intermediate_gamma);
    let (next_R, next_W, next_rw_counter) = self.rw_trace.iter().enumerate().try_fold(
      (prev_R.clone(), prev_W.clone(), prev_rw_counter.clone()),
      |(prev_R, prev_W, prev_rw_counter), (i, rwtrace)| match rwtrace {
        RWTrace::Read(addr, read_value) => {
          let (next_R, next_W, next_rw_counter) = self.lookup.read(
            cs.namespace(|| format!("{}th read ", i)),
            true,
            &mut ro,
            &addr,
            gamma,
            &read_value,
            &prev_R,
            &prev_W,
            &prev_rw_counter,
          )?;
          Ok::<
            (
              AllocatedNum<G::Base>,
              AllocatedNum<G::Base>,
              AllocatedNum<G::Base>,
            ),
            SynthesisError,
          >((next_R, next_W, next_rw_counter))
        }
        RWTrace::Write(addr, read_value) => {
          let (next_R, next_W, next_rw_counter) = self.lookup.read(
            cs.namespace(|| format!("{}th write ", i)),
            false,
            &mut ro,
            &addr,
            gamma,
            &read_value,
            &prev_R,
            &prev_W,
            &prev_rw_counter,
          )?;
          Ok::<
            (
              AllocatedNum<G::Base>,
              AllocatedNum<G::Base>,
              AllocatedNum<G::Base>,
            ),
            SynthesisError,
          >((next_R, next_W, next_rw_counter))
        }
      },
    )?;
    let hash_bits = ro.squeeze(cs.namespace(|| "challenge"), NUM_CHALLENGE_BITS)?;
    let hash = le_bits_to_num(cs.namespace(|| "bits to hash"), &hash_bits)?;
    Ok((next_R, next_W, next_rw_counter, hash))
  }
}

/// Lookup in R1CS
pub struct Lookup<G: Group> {
  pub(crate) map_aux: BTreeMap<<G as Group>::Base, (<G as Group>::Base, <G as Group>::Base)>, // (value, counter)
  /// map_aux_dirty only include the modified fields of `map_aux`, thats why called dirty
  map_aux_dirty: BTreeMap<G::Base, (G::Base, G::Base)>, // (value, counter)
  rw_counter: G::Base,
  rw: bool, // read only or read-write
}

impl<G: Group> Lookup<G> {
  fn new(rw: bool, initial_table: Vec<(G::Base, G::Base)>) -> Lookup<G>
  where
    <G as Group>::Base: std::cmp::Ord,
  {
    Self {
      map_aux: initial_table
        .into_iter()
        .map(|(addr, value)| (addr, (value, G::Base::ZERO)))
        .collect(),
      map_aux_dirty: BTreeMap::new(),
      rw_counter: G::Base::ZERO,
      rw,
    }
  }

  fn read<CS: ConstraintSystem<<G as Group>::Base>>(
    &mut self,
    mut cs: CS,
    is_read: bool,
    ro: &mut G::ROCircuit,
    addr: &AllocatedNum<G::Base>,
    // challenges: &(AllocatedNum<G::Base>, AllocatedNum<G::Base>),
    gamma: &AllocatedNum<G::Base>,
    external_value: &AllocatedNum<G::Base>,
    prev_R: &AllocatedNum<G::Base>,
    prev_W: &AllocatedNum<G::Base>,
    prev_rw_counter: &AllocatedNum<G::Base>,
  ) -> Result<
    (
      AllocatedNum<G::Base>,
      AllocatedNum<G::Base>,
      AllocatedNum<G::Base>,
    ),
    SynthesisError,
  >
  where
    <G as Group>::Base: std::cmp::Ord,
  {
    // extract challenge
    // get content from map
    // value are provided beforehand from outside, therefore here just constraints it
    let (_read_value, _read_counter) = self
      .map_aux
      .get(&addr.get_value().unwrap())
      .cloned()
      .unwrap_or((G::Base::from(0), G::Base::from(0)));

    let counter = AllocatedNum::alloc(cs.namespace(|| "counter"), || Ok(_read_counter))?;

    // external_read_value should match with _read_value
    if is_read {
      if let Some(external_read_value) = external_value.get_value() {
        assert_eq!(external_read_value, _read_value)
      }
    };

    // external_read_value should match with rw_counter witness
    if let Some(external_rw_counter) = prev_rw_counter.get_value() {
      assert_eq!(external_rw_counter, self.rw_counter)
    }

    let one = <G as Group>::Base::ONE;
    let neg_one = one.invert().unwrap();

    // update R
    let gamma_square = gamma.mul(cs.namespace(|| "gamme^2"), gamma)?;
    // read_value_term = gamma * value
    let read_value = if is_read {
      external_value.clone()
    } else {
      AllocatedNum::alloc(cs.namespace(|| "read_value"), || Ok(_read_value))?
    };
    let read_value_term = gamma.mul(cs.namespace(|| "read_value_term"), &read_value)?;
    // counter_term = gamma^2 * counter
    let counter_term = gamma_square.mul(cs.namespace(|| "second_term"), &counter)?;
    // new_R = R * (gamma - (addr + gamma * value + gamma^2 * counter))
    let new_R = AllocatedNum::alloc(cs.namespace(|| "new_R"), || {
      prev_R
        .get_value()
        .zip(gamma.get_value())
        .zip(addr.get_value())
        .zip(read_value_term.get_value())
        .zip(counter_term.get_value())
        .map(|((((R, gamma), addr), value_term), counter_term)| {
          R * (gamma - (addr + value_term + counter_term))
        })
        .ok_or(SynthesisError::AssignmentMissing)
    })?;
    let mut r_blc = LinearCombination::<G::Base>::zero();
    r_blc = r_blc
      + (one, gamma.get_variable())
      + (neg_one, addr.get_variable())
      + (neg_one, read_value_term.get_variable())
      + (neg_one, counter_term.get_variable());
    cs.enforce(
      || "R update",
      |lc| lc + (one, prev_R.get_variable()),
      |_| r_blc,
      |lc| lc + (one, new_R.get_variable()),
    );

    // RO to get challenge
    // where the input only cover
    ro.absorb(addr);
    ro.absorb(&read_value);
    ro.absorb(&counter);

    let alloc_num_one = alloc_one(cs.namespace(|| "one"))?;

    // max{c, ts} + 1 logic on read-write lookup
    // c + 1 on read-only
    let (write_counter, write_counter_term) = if self.rw {
      // write_counter = read_counter < prev_rw_counter ? prev_rw_counter: read_counter
      // TODO optimise with `max` table lookup to save more constraints
      let lt = less_than::<G, _>(
        cs.namespace(|| "read_counter < a"),
        &counter,
        prev_rw_counter,
        12, // TODO configurable n_bit
      )?;
      let write_counter = conditionally_select2(
        cs.namespace(|| {
          "write_counter = read_counter < prev_rw_counter ? prev_rw_counter: read_counter"
        }),
        prev_rw_counter,
        &counter,
        &lt,
      )?;
      let write_counter_term =
        gamma_square.mul(cs.namespace(|| "write_counter_term"), &write_counter)?;
      (write_counter, write_counter_term)
    } else {
      (counter, counter_term)
    };

    // update W
    // write_value_term = gamma * value
    let write_value_term = if is_read {
      read_value_term
    } else {
      gamma.mul(cs.namespace(|| "write_value_term"), external_value)?
    };
    let new_W = AllocatedNum::alloc(cs.namespace(|| "new_W"), || {
      prev_W
        .get_value()
        .zip(gamma.get_value())
        .zip(addr.get_value())
        .zip(write_value_term.get_value())
        .zip(write_counter_term.get_value())
        .zip(gamma_square.get_value())
        .map(
          |(((((W, gamma), addr), value_term), write_counter_term), gamma_square)| {
            W * (gamma - (addr + value_term + write_counter_term + gamma_square))
          },
        )
        .ok_or(SynthesisError::AssignmentMissing)
    })?;
    // new_W = W * (gamma - (addr + gamma * value + gamma^2 * counter + gamma^2)))
    let mut w_blc = LinearCombination::<G::Base>::zero();
    w_blc = w_blc
      + (one, gamma.get_variable())
      + (neg_one, addr.get_variable())
      + (neg_one, write_value_term.get_variable())
      + (neg_one, write_counter_term.get_variable())
      + (neg_one, gamma_square.get_variable());
    cs.enforce(
      || "W update",
      |lc| lc + (one, prev_W.get_variable()),
      |_| w_blc,
      |lc| lc + (one, new_W.get_variable()),
    );

    // update witness
    self.map_aux.insert(
      addr.get_value().unwrap(),
      (
        external_value.get_value().unwrap_or_default(),
        write_counter.get_value().unwrap() + one,
      ),
    );
    self.map_aux_dirty.insert(
      addr.get_value().unwrap(),
      (
        external_value.get_value().unwrap_or_default(),
        write_counter.get_value().unwrap() + one,
      ),
    );
    let new_rw_counter = add_allocated_num(
      cs.namespace(|| "new_rw_counter"),
      &write_counter,
      &alloc_num_one,
    )?;
    if let Some(new_rw_counter) = new_rw_counter.get_value() {
      self.rw_counter = new_rw_counter;
    }
    Ok((new_R, new_W, new_rw_counter))
  }

  // fn write(&mut self, addr: AllocatedNum<F>, value: F) {}
}

// a < b ? 1 : 0
fn less_than<G: Group, CS: ConstraintSystem<G::Base>>(
  mut cs: CS,
  a: &AllocatedNum<G::Base>,
  b: &AllocatedNum<G::Base>,
  n_bits: usize,
) -> Result<AllocatedNum<G::Base>, SynthesisError>
where
  <G as Group>::Base: PartialOrd,
{
  assert!(n_bits < 64, "not support n_bits {n_bits} >= 64");
  let range = alloc_const(
    cs.namespace(|| "range"),
    G::Base::from(2_usize.pow(n_bits as u32) as u64),
  )?;
  let diff = Num::alloc(cs.namespace(|| "diff"), || {
    a.get_value()
      .zip(b.get_value())
      .zip(range.get_value())
      .map(|((a, b), range)| {
        let lt = a < b;
        (a - b) + (if lt { range } else { G::Base::ZERO })
      })
      .ok_or(SynthesisError::AssignmentMissing)
  })?;
  diff.fits_in_bits(cs.namespace(|| "diff fit in bits"), n_bits)?;
  let lt = AllocatedNum::alloc(cs.namespace(|| "lt"), || {
    a.get_value()
      .zip(b.get_value())
      .map(|(a, b)| G::Base::from((a < b) as u64))
      .ok_or(SynthesisError::AssignmentMissing)
  })?;
  cs.enforce(
    || "lt is bit",
    |lc| lc + lt.get_variable(),
    |lc| lc + CS::one() - lt.get_variable(),
    |lc| lc,
  );
  cs.enforce(
    || "lt ⋅ range == diff - lhs + rhs",
    |lc| lc + lt.get_variable(),
    |lc| lc + range.get_variable(),
    |_| diff.num + (G::Base::ONE.invert().unwrap(), a.get_variable()) + b.get_variable(),
  );
  Ok(lt)
}

#[cfg(test)]
mod test {
  use crate::{
    // bellpepper::test_shape_cs::TestShapeCS,
    constants::NUM_CHALLENGE_BITS,
    gadgets::{
      lasso::LassoTransaction,
      utils::{alloc_one, alloc_zero, scalar_as_base},
    },
    provider::poseidon::PoseidonConstantsCircuit,
    traits::{Group, ROConstantsCircuit},
  };
  use ff::Field;

  use super::Lookup;
  use crate::traits::ROConstantsTrait;
  use crate::traits::ROTrait;
  use bellpepper_core::{num::AllocatedNum, test_cs::TestConstraintSystem, ConstraintSystem};

  #[test]
  fn test_read_twice_on_readonly() {
    type G1 = pasta_curves::pallas::Point;
    type G2 = pasta_curves::vesta::Point;

    let ro_consts: ROConstantsCircuit<G2> = PoseidonConstantsCircuit::new();

    let mut cs = TestConstraintSystem::<<G1 as Group>::Scalar>::new();
    // let mut cs: TestShapeCS<G1> = TestShapeCS::new();
    let initial_table = vec![
      (
        <G1 as Group>::Scalar::ZERO,
        <G1 as Group>::Scalar::from(101),
      ),
      (<G1 as Group>::Scalar::ONE, <G1 as Group>::Scalar::ZERO),
    ];
    let mut lookup = Lookup::<G2>::new(false, initial_table);
    let mut lookup_transaction = LassoTransaction::start_transaction(&mut lookup);
    let gamma = AllocatedNum::alloc(cs.namespace(|| "gamma"), || {
      Ok(<G1 as Group>::Scalar::from(2))
    })
    .unwrap();
    let zero = alloc_zero(cs.namespace(|| "zero")).unwrap();
    let one = alloc_one(cs.namespace(|| "one")).unwrap();
    let prev_intermediate_gamma = &one;
    let prev_rw_counter = &zero;
    let addr = zero.clone();
    let read_value = lookup_transaction
      .read(cs.namespace(|| "read_value1"), &addr)
      .unwrap();
    assert_eq!(
      read_value.get_value(),
      Some(<G1 as Group>::Scalar::from(101))
    );
    let read_value = lookup_transaction
      .read(cs.namespace(|| "read_value2"), &addr)
      .unwrap();
    assert_eq!(
      read_value.get_value(),
      Some(<G1 as Group>::Scalar::from(101))
    );
    let (prev_W, prev_R) = (&one, &one);
    let (next_R, next_W, next_rw_counter, next_intermediate_gamma) = lookup_transaction
      .commit(
        cs.namespace(|| "commit"),
        ro_consts.clone(),
        prev_intermediate_gamma,
        &gamma,
        prev_W,
        prev_R,
        prev_rw_counter,
      )
      .unwrap();
    assert_eq!(
      next_rw_counter.get_value(),
      Some(<G1 as Group>::Scalar::from(2))
    );
    // next_R check
    assert_eq!(
      next_R.get_value(),
      prev_R
        .get_value()
        .zip(gamma.get_value())
        .zip(addr.get_value())
        .zip(read_value.get_value())
        .map(|(((prev_R, gamma), addr), read_value)| prev_R
          * (gamma - (addr + gamma * read_value + gamma * gamma * <G1 as Group>::Scalar::ZERO))
          * (gamma - (addr + gamma * read_value + gamma * gamma * <G1 as Group>::Scalar::ONE)))
    );
    // next_W check
    assert_eq!(
      next_W.get_value(),
      prev_W
        .get_value()
        .zip(gamma.get_value())
        .zip(addr.get_value())
        .zip(read_value.get_value())
        .map(|(((prev_W, gamma), addr), read_value)| {
          prev_W
            * (gamma - (addr + gamma * read_value + gamma * gamma * (<G1 as Group>::Scalar::ONE)))
            * (gamma
              - (addr + gamma * read_value + gamma * gamma * (<G1 as Group>::Scalar::from(2))))
        }),
    );

    let mut hasher = <G2 as Group>::RO::new(ro_consts, 7);
    hasher.absorb(prev_intermediate_gamma.get_value().unwrap());
    hasher.absorb(addr.get_value().unwrap());
    hasher.absorb(read_value.get_value().unwrap());
    hasher.absorb(<G1 as Group>::Scalar::ZERO);
    hasher.absorb(addr.get_value().unwrap());
    hasher.absorb(read_value.get_value().unwrap());
    hasher.absorb(<G1 as Group>::Scalar::ONE);
    let res = hasher.squeeze(NUM_CHALLENGE_BITS);
    assert_eq!(
      scalar_as_base::<G2>(res),
      next_intermediate_gamma.get_value().unwrap()
    );
    // TODO check rics is_sat
    // let (_, _) = cs.r1cs_shape_with_commitmentkey();
    // let (U1, W1) = cs.r1cs_instance_and_witness(&shape, &ck).unwrap();

    // // Make sure that the first instance is satisfiable
    // assert!(shape.is_sat(&ck, &U1, &W1).is_ok());
  }

  #[test]
  fn test_write_read_on_rwlookup() {
    type G1 = pasta_curves::pallas::Point;
    type G2 = pasta_curves::vesta::Point;

    let ro_consts: ROConstantsCircuit<G2> = PoseidonConstantsCircuit::new();

    let mut cs = TestConstraintSystem::<<G1 as Group>::Scalar>::new();
    // let mut cs: TestShapeCS<G1> = TestShapeCS::new();
    let initial_table = vec![
      (<G1 as Group>::Scalar::ZERO, <G1 as Group>::Scalar::ZERO),
      (<G1 as Group>::Scalar::ONE, <G1 as Group>::Scalar::ZERO),
    ];
    let mut lookup = Lookup::<G2>::new(true, initial_table);
    let mut lookup_transaction = LassoTransaction::start_transaction(&mut lookup);
    let gamma = AllocatedNum::alloc(cs.namespace(|| "gamma"), || {
      Ok(<G1 as Group>::Scalar::from(2))
    })
    .unwrap();
    let zero = alloc_zero(cs.namespace(|| "zero")).unwrap();
    let one = alloc_one(cs.namespace(|| "one")).unwrap();
    let prev_intermediate_gamma = &one;
    let prev_rw_counter = &zero;
    let addr = zero.clone();
    lookup_transaction
      .write(
        &addr,
        &AllocatedNum::alloc(cs.namespace(|| "write value 1"), || {
          Ok(<G1 as Group>::Scalar::from(101))
        })
        .unwrap(),
      )
      .unwrap();
    let read_value = lookup_transaction
      .read(cs.namespace(|| "read_value 1"), &addr)
      .unwrap();
    assert_eq!(
      read_value.get_value(),
      Some(<G1 as Group>::Scalar::from(101))
    );
    let (prev_W, prev_R) = (&one, &one);
    let (next_R, next_W, next_rw_counter, next_intermediate_gamma) = lookup_transaction
      .commit(
        cs.namespace(|| "commit"),
        ro_consts.clone(),
        prev_intermediate_gamma,
        &gamma,
        prev_W,
        prev_R,
        prev_rw_counter,
      )
      .unwrap();
    assert_eq!(
      next_rw_counter.get_value(),
      Some(<G1 as Group>::Scalar::from(2))
    );
    // next_R check
    assert_eq!(
      next_R.get_value(),
      prev_R
        .get_value()
        .zip(gamma.get_value())
        .zip(addr.get_value())
        .zip(read_value.get_value())
        .map(|(((prev_R, gamma), addr), read_value)| prev_R
          * (gamma
            - (addr
              + gamma * <G1 as Group>::Scalar::ZERO
              + gamma * gamma * <G1 as Group>::Scalar::ZERO))
          * (gamma - (addr + gamma * read_value + gamma * gamma * <G1 as Group>::Scalar::ONE)))
    );
    // next_W check
    assert_eq!(
      next_W.get_value(),
      prev_W
        .get_value()
        .zip(gamma.get_value())
        .zip(addr.get_value())
        .zip(read_value.get_value())
        .map(|(((prev_W, gamma), addr), read_value)| {
          prev_W
            * (gamma - (addr + gamma * read_value + gamma * gamma * (<G1 as Group>::Scalar::ONE)))
            * (gamma
              - (addr + gamma * read_value + gamma * gamma * (<G1 as Group>::Scalar::from(2))))
        }),
    );

    let mut hasher = <G2 as Group>::RO::new(ro_consts, 7);
    hasher.absorb(prev_intermediate_gamma.get_value().unwrap());
    hasher.absorb(addr.get_value().unwrap());
    hasher.absorb(<G1 as Group>::Scalar::ZERO);
    hasher.absorb(<G1 as Group>::Scalar::ZERO);
    hasher.absorb(addr.get_value().unwrap());
    hasher.absorb(read_value.get_value().unwrap());
    hasher.absorb(<G1 as Group>::Scalar::ONE);
    let res = hasher.squeeze(NUM_CHALLENGE_BITS);
    assert_eq!(
      scalar_as_base::<G2>(res),
      next_intermediate_gamma.get_value().unwrap()
    );
    // TODO check rics is_sat
    // let (_, _) = cs.r1cs_shape_with_commitmentkey();
    // let (U1, W1) = cs.r1cs_instance_and_witness(&shape, &ck).unwrap();

    // // Make sure that the first instance is satisfiable
    // assert!(shape.is_sat(&ck, &U1, &W1).is_ok());
  }
}