//! This module defines CCS related types and functions.
#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(clippy::type_complexity)]

use crate::{
  constants::{BN_LIMB_WIDTH, BN_N_LIMBS, NUM_FE_FOR_RO, NUM_HASH_BITS},
  errors::NovaError,
  gadgets::{
    nonnative::{bignat::nat_to_limbs, util::f_to_nat},
    utils::scalar_as_base,
  },
  r1cs::{R1CSInstance, R1CSShape, R1CSWitness, R1CS},
  traits::{
    commitment::CommitmentEngineTrait, commitment::CommitmentTrait, AbsorbInROTrait, Group, ROTrait,
  },
  utils::*,
  Commitment, CommitmentKey, CE,
};
use bitvec::vec;
use core::{cmp::max, marker::PhantomData};
use ff::Field;
use flate2::{write::ZlibEncoder, Compression};
use itertools::{concat, Itertools};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use sha3::{Digest, Sha3_256};

// TODO, based on r1cs.rs:
// x CCS struct
// x CCS basic impl
// x CCS basic is_sat
// - Clean up old R1CS stuff we don't need
// x Get rid of hardcoded R1CS
// - Linearized/Committed CCS
// - R1CS to CCS

/// Public parameters for a given CCS
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct CCS<G: Group> {
  _p: PhantomData<G>,
}

/// Set of parameters that defines a [CCSInstance](CCSInstance) characteristic shape parameters.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Shape {
  /// Number of constraints.
  pub(crate) m: usize,
  /// Number of columns of the matrixes.
  pub(crate) n: usize,
  /// Size of the public input vector.
  pub(crate) l: usize,
  /// Number of variables in the multivariate polynomial `g`.
  pub(crate) t: usize,
  /// Number of monomials in the multivariate polynomial `g`.
  pub(crate) q: usize,
  /// Max degree among any of the monomials in `g`.
  pub(crate) d: usize,
  /// Number of selectors (only relevant to plonkish).
  pub(crate) e: usize,
}

/// CCS Instance data. This structure contains all the actual data needed to represent a full CCS Instance.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CCSInstance<G: Group> {
  /// Shape of the CCS Instance
  pub(crate) shape: Shape,
  /// Vector of matrixes `M` that define the CCS constraints.
  pub(crate) M: Vec<Vec<(usize, usize, G::Scalar)>>,
  /// A sequence of multisets of domain `t-1`.
  pub(crate) S: Vec<Vec<usize>>,
  /// A collection of constants
  pub(crate) c: Vec<isize>,
  /// Witness of the CCS Instance.
  pub(crate) w: Vec<G::Scalar>,
  /// Public IO vector of the CCS instance.
  pub(crate) x: Vec<G::Scalar>,
}

// TODO: Type for other CCS types, eqv to RelaxedR1CS

// TODO: Update variables here? This is currently based on R1CS with M length, not sanity checked
// impl<G: Group> CCS<G> {
//   /// Samples public parameters for the specified number of constraints and variables in an CCS
//   pub fn commitment_key(S: &CCSShape<G>) -> CommitmentKey<G> {
//     let num_cons = S.num_cons;
//     let num_vars = S.num_vars;
//     let total_nz = S.M.iter().fold(0, |acc, m| acc + m.len());

//     G::CE::setup(b"ck", max(max(num_cons, num_vars), total_nz))
//   }
// }

// TODO: Util fn to create new CCSShape for R1CS with following values
// n=n, m=m, N=N, l=l, t=3, q=2, d=2
// M={A,B,C}, S={{0, 1}, {2}}, c={1,−1}

impl<G: Group> CCSInstance<G> {
  /// Create an object of type [`CCSInstance`] from the given R1CS instance.
  pub fn from_r1cs(
    shape: R1CSShape<G>,
    instance: R1CSWitness<G>,
    io: R1CSInstance<G>,
  ) -> Result<CCSInstance<G>, NovaError> {
    // We know that when porting an R1CS instance to a CCS one, some values are already set.
    // For instance:
    // - $t$ = 3
    // - $q$ = 2
    // - $d$ = 2
    // - $\vec{M}$ = $[M_A, M_B, M_C]$ (R1CS matrices A, B and C)
    // - $\vec{\mathbb{S}}$ = $[S_0 = \{0,1\}, S_1 = \{2\}]$
    // - $\vec{c}$ = $\{c_0=1, c_1=-1\}$

    let last_items = [&shape.A, &shape.B, &shape.C]
      .iter()
      .map(|matrix| matrix.last().ok_or(NovaError::InvalidInputLength))
      .map_results(|last| (last.0, last.1))
      .collect::<Result<Vec<(usize, usize)>, NovaError>>()?;

    // Sanity check for matrix input consistency
    assert_eq!(last_items[0], last_items[1]);
    assert_eq!(last_items[2], last_items[1]);

    let (m, n) = last_items[0];
    let w = instance.W;
    let x = io.X;

    Ok(CCSInstance {
      shape: Shape {
        m,
        n,
        l: x.len(),
        t: 3,
        q: 2,
        d: 2,
        e: 0,
      },
      M: vec![shape.A, shape.B, shape.C],
      S: vec![vec![0, 1], vec![2]],
      c: vec![1, -1],
      w,
      x,
    })
  }
}

#[cfg(test)]
pub mod test {
  use super::*;
  use crate::{
    r1cs::R1CS,
    traits::{Group, ROConstantsTrait},
  };
  use ::bellperson::{gadgets::num::AllocatedNum, ConstraintSystem, SynthesisError};
  use ff::{Field, PrimeField};
  use rand::rngs::OsRng;

  type S = pasta_curves::pallas::Scalar;
  type G = pasta_curves::pallas::Point;

  #[test]
  fn test_tiny_ccs() {
    // 1. Generate valid R1CS Shape
    // 2. Convert to CCS
    // 3. Test that it is satisfiable

    let one = S::one();
    let (num_cons, num_vars, num_io, A, B, C) = {
      let num_cons = 4;
      let num_vars = 4;
      let num_io = 2;

      // Consider a cubic equation: `x^3 + x + 5 = y`, where `x` and `y` are respectively the input and output.
      // The R1CS for this problem consists of the following constraints:
      // `I0 * I0 - Z0 = 0`
      // `Z0 * I0 - Z1 = 0`
      // `(Z1 + I0) * 1 - Z2 = 0`
      // `(Z2 + 5) * 1 - I1 = 0`

      // Relaxed R1CS is a set of three sparse matrices (A B C), where there is a row for every
      // constraint and a column for every entry in z = (vars, u, inputs)
      // An R1CS instance is satisfiable iff:
      // Az \circ Bz = u \cdot Cz + E, where z = (vars, 1, inputs)
      let mut A: Vec<(usize, usize, S)> = Vec::new();
      let mut B: Vec<(usize, usize, S)> = Vec::new();
      let mut C: Vec<(usize, usize, S)> = Vec::new();

      // constraint 0 entries in (A,B,C)
      // `I0 * I0 - Z0 = 0`
      A.push((0, num_vars + 1, one));
      B.push((0, num_vars + 1, one));
      C.push((0, 0, one));

      // constraint 1 entries in (A,B,C)
      // `Z0 * I0 - Z1 = 0`
      A.push((1, 0, one));
      B.push((1, num_vars + 1, one));
      C.push((1, 1, one));

      // constraint 2 entries in (A,B,C)
      // `(Z1 + I0) * 1 - Z2 = 0`
      A.push((2, 1, one));
      A.push((2, num_vars + 1, one));
      B.push((2, num_vars, one));
      C.push((2, 2, one));

      // constraint 3 entries in (A,B,C)
      // `(Z2 + 5) * 1 - I1 = 0`
      A.push((3, 2, one));
      A.push((3, num_vars, one + one + one + one + one));
      B.push((3, num_vars, one));
      C.push((3, num_vars + 2, one));

      (num_cons, num_vars, num_io, A, B, C)
    };

    // create a R1CS shape object
    let S = {
      let res = R1CSShape::new(num_cons, num_vars, num_io, &A, &B, &C);
      assert!(res.is_ok());
      res.unwrap()
    };

    // 2. Take R1CS and convert to CCS
    let S = CCSShape::from_r1cs(S);

    // generate generators and ro constants
    let _ck = CCS::<G>::commitment_key(&S);
    let _ro_consts =
      <<G as Group>::RO as ROTrait<<G as Group>::Base, <G as Group>::Scalar>>::Constants::new();

    // 3. Test that CCS is satisfiable
    let _rand_inst_witness_generator =
      |ck: &CommitmentKey<G>, I: &S| -> (S, CCSInstance<G>, CCSWitness<G>) {
        let i0 = *I;

        // compute a satisfying (vars, X) tuple
        let (O, vars, X) = {
          let z0 = i0 * i0; // constraint 0
          let z1 = i0 * z0; // constraint 1
          let z2 = z1 + i0; // constraint 2
          let i1 = z2 + one + one + one + one + one; // constraint 3

          // store the witness and IO for the instance
          let W = vec![z0, z1, z2, S::zero()];
          let X = vec![i0, i1];
          (i1, W, X)
        };

        let W = {
          let res = CCSWitness::new(&S, &vars);
          assert!(res.is_ok());
          res.unwrap()
        };
        let U = {
          let comm_W = W.commit(ck);
          let res = CCSInstance::new(&S, &comm_W, &X);
          assert!(res.is_ok());
          res.unwrap()
        };

        // check that generated instance is satisfiable
        assert!(S.is_sat(ck, &U, &W).is_ok());

        (O, U, W)
      };
  }
}
