//! This module is an adaptation of code from the Lasso crate.
//! See NOTICE.md for more details
use super::bullet::BulletReductionProof;
use super::commitments::{Commitments, MultiCommitGens};

use crate::{
  errors::NovaError,
  spartan::{
    math::Math,
  },
  traits::{TranscriptEngineTrait, Group}
};

#[derive(Debug)]
#[allow(unused)]
pub struct DotProductProof<G: Group> {
  delta: G,
  beta: G,
  z: Vec<G::Scalar>,
  z_delta: G::Scalar,
  z_beta: G::Scalar,
}

impl<G: Group> DotProductProof<G> {

  pub fn compute_dotproduct(a: &[G::Scalar], b: &[G::Scalar]) -> G::Scalar {
    assert_eq!(a.len(), b.len());
    (0..a.len()).map(|i| a[i] * b[i]).sum()
  }

  #[allow(dead_code)]
  pub fn prove(
    gens_1: &MultiCommitGens<G>,
    gens_n: &MultiCommitGens<G>,
    transcript: &mut G::TE,
    x_vec: &[G::Scalar],
    blind_x: &G::Scalar,
    a_vec: &[G::Scalar],
    y: &G::Scalar,
    blind_y: &G::Scalar,
  ) -> Result<(Self, G, G), NovaError> {

    assert_eq!(x_vec.len(), a_vec.len());
    assert_eq!(gens_n.n, a_vec.len());
    assert_eq!(gens_1.n, 1);

    let mut d_vec = Vec::new();

    for _x in x_vec {
      d_vec.push(transcript.squeeze(b"d_vec")?);
    }

    let r_delta = transcript.squeeze(b"r_delta")?;
    let r_beta = transcript.squeeze(b"r_beta")?;

    let Cx = Commitments::batch_commit(x_vec, blind_x, gens_n);
    //transcript.absorb(b"Cx", &Cx);

    let Cy = y.commit(blind_y, gens_1);
    //transcript.absorb(b"Cy", &Cy);
    
    for sub_a in a_vec {
      transcript.absorb(b"a", sub_a);
    }
  
    let delta = Commitments::batch_commit(&d_vec, &r_delta, gens_n);
    //transcript.absorb(b"delta", &delta);

    let dotproduct_a_d = DotProductProof::<G>::compute_dotproduct(a_vec, &d_vec);

    let beta = dotproduct_a_d.commit(&r_beta, gens_1);
    //transcript.absorb(b"beta", &beta);

    let c = transcript.squeeze(b"c")?;

    let z = (0..d_vec.len())
      .map(|i| c * x_vec[i] + d_vec[i])
      .collect::<Vec<G::Scalar>>();

    let z_delta = c * blind_x + r_delta;
    let z_beta = c * blind_y + r_beta;

    Ok((
      DotProductProof {
        delta,
        beta,
        z,
        z_delta,
        z_beta,
      },
      Cx,
      Cy,
    ))
  }

  pub fn verify(
    &self,
    gens_1: &MultiCommitGens<G>,
    gens_n: &MultiCommitGens<G>,
    transcript: &mut G::TE,
    a: &[G::Scalar],
    Cx: &G,
    Cy: &G,
  ) -> Result<(), NovaError> {
    if a.len() != gens_n.n {
      return Err(NovaError::InvalidInputLength);
    }
    if gens_1.n != 1 {
      return Err(NovaError::InvalidInputLength);
    }

    //transcript.absorb(b"Cy", Cx);
    //transcript.absorb(b"Cy", Cy);

    for sub_a in a {
      transcript.absorb(b"a", sub_a);
    }

    //transcript.absorb(b"delta", &self.delta);
    //transcript.absorb(b"beta", &self.beta);

    let c = transcript.squeeze(b"c")?;

    let mut result =
      *Cx * c + self.delta == Commitments::batch_commit(self.z.as_ref(), &self.z_delta, gens_n);

    let dotproduct_z_a = DotProductProof::<G>::compute_dotproduct(&self.z, a);
    result &= *Cy * c + self.beta == dotproduct_z_a.commit(&self.z_beta, gens_1);

    if result {
      Ok(())
    } else {
      Err(NovaError::InternalTranscriptError)
    }
  }
}

#[allow(unused)]
pub struct DotProductProofGens<G: Group> {
  n: usize,
  pub gens_n: MultiCommitGens<G>,
  pub gens_1: MultiCommitGens<G>,
}

impl<G: Group> DotProductProofGens<G> {
  pub fn new(n: usize, label: &[u8], transcript: &mut G::TE) -> Self {
    let (gens_n, gens_1) = MultiCommitGens::new(n + 1, label, transcript).split_at(n);
    DotProductProofGens { n, gens_n, gens_1 }
  }
}


#[derive(Debug)]
#[allow(unused)]
pub struct DotProductProofLog<G: Group> {
  bullet_reduction_proof: BulletReductionProof<G>,
  delta: G,
  beta: G,
  z1: G::Scalar,
  z2: G::Scalar,
}

impl<G: Group> DotProductProofLog<G> {

  pub fn prove(
    gens: &DotProductProofGens<G>,
    transcript: &mut G::TE,
    x_vec: &[G::Scalar],
    blind_x: &G::Scalar,
    a_vec: &[G::Scalar],
    y: &G::Scalar,
    blind_y: &G::Scalar,
  ) -> Result<(Self, G, G), NovaError> {

    let n = x_vec.len();
    assert_eq!(x_vec.len(), a_vec.len());
    assert_eq!(gens.n, n);

    // produce randomness for generating a proof
    let d = transcript.squeeze(b"d")?;
    let r_delta = transcript.squeeze(b"r_delta")?;
    let r_beta = transcript.squeeze(b"r_beta")?;
    let blinds_vec = {
      let mut v1 = Vec::new();
      for _i in 0..(2 * n.log_2()) {       
        v1.push(transcript.squeeze(b"blinds_vec_1")?);
      }

      let mut v2 = Vec::new();
      for _i in 0..(2 * n.log_2()) {
        v2.push(transcript.squeeze(b"blinds_vec21")?);
      }

      (0..v1.len())
        .map(|i| (v1[i], v2[i]))
        .collect::<Vec<(G::Scalar, G::Scalar)>>()
    };

    let Cx = Commitments::batch_commit(x_vec, blind_x, &gens.gens_n);
    //transcript.absorb(b"Cx", &Cx);

    let Cy = y.commit(blind_y, &gens.gens_1);
    //transcript.absorb(b"Cy", &Cy);

    for _sub_a in a_vec {
      //transcript.absorb(b"a", sub_a);
    }

    let blind_Gamma = *blind_x + *blind_y;
    let (bullet_reduction_proof, _Gamma_hat, x_hat, a_hat, g_hat, rhat_Gamma) =
      BulletReductionProof::prove(
        transcript,
        &gens.gens_1.G[0],
        &gens.gens_n.G,
        &gens.gens_n.h,
        x_vec,
        a_vec,
        &blind_Gamma,
        &blinds_vec,
      );
    let y_hat = x_hat * a_hat;

    let delta = {
      let gens_hat = MultiCommitGens {
        n: 1,
        G: vec![g_hat],
        h: gens.gens_1.h,
      };
      d.commit(&r_delta, &gens_hat)
    };

    //transcript.absorb(b"delta", &delta);

    let beta = d.commit(&r_beta, &gens.gens_1);
    //transcript.absorb(b"beta", &beta);

    let c = transcript.squeeze(b"c")?;

    let z1 = d + c * y_hat;
    let z2 = a_hat * (c * rhat_Gamma + r_beta) + r_delta;

    Ok((
      DotProductProofLog {
        bullet_reduction_proof,
        delta,
        beta,
        z1,
        z2,
      },
      Cx,
      Cy,
    ))
  }

  pub fn verify(
    &self,
    n: usize,
    gens: &DotProductProofGens<G>,
    transcript: &mut G::TE,
    a: &[G::Scalar],
    Cx: &G,
    Cy: &G,
  ) -> Result<(), NovaError> {
    assert_eq!(gens.n, n);
    assert_eq!(a.len(), n);

    //transcript.absorb(b"Cy", Cx);
    //transcript.absorb(b"Cy", Cy);

    for sub_a in a {
      transcript.absorb(b"a", sub_a);
    }


    let Gamma = *Cx + *Cy;

    let (g_hat, Gamma_hat, a_hat) =
      self
        .bullet_reduction_proof
        .verify(n, a, transcript, &Gamma, &gens.gens_n.G)?;

    //transcript.absorb(b"delta", &self.delta);
    //transcript.absorb(b"beta", &self.beta);

    let c = transcript.squeeze(b"c")?;

    let c_s = &c;
    let beta_s = self.beta;
    let a_hat_s = &a_hat;
    let delta_s = self.delta;
    let z1_s = &self.z1;
    let z2_s = &self.z2;

    let lhs = (Gamma_hat * c_s + beta_s) * a_hat_s + delta_s;
    let rhs = (g_hat + gens.gens_1.G[0] * a_hat_s) * z1_s + gens.gens_1.h * z2_s;

    (lhs == rhs)
      .then_some(())
      .ok_or(NovaError::InternalTranscriptError)
  }
}

/*#[cfg(test)]
mod tests {
  use super::*;
  use rand::rngs::OsRng;

  use crate::provider::bn256_grumpkin::bn256::Point as G1;
  use crate::provider::bn256_grumpkin::bn256;

  use ff::Field;

  use crate::traits;

  #[test]
  fn check_dotproductproof() {
    check_dotproductproof_helper()
  }

  fn check_dotproductproof_helper() {
    let mut csprng: OsRng = OsRng;

    let n = 1024;

    let mut prover_transcript = <bn256::Point as traits::Group>::TE::new(b"example");
    let gens_1 = MultiCommitGens::<G1>::new(1, b"test-two", &mut prover_transcript);
    let gens_1024 = MultiCommitGens::<G1>::new(n, b"test-1024", &mut prover_transcript);

    let mut x: Vec<<bn256::Point as group::Group>::Scalar> = Vec::new();
    let mut a: Vec<<bn256::Point as group::Group>::Scalar> = Vec::new();
    for _ in 0..n {
      x.push(<bn256::Point as traits::Group>::Scalar::random(&mut csprng));
      a.push(<bn256::Point as traits::Group>::Scalar::random(&mut csprng));
    }
    let r_x = <bn256::Point as traits::Group>::Scalar::random(&mut csprng);
    let r_y = <bn256::Point as traits::Group>::Scalar::random(&mut csprng);

    let y = DotProductProof::<G1>::compute_dotproduct(&x, &a);

    let result = DotProductProof::prove(
      &gens_1,
      &gens_1024,
      &mut prover_transcript,
      &x,
      &r_x,
      &a,
      &y,
      &r_y,
    );

    if let Ok((proof, Cx, Cy)) = result {
      let mut verifier_transcript = <bn256::Point as traits::Group>::TE::new(b"example");
      assert!(proof
        .verify(&gens_1, &gens_1024, &mut verifier_transcript, &a, &Cx, &Cy)
        .is_ok());
    } else {
      assert!(false);
    }

  }

  /*#[test]
  fn check_dotproductproof_log() {
    check_dotproductproof_log_helper::<G1Projective>()
  }
  fn check_dotproductproof_log_helper<G: Group>() {
    let mut prng = test_rng();

    let n = 1024;

    let gens = DotProductProofGens::<G>::new(n, b"test-1024");

    let x: Vec<G::Scalar> = (0..n).map(|_i| G::Scalar::rand(&mut prng)).collect();
    let a: Vec<G::Scalar> = (0..n).map(|_i| G::Scalar::rand(&mut prng)).collect();
    let y = DotProductProof::<G>::compute_dotproduct(&x, &a);

    let r_x = G::Scalar::rand(&mut prng);
    let r_y = G::Scalar::rand(&mut prng);

    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, Cx, Cy) = DotProductProofLog::prove(
      &gens,
      &mut prover_transcript,
      &mut random_tape,
      &x,
      &r_x,
      &a,
      &y,
      &r_y,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(n, &gens, &mut verifier_transcript, &a, &Cx, &Cy)
      .is_ok());
  }*/
}*/
