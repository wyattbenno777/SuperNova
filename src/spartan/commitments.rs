//! This module is an adaptation of code from the Lasso crate.
use digest::{ExtendableOutput, Update};
use sha3::Shake256;
use std::io::Read;
use halo2curves::bn256::{
  G1Affine as Bn256Affine, G1 as Bn256Point, Fr as Scalar
};
use halo2curves::CurveExt;
use group::Curve;
use crate::traits::Group;


#[derive(Debug)]
pub struct MultiCommitGens  {
  pub n: usize,
  pub G: Vec<Bn256Affine>,
  pub h: Bn256Affine,
}

impl MultiCommitGens {
  pub fn new(n: usize, label: &[u8]) -> Self {
    let mut shake = Shake256::default();
    shake.update(label);
    let mut reader = shake.finalize_xof();

    let mut gens = Vec::new();
    for _ in 0..n {
      let mut uniform_bytes = [0u8; 32];
      reader.read_exact(&mut uniform_bytes).unwrap();
      let hash = Bn256Point::hash_to_curve("from_uniform_bytes");
      gens.push(hash(&uniform_bytes).to_affine());
    }

    MultiCommitGens {
      n,
      G: gens[..n].to_vec(),
      h: gens[n],
    }
  }

  pub fn clone(&self) -> Self {
    MultiCommitGens {
      n: self.n,
      h: self.h,
      G: self.G.clone(),
    }
  }

  pub fn split_at(&self, mid: usize) -> (Self, Self) {
    let (G1, G2) = self.G.split_at(mid);

    (
      MultiCommitGens {
        n: G1.len(),
        G: G1.to_vec(),
        h: self.h,
      },
      MultiCommitGens {
        n: G2.len(),
        G: G2.to_vec(),
        h: self.h,
      },
    )
  }
}

pub trait Commitments: Sized {
  fn commit(&self, blind: &Scalar, gens_n: &MultiCommitGens) -> Bn256Point;
  fn batch_commit(inputs: &[Self], blind: &Scalar, gens_n: &MultiCommitGens) -> Bn256Point;
}

impl Commitments for Scalar {
  fn commit(&self, blind: &Scalar, gens_n: &MultiCommitGens) -> Bn256Point {
    assert_eq!(gens_n.n, 1);

    gens_n.G[0] * self + gens_n.h * blind
  }

  fn batch_commit(inputs: &[Self], blind: &Scalar, gens_n: &MultiCommitGens) -> Bn256Point {
    assert_eq!(gens_n.n, inputs.len());
    
    let mut bases: Vec<Bn256Affine> = gens_n.G.clone();
    let mut scalars = inputs.to_vec();

    bases.push(gens_n.h.clone());
    scalars.push(*blind);

    Bn256Point::vartime_multiscalar_mul(&scalars, &bases)
  }
}
