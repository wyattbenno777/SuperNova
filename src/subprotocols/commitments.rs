//! This module is an adaptation of code from the Lasso crate.
//! See NOTICE.md for more details
use digest::{ExtendableOutput, Update};
use sha3::Shake256;
use std::io::Read;
use crate::traits::Group;


#[derive(Debug)]
pub struct MultiCommitGens<G: Group>  {
  pub n: usize,
  pub G: Vec<G>,
  pub h: G,
}

impl<G: Group + halo2curves::CurveExt<AffineExt = G>> MultiCommitGens<G> {
  pub fn new(n: usize, label: &[u8]) -> Self {
    let mut shake = Shake256::default();
    shake.update(label);
    let mut reader = shake.finalize_xof();

    let mut gens = Vec::new();
    for _ in 0..n {
      let mut uniform_bytes = [0u8; 32];
      reader.read_exact(&mut uniform_bytes).unwrap();
      let hash = G::hash_to_curve("from_uniform_bytes");
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

pub trait Commitments<G: Group>: Sized{
  fn commit(&self, blind: &G::Scalar, gens_n: &MultiCommitGens<G>) -> G;
  fn batch_commit(inputs: &[Self], blind: &G::Scalar, gens_n: &MultiCommitGens<G>) -> G;
}

impl<G: Group> Commitments<G> for G::Scalar
  where
    G: Group,
{
  fn commit(&self, blind: &G::Scalar, gens_n: &MultiCommitGens<G>) -> G {
    assert_eq!(gens_n.n, 1);

    gens_n.G[0] * self + gens_n.h * blind
  }

  fn batch_commit(inputs: &[Self], blind: &G::Scalar, gens_n: &MultiCommitGens<G>) -> G {
    assert_eq!(gens_n.n, inputs.len());
    
    let mut bases: Vec<G> = gens_n.G.clone();
    let mut scalars = inputs.to_vec();

    bases.push(gens_n.h.clone());
    scalars.push(*blind);

    let bases: Vec<G::PreprocessedGroupElement> = 
    bases.iter().map(G::preprocessed).collect();


    G::vartime_multiscalar_mul(&scalars, bases.as_slice())
  }
}
