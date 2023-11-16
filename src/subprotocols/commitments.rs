//! This module is an adaptation of code from the Lasso crate.
//! See NOTICE.md for more details
use crate::traits::{TranscriptEngineTrait, Group};
//use group::Group as G;

#[derive(Debug)]
pub struct MultiCommitGens<G: Group>  {
  pub n: usize,
  pub G: Vec<G>,
  pub h: G,
}

impl<G: Group> MultiCommitGens<G> {
  fn random(
    transcript: &mut G::TE,
  ) -> G {
    let label = b"Inside rand";
    let bases = G::from_label(label, 32);

    let mut scalars = Vec::with_capacity(32);
    for _i in 0..32 {
      scalars.push(transcript.squeeze(b"rand").unwrap());
    }
    G::vartime_multiscalar_mul(&scalars, bases.as_slice())
  }

  pub fn new(n: usize, _label: &[u8], transcript: &mut G::TE) -> Self {

    //transcript.absorb(b"label", &label);
    let mut gens: Vec<G> = Vec::new();
    for _ in 0..n + 1 {
      gens.push(Self::random(transcript));
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
