use crate::provider::bn256_grumpkin::bn256;
use digest::{ExtendableOutput, Update};
use pasta_curves::arithmetic::{CurveExt};
use sha3::Shake256;
use std::io::Read;
use crate::traits::Group;

type GroupElement = bn256::Point;
type Scalar = bn256::Scalar;
use halo2curves::bn256::{
  G1Affine as Bn256Affine, G1Compressed as Bn256Compressed, G1 as Bn256Point,
};

#[derive(Debug)]
pub struct MultiCommitGens {
  pub n: usize,
  pub G: Vec<GroupElement>,
  pub h: GroupElement,
}

impl MultiCommitGens {
  pub fn new(n: usize, label: &[u8]) -> Self {
    let mut shake = Shake256::default();
    shake.update(label);
    //shake.input(GROUP_BASEPOINT_COMPRESSED.as_bytes());

    let mut reader = shake.finalize_xof();
    let mut gens: Vec<GroupElement> = Vec::new();

    for _ in 0..n {
      let mut uniform_bytes = [0u8; 32];
      reader.read_exact(&mut uniform_bytes).unwrap();
      let hash = bn256::Point::hash_to_curve("from_uniform_bytes");
      gens.push(hash(&uniform_bytes));
    }

    MultiCommitGens {
      n,
      G: gens[..n].to_vec(),
      h: gens[n],
    }
  }

  pub fn clone(&self) -> MultiCommitGens {
    MultiCommitGens {
      n: self.n,
      h: self.h,
      G: self.G.clone(),
    }
  }

  pub fn scale(&self, s: &Scalar) -> Self {
  
    let s_scaled = self
    .G 
    .clone()
    .iter()
    .map(|g| {
       // Map G1Affine -> G1
       let g: GroupElement = g.into();  
       GroupElement::vartime_multiscalar_mul(&[*s], &[g])
         .preprocessed()
    })
    .collect();
    
    MultiCommitGens {
      n: self.n,
      h: self.h,  
      G: s_scaled,
    }
  }

  pub fn split_at(&self, mid: usize) -> (MultiCommitGens, MultiCommitGens) {
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

pub trait Commitments {
  fn commit(&self, blind: &Scalar, gens_n: &MultiCommitGens) -> GroupElement;
}

impl Commitments for Scalar {
  fn commit(&self, blind: &Scalar, gens_n: &MultiCommitGens) -> GroupElement {
    assert_eq!(gens_n.n, 1);
    GroupElement::vartime_multiscalar_mul(&[*self, *blind], &[gens_n.G[0].into(), gens_n.h.into()])
  }
}

impl Commitments for Vec<Scalar> {
  fn commit(&self, blind: &Scalar, gens_n: &MultiCommitGens) -> GroupElement {
    assert_eq!(gens_n.n, self.len());
    GroupElement::vartime_multiscalar_mul(self, &gens_n.G) + blind * gens_n.h
  }
}

impl Commitments for [Scalar] {
  fn commit(&self, blind: &Scalar, gens_n: &MultiCommitGens) -> GroupElement {
    assert_eq!(gens_n.n, self.len());
    GroupElement::vartime_multiscalar_mul(self, &gens_n.G) + blind * gens_n.h
  }
}