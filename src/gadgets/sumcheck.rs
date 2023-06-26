#![allow(unused)]
use crate::traits::Group;
use bellperson::{
  gadgets::{
    boolean::{AllocatedBit, Boolean},
    num::{AllocatedNum, Num},
    Assignment,
  },
  ConstraintSystem, LinearCombination, SynthesisError,
};
use ff::{Field, PrimeField, PrimeFieldBits};

// method compatible with src/spartan/sumcheck.rs > UniPoly::evaluate()
pub fn uni_evaluate<Scalar, CS>(
  mut cs: CS,
  coeffs: Vec<AllocatedNum<Scalar>>,
  r: AllocatedNum<Scalar>,
) -> Result<AllocatedNum<Scalar>, SynthesisError>
where
  Scalar: PrimeField + PrimeFieldBits,
  CS: ConstraintSystem<Scalar>,
{
  let mut eval_alloc: AllocatedNum<Scalar> =
    AllocatedNum::<Scalar>::alloc(&mut cs, || Ok(Scalar::ZERO))?;
  let mut eval: Num<Scalar> = Num::<Scalar>::from(eval_alloc);

  let mut curr: AllocatedNum<Scalar> = AllocatedNum::<Scalar>::alloc(&mut cs, || Ok(Scalar::ONE))?;
  for (i, coeff) in coeffs.iter().enumerate() {
    eval = eval.add(&Num::<Scalar>::from(
      curr.mul(cs.namespace(|| format!("mul {}", i)), &coeff)?,
    ));
    curr = curr.mul(cs.namespace(|| format!("mul2 {}", i)), &r)?;
  }
  let allocated_eval: AllocatedNum<Scalar> =
    AllocatedNum::<Scalar>::alloc(&mut cs, || Ok(eval.get_value().unwrap()))?;

  Ok(allocated_eval)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::bellperson::{
    r1cs::{NovaShape, NovaWitness},
    {shape_cs::ShapeCS, solver::SatisfyingAssignment},
  };
  use crate::spartan::sumcheck::UniPoly;
  use pasta_curves::{
    arithmetic::CurveAffine,
    group::{Curve, Group},
    pallas,
    pallas::Scalar,
    vesta,
  };

  fn synthetize_uni_evaluate<Scalar, CS>(
    mut cs: CS,
    coeffs: Vec<Scalar>,
    r: Scalar,
  ) -> AllocatedNum<Scalar>
  where
    Scalar: PrimeField + PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
  {
    // prepare inputs
    let r_var = AllocatedNum::<Scalar>::alloc(cs.namespace(|| "alloc r"), || Ok(r)).unwrap();
    let mut coeffs_var: Vec<AllocatedNum<Scalar>> = Vec::new();
    for (i, coeff) in coeffs.iter().enumerate() {
      coeffs_var.push(
        AllocatedNum::<Scalar>::alloc(cs.namespace(|| format!("alloc coeffs {}", i)), || {
          Ok(*coeff)
        })
        .unwrap(),
      );
    }

    // define inputs
    // let _ = r_var.inputize(cs.namespace(|| "Input r"));
    // for (i, coeff) in coeffs_var.iter().enumerate() {
    //   let _ = coeff.inputize(cs.namespace(|| format!("Input coeffs {}", i)));
    // }

    // evaluate in-circuit (synthetize)
    let res = uni_evaluate(cs.namespace(|| "uni_evaluate"), coeffs_var, r_var).unwrap();
    // let _ = res.inputize(cs.namespace(|| "Output res"));

    res
  }

  #[test]
  fn test_uni_evaluate() {
    let evals = vec![
      Scalar::from(1_u64),
      Scalar::from(2_u64),
      Scalar::from(3_u64),
    ];
    let p = UniPoly::<pallas::Point>::from_evals(&evals);
    let r = Scalar::from(5_u64);

    // let's test it against the CS
    let mut cs: ShapeCS<pallas::Point> = ShapeCS::new();
    let _ = synthetize_uni_evaluate(&mut cs, p.coeffs.clone(), r);

    println!("Number of constraints: {}", cs.num_constraints());

    let (shape, ck) = cs.r1cs_shape();

    let mut cs: SatisfyingAssignment<pallas::Point> = SatisfyingAssignment::new();
    let res = synthetize_uni_evaluate(&mut cs, p.coeffs.clone(), r);
    println!("circ res {:?}", res.get_value());
    assert_eq!(res.get_value().unwrap(), p.evaluate(&r));

    let (inst, witness) = cs.r1cs_instance_and_witness(&shape, &ck).unwrap();
    assert!(shape.is_sat(&ck, &inst, &witness).is_ok());
  }
}
