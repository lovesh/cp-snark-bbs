use ark_ff::{Field, PrimeField};
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::prelude::{AllocVar, AllocationMode, EqGadget};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_std::{cmp::Ordering, vec, vec::Vec};

/// Enforce min < value < max
#[derive(Clone)]
struct BoundCheckCircuit<F: Field> {
    min: Option<F>,
    max: Option<F>,
    value: Option<F>,
}

/// Enforce min < sum of values < max
#[derive(Clone)]
struct SumBoundCheckCircuit<F: Field> {
    min: Option<F>,
    max: Option<F>,
    values: Option<[F; 4]>,
}

impl<ConstraintF: PrimeField> ConstraintSynthesizer<ConstraintF>
    for BoundCheckCircuit<ConstraintF>
{
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<ConstraintF>,
    ) -> Result<(), SynthesisError> {
        let val = FpVar::new_variable(
            cs.clone(),
            || self.value.ok_or(SynthesisError::AssignmentMissing),
            AllocationMode::Witness,
        )?;

        let min = FpVar::new_variable(
            cs.clone(),
            || self.min.ok_or(SynthesisError::AssignmentMissing),
            AllocationMode::Input,
        )?;
        let max = FpVar::new_variable(
            cs.clone(),
            || self.max.ok_or(SynthesisError::AssignmentMissing),
            AllocationMode::Input,
        )?;

        // val strictly less than max, i.e. val < max and val != max
        val.enforce_cmp(&max, Ordering::Less, false)?;
        // val strictly greater than max, i.e. val > min and val != min
        val.enforce_cmp(&min, Ordering::Greater, false)?;
        Ok(())
    }
}

impl<ConstraintF: PrimeField> ConstraintSynthesizer<ConstraintF>
    for SumBoundCheckCircuit<ConstraintF>
{
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<ConstraintF>,
    ) -> Result<(), SynthesisError> {
        let mut sum_vars = vec![];
        let mut sum = ConstraintF::zero();
        let values = match self.values {
            Some(vals) => vals.map(|m| Some(m)),
            _ => [None, None, None, None],
        };

        for v in values {
            let v = FpVar::new_variable(
                cs.clone(),
                || {
                    let v = v.ok_or(SynthesisError::AssignmentMissing)?;
                    sum += v;
                    Ok(v)
                },
                AllocationMode::Witness,
            )?;
            sum_vars.push(v);
        }

        let sum = FpVar::new_variable(cs.clone(), || Ok(sum), AllocationMode::Witness)?;
        sum.enforce_equal(&sum_vars.iter().sum())?;

        let min = FpVar::new_variable(
            cs.clone(),
            || self.min.ok_or(SynthesisError::AssignmentMissing),
            AllocationMode::Input,
        )?;
        let max = FpVar::new_variable(
            cs.clone(),
            || self.max.ok_or(SynthesisError::AssignmentMissing),
            AllocationMode::Input,
        )?;

        // sum less than or equal to max, i.e. sum <= max
        sum.enforce_cmp(&max, Ordering::Less, true)?;
        // sum greater than or equal to min, i.e. sum >= min
        sum.enforce_cmp(&min, Ordering::Greater, true)?;
        // let csp = cs.clone().into_inner().unwrap();
        // println!("{} {} {}, {:?}", csp.num_constraints, csp.num_instance_variables, csp.num_witness_variables, cs.which_is_unsatisfied());
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::{Bls12_381, G1Affine, G1Projective};
    use ark_ec::{PairingEngine, ProjectiveCurve};
    use ark_std::{
        collections::{BTreeMap, BTreeSet},
        rand::{rngs::StdRng, RngCore, SeedableRng},
        UniformRand,
    };
    use bbs_plus::prelude::{KeypairG2, SignatureG1, SignatureParamsG1};
    use blake2::Blake2b;
    use legogro16::verifier_new::get_commitment_to_witnesses;
    use legogro16::{
        generator_new::generate_random_parameters_new, prepare_verifying_key,
        prover_new::create_random_proof_new, verifier::verify_proof,
        verifier_new::verify_commitment_new,
    };
    use proof_system::prelude::{
        EqualWitnesses, MetaStatement, MetaStatements, Proof, ProofSpec, Statement, Statements,
        Witness, WitnessRef, Witnesses,
    };
    use proof_system::statement::{
        PedersenCommitment as PedersenCommitmentStmt, PoKBBSSignatureG1 as PoKSignatureBBSG1Stmt,
    };
    use proof_system::witness::PoKBBSSignatureG1 as PoKSignatureBBSG1Wit;

    type Fr = <Bls12_381 as PairingEngine>::Fr;
    type ProofG1 = Proof<Bls12_381, G1Affine, Fr, Blake2b>;

    // Generate messages, public params and signature
    fn sig_setup<R: RngCore>(
        rng: &mut R,
        message_count: usize,
    ) -> (
        Vec<Fr>,
        SignatureParamsG1<Bls12_381>,
        KeypairG2<Bls12_381>,
        SignatureG1<Bls12_381>,
    ) {
        // Generate messages as 101, 102, ..., 100+ message_count
        let messages: Vec<Fr> = (1..=message_count)
            .into_iter()
            .map(|i| Fr::from(100 + i as u64))
            .collect();
        let params = SignatureParamsG1::<Bls12_381>::generate_using_rng(rng, message_count);
        let keypair = KeypairG2::<Bls12_381>::generate_using_rng(rng, &params);
        let sig =
            SignatureG1::<Bls12_381>::new(rng, &messages, &keypair.secret_key, &params).unwrap();
        (messages, params, keypair, sig)
    }

    fn get_pedersen_bases<R: RngCore>(
        rng: &mut R,
        num_instance_variables: usize,
        commit_witness_count: usize,
    ) -> Vec<G1Affine> {
        (0..num_instance_variables + commit_witness_count + 1)
            .map(|_| G1Projective::rand(rng).into_affine())
            .collect::<Vec<_>>()
    }

    #[test]
    fn bound_check_message() {
        // Prover has a BBS+ signature and he wants to prove that one of the signed message satisfies `min < message < max`
        // on public `min` and `max` but hiding the message.

        let mut rng = StdRng::seed_from_u64(0u64);
        // Prover has the BBS+ signature
        let message_count = 10;
        let (messages, sig_params, keypair, sig) = sig_setup(&mut rng, message_count);
        sig.verify(&messages, &keypair.public_key, &sig_params)
            .unwrap();

        // There are 2 public inputs and there is always an instance variable as 1
        let num_instance_variables = 3;
        // Only 1 witness that is the message whose bounds need to proved is committed
        let commit_witness_count = 1;

        // Generators for the Pedersen commitment. Its important that prover does not discrete log of these wrt each other
        let pedersen_bases =
            get_pedersen_bases(&mut rng, num_instance_variables, commit_witness_count);

        let circuit = BoundCheckCircuit::<Fr> {
            min: None,
            max: None,
            value: None,
        };
        let params = generate_random_parameters_new::<Bls12_381, _, _>(
            circuit,
            &pedersen_bases,
            commit_witness_count,
            &mut rng,
        )
        .unwrap();

        let pvk = prepare_verifying_key(&params.vk);

        // Create commitment randomness
        let v = Fr::rand(&mut rng);
        let link_v = Fr::rand(&mut rng);

        // Message whose bounds need to be proved, i.e. `min < val < max` needs to be proved
        let m_idx = 4;
        let val = messages[m_idx].clone();

        let min = Fr::from(100u64);
        let max = Fr::from(107u64);
        let circuit = BoundCheckCircuit {
            min: Some(min),
            max: Some(max),
            value: Some(val),
        };

        // Prover creates Groth16 proof
        let proof = create_random_proof_new(circuit, v, link_v, &params, &mut rng).unwrap();

        // Verifies verifies Groth16 proof
        assert!(verify_proof(&pvk, &proof).unwrap());

        // This is not done by the verifier but the prover as safety check that the commitment is correct
        assert!(
            verify_commitment_new(&params.vk, &proof, &[min, max], &[val], &v, &link_v).unwrap()
        );
        assert!(!verify_commitment_new(
            &params.vk,
            &proof,
            &[min, Fr::from(105u64)],
            &[val],
            &v,
            &link_v
        )
        .unwrap());
        assert!(!verify_commitment_new(
            &params.vk,
            &proof,
            &[min, Fr::from(104u64)],
            &[val],
            &v,
            &link_v
        )
        .unwrap());
        assert!(!verify_commitment_new(
            &params.vk,
            &proof,
            &[Fr::from(105u64), max],
            &[val],
            &v,
            &link_v
        )
        .unwrap());
        assert!(!verify_commitment_new(
            &params.vk,
            &proof,
            &[Fr::from(106u64), max],
            &[val],
            &v,
            &link_v
        )
        .unwrap());

        // Since both prover and verifier know the public inputs, they can independently get the commitment to the witnesses
        let commitment_to_witness =
            get_commitment_to_witnesses(&params.vk, &proof, &[min, max]).unwrap();

        // The bases and commitment opening
        let bases = vec![pedersen_bases[3].clone(), pedersen_bases[4].clone()];
        let committed = vec![val, link_v];

        // Prove the equality of message in the BBS+ signature and `commitment_to_witness`
        let mut statements = Statements::new();
        statements.add(Statement::PoKBBSSignatureG1(PoKSignatureBBSG1Stmt {
            params: sig_params.clone(),
            public_key: keypair.public_key.clone(),
            revealed_messages: BTreeMap::new(),
        }));
        statements.add(Statement::PedersenCommitment(PedersenCommitmentStmt {
            bases: bases.clone(),
            commitment: commitment_to_witness.clone(),
        }));

        let mut meta_statements = MetaStatements::new();
        meta_statements.add(MetaStatement::WitnessEquality(EqualWitnesses(
            vec![(0, m_idx), (1, 0)] // 0th statement's `m_idx`th witness is equal to 1st statement's 0th witness
                .into_iter()
                .collect::<BTreeSet<WitnessRef>>(),
        )));

        let proof_spec = ProofSpec {
            statements: statements.clone(),
            meta_statements: meta_statements.clone(),
            context: None,
        };

        let mut witnesses = Witnesses::new();
        witnesses.add(PoKSignatureBBSG1Wit::new_as_witness(
            sig.clone(),
            messages
                .clone()
                .into_iter()
                .enumerate()
                .map(|t| t)
                .collect(),
        ));
        witnesses.add(Witness::PedersenCommitment(committed));

        let proof = ProofG1::new(&mut rng, proof_spec.clone(), witnesses.clone(), None).unwrap();

        proof.verify(proof_spec, None).unwrap();
    }

    #[test]
    fn bound_check_messages_sum() {
        // Prover has a BBS+ signature and he wants to prove that sum of certain signed messages satisfies `min <= sum <= max`
        // on public `min` and `max` but hiding the messages and the sum.

        let mut rng = StdRng::seed_from_u64(0u64);
        // Prover has the BBS+ signature
        let message_count = 10;
        let (messages, sig_params, keypair, sig) = sig_setup(&mut rng, message_count);
        sig.verify(&messages, &keypair.public_key, &sig_params)
            .unwrap();

        // There are 2 public inputs and there is always an instance variable as 1
        let num_instance_variables = 3;
        // 4 witnesses (messages) whose sum needs to be bounded
        let commit_witness_count = 4;

        // Generators for the Pedersen commitment. Its important that prover does not discrete log of these wrt each other
        let pedersen_bases =
            get_pedersen_bases(&mut rng, num_instance_variables, commit_witness_count);

        let circuit = SumBoundCheckCircuit::<Fr> {
            min: None,
            max: None,
            values: None,
        };
        let params = generate_random_parameters_new::<Bls12_381, _, _>(
            circuit,
            &pedersen_bases,
            commit_witness_count,
            &mut rng,
        )
        .unwrap();

        let pvk = prepare_verifying_key(&params.vk);

        // Create commitment randomness
        let v = Fr::rand(&mut rng);
        let link_v = Fr::rand(&mut rng);

        // Messages whose sum need to be proven bounded, i.e. `min < sum of messages < max` needs to be proved
        // Indexes of the messages
        let m_ids: [usize; 4] = [2, 3, 4, 5];
        let mut vals = m_ids
            .iter()
            .map(|i| messages[*i].clone())
            .collect::<Vec<_>>();
        let vals: [Fr; 4] = [
            vals.remove(0),
            vals.remove(0),
            vals.remove(0),
            vals.remove(0),
        ];

        let min = Fr::from(400u64);
        let max = Fr::from(419u64);
        let circuit = SumBoundCheckCircuit {
            min: Some(min),
            max: Some(max),
            values: Some(vals.clone()),
        };

        // Prover creates Groth16 proof
        let proof = create_random_proof_new(circuit, v, link_v, &params, &mut rng).unwrap();

        // Verifies verifies Groth16 proof
        assert!(verify_proof(&pvk, &proof).unwrap());

        // This is not done by the verifier but the prover as safety check that the commitment is correct
        assert!(
            verify_commitment_new(&params.vk, &proof, &[min, max], &vals, &v, &link_v).unwrap()
        );
        assert!(!verify_commitment_new(
            &params.vk,
            &proof,
            &[min, Fr::from(412u64)],
            &vals,
            &v,
            &link_v
        )
        .unwrap());

        assert!(!verify_commitment_new(
            &params.vk,
            &proof,
            &[Fr::from(420u64), max],
            &vals,
            &v,
            &link_v
        )
        .unwrap());

        // Since both prover and verifier know the public inputs, they can independently get the commitment to the witnesses
        let commitment_to_witnesses =
            get_commitment_to_witnesses(&params.vk, &proof, &[min, max]).unwrap();

        // The bases and commitment opening
        let bases = vec![
            pedersen_bases[3].clone(),
            pedersen_bases[4].clone(),
            pedersen_bases[5].clone(),
            pedersen_bases[6].clone(),
            pedersen_bases[7].clone(),
        ];
        let mut committed = vals.to_vec();
        committed.push(link_v);

        // Prove the equality of messages in the BBS+ signature and `commitment_to_witnesses`
        let mut statements = Statements::new();
        statements.add(Statement::PoKBBSSignatureG1(PoKSignatureBBSG1Stmt {
            params: sig_params.clone(),
            public_key: keypair.public_key.clone(),
            revealed_messages: BTreeMap::new(),
        }));
        statements.add(Statement::PedersenCommitment(PedersenCommitmentStmt {
            bases: bases.clone(),
            commitment: commitment_to_witnesses.clone(),
        }));

        let mut meta_statements = MetaStatements::new();
        for (i, m_i) in m_ids.iter().enumerate() {
            meta_statements.add(MetaStatement::WitnessEquality(EqualWitnesses(
                vec![(0, *m_i), (1, i)]
                    .into_iter()
                    .collect::<BTreeSet<WitnessRef>>(),
            )));
        }

        let proof_spec = ProofSpec {
            statements: statements.clone(),
            meta_statements: meta_statements.clone(),
            context: None,
        };

        let mut witnesses = Witnesses::new();
        witnesses.add(PoKSignatureBBSG1Wit::new_as_witness(
            sig.clone(),
            messages
                .clone()
                .into_iter()
                .enumerate()
                .map(|t| t)
                .collect(),
        ));
        witnesses.add(Witness::PedersenCommitment(committed));

        let proof = ProofG1::new(&mut rng, proof_spec.clone(), witnesses.clone(), None).unwrap();

        proof.verify(proof_spec, None).unwrap();
    }
}
