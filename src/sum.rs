use ark_ff::{Field, PrimeField};
use ark_r1cs_std::alloc::{AllocVar, AllocationMode};
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use std::cmp::Ordering;

/// Enforce min < sum of values < max
#[derive(Clone)]
pub struct SumBoundCheckCircuit<F: Field> {
    min: Option<F>,
    max: Option<F>,
    values: Option<[F; 4]>,
}

/// Enforce sum of `smalls` < sum of `larges`
#[derive(Clone)]
pub struct SumCompareCircuit<F: Field> {
    smalls: Option<[F; 4]>,
    larges: Option<[F; 4]>,
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
        Ok(())
    }
}

impl<ConstraintF: PrimeField> ConstraintSynthesizer<ConstraintF>
    for SumCompareCircuit<ConstraintF>
{
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<ConstraintF>,
    ) -> Result<(), SynthesisError> {
        let mut small_sum_vars = vec![];
        let mut small_sum = ConstraintF::zero();
        let mut large_sum_vars = vec![];
        let mut large_sum = ConstraintF::zero();

        let smalls = match self.smalls {
            Some(vals) => vals.map(|m| Some(m)),
            _ => [None, None, None, None],
        };

        let larges = match self.larges {
            Some(vals) => vals.map(|m| Some(m)),
            _ => [None, None, None, None],
        };

        // Note: Its important to allocate witness variables that are committed so allocate variables for
        // all in `smalls` and then all in `larges` and then variables for sum and the Schnorr proof
        // for the commitment assumes that.

        for v in smalls {
            let v = FpVar::new_variable(
                cs.clone(),
                || {
                    let v = v.ok_or(SynthesisError::AssignmentMissing)?;
                    small_sum += v;
                    Ok(v)
                },
                AllocationMode::Witness,
            )?;
            small_sum_vars.push(v);
        }

        for v in larges {
            let v = FpVar::new_variable(
                cs.clone(),
                || {
                    let v = v.ok_or(SynthesisError::AssignmentMissing)?;
                    large_sum += v;
                    Ok(v)
                },
                AllocationMode::Witness,
            )?;
            large_sum_vars.push(v);
        }

        let small_sum = FpVar::new_variable(cs.clone(), || Ok(small_sum), AllocationMode::Witness)?;
        small_sum.enforce_equal(&small_sum_vars.iter().sum())?;

        let large_sum = FpVar::new_variable(cs.clone(), || Ok(large_sum), AllocationMode::Witness)?;
        large_sum.enforce_equal(&large_sum_vars.iter().sum())?;

        // small_sum less than large_sum, i.e. small_sum < large_sum
        small_sum.enforce_cmp(&large_sum, Ordering::Less, false)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::*;
    use ark_bls12_381::Bls12_381;
    use ark_std::{
        collections::{BTreeMap, BTreeSet},
        rand::{rngs::StdRng, RngCore, SeedableRng},
        UniformRand,
    };
    use legogroth16::{
        create_random_proof, generate_random_parameters, prepare_verifying_key, verify_witness_commitment,
        verify_proof,
    };
    use proof_system::prelude::{
        EqualWitnesses, MetaStatement, MetaStatements, ProofSpec, Statement, Statements, Witness,
        WitnessRef, Witnesses,
    };
    use std::time::Instant;

    #[test]
    fn bound_check_messages_sum() {
        // Prover has a BBS+ signature and he wants to prove that sum of certain signed messages satisfies `min <= sum <= max`
        // on public `min` and `max` but hiding the messages and the sum. This can be useful in proving
        // that the sum of income sources is in a range.

        let mut rng = StdRng::seed_from_u64(0u64);
        // Prover has the BBS+ signature
        let message_count = 10;
        let (messages, sig_params, keypair, sig) = sig_setup(&mut rng, message_count);
        sig.verify(&messages, &keypair.public_key, &sig_params)
            .unwrap();

        // 4 witnesses (messages) whose sum needs to be bounded
        let commit_witness_count = 4;
        let public_inputs_count = 2;

        let circuit = SumBoundCheckCircuit::<Fr> {
            min: None,
            max: None,
            values: None,
        };
        let params = generate_random_parameters::<Bls12_381, _, _>(
            circuit,
            commit_witness_count,
            &mut rng,
        )
        .unwrap();

        let pvk = prepare_verifying_key(&params.vk);

        // Create commitment randomness
        let v = Fr::rand(&mut rng);
       
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

        let start = Instant::now();
        // Prover creates Groth16 proof
        let snark_proof = create_random_proof(circuit, v, &params, &mut rng).unwrap();
        let t1 = start.elapsed();
        println!("Time taken to create LegoGroth16 proof {:?}", t1);

        // This is not done by the verifier but the prover as safety check that the commitment is correct
        verify_witness_commitment(&params.vk, &snark_proof, 2, &vals, &v).unwrap();
        assert!(verify_witness_commitment(&params.vk, &snark_proof, 1, &vals, &v).is_err());

        assert!(verify_witness_commitment(
            &params.vk,
            &snark_proof,
            2,
            &[Fr::from(420u64), max],
            &v
        )
        .is_err());

        // Since both prover and verifier know the public inputs, they can independently get the commitment to the witnesses
        let commitment_to_witnesses = snark_proof.d;

        // The bases and commitment opening
        let mut bases = params.vk.gamma_abc_g1[1+public_inputs_count..1+public_inputs_count+commit_witness_count].to_vec();
        bases.push(params.vk.eta_gamma_inv_g1);
        let mut committed = vals.to_vec();
        committed.push(v);

        // Prove the equality of messages in the BBS+ signature and `commitment_to_witnesses`
        let start = Instant::now();
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
        let t2 = start.elapsed();
        println!("Time taken to create composite proof {:?}", t2);
        println!("Total time taken to create proof {:?}", t1 + t2);

        let start = Instant::now();
        // Verifies verifies Groth16 proof
        verify_proof(&pvk, &snark_proof, &[min, max]).unwrap();
        let t1 = start.elapsed();
        println!("Time taken to verify LegoGroth16 proof {:?}", t1);

        let start = Instant::now();
        proof.verify(proof_spec, None).unwrap();
        let t2 = start.elapsed();
        println!("Time taken to verify composite proof {:?}", t2);
        println!("Total time taken to verify proof {:?}", t1 + t2);
    }

    #[test]
    fn compare_messages_sum() {
        // Prover has 2 BBS+ signatures and he wants to prove that sum of certain signed messages from
        // the 1st signature are less than the sum of certain signed messages from 2nd signature.
        // This can be useful in proving sum of liabilities < sum of assets where liabilities and assets
        // are signed under different signatures.

        let mut rng = StdRng::seed_from_u64(0u64);

        // 1st BBS+ signature
        let message_count_1 = 5;
        let (messages_1, sig_params_1, keypair_1, sig_1) = sig_setup(&mut rng, message_count_1);
        sig_1
            .verify(&messages_1, &keypair_1.public_key, &sig_params_1)
            .unwrap();

        // 2nd BBS+ signature
        let message_count_2 = 10;
        let (messages_2, sig_params_2, keypair_2, sig_2) = sig_setup(&mut rng, message_count_2);
        sig_2
            .verify(&messages_2, &keypair_2.public_key, &sig_params_2)
            .unwrap();

        // 8 witnesses (messages), 4 from each signature
        let commit_witness_count = 8;
        let public_inputs_count = 0;

        let circuit = SumCompareCircuit::<Fr> {
            smalls: None,
            larges: None,
        };
        let params = generate_random_parameters::<Bls12_381, _, _>(
            circuit,
            commit_witness_count,
            &mut rng,
        )
        .unwrap();

        let pvk = prepare_verifying_key(&params.vk);

        // Create commitment randomness
        let v = Fr::rand(&mut rng);

        // Messages from 1st signature
        // Indexes of the messages
        let s_m_ids: [usize; 4] = [0, 1, 2, 3];
        let mut smalls = s_m_ids
            .iter()
            .map(|i| messages_1[*i].clone())
            .collect::<Vec<_>>();
        let smalls: [Fr; 4] = [
            smalls.remove(0),
            smalls.remove(0),
            smalls.remove(0),
            smalls.remove(0),
        ];

        // Messages from 2nd signature
        // Indexes of the messages
        let l_m_ids: [usize; 4] = [4, 6, 7, 8];
        let mut larges = l_m_ids
            .iter()
            .map(|i| messages_2[*i].clone())
            .collect::<Vec<_>>();
        let larges: [Fr; 4] = [
            larges.remove(0),
            larges.remove(0),
            larges.remove(0),
            larges.remove(0),
        ];

        let circuit = SumCompareCircuit {
            smalls: Some(smalls.clone()),
            larges: Some(larges.clone()),
        };

        // Prover creates Groth16 proof
        let start = Instant::now();
        let snark_proof = create_random_proof(circuit, v, &params, &mut rng).unwrap();
        let t1 = start.elapsed();
        println!("Time taken to create LegoGroth16 proof {:?}", t1);

        // This is not done by the verifier but the prover as safety check that the commitment is correct
        let mut wits = vec![];
        wits.extend_from_slice(&smalls);
        wits.extend_from_slice(&larges);

        verify_witness_commitment(&params.vk, &snark_proof, 0, &wits, &v).unwrap();

        assert!(verify_witness_commitment(&params.vk, &snark_proof, 0, &smalls, &v).is_err());

        assert!(verify_witness_commitment(&params.vk, &snark_proof, 0, &larges, &v).is_err());

        // Since both prover and verifier know the public inputs, they can independently get the commitment to the witnesses
        let commitment_to_witnesses = snark_proof.d;

        // The bases and commitment opening
        let mut bases = params.vk.gamma_abc_g1[1+public_inputs_count..1+public_inputs_count+commit_witness_count].to_vec();
        bases.push(params.vk.eta_gamma_inv_g1);
        let mut committed = wits.clone();
        committed.push(v);

        // Prove the equality of messages in the 2 BBS+ signatures and `commitment_to_witnesses`
        let start = Instant::now();
        let mut statements = Statements::new();
        statements.add(Statement::PoKBBSSignatureG1(PoKSignatureBBSG1Stmt {
            params: sig_params_1.clone(),
            public_key: keypair_1.public_key.clone(),
            revealed_messages: BTreeMap::new(),
        }));
        statements.add(Statement::PoKBBSSignatureG1(PoKSignatureBBSG1Stmt {
            params: sig_params_2.clone(),
            public_key: keypair_2.public_key.clone(),
            revealed_messages: BTreeMap::new(),
        }));
        statements.add(Statement::PedersenCommitment(PedersenCommitmentStmt {
            bases: bases.clone(),
            commitment: commitment_to_witnesses.clone(),
        }));

        let mut meta_statements = MetaStatements::new();

        // Enforce equality between the signatures' messages and commitment's opening
        // s_m_ids are message indexes from 1st signature, i.e. statement index 0
        for (i, m_i) in s_m_ids.iter().enumerate() {
            meta_statements.add(MetaStatement::WitnessEquality(EqualWitnesses(
                vec![(0, *m_i), (2, i)]
                    .into_iter()
                    .collect::<BTreeSet<WitnessRef>>(),
            )));
        }

        // l_m_ids are message indexes from 2st signature, i.e. statement index 1
        for (i, m_i) in l_m_ids.iter().enumerate() {
            meta_statements.add(MetaStatement::WitnessEquality(EqualWitnesses(
                vec![(1, *m_i), (2, s_m_ids.len() + i)]
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
            sig_1.clone(),
            messages_1
                .clone()
                .into_iter()
                .enumerate()
                .map(|t| t)
                .collect(),
        ));
        witnesses.add(PoKSignatureBBSG1Wit::new_as_witness(
            sig_2.clone(),
            messages_2
                .clone()
                .into_iter()
                .enumerate()
                .map(|t| t)
                .collect(),
        ));
        witnesses.add(Witness::PedersenCommitment(committed));

        let proof = ProofG1::new(&mut rng, proof_spec.clone(), witnesses.clone(), None).unwrap();
        let t2 = start.elapsed();
        println!("Time taken to create composite proof {:?}", t2);
        println!("Total time taken to create proof {:?}", t1 + t2);

        // Verifies verifies LegoGroth16 proof
        let start = Instant::now();
        verify_proof(&pvk, &snark_proof, &[]).unwrap();
        let t1 = start.elapsed();
        println!("Time taken to verify LegoGroth16 proof {:?}", t1);

        let start = Instant::now();
        proof.verify(proof_spec, None).unwrap();
        let t2 = start.elapsed();
        println!("Time taken to verify composite proof {:?}", t2);
        println!("Total time taken to verify proof {:?}", t1 + t2);
    }
}
