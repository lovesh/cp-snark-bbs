mod bounds;
pub mod sum;

use ark_ff::{Field, PrimeField};
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::prelude::{AllocVar, AllocationMode, EqGadget};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_std::{cmp::Ordering, vec, vec::Vec};

#[cfg(test)]
pub mod tests {
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
    use legogroth16::LinkPublicGenerators;
    use proof_system::prelude::Proof;
    pub use proof_system::statement::{
        PedersenCommitment as PedersenCommitmentStmt, PoKBBSSignatureG1 as PoKSignatureBBSG1Stmt,
    };
    pub use proof_system::witness::PoKBBSSignatureG1 as PoKSignatureBBSG1Wit;

    pub type Fr = <Bls12_381 as PairingEngine>::Fr;
    pub type ProofG1 = Proof<Bls12_381, G1Affine, Fr, Blake2b>;

    // Generate messages, public params and signature
    pub fn sig_setup<R: RngCore>(
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

    pub fn get_link_public_gens<R: RngCore, E: PairingEngine>(
        rng: &mut R,
        count: usize,
    ) -> LinkPublicGenerators<E> {
        let pedersen_gens = (0..count)
            .map(|_| E::G1Projective::rand(rng).into_affine())
            .collect::<Vec<_>>();
        let g1 = E::G1Projective::rand(rng).into_affine();
        let g2 = E::G2Projective::rand(rng).into_affine();
        LinkPublicGenerators {
            pedersen_gens,
            g1,
            g2,
        }
    }
}
