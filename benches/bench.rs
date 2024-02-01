use criterion::{black_box, criterion_group, criterion_main, Criterion};
use halo2_rsa::big_integer::{BigIntChip, BigIntConfig, BigIntInstructions, UnassignedInteger};
use halo2wrong::{
    curves::FieldExt,
    halo2::{
        circuit::SimpleFloorPlanner,
        plonk::{
            create_proof, keygen_pk, keygen_vk, verify_proof, Advice, Circuit, Column,
            ConstraintSystem, Error, Fixed, Instance, ProvingKey, VerifyingKey,
        },
        poly::{
            commitment::{CommitmentScheme, Params, ParamsProver},
            kzg::{
                commitment::{KZGCommitmentScheme, ParamsKZG},
                multiopen::{ProverGWC, VerifierGWC},
                strategy::{AccumulatorStrategy, SingleStrategy},
            },
        },
        transcript::{
            Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
        },
    },
};
use maingate::{
    decompose_big, MainGate, MainGateInstructions, RangeChip, RangeInstructions, RegionCtx,
};
use num_bigint::{BigUint, RandomBits};
use rand::rngs::OsRng;
use std::{
    fs::File,
    io::{BufReader, Read, Write},
    marker::PhantomData,
    path::Path,
    str::FromStr,
};

use halo2wrong::curves::bn256::{Bn256, Fr, G1Affine};
use halo2wrong::halo2::dev::MockProver;
use rand::{thread_rng, Rng};
use rsa::{Hash, PaddingScheme, PublicKeyParts, RsaPrivateKey, RsaPublicKey};
use sha2::{Digest, Sha256};

struct TestBigMulModCircuit<F: FieldExt> {
    a: BigUint,
    b: BigUint,
    n: BigUint,
    _f: PhantomData<F>,
}

impl<F: FieldExt> TestBigMulModCircuit<F> {
    const LIMB_WIDTH: usize = 64;
    const BITS_LEN: usize = 2048;
    fn bigint_chip(&self, config: BigIntConfig) -> BigIntChip<F> {
        BigIntChip::new(config, Self::LIMB_WIDTH, Self::BITS_LEN)
    }
}

impl<F: FieldExt> Circuit<F> for TestBigMulModCircuit<F> {
    type Config = BigIntConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        unimplemented!();
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let main_gate_config = MainGate::<F>::configure(meta);
        let (composition_bit_lens, overflow_bit_lens) = BigIntChip::<F>::compute_range_lens(
            Self::LIMB_WIDTH,
            Self::BITS_LEN / Self::LIMB_WIDTH,
        );
        let range_config = RangeChip::<F>::configure(
            meta,
            &main_gate_config,
            composition_bit_lens,
            overflow_bit_lens,
        );
        BigIntConfig::new(range_config, main_gate_config)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl halo2wrong::halo2::circuit::Layouter<F>,
    ) -> Result<(), Error> {
        let bigint_chip = self.bigint_chip(config);
        let num_limbs = Self::BITS_LEN / Self::LIMB_WIDTH;
        layouter.assign_region(
            || "a * b = ab mod n",
            |region| {
                let offset = 0;
                let ctx = &mut RegionCtx::new(region, offset);
                let c = (self.a.clone() * self.b.clone()) % self.n.clone();
                let a_limbs = decompose_big::<F>(self.a.clone(), num_limbs, Self::LIMB_WIDTH);
                let a_unassigned = UnassignedInteger::from(a_limbs);
                let a_assigned = bigint_chip.assign_integer(ctx, a_unassigned)?;
                let b_limbs = decompose_big::<F>(self.b.clone(), num_limbs, Self::LIMB_WIDTH);
                let b_unassigned = UnassignedInteger::from(b_limbs);
                let b_assigned = bigint_chip.assign_integer(ctx, b_unassigned)?;
                let c_limbs = decompose_big::<F>(c.clone(), num_limbs, Self::LIMB_WIDTH);
                let c_unassigned = UnassignedInteger::from(c_limbs);
                let c_assigned = bigint_chip.assign_integer(ctx, c_unassigned)?;
                let n_limbs = decompose_big::<F>(self.n.clone(), num_limbs, Self::LIMB_WIDTH);
                let n_unassigned = UnassignedInteger::from(n_limbs);
                let n_assigned = bigint_chip.assign_integer(ctx, n_unassigned)?;
                let ab = bigint_chip.mul_mod(ctx, &a_assigned, &b_assigned, &n_assigned)?;
                bigint_chip.assert_equal_fresh(ctx, &ab, &c_assigned)?;
                Ok(())
            },
        )?;
        let range_chip = bigint_chip.range_chip();
        range_chip.load_table(&mut layouter)?;
        Ok(())
    }
}

impl<F: FieldExt> Default for TestBigMulModCircuit<F> {
    fn default() -> Self {
        let mut rng = thread_rng();
        let bits_len = TestBigMulModCircuit::<Fr>::BITS_LEN as u64;
        let mut n = BigUint::default();
        while n.bits() != bits_len {
            n = rng.sample(RandomBits::new(bits_len));
        }
        let a = rng.sample::<BigUint, _>(RandomBits::new(bits_len)) % &n;
        let b = rng.sample::<BigUint, _>(RandomBits::new(bits_len)) % &n;
        Self {
            a,
            b,
            n,
            _f: PhantomData,
        }
    }
}

fn setup() -> (
    ParamsKZG<Bn256>,
    VerifyingKey<G1Affine>,
    ProvingKey<G1Affine>,
) {
    let circuit = TestBigMulModCircuit::<Fr>::default();
    let k = 14;
    let params = ParamsKZG::<Bn256>::setup(k, OsRng);
    let vk = keygen_vk(&params, &circuit).unwrap();
    let pk = keygen_pk(&params, vk.clone(), &circuit).unwrap();
    (params, vk, pk)
}

fn prove_and_verify(
    params: &ParamsKZG<Bn256>,
    vk: &VerifyingKey<G1Affine>,
    pk: &ProvingKey<G1Affine>,
) {
    let mut rng = thread_rng();
    let bits_len = TestBigMulModCircuit::<Fr>::BITS_LEN as u64;
    let mut n = BigUint::default();
    while n.bits() != bits_len {
        n = rng.sample(RandomBits::new(bits_len));
    }
    let a = rng.sample::<BigUint, _>(RandomBits::new(bits_len)) % &n;
    let b = rng.sample::<BigUint, _>(RandomBits::new(bits_len)) % &n;

    // Define circuit
    let circuit = TestBigMulModCircuit::<Fr> {
        a,
        b,
        n,
        _f: PhantomData,
    };

    // Set public inputs
    let column0_public_inputs = vec![];

    // Generate a proof
    let proof = {
        let mut transcript = Blake2bWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);
        create_proof::<KZGCommitmentScheme<_>, ProverGWC<_>, _, _, _, _>(
            params,
            pk,
            &[circuit],
            &[&[&column0_public_inputs]],
            OsRng,
            &mut transcript,
        )
        .unwrap();
        transcript.finalize()
    };
    // Verify the proof
    {
        let strategy = SingleStrategy::new(&params);
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
        assert!(verify_proof::<_, VerifierGWC<_>, _, _, _>(
            params,
            vk,
            strategy,
            &[&[&column0_public_inputs]],
            &mut transcript
        )
        .is_ok());
    }
}

fn bench_bigmulmod(c: &mut Criterion) {
    let (params_64, vk_64, pk_64) = setup();
    let mut group = c.benchmark_group("big integer multiplication");
    group.sample_size(10);
    group.bench_function("message 64 bytes", |b| {
        b.iter(|| prove_and_verify(&params_64, &vk_64, &pk_64))
    });
    group.finish();
}

criterion_group!(benches, bench_bigmulmod,);
criterion_main!(benches);
