//! Gadget and chips for the [SHA-256] hash function.
//!
//! [SHA-256]: https://tools.ietf.org/html/rfc6234

use std::cmp::min;
use std::convert::TryInto;
use std::fmt;

use crate::{table16::lebs2ip, BlockWord};
use halo2wrong::halo2::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Chip, Layouter, Value},
    plonk::Error,
};

// use crate::{BlockWord, Table16Chip, Table16Config};

/// The size of a SHA-256 block, in 32-bit words.
pub const BLOCK_SIZE: usize = 16;
/// The size of a SHA-256 digest, in 32-bit words.
pub(crate) const DIGEST_SIZE: usize = 8;

/// The set of circuit instructions required to use the [`Sha256`] gadget.
pub trait Sha256Instructions<F: FieldExt>: Chip<F> {
    /// Variable representing the SHA-256 internal state.
    type State: Clone + fmt::Debug;
    /// Variable representing a 32-bit word of the input block to the SHA-256 compression
    /// function.
    type BlockWord: Copy + fmt::Debug + Default + From<u32>;

    /// Places the SHA-256 IV in the circuit, returning the initial state variable.
    fn initialization_vector(&self, layouter: &mut impl Layouter<F>) -> Result<Self::State, Error>;

    /// Creates an initial state from the output state of a previous block
    fn initialization(
        &self,
        layouter: &mut impl Layouter<F>,
        init_state: &Self::State,
    ) -> Result<Self::State, Error>;

    /// Starting from the given initialized state, processes a block of input and returns the
    /// final state.
    fn compress(
        &self,
        layouter: &mut impl Layouter<F>,
        initialized_state: &Self::State,
        input: [Self::BlockWord; BLOCK_SIZE],
    ) -> Result<Self::State, Error>;

    /// Converts the given state into a message digest.
    fn digest(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &Self::State,
    ) -> Result<[Self::BlockWord; DIGEST_SIZE], Error>;

    /*
    /// Converts the given state into a message digest.
    fn digest_cells(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &Self::State,
    ) -> Result<[AssignedCell<F, F>; DIGEST_SIZE], Error>;*/
}

/// The output of a SHA-256 circuit invocation.
#[derive(Debug)]
pub struct Sha256Digest<BlockWord>(pub [BlockWord; DIGEST_SIZE]);

/// A gadget that constrains a SHA-256 invocation. It supports input at a granularity of
/// 32 bits.
#[derive(Debug)]
pub struct Sha256<F: FieldExt, CS: Sha256Instructions<F>> {
    chip: CS,
    state: CS::State,
    cur_block: Vec<CS::BlockWord>,
    length: usize,
}

impl<F: FieldExt, Sha256Chip: Sha256Instructions<F>> Sha256<F, Sha256Chip> {
    /// Create a new hasher instance.
    pub fn new(chip: Sha256Chip, mut layouter: impl Layouter<F>) -> Result<Self, Error> {
        let state = chip.initialization_vector(&mut layouter)?;
        Ok(Sha256 {
            chip,
            state,
            cur_block: Vec::with_capacity(BLOCK_SIZE),
            length: 0,
        })
    }

    /// Digest data, updating the internal state.
    pub fn update(
        &mut self,
        mut layouter: impl Layouter<F>,
        mut data: &[Sha256Chip::BlockWord],
    ) -> Result<(), Error> {
        self.length += data.len() * 32;

        // Fill the current block, if possible.
        let remaining = BLOCK_SIZE - self.cur_block.len();
        let (l, r) = data.split_at(min(remaining, data.len()));
        self.cur_block.extend_from_slice(l);
        data = r;

        // If we still don't have a full block, we are done.
        if self.cur_block.len() < BLOCK_SIZE {
            return Ok(());
        }

        // Process the now-full current block.
        self.state = self.chip.compress(
            &mut layouter,
            &self.state,
            self.cur_block[..]
                .try_into()
                .expect("cur_block.len() == BLOCK_SIZE"),
        )?;
        self.cur_block.clear();

        // Process any additional full blocks.
        let mut chunks_iter = data.chunks_exact(BLOCK_SIZE);
        for chunk in &mut chunks_iter {
            self.state = self.chip.initialization(&mut layouter, &self.state)?;
            self.state = self.chip.compress(
                &mut layouter,
                &self.state,
                chunk.try_into().expect("chunk.len() == BLOCK_SIZE"),
            )?;
        }

        // Cache the remaining partial block, if any.
        let rem = chunks_iter.remainder();
        self.cur_block.extend_from_slice(rem);

        Ok(())
    }

    /*
    /// Retrieve result and consume hasher instance.
    pub fn finalize(
        mut self,
        mut layouter: impl Layouter<F>,
    ) -> Result<[AssignedCell<F, F>; DIGEST_SIZE], Error> {
        // Pad the remaining block
        let is_next_block = (self.cur_block.len() * 32 + 65) > (32 * BLOCK_SIZE);
        let num_cur_block_words = if is_next_block {
            BLOCK_SIZE - self.cur_block.len()
        } else {
            BLOCK_SIZE - self.cur_block.len() - 2
        };
        let num_next_block_words = if is_next_block { BLOCK_SIZE - 2 } else { 0 };
        let mut input_len_bits1 = [false; 32];
        let mut input_len_bits2 = [false; 32];
        for i in 0..64 {
            let bit = (self.length >> (63 - i)) & 1 == 1;
            if i < 32 {
                input_len_bits1[i] = bit;
            } else {
                input_len_bits2[i - 32] = bit;
            }
        }
        //input_len_bits1.reverse();
        //input_len_bits2.reverse();
        //println!("input_len_bits2 {:?}", input_len_bits2);
        let input_len_padding_1 = Sha256Chip::BlockWord::from(lebs2ip(&input_len_bits1) as u32);
        let input_len_padding_2 = Sha256Chip::BlockWord::from(lebs2ip(&input_len_bits2) as u32);
        let mut padding = Vec::new();
        if is_next_block {
            padding.append(&mut vec![
                Sha256Chip::BlockWord::from(0);
                num_cur_block_words
            ]);
            padding.push(Sha256Chip::BlockWord::from(1));
            padding.append(&mut vec![
                Sha256Chip::BlockWord::from(0);
                num_next_block_words - 1
            ]);
            padding.push(input_len_padding_1);
            padding.push(input_len_padding_2);
        } else {
            padding.push(Sha256Chip::BlockWord::from(1));
            padding.append(&mut vec![
                Sha256Chip::BlockWord::from(0);
                num_cur_block_words - 1
            ]);
            padding.push(input_len_padding_1);
            padding.push(input_len_padding_2);
        };

        self.cur_block.extend_from_slice(&padding);
        /*for block in self.cur_block.iter() {
            println!("input {:?}", block);
        }*/
        self.state = self.chip.initialization(&mut layouter, &self.state)?;
        self.state = self.chip.compress(
            &mut layouter,
            &self.state,
            self.cur_block[..]
                .try_into()
                .expect("cur_block.len() == BLOCK_SIZE"),
        )?;

        /*if !self.cur_block.is_empty() {
            self.cur_block.extend_from_slice(&padding);
            for block in self.cur_block.iter() {
                println!("input {:?}", block);
            }
            self.state = self.chip.initialization(&mut layouter, &self.state)?;
            self.state = self.chip.compress(
                &mut layouter,
                &self.state,
                self.cur_block[..]
                    .try_into()
                    .expect("cur_block.len() == BLOCK_SIZE"),
            )?;
        } else {
            padding.push(Sha256Chip::BlockWord::from(1));
            padding.append(&mut vec![
                Sha256Chip::BlockWord::from(0);
                num_next_block_words - 1
            ]);
        }*/
        /*if is_next_block {
            let num_next_block_words = if is_next_block { BLOCK_SIZE - 2 } else { 0 };
            let mut padding = Vec::with_capacity(BLOCK_SIZE);
            padding.push(Sha256Chip::BlockWord::from(1));
            padding.append(&mut vec![
                Sha256Chip::BlockWord::default();
                num_next_block_words - 1
            ]);
            padding.push(input_len_padding_1);
            padding.push(input_len_padding_2);

            self.cur_block.extend_from_slice(&padding);
            self.state = self.chip.initialization(&mut layouter, &self.state)?;
            self.state = self.chip.compress(
                &mut layouter,
                &self.state,
                self.cur_block[..]
                    .try_into()
                    .expect("cur_block.len() == BLOCK_SIZE"),
            )?;
        }*/

        //self.chip.digest_cells(&mut layouter, &self.state)
    }*/

    /*
    /// Convenience function to compute hash of the data. It will handle hasher creation,
    /// data feeding and finalization.
    pub fn digest(
        chip: Sha256Chip,
        mut layouter: impl Layouter<F>,
        data: &[Sha256Chip::BlockWord],
    ) -> Result<[AssignedCell<F, F>; DIGEST_SIZE], Error> {
        let mut hasher = Self::new(chip, layouter.namespace(|| "init"))?;
        hasher.update(layouter.namespace(|| "update"), data)?;
        hasher.finalize(layouter.namespace(|| "finalize"))
    }*/
}
/*
#[cfg(test)]
mod test {
    use crate::table16::*;
    use std::marker::PhantomData;

    use super::*;
    use halo2wrong::curves::pasta::pallas;
    use halo2wrong::halo2::plonk::Advice;
    use halo2wrong::halo2::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        plonk::{
            create_proof, keygen_pk, keygen_vk, verify_proof, Circuit, Column, ConstraintSystem,
            Error, Instance,
        },
        poly::commitment::Params,
        transcript::{Blake2bRead, Blake2bWrite, Challenge255},
    };
    use halo2wrong::utils::fe_to_big;
    use rand::rngs::OsRng;

    struct TestCircuit<F: FieldExt> {
        test_input: Vec<BlockWord>,
        _f: PhantomData<F>,
    }

    #[derive(Clone)]
    struct TestConfig {
        output_advice: Column<Advice>,
        instance: Column<Instance>,
        table16_config: Table16Config,
    }

    impl<F: FieldExt> Circuit<F> for TestCircuit<F> {
        type Config = TestConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            unimplemented!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let output_advice = meta.advice_column();
            let instance = meta.instance_column();
            meta.enable_equality(output_advice);
            meta.enable_equality(instance);
            let table16_config = Table16Chip::configure(meta);
            Self::Config {
                output_advice,
                instance,
                table16_config,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            Table16Chip::load(config.table16_config.clone(), &mut layouter)?;
            let table16_chip = Table16Chip::<F>::construct(config.clone().table16_config);
            let output = Sha256::digest(
                table16_chip,
                layouter.namespace(|| "'abc' * 2"),
                &self.test_input,
            )?;
            /*let mut output_cells = Vec::new();
            layouter.assign_region(
                || "expose sha256 outputs",
                |mut region| {
                    for (i, word) in output.0.iter().enumerate() {
                        word.0.map(|v| println!("output {}", v));
                        let assigned_cell = region.assign_advice(
                            || format!("{} th output advice", i),
                            config.clone().output_advice,
                            i,
                            || word.0.map(|v| F::from(1 as u64)),
                        )?;
                        output_cells.push(assigned_cell);
                    }
                    Ok(())
                },
            )?;*/
            for (i, cell) in output.iter().enumerate() {
                //cell.value().map(|v| println!("output {:?}", v));
                layouter.constrain_instance(cell.cell(), config.instance, i)?;
            }
            Ok(())
        }
    }

    #[test]
    fn test_sha256_correct1() {
        use halo2wrong::curves::pasta::pallas::Base;
        use halo2wrong::halo2::dev::MockProver;

        // ANCHOR: test-circuit
        // The number of rows in our circuit cannot exceed 2^k. Since our example
        // circuit is very small, we can pick a very small value here.
        let k = 18;

        // Prepare the private and public inputs to the circuit!
        let test_input = vec![];

        // Instantiate the circuit with the private inputs.
        let circuit = TestCircuit::<Base> {
            test_input,
            _f: PhantomData,
        };
        let test_output = [
            Base::from(206920545),
            Base::from(2058853055),
            Base::from(2833460027),
            Base::from(3032324940),
            Base::from(2444571389),
            Base::from(1853071663),
            Base::from(2113299747),
            Base::from(2174712695),
        ];

        // Arrange the public input. We expose the multiplication result in row 0
        // of the instance column, so we position it there in our public inputs.
        let public_inputs = vec![test_output.to_vec()];

        // Given the correct public input, our circuit will verify.
        let prover = MockProver::run(k, &circuit, public_inputs).unwrap();
        assert_eq!(prover.verify(), Ok(()));

        // If we try some other public input, the proof will fail!
        /*public_inputs[0] += Fr::one();
        let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();
        assert!(prover.verify().is_err());*/
    }
}
*/
