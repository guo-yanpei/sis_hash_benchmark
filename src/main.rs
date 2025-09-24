use core::cmp::max;
use core::time;
use plonky2::field::extension::Extendable;
use plonky2::field::fft::fft_root_table;
use plonky2::field::polynomial::{PolynomialCoeffs, PolynomialValues};
use plonky2::field::types::Field;
use plonky2::fri::oracle::PolynomialBatch;
use plonky2::plonk::config::GenericHashOut;
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
use plonky2::util::timing::TimingTree;
use plonky2::util::{log2_ceil, log2_strict};
use plonky2_maybe_rayon::MaybeParIter;
use plonky2_maybe_rayon::ParallelIterator;
use sha2::{Digest, Sha256};
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::time::{Instant, SystemTime, UNIX_EPOCH};

use plonky2::fri::FriConfig;
use plonky2::fri::proof::FriChallenges;
use plonky2::fri::proof::FriProof;
use plonky2::fri::reduction_strategies::FriReductionStrategy;
use plonky2::fri::structure::FriBatchInfo;
use plonky2::fri::structure::FriInstanceInfo;
use plonky2::fri::structure::FriOpeningBatch;
use plonky2::fri::structure::FriOpenings;
use plonky2::fri::structure::FriOracleInfo;
use plonky2::fri::structure::FriPolynomialInfo;
use plonky2::fri::verifier::verify_fri_proof;
use plonky2::hash::merkle_tree::MerkleCap;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::iop::challenger::Challenger;
use plonky2_field::extension::quadratic::QuadraticExtension;
use plonky2_field::fft::FftRootTable;
use plonky2_field::goldilocks_field::GoldilocksField;
use plonky2_field::types::Field64;
use plonky2_field::types::PrimeField64;
use plonky2_field::types::Sample;

static PIXELS: usize = 30000000;
static EXPONENT: u32 = 8;
const DEGREE: usize = 1 << 25;
static PIXEL_RANGE: i32 = 2_i32.pow(EXPONENT);
static HASH_LENGTH: usize = 128;
const X: u128 = 3091352403337663489;
const A_CONSTANT: u128 = 3935559000370003845;
const C_CONSTANT: u128 = 2691343689449507681;

const D: usize = 2;
type C = PoseidonGoldilocksConfig;
type F = <C as GenericConfig<D>>::F;
const USE_ZK: bool = false;

fn print_time_since(start: u128, last: u128, tag: &str) -> u128 {
    let now = SystemTime::now();
    let now_epoc = now.duration_since(UNIX_EPOCH).expect("Time went backwards");
    let now = now_epoc.as_millis();
    println!(
        "{:?}; time since start {:?} mins; time since last check: {:?} mins",
        tag,
        (now - start) as f32 / 60000.0,
        (now - last) as f32 / 60000.0
    );
    return now;
}

fn sha256_hex_bytes(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    let digest = hasher.finalize();
    hex::encode(digest)
}

fn read_photo(prefix: &str) -> BufReader<File> {
    let file = File::open("bytes.txt").expect("Unable to open file");
    return BufReader::new(file);
}

fn get_filename(prefix: &str) -> String {
    let mut filename = prefix.to_owned();
    filename.push_str("image_");
    filename.push_str(&PIXELS.to_string());
    filename.push_str("_");
    filename.push_str(&EXPONENT.to_string());
    filename.push_str(".txt");
    return filename;
}

fn main() {
    let mut bytes = vec![];
    let file = read_photo("orig_");
    for line in file.lines() {
        let line = line.expect("Unable to read line");
        let i = line.parse::<u8>().unwrap();
        bytes.push(i);
    }
    let start = Instant::now();
    println!("{}", sha256_hex_bytes(&bytes));
    println!("sha256 time: {}ms", start.elapsed().as_millis());

    // FRI commitment constants
    let mut hash_coeffs = Vec::new();
    for i in 0..HASH_LENGTH {
        hash_coeffs.push(F::rand());
    }

    let start = SystemTime::now();
    let start_epoch = start
        .duration_since(UNIX_EPOCH)
        .expect("Time went backwards");
    let start = start_epoch.as_millis();
    let mut last = start;

    let mut x = X;
    let mut sum = F::ZERO;
    let mut hash = Vec::new();
    for _ in 0..HASH_LENGTH {
        hash.push(F::ZERO);
    }
    // Re-read in pixels
    let file = read_photo("orig_");
    for line in file.lines() {
        let line = line.expect("Unable to read line");
        let i = line.parse::<i32>().unwrap();

        let v_point = GoldilocksField(i as u64);

        let mut a_point = F::ZERO;
        for j in 0..hash_coeffs.len() {
            x = (A_CONSTANT * x + C_CONSTANT) & 0xffffffffffffffff;
            let x1 = x >> 32;
            x = (A_CONSTANT * x + C_CONSTANT) & 0xffffffffffffffff;
            let x2 = ((x & 0xffffffff00000000) + x1) & 0xffffffffffffffff;

            a_point +=
                F::from_canonical_u64(u64::try_from(x2).unwrap() % F::ORDER) * hash_coeffs[j];
            hash[j] += F::from_canonical_u64(u64::try_from(x2).unwrap() % F::ORDER) * v_point;
        }
        sum += v_point * a_point;
    }
    println!("sum: {:?}", sum);
    last = print_time_since(start, last, "first thingy done");
    let mut hash = Vec::new();
    for _ in 0..HASH_LENGTH {
        hash.push(F::ZERO);
    }

    let mut x = X;
    // Re-read in pixels
    let file = read_photo("orig_");
    for line in file.lines() {
        let line = line.expect("Unable to read line");
        let i = line.parse::<i32>().unwrap();

        let v_point = GoldilocksField(i as u64);

        let mut a_point = F::ZERO;
        for j in 0..hash_coeffs.len() {
            x = (A_CONSTANT * x + C_CONSTANT) & 0xffffffffffffffff;
            let x1 = x >> 32;
            x = (A_CONSTANT * x + C_CONSTANT) & 0xffffffffffffffff;
            let x2 = ((x & 0xffffffff00000000) + x1) & 0xffffffffffffffff;

            hash[j] += F::from_canonical_u64(u64::try_from(x2).unwrap() % F::ORDER) * v_point;
        }
    }

    let mut hash_sum = F::ZERO;
    for i in 0..HASH_LENGTH {
        hash_sum += hash[i] * hash_coeffs[i];
    }
    println!("hash_sum: {:?}", hash_sum);
    assert!(hash_sum == sum);

    //let mem = proc_status::mem_usage().unwrap();
    //println!("Mem usage in bytes: current={}, peak={}", mem.current, mem.peak);
    _ = print_time_since(start, last, "verification done");

    
}
