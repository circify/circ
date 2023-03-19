use super::*;
use rand::thread_rng;
use rand::Rng;
use rug::ops::RemRounding;

#[test]
fn inline_signed_bits() {
    assert_eq!(InlineFieldV(-2, InlineFieldTag::Bls12381).signed_bits(), 2);
    assert_eq!(InlineFieldV(1, InlineFieldTag::Bls12381).signed_bits(), 2);
    assert_eq!(
        InlineFieldV(i64::MAX, InlineFieldTag::Bls12381).signed_bits(),
        64
    );
    assert_eq!(
        InlineFieldV(i64::MIN, InlineFieldTag::Bls12381).signed_bits(),
        64
    );
    assert_eq!(
        InlineFieldV(i64::MAX / 2, InlineFieldTag::Bls12381).signed_bits(),
        63
    );
    assert_eq!(
        InlineFieldV(i64::MIN / 2, InlineFieldTag::Bls12381).signed_bits(),
        63
    );
    assert_eq!(
        InlineFieldV(i64::MAX / 2 + 1, InlineFieldTag::Bls12381).signed_bits(),
        64
    );
    assert_eq!(
        InlineFieldV(i64::MIN / 2 - 1, InlineFieldTag::Bls12381).signed_bits(),
        64
    );
}
use rug::Integer;

#[test]
fn inline_signed_bits_randomized() {
    let mut rng = thread_rng();
    for _ in 0..1024 {
        let i: i64 = rng.gen();
        let n_bits = rng.gen_range(0..64);
        let i = i % (1 << n_bits);
        let big_i = Integer::from(i);
        assert_eq!(
            InlineFieldV(i, InlineFieldTag::Bls12381).signed_bits(),
            big_i.signed_bits(),
            "wrong answer on {:b}",
            i
        )
    }
}

/// Samples a random integer with up to `max_bits` bits.
///
/// A number with `i` is chosen with probability proportional to `2^-i`.
fn random_rug_int_exp(rng: &mut impl Rng, max_bits: u32) -> Integer {
    let num_bits = rng.gen_range(1u32..max_bits);
    let mut rug_rng = rug::rand::RandState::new_mersenne_twister();
    rug_rng.seed(&Integer::from(rng.next_u64()));
    Integer::from(Integer::random_bits(num_bits, &mut rug_rng))
}

/// Sample a [FieldT] that is:
/// * Bls w/ p = 0.25
/// * Bn w/ p = 0.25
/// * An integer field otherwise
///   * with a number of bits sampled uniformly between 1..max_bits
fn sample_field_t(r: &mut impl Rng, max_bits: u32) -> FieldT {
    if r.gen_bool(0.5) {
        if r.gen_bool(0.5) {
            FieldT::FBls12381
        } else {
            FieldT::FBn254
        }
    } else {
        FieldT::IntField(Arc::new(random_rug_int_exp(r, max_bits).next_prime()))
    }
}

/// Sample a [FieldV]. If `ty` is inlinable, the value will be inline with probability 0.5.
fn sample_field_v(ty: &FieldT, r: &mut impl Rng) -> FieldV {
    if let Some(t) = ty.inline_tag() {
        if r.gen_bool(0.5) {
            let num_bits = r.gen_range(0..62);
            let i: i64 = r.gen();
            return FieldV::from(InlineFieldV(i % (1 << num_bits as i64), t));
        }
    }
    ty.new_v(random_rug_int_exp(r, ty.modulus().significant_bits()))
}

#[test]
fn random() {
    let mut rng = thread_rng();
    for _ in 0..1024 {
        let f = sample_field_t(&mut rng, 256);
        let a = sample_field_v(&f, &mut rng);
        let b = sample_field_v(&f, &mut rng);
        let a_i = a.i();
        let b_i = b.i();

        // add
        let c = a.clone() + &b;
        let c_i = (a_i.clone() + &b_i).rem_floor(f.modulus());
        assert_eq!(c.i(), c_i);

        // sub
        let c = a.clone() - &b;
        let c_i = (a_i.clone() - &b_i).rem_floor(f.modulus());
        assert_eq!(c.i(), c_i);

        // mul
        let c = a.clone() * &b;
        let c_i = (a_i.clone() * &b_i).rem_floor(f.modulus());
        assert_eq!(c.i(), c_i);

        // neg
        let c = -a.clone();
        let c_i = (-a_i.clone()).rem_floor(f.modulus());
        assert_eq!(c.i(), c_i);
    }
}
