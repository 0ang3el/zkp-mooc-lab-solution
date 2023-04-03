pragma circom 2.0.0;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////// Templates from the circomlib ////////////////////////////////
////////////////// Copy-pasted here for easy reference //////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `a` AND `b`
 */
template AND() {
    signal input a;
    signal input b;
    signal output out;

    out <== a*b;
}

/*
 * Outputs `a` OR `b`
 */
template OR() {
    signal input a;
    signal input b;
    signal output out;

    out <== a + b - a*b;
}

/*
 * `out` = `cond` ? `L` : `R`
 */
template IfThenElse() {
    signal input cond;
    signal input L;
    signal input R;
    signal output out;

    out <== cond * (L - R) + R;
}

/*
 * (`outL`, `outR`) = `sel` ? (`R`, `L`) : (`L`, `R`)
 */
template Switcher() {
    signal input sel;
    signal input L;
    signal input R;
    signal output outL;
    signal output outR;

    signal aux;

    aux <== (R-L)*sel;
    outL <==  aux + L;
    outR <== -aux + R;
}

/*
 * Decomposes `in` into `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 * Enforces that `in` is at most `b` bits long.
 */
template Num2Bits(b) {
    signal input in;
    signal output bits[b];

    for (var i = 0; i < b; i++) {
        bits[i] <-- (in >> i) & 1;
        bits[i] * (1 - bits[i]) === 0;
    }
    var sum_of_bits = 0;
    for (var i = 0; i < b; i++) {
        sum_of_bits += (2 ** i) * bits[i];
    }
    sum_of_bits === in;
}

/*
 * Reconstructs `out` from `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 */
template Bits2Num(b) {
    signal input bits[b];
    signal output out;
    var lc = 0;

    for (var i = 0; i < b; i++) {
        lc += (bits[i] * (1 << i));
    }
    out <== lc;
}

/*
 * Checks if `in` is zero and returns the output in `out`.
 */
template IsZero() {
    signal input in;
    signal output out;

    signal inv;

    inv <-- in!=0 ? 1/in : 0;

    out <== -in*inv +1;
    in*out === 0;
}

/*
 * Checks if `in[0]` == `in[1]` and returns the output in `out`.
 */
template IsEqual() {
    signal input in[2];
    signal output out;

    component isz = IsZero();

    in[1] - in[0] ==> isz.in;

    isz.out ==> out;
}

/*
 * Checks if `in[0]` < `in[1]` and returns the output in `out`.
 */
template LessThan(n) {
    assert(n <= 252);
    signal input in[2];
    signal output out;

    component n2b = Num2Bits(n+1);

    n2b.in <== in[0]+ (1<<n) - in[1];

    out <== 1-n2b.bits[n];
}

/////////////////////////////////////////////////////////////////////////////////////
///////////////////////// Templates for this lab ////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `out` = 1 if `in` is at most `b` bits long, and 0 otherwise.
 */
template CheckBitLength(b) {
    signal input in;
    signal output out;

    signal bits[b];

    for (var i = 0; i < b; i++) {
        bits[i] <-- (in >> i) & 1;
        bits[i] * (1 - bits[i]) === 0;
    }
    var sum_of_bits = 0;
    for (var i = 0; i < b; i++) {
        sum_of_bits += (2 ** i) * bits[i];
    }
    
    component isz = IsZero();

    isz.in <== sum_of_bits - in;

    out <== isz.out;
}

/*
 * Enforces the well-formedness of an exponent-mantissa pair (e, m), which is defined as follows:
 * if `e` is zero, then `m` must be zero
 * else, `e` must be at most `k` bits long, and `m` must be in the range [2^p, 2^p+1)
 */
template CheckWellFormedness(k, p) {
    signal input e;
    signal input m;

    // check if `e` is zero
    component is_e_zero = IsZero();
    is_e_zero.in <== e;

    // Case I: `e` is zero
    //// `m` must be zero
    component is_m_zero = IsZero();
    is_m_zero.in <== m;

    // Case II: `e` is nonzero
    //// `e` is `k` bits
    component check_e_bits = CheckBitLength(k);
    check_e_bits.in <== e;
    //// `m` is `p`+1 bits with the MSB equal to 1
    //// equivalent to check `m` - 2^`p` is in `p` bits
    component check_m_bits = CheckBitLength(p);
    check_m_bits.in <== m - (1 << p);

    // choose the right checks based on `is_e_zero`
    component if_else = IfThenElse();
    if_else.cond <== is_e_zero.out;
    if_else.L <== is_m_zero.out;
    //// check_m_bits.out * check_e_bits.out is equivalent to check_m_bits.out AND check_e_bits.out
    if_else.R <== check_m_bits.out * check_e_bits.out;

    // assert that those checks passed
    if_else.out === 1;
}

/*
 * Right-shifts `x` by `shift` bits to output `y`, where `shift` is a public circuit parameter.
 */
template RightShift(shift) {
    signal input x;
    signal output y;

    signal qs[shift+1];
    signal rs[shift+1];

    qs[0] <==  x;

    for (var i = 1; i < shift+1; i++) {
        qs[i] <-- qs[i-1] \ 2;
        rs[i] <== qs[i-1] - 2*qs[i];
        rs[i]*(1-rs[i]) === 0;
    }

    y <== qs[shift];
}

/*
 * Rounds the input floating-point number and checks to ensure that rounding does not make the mantissa unnormalized.
 * Rounding is necessary to prevent the bitlength of the mantissa from growing with each successive operation.
 * The input is a normalized floating-point number (e, m) with precision `P`, where `e` is a `k`-bit exponent and `m` is a `P`+1-bit mantissa.
 * The output is a normalized floating-point number (e_out, m_out) representing the same value with a lower precision `p`.
 */
template RoundAndCheck(k, p, P) {
    signal input e;
    signal input m;
    signal output e_out;
    signal output m_out;
    assert(P > p);

    // check if no overflow occurs
    component if_no_overflow = LessThan(P+1);
    if_no_overflow.in[0] <== m;
    if_no_overflow.in[1] <== (1 << (P+1)) - (1 << (P-p-1));
    signal no_overflow <== if_no_overflow.out;

    var round_amt = P-p;
    // Case I: no overflow
    // compute (m + 2^{round_amt-1}) >> round_amt
    var m_prime = m + (1 << (round_amt-1));
    component right_shift = RightShift(round_amt);
    right_shift.x <== m_prime;
    var m_out_1 = right_shift.y;
    var e_out_1 = e;

    // Case II: overflow
    var e_out_2 = e + 1;
    var m_out_2 = (1 << p);

    // select right output based on no_overflow
    component if_else[2];
    for (var i = 0; i < 2; i++) {
        if_else[i] = IfThenElse();
        if_else[i].cond <== no_overflow;
    }
    if_else[0].L <== e_out_1;
    if_else[0].R <== e_out_2;
    if_else[1].L <== m_out_1;
    if_else[1].R <== m_out_2;
    e_out <== if_else[0].out;
    m_out <== if_else[1].out;
}

/*
 * Left-shifts `x` by `shift` bits to output `y`.
 * Enforces 0 <= `shift` < `shift_bound`.
 * If `skip_checks` = 1, then we don't care about the output and the `shift_bound` constraint is not enforced.
 */
template LeftShift(shift_bound) {
    signal input x;
    signal input shift;
    signal input skip_checks;
    signal output y;

    var lc = 0;

    component zero_check[shift_bound];

    // here we emulate 1 << shift, shift is a signal
    // trick with linear combination allows to retain the soundness
    for (var i=0; i < shift_bound; i++) {
        zero_check[i] = IsZero();
        zero_check[i].in <== shift - i;

        lc += (1 << i)*zero_check[i].out;
    }

    // if shift > shift_bound => lc = 0;
    component lc_is_zero = IsZero();
    lc_is_zero.in <== lc;

    // if shift > shift_bound when skip_checks = 0 => throw exception
    lc_is_zero.out*(1 - skip_checks) === 0;

    y <== lc*x;
}

/*
 * Find the Most-Significant Non-Zero Bit (MSNZB) of `in`, where `in` is assumed to be non-zero value of `b` bits.
 * Outputs the MSNZB as a one-hot vector `one_hot` of `b` bits, where `one_hot`[i] = 1 if MSNZB(`in`) = i and 0 otherwise.
 * The MSNZB is output as a one-hot vector to reduce the number of constraints in the subsequent `Normalize` template.
 * Enforces that `in` is non-zero as MSNZB(0) is undefined.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.
 */
template MSNZB(b) {
    signal input in;
    signal input skip_checks;
    signal output one_hot[b];

    component n2b = Num2Bits(b);

    signal aux[b];

    component is_zero = IsZero();
    is_zero.in <== in;

    n2b.in <== in*(1 - skip_checks);

    // Check `in` for zero value if skip_checks=false => if `in` is zero then not satisfied constraint: 1 === 0
    (1 - skip_checks)*is_zero.out === 0;

    for (var i = b-1; i >= 0; i--) {
        var lc = 0;

        // we go forward to see if we've already found MSNZB and compute linear combination
        for (var j = i+1; j < b; j++) {
            lc += one_hot[j];
        }

        aux[i] <== lc;

        one_hot[i] <== (1 - aux[i])*n2b.bits[i];
    }
}

/*
 * Normalizes the input floating-point number.
 * The input is a floating-point number with a `k`-bit exponent `e` and a `P`+1-bit *unnormalized* mantissa `m` with precision `p`, where `m` is assumed to be non-zero.
 * The output is a floating-point number representing the same value with exponent `e_out` and a *normalized* mantissa `m_out` of `P`+1-bits and precision `P`.
 * Enforces that `m` is non-zero as a zero-value can not be normalized.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.
 */
template Normalize(k, p, P) {
    signal input e;
    signal input m;
    signal input skip_checks;
    signal output e_out;
    signal output m_out;
    assert(P > p);

    component msnzb = MSNZB(P + 1);

    msnzb.in <== m;
    msnzb.skip_checks <== skip_checks;

    var lc_m = 0;
    var lc_e = 0;

    for (var i = 0; i < P+1; i++) {
        lc_m += (P - i)*msnzb.one_hot[i];
        lc_e += (i - p)*msnzb.one_hot[i];
    }

    e_out <== e + lc_e;

    component lsh = LeftShift(P+1);
    lsh.x <== m;
    lsh.shift <== lc_m;
    lsh.skip_checks <== skip_checks;

    m_out <== lsh.y;
}

/*
 * Adds two floating-point numbers.
 * The inputs are normalized floating-point numbers with `k`-bit exponents `e` and `p`+1-bit mantissas `m` with scale `p`.
 * Does not assume that the inputs are well-formed and makes appropriate checks for the same.
 * The output is a normalized floating-point number with exponent `e_out` and mantissa `m_out` of `p`+1-bits and scale `p`.
 * Enforces that inputs are well-formed.
 */
template FloatAdd(k, p) {
    signal input e[2];
    signal input m[2];
    signal output e_out;
    signal output m_out;

    component well_formed[2]; 
    well_formed[0] = CheckWellFormedness(k, p);
    well_formed[1] = CheckWellFormedness(k, p);

    // check_well_formedness(k, p, e_1, m_1)
    well_formed[0].e <== e[0];
    well_formed[0].m <== m[0];

    // check_well_formedness(k, p, e_2, m_2)
    well_formed[1].e <== e[1];
    well_formed[1].m <== m[1];
    
    // e_1 << (p+1)
    component mgn_1_lsh = LeftShift(p+2);
    mgn_1_lsh.x <== e[0];
    mgn_1_lsh.shift <== p + 1;
    mgn_1_lsh.skip_checks <== 0;

    // e_2 << (p+1)
    component mgn_2_lsh = LeftShift(p+2);
    mgn_2_lsh.x <== e[1];
    mgn_2_lsh.shift <== p + 1;
    mgn_2_lsh.skip_checks <== 0;

    // mgn_1 > mgn_2
    component less_than_magnitude = LessThan(p+k+2);
    less_than_magnitude.in[1] <== mgn_2_lsh.y + m[1];  // mgn_2 = (e_2 << (p+1)) + m_2
    less_than_magnitude.in[0] <== mgn_1_lsh.y + m[0];  // mgn_1 = (e_1 << (p+1)) + m_1

    // choose alpha_e, betta_e
    component switcher_magnitude_e = Switcher();
    switcher_magnitude_e.sel <== less_than_magnitude.out;
    switcher_magnitude_e.L <== e[0];  // mgn_1 > mgn_2
    switcher_magnitude_e.R <== e[1];

    // choose alpha_m, betta_m
    component switcher_magnitude_m = Switcher();
    switcher_magnitude_m.sel <== less_than_magnitude.out;
    switcher_magnitude_m.L <== m[0]; //  mgn_1 > mgn_2
    switcher_magnitude_m.R <== m[1];

    // diff = alpha_e - beta_e
    signal diff <== switcher_magnitude_e.outL - switcher_magnitude_e.outR;

    // diff > p + 1
    component compare_diff = LessThan(k+1);
    compare_diff.in[0] <== p + 1;
    compare_diff.in[1] <== diff;

    // alpha_e == 0
    component iz = IsZero();
    iz.in <== switcher_magnitude_e.outL;

    // diff > p + 1 or alpha_e == 0
    component or_cond = OR();
    or_cond.a <== compare_diff.out;
    or_cond.b <== iz.out;

    // alpha_m <<= diff
    component alpha_m_lsh = LeftShift(p+2);
    alpha_m_lsh.x <== switcher_magnitude_m.outL;
    alpha_m_lsh.shift <== diff;
    alpha_m_lsh.skip_checks <== or_cond.out;
    signal alpha_m <== alpha_m_lsh.y;

    // normalize(k, p, 2*p+1, e, m)
    component normalize = Normalize(k, p, 2*p+1);
    normalize.e <== switcher_magnitude_e.outR; // beta_e
    normalize.m <== alpha_m + switcher_magnitude_m.outR;  // alpha_m + beta_m
    normalize.skip_checks <== or_cond.out;

    // round_nearest_and_check(k, p, 2*p+1, normalized_e, normalized_m)
    component round = RoundAndCheck(k, p, 2*p+1);
    round.e <== normalize.e_out;
    round.m <== normalize.m_out;

    component compute_e = IfThenElse();
    compute_e.cond <== or_cond.out;
    compute_e.L <== switcher_magnitude_e.outL;
    compute_e.R <== round.e_out;

    component compute_m = IfThenElse();
    compute_m.cond <== or_cond.out;
    compute_m.L <== switcher_magnitude_m.outL;
    compute_m.R <== round.m_out;

    e_out <== compute_e.out;
    m_out <== compute_m.out;
}
