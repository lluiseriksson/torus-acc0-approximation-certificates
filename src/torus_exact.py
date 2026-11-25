"""Pure-stdlib zero-floating-point exact-Q primitives for Paper 41:
Shuhei Osaki & Ryuhei Mori (arXiv:2611.32163, Nov 24, 2026)
"Low-Degree Torus Approximations of the AND Function and ACC^0 Circuits".

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

from fractions import Fraction
from typing import Dict, List, Sequence, Tuple

# Certified rational upper bound on pi: 355/113 = 3.14159292... > pi = 3.14159265...
PI_UPPER_Q = Fraction(355, 113)


def format_rat(q: Fraction) -> str:
    """Canonical reduced rational string ('n' if denominator == 1 else 'n/d')."""
    if q.denominator == 1:
        return str(q.numerator)
    return f"{q.numerator}/{q.denominator}"


def torus_dist_q(a: Fraction, b: Fraction) -> Fraction:
    """Exact distance ||a - b||_T = min_{z in Z} |a - b - z| in [0, 1/2]."""
    diff = a - b
    # Fractional part in [0, 1)
    q_floor = diff.numerator // diff.denominator
    frac = diff - Fraction(q_floor, 1)
    if frac <= Fraction(1, 2):
        return frac
    return Fraction(1, 1) - frac


def int_binom(z: int, j: int) -> int:
    """Exact generalized integer binomial coefficient C(z, j) for ANY z in Z and j >= 0."""
    if j < 0:
        return 0
    if j == 0:
        return 1
    num = 1
    den = 1
    for t in range(j):
        num *= (z - t)
        den *= (t + 1)
    assert num % den == 0
    return num // den


def is_prime(p: int) -> bool:
    if p < 2:
        return False
    d = 2
    while d * d <= p:
        if p % d == 0:
            return False
        d += 1
    return True


def delta_mod(m: int, z: int) -> int:
    return 1 if (z % m == 0) else 0


def lemma9_finite_diff_coeffs_exact(p: int, e: int, k: int) -> List[int]:
    """Exact Lemma 9 construction: computes a_j = (Delta^j delta_q)(0) mod p^k
    for j = 0 .. (q - 1) * k, where q = p^e."""
    q = p ** e
    mod = p ** k
    d = (q - 1) * k
    # (Delta^j f)(0) = sum_{t=0}^j (-1)^{j-t} C(j, t) f(t)
    # Use Pascal recurrence for Delta^j delta_q(0) mod p^k
    vals = [delta_mod(q, t) % mod for t in range(d + 1)]
    coeffs: List[int] = []
    cur = vals
    for _ in range(d + 1):
        coeffs.append(cur[0] % mod)
        cur = [(cur[i + 1] - cur[i]) % mod for i in range(len(cur) - 1)]
    # Trim trailing zeros to see exact degree!
    while len(coeffs) > 1 and coeffs[-1] == 0:
        coeffs.pop()
    return coeffs


def eval_lemma9_poly_q(coeffs: Sequence[int], p: int, k: int, z: int) -> Fraction:
    """Evaluate Q_{q,k}(z) = (1 / p^k) * sum_{j=0}^{len-1} coeffs[j] * C(z, j)."""
    mod = p ** k
    tot = 0
    for j, aj in enumerate(coeffs):
        if aj:
            tot += aj * int_binom(z, j)
    return Fraction(tot, mod)


def eval_multilinear_poly_q(terms: Sequence[Tuple[Tuple[int, ...], Fraction]], x: Sequence[int]) -> Fraction:
    """Evaluate multilinear polynomial sum_S alpha_S * prod_{i in S} x_i at x in {0,1}^n."""
    tot = Fraction(0, 1)
    for mon, coeff in terms:
        if all(x[idx] == 1 for idx in mon):
            tot += coeff
    return tot


def round_to_grid_q(val: Fraction, den: int) -> int:
    """Exact nearest integer c minimizing |val - c / den| (ties round to even/up deterministically)."""
    # Minimize |val * den - c| = |num / d - c|
    scaled = val * Fraction(den, 1)
    q_floor = scaled.numerator // scaled.denominator
    rem = scaled - Fraction(q_floor, 1)
    if rem * 2 >= Fraction(1, 1):
        return q_floor + 1
    return q_floor


def fourier_transform_exact_q(truth_table: Sequence[Fraction], n: int) -> Dict[int, Fraction]:
    """Exact normalized Fourier transform f_hat(gamma) = 2^{-n} sum_x f(x) (-1)^{<gamma, x>}."""
    size = 1 << n
    assert len(truth_table) == size
    out: Dict[int, Fraction] = {}
    for mask in range(size):
        acc = Fraction(0, 1)
        for x in range(size):
            par = bin(mask & x).count("1") & 1
            if par == 0:
                acc += truth_table[x]
            else:
                acc -= truth_table[x]
        val = acc / Fraction(size, 1)
        if val != 0:
            out[mask] = val
    return out


def compile_parity_torus_poly_q(
    parity_weights: Dict[int, Fraction],
    k: int,
    n: int,
) -> Dict[Tuple[int, ...], Fraction]:
    """Compile a weighted sum of parity characters sum_S beta_S (-1)^{sum_{i in S} x_i}
    into an exact multilinear torus polynomial of degree <= max(0, k - 1) by:
      1. Rounding each beta_S to nearest c_S / 2^k,
      2. Substituting exact Lemma 9 binary representation:
         (-1)^z / 2^k === (1 / 2^k) sum_{j=0}^{k-1} (-2)^j C(z, j) (mod 1),
         where for z = sum_{i in S} x_i (x_i in {0,1}), C(z, j) = sum_{T subset S, |T|=j} prod_{i in T} x_i!
    Returns canonical dict {sorted_monomial_tuple: coeff mod 1}."""
    import itertools

    den = 1 << k
    poly: Dict[Tuple[int, ...], Fraction] = {}
    for mask, beta in parity_weights.items():
        if mask == 0:
            # Constant term: keep exact beta mod 1 (no rounding needed, degree 0!)
            poly[()] = poly.get((), Fraction(0, 1)) + beta
            continue
        c_s = round_to_grid_q(beta, den)
        if c_s == 0:
            continue
        bits = [i for i in range(n) if (mask >> i) & 1]
        max_j = min(k - 1, len(bits))
        for j in range(max_j + 1):
            term_coeff = Fraction(c_s * ((-2) ** j), den)
            for sub in itertools.combinations(bits, j):
                poly[sub] = poly.get(sub, Fraction(0, 1)) + term_coeff

    # Reduce all coefficients modulo 1 into (-1/2, 1/2] and drop exact zeros
    cleaned: Dict[Tuple[int, ...], Fraction] = {}
    for mon, val in poly.items():
        q_floor = val.numerator // val.denominator
        r = val - Fraction(q_floor, 1)
        if r > Fraction(1, 2):
            r -= Fraction(1, 1)
        if r != 0:
            cleaned[mon] = r
    return cleaned
