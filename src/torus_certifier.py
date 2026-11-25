"""Zero-floating-point exact-Q certificate verifier: TORUS-ACC0-CERT-1.0.
Audits all four algebraic, Fourier, CRT, and quantum NMQC pillars of
Shuhei Osaki & Ryuhei Mori (arXiv:2611.32163, Nov 24, 2026)
"Low-Degree Torus Approximations of the AND Function and ACC^0 Circuits":
  - Mode 1: prime_power_finite_diff_lemma9_cert (Lemma 9 Q_{q,k}(z) === delta_q(z)/p^k mod 1 & App. B degree)
  - Mode 2: fourier_rounding_torus_approx_cert (Thm. 14 & Cor. 16 AND_n/2 & Boolean cube torus approx)
  - Mode 3: composite_modulus_crt_lemma11_cert (Lemma 11 CRT delta_m(G(x)) factorization & torus approx)
  - Mode 4: periodic_fourier_nmqc_equiv_cert (Sec. 7 Props. 23, 25, 26 NMQC_oplus <-> Torus equivalence)

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import re
from fractions import Fraction
from typing import Any, Dict, List, Set, Tuple

from src.torus_exact import (
    PI_UPPER_Q,
    compile_parity_torus_poly_q,
    delta_mod,
    eval_lemma9_poly_q,
    eval_multilinear_poly_q,
    format_rat,
    fourier_transform_exact_q,
    is_prime,
    lemma9_finite_diff_coeffs_exact,
    torus_dist_q,
)

SCHEMA_VERSION = "TORUS-ACC0-CERT-1.0"
_CANON_INT_RE = re.compile(r"\A(0|-?[1-9][0-9]*)\Z")
_CANON_FRAC_RE = re.compile(r"\A-?[1-9][0-9]*/[1-9][0-9]*\Z")
MAX_RAT_STR_LEN = 1024
MAX_INT_BITS = 2048
MAX_ID_LEN = 128


def _gcd_int(a: int, b: int) -> int:
    a, b = abs(a), abs(b)
    while b:
        a, b = b, a % b
    return a


class TorusCertificateError(ValueError):
    """Raised whenever a TORUS-ACC0-CERT-1.0 certificate fails any invariant."""


def _assert_strict_json_types(obj: Any, path: str = "$") -> None:
    t = type(obj)
    if t is int:
        if obj.bit_length() > MAX_INT_BITS:
            raise TorusCertificateError(f"Integer bit-length > {MAX_INT_BITS} at {path}")
        return
    if t is str or t is bool:
        return
    if t is list:
        for i, v in enumerate(obj):
            _assert_strict_json_types(v, f"{path}[{i}]")
        return
    if t is dict:
        for k, v in obj.items():
            if type(k) is not str:
                raise TorusCertificateError(f"Non-string dict key at {path}")
            _assert_strict_json_types(v, f"{path}.{k}")
        return
    raise TorusCertificateError(f"Forbidden JSON type {t.__name__} at {path}")


def _parse_int(val: Any, name: str) -> int:
    if type(val) is not int:
        raise TorusCertificateError(f"{name} must be strict int, got {type(val).__name__}")
    if val.bit_length() > MAX_INT_BITS:
        raise TorusCertificateError(f"{name} integer too large")
    return val


def _parse_rat(val: Any, name: str) -> Fraction:
    if type(val) is int:
        if val.bit_length() > MAX_INT_BITS:
            raise TorusCertificateError(f"{name} integer too large")
        return Fraction(val, 1)
    if type(val) is str:
        if len(val) > MAX_RAT_STR_LEN:
            raise TorusCertificateError(f"{name} rational string too long")
        if _CANON_INT_RE.match(val):
            iv = int(val)
            if iv.bit_length() > MAX_INT_BITS:
                raise TorusCertificateError(f"{name} integer bit-length > {MAX_INT_BITS}")
            return Fraction(iv, 1)
        if _CANON_FRAC_RE.match(val):
            num_s, den_s = val.split("/")
            num, den = int(num_s), int(den_s)
            if num.bit_length() > MAX_INT_BITS or den.bit_length() > MAX_INT_BITS:
                raise TorusCertificateError(f"{name} rational bit-length > {MAX_INT_BITS}")
            if den < 2:
                raise TorusCertificateError(f"{name} denominator must be >= 2: {val!r}")
            q = Fraction(num, den)
            if q.numerator != num or q.denominator != den:
                raise TorusCertificateError(f"{name} unreduced fraction: {val!r}")
            return q
        raise TorusCertificateError(f"{name} non-canonical rational string: {val!r}")
    raise TorusCertificateError(f"{name} invalid type {type(val).__name__}")


def _parse_exact_keys(cert: Dict[str, Any], req: Set[str], mode: str) -> None:
    keys = set(cert.keys())
    if keys != req:
        raise TorusCertificateError(f"{mode} key mismatch: {sorted(keys ^ req)}")


def _parse_poly_terms(raw: Any, n: int, name: str) -> List[Tuple[Tuple[int, ...], Fraction]]:
    if type(raw) is not list or len(raw) > 512:
        raise TorusCertificateError(f"{name} must be list of length <= 512")
    terms: List[Tuple[Tuple[int, ...], Fraction]] = []
    seen: Set[Tuple[int, ...]] = set()
    for idx, item in enumerate(raw):
        if type(item) is not dict or set(item.keys()) != {"vars", "coeff"}:
            raise TorusCertificateError(f"{name}[{idx}] schema mismatch")
        rv = item["vars"]
        if type(rv) is not list:
            raise TorusCertificateError(f"{name}[{idx}].vars must be list")
        vs = [_parse_int(v, f"{name}[{idx}].vars") for v in rv]
        if vs != sorted(vs) or len(set(vs)) != len(vs) or any(not (0 <= v < n) for v in vs):
            raise TorusCertificateError(f"{name}[{idx}].vars must be strictly increasing indices in [0, {n-1}]")
        key = tuple(vs)
        if key in seen:
            raise TorusCertificateError(f"Duplicate monomial {key} in {name}")
        seen.add(key)
        c = _parse_rat(item["coeff"], f"{name}[{idx}].coeff")
        terms.append((key, c))
    return terms


def _bits_of(x: int, n: int) -> List[int]:
    return [(x >> i) & 1 for i in range(n)]


# =============================================================================
# Mode 1: Lemma 9 Prime-Power Finite-Difference Torus Polynomial Q_{q,k}(z)
# =============================================================================


def _verify_mode1_prime_power(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema",
        "mode",
        "cert_id",
        "prime_p",
        "exponent_e",
        "precision_k",
        "claimed_modulus_q",
        "claimed_coeffs_mod_pk",
        "claimed_exact_degree",
        "claimed_simple_degree_ub",
        "claimed_verified_z_range",
    }
    _parse_exact_keys(cert, req, "Mode 1")
    p = _parse_int(cert["prime_p"], "prime_p")
    e = _parse_int(cert["exponent_e"], "exponent_e")
    k = _parse_int(cert["precision_k"], "precision_k")
    if not is_prime(p) or not (2 <= p <= 7) or not (1 <= e <= 3) or not (1 <= k <= 6):
        raise TorusCertificateError("Require prime p in [2,7], e in [1,3], k in [1,6]")
    q = p ** e
    if q > 9:
        raise TorusCertificateError("Require q = p^e <= 9 for fast exact audit")

    exact_coeffs = lemma9_finite_diff_coeffs_exact(p, e, k)
    exact_deg = len(exact_coeffs) - 1
    app_b_deg = (p - 1) * (p ** (e - 1)) * k + (p ** (e - 1)) - 1
    simple_ub = (q - 1) * k
    if exact_deg != app_b_deg or exact_deg > simple_ub:
        raise TorusCertificateError(f"Lemma 9 degree mismatch: got {exact_deg}, App. B {app_b_deg}, ub {simple_ub}")

    # Independently verify Q_{q,k}(z) - delta_q(z) / p^k in Z over [-2q, 4q] (both negative & positive z!)
    z_lo, z_hi = -2 * q, 4 * q
    mod = p ** k
    for z in range(z_lo, z_hi + 1):
        val = eval_lemma9_poly_q(exact_coeffs, p, k, z)
        target = Fraction(delta_mod(q, z), mod)
        if torus_dist_q(val, target) != Fraction(0, 1):
            raise TorusCertificateError(f"Lemma 9 congruence failed at z={z}: Q={val}, target={target}")

    if _parse_int(cert["claimed_modulus_q"], "claimed_modulus_q") != q:
        raise TorusCertificateError("claimed_modulus_q mismatch")
    raw_c = cert["claimed_coeffs_mod_pk"]
    if type(raw_c) is not list or len(raw_c) != len(exact_coeffs) or [_parse_int(v, "coeff") for v in raw_c] != exact_coeffs:
        raise TorusCertificateError("claimed_coeffs_mod_pk mismatch")
    if _parse_int(cert["claimed_exact_degree"], "claimed_exact_degree") != exact_deg:
        raise TorusCertificateError("claimed_exact_degree mismatch")
    if _parse_int(cert["claimed_simple_degree_ub"], "claimed_simple_degree_ub") != simple_ub:
        raise TorusCertificateError("claimed_simple_degree_ub mismatch")
    if cert["claimed_verified_z_range"] != [z_lo, z_hi]:
        raise TorusCertificateError("claimed_verified_z_range mismatch")

    return {
        "verified": True,
        "mode": cert["mode"],
        "q": q,
        "k": k,
        "exact_degree": exact_deg,
        "simple_ub": simple_ub,
    }


# =============================================================================
# Mode 2: Theorem 14 & Corollary 16 Fourier-Rounding Torus Approximation
# =============================================================================


def _verify_mode2_fourier_rounding(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema",
        "mode",
        "cert_id",
        "num_vars_n",
        "function_name",
        "truth_table_01",
        "rounding_k",
        "target_eps",
        "torus_poly_terms",
        "claimed_fourier_l1_norm",
        "claimed_fourier_sparsity",
        "claimed_poly_degree",
        "claimed_max_torus_error",
    }
    _parse_exact_keys(cert, req, "Mode 2")
    n = _parse_int(cert["num_vars_n"], "num_vars_n")
    fn_name = cert["function_name"]
    if type(fn_name) is not str or not (1 <= len(fn_name) <= MAX_ID_LEN):
        raise TorusCertificateError(f"function_name must be string of length in [1, {MAX_ID_LEN}]")
    k = _parse_int(cert["rounding_k"], "rounding_k")
    if not (2 <= n <= 6) or not (1 <= k <= 10):
        raise TorusCertificateError("Require 2 <= n <= 6 and 1 <= k <= 10")
    eps = _parse_rat(cert["target_eps"], "target_eps")
    if not (Fraction(0, 1) < eps < Fraction(1, 4)):
        raise TorusCertificateError("Require 0 < target_eps < 1/4")

    raw_tt = cert["truth_table_01"]
    size = 1 << n
    if type(raw_tt) is not list or len(raw_tt) != size:
        raise TorusCertificateError(f"truth_table_01 must have length 2^n={size}")
    tt_bits = [_parse_int(v, "truth_table") for v in raw_tt]
    if any(b not in (0, 1) for b in tt_bits):
        raise TorusCertificateError("truth_table_01 entries must be in {0, 1}")

    # Compute exact Fourier transform of f (values in {0, 1}) and f/2
    tt_f = [Fraction(b, 1) for b in tt_bits]
    fhat = fourier_transform_exact_q(tt_f, n)
    l1_norm = sum((abs(v) for v in fhat.values()), Fraction(0, 1))
    sparsity = len(fhat)

    # Parse supplied torus polynomial and verify degree <= max(0, k - 1) and error <= eps on ALL 2^n inputs!
    terms = _parse_poly_terms(cert["torus_poly_terms"], n, "torus_poly_terms")
    poly_deg = max((len(mon) for mon, _ in terms), default=0)
    if poly_deg > max(0, k - 1):
        raise TorusCertificateError(f"Torus polynomial degree {poly_deg} exceeds k - 1 = {k - 1}")

    max_err = Fraction(0, 1)
    for x in range(size):
        bits = _bits_of(x, n)
        pval = eval_multilinear_poly_q(terms, bits)
        target = Fraction(tt_bits[x], 2)
        err = torus_dist_q(pval, target)
        if err > max_err:
            max_err = err
    if max_err > eps:
        raise TorusCertificateError(f"Max torus error {max_err} exceeds target_eps={eps}")

    if _parse_rat(cert["claimed_fourier_l1_norm"], "claimed_fourier_l1_norm") != l1_norm:
        raise TorusCertificateError(f"claimed_fourier_l1_norm mismatch: exact={l1_norm}")
    if _parse_int(cert["claimed_fourier_sparsity"], "claimed_fourier_sparsity") != sparsity:
        raise TorusCertificateError("claimed_fourier_sparsity mismatch")
    if _parse_int(cert["claimed_poly_degree"], "claimed_poly_degree") != poly_deg:
        raise TorusCertificateError("claimed_poly_degree mismatch")
    if _parse_rat(cert["claimed_max_torus_error"], "claimed_max_torus_error") != max_err:
        raise TorusCertificateError(f"claimed_max_torus_error mismatch: exact={max_err}")

    return {
        "verified": True,
        "mode": cert["mode"],
        "n": n,
        "l1_norm": format_rat(l1_norm),
        "poly_deg": poly_deg,
        "max_error": format_rat(max_err),
    }


# =============================================================================
# Mode 3: Lemma 11 Composite-Modulus CRT Approximation alpha * delta_m(G(x))
# =============================================================================


def _verify_mode3_crt_composite(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema",
        "mode",
        "cert_id",
        "num_vars_n",
        "factor_q1",
        "factor_q2",
        "alpha_weight",
        "affine_G_coeffs",
        "affine_G_offset",
        "target_eps",
        "torus_poly_terms",
        "claimed_modulus_m",
        "claimed_crt_verified_inputs",
        "claimed_poly_degree",
        "claimed_max_torus_error",
    }
    _parse_exact_keys(cert, req, "Mode 3")
    n = _parse_int(cert["num_vars_n"], "num_vars_n")
    q1 = _parse_int(cert["factor_q1"], "factor_q1")
    q2 = _parse_int(cert["factor_q2"], "factor_q2")
    if not (2 <= n <= 5) or not (2 <= q1 <= 7) or not (2 <= q2 <= 7):
        raise TorusCertificateError("Require 2 <= n <= 5 and factors in [2, 7]")
    if _gcd_int(q1, q2) != 1:
        raise TorusCertificateError(f"CRT factors q1={q1}, q2={q2} are not coprime")
    m = q1 * q2

    alpha = _parse_rat(cert["alpha_weight"], "alpha_weight")
    eps = _parse_rat(cert["target_eps"], "target_eps")
    if not (Fraction(0, 1) < eps < Fraction(1, 2)):
        raise TorusCertificateError("Require 0 < target_eps < 1/2")

    raw_g = cert["affine_G_coeffs"]
    if type(raw_g) is not list or len(raw_g) != n:
        raise TorusCertificateError(f"affine_G_coeffs must have length {n}")
    g_coeffs = [_parse_int(v, "affine_G_coeffs") for v in raw_g]
    g_off = _parse_int(cert["affine_G_offset"], "affine_G_offset")

    terms = _parse_poly_terms(cert["torus_poly_terms"], n, "torus_poly_terms")
    poly_deg = max((len(mon) for mon, _ in terms), default=0)

    # Verify CRT identity delta_m(G(x)) == delta_{q1}(G(x)) * delta_{q2}(G(x)) and
    # ||R(x) - alpha * delta_m(G(x))||_T <= eps on ALL 2^n Boolean inputs!
    size = 1 << n
    max_err = Fraction(0, 1)
    for x in range(size):
        bits = _bits_of(x, n)
        gx = g_off + sum(g_coeffs[i] * bits[i] for i in range(n))
        dm = delta_mod(m, gx)
        if dm != delta_mod(q1, gx) * delta_mod(q2, gx):
            raise TorusCertificateError(f"CRT failed at x={x}")
        target = alpha * Fraction(dm, 1)
        pval = eval_multilinear_poly_q(terms, bits)
        err = torus_dist_q(pval, target)
        if err > max_err:
            max_err = err
    if max_err > eps:
        raise TorusCertificateError(f"CRT torus error {max_err} > target_eps={eps}")

    if _parse_int(cert["claimed_modulus_m"], "claimed_modulus_m") != m:
        raise TorusCertificateError("claimed_modulus_m mismatch")
    if _parse_int(cert["claimed_crt_verified_inputs"], "claimed_crt_verified_inputs") != size:
        raise TorusCertificateError("claimed_crt_verified_inputs mismatch")
    if _parse_int(cert["claimed_poly_degree"], "claimed_poly_degree") != poly_deg:
        raise TorusCertificateError("claimed_poly_degree mismatch")
    if _parse_rat(cert["claimed_max_torus_error"], "claimed_max_torus_error") != max_err:
        raise TorusCertificateError(f"claimed_max_torus_error mismatch: exact={max_err}")

    return {
        "verified": True,
        "mode": cert["mode"],
        "modulus_m": m,
        "poly_deg": poly_deg,
        "max_error": format_rat(max_err),
    }


# =============================================================================
# Mode 4: Section 7 Periodic Fourier / NMQC_oplus <-> Torus Degree Equivalence
# =============================================================================


def _verify_mode4_nmqc_equiv(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema",
        "mode",
        "cert_id",
        "num_vars_n",
        "truth_table_01",
        "periodic_const_alpha",
        "periodic_parities",
        "conversion_k",
        "target_nmqc_err_eps",
        "target_torus_extra_eta",
        "claimed_nmqc_qubits",
        "claimed_periodic_max_torus_dist",
        "claimed_nmqc_err_ub",
        "claimed_converted_torus_degree",
        "claimed_converted_max_torus_error",
    }
    _parse_exact_keys(cert, req, "Mode 4")
    n = _parse_int(cert["num_vars_n"], "num_vars_n")
    conv_k = _parse_int(cert["conversion_k"], "conversion_k")
    if not (2 <= n <= 5) or not (1 <= conv_k <= 10):
        raise TorusCertificateError("Require 2 <= n <= 5 and 1 <= conversion_k <= 10")
    eps = _parse_rat(cert["target_nmqc_err_eps"], "target_nmqc_err_eps")
    eta = _parse_rat(cert["target_torus_extra_eta"], "target_torus_extra_eta")
    if not (Fraction(0, 1) < eps < Fraction(1, 2)) or not (Fraction(0, 1) < eta < Fraction(1, 4)):
        raise TorusCertificateError("Invalid eps / eta ranges")

    size = 1 << n
    raw_tt = cert["truth_table_01"]
    if type(raw_tt) is not list or len(raw_tt) != size:
        raise TorusCertificateError(f"truth_table_01 must have length {size}")
    tt_bits = [_parse_int(v, "truth_table") for v in raw_tt]
    if any(b not in (0, 1) for b in tt_bits):
        raise TorusCertificateError("truth_table_01 entries must be in {0, 1}")

    alpha0 = _parse_rat(cert["periodic_const_alpha"], "periodic_const_alpha")
    raw_par = cert["periodic_parities"]
    if type(raw_par) is not list or not (1 <= len(raw_par) <= 64):
        raise TorusCertificateError("periodic_parities must have length in [1, 64]")

    parity_weights: Dict[int, Fraction] = {0: alpha0}
    seen_masks: Set[int] = set()
    for idx, item in enumerate(raw_par):
        if type(item) is not dict or set(item.keys()) != {"vars", "weight"}:
            raise TorusCertificateError(f"periodic_parities[{idx}] schema mismatch")
        rv = item["vars"]
        if type(rv) is not list or not rv:
            raise TorusCertificateError(f"periodic_parities[{idx}].vars must be non-empty list")
        vs = [_parse_int(v, f"par[{idx}].vars") for v in rv]
        if vs != sorted(vs) or len(set(vs)) != len(vs) or any(not (0 <= v < n) for v in vs):
            raise TorusCertificateError(f"periodic_parities[{idx}].vars invalid")
        mask = 0
        for v in vs:
            mask |= (1 << v)
        if mask in seen_masks:
            raise TorusCertificateError(f"Duplicate parity subset in periodic_parities[{idx}]")
        seen_masks.add(mask)
        w = _parse_rat(item["weight"], f"par[{idx}].weight")
        if w == 0:
            raise TorusCertificateError(f"Zero weight in periodic_parities[{idx}]")
        parity_weights[mask] = w

    r_sparsity = len(seen_masks)
    qubits = max(1, r_sparsity)

    # Evaluate Q(x) = alpha + sum_S beta_S (-1)^{<S, x>} over all 2^n inputs
    # Fact 19: Err(f/2, Q) = sin^2(pi * d_T) <= (355/113)^2 * d_T^2 <= eps!
    max_d_per = Fraction(0, 1)
    for x in range(size):
        qval = alpha0
        for mask in seen_masks:
            par = bin(mask & x).count("1") & 1
            if par == 0:
                qval += parity_weights[mask]
            else:
                qval -= parity_weights[mask]
        d = torus_dist_q(qval, Fraction(tt_bits[x], 2))
        if d > max_d_per:
            max_d_per = d
    nmqc_err_ub = (PI_UPPER_Q ** 2) * (max_d_per ** 2)
    if nmqc_err_ub > eps:
        raise TorusCertificateError(f"NMQC error upper bound {nmqc_err_ub} > target_eps={eps}")

    # Proposition 26 constructive conversion: compile periodic Fourier polynomial into
    # degree <= conv_k - 1 torus polynomial Q_tilde and verify total error <= max_d_per + eta < 1/4!
    conv_poly = compile_parity_torus_poly_q(parity_weights, conv_k, n)
    conv_terms = list(conv_poly.items())
    conv_deg = max((len(mon) for mon, _ in conv_terms), default=0)
    max_d_conv = Fraction(0, 1)
    for x in range(size):
        bits = _bits_of(x, n)
        pval = eval_multilinear_poly_q(conv_terms, bits)
        d = torus_dist_q(pval, Fraction(tt_bits[x], 2))
        if d > max_d_conv:
            max_d_conv = d
    if max_d_conv > max_d_per + eta or max_d_conv >= Fraction(1, 4):
        raise TorusCertificateError(
            f"Converted torus error {max_d_conv} failed Prop. 26 bound (<= {max_d_per + eta} and < 1/4)"
        )

    if _parse_int(cert["claimed_nmqc_qubits"], "claimed_nmqc_qubits") != qubits:
        raise TorusCertificateError("claimed_nmqc_qubits mismatch")
    if _parse_rat(cert["claimed_periodic_max_torus_dist"], "claimed_periodic_max_torus_dist") != max_d_per:
        raise TorusCertificateError("claimed_periodic_max_torus_dist mismatch")
    if _parse_rat(cert["claimed_nmqc_err_ub"], "claimed_nmqc_err_ub") != nmqc_err_ub:
        raise TorusCertificateError("claimed_nmqc_err_ub mismatch")
    if _parse_int(cert["claimed_converted_torus_degree"], "claimed_converted_torus_degree") != conv_deg:
        raise TorusCertificateError("claimed_converted_torus_degree mismatch")
    if _parse_rat(cert["claimed_converted_max_torus_error"], "claimed_converted_max_torus_error") != max_d_conv:
        raise TorusCertificateError("claimed_converted_max_torus_error mismatch")

    return {
        "verified": True,
        "mode": cert["mode"],
        "qubits": qubits,
        "nmqc_err_ub": format_rat(nmqc_err_ub),
        "conv_deg": conv_deg,
        "conv_max_err": format_rat(max_d_conv),
    }


def verify_torus_certificate_exact(cert: Dict[str, Any]) -> Dict[str, Any]:
    """Top-level zero-float entry point for TORUS-ACC0-CERT-1.0."""
    if type(cert) is not dict:
        raise TorusCertificateError("Certificate root must be a JSON object")
    _assert_strict_json_types(cert)
    if cert.get("schema") != SCHEMA_VERSION:
        raise TorusCertificateError(f"Unsupported schema: {cert.get('schema')!r}")
    cid = cert.get("cert_id")
    if type(cid) is not str or not (1 <= len(cid) <= MAX_ID_LEN):
        raise TorusCertificateError(f"cert_id must be string of length in [1, {MAX_ID_LEN}]")
    mode = cert.get("mode")
    if mode == "prime_power_finite_diff_lemma9_cert":
        return _verify_mode1_prime_power(cert)
    if mode == "fourier_rounding_torus_approx_cert":
        return _verify_mode2_fourier_rounding(cert)
    if mode == "composite_modulus_crt_lemma11_cert":
        return _verify_mode3_crt_composite(cert)
    if mode == "periodic_fourier_nmqc_equiv_cert":
        return _verify_mode4_nmqc_equiv(cert)
    raise TorusCertificateError(f"Unknown verification mode: {mode!r}")
