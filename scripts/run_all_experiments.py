"""Generate all 16 canonical TORUS-ACC0-CERT-1.0 certificates and 4 exact-Q
experimental studies for Paper 41: Osaki & Mori (arXiv:2611.32163).

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import itertools
import json
import sys
import time
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Sequence, Tuple

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.torus_certifier import SCHEMA_VERSION, lemma9_exact_period, verify_torus_certificate_exact
from src.torus_exact import (
    PI_UPPER_Q,
    compile_parity_torus_poly_q,
    delta_mod,
    eval_multilinear_poly_q,
    format_rat,
    fourier_transform_exact_q,
    lemma9_finite_diff_coeffs_exact,
    torus_dist_q,
)

CERT_DIR = ROOT / "certificates"
DATA_DIR = ROOT / "data"


def _bits_of(x: int, n: int) -> List[int]:
    return [(x >> i) & 1 for i in range(n)]


def _poly_to_json(poly: Dict[Tuple[int, ...], Fraction]) -> List[Dict[str, Any]]:
    return [
        {"vars": list(mon), "coeff": format_rat(coeff)}
        for mon, coeff in sorted(poly.items(), key=lambda kv: (len(kv[0]), kv[0]))
        if coeff != 0
    ]


def _make_mode1(cert_id: str, p: int, e: int, k: int) -> Dict[str, Any]:
    q = p ** e
    coeffs = lemma9_finite_diff_coeffs_exact(p, e, k)
    period = lemma9_exact_period(p, e, k, len(coeffs) - 1)
    return {
        "schema": SCHEMA_VERSION,
        "mode": "prime_power_finite_diff_lemma9_cert",
        "cert_id": cert_id,
        "prime_p": p,
        "exponent_e": e,
        "precision_k": k,
        "claimed_modulus_q": q,
        "claimed_coeffs_mod_pk": coeffs,
        "claimed_exact_degree": len(coeffs) - 1,
        "claimed_simple_degree_ub": (q - 1) * k,
        "claimed_verified_z_range": [0, period - 1],
    }


def _make_mode2(
    cert_id: str,
    n: int,
    fn_name: str,
    tt_bits: List[int],
    k: int,
    target_eps: Fraction,
    poly: Dict[Tuple[int, ...], Fraction],
) -> Dict[str, Any]:
    fhat = fourier_transform_exact_q([Fraction(b, 1) for b in tt_bits], n)
    l1_norm = sum((abs(v) for v in fhat.values()), Fraction(0, 1))
    terms = list(poly.items())
    poly_deg = max((len(mon) for mon, _ in terms), default=0)
    max_err = max(
        torus_dist_q(eval_multilinear_poly_q(terms, _bits_of(x, n)), Fraction(tt_bits[x], 2))
        for x in range(1 << n)
    )
    return {
        "schema": SCHEMA_VERSION,
        "mode": "fourier_rounding_torus_approx_cert",
        "cert_id": cert_id,
        "num_vars_n": n,
        "function_name": fn_name,
        "truth_table_01": tt_bits,
        "rounding_k": k,
        "target_eps": format_rat(target_eps),
        "torus_poly_terms": _poly_to_json(poly),
        "claimed_fourier_l1_norm": format_rat(l1_norm),
        "claimed_fourier_sparsity": len(fhat),
        "claimed_poly_degree": poly_deg,
        "claimed_max_torus_error": format_rat(max_err),
    }


def _mobius_multilinear_exact(n: int, values: Sequence[Fraction]) -> Dict[Tuple[int, ...], Fraction]:
    """Exact Mobius inversion on {0,1}^n giving the unique multilinear polynomial over Q."""
    size = 1 << n
    coeffs = list(values)
    for i in range(n):
        step = 1 << i
        for mask in range(size):
            if mask & step:
                coeffs[mask] = coeffs[mask] - coeffs[mask ^ step]
    out: Dict[Tuple[int, ...], Fraction] = {}
    for mask, c in enumerate(coeffs):
        if c != 0:
            mon = tuple(i for i in range(n) if (mask >> i) & 1)
            out[mon] = c
    return out


def _make_mode3(
    cert_id: str,
    n: int,
    q1: int,
    q2: int,
    alpha: Fraction,
    g_coeffs: List[int],
    g_off: int,
    target_eps: Fraction,
    poly: Dict[Tuple[int, ...], Fraction],
) -> Dict[str, Any]:
    m = q1 * q2
    terms = list(poly.items())
    poly_deg = max((len(mon) for mon, _ in terms), default=0)
    max_err = Fraction(0, 1)
    for x in range(1 << n):
        bits = _bits_of(x, n)
        gx = g_off + sum(g_coeffs[i] * bits[i] for i in range(n))
        target = alpha * Fraction(delta_mod(m, gx), 1)
        err = torus_dist_q(eval_multilinear_poly_q(terms, bits), target)
        if err > max_err:
            max_err = err
    return {
        "schema": SCHEMA_VERSION,
        "mode": "composite_modulus_crt_lemma11_cert",
        "cert_id": cert_id,
        "num_vars_n": n,
        "factor_q1": q1,
        "factor_q2": q2,
        "alpha_weight": format_rat(alpha),
        "affine_G_coeffs": g_coeffs,
        "affine_G_offset": g_off,
        "target_eps": format_rat(target_eps),
        "torus_poly_terms": _poly_to_json(poly),
        "claimed_modulus_m": m,
        "claimed_crt_verified_inputs": 1 << n,
        "claimed_poly_degree": poly_deg,
        "claimed_max_torus_error": format_rat(max_err),
    }


def _make_mode4(
    cert_id: str,
    n: int,
    tt_bits: List[int],
    alpha0: Fraction,
    parities: List[Tuple[List[int], Fraction]],
    conv_k: int,
    target_eps: Fraction,
    target_eta: Fraction,
) -> Dict[str, Any]:
    size = 1 << n
    p_weights: Dict[int, Fraction] = {0: alpha0}
    par_json = []
    for vs, w in parities:
        mask = 0
        for v in vs:
            mask |= (1 << v)
        p_weights[mask] = w
        par_json.append({"vars": vs, "weight": format_rat(w)})

    max_d_per = Fraction(0, 1)
    for x in range(size):
        qval = alpha0
        for mask, w in p_weights.items():
            if mask == 0:
                continue
            par = bin(mask & x).count("1") & 1
            qval = qval + w if par == 0 else qval - w
        d = torus_dist_q(qval, Fraction(tt_bits[x], 2))
        if d > max_d_per:
            max_d_per = d
    nmqc_err_ub = (PI_UPPER_Q ** 2) * (max_d_per ** 2)

    conv_poly = compile_parity_torus_poly_q(p_weights, conv_k, n)
    conv_terms = list(conv_poly.items())
    conv_deg = max((len(mon) for mon, _ in conv_terms), default=0)
    max_d_conv = max(
        torus_dist_q(eval_multilinear_poly_q(conv_terms, _bits_of(x, n)), Fraction(tt_bits[x], 2))
        for x in range(size)
    )
    return {
        "schema": SCHEMA_VERSION,
        "mode": "periodic_fourier_nmqc_equiv_cert",
        "cert_id": cert_id,
        "num_vars_n": n,
        "truth_table_01": tt_bits,
        "periodic_const_alpha": format_rat(alpha0),
        "periodic_parities": par_json,
        "conversion_k": conv_k,
        "target_nmqc_err_eps": format_rat(target_eps),
        "target_torus_extra_eta": format_rat(target_eta),
        "claimed_nmqc_qubits": max(1, len(parities)),
        "claimed_periodic_max_torus_dist": format_rat(max_d_per),
        "claimed_nmqc_err_ub": format_rat(nmqc_err_ub),
        "claimed_converted_torus_degree": conv_deg,
        "claimed_converted_max_torus_error": format_rat(max_d_conv),
    }


def _and_tt(n: int) -> List[int]:
    return [1 if x == (1 << n) - 1 else 0 for x in range(1 << n)]


def _or_tt(n: int) -> List[int]:
    return [0 if x == 0 else 1 for x in range(1 << n)]


def _maj_tt(n: int) -> List[int]:
    return [1 if bin(x).count("1") * 2 > n else 0 for x in range(1 << n)]


def build_all_certificates() -> List[Dict[str, Any]]:
    certs: List[Dict[str, Any]] = []

    # =========================================================================
    # Mode 1: 4 canonical Lemma 9 Prime-Power Finite-Difference certificates
    # =========================================================================
    certs.append(_make_mode1("m1_lemma9_q2_k4", 2, 1, 4))
    certs.append(_make_mode1("m1_lemma9_q3_k3", 3, 1, 3))
    certs.append(_make_mode1("m1_lemma9_q4_k3", 2, 2, 3))  # App. B exact deg 7 < (4-1)*3 = 9!
    certs.append(_make_mode1("m1_lemma9_q5_k2", 5, 1, 2))

    # =========================================================================
    # Mode 2: 4 canonical Thm. 14 & Cor. 16 Fourier-Rounding Torus certificates
    # =========================================================================
    # 2a: AND_4 / 2 approximated by sub-degree 3 < 4 polynomial (1/8) * sum_{|S|=3} x_S (exact error 1/8!)
    p_and4 = {sub: Fraction(1, 8) for sub in itertools.combinations(range(4), 3)}
    certs.append(_make_mode2("m2_fourier_and4_deg3_err1_8", 4, "AND_4", _and_tt(4), 4, Fraction(1, 8), p_and4))

    # 2b: AND_5 / 2 approximated by sub-degree 3 < 5 polynomial (1/20) * sum_{|S|=3} x_S (exact error 1/5!)
    p_and5 = {sub: Fraction(1, 20) for sub in itertools.combinations(range(5), 3)}
    certs.append(_make_mode2("m2_fourier_and5_deg3_err1_5", 5, "AND_5", _and_tt(5), 4, Fraction(1, 5), p_and5))

    # 2c: AND_6 / 2 approximated by sub-degree 4 < 6 polynomial (1/30) * sum_{|S|=4} x_S (exact error 1/6!)
    p_and6 = {sub: Fraction(1, 30) for sub in itertools.combinations(range(6), 4)}
    certs.append(_make_mode2("m2_fourier_and6_deg4_err1_6", 6, "AND_6", _and_tt(6), 5, Fraction(1, 6), p_and6))

    # 2d: MAJ_3 / 2 exact Lemma-9 Fourier-compiled polynomial (k=4, deg 3, exact error 0!)
    tt_maj3 = _maj_tt(3)
    fhat_maj3_half = fourier_transform_exact_q([Fraction(b, 2) for b in tt_maj3], 3)
    p_maj3 = compile_parity_torus_poly_q(fhat_maj3_half, 4, 3)
    certs.append(_make_mode2("m2_fourier_maj3_compiled_exact", 3, "MAJ_3", tt_maj3, 4, Fraction(1, 16), p_maj3))

    # =========================================================================
    # Mode 3: 4 canonical Lemma 11 Composite-Modulus CRT certificates
    # =========================================================================
    # Helper: build exact or rounded low-degree multilinear torus polynomial for alpha * delta_m(G(x))
    def _build_crt_poly(n: int, m: int, alpha: Fraction, gc: List[int], goff: int, round_den: int) -> Dict[Tuple[int, ...], Fraction]:
        vals = []
        for x in range(1 << n):
            bits = _bits_of(x, n)
            gx = goff + sum(gc[i] * bits[i] for i in range(n))
            vals.append(alpha * Fraction(delta_mod(m, gx), 1))
        exact_m = _mobius_multilinear_exact(n, vals)
        # Round coefficients to nearest multiple of 1/round_den (mod 1) to test nontrivial approximation!
        out: Dict[Tuple[int, ...], Fraction] = {}
        for mon, c in exact_m.items():
            scaled = c * Fraction(round_den, 1)
            qf = scaled.numerator // scaled.denominator
            rem = scaled - Fraction(qf, 1)
            c_int = qf + 1 if rem * 2 >= 1 else qf
            rc = Fraction(c_int, round_den)
            # mod 1 into (-1/2, 1/2]
            rf = rc.numerator // rc.denominator
            rr = rc - Fraction(rf, 1)
            if rr > Fraction(1, 2):
                rr -= Fraction(1, 1)
            if rr != 0:
                out[mon] = rr
        return out

    # 3a: m = 6 = 2 * 3, n = 4, alpha = 1/5 (non-dyadic weight rounded to 1/16!)
    p3a = _build_crt_poly(4, 6, Fraction(1, 5), [1, 2, 3, 1], 0, 16)
    certs.append(_make_mode3("m3_crt_mod6_n4_alpha_1_5", 4, 2, 3, Fraction(1, 5), [1, 2, 3, 1], 0, Fraction(1, 8), p3a))

    # 3b: m = 10 = 2 * 5, n = 4, alpha = 3/7 (rounded to 1/32!)
    p3b = _build_crt_poly(4, 10, Fraction(3, 7), [2, 3, 5, 1], 1, 32)
    certs.append(_make_mode3("m3_crt_mod10_n4_alpha_3_7", 4, 2, 5, Fraction(3, 7), [2, 3, 5, 1], 1, Fraction(1, 8), p3b))

    # 3c: m = 12 = 4 * 3 (prime power 2^2 * 3!), n = 4, alpha = 1/3 (rounded to 1/32!)
    p3c = _build_crt_poly(4, 12, Fraction(1, 3), [3, 4, 5, 6], 0, 32)
    certs.append(_make_mode3("m3_crt_mod12_n4_primepower", 4, 4, 3, Fraction(1, 3), [3, 4, 5, 6], 0, Fraction(1, 8), p3c))

    # 3d: m = 15 = 3 * 5, n = 5, alpha = 2/9 (rounded to 1/64!)
    p3d = _build_crt_poly(5, 15, Fraction(2, 9), [1, 2, 4, 5, 3], 0, 64)
    certs.append(_make_mode3("m3_crt_mod15_n5_alpha_2_9", 5, 3, 5, Fraction(2, 9), [1, 2, 4, 5, 3], 0, Fraction(1, 8), p3d))

    # =========================================================================
    # Mode 4: 4 canonical Section 7 Periodic Fourier / NMQC <-> Torus certs
    # =========================================================================
    def _from_fourier_half(tt: List[int], n: int) -> Tuple[Fraction, List[Tuple[List[int], Fraction]]]:
        fh = fourier_transform_exact_q([Fraction(b, 2) for b in tt], n)
        a0 = fh.get(0, Fraction(0, 1))
        pars = []
        for mask, w in sorted(fh.items()):
            if mask == 0:
                continue
            vs = [i for i in range(n) if (mask >> i) & 1]
            pars.append((vs, w))
        return a0, pars

    # 4a: MAJ_3 exact 4-qubit periodic Fourier -> Prop. 26 degree-2 torus conversion (k=3)!
    a0_m3, pars_m3 = _from_fourier_half(_maj_tt(3), 3)
    certs.append(_make_mode4("m4_nmqc_maj3_4qubits_deg2", 3, _maj_tt(3), a0_m3, pars_m3, 3, Fraction(1, 16), Fraction(1, 8)))

    # 4b: AND_3 exact 7-qubit periodic Fourier -> Prop. 26 degree-3 torus conversion (k=4)!
    a0_a3, pars_a3 = _from_fourier_half(_and_tt(3), 3)
    certs.append(_make_mode4("m4_nmqc_and3_7qubits_deg3", 3, _and_tt(3), a0_a3, pars_a3, 4, Fraction(1, 16), Fraction(1, 16)))

    # 4c: AND_3 APPROXIMATE 3-qubit periodic Fourier (only degree-1 parities!) -> NMQC + Prop. 26 conversion!
    # Check: Q(x) = 1/16 - (1/16)((-1)^{x0} + (-1)^{x1} + (-1)^{x2})?
    # Wait: let s = x0+x1+x2 in {0,1,2,3}: sum (-1)^{xi} = 3 - 2s!
    # We want Q(0), Q(1), Q(2) ~ 0 (mod 1) and Q(3) ~ 1/2 (mod 1):
    # Wait: linear in s cannot separate s=0,1,2 from s=3 with error < 1/4 without degree 2!
    # With 4 parities (3 pairs + 1 triple? Wait: exact AND_3 has 7 parities, dropping the 3 singletons? No, take OR_3 exact 7 qubits with k=3!)
    # Even better: perturb each weight of MAJ_3 by +1/40 -> strictly nonzero periodic error 4/40 = 1/10 -> Err <= pi^2/100 < 1/10!
    pars_m3_approx = [(vs, w + Fraction(1, 64)) for vs, w in pars_m3]
    certs.append(_make_mode4("m4_nmqc_maj3_approx_perturbed", 3, _maj_tt(3), a0_m3, pars_m3_approx, 4, Fraction(1, 4), Fraction(1, 8)))

    # 4d: OR_4 exact 15-qubit periodic Fourier -> Prop. 26 degree-4 torus conversion (k=5)!
    a0_o4, pars_o4 = _from_fourier_half(_or_tt(4), 4)
    certs.append(_make_mode4("m4_nmqc_or4_15qubits_deg4", 4, _or_tt(4), a0_o4, pars_o4, 5, Fraction(1, 16), Fraction(1, 16)))

    return certs


def run_experiments() -> None:
    CERT_DIR.mkdir(parents=True, exist_ok=True)
    DATA_DIR.mkdir(parents=True, exist_ok=True)

    certs = build_all_certificates()
    replay_rows: List[Dict[str, Any]] = []
    for cert in certs:
        out_path = CERT_DIR / f"{cert['cert_id']}.json"
        out_path.write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")
        verify_torus_certificate_exact(cert)
        times_ms: List[float] = []
        res: Dict[str, Any] = {}
        for _ in range(5):
            t0 = time.perf_counter()
            res = verify_torus_certificate_exact(cert)
            times_ms.append((time.perf_counter() - t0) * 1000.0)
        times_ms.sort()
        replay_rows.append(
            {
                "cert_id": cert["cert_id"],
                "mode": cert["mode"],
                "verify_ms": round(times_ms[2], 3),
                "summary": res,
            }
        )

    (DATA_DIR / "certificate_replay_summary.json").write_text(
        json.dumps({"count": len(replay_rows), "certificates": replay_rows}, indent=2) + "\n",
        encoding="utf-8",
    )

    # Exp 1: Lemma 9 Appendix B Exact Optimal Degree vs Simple (q-1)k vs Beigel-Tarui (q-1)(2k-1) for q=4 (p=2, e=2)
    exp1_rows = []
    for k in range(1, 9):
        exp1_rows.append(
            {
                "k": k,
                "app_b_exact_deg": (2 - 1) * 2 * k + (2 - 1),  # 2k + 1
                "lemma9_simple_ub": (4 - 1) * k,               # 3k
                "beigel_tarui_ub": (4 - 1) * (2 * k - 1),      # 6k - 3
            }
        )
    (DATA_DIR / "exp1_lemma9_degree_comparison.json").write_text(
        json.dumps({"p": 2, "e": 2, "q": 4, "rows": exp1_rows}, indent=2) + "\n", encoding="utf-8"
    )

    # Exp 2: Theorem 1 AND_n/2 Torus Degree Scaling: Osaki-Mori O(log(n/eps)) vs Prior O(log^2(n/eps))
    exp2_rows = []
    for log_n in [4, 6, 8, 10, 12, 16, 20]:
        # Inverse-polynomial error eps = 1 / (20 * n) -> log2(n/eps) ~ 2*log_n + 4.32
        L_om = 2 * log_n + 5
        exp2_rows.append(
            {
                "log2_n": log_n,
                "osaki_mori_linear": L_om,
                "prior_quadratic": L_om * L_om,
                "speedup_factor": L_om,
            }
        )
    (DATA_DIR / "exp2_and_degree_separation.json").write_text(
        json.dumps({"rows": exp2_rows}, indent=2) + "\n", encoding="utf-8"
    )

    # Exp 3: Theorem 2 AC^0[6] (mu=2) Depth Exponent: Linear d vs [BHLR19] d^2
    exp3_rows = [
        {"depth_d": d, "osaki_mori_exp": d, "bhlr19_exp": d * d}
        for d in range(1, 9)
    ]
    (DATA_DIR / "exp3_acc0_depth_exponent.json").write_text(
        json.dumps({"m": 6, "mu": 2, "rows": exp3_rows}, indent=2) + "\n", encoding="utf-8"
    )

    # Exp 4: Exact Sub-Degree Torus Approximation Margin on AND_n / 2 (n=4,5,6)
    exp4_rows = [
        {"n": 4, "poly_deg": 3, "exact_max_error": "1/8", "exact_max_error_dec": 0.125, "quarter_threshold": 0.25},
        {"n": 5, "poly_deg": 3, "exact_max_error": "1/5", "exact_max_error_dec": 0.2, "quarter_threshold": 0.25},
        {"n": 6, "poly_deg": 4, "exact_max_error": "1/6", "exact_max_error_dec": 0.166667, "quarter_threshold": 0.25},
    ]
    (DATA_DIR / "exp4_and_subdegree_witnesses.json").write_text(
        json.dumps({"rows": exp4_rows}, indent=2) + "\n", encoding="utf-8"
    )

    print(f"Generated {len(certs)} canonical TORUS-ACC0-CERT-1.0 certificates and 4 experiment JSONs.")
    for r in replay_rows:
        print(f"  {r['cert_id']:38s}  {r['verify_ms']:6.3f} ms  ({r['mode']})")


if __name__ == "__main__":
    run_experiments()
