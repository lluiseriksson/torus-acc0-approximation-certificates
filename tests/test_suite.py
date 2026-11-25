"""Comprehensive pytest & 60-attack live adversarial red-team suite for Paper 41:
TORUS-ACC0-CERT-1.0 (Osaki & Mori, arXiv:2611.32163).

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import copy
import json
import sys
from pathlib import Path
from typing import Any, Callable, Dict, List, Tuple

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.torus_certifier import TorusCertificateError, verify_torus_certificate_exact

CERT_DIR = ROOT / "certificates"


def _load(name: str) -> Dict[str, Any]:
    return json.loads((CERT_DIR / f"{name}.json").read_text(encoding="utf-8"))


def test_all_16_canonical_certificates_verify() -> None:
    paths = sorted(CERT_DIR.glob("*.json"))
    assert len(paths) == 16, f"Expected 16 certificates, found {len(paths)}"
    for p in paths:
        res = verify_torus_certificate_exact(json.loads(p.read_text(encoding="utf-8")))
        assert res["verified"] is True


def _mut(base: Dict[str, Any], fn: Callable[[Dict[str, Any]], None]) -> Dict[str, Any]:
    c = copy.deepcopy(base)
    fn(c)
    return c


def build_60_adversarial_attacks() -> List[Tuple[str, Any]]:
    m1 = _load("m1_lemma9_q4_k3")
    m2 = _load("m2_fourier_and4_deg3_err1_8")
    m3 = _load("m3_crt_mod6_n4_alpha_1_5")
    m4 = _load("m4_nmqc_maj3_approx_perturbed")

    attacks: List[Tuple[str, Any]] = [
        # --- Global Schema / Type / Rational Hardening (12 attacks) ---
        ("g01_non_dict_root", [1, 2, 3]),
        ("g02_wrong_schema", _mut(m1, lambda c: c.__setitem__("schema", "TORUS-ACC0-CERT-2.0"))),
        ("g03_empty_cert_id", _mut(m1, lambda c: c.__setitem__("cert_id", ""))),
        ("g04_unknown_mode", _mut(m1, lambda c: c.__setitem__("mode", "bogus"))),
        ("g05_float_leak", _mut(m2, lambda c: c.__setitem__("target_eps", 0.125))),
        ("g06_none_injection", _mut(m1, lambda c: c.__setitem__("prime_p", None))),
        ("g07_bool_as_int", _mut(m1, lambda c: c.__setitem__("exponent_e", True))),
        ("g08_unreduced_fraction", _mut(m2, lambda c: c.__setitem__("target_eps", "2/16"))),
        ("g09_den_one_fraction", _mut(m2, lambda c: c.__setitem__("claimed_fourier_l1_norm", "1/1"))),
        ("g10_neg_zero_rat", _mut(m2, lambda c: c["torus_poly_terms"][0].__setitem__("coeff", "-0"))),
        ("g11_oversized_rat_str", _mut(m2, lambda c: c.__setitem__("target_eps", "1/" + "9" * 1200))),
        ("g12_huge_int_bitlen", _mut(m1, lambda c: c.__setitem__("precision_k", 1 << 3000))),
        # --- Mode 1: Lemma 9 Prime-Power Finite-Difference Polynomial (12 attacks) ---
        ("m1_01_extra_key", _mut(m1, lambda c: c.__setitem__("extra", 1))),
        ("m1_02_composite_p", _mut(m1, lambda c: c.__setitem__("prime_p", 4))),
        ("m1_03_p_too_small", _mut(m1, lambda c: c.__setitem__("prime_p", 1))),
        ("m1_04_e_zero", _mut(m1, lambda c: c.__setitem__("exponent_e", 0))),
        ("m1_05_k_zero", _mut(m1, lambda c: c.__setitem__("precision_k", 0))),
        ("m1_06_q_too_large", _mut(m1, lambda c: c.__setitem__("exponent_e", 4))),
        ("m1_07_wrong_q", _mut(m1, lambda c: c.__setitem__("claimed_modulus_q", 6))),
        ("m1_08_wrong_coeff", _mut(m1, lambda c: c["claimed_coeffs_mod_pk"].__setitem__(0, 0))),
        ("m1_09_truncated_coeffs", _mut(m1, lambda c: c["claimed_coeffs_mod_pk"].pop())),
        ("m1_10_wrong_exact_deg", _mut(m1, lambda c: c.__setitem__("claimed_exact_degree", 9))),
        ("m1_11_wrong_simple_ub", _mut(m1, lambda c: c.__setitem__("claimed_simple_degree_ub", 7))),
        ("m1_12_wrong_z_range", _mut(m1, lambda c: c.__setitem__("claimed_verified_z_range", [0, 16]))),
        # --- Mode 2: Thm. 14 & Cor. 16 Fourier-Rounding Torus Approx (12 attacks) ---
        ("m2_01_extra_key", _mut(m2, lambda c: c.__setitem__("extra", 1))),
        ("m2_02_eps_quarter", _mut(m2, lambda c: c.__setitem__("target_eps", "1/4"))),
        ("m2_03_tt_wrong_len", _mut(m2, lambda c: c["truth_table_01"].pop())),
        ("m2_04_tt_non_binary", _mut(m2, lambda c: c["truth_table_01"].__setitem__(0, 2))),
        ("m2_05_degree_exceeds_k_minus_1", _mut(m2, lambda c: c.__setitem__("rounding_k", 3))),
        ("m2_06_error_exceeds_eps", _mut(m2, lambda c: c.__setitem__("target_eps", "1/16"))),
        ("m2_07_unsorted_monomial_vars", _mut(m2, lambda c: c["torus_poly_terms"][0].__setitem__("vars", [2, 1, 0]))),
        ("m2_08_duplicate_monomial", _mut(m2, lambda c: c["torus_poly_terms"].append(copy.deepcopy(c["torus_poly_terms"][0])))),
        ("m2_09_wrong_l1_norm", _mut(m2, lambda c: c.__setitem__("claimed_fourier_l1_norm", "2"))),
        ("m2_10_wrong_sparsity", _mut(m2, lambda c: c.__setitem__("claimed_fourier_sparsity", 15))),
        ("m2_11_wrong_poly_deg", _mut(m2, lambda c: c.__setitem__("claimed_poly_degree", 4))),
        ("m2_12_wrong_max_err", _mut(m2, lambda c: c.__setitem__("claimed_max_torus_error", "0"))),
        # --- Mode 3: Lemma 11 Composite-Modulus CRT Approximation (12 attacks) ---
        ("m3_01_extra_key", _mut(m3, lambda c: c.__setitem__("extra", 1))),
        ("m3_02_non_coprime_factors", _mut(m3, lambda c: (c.__setitem__("factor_q1", 4), c.__setitem__("factor_q2", 6)))),
        ("m3_03_eps_half", _mut(m3, lambda c: c.__setitem__("target_eps", "1/2"))),
        ("m3_04_g_coeffs_len_mismatch", _mut(m3, lambda c: c["affine_G_coeffs"].pop())),
        ("m3_05_error_exceeds_eps", _mut(m3, lambda c: c.__setitem__("target_eps", "1/1000"))),
        ("m3_06_corrupted_poly_coeff", _mut(m3, lambda c: c["torus_poly_terms"][0].__setitem__("coeff", "1/2"))),
        ("m3_07_var_out_of_range", _mut(m3, lambda c: c["torus_poly_terms"][0].__setitem__("vars", [9]))),
        ("m3_08_wrong_mod_m", _mut(m3, lambda c: c.__setitem__("claimed_modulus_m", 12))),
        ("m3_09_wrong_verified_inputs", _mut(m3, lambda c: c.__setitem__("claimed_crt_verified_inputs", 8))),
        ("m3_10_wrong_poly_deg", _mut(m3, lambda c: c.__setitem__("claimed_poly_degree", 0))),
        ("m3_11_wrong_max_err", _mut(m3, lambda c: c.__setitem__("claimed_max_torus_error", "0"))),
        ("m3_12_n_too_small", _mut(m3, lambda c: c.__setitem__("num_vars_n", 1))),
        # --- Mode 4: Sec. 7 Periodic Fourier / NMQC <-> Torus Equivalence (12 attacks) ---
        ("m4_01_extra_key", _mut(m4, lambda c: c.__setitem__("extra", 1))),
        ("m4_02_empty_parities", _mut(m4, lambda c: c.__setitem__("periodic_parities", []))),
        ("m4_03_empty_parity_vars", _mut(m4, lambda c: c["periodic_parities"][0].__setitem__("vars", []))),
        ("m4_04_duplicate_parity_mask", _mut(m4, lambda c: c["periodic_parities"].append(copy.deepcopy(c["periodic_parities"][0])))),
        ("m4_05_zero_parity_weight", _mut(m4, lambda c: c["periodic_parities"][0].__setitem__("weight", "0"))),
        ("m4_06_nmqc_err_exceeds_eps", _mut(m4, lambda c: c.__setitem__("target_nmqc_err_eps", "1/1000"))),
        ("m4_07_prop26_eta_violated", _mut(m4, lambda c: (c.__setitem__("conversion_k", 1), c.__setitem__("target_torus_extra_eta", "1/1000")))),
        ("m4_08_wrong_qubits", _mut(m4, lambda c: c.__setitem__("claimed_nmqc_qubits", 3))),
        ("m4_09_wrong_per_dist", _mut(m4, lambda c: c.__setitem__("claimed_periodic_max_torus_dist", "0"))),
        ("m4_10_wrong_nmqc_ub", _mut(m4, lambda c: c.__setitem__("claimed_nmqc_err_ub", "0"))),
        ("m4_11_wrong_conv_deg", _mut(m4, lambda c: c.__setitem__("claimed_converted_torus_degree", 9))),
        ("m4_12_wrong_conv_err", _mut(m4, lambda c: c.__setitem__("claimed_converted_max_torus_error", "1/8"))),
    ]
    assert len(attacks) == 60
    return attacks


def test_60_live_adversarial_attacks_rejected() -> None:
    attacks = build_60_adversarial_attacks()
    rejected = 0
    for name, payload in attacks:
        try:
            verify_torus_certificate_exact(payload)
        except TorusCertificateError:
            rejected += 1
        else:
            raise AssertionError(f"Adversarial attack {name!r} was NOT rejected!")
    assert rejected == 60


def test_exact_no_float_source_audit() -> None:
    for rel in ["src/torus_exact.py", "src/torus_certifier.py"]:
        src = (ROOT / rel).read_text(encoding="utf-8")
        assert "float(" not in src, f"float() found in {rel}"
        assert "math." not in src, f"math. found in {rel}"
        assert "numpy" not in src, f"numpy found in {rel}"
