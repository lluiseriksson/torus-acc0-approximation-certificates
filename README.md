# Machine-Checked Algebraic Kernel and Exact-Rational Certificates for Prime-Power Finite Differences, Fourier Rounding, CRT, and Periodic-Fourier $\mathsf{NMQC}_\oplus$ Torus Approximations

**Author:** Lluis Eriksson (prepared with transparent AI assistance via Google Antigravity)
**Target Reference:** Shuhei Osaki & Ryuhei Mori, *Low-Degree Torus Approximations of the AND Function and $\mathsf{ACC}^0$ Circuits*, `arXiv:2611.32163` (November 24, 2026).
**Licenses:** Manuscript (`paper/main.tex`, `paper/main.pdf`) under `CC-BY-4.0`; code, Lean 4 proofs, and exact certificates under `MIT`.

## Highlights (`v2.0.0`)
- **Zero-Dependency Lean 4 Kernel (`lean/TorusACC0.lean`, Lean 4.35.0):** 18 constructive theorems, `0` `sorry`, `0` warnings, `0` `Classical.choice`, `0` `Lean.ofReduceBool` (3 zero-axiom `none`, 1 `[propext]`, 14 `[propext, Quot.sound]`), including universal `q = 2, k = 3` Lemma 9 mod-8 congruence for all `z : Nat`, universal coprime CRT factorization `deltaMod (q1 * q2) z = deltaMod q1 z * deltaMod q2 z` for all `Nat.gcd q1 q2 = 1`, strict Beigel–Tarui degree domination for `k >= 2`, and explicit scope calibration.
- **Pure-Stdlib Zero-Float Verifier (`TORUS-ACC0-CERT-1.0`, `src/torus_certifier.py`):** Four exact-$\mathbb{Q}$ modes auditing full-period `[0, P - 1]` ($P = p^{\max(e, k + v_p(d!))}$) Lemma 9 prime-power finite-difference polynomials (mathematically certifying Eq. (1) for EVERY integer $z \in \mathbb{Z}$), Theorem 14 / Corollary 16 Fourier-rounding torus approximations (explicit sub-degree $\mathrm{AND}_4, \mathrm{AND}_5, \mathrm{AND}_6$ witnesses), Lemma 11 composite-modulus CRT approximations ($m \in \{6,10,12,15\}$), and Section 7 bidirectional periodic-Fourier $\mathsf{NMQC}_\oplus \leftrightarrow$ torus degree conversions.
- **Canonical Atlas & Adversarial Audit:** 16/16 canonical certificates replayed in `0.129–3.911 ms` and **60/60 live adversarial forgery attacks rejected**.

## Quick Reproduction
```bash
# 1. Build & audit Lean 4 kernel
cd lean && lake build && lake env lean -j 1 AuditAxioms.lean && cd ..

# 2. Run deterministic end-to-end verification (Lean + 16 certs + 60/60 attacks + SHA-256 manifest)
python scripts/verify_all.py

# Optional: regenerate certificates, wall-clock benchmark JSONs, and figures
python scripts/run_all_experiments.py
python scripts/make_figures.py
```
