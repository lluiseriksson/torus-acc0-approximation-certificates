# Machine-Checked Exact-Rational Prime-Power Finite-Difference, Fourier-Rounding, CRT, and Periodic-Fourier NMQC Certificates for Low-Degree Torus Approximations of AND and $\mathsf{ACC}^0$

**Author:** Lluis Eriksson (prepared with transparent AI assistance via Google Antigravity)
**Target Reference:** Shuhei Osaki & Ryuhei Mori, *Low-Degree Torus Approximations of the AND Function and $\mathsf{ACC}^0$ Circuits*, `arXiv:2611.32163` (November 24, 2026).
**Licenses:** Manuscript (`paper/main.tex`, `paper/main.pdf`) under `CC-BY-4.0`; code, Lean 4 proofs, and exact certificates under `MIT`.

## Highlights
- **Zero-Dependency Lean 4 Kernel (`lean/TorusACC0.lean`, Lean 4.35.0):** 18 constructive theorems, `0` `sorry`, `0` warnings, `0` `Classical.choice`, `0` `Lean.ofReduceBool` (4 zero-axiom `none`, 1 `[propext]`, 13 `[propext, Quot.sound]`).
- **Pure-Stdlib Zero-Float Verifier (`TORUS-ACC0-CERT-1.0`, `src/torus_certifier.py`):** Four exact-$\mathbb{Q}$ modes auditing Lemma 9 prime-power finite-difference polynomials & Appendix B optimal degrees, Theorem 14 / Corollary 16 Fourier-rounding torus approximations (including explicit sub-degree $\mathrm{AND}_4, \mathrm{AND}_5, \mathrm{AND}_6$ witnesses), Lemma 11 composite-modulus CRT approximations ($m \in \{6,10,12,15\}$), and Section 7 bidirectional periodic-Fourier $\mathsf{NMQC}_\oplus \leftrightarrow$ torus degree conversions.
- **Canonical Atlas & Adversarial Audit:** 16/16 canonical certificates replayed in `0.083–3.464 ms` and **60/60 live adversarial forgery attacks rejected**.

## Quick Reproduction
```bash
# 1. Build & audit Lean 4 kernel
cd lean && lake build && lake env lean AuditAxioms.lean && cd ..

# 2. Run deterministic end-to-end verification (Lean + 16 certs + 60/60 attacks + SHA-256 manifest)
python scripts/verify_all.py

# Optional: regenerate certificates, wall-clock benchmark JSONs, and figures
python scripts/run_all_experiments.py
python scripts/make_figures.py
```
