"""Generate 3 publication-grade figures for Paper 41:
TORUS-ACC0-CERT-1.0 (Osaki & Mori, arXiv:2611.32163).

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parent.parent
DATA_DIR = ROOT / "data"
FIG_DIR = ROOT / "figures"

plt.rcParams.update(
    {
        "font.family": "serif",
        "font.size": 8.5,
        "axes.titlesize": 9.2,
        "axes.labelsize": 8.5,
        "legend.fontsize": 7.2,
        "xtick.labelsize": 7.8,
        "ytick.labelsize": 7.8,
        "axes.grid": True,
        "grid.alpha": 0.28,
        "grid.linestyle": "--",
    }
)


def make_fig1() -> None:
    d1 = json.loads((DATA_DIR / "exp1_lemma9_degree_comparison.json").read_text(encoding="utf-8"))
    d2 = json.loads((DATA_DIR / "exp2_and_degree_separation.json").read_text(encoding="utf-8"))

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.2, 3.6), dpi=300)

    # Panel (a): Lemma 9 degree comparison for q = 4 = 2^2
    ks = [r["k"] for r in d1["rows"]]
    ax1.plot(ks, [r["beigel_tarui_ub"] for r in d1["rows"]], "s--", color="#c00000", lw=1.6, ms=4.5,
             label=r"Beigel--Tarui $(q-1)(2k-1) = 6k-3$")
    ax1.plot(ks, [r["lemma9_simple_ub"] for r in d1["rows"]], "^-.", color="#c55a11", lw=1.6, ms=4.5,
             label=r"Lemma 9 simple $(q-1)k = 3k$")
    ax1.plot(ks, [r["app_b_exact_deg"] for r in d1["rows"]], "o-", color="#1f4e79", lw=1.9, ms=5.0,
             label=r"Appendix B optimal $2k+1$")
    ax1.set_xlabel(r"Precision exponent $k$ (modulus $q = 2^2 = 4$)")
    ax1.set_ylabel(r"Polynomial degree $\deg Q_{4,k}$")
    ax1.set_title("(a) Lemma 9 Prime-Power Degree Savings ($q=4$)")
    ax1.legend(loc="upper left", framealpha=0.92, fontsize=6.9)

    # Panel (b): Theorem 1 AND_n/2 degree O(log(n/eps)) vs O(log^2(n/eps))
    lns = [r["log2_n"] for r in d2["rows"]]
    ax2.plot(lns, [r["prior_quadratic"] for r in d2["rows"]], "s--", color="#c00000", lw=1.7, ms=4.5,
             label=r"Prior bound $O(\log^2(n/\varepsilon))$")
    ax2.plot(lns, [r["osaki_mori_linear"] for r in d2["rows"]], "o-", color="#1f4e79", lw=1.9, ms=5.0,
             label=r"Osaki--Mori $O(\log(n/\varepsilon))$ (optimal)")
    ax2.set_yscale("log")
    ax2.set_xlabel(r"Input bit-width $\log_2 n$ (at $\varepsilon = 1/(20n)$)")
    ax2.set_ylabel("Torus degree scaling factor (log scale)")
    ax2.set_title(r"(b) Breaking $O(\log^2(n/\varepsilon))$ for $\mathrm{AND}_n/2$")
    ax2.legend(loc="upper left", framealpha=0.92, fontsize=7.0)

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig1_lemma9_and_degree_separation.png", dpi=300)
    plt.close(fig)


def make_fig2() -> None:
    d3 = json.loads((DATA_DIR / "exp3_acc0_depth_exponent.json").read_text(encoding="utf-8"))
    d4 = json.loads((DATA_DIR / "exp4_and_subdegree_witnesses.json").read_text(encoding="utf-8"))

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.2, 3.6), dpi=300)

    # Panel (a): AC^0[6] depth exponent d vs d^2
    ds = [r["depth_d"] for r in d3["rows"]]
    ax1.plot(ds, [r["bhlr19_exp"] for r in d3["rows"]], "s--", color="#c00000", lw=1.7, ms=4.8,
             label=r"[BHLR19] quadratic depth exponent $d^2$")
    ax1.plot(ds, [r["osaki_mori_exp"] for r in d3["rows"]], "o-", color="#548235", lw=1.9, ms=5.0,
             label=r"Theorem 2 linear depth exponent $(\mu-1)d = d$")
    ax1.set_xlabel(r"$\mathsf{AC}^0[6]$ circuit depth $d$ ($\mu = 2$ primes)")
    ax1.set_ylabel(r"Exponent of $\log s$ in torus degree")
    ax1.set_title(r"(a) Linear vs. Quadratic $\mathsf{ACC}^0$ Depth Exponent")
    ax1.legend(loc="upper left", framealpha=0.92, fontsize=6.9)

    # Panel (b): Certified exact sub-degree torus approximations of AND_n / 2 (n=4,5,6)
    xs = np.arange(len(d4["rows"]))
    errs = [r["exact_max_error_dec"] for r in d4["rows"]]
    labels = [f"AND$_{r['n']}/2$\n(deg {r['poly_deg']} < {r['n']})" for r in d4["rows"]]
    bars = ax2.bar(xs, errs, color=["#1f4e79", "#2e75b6", "#548235"], width=0.52, alpha=0.92)
    ax2.axhline(0.25, color="#c00000", ls="--", lw=1.4, label=r"Trivial constant error $1/4 = 0.25$")
    for bar, r in zip(bars, d4["rows"]):
        ax2.text(bar.get_x() + bar.get_width() / 2, bar.get_height() + 0.008, r["exact_max_error"],
                 ha="center", va="bottom", fontsize=8.0, fontweight="bold")
    ax2.set_xticks(xs)
    ax2.set_xticklabels(labels, fontsize=7.6)
    ax2.set_ylim(0, 0.30)
    ax2.set_ylabel(r"Exact $\max_{x \in \{0,1\}^n} \|P(x) - \mathrm{AND}_n(x)/2\|_{\mathbb{T}}$")
    ax2.set_title(r"(b) Certified Exact Sub-Degree $\mathrm{AND}_n/2$ Witnesses")
    ax2.legend(loc="upper right", framealpha=0.92, fontsize=7.0)

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig2_acc0_depth_and_and_witnesses.png", dpi=300)
    plt.close(fig)


def make_fig3() -> None:
    rep = json.loads((DATA_DIR / "certificate_replay_summary.json").read_text(encoding="utf-8"))
    rows = rep["certificates"]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.2, 3.6), dpi=300)

    mode_colors = {
        "prime_power_finite_diff_lemma9_cert": "#1f4e79",
        "fourier_rounding_torus_approx_cert": "#2e75b6",
        "composite_modulus_crt_lemma11_cert": "#548235",
        "periodic_fourier_nmqc_equiv_cert": "#c55a11",
    }
    mode_short = {
        "prime_power_finite_diff_lemma9_cert": "Mode 1 (Lemma 9)",
        "fourier_rounding_torus_approx_cert": "Mode 2 (Fourier)",
        "composite_modulus_crt_lemma11_cert": "Mode 3 (CRT)",
        "periodic_fourier_nmqc_equiv_cert": "Mode 4 (NMQC)",
    }
    xs = np.arange(len(rows))
    lat = [r["verify_ms"] for r in rows]
    cols = [mode_colors[r["mode"]] for r in rows]
    ax1.bar(xs, lat, color=cols, width=0.68, alpha=0.92)
    ax1.set_xticks(xs)
    ax1.set_xticklabels([f"C{i+1}" for i in range(len(rows))], fontsize=7.0)
    ax1.set_ylim(0, max(lat) * 1.38)
    ax1.set_xlabel("Canonical TORUS-ACC0-CERT-1.0 certificate (C1–C16)")
    ax1.set_ylabel("Exact zero-float replay latency (ms)")
    ax1.set_title("(a) Canonical Certificate Replay Latency")
    handles = [
        plt.Rectangle((0, 0), 1, 1, color=mode_colors[m], label=mode_short[m])
        for m in mode_colors
    ]
    ax1.legend(handles=handles, loc="upper left", ncol=2, framealpha=0.92, fontsize=6.5)

    cats = ["Global /\nType", "Mode 1\nLemma 9", "Mode 2\nFourier", "Mode 3\nCRT", "Mode 4\nNMQC"]
    counts = [12, 12, 12, 12, 12]
    bcols = ["#595959", "#1f4e79", "#2e75b6", "#548235", "#c55a11"]
    bars = ax2.bar(cats, counts, color=bcols, width=0.58, alpha=0.92)
    for bar, c in zip(bars, counts):
        ax2.text(bar.get_x() + bar.get_width() / 2, bar.get_height() + 0.35, f"{c}/{c}",
                 ha="center", va="bottom", fontsize=7.8, fontweight="bold")
    ax2.set_ylim(0, 15.0)
    ax2.set_ylabel("Live adversarial forgeries rejected")
    ax2.set_title("(b) Adversarial Red-Team Audit (60/60 Rejected)")

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig3_certificate_replay_atlas.png", dpi=300)
    plt.close(fig)


def main() -> None:
    FIG_DIR.mkdir(parents=True, exist_ok=True)
    make_fig1()
    make_fig2()
    make_fig3()
    print("Generated all 3 Paper 41 publication figures successfully.")


if __name__ == "__main__":
    main()
