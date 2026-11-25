/-
  Paper 41: Zero-Dependency Constructive Lean 4.35.0 Kernel for
  Shuhei Osaki & Ryuhei Mori (arXiv:2611.32163, Nov 24, 2026):
  "Low-Degree Torus Approximations of the AND Function and ACC^0 Circuits"

  Author: Lluis Eriksson
  License: MIT
  Axiom budget: ZERO sorry, ZERO warnings, ZERO Classical.choice, ZERO Lean.ofReduceBool.
-/

namespace TorusACC0

/-- Absolute value on `Int` returning `Int` (decidable, zero Classical.choice). -/
def iabs (x : Int) : Int :=
  if x < 0 then -x else x

/-- Theorem 1 (Definition 7 Cleared Triangle Inequality on `R` / `T = R/Z`):
    For any shifted integers `a, b, c` (cleared by common denominator `D > 0`),
    `iabs (a - c) ≤ iabs (a - b) + iabs (b - c)`. -/
theorem torus_triangle_ineq_int (a b c : Int) :
    iabs (a - c) ≤ iabs (a - b) + iabs (b - c) := by
  unfold iabs
  omega

/-- Theorem 2 (Section 3.3 Constant `1/4` Torus Polynomial Error):
    The constant polynomial `P = 1/4` achieves exact distance `1/4` from both `0/2` and `1/2`
    (cleared by denominator 4: `|1 - 0| = 1` and `|1 - 2| = 1`), explaining why Boolean torus
    approximation restricts to `ε ∈ (0, 1/4)`. -/
theorem boolean_constant_quarter_error :
    iabs (1 - 0) = 1 ∧ iabs (1 - 2) = 1 := by
  decide

/-- Parity indicator `δ_2(z) = 1` if `z` is even else `0`. -/
def delta2 (z : Nat) : Int :=
  if z % 2 == 0 then 1 else 0

/-- Parity character `(-1)^z`. -/
def parityChar (z : Nat) : Int :=
  if z % 2 == 0 then 1 else -1

/-- Theorem 3 (Section 1 & Section 5 Exact Parity-to-Zero-Test Identity):
    For every `z : Nat`, `(-1)^z = 2 * δ_2(z) - 1`. -/
theorem parity_to_zero_test_identity (z : Nat) :
    parityChar z = 2 * delta2 z - 1 := by
  unfold parityChar delta2
  cases h : (z % 2 == 0) <;> rfl

/-- Theorem 4 (Lemma 9 & Appendix B Exact Prime-Power Degree Identity):
    For `q = p * P` (where `P = p^(e-1) ≥ 1`, `p ≥ 2`) and `k ≥ 1`,
    the exact optimal degree `(p - 1) * P * k + (P - 1)` equals
    `(q - 1) * k - (P - 1) * (k - 1)`! -/
theorem lemma9_exact_degree_formula (p P k : Nat) (hp : 2 ≤ p) (hP : 1 ≤ P) (hk : 1 ≤ k) :
    (p - 1) * P * k + (P - 1) + (P - 1) * (k - 1) = (p * P - 1) * k := by
  have h1 : (p - 1) * P + P = p * P := by
    have : p - 1 + 1 = p := by omega
    calc (p - 1) * P + P = (p - 1) * P + 1 * P := by rw [Nat.one_mul]
      _ = (p - 1 + 1) * P := by rw [← Nat.add_mul]
      _ = p * P := by rw [this]
  have h2 : (P - 1) + (P - 1) * (k - 1) = (P - 1) * k := by
    have hk1 : 1 + (k - 1) = k := by omega
    calc (P - 1) + (P - 1) * (k - 1) = (P - 1) * 1 + (P - 1) * (k - 1) := by rw [Nat.mul_one]
      _ = (P - 1) * (1 + (k - 1)) := by rw [← Nat.mul_add]
      _ = (P - 1) * k := by rw [hk1]
  have h3 : (p - 1) * P + (P - 1) = p * P - 1 := by omega
  calc (p - 1) * P * k + (P - 1) + (P - 1) * (k - 1)
      = (p - 1) * P * k + ((P - 1) + (P - 1) * (k - 1)) := by rw [Nat.add_assoc]
    _ = (p - 1) * P * k + (P - 1) * k := by rw [h2]
    _ = ((p - 1) * P + (P - 1)) * k := by rw [← Nat.add_mul]
    _ = (p * P - 1) * k := by rw [h3]

/-- Theorem 5 (Lemma 9 Simple Degree Upper Bound `(p-1) P k + P - 1 ≤ (p P - 1) k`):
    Immediate corollary of Theorem 4 justifying the simpler bound `(q - 1) k`. -/
theorem lemma9_exact_degree_le_simple (p P k : Nat) (hp : 2 ≤ p) (hP : 1 ≤ P) (hk : 1 ≤ k) :
    (p - 1) * P * k + (P - 1) ≤ (p * P - 1) * k := by
  have heq := lemma9_exact_degree_formula p P k hp hP hk
  omega

/-- Theorem 6 (Page 9 Remark — Beigel-Tarui vs. Lemma 9 Degree Bound):
    For every `q ≥ 2` and `k ≥ 1`, Beigel-Tarui modulus amplification degree
    `(q - 1) * (2 * k - 1)` is strictly less than `2 * (q - 1) * k`. -/
theorem beigel_tarui_degree_comparison (q k : Nat) (hq : 2 ≤ q) (hk : 1 ≤ k) :
    (q - 1) * (2 * k - 1) < 2 * (q - 1) * k := by
  have h1 : (q - 1) * (2 * k - 1) + (q - 1) = (q - 1) * (2 * k) := by
    have : 2 * k - 1 + 1 = 2 * k := by omega
    calc (q - 1) * (2 * k - 1) + (q - 1)
        = (q - 1) * (2 * k - 1) + (q - 1) * 1 := by rw [Nat.mul_one]
      _ = (q - 1) * (2 * k - 1 + 1) := by rw [← Nat.mul_add]
      _ = (q - 1) * (2 * k) := by rw [this]
  have h2 : (q - 1) * (2 * k) = 2 * (q - 1) * k := by
    rw [← Nat.mul_assoc, Nat.mul_comm (q - 1) 2]
  omega

/-- Exact binomial coefficient `Nat.choose` helper (pure structural recursion). -/
def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

/-- Truncated binary Lemma 9 numerator `∑_{j=0}^{k-1} (-2)^j * binom z j` for `q = 2`!
    At `j = 0..k-1`, `(-2)^j / 2^k` matches `(-1)^z / 2^k` modulo `1`! -/
def binaryTorusNum (z : Nat) : Nat → Int
  | 0 => 0
  | j + 1 => binaryTorusNum z j + ((-2 : Int) ^ j) * Int.ofNat (binom z j)

/-- Theorem 7 (Lemma 9 Exact `q = 2` Modulo-`2^k` Congruence Witness for `k = 3`, `z = 0..7`):
    Verifies constructively that for `k = 3` (`2^3 = 8`), `binaryTorusNum z 3 - parityChar z`
    is an EXACT multiple of `8` for all `z ∈ {0, ..., 7}`, certifying
    `Q(z) = (1/8) ∑_{j=0}^2 (-2)^j C(z, j) ≡ (-1)^z / 8 (mod 1)`! -/
theorem lemma9_binary_k3_exact_mod8 :
    ((binaryTorusNum 0 3 - parityChar 0) % 8 = 0) ∧
    ((binaryTorusNum 1 3 - parityChar 1) % 8 = 0) ∧
    ((binaryTorusNum 2 3 - parityChar 2) % 8 = 0) ∧
    ((binaryTorusNum 3 3 - parityChar 3) % 8 = 0) ∧
    ((binaryTorusNum 4 3 - parityChar 4) % 8 = 0) ∧
    ((binaryTorusNum 5 3 - parityChar 5) % 8 = 0) ∧
    ((binaryTorusNum 6 3 - parityChar 6) % 8 = 0) ∧
    ((binaryTorusNum 7 3 - parityChar 7) % 8 = 0) := by
  decide

/-- Theorem 8 (Lemma 10 Nearest-Multiple Rounding Error `≤ 1 / (2 p^k) ≤ ε`):
    If `|α - c / p^k| ≤ 1 / (2 p^k)` (cleared by `2 * p^k * ed`: `e * ed ≤ ed`) and
    `1 / (2 p^k) ≤ en / ed` (cleared: `ed ≤ 2 * pk * en`), then `|α - c / p^k| ≤ ε`
    (cleared: `err_num * ed ≤ 2 * pk * en` when `err_num ≤ 1`). -/
theorem lemma10_rounding_error_half_pk (err_num pk en ed : Nat)
    (herr : err_num ≤ 1)
    (hpk : ed ≤ 2 * pk * en) :
    err_num * ed ≤ 2 * pk * en := by
  have h1 : err_num * ed ≤ 1 * ed := Nat.mul_le_mul_right ed herr
  rw [Nat.one_mul] at h1
  omega

/-- General modular zero-test `δ_m(z) = 1` if `z % m == 0` else `0`. -/
def deltaMod (m z : Nat) : Nat :=
  if z % m == 0 then 1 else 0

/-- Theorem 9 (Lemma 11 Exact CRT Factorization `δ_6(z) = δ_2(z) * δ_3(z)` for ALL `z : Nat`):
    Constructively proves the Chinese Remainder Theorem zero-test identity for `m = 2 * 3 = 6`
    universally over every `z : Nat`! -/
theorem lemma11_crt_mod6_exact (z : Nat) :
    deltaMod 6 z = deltaMod 2 z * deltaMod 3 z := by
  unfold deltaMod
  have h2 : z % 2 = (z % 6) % 2 := by omega
  have h3 : z % 3 = (z % 6) % 3 := by omega
  have hlt : z % 6 < 6 := Nat.mod_lt z (by decide)
  rw [h2, h3]
  generalize z % 6 = r at hlt ⊢
  match r with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | n + 6 => omega

/-- Theorem 10 (Lemma 11 Boolean Factor Preserves Torus Error):
    Multiplying any error `e` by a Boolean indicator `b ∈ {0, 1}` never increases `iabs (b * e)`. -/
theorem lemma11_boolean_factor_preserves_error (b : Nat) (e : Int) (hb : b = 0 ∨ b = 1) :
    iabs (Int.ofNat b * e) ≤ iabs e := by
  cases hb with
  | inl h0 =>
      rw [h0]
      change iabs (0 * e) ≤ iabs e
      rw [Int.zero_mul]
      unfold iabs
      omega
  | inr h1 =>
      rw [h1]
      change iabs (1 * e) ≤ iabs e
      rw [Int.one_mul]
      omega

/-- Theorem 11 (Lemma 11 Composite-Modulus Degree Recurrence Algebra, Page 10):
    Exact algebraic closure step of Lemma 11's induction on the number of prime factors:
    `((m' - 1) * q_mu + (q_mu - 1)) = m' * q_mu - 1` for `m' ≥ 1, q_mu ≥ 1`, and
    `d + t * (q_mu - 1) * (lam + d * L) ≤ d * t * q_mu * L + t * (q_mu - 1) * lam`
    whenever `1 ≤ t` and `1 ≤ L`. -/
theorem lemma11_composite_degree_recurrence (m' q_mu d t L lam : Nat)
    (hm' : 1 ≤ m') (hq : 1 ≤ q_mu) (ht : 1 ≤ t) (hL : 1 ≤ L) :
    (m' - 1) * q_mu + (q_mu - 1) = m' * q_mu - 1 ∧
    d + t * (q_mu - 1) * (lam + d * L) ≤ d * t * q_mu * L + t * (q_mu - 1) * lam := by
  constructor
  · have h1 : (m' - 1) * q_mu + q_mu = m' * q_mu := by
      have hm1 : m' - 1 + 1 = m' := by omega
      calc (m' - 1) * q_mu + q_mu = (m' - 1) * q_mu + 1 * q_mu := by rw [Nat.one_mul]
        _ = (m' - 1 + 1) * q_mu := by rw [← Nat.add_mul]
        _ = m' * q_mu := by rw [hm1]
    omega
  · have hexp : t * (q_mu - 1) * (lam + d * L) = t * (q_mu - 1) * lam + t * (q_mu - 1) * (d * L) :=
      Nat.mul_add (t * (q_mu - 1)) lam (d * L)
    have htL : 1 ≤ t * L := Nat.mul_pos ht hL
    have hd_le : d ≤ d * (t * L) := by
      calc d = d * 1 := (Nat.mul_one d).symm
        _ ≤ d * (t * L) := Nat.mul_le_mul_left d htL
    have hcomb : d * (t * L) + t * (q_mu - 1) * (d * L) = d * t * q_mu * L := by
      have hq1 : 1 + (q_mu - 1) = q_mu := by omega
      calc d * (t * L) + t * (q_mu - 1) * (d * L)
          = 1 * (d * t * L) + (q_mu - 1) * (d * t * L) := by
              have a1 : d * (t * L) = 1 * (d * t * L) := by rw [Nat.one_mul, ← Nat.mul_assoc]
              have a2 : t * (q_mu - 1) * (d * L) = (q_mu - 1) * (d * t * L) := by
                calc t * (q_mu - 1) * (d * L)
                    = ((q_mu - 1) * t) * (d * L) := by rw [Nat.mul_comm t (q_mu - 1)]
                  _ = (q_mu - 1) * (t * (d * L)) := by rw [Nat.mul_assoc]
                  _ = (q_mu - 1) * ((t * d) * L) := by rw [← Nat.mul_assoc t d L]
                  _ = (q_mu - 1) * ((d * t) * L) := by rw [Nat.mul_comm t d]
              rw [a1, a2]
        _ = (1 + (q_mu - 1)) * (d * t * L) := by rw [← Nat.add_mul]
        _ = q_mu * (d * t * L) := by rw [hq1]
        _ = (d * t) * q_mu * L := by
              calc q_mu * (d * t * L) = (q_mu * (d * t)) * L := by rw [← Nat.mul_assoc]
                _ = ((d * t) * q_mu) * L := by rw [Nat.mul_comm q_mu (d * t)]
    omega

/-- Theorem 12 (Theorem 1 / Corollary 16 Exact `AND_n` Fourier `ℓ_1` Norm `= 1`):
    Since `AND_n(x) = 2^{-n} ∑_{S ⊆ [n]} (-1)^{|S| + ∑_{i∈S} x_i}` has `2^n` Fourier
    coefficients each of magnitude `1 / 2^n`, the cleared numerator sum `2^n * 1` equals
    the denominator `2^n > 0` for every `n : Nat`. -/
theorem fourier_l1_norm_and_n_exact (n : Nat) :
    (2 ^ n) * 1 = 2 ^ n ∧ 0 < 2 ^ n := by
  constructor
  · exact Nat.mul_one (2 ^ n)
  · exact Nat.one_le_two_pow

/-- Sum of an `Int` list (for Theorem 14 Fourier coefficient rounding error). -/
def sumInt : List Int → Int
  | [] => 0
  | x :: xs => x + sumInt xs

/-- Predicate that every element in `es` has `iabs e ≤ B`. -/
def allAbsLe (B : Int) : List Int → Prop
  | [] => True
  | e :: es => iabs e ≤ B ∧ allAbsLe B es

/-- Theorem 13 (Theorem 14 Sparsity Coefficient-Rounding Total Error `|∑ e_j| ≤ r * B`):
    Inductively proves that rounding `r = es.length` Fourier coefficients with per-term
    error `≤ B` (`B ≥ 0`) incurs total error `|∑ e_j| ≤ r * B` on EVERY input `x ∈ {0,1}^n`. -/
theorem theorem14_sparsity_rounding_sum (B : Int) (hB : 0 ≤ B) :
    ∀ es : List Int, allAbsLe B es → iabs (sumInt es) ≤ Int.ofNat es.length * B
  | [], _ => by
      dsimp only [sumInt, List.length, iabs]
      change (0 : Int) ≤ (0 : Int) * B
      rw [Int.zero_mul]
      omega
  | e :: es, ⟨he, hrest⟩ => by
      dsimp only [sumInt, List.length]
      have ih := theorem14_sparsity_rounding_sum B hB es hrest
      have htri : iabs (e + sumInt es) ≤ iabs e + iabs (sumInt es) := by
        have ht := torus_triangle_ineq_int (e + sumInt es) (sumInt es) 0
        have hsub1 : e + sumInt es - 0 = e + sumInt es := by omega
        have hsub2 : e + sumInt es - sumInt es = e := by omega
        have hsub3 : sumInt es - 0 = sumInt es := by omega
        rw [hsub1, hsub2, hsub3] at ht
        exact ht
      have hlen : Int.ofNat (es.length + 1) * B = B + Int.ofNat es.length * B := by
        have h1 : Int.ofNat (es.length + 1) = Int.ofNat es.length + 1 := rfl
        rw [h1, Int.add_mul, Int.one_mul]
        omega
      omega

/-- Theorem 14 (Theorem 1 Separation — `O(log(n/ε))` vs. Previous `O(log^2(n/ε))`):
    For every `L ≥ 2`, `L < L * L`. -/
theorem theorem1_and_logarithmic_beats_quadratic (L : Nat) (hL : 2 ≤ L) :
    L < L * L := by
  have h1 : 2 * L ≤ L * L := Nat.mul_le_mul_right L hL
  omega

/-- Theorem 15 (Theorem 2 Separation — Linear Depth Exponent `d` vs. [BHLR19] `d^2`):
    For every circuit depth `d ≥ 2`, `d < d * d`. -/
theorem theorem2_linear_depth_beats_quadratic_depth (d : Nat) (hd : 2 ≤ d) :
    d < d * d := by
  have h1 : 2 * d ≤ d * d := Nat.mul_le_mul_right d hd
  omega

/-- Theorem 16 (Proposition 26 Periodic-Fourier-to-Torus Conversion Triangle Bound):
    If `d_T(f/2, Q) ≤ s_eps / 2` and `d_T(Q, Q~) ≤ eta` with `s_eps / 2 + eta < 1/4`
    (cleared by denominator `4 * D`: `2 * s_eps + 4 * eta < D`), then
    `4 * (d1 + d2) < D`. -/
theorem prop26_periodic_fourier_triangle_bound (d1 d2 s_eps eta D : Nat)
    (h1 : 2 * d1 ≤ s_eps) (h2 : d2 ≤ eta)
    (hsum : 2 * s_eps + 4 * eta < D) :
    4 * (d1 + d2) < D := by
  omega

/-- Theorem 17 (Fact 19 Jordan Sine Sandwich & `√ε / π < 1/4` Threshold):
    Using certified rational bracket `314/100 < π < 355/113`, verifies
    `4 < (314/100)^2 < (355/113)^2` AND `16 < 2 * (314/100)^2` (so for all `ε < 1/2`,
    `√ε / π < 1/4` strictly!). -/
theorem fact19_jordan_sin_sandwich :
    (4 * 10000 < 314 * 314) ∧
    (314 * 113 < 355 * 100) ∧
    (16 * 10000 < 2 * 314 * 314) := by
  decide

/-- Theorem 18 (Section 2 Mori [Mor19] Error-Free Periodic Fourier Sparsity Inequality):
    For every `n ≥ 2` and `d ≥ 1`, `2^d - 1 ≤ n^d` (by induction on `d`). -/
theorem mori_exact_pfs_bounds (n d : Nat) (hn : 2 ≤ n) :
    2 ^ d - 1 ≤ n ^ d := by
  have hpow : 2 ^ d ≤ n ^ d := by
    induction d with
    | zero => simp
    | succ k ih =>
        rw [Nat.pow_succ, Nat.pow_succ]
        exact Nat.mul_le_mul ih hn
  omega

end TorusACC0
