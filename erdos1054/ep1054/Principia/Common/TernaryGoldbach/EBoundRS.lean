/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.OstopSpine
import Principia.Common.TernaryGoldbach.Dubistdie

set_option autoImplicit false

/-!
# `OS.EBound2` PROVED from Rosser–Schoenfeld 1962 Theorems 12 and 13

`OS.EBound2` (`OstopSpine.lean`) is the `E` bound of `thm:ostop` (`ternvin.tex` 3846-3884):
`∫₀¹|S_{2,η}|² = s2Sq η x ≤ E = MinSp.eBig b x`. It was one named citation. Here it is PROVED
(`eBound2_of_rs62`) from exactly two literature statements, each a NAMED hypothesis transcribed
from the source (never stronger):

* **`RS62Thm12`** — Rosser–Schoenfeld 1962, Theorem 12: `ψ(x) < 1.03883x` for `x > 0`.
* **`RS62Thm13`** — Rosser–Schoenfeld 1962, Theorem 13, the part consumed:
  `ψ(x) − θ(x) < 1.42620√x` for `x > 0` (Helfgott prints `1.4262`).

Their lower endpoints do not matter: `ψ = 0` below `2` and `ψ − θ = 0` below `4`, so each is
EQUIVALENT to its restriction to `x ≥ 2` (resp. `x ≥ 4`) (`rs62Thm12_iff`, `rs62Thm13_iff`).
Provenance: Theorem 12's statement and range are confirmed by Broadbent et al., arXiv:2002.11068,
(3.20) and (3.23); Theorem 13's constant is as Helfgott quotes it (`ternvin.tex` 3855-3863,
`typeII.tex` 139-141 of arXiv:1501.05438). The primary (Illinois J. Math. 6 (1962) 64-94) was not
reachable from this machine. Both are cited THEOREMS, not computations: an owner question.

## The proof (`ternvin.tex` 3846-3878, made discrete)

`s2Sq` runs over the `n` that are not a prime `> √x`; each such term is at most the sum of
* a SMALL term `[n ≤ √x]Λ(n)²η(n/x)² ≤ Λ(n)·log√x·b(0)²`, summing to
  `b(0)²·(½ log x)·ψ(√x) < 0.519415·b(0)²√x log x` by Theorem 12 (`small_le`); and
* a NON-PRIME term `[n not prime]Λ(n)²·b(n/x)²` (`|η| ≤ b`).

For the second, `C(N) = Σ_{n ≤ N, not prime}Λ(n)² ≤ log N·(ψ(N) − θ(N)) ≤ g(N) = 1.4262√N log N`
by Theorem 13 (`cNP_le`), and `f(n) = b(n/x)²` is non-increasing, so FINITE Abel summation
(`abel_le`, no limit needed) gives `Σ c_n f(n) ≤ Σ_n (g(n+1) − g(n))f(n+1)`. With
`G(u) = √u(log x + log u)`, `g(n) = 1.4262√x·G(n/x)` (`g_eq`), and on `[n/x, (n+1)/x]`
`(G(c) − G(a))·b(c)² ≤ ∫ G'b²` since `G' ≥ 0` and `b` decreases (`step`). The pieces telescope
to `∫_{1/x}^{N/x} G'b²`, and `G'(u)b(u)² = ((log x + 2)/2)·b²/√u + ½(log u/√u)b²` is at most the
integrable majorant whose integral over `(0, ∞)` is `((log x + 2)/2)·∫₀^∞ b²/√u + ½∫₁^∞(log u/√u)b²`
(`big_le`). Adding: `E` exactly, with `C_{η,0}`, `C_{η,1}`, `0.51942 ≥ 1.03883/2`.

The hypotheses `|η| ≤ 1.079955`, `|η(t)t| ≤ 1.19073` enter ONLY to make `b²/√t` and
`(log t/√t)b²` integrable (`int0`, `int1`, against `DB.m0`, `DB.m1`); without them the Bochner
integrals in `eBig` could be junk `0` and the statement false. Nothing beyond Theorems 12 and 13
is needed.
-/

namespace Principia.Common.TernaryGoldbach.EB

open MeasureTheory Set
open scoped ArithmeticFunction

/-! ## (0) The two literature statements -/

/-- **NAMED (literature) — Rosser–Schoenfeld 1962, Theorem 12** (Illinois J. Math. 6, 64-94;
`ternvin.tex` 3872-3877 cites it as `[Thm. 12]`): `ψ(x) < 1.03883x` for `x > 0`. A cited
THEOREM, not a computation of Helfgott's: an owner question, like `GS.RS62Thm15`. -/
def RS62Thm12 : Prop := ∀ x : ℝ, 0 < x → Chebyshev.psi x < 1.03883 * x

/-- **NAMED (literature) — Rosser–Schoenfeld 1962, Theorem 13, the part consumed**
(`ternvin.tex` 3855-3863 cites it as `[Thm. 13]`): `ψ(x) − θ(x) < 1.42620√x` for `x > 0`. A cited
THEOREM (owner question). The range is immaterial (`rs62Thm13_iff`). -/
def RS62Thm13 : Prop :=
  ∀ x : ℝ, 0 < x → Chebyshev.psi x - Chebyshev.theta x < 1.42620 * Real.sqrt x

/-- `RS62Thm12` is equivalent to its restriction to `x ≥ 2` (`ψ = 0` below `2`). -/
theorem rs62Thm12_iff : RS62Thm12 ↔ ∀ x : ℝ, 2 ≤ x → Chebyshev.psi x < 1.03883 * x := by
  constructor
  · intro h x hx
    exact h x (by linarith)
  · intro h x hx
    rcases lt_or_ge x 2 with h2 | h2
    · rw [Chebyshev.psi_eq_zero_of_lt_two h2]
      linarith
    · exact h x h2

/-- `ψ(x) − θ(x) = 0` for `x < 4` (the only non-prime `n ≤ 3` with `n ≥ 1` is `1`). -/
theorem psi_sub_theta_small {x : ℝ} (hx : x < 4) : Chebyshev.psi x - Chebyshev.theta x = 0 := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
  refine Finset.sum_eq_zero fun n hn => ?_
  rw [Finset.mem_filter, Finset.mem_Ioc] at hn
  obtain ⟨⟨h0, hn⟩, hp⟩ := hn
  have hfl : ⌊x⌋₊ < 4 := (Nat.floor_lt' (by norm_num)).mpr (by exact_mod_cast hx)
  have h3 : n ≤ 3 := by omega
  interval_cases n
  · simp
  · exact absurd Nat.prime_two hp
  · exact absurd Nat.prime_three hp

/-- `RS62Thm13` is equivalent to its restriction to `x ≥ 4` (`ψ − θ = 0` below `4`). -/
theorem rs62Thm13_iff : RS62Thm13 ↔
    ∀ x : ℝ, 4 ≤ x → Chebyshev.psi x - Chebyshev.theta x < 1.42620 * Real.sqrt x := by
  constructor
  · intro h x hx
    exact h x (by linarith)
  · intro h x hx
    rcases lt_or_ge x 4 with h4 | h4
    · rw [psi_sub_theta_small h4]
      have := Real.sqrt_pos.mpr hx
      positivity
    · exact h x h4

/-! ## (1) The sup function -/

/-- `|η(r)| ≤ b(t)` for `0 ≤ t ≤ r`. -/
theorem abs_le_supFn {η b : ℝ → ℝ} (hb : MinSp.SupFn η b) {r t : ℝ} (ht : 0 ≤ t) (htr : t ≤ r) :
    |η r| ≤ b t :=
  (hb t ht).1 ⟨r, htr, rfl⟩

/-- `b(t) ≥ 0` for `t ≥ 0`. -/
theorem supFn_nonneg {η b : ℝ → ℝ} (hb : MinSp.SupFn η b) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ b t :=
  le_trans (abs_nonneg _) (abs_le_supFn hb ht le_rfl)

/-- `b` is non-increasing on `[0, ∞)`. -/
theorem supFn_anti {η b : ℝ → ℝ} (hb : MinSp.SupFn η b) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    b t ≤ b s :=
  (hb t (le_trans hs hst)).2 (by
    rintro _ ⟨r, hr, rfl⟩
    exact (hb s hs).1 ⟨r, le_trans hst hr, rfl⟩)

/-- `b²` is non-increasing on `[0, ∞)`. -/
theorem sq_anti {η b : ℝ → ℝ} (hb : MinSp.SupFn η b) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    b t ^ 2 ≤ b s ^ 2 :=
  pow_le_pow_left₀ (supFn_nonneg hb (le_trans hs hst)) (supFn_anti hb hs hst) 2

/-! ## (2) Finite Abel summation -/

/-- **Abel summation, finite form**: if `f ≥ 0` is non-increasing and every partial sum
`Σ_{n ≤ N} c_n` is at most `g(N)`, then
`Σ_{n ≤ N} c_n f(n) ≤ g(0)f(0) + Σ_{n < N}(g(n+1) − g(n))f(n+1)`. No limit is taken. -/
theorem abel_le (c f g : ℕ → ℝ) (hf : ∀ n, f (n + 1) ≤ f n) (hf0 : ∀ n, 0 ≤ f n)
    (hC : ∀ N, ∑ n ∈ Finset.range (N + 1), c n ≤ g N) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), c n * f n ≤
      g 0 * f 0 + ∑ n ∈ Finset.range N, (g (n + 1) - g n) * f (n + 1) := by
  have key : ∀ M : ℕ, ∑ n ∈ Finset.range (M + 1), c n * f n +
      (g M - ∑ n ∈ Finset.range (M + 1), c n) * f M ≤
      g 0 * f 0 + ∑ n ∈ Finset.range M, (g (n + 1) - g n) * f (n + 1) := by
    intro M
    induction M with
    | zero =>
      simp only [zero_add, Finset.sum_range_one, Finset.sum_range_zero, add_zero]
      exact le_of_eq (by ring)
    | succ M ih =>
      rw [Finset.sum_range_succ (fun n => c n * f n) (M + 1), Finset.sum_range_succ c (M + 1),
        Finset.sum_range_succ (fun n => (g (n + 1) - g n) * f (n + 1)) M]
      have h1 : 0 ≤ g M - ∑ n ∈ Finset.range (M + 1), c n := sub_nonneg.mpr (hC M)
      have h2 : 0 ≤ f M - f (M + 1) := sub_nonneg.mpr (hf M)
      nlinarith [mul_nonneg h1 h2]
  have hk := key N
  have hpos := mul_nonneg (sub_nonneg.mpr (hC N)) (hf0 N)
  linarith

/-! ## (3) The non-prime prime powers, from Theorem 13 -/

/-- **`C(N) = Σ_{n ≤ N, n not prime}Λ(n)² ≤ 1.4262√N log N`**: `Λ(n) ≤ log n ≤ log N` and
`Σ_{n ≤ N, n not prime}Λ(n) = ψ(N) − θ(N)`. -/
theorem cNP_le (h13 : RS62Thm13) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (if ¬n.Prime then Λ n ^ 2 else 0) ≤
      1.42620 * Real.sqrt N * Real.log N := by
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    simp
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hpos
  have hL : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hpt : ∀ n ∈ Finset.range (N + 1), (if ¬n.Prime then Λ n ^ 2 else 0) ≤
      (if ¬n.Prime then Λ n else 0) * Real.log N := by
    intro n hn
    have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    by_cases hp : n.Prime
    · rw [if_neg (not_not.mpr hp), if_neg (not_not.mpr hp), zero_mul]
    · rw [if_pos hp, if_pos hp]
      have hΛ0 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
      have hΛ : Λ n ≤ Real.log N := by
        rcases Nat.eq_zero_or_pos n with hn0 | hnp
        · subst hn0
          simpa using hL
        · exact le_trans ArithmeticFunction.vonMangoldt_le_log
            (Real.log_le_log (by exact_mod_cast hnp) (by exact_mod_cast hnN))
      calc Λ n ^ 2 = Λ n * Λ n := by ring
        _ ≤ Λ n * Real.log N := mul_le_mul_of_nonneg_left hΛ hΛ0
  have hsum : ∑ n ∈ Finset.range (N + 1), (if ¬n.Prime then Λ n else 0) =
      Chebyshev.psi N - Chebyshev.theta N := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, Finset.sum_filter]
    refine (Finset.sum_subset (fun n hn => ?_) fun n hn hn' => ?_).symm
    · rw [Finset.mem_range]
      have := (Finset.mem_Ioc.mp hn).2
      omega
    · have hn0 : n = 0 := by
        rw [Finset.mem_Ioc] at hn'
        have := Finset.mem_range.mp hn
        omega
      subst hn0
      simp
  have h1 := Finset.sum_le_sum hpt
  rw [← Finset.sum_mul, hsum] at h1
  have h2 := h13 N (by linarith)
  calc ∑ n ∈ Finset.range (N + 1), (if ¬n.Prime then Λ n ^ 2 else 0)
      ≤ (Chebyshev.psi N - Chebyshev.theta N) * Real.log N := h1
    _ ≤ 1.42620 * Real.sqrt N * Real.log N := mul_le_mul_of_nonneg_right h2.le hL

/-! ## (4) The small `n`, from Theorem 12 -/

/-- **`Σ_{n ≤ √x}Λ(n)²η(n/x)² ≤ 0.51942·b(0)²√x log x`** (`ternvin.tex` 3872-3877): each term is
`≤ Λ(n)·log√x·b(0)²`, the sum of `Λ(n)` is `ψ(√x) < 1.03883√x`, and `1.03883/2 ≤ 0.51942`. -/
theorem small_le (h12 : RS62Thm12) (η b : ℝ → ℝ) (hb : MinSp.SupFn η b) (x : ℝ) (hx : 1 ≤ x)
    (N : ℕ) :
    ∑ n ∈ Finset.range N,
        (if (n : ℝ) ≤ Real.sqrt x then Λ n ^ 2 * η ((n : ℝ) / x) ^ 2 else 0) ≤
      0.51942 * b 0 ^ 2 * (Real.sqrt x * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hs1 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx
  have hLs : Real.log (Real.sqrt x) = Real.log x / 2 := by rw [Real.log_sqrt hx0.le]
  have hLs0 : 0 ≤ Real.log (Real.sqrt x) := Real.log_nonneg hs1
  have hB : 0 ≤ Real.log (Real.sqrt x) * b 0 ^ 2 := mul_nonneg hLs0 (sq_nonneg _)
  have hpt : ∀ n ∈ Finset.range N,
      (if (n : ℝ) ≤ Real.sqrt x then Λ n ^ 2 * η ((n : ℝ) / x) ^ 2 else 0) ≤
        if n ∈ Finset.Icc 0 ⌊Real.sqrt x⌋₊ then
          Λ n * (Real.log (Real.sqrt x) * b 0 ^ 2) else 0 := by
    intro n _
    have hΛ0 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    by_cases hn : (n : ℝ) ≤ Real.sqrt x
    · have hmem : n ∈ Finset.Icc 0 ⌊Real.sqrt x⌋₊ :=
        Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor hn⟩
      rw [if_pos hn, if_pos hmem]
      have hΛ : Λ n ≤ Real.log (Real.sqrt x) := by
        rcases Nat.eq_zero_or_pos n with hn0 | hnp
        · subst hn0
          simpa using hLs0
        · exact le_trans ArithmeticFunction.vonMangoldt_le_log
            (Real.log_le_log (by exact_mod_cast hnp) hn)
      have hη : η ((n : ℝ) / x) ^ 2 ≤ b 0 ^ 2 := by
        have h := abs_le_supFn hb (le_refl (0 : ℝ)) (div_nonneg (Nat.cast_nonneg n) hx0.le)
        calc η ((n : ℝ) / x) ^ 2 = |η ((n : ℝ) / x)| ^ 2 := (sq_abs _).symm
          _ ≤ b 0 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      calc Λ n ^ 2 * η ((n : ℝ) / x) ^ 2 = Λ n * (Λ n * η ((n : ℝ) / x) ^ 2) := by ring
        _ ≤ Λ n * (Real.log (Real.sqrt x) * b 0 ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hΛ hη (sq_nonneg _) hLs0) hΛ0
    · rw [if_neg hn]
      split_ifs
      · exact mul_nonneg hΛ0 hB
      · exact le_rfl
  have h1 := Finset.sum_le_sum hpt
  rw [Finset.sum_ite_mem] at h1
  have h2 : ∑ n ∈ Finset.range N ∩ Finset.Icc 0 ⌊Real.sqrt x⌋₊,
      Λ n * (Real.log (Real.sqrt x) * b 0 ^ 2) ≤
        Chebyshev.psi (Real.sqrt x) * (Real.log (Real.sqrt x) * b 0 ^ 2) := by
    rw [Chebyshev.psi_eq_sum_Icc, Finset.sum_mul]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      fun n _ _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hB
  have hψ := h12 (Real.sqrt x) hs0
  have h3 : Chebyshev.psi (Real.sqrt x) * (Real.log (Real.sqrt x) * b 0 ^ 2) ≤
      1.03883 * Real.sqrt x * (Real.log (Real.sqrt x) * b 0 ^ 2) :=
    mul_le_mul_of_nonneg_right hψ.le hB
  rw [hLs] at h1 h2 h3
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h4 : 0 ≤ b 0 ^ 2 * (Real.sqrt x * Real.log x) := by positivity
  nlinarith

/-! ## (5) Integrability of the two weights -/

/-- `b(t)²/√t ≤ DB.m₀(t)` for `t > 0` (the pointwise step of `DB.int0_le`). -/
theorem b_sq_div_le (η b : ℝ → ℝ) (h1 : ∀ t : ℝ, 0 ≤ t → |η t| ≤ 1.079955)
    (h2 : ∀ t : ℝ, 0 ≤ t → |η t * t| ≤ 1.19073) (hb : MinSp.SupFn η b) {t : ℝ} (ht0 : 0 < t) :
    b t ^ 2 / Real.sqrt t ≤ DB.m0 t := by
  obtain ⟨hb0, hba, hbt⟩ := DB.supFn_bounds η b h1 h2 hb ht0.le
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  unfold DB.m0
  split_ifs with hts
  · rw [DB.rpow_neg_half ht0, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hb0 hba 2) hs0.le
  · rw [DB.rpow_five_half ht0, ← div_eq_mul_inv, div_le_div_iff₀ hs0 (by positivity)]
    have hsq : (b t * t) ^ 2 ≤ 1.19073 ^ 2 := pow_le_pow_left₀ (by positivity) hbt 2
    calc b t ^ 2 * (t ^ 2 * Real.sqrt t) = (b t * t) ^ 2 * Real.sqrt t := by ring
      _ ≤ 1.19073 ^ 2 * Real.sqrt t := mul_le_mul_of_nonneg_right hsq hs0.le

/-- `(log t/√t)·b(t)² ≤ DB.m₁(t)` for `t > 1` (the pointwise step of `DB.int1_le`). -/
theorem log_b_sq_le (η b : ℝ → ℝ) (h1 : ∀ t : ℝ, 0 ≤ t → |η t| ≤ 1.079955)
    (h2 : ∀ t : ℝ, 0 ≤ t → |η t * t| ≤ 1.19073) (hb : MinSp.SupFn η b) {t : ℝ} (ht1 : 1 < t) :
    Real.log t / Real.sqrt t * b t ^ 2 ≤ DB.m1 t := by
  have ht0 : 0 < t := by linarith
  obtain ⟨hb0, hba, hbt⟩ := DB.supFn_bounds η b h1 h2 hb ht0.le
  have hL0 : 0 ≤ Real.log t := Real.log_nonneg ht1.le
  have hq1 : 1 ≤ Real.sqrt t := Real.one_le_sqrt.mpr ht1.le
  have hq0 : 0 < Real.sqrt t := by linarith
  unfold DB.m1
  split_ifs with hts
  · have hlq : Real.log t / Real.sqrt t ≤ 1.1025 - 1 := by
      rw [div_le_iff₀ hq0]
      have hl := Real.log_le_sub_one_of_pos ht0
      nlinarith
    calc Real.log t / Real.sqrt t * b t ^ 2 ≤ (1.1025 - 1) * 1.079955 ^ 2 :=
          mul_le_mul hlq (pow_le_pow_left₀ hb0 hba 2) (sq_nonneg _) (by norm_num)
      _ = 1.079955 ^ 2 * (1.1025 - 1) := by ring
  · set q := Real.sqrt t with hq_def
    have htq : t = q ^ 2 := (Real.sq_sqrt ht0.le).symm
    have hlog : Real.log t ≤ 2 * (q - 1) := by
      have h := Real.log_le_sub_one_of_pos hq0
      rw [hq_def, Real.log_sqrt ht0.le] at h
      linarith
    rw [DB.rpow_neg_two ht0, DB.rpow_five_half ht0, ← hq_def]
    have hbq : b t * q ^ 2 ≤ 1.19073 := by rw [← htq]; exact hbt
    have hbq0 : 0 ≤ b t * q ^ 2 := by positivity
    have hb2 : (b t * q ^ 2) ^ 2 ≤ 1.19073 ^ 2 := pow_le_pow_left₀ hbq0 hbq 2
    have e : 2 * 1.19073 ^ 2 * ((t ^ 2)⁻¹ - (t ^ 2 * q)⁻¹) =
        2 * (q - 1) * 1.19073 ^ 2 / q ^ 5 := by
      rw [htq]
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    have hstep : Real.log t / q * b t ^ 2 * q ^ 5 = Real.log t * (b t * q ^ 2) ^ 2 := by
      field_simp
    rw [hstep]
    calc Real.log t * (b t * q ^ 2) ^ 2 ≤ 2 * (q - 1) * (b t * q ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_right hlog (sq_nonneg _)
      _ ≤ 2 * (q - 1) * 1.19073 ^ 2 := mul_le_mul_of_nonneg_left hb2 (by linarith)

/-- **`b²/√t` is integrable on `(0, ∞)`** (dominated by `DB.m₀`; `b` is monotone, so measurable). -/
theorem int0 (η b : ℝ → ℝ) (h1 : ∀ t : ℝ, 0 ≤ t → |η t| ≤ 1.079955)
    (h2 : ∀ t : ℝ, 0 ≤ t → |η t * t| ≤ 1.19073) (hb : MinSp.SupFn η b) :
    IntegrableOn (fun t : ℝ => b t ^ 2 / Real.sqrt t) (Ioi 0) := by
  refine Integrable.mono' DB.m0_int.1 ?_ ?_
  · have hae : AEMeasurable b (volume.restrict (Ioi (0 : ℝ))) :=
      aemeasurable_restrict_of_antitoneOn measurableSet_Ioi
        (fun s hs _ _ hst => supFn_anti hb (le_of_lt hs) hst)
    exact ((hae.pow_const 2).div Real.continuous_sqrt.measurable.aemeasurable).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))]
    exact b_sq_div_le η b h1 h2 hb ht

/-- **`(log t/√t)b²` is integrable on `(1, ∞)`** (dominated by `DB.m₁`). -/
theorem int1 (η b : ℝ → ℝ) (h1 : ∀ t : ℝ, 0 ≤ t → |η t| ≤ 1.079955)
    (h2 : ∀ t : ℝ, 0 ≤ t → |η t * t| ≤ 1.19073) (hb : MinSp.SupFn η b) :
    IntegrableOn (fun t : ℝ => Real.log t / Real.sqrt t * b t ^ 2) (Ioi 1) := by
  refine Integrable.mono' DB.m1_int.1 ?_ ?_
  · have hae : AEMeasurable b (volume.restrict (Ioi (1 : ℝ))) :=
      aemeasurable_restrict_of_antitoneOn measurableSet_Ioi
        (fun s hs _ _ hst => supFn_anti hb (by have : (1 : ℝ) < s := hs; linarith) hst)
    exact ((Real.measurable_log.aemeasurable.div Real.continuous_sqrt.measurable.aemeasurable).mul
      (hae.pow_const 2)).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht1 : 1 < t := ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (div_nonneg (Real.log_nonneg ht1.le)
      (Real.sqrt_nonneg _)) (sq_nonneg _))]
    exact log_b_sq_le η b h1 h2 hb ht1

/-! ## (6) One step of the partial summation -/

/-- `G(u) = √u(log x + log u)`: `1.4262√x·G(n/x) = 1.4262√n log n` (`g_eq`). -/
noncomputable def gG (x u : ℝ) : ℝ := Real.sqrt u * (Real.log x + Real.log u)

/-- `G'(u) = (log x + log u + 2)/(2√u)`. -/
noncomputable def kG (x u : ℝ) : ℝ := (Real.log x + Real.log u + 2) / (2 * Real.sqrt u)

/-- `G' = kG` on `u > 0`. -/
theorem hasDerivAt_gG (x : ℝ) {u : ℝ} (hu : 0 < u) : HasDerivAt (gG x) (kG x u) u := by
  have h := (Real.hasDerivAt_sqrt hu.ne').mul
    ((hasDerivAt_const u (Real.log x)).add (Real.hasDerivAt_log hu.ne'))
  refine h.congr_deriv ?_
  simp only [Pi.add_apply]
  have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hss : u⁻¹ = (Real.sqrt u * Real.sqrt u)⁻¹ := by rw [Real.mul_self_sqrt hu.le]
  unfold kG
  rw [hss]
  field_simp
  ring

/-- `kG x` is continuous on `(0, ∞)`. -/
theorem kG_contAt (x : ℝ) {u : ℝ} (hu : 0 < u) : ContinuousAt (kG x) u := by
  have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  exact ((continuousAt_const.add (Real.continuousAt_log hu.ne')).add continuousAt_const).div
    (continuousAt_const.mul Real.continuous_sqrt.continuousAt) (by positivity)

/-- `1.4262√m log m = 1.4262√x·G(m/x)` for `m ≥ 1`, `x > 0`. -/
theorem g_eq (x : ℝ) (hx : 0 < x) (m : ℕ) (hm : 1 ≤ m) :
    1.42620 * Real.sqrt (m : ℝ) * Real.log (m : ℝ) =
      1.42620 * Real.sqrt x * gG x ((m : ℝ) / x) := by
  have hm0 : (m : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hsx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  unfold gG
  rw [Real.sqrt_div (Nat.cast_nonneg m), Real.log_div hm0 hx.ne']
  field_simp
  ring

/-- On `[a, c]`, `0 < a`: `kG x · b²` is interval-integrable (`b²` monotone, `kG` continuous). -/
theorem kb_int {η b : ℝ → ℝ} (hb : MinSp.SupFn η b) (x : ℝ) {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) :
    IntervalIntegrable (fun u => kG x u * b u ^ 2) volume a c := by
  have hsub : uIcc a c = Icc a c := uIcc_of_le hac
  have hpos : ∀ s ∈ uIcc a c, 0 < s := fun s hs => by
    rw [hsub] at hs
    exact lt_of_lt_of_le ha hs.1
  have hbint : IntervalIntegrable (fun u => b u ^ 2) volume a c :=
    AntitoneOn.intervalIntegrable fun s hs _ _ hst => sq_anti hb (hpos s hs).le hst
  exact hbint.continuousOn_mul
    (continuousOn_of_forall_continuousAt fun s hs => kG_contAt x (hpos s hs))

/-- **One step**: for `n ≥ 1`, `(G((n+1)/x) − G(n/x))·b((n+1)/x)² ≤ ∫_{n/x}^{(n+1)/x} G'·b²`
(the fundamental theorem of calculus, `G' ≥ 0` there because `xu ≥ 1`, and `b` decreasing). -/
theorem step {η b : ℝ → ℝ} (hb : MinSp.SupFn η b) (x : ℝ) (hx : 1 ≤ x) (n : ℕ) (hn : 1 ≤ n) :
    (gG x (((n + 1 : ℕ) : ℝ) / x) - gG x ((n : ℝ) / x)) * b (((n + 1 : ℕ) : ℝ) / x) ^ 2 ≤
      ∫ u in (n : ℝ) / x..((n + 1 : ℕ) : ℝ) / x, kG x u * b u ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 < (n : ℝ) / x := div_pos (by linarith) hx0
  have hac : (n : ℝ) / x ≤ ((n + 1 : ℕ) : ℝ) / x :=
    div_le_div_of_nonneg_right (by push_cast; linarith) hx0.le
  have hsub : uIcc ((n : ℝ) / x) (((n + 1 : ℕ) : ℝ) / x) =
      Icc ((n : ℝ) / x) (((n + 1 : ℕ) : ℝ) / x) := uIcc_of_le hac
  have hcont : ContinuousOn (kG x) (uIcc ((n : ℝ) / x) (((n + 1 : ℕ) : ℝ) / x)) :=
    continuousOn_of_forall_continuousAt fun s hs => by
      rw [hsub] at hs
      exact kG_contAt x (lt_of_lt_of_le ha hs.1)
  have hFTC : ∫ u in (n : ℝ) / x..((n + 1 : ℕ) : ℝ) / x, kG x u =
      gG x (((n + 1 : ℕ) : ℝ) / x) - gG x ((n : ℝ) / x) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu => by
        rw [hsub] at hu
        exact hasDerivAt_gG x (lt_of_lt_of_le ha hu.1))
      hcont.intervalIntegrable
  rw [← hFTC, ← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_mono_on hac (hcont.intervalIntegrable.mul_const _)
    (kb_int hb x ha hac) fun u hu => ?_
  have hu0 : 0 < u := lt_of_lt_of_le ha hu.1
  have hxu : 1 ≤ x * u := by
    have h := mul_le_mul_of_nonneg_left hu.1 hx0.le
    rw [mul_div_cancel₀ _ hx0.ne'] at h
    linarith
  have hk : 0 ≤ kG x u := by
    unfold kG
    have hl : 0 ≤ Real.log (x * u) := Real.log_nonneg hxu
    rw [Real.log_mul hx0.ne' hu0.ne'] at hl
    have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
    exact div_nonneg (by linarith) (by positivity)
  exact mul_le_mul_of_nonneg_left (sq_anti hb (le_trans ha.le hu.1) hu.2) hk

/-! ## (7) The non-prime part -/

/-- **`Σ_{n<N, n not prime}Λ(n)²b(n/x)² ≤ 0.7131√x((log x + 2)∫₀^∞ b²/√t + ∫₁^∞ (log t/√t)b²)`**
(`ternvin.tex` 3855-3871): `abel_le` against `cNP_le`, then `step`, telescoping, and the
integrable majorant. -/
theorem big_le (h13 : RS62Thm13) (η b : ℝ → ℝ) (h1 : ∀ t : ℝ, 0 ≤ t → |η t| ≤ 1.079955)
    (h2 : ∀ t : ℝ, 0 ≤ t → |η t * t| ≤ 1.19073) (hb : MinSp.SupFn η b) (x : ℝ) (hx : 1 ≤ x)
    (N : ℕ) :
    ∑ n ∈ Finset.range N, (if ¬n.Prime then Λ n ^ 2 else 0) * b ((n : ℝ) / x) ^ 2 ≤
      0.7131 * Real.sqrt x * ((Real.log x + 2) * (∫ t in Ioi (0 : ℝ), b t ^ 2 / Real.sqrt t) +
        ∫ t in Ioi (1 : ℝ), Real.log t / Real.sqrt t * b t ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hi0 := int0 η b h1 h2 hb
  have hi1 := int1 η b h1 h2 hb
  -- the majorant
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ → ℝ, M = fun u => (Real.log x + 2) / 2 * (b u ^ 2 / Real.sqrt u) +
      1 / 2 * (Ioi (1 : ℝ)).indicator (fun t => Real.log t / Real.sqrt t * b t ^ 2) u :=
    ⟨_, rfl⟩
  have hind : IntegrableOn ((Ioi (1 : ℝ)).indicator
      (fun t => Real.log t / Real.sqrt t * b t ^ 2)) (Ioi 0) :=
    (hi1.integrable_indicator measurableSet_Ioi).integrableOn
  have hMint : IntegrableOn M (Ioi 0) := by
    rw [hMdef]
    exact (hi0.const_mul _).add (hind.const_mul _)
  have hMval : ∫ u in Ioi (0 : ℝ), M u = (Real.log x + 2) / 2 *
      (∫ t in Ioi (0 : ℝ), b t ^ 2 / Real.sqrt t) +
        1 / 2 * ∫ t in Ioi (1 : ℝ), Real.log t / Real.sqrt t * b t ^ 2 := by
    rw [hMdef, integral_add (hi0.const_mul _) (hind.const_mul _), integral_const_mul,
      integral_const_mul, setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]
  have hM0 : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ M u := by
    intro u hu
    have hu0 : 0 < u := hu
    rw [hMdef]
    have hA : 0 ≤ (Real.log x + 2) / 2 * (b u ^ 2 / Real.sqrt u) :=
      mul_nonneg (by linarith) (div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))
    have hB : 0 ≤ (Ioi (1 : ℝ)).indicator (fun t => Real.log t / Real.sqrt t * b t ^ 2) u := by
      by_cases h : u ∈ Ioi (1 : ℝ)
      · rw [indicator_of_mem h]
        have h' : 1 < u := h
        exact mul_nonneg (div_nonneg (Real.log_nonneg h'.le) (Real.sqrt_nonneg _)) (sq_nonneg _)
      · rw [indicator_of_notMem h]
    dsimp only
    linarith
  have hMpos : 0 ≤ ∫ u in Ioi (0 : ℝ), M u := setIntegral_nonneg measurableSet_Ioi hM0
  -- Abel summation
  have hf : ∀ n : ℕ, b (((n + 1 : ℕ) : ℝ) / x) ^ 2 ≤ b ((n : ℝ) / x) ^ 2 := fun n =>
    sq_anti hb (div_nonneg (Nat.cast_nonneg n) hx0.le)
      (div_le_div_of_nonneg_right (by push_cast; linarith) hx0.le)
  have hf0 : ∀ n : ℕ, 0 ≤ b ((n : ℝ) / x) ^ 2 := fun n => sq_nonneg _
  have hab := abel_le (fun n => if ¬n.Prime then Λ n ^ 2 else 0) (fun n => b ((n : ℝ) / x) ^ 2)
    (fun n => 1.42620 * Real.sqrt (n : ℝ) * Real.log (n : ℝ)) hf hf0 (cNP_le h13) N
  have hext : ∑ n ∈ Finset.range N, (if ¬n.Prime then Λ n ^ 2 else 0) * b ((n : ℝ) / x) ^ 2 ≤
      ∑ n ∈ Finset.range (N + 1), (if ¬n.Prime then Λ n ^ 2 else 0) * b ((n : ℝ) / x) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
      fun n _ _ => mul_nonneg (by split_ifs <;> positivity) (sq_nonneg _)
  -- the telescoped sum
  have hT : ∑ n ∈ Finset.range N,
      (1.42620 * Real.sqrt ((n + 1 : ℕ) : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) -
        1.42620 * Real.sqrt (n : ℝ) * Real.log (n : ℝ)) * b (((n + 1 : ℕ) : ℝ) / x) ^ 2 ≤
      1.42620 * Real.sqrt x * ∫ u in Ioi (0 : ℝ), M u := by
    rcases Nat.eq_zero_or_pos N with h0 | hN
    · subst h0
      simp only [Finset.range_zero, Finset.sum_empty]
      exact mul_nonneg (by positivity) hMpos
    obtain ⟨K, rfl⟩ : ∃ K : ℕ, N = K + 1 := ⟨N - 1, by omega⟩
    rw [Finset.sum_range_succ']
    have hz : (1.42620 * Real.sqrt ((0 + 1 : ℕ) : ℝ) * Real.log ((0 + 1 : ℕ) : ℝ) -
        1.42620 * Real.sqrt ((0 : ℕ) : ℝ) * Real.log ((0 : ℕ) : ℝ)) *
          b (((0 + 1 : ℕ) : ℝ) / x) ^ 2 = 0 := by simp
    rw [hz, add_zero]
    have hterm : ∀ k ∈ Finset.range K,
        (1.42620 * Real.sqrt ((k + 1 + 1 : ℕ) : ℝ) * Real.log ((k + 1 + 1 : ℕ) : ℝ) -
          1.42620 * Real.sqrt ((k + 1 : ℕ) : ℝ) * Real.log ((k + 1 : ℕ) : ℝ)) *
            b (((k + 1 + 1 : ℕ) : ℝ) / x) ^ 2 ≤
        1.42620 * Real.sqrt x *
          ∫ u in ((k + 1 : ℕ) : ℝ) / x..((k + 1 + 1 : ℕ) : ℝ) / x, kG x u * b u ^ 2 := by
      intro k _
      rw [g_eq x hx0 (k + 1 + 1) (by omega), g_eq x hx0 (k + 1) (by omega)]
      have hs := step hb x hx (k + 1) (by omega)
      calc (1.42620 * Real.sqrt x * gG x (((k + 1 + 1 : ℕ) : ℝ) / x) -
            1.42620 * Real.sqrt x * gG x (((k + 1 : ℕ) : ℝ) / x)) *
              b (((k + 1 + 1 : ℕ) : ℝ) / x) ^ 2
          = 1.42620 * Real.sqrt x * ((gG x (((k + 1 + 1 : ℕ) : ℝ) / x) -
              gG x (((k + 1 : ℕ) : ℝ) / x)) * b (((k + 1 + 1 : ℕ) : ℝ) / x) ^ 2) := by ring
        _ ≤ 1.42620 * Real.sqrt x *
            ∫ u in ((k + 1 : ℕ) : ℝ) / x..((k + 1 + 1 : ℕ) : ℝ) / x, kG x u * b u ^ 2 :=
          mul_le_mul_of_nonneg_left hs (by positivity)
    have hsum := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum] at hsum
    have hadj := intervalIntegral.sum_integral_adjacent_intervals
      (f := fun u => kG x u * b u ^ 2) (μ := volume)
      (a := fun k : ℕ => ((k + 1 : ℕ) : ℝ) / x) (n := K) (fun k _ => by
        have hk1' : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        exact kb_int hb x (div_pos (by push_cast; linarith) hx0)
          (div_le_div_of_nonneg_right (by push_cast; linarith) hx0.le))
    rw [hadj] at hsum
    have hle : ((0 + 1 : ℕ) : ℝ) / x ≤ ((K + 1 : ℕ) : ℝ) / x :=
      div_le_div_of_nonneg_right (by exact_mod_cast (by omega : 0 + 1 ≤ K + 1)) hx0.le
    have hpos1 : 0 < ((0 + 1 : ℕ) : ℝ) / x := div_pos (by norm_num) hx0
    have hIoc : Ioc (((0 + 1 : ℕ) : ℝ) / x) (((K + 1 : ℕ) : ℝ) / x) ⊆ Ioi 0 := fun u hu =>
      lt_trans hpos1 hu.1
    have hcmp : ∫ u in ((0 + 1 : ℕ) : ℝ) / x..((K + 1 : ℕ) : ℝ) / x, kG x u * b u ^ 2 ≤
        ∫ u in Ioi (0 : ℝ), M u := by
      rw [intervalIntegral.integral_of_le hle]
      calc ∫ u in Ioc (((0 + 1 : ℕ) : ℝ) / x) (((K + 1 : ℕ) : ℝ) / x), kG x u * b u ^ 2
          ≤ ∫ u in Ioc (((0 + 1 : ℕ) : ℝ) / x) (((K + 1 : ℕ) : ℝ) / x), M u := by
            refine integral_mono_of_nonneg ?_ (hMint.mono_set hIoc) ?_
            · refine ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => ?_
              have hu0 : 0 < u := hIoc hu
              have hxu : 1 < x * u := by
                have h := mul_lt_mul_of_pos_left hu.1 hx0
                rw [mul_div_cancel₀ _ hx0.ne'] at h
                push_cast at h
                linarith
              have hl : 0 ≤ Real.log (x * u) := Real.log_nonneg hxu.le
              rw [Real.log_mul hx0.ne' hu0.ne'] at hl
              have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
              unfold kG
              exact mul_nonneg (div_nonneg (by linarith) (by positivity)) (sq_nonneg _)
            · refine ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => ?_
              have hu0 : 0 < u := hIoc hu
              have hs : Real.sqrt u ≠ 0 := (Real.sqrt_pos.mpr hu0).ne'
              have e : kG x u * b u ^ 2 = (Real.log x + 2) / 2 * (b u ^ 2 / Real.sqrt u) +
                  1 / 2 * (Real.log u / Real.sqrt u * b u ^ 2) := by
                unfold kG
                field_simp
                ring
              dsimp only
              rw [e, hMdef]
              dsimp only
              by_cases h : u ∈ Ioi (1 : ℝ)
              · rw [indicator_of_mem h]
              · rw [indicator_of_notMem h]
                have hu1 : u ≤ 1 := not_lt.mp h
                have hl : Real.log u ≤ 0 := Real.log_nonpos hu0.le hu1
                have h3 : Real.log u / Real.sqrt u * b u ^ 2 ≤ 0 :=
                  mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hl
                    (Real.sqrt_nonneg _)) (sq_nonneg _)
                linarith
        _ ≤ ∫ u in Ioi (0 : ℝ), M u :=
            setIntegral_mono_set hMint (ae_restrict_of_forall_mem measurableSet_Ioi hM0)
              hIoc.eventuallyLE
    exact le_trans hsum (mul_le_mul_of_nonneg_left hcmp (by positivity))
  have hg0 : (1.42620 : ℝ) * Real.sqrt ((0 : ℕ) : ℝ) * Real.log ((0 : ℕ) : ℝ) *
      b (((0 : ℕ) : ℝ) / x) ^ 2 = 0 := by simp
  rw [hg0, zero_add] at hab
  rw [hMval] at hT
  calc ∑ n ∈ Finset.range N, (if ¬n.Prime then Λ n ^ 2 else 0) * b ((n : ℝ) / x) ^ 2
      ≤ 1.42620 * Real.sqrt x * ((Real.log x + 2) / 2 *
          (∫ t in Ioi (0 : ℝ), b t ^ 2 / Real.sqrt t) +
            1 / 2 * ∫ t in Ioi (1 : ℝ), Real.log t / Real.sqrt t * b t ^ 2) :=
        le_trans hext (le_trans hab hT)
    _ = 0.7131 * Real.sqrt x * ((Real.log x + 2) * (∫ t in Ioi (0 : ℝ), b t ^ 2 / Real.sqrt t) +
          ∫ t in Ioi (1 : ℝ), Real.log t / Real.sqrt t * b t ^ 2) := by ring

/-! ## (8) `OS.EBound2` -/

/-- **`OS.EBound2 η`, PROVED for every `η`, from Rosser–Schoenfeld 1962 Theorems 12 and 13**
(`ternvin.tex` 3846-3884). Each term of `s2Sq` is at most a small-`n` term plus a non-prime term
(`small_le`, `big_le`), and the two bounds add up to `E = MinSp.eBig b x`. -/
theorem eBound2_of_rs62 (h12 : RS62Thm12) (h13 : RS62Thm13) (η : ℝ → ℝ) : OS.EBound2 η := by
  intro h1 h2 b hb x hx
  have hx1 : 1 ≤ x := le_trans (by norm_num) hx
  have hx0 : 0 < x := by linarith
  unfold OS.s2Sq
  refine Real.tsum_le_of_sum_range_le (fun n => ?_) fun N => ?_
  · split_ifs
    · exact le_rfl
    · positivity
  have hpt : ∀ n ∈ Finset.range N,
      (if n.Prime ∧ Real.sqrt x < (n : ℝ) then 0 else Λ n ^ 2 * η ((n : ℝ) / x) ^ 2) ≤
        (if (n : ℝ) ≤ Real.sqrt x then Λ n ^ 2 * η ((n : ℝ) / x) ^ 2 else 0) +
          (if ¬n.Prime then Λ n ^ 2 else 0) * b ((n : ℝ) / x) ^ 2 := by
    intro n _
    have hη : η ((n : ℝ) / x) ^ 2 ≤ b ((n : ℝ) / x) ^ 2 := by
      have hn0 : 0 ≤ (n : ℝ) / x := div_nonneg (Nat.cast_nonneg n) hx0.le
      have h := abs_le_supFn hb hn0 le_rfl
      calc η ((n : ℝ) / x) ^ 2 = |η ((n : ℝ) / x)| ^ 2 := (sq_abs _).symm
        _ ≤ b ((n : ℝ) / x) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    have hA : 0 ≤ Λ n ^ 2 * η ((n : ℝ) / x) ^ 2 := by positivity
    have hB : 0 ≤ Λ n ^ 2 * b ((n : ℝ) / x) ^ 2 := by positivity
    have hC : Λ n ^ 2 * η ((n : ℝ) / x) ^ 2 ≤ Λ n ^ 2 * b ((n : ℝ) / x) ^ 2 :=
      mul_le_mul_of_nonneg_left hη (sq_nonneg _)
    by_cases hp : n.Prime
    · by_cases hs : (n : ℝ) ≤ Real.sqrt x
      · rw [if_neg (fun h => absurd h.2 (not_lt.mpr hs)), if_pos hs, if_neg (not_not.mpr hp)]
        simp
      · rw [if_pos ⟨hp, not_le.mp hs⟩, if_neg hs, if_neg (not_not.mpr hp)]
        simp
    · rw [if_neg (fun h => hp h.1), if_pos hp]
      split_ifs
      · linarith
      · linarith
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib] at hsum
  have hs := small_le h12 η b hb x hx1 N
  have hbg := big_le h13 η b h1 h2 hb x hx1 N
  refine le_trans hsum (le_trans (add_le_add hs hbg) (le_of_eq ?_))
  unfold MinSp.eBig MinSp.cE0 MinSp.cE1
  ring

end Principia.Common.TernaryGoldbach.EB
