import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

set_option autoImplicit false

/-!
# MathDB 343776 — convexity of Hadamard products in the class `Ω`

Write-up: `mathdb-open-problems/problems/343776/solution.tex` on the `mathdb-results`
branch of `antoshashakov/Principia-Math-In-Progress`, "Convexity of Hadamard products in
the class Ω".  It resolves the unnumbered conjecture on p. 19 of Swaminathan–Wani,
*Sufficient Conditions and Radius Problems for a Starlike Class Involving a Differential
Inequality*, Bull. Korean Math. Soc. **57** (2020) 1409–1426, retained as the open Problem
on published page 1424:

  with `Ω = {f(z) = z + ∑_{n≥2} aₙzⁿ analytic on 𝔻 : |z f'(z) - f(z)| < 1/2 on 𝔻}`,
  is the Hadamard product `f₁ * f₂` convex for every `f₁, f₂ ∈ Ω`?

The answer is **yes**, and the write-up's proof has an analytic shell around an
elementary core.  This module proves the core and carries the shell.

## What is carried, and why

* **Parseval** (`Setup.parseval`): `Eₐ := ∑_{n≥2} (n-1)²|aₙ|² ≤ 1/4` for `f ∈ Ω`.  This is
  the only place the differential inequality defining `Ω` is used, and it needs the
  `L²` theory of boundary values plus monotone convergence in `ρ ↑ 1`.
* **Termwise bounds** on `h'` and `z·h''` by `A r` and `B r` (`Setup.deriv_lb`,
  `Setup.hderiv_ub`) — differentiating the power series term by term.
* **The analytic characterisation of convexity** (`Setup.convex_of_re_pos`), which the
  write-up itself defers to in its last sentence, citing the definition of `𝒞` on
  published page 1410.

## What is proved here

Everything between those, which is the write-up's actual argument:

* `sq_le_four_mul_sq` : `n² ≤ 4(n-1)²` for `n ≥ 2` — with the slack `3k² + 4k` exact.
* `hadamard_bound` : **equation (1)**, `∑_{n≥2} n²|aₙbₙ| ≤ 1`, by Cauchy–Schwarz from
  the two Parseval bounds.  Proved on partial sums, which simultaneously yields the
  summability of the left side, so nothing about `h` is assumed to converge.
* `AB_le_self` : `A r + B r ≤ r` for `0 < r < 1`, because `r^{n-1} ≤ r` when `n ≥ 2`.
* `B_lt_one_sub_A` and `re_one_add_pos` : `|w| < 1 ⇒ 0 < (1 + w).re`, applied to
  `w = z h''(z)/h'(z)` whose modulus is at most `B r / (1 - A r) < 1`.
* `conjecture` : assembling these with the carried shell.

## Sharpness

`f₁ = f₂ = z + z²/2` lies in `Ω` (`extremal_mem`, since `z f' - f = z²/2` exactly), gives
`h = z + z²/4`, and attains **equality** in (1) (`extremal_energy`, `extremal_eq`).  For it
`1 + z h''/h' = (1+z)/(1+z/2)`, whose real part at `z = -r` is `2(1-r)/(2-r) → 0`
(`extremal_order_tendsto_zero`), so no positive *uniform* order of convexity holds —
the conjecture is true but cannot be strengthened to an order.

## Indexing

Everything is reindexed by `k = n - 2`, so `n = k+2` and `n - 1 = k+1`.  No `ℕ`
subtraction appears anywhere.  `Campaigns/MathDB-Formalization/verify_343776.py` checks
the inequality chain, the extremal pair, and the `2(1-r)/(2-r)` decay.
-/

namespace Principia.MathDB.P343776

open Finset

/-! ## The coefficient inequality -/

/-- `n² ≤ 4(n-1)²` for `n ≥ 2`, reindexed as `k = n - 2`.  The slack is exactly
`3k² + 4k`, so equality holds only at `k = 0`, i.e. `n = 2`. -/
theorem sq_le_four_mul_sq (k : ℕ) : ((k : ℝ) + 2) ^ 2 ≤ 4 * ((k : ℝ) + 1) ^ 2 := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith [sq_nonneg (k : ℝ)]

theorem four_mul_sq_sub (k : ℕ) :
    4 * ((k : ℝ) + 1) ^ 2 - ((k : ℝ) + 2) ^ 2 = 3 * (k : ℝ) ^ 2 + 4 * (k : ℝ) := by
  ring

/-! ## Equation (1) — the Hadamard bound -/

/-- `Eₐ = ∑_{n≥2} (n-1)²|aₙ|²`, reindexed. -/
noncomputable def energy (a : ℕ → ℝ) : ℝ := ∑' k : ℕ, ((k : ℝ) + 1) ^ 2 * a (k + 2) ^ 2

/-- `∑_{n≥2} n²|aₙbₙ|`, reindexed.  `a`, `b` are the coefficient *moduli*. -/
noncomputable def hadamard (a b : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, ((k : ℝ) + 2) ^ 2 * (a (k + 2) * b (k + 2))

/-- The partial sums of the Hadamard series are bounded by `4√(Eₐ)√(E_b)`.
This is the Cauchy–Schwarz step, and it is the whole content of equation (1). -/
theorem hadamard_partial_le {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hsa : Summable fun k : ℕ => ((k : ℝ) + 1) ^ 2 * a (k + 2) ^ 2)
    (hsb : Summable fun k : ℕ => ((k : ℝ) + 1) ^ 2 * b (k + 2) ^ 2) (N : ℕ) :
    ∑ k ∈ range N, ((k : ℝ) + 2) ^ 2 * (a (k + 2) * b (k + 2))
      ≤ 4 * (Real.sqrt (energy a) * Real.sqrt (energy b)) := by
  have step1 : ∑ k ∈ range N, ((k : ℝ) + 2) ^ 2 * (a (k + 2) * b (k + 2))
      ≤ 4 * ∑ k ∈ range N, (((k : ℝ) + 1) * a (k + 2)) * (((k : ℝ) + 1) * b (k + 2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have hab : 0 ≤ a (k + 2) * b (k + 2) := mul_nonneg (ha _) (hb _)
    have := sq_le_four_mul_sq k
    nlinarith [hab]
  have cs := Real.sum_mul_le_sqrt_mul_sqrt (range N)
    (fun k => ((k : ℝ) + 1) * a (k + 2)) (fun k => ((k : ℝ) + 1) * b (k + 2))
  have hexp : ∀ (v : ℕ → ℝ) (k : ℕ),
      (((k : ℝ) + 1) * v (k + 2)) ^ 2 = ((k : ℝ) + 1) ^ 2 * v (k + 2) ^ 2 :=
    fun v k => by ring
  have hA : ∑ k ∈ range N, (((k : ℝ) + 1) * a (k + 2)) ^ 2 ≤ energy a := by
    rw [energy]
    simp_rw [hexp]
    exact hsa.sum_le_tsum _ (fun k _ => by positivity)
  have hB : ∑ k ∈ range N, (((k : ℝ) + 1) * b (k + 2)) ^ 2 ≤ energy b := by
    rw [energy]
    simp_rw [hexp]
    exact hsb.sum_le_tsum _ (fun k _ => by positivity)
  have hmono : Real.sqrt (∑ k ∈ range N, (((k : ℝ) + 1) * a (k + 2)) ^ 2)
        * Real.sqrt (∑ k ∈ range N, (((k : ℝ) + 1) * b (k + 2)) ^ 2)
      ≤ Real.sqrt (energy a) * Real.sqrt (energy b) :=
    mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  linarith [cs, hmono]

/-- Every partial sum of the Hadamard series is at most `1`.  Both the bound and the
convergence of that series come from this single statement. -/
theorem hadamard_partial_le_one {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hsa : Summable fun k : ℕ => ((k : ℝ) + 1) ^ 2 * a (k + 2) ^ 2)
    (hsb : Summable fun k : ℕ => ((k : ℝ) + 1) ^ 2 * b (k + 2) ^ 2)
    (hEa : energy a ≤ 1 / 4) (hEb : energy b ≤ 1 / 4) (N : ℕ) :
    ∑ k ∈ range N, ((k : ℝ) + 2) ^ 2 * (a (k + 2) * b (k + 2)) ≤ 1 := by
  refine (hadamard_partial_le ha hb hsa hsb N).trans ?_
  have hv : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h1 : Real.sqrt (energy a) ≤ 1 / 2 := by
    have := Real.sqrt_le_sqrt hEa; rwa [hv] at this
  have h2 : Real.sqrt (energy b) ≤ 1 / 2 := by
    have := Real.sqrt_le_sqrt hEb; rwa [hv] at this
  nlinarith [Real.sqrt_nonneg (energy a), Real.sqrt_nonneg (energy b)]

theorem hadamard_term_nonneg {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (k : ℕ) : 0 ≤ ((k : ℝ) + 2) ^ 2 * (a (k + 2) * b (k + 2)) := by
  have h1 := ha (k + 2)
  have h2 := hb (k + 2)
  positivity

/-- **Equation (1)**: `∑_{n≥2} n²|aₙbₙ| ≤ 1` whenever both energies are at most `1/4`. -/
theorem hadamard_bound {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hsa : Summable fun k : ℕ => ((k : ℝ) + 1) ^ 2 * a (k + 2) ^ 2)
    (hsb : Summable fun k : ℕ => ((k : ℝ) + 1) ^ 2 * b (k + 2) ^ 2)
    (hEa : energy a ≤ 1 / 4) (hEb : energy b ≤ 1 / 4) :
    hadamard a b ≤ 1 :=
  Real.tsum_le_of_sum_range_le (hadamard_term_nonneg ha hb)
    (hadamard_partial_le_one ha hb hsa hsb hEa hEb)

/-- The Hadamard series converges — a by-product of the same partial-sum bound, so
nothing about `h` has to be assumed. -/
theorem hadamard_summable {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hsa : Summable fun k : ℕ => ((k : ℝ) + 1) ^ 2 * a (k + 2) ^ 2)
    (hsb : Summable fun k : ℕ => ((k : ℝ) + 1) ^ 2 * b (k + 2) ^ 2)
    (hEa : energy a ≤ 1 / 4) (hEb : energy b ≤ 1 / 4) :
    Summable fun k : ℕ => ((k : ℝ) + 2) ^ 2 * (a (k + 2) * b (k + 2)) :=
  summable_of_sum_range_le (c := 1) (hadamard_term_nonneg ha hb)
    (hadamard_partial_le_one ha hb hsa hsb hEa hEb)

/-! ## `A r + B r ≤ r` -/

/-- `A r = ∑_{n≥2} n|cₙ| r^{n-1}`. -/
noncomputable def A (c : ℕ → ℝ) (r : ℝ) : ℝ :=
  ∑' k : ℕ, ((k : ℝ) + 2) * c (k + 2) * r ^ (k + 1)

/-- `B r = ∑_{n≥2} n(n-1)|cₙ| r^{n-1}`. -/
noncomputable def B (c : ℕ → ℝ) (r : ℝ) : ℝ :=
  ∑' k : ℕ, ((k : ℝ) + 2) * ((k : ℝ) + 1) * c (k + 2) * r ^ (k + 1)

/-- Termwise: `n|cₙ|r^{n-1} + n(n-1)|cₙ|r^{n-1} = n²|cₙ|r^{n-1} ≤ r · n²|cₙ|`. -/
theorem term_le {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (k : ℕ) :
    ((k : ℝ) + 2) * c (k + 2) * r ^ (k + 1)
        + ((k : ℝ) + 2) * ((k : ℝ) + 1) * c (k + 2) * r ^ (k + 1)
      ≤ r * (((k : ℝ) + 2) ^ 2 * c (k + 2)) := by
  have hpow : r ^ (k + 1) ≤ r := by
    calc r ^ (k + 1) = r * r ^ k := by ring
      _ ≤ r * 1 := by
          have : r ^ k ≤ 1 := pow_le_one₀ hr0.le hr1.le
          nlinarith
      _ = r := by ring
  have hnn : 0 ≤ ((k : ℝ) + 2) ^ 2 * c (k + 2) := by
    have := hc (k + 2); positivity
  have hid : ((k : ℝ) + 2) * c (k + 2) * r ^ (k + 1)
      + ((k : ℝ) + 2) * ((k : ℝ) + 1) * c (k + 2) * r ^ (k + 1)
      = r ^ (k + 1) * (((k : ℝ) + 2) ^ 2 * c (k + 2)) := by ring
  rw [hid]
  exact mul_le_mul_of_nonneg_right hpow hnn

/-- **`A r + B r ≤ r`** whenever `∑ n²|cₙ| ≤ 1` and `0 < r < 1`. -/
theorem AB_le_self {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hs : Summable fun k : ℕ => ((k : ℝ) + 2) ^ 2 * c (k + 2))
    (h1 : ∑' k : ℕ, ((k : ℝ) + 2) ^ 2 * c (k + 2) ≤ 1)
    (hA : Summable fun k : ℕ => ((k : ℝ) + 2) * c (k + 2) * r ^ (k + 1))
    (hB : Summable fun k : ℕ => ((k : ℝ) + 2) * ((k : ℝ) + 1) * c (k + 2) * r ^ (k + 1)) :
    A c r + B c r ≤ r := by
  have hsum : A c r + B c r
      ≤ ∑' k : ℕ, r * (((k : ℝ) + 2) ^ 2 * c (k + 2)) := by
    rw [A, B, ← hA.tsum_add hB]
    exact (hA.add hB).tsum_le_tsum (fun k => term_le hc hr0 hr1 k) (hs.mul_left r)
  have : ∑' k : ℕ, r * (((k : ℝ) + 2) ^ 2 * c (k + 2)) ≤ r := by
    rw [hs.tsum_mul_left]
    nlinarith
  linarith

/-! ## The convexity step -/

/-- `B r < 1 - A r`, and `A r < 1`, from `A r + B r ≤ r < 1` and `0 ≤ B r`.
Note `0 ≤ A r` is *not* needed: the first conjunct is pure arithmetic and the second
needs only that the discarded summand `B r` is nonnegative. -/
theorem B_lt_one_sub_A {Ar Br r : ℝ} (hB0 : 0 ≤ Br)
    (h : Ar + Br ≤ r) (hr1 : r < 1) : Br < 1 - Ar ∧ Ar < 1 := by
  constructor <;> linarith

/-- The elementary fact the analytic characterisation is fed: `‖w‖ < 1 ⇒ 0 < (1+w).re`.
`w` is `z h''(z)/h'(z)`, whose modulus is at most `B r / (1 - A r)`. -/
theorem re_one_add_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (1 + w).re := by
  have h : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
  have h2 : |w.re| < 1 := lt_of_le_of_lt h hw
  have h3 : -1 < w.re := (abs_lt.mp h2).1
  have h4 : (1 + w).re = 1 + w.re := by simp
  rw [h4]
  linarith

/-- The modulus bound actually available: `|z h''/h'| ≤ B r / (1 - A r) < 1`. -/
theorem quotient_lt_one {Ar Br t : ℝ} (hA1 : Ar < 1)
    (hBA : Br < 1 - Ar) (ht : t ≤ Br / (1 - Ar)) : t < 1 := by
  have hpos : 0 < 1 - Ar := by linarith
  have : Br / (1 - Ar) < 1 := (div_lt_one hpos).mpr hBA
  linarith

/-! ## The carried analytic shell -/

/-- The three analytic inputs the write-up itself attributes or defers to. -/
structure Setup where
  /-- coefficient moduli of `f₁` -/
  a : ℕ → ℝ
  /-- coefficient moduli of `f₂` -/
  b : ℕ → ℝ
  /-- coefficient moduli of the Hadamard product `h = f₁ * f₂` -/
  c : ℕ → ℝ
  ha : ∀ n, 0 ≤ a n
  hb : ∀ n, 0 ≤ b n
  /-- `|cₙ| = |aₙ||bₙ|` — the Hadamard product is coefficientwise multiplication. -/
  hc : ∀ n, c n = a n * b n
  hsa : Summable fun k : ℕ => ((k : ℝ) + 1) ^ 2 * a (k + 2) ^ 2
  hsb : Summable fun k : ℕ => ((k : ℝ) + 1) ^ 2 * b (k + 2) ^ 2
  /-- **Parseval + monotone convergence**: the only use of the defining inequality of `Ω`. -/
  parseval_a : energy a ≤ 1 / 4
  parseval_b : energy b ≤ 1 / 4
  /-- summability of the two derivative series on each circle `|z| = r < 1` -/
  hsA : ∀ r : ℝ, 0 < r → r < 1 →
    Summable fun k : ℕ => ((k : ℝ) + 2) * c (k + 2) * r ^ (k + 1)
  hsB : ∀ r : ℝ, 0 < r → r < 1 →
    Summable fun k : ℕ => ((k : ℝ) + 2) * ((k : ℝ) + 1) * c (k + 2) * r ^ (k + 1)
  /-- `Q z = 1 + z h''(z)/h'(z)`, the quantity the convexity criterion is stated for. -/
  Q : ℂ → ℂ
  /-- **termwise differentiation**: `‖Q z - 1‖ ≤ B r / (1 - A r)` on `‖z‖ = r`. -/
  quotient_bound : ∀ z : ℂ, ∀ r : ℝ, 0 < r → r < 1 → ‖z‖ = r →
    ‖Q z - 1‖ ≤ B c r / (1 - A c r)
  /-- **the analytic characterisation of convexity** (Swaminathan–Wani, published p. 1410),
  which the write-up's final sentence invokes by name. -/
  Convex_h : Prop
  convex_of_re_pos : (∀ z : ℂ, ‖z‖ < 1 → 0 < (Q z).re) → Convex_h

namespace Setup

variable (S : Setup)

theorem A_nonneg {r : ℝ} (hr0 : 0 < r) : 0 ≤ A S.c r := by
  refine tsum_nonneg fun k => ?_
  have h1 : 0 ≤ S.c (k + 2) := by rw [S.hc]; exact mul_nonneg (S.ha _) (S.hb _)
  positivity

theorem B_nonneg {r : ℝ} (hr0 : 0 < r) : 0 ≤ B S.c r := by
  refine tsum_nonneg fun k => ?_
  have h1 : 0 ≤ S.c (k + 2) := by rw [S.hc]; exact mul_nonneg (S.ha _) (S.hb _)
  positivity

theorem c_nonneg (n : ℕ) : 0 ≤ S.c n := by
  rw [S.hc]; exact mul_nonneg (S.ha _) (S.hb _)

theorem c_summable : Summable fun k : ℕ => ((k : ℝ) + 2) ^ 2 * S.c (k + 2) := by
  have := hadamard_summable S.ha S.hb S.hsa S.hsb S.parseval_a S.parseval_b
  refine this.congr fun k => ?_
  rw [S.hc]

/-- **Equation (1)** for this `Setup`. -/
theorem eq_one : ∑' k : ℕ, ((k : ℝ) + 2) ^ 2 * S.c (k + 2) ≤ 1 := by
  have := hadamard_bound S.ha S.hb S.hsa S.hsb S.parseval_a S.parseval_b
  rw [hadamard] at this
  refine le_trans (le_of_eq (tsum_congr fun k => ?_)) this
  rw [S.hc]

theorem AB_le {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : A S.c r + B S.c r ≤ r :=
  AB_le_self S.c_nonneg hr0 hr1 S.c_summable S.eq_one (S.hsA r hr0 hr1) (S.hsB r hr0 hr1)

/-- The three bounds the write-up displays on the circle `‖z‖ = r`: each of `A r`, `B r`
is at most `r`, and `B r < 1 - A r` — the last being what makes `h'` non-vanishing and
dominant over `z h''`. -/
theorem disc_bounds {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    A S.c r ≤ r ∧ B S.c r ≤ r ∧ B S.c r < 1 - A S.c r := by
  have h1 := S.A_nonneg hr0
  have h2 := S.B_nonneg hr0
  have h3 := S.AB_le hr0 hr1
  exact ⟨by linarith, by linarith, (B_lt_one_sub_A h2 h3 hr1).1⟩

/-- `Re (1 + z h''/h') > 0` throughout `𝔻` — the criterion's hypothesis. -/
theorem re_Q_pos (hQ0 : 0 < (S.Q 0).re) :
    ∀ z : ℂ, ‖z‖ < 1 → 0 < (S.Q z).re := by
  intro z hz
  rcases eq_or_lt_of_le (norm_nonneg z) with h0 | h0
  · have hz0 : z = 0 := by
      have := h0.symm
      simpa using norm_eq_zero.mp this
    rw [hz0]; exact hQ0
  · obtain ⟨hAr, -, hBA⟩ := S.disc_bounds h0 hz
    have hA1 : A S.c ‖z‖ < 1 := lt_of_le_of_lt hAr hz
    have hb := S.quotient_bound z ‖z‖ h0 hz rfl
    have hlt : ‖S.Q z - 1‖ < 1 := quotient_lt_one hA1 hBA hb
    have hre := re_one_add_pos hlt
    have : (1 : ℂ) + (S.Q z - 1) = S.Q z := by ring
    rwa [this] at hre

/-- **The conjecture**: `f₁ * f₂` is convex for every `f₁, f₂ ∈ Ω`. -/
theorem conjecture (hQ0 : 0 < (S.Q 0).re) : S.Convex_h :=
  S.convex_of_re_pos (S.re_Q_pos hQ0)

end Setup

/-! ## Sharpness: the bound (1) is attained, and no uniform order survives -/

/-- `f(z) = z + z²/2` satisfies `z f'(z) - f(z) = z²/2`, so `|z f' - f| = |z|²/2 < 1/2`
on `𝔻`: it lies in `Ω`. -/
theorem extremal_mem (z : ℂ) : z * (1 + z) - (z + z ^ 2 / 2) = z ^ 2 / 2 := by ring

theorem extremal_mem_abs {z : ℂ} (hz : ‖z‖ < 1) :
    ‖z * (1 + z) - (z + z ^ 2 / 2)‖ < 1 / 2 := by
  rw [extremal_mem, norm_div, norm_pow]
  have h : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  linarith

/-- Its energy is exactly `1/4` — equality in the Parseval bound. -/
theorem extremal_energy : (1 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ 2 = 1 / 4 := by norm_num

/-- and the product `h = z + z²/4` attains **equality** in (1): `2² · (1/4) = 1`. -/
theorem extremal_eq : (2 : ℝ) ^ 2 * (1 / 4 : ℝ) = 1 := by norm_num

/-- For `h = z + z²/4`, `1 + z h''(z)/h'(z) = (1+z)/(1+z/2)`. -/
theorem extremal_quotient {z : ℂ} (hz : (2 : ℂ) + z ≠ 0) :
    1 + z * (1 / 2) / (1 + z / 2) = (1 + z) / (1 + z / 2) := by
  have h : (1 : ℂ) + z / 2 = (2 + z) / 2 := by ring
  rw [h]
  field_simp
  ring

/-- On the real segment `z = -r`, that quotient equals `2(1-r)/(2-r)`. -/
theorem extremal_at_neg {r : ℝ} (hr : r < 1) :
    (1 + (-r : ℝ)) / (1 + (-r) / 2) = 2 * (1 - r) / (2 - r) := by
  have h : (1 : ℝ) + (-r) / 2 ≠ 0 := by intro h; nlinarith
  field_simp
  ring

/-- **No positive uniform order of convexity.**  `2(1-r)/(2-r) → 0` as `r ↑ 1`, so the
infimum of `Re (1 + z h''/h')` over `𝔻` is `0` for this product, even though it is
strictly positive at every point. -/
theorem extremal_order_tendsto_zero :
    Filter.Tendsto (fun r : ℝ => 2 * (1 - r) / (2 - r)) (nhds 1) (nhds 0) := by
  have hnum : Filter.Tendsto (fun r : ℝ => 2 * (1 - r)) (nhds 1) (nhds 0) := by
    have h : Filter.Tendsto (fun r : ℝ => 2 * (1 - r)) (nhds 1) (nhds (2 * (1 - 1))) :=
      (tendsto_const_nhds.sub Filter.tendsto_id).const_mul 2
    simpa using h
  have hden : Filter.Tendsto (fun r : ℝ => 2 - r) (nhds 1) (nhds 1) := by
    have h : Filter.Tendsto (fun r : ℝ => 2 - r) (nhds 1) (nhds (2 - 1)) :=
      tendsto_const_nhds.sub Filter.tendsto_id
    simpa only [show (2 : ℝ) - 1 = 1 from by norm_num] using h
  -- `Tendsto.div` returns the `Pi.div` of the two functions, not the pointwise quotient.
  have hres := hnum.div hden one_ne_zero
  simp only [zero_div] at hres
  exact hres

end Principia.MathDB.P343776
