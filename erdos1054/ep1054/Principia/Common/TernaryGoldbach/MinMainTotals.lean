/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.OstopL
import Principia.Common.Goldbach.Vaughan

set_option autoImplicit false

/-!
# The Totals of `minarcs.tex` (layer M-A): the first case of the Main Theorem from NAMED pieces

**Two constants of `OL.MinMainL`'s first case are NOT reachable from the pieces, and both
failures are Lean-checked.** `OL.krawL` is `krawAt 0.5 22.7538` (`krawL_eq`); the pieces give
`krawAt 0.811 45.7575` (`minMainL1c_of_pieces`), and `not_arith_typed` proves that the Totals
arithmetic `ArithAt 0.5 22.7538` — the only route from the pieces to the typed constants — is
FALSE. So `minMainL1_of_pieces` in the brief's form cannot exist; this file proves the corrected
statement and fences the typed one.

## Finding 1 — the AM-GM of the Conclusion halves a summand (`0.5` must be `0.811`)

`minarcs.tex` 5549-5566 (and, unchanged, the book `minarctotals.tex` 2257-2288) bound
`√(C(ℓ+0.002) + (log 4 + ℓ)/2)·√(0.30214ℓ + 0.67506)` by
`½(A/√ρ + √ρ·B)` and then write its constant as `½(log 2/√ρ + (√ρ/2)·0.67506) = 0.49911`.
The `B`-summand is `(√ρ/2)·0.67506`, not half of it: the constant is
`log 2/(2√ρ) + √ρ·0.67506/2 = 0.81019` at `√ρ = 1.84332`. It is not an artefact of the
AM-GM: `√A√B − (0.27125C + 0.41415)ℓ` itself reaches `0.80988` inside the admissible range
(`x = 3.4·10²³`, `log δ₀q = 12.235`; at Helfgott's own `x = 10²⁵`, `δ₀q = 4·10⁵` it is `0.80984`,
where he claims `≤ 0.5`). `amgm_main` proves the constant `0.811` (`√ρ = 1.8434`);
`not_arith_05` proves `0.5` is unreachable even with `L`'s constant raised to `45.7575`.

## Finding 2 — Helfgott's book corrects `S_{I,2}`: `L`'s `1/q` constant is `45.7575`, not `22.7538`

The arXiv `eq:cleson` (5092-5102) uses `c_1 = 1.0000028 > 1 + 8 log 2/V` inside `lem:bosta2`,
but at scale `x/v` with `D = U` the lemma's `c_1` is `1 + 8 log 2·vU/x ≤ 1 + 8 log 2/(x/UV) =
1 + 4 log 2/√(qδ₀)`, up to `1.98`. The book (`minarctotals.tex` 195, 362-399, 1499-1548) replaces
it by `c_+`, and its `eq:cleson` reads `2.49157x/√(qδ₀) + min(1, 4c₀'/δ²)(3/2 log q +
2.74107)x/φ(q) + (3.59676 log δ₀ + 27.3032 log q + 91.515)x/(qδ₀) + (22.9812 log x +
411.424)x^{2/3}`. It also carries the planner's corrections (H1: `ε = 0.07`, `log δq³`; H2: the
`min` branch dropped; the missing `x^{2/3}` mass). The pieces here are the BOOK's. Halving,
`(3.59676, 27.3032, 91.515)/2 = (1.79838, 13.6516, 45.7575)`: `A = 13.6516` and `B = 1.7984`
survive, `C = 22.7538` does not. `not_arith_typedL` proves `22.7538` unreachable even with the
main constant raised to `1.5`.

## The spine (every link either PROVED or a named `Prop`)

```
 A0  vaughan_split : S_{η₂} = S_{I,1} − S_{I,2} + S_{II} + S_{0,∞} + S_{0,2}   PROVED
     s0i_eq_zero (V < x/4), s02_norm_le (|S_{0,2}| ≤ 3(log x + 1))            PROVED
 A1  TypeI1 : |S_{I,1}| ≤ bI1  (book eq:therwald 1434-1441)                   OPEN
 A2  TypeI2 : |S_{I,2}| ≤ bI2  (book eq:cleson 1542-1548)                     OPEN
 A3  TypeII : |S_{II}|  ≤ bII  (book eq:senorburns 1710-1717)                 OPEN
 A5+A9+A10  arith_811 : ArithAt 0.811 45.7575                                PROVED
 minMain1_of_arith → minMainL1c_of_pieces : TypeI1 → TypeI2 → TypeII →
     MinMain1At 0.811 45.7575                                  (application only)
 minMainL_iff : OL.MinMainL ↔ MinMain1At 0.5 22.7538 ∧ MinMain2L
 not_arith_05 : ¬ ArithAt 0.5 45.7575,  not_arith_typedL : ¬ ArithAt 1.5 22.7538
```

The pieces are defined as Helfgott's sums (`eq:nielsen`, twisted by `f = 1_{(n,2)=1}`) in
convolution form, `sP (g ∗ h)`; `sP_mul_eq` unfolds each to the double sum of `eq:nielsen`.
`S_{0,2}` runs over `n ∣ 2^∞` (the arXiv text says `n ∣ 2` and `0`). The parameters are the first
choice (`eq:humid`): `U = x^{2/3}/(9√(qδ₀))`, `V = (9/2)x^{1/3}`.

## Constants and margins (`scratchpad/mintot/*.py`, mpmath)

* main term: `√ρ = 1.8434`: `1/(2√ρ) = 0.2712379 ≤ 0.27125`, `ℓ`-coefficient `0.4141014 ≤
  0.41415`, constant `0.8102106 + 0.000542C ≤ 0.811` using `C_{x,t} ≤ 0.723 + 0.0625 log t`
  (`cXT_bounds`; `9x^{1/3}/(2.004t) ≥ 13.47 ≥ e²` from `δ₀q ≤ x^{1/3}/3`, `dz_q_le`).
* `2.49157 ≤ 2.5` (margin `0.00843`); `q/φ(q)` part `6.11676 + 2.74107 = 8.85783 ≤ 80/9`
  (`0.03106`); `1/q` part `(1.79838, 13.6516, 45.7575) ≤ (1.7984, 13.6516, 45.7575)`
  (`2·10⁻⁵, 0, 0`); `min(1, c/δ²) ≤ 2/δ₀` for `c ≤ 64` (`capM_le`).
* lower order (`low_le`): every `x^{2/3}` term, `2.73908x^{5/6}` and `3(log x + 1)` total
  `2.9404x^{5/6}` at `x = 3.4·10²³` (`2.8591` at `10²⁵`, `2.8051` at `4.9·10²⁶`): margin
  `0.2596x^{5/6}` in `3.2x^{5/6}`.
* fences: `not_arith_05` at `q = 1`, `δ = 2³⁰`, `x = ((4.008/9)·2⁴²)³` (`C = log 2` exactly)
  by `0.2407x/√t`; `not_arith_typedL` at `q = 2⁷`, `δ = 0`, `x = ((2.004/9)·2²⁹)³`
  (`C = log(26/21)`) by `≥ 0.098x`.

## Consequence downstream (floating-point scoping, NOT certified)

`OL.gYL` carries `0.5` (in `(R log 2r + 0.5)√ϝ`) and `OL.lLc` carries `22.7538`. With
`(0.811, 45.7575)`, `g_Y(10²⁵, r)` rises by `3.58%` at `r = 1.5·10⁵` (`2.89%` at `10⁶`,
`2.17%` at `10⁷`; `scratchpad/mintot/gimpact.py`). At `≈0.0078` of `M̃` per `1%` of `g`
(planner H4) that is `≈ +0.02-0.028` on `M̃`, against the `≈0.017` margin `OL.MNumL` at
`0.8095` was recorded with: `OL.MNumL HW.phi 8.54 0.8095 0.6406` must be recomputed and is
likely FALSE on the corrected `g`.
-/

namespace Principia.Common.TernaryGoldbach.MT

open ArithmeticFunction Principia.Common.Goldbach
open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-! ## (1) Link A0 — the twisted smoothed Vaughan split, PROVED -/

/-- **`f = 1_{(n,2)=1}`** (`minarcs.tex` `eq:joroy` 775-778 at `v = 2`), completely
multiplicative. -/
noncomputable def fOdd : ArithmeticFunction ℝ :=
  ⟨fun n => if n % 2 = 1 then 1 else 0, by simp⟩

theorem fOdd_apply (n : ℕ) : fOdd n = if n % 2 = 1 then 1 else 0 :=
  rfl

/-- `f` is completely multiplicative. -/
theorem fOdd_mul (a b : ℕ) : fOdd (a * b) = fOdd a * fOdd b := by
  rw [fOdd_apply, fOdd_apply, fOdd_apply, Nat.mul_mod]
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;> simp [ha, hb]

theorem fOdd_nonneg (n : ℕ) : 0 ≤ fOdd n := by
  rw [fOdd_apply]
  split_ifs <;> norm_num

theorem fOdd_le_one (n : ℕ) : fOdd n ≤ 1 := by
  rw [fOdd_apply]
  split_ifs <;> norm_num

/-- **The twist `g ↦ g·f`.** -/
noncomputable def tw (g : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  g.pmul fOdd

theorem tw_apply (g : ArithmeticFunction ℝ) (n : ℕ) : tw g n = g n * fOdd n :=
  ArithmeticFunction.pmul_apply

/-- **The twist by a completely multiplicative `f` is a ring map for `∗`.** -/
theorem tw_mul (g h : ArithmeticFunction ℝ) : tw (g * h) = tw g * tw h := by
  ext n
  rw [tw_apply, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [tw_apply, tw_apply, ← (Nat.mem_divisorsAntidiagonal.mp hp).1, fOdd_mul]
  ring

theorem tw_add (g h : ArithmeticFunction ℝ) : tw (g + h) = tw g + tw h := by
  ext n
  rw [tw_apply, ArithmeticFunction.add_apply, ArithmeticFunction.add_apply, tw_apply, tw_apply]
  ring

theorem tw_neg (g : ArithmeticFunction ℝ) : tw (-g) = -tw g := by
  ext n
  rw [tw_apply, ArithmeticFunction.neg_apply, ArithmeticFunction.neg_apply, tw_apply]
  ring

theorem tw_sub (g h : ArithmeticFunction ℝ) : tw (g - h) = tw g - tw h := by
  rw [sub_eq_add_neg, tw_add, tw_neg, ← sub_eq_add_neg]

/-- **The smoothed character `η₂(n/x)e(nα)`.** -/
noncomputable def wt (x α : ℝ) (n : ℕ) : ℂ :=
  ((HW.eta2 ((n : ℝ) / x) : ℝ) : ℂ) * e ((n : ℝ) * α)

/-- **`∑_{n ≤ x} g(n)η₂(n/x)e(nα)`**: every Vaughan piece is this for a convolution `g`. -/
noncomputable def sP (g : ArithmeticFunction ℝ) (x α : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ((g n : ℝ) : ℂ) * wt x α n

theorem sP_add (g h : ArithmeticFunction ℝ) (x α : ℝ) :
    sP (g + h) x α = sP g x α + sP h x α := by
  unfold sP
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [ArithmeticFunction.add_apply]
  push_cast
  ring

theorem sP_sub (g h : ArithmeticFunction ℝ) (x α : ℝ) :
    sP (g - h) x α = sP g x α - sP h x α := by
  unfold sP
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [sub_eq_add_neg g h, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply]
  push_cast
  ring

/-- **A convolution piece is the double sum of `eq:nielsen`**: `∑_d g(d) ∑_m h(m) w(dm)`
(`MinSum.sum_Ioc_mul_weight_eq_sum_sum`). -/
theorem sP_mul_eq (g h : ArithmeticFunction ℝ) (x α : ℝ) :
    sP (g * h) x α = ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, ((g d : ℝ) : ℂ) *
      ∑ m ∈ Finset.Ioc 0 (⌊x⌋₊ / d), ((h m : ℝ) : ℂ) * wt x α (d * m) :=
  MinSum.sum_Ioc_mul_weight_eq_sum_sum g h (wt x α) ⌊x⌋₊

/-- `η₂ = 0` on `[1, ∞)`. -/
theorem eta2_zero_of_one_le (t : ℝ) (ht : 1 ≤ t) : HW.eta2 t = 0 := by
  unfold HW.eta2
  rw [if_pos (by linarith)]
  have h2 : Real.log 2 ≤ Real.log (2 * t) := Real.log_le_log (by norm_num) (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmax : max (Real.log 2 - |Real.log (2 * t)|) 0 = 0 := by
    rw [abs_of_nonneg (show (0 : ℝ) ≤ Real.log (2 * t) by linarith)]
    exact max_eq_right (by linarith)
  rw [hmax, mul_zero]

/-- `η₂ = 0` on `(-∞, 1/4]`. -/
theorem eta2_zero_of_le (t : ℝ) (ht : t ≤ 1 / 4) : HW.eta2 t = 0 := by
  unfold HW.eta2
  by_cases h : 0 < t
  · rw [if_pos h]
    have h1 : Real.log (2 * t) ≤ Real.log (1 / 2) := Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
    have h3 := neg_abs_le (Real.log (2 * t))
    have hmax : max (Real.log 2 - |Real.log (2 * t)|) 0 = 0 := max_eq_right (by linarith)
    rw [hmax, mul_zero]
  · rw [if_neg h]

theorem eta2_nonneg (t : ℝ) : 0 ≤ HW.eta2 t := by
  unfold HW.eta2
  split_ifs
  · exact mul_nonneg (by norm_num) (le_max_right _ _)
  · exact le_refl 0

theorem eta2_le (t : ℝ) : HW.eta2 t ≤ 4 * Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold HW.eta2
  split_ifs
  · have h : max (Real.log 2 - |Real.log (2 * t)|) 0 ≤ Real.log 2 :=
      max_le (by linarith [abs_nonneg (Real.log (2 * t))]) hl2.le
    linarith
  · linarith

/-- **`S_{η₂}(α, x)` is the finite sum `sP Λ`** (`η₂` vanishes beyond `1`, `Λ(0) = 0`). -/
theorem smSum_eq_sP (x α : ℝ) (hx : 0 < x) : Smooth.smSum HW.eta2 x α = sP Λ x α := by
  unfold Smooth.smSum sP
  rw [tsum_eq_sum (s := Finset.Ioc 0 ⌊x⌋₊)]
  · refine Finset.sum_congr rfl fun n _ => ?_
    unfold wt
    ring
  · intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp
    · have hN : ⌊x⌋₊ < n := by
        by_contra hc
        exact hn (Finset.mem_Ioc.mpr ⟨hpos, not_lt.mp hc⟩)
      have hxn : x < (n : ℝ) := Nat.lt_of_floor_lt hN
      have h1 : 1 ≤ (n : ℝ) / x := by
        rw [le_div_iff₀ hx]
        linarith
      rw [eta2_zero_of_one_le _ h1]
      simp

/-- **`a = μ_{≤U}`** (`eq:nielsen`, `m ≤ U`). -/
noncomputable def aU (U : ℝ) : ArithmeticFunction ℝ :=
  MinSum.truncate (μ : ArithmeticFunction ℝ) ⌊U⌋₊

/-- **`b = Λ_{≤V}`** (`eq:nielsen`, `d ≤ V`). -/
noncomputable def bV (V : ℝ) : ArithmeticFunction ℝ :=
  MinSum.truncate Λ ⌊V⌋₊

/-- **`S_{I,1}`** (`eq:nielsen` 766): `∑_{m≤U} μ(m)f(m) ∑_n (log n) f(n) η₂(mn/x) e(αmn)`. -/
noncomputable def sI1 (x α U : ℝ) : ℂ :=
  sP (tw (aU U) * tw ArithmeticFunction.log) x α

/-- **`S_{I,2}`** (`eq:nielsen` 767-768): `∑_{d≤V} Λ(d)f(d) ∑_{m≤U} μ(m)f(m) ∑_n f(n)…`. -/
noncomputable def sI2 (x α U V : ℝ) : ℂ :=
  sP (tw (aU U) * tw (bV V) * tw (ζ : ArithmeticFunction ℝ)) x α

/-- **`S_{II}`** (`eq:nielsen` 769-770): `∑_{m>U} f(m)(∑_{d∣m, d>U} μ(d)) ∑_{n>V} Λ(n)f(n)…`. -/
noncomputable def sII (x α U V : ℝ) : ℂ :=
  sP (tw ((μ : ArithmeticFunction ℝ) - aU U) * tw (Λ - bV V) * tw (ζ : ArithmeticFunction ℝ)) x α

/-- **`S_{0,∞}`** (`eq:nielsen` 771): `∑_{n≤V} Λ(n)f(n)η₂(n/x)e(αn)`. -/
noncomputable def s0i (x α V : ℝ) : ℂ :=
  sP (tw (bV V)) x α

/-- **`S_{0,2}`**: the even `n` (`eq:sofot` 782-784; it runs over `n ∣ 2^∞`, not `n ∣ 2`). -/
noncomputable def s02 (x α : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ((Λ n * (1 - fOdd n) : ℝ) : ℂ) * wt x α n

/-- **Vaughan's identity twisted by `f`**: `MinSum.vaughan_identity` pushed through `tw`. -/
theorem tw_vaughan (U V : ℝ) :
    tw Λ = tw (aU U) * tw ArithmeticFunction.log -
        tw (aU U) * tw (bV V) * tw (ζ : ArithmeticFunction ℝ) + tw (bV V) +
      tw ((μ : ArithmeticFunction ℝ) - aU U) * tw (Λ - bV V) * tw (ζ : ArithmeticFunction ℝ) := by
  conv_lhs => rw [MinSum.vaughan_identity (aU U) (bV V)]
  simp only [tw_add, tw_sub, tw_mul]

/-- **Link A0, PROVED — `eq:bob` / `eq:sofot` for `η₂`, `v = 2`**: for every `x > 0` and every
`U, V`, `S_{η₂}(α, x) = S_{I,1} − S_{I,2} + S_{II} + S_{0,∞} + S_{0,2}`. -/
theorem vaughan_split (x α U V : ℝ) (hx : 0 < x) :
    Smooth.smSum HW.eta2 x α =
      sI1 x α U - sI2 x α U V + sII x α U V + s0i x α V + s02 x α := by
  have h1 : sP Λ x α = sP (tw Λ) x α + s02 x α := by
    unfold sP s02
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [tw_apply]
    push_cast
    ring
  rw [smSum_eq_sP x α hx, h1, tw_vaughan U V, sP_add, sP_add, sP_sub]
  unfold sI1 sI2 sII s0i
  ring

/-- **`S_{0,∞} = 0` when `V < x/4`** (minarcs 3777: `η₂` vanishes on `(0, 1/4]`). -/
theorem s0i_eq_zero (x α V : ℝ) (hx : 0 < x) (hV : V < x / 4) : s0i x α V = 0 := by
  unfold s0i sP
  refine Finset.sum_eq_zero fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Ioc.mp hn).1
  rw [tw_apply]
  unfold bV
  rw [MinSum.truncate_apply]
  split_ifs with h
  · have hV0 : 0 ≤ V := by
      by_contra hc
      have h0 : ⌊V⌋₊ = 0 := Nat.floor_of_nonpos (by linarith)
      omega
    have hnV : (n : ℝ) ≤ V := le_trans (by exact_mod_cast h) (Nat.floor_le hV0)
    have hq : (n : ℝ) / x ≤ 1 / 4 := by
      rw [div_le_iff₀ hx]
      linarith
    unfold wt
    rw [eta2_zero_of_le _ hq]
    simp
  · simp

/-- **The even `n ≤ N` carry `∑ Λ(n) ≤ (log₂N + 1) log 2`**: they are the powers of `2`, all
dividing `2^{⌊log₂N⌋+1}`. -/
theorem sum_even_vM_le (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, Λ n * (1 - fOdd n) ≤ ((Nat.log 2 N + 1 : ℕ) : ℝ) * Real.log 2 := by
  have hg0 : ∀ n, 0 ≤ Λ n * (1 - fOdd n) := fun n =>
    mul_nonneg vonMangoldt_nonneg (by linarith [fOdd_le_one n])
  have hsub : (Finset.Ioc 0 N).filter (fun n => Λ n * (1 - fOdd n) ≠ 0) ⊆
      (2 ^ (Nat.log 2 N + 1)).divisors := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨-, hnN⟩, hne⟩ := hn
    have hΛ : Λ n ≠ 0 := left_ne_zero_of_mul hne
    have hf : 1 - fOdd n ≠ 0 := right_ne_zero_of_mul hne
    have hev : n % 2 = 0 := by
      rw [fOdd_apply] at hf
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · exact h
      · rw [if_pos h] at hf
        norm_num at hf
    obtain ⟨p, k, hp, -, rfl⟩ :=
      (isPrimePow_nat_iff n).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
    have h2p : 2 ∣ p ^ k := Nat.dvd_of_mod_eq_zero hev
    have hp2 : p = 2 :=
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h2p)).symm
    subst hp2
    have hlt : 2 ^ k < 2 ^ (Nat.log 2 N + 1) :=
      lt_of_le_of_lt hnN (Nat.lt_pow_succ_log_self (by norm_num) N)
    have hkj : k ≤ Nat.log 2 N + 1 := by
      by_contra hc
      have h2 := Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_le.mp hc).le
      omega
    rw [Nat.mem_divisors]
    exact ⟨Nat.pow_dvd_pow 2 hkj, by positivity⟩
  calc ∑ n ∈ Finset.Ioc 0 N, Λ n * (1 - fOdd n)
      = ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => Λ n * (1 - fOdd n) ≠ 0),
          Λ n * (1 - fOdd n) := (Finset.sum_filter_ne_zero _).symm
    _ ≤ ∑ n ∈ (2 ^ (Nat.log 2 N + 1)).divisors, Λ n * (1 - fOdd n) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => hg0 n
    _ ≤ ∑ n ∈ (2 ^ (Nat.log 2 N + 1)).divisors, Λ n := by
        refine Finset.sum_le_sum fun n _ => ?_
        have h1 := fOdd_nonneg n
        have h2 : 0 ≤ Λ n := vonMangoldt_nonneg
        nlinarith
    _ = Real.log ((2 ^ (Nat.log 2 N + 1) : ℕ) : ℝ) := vonMangoldt_sum
    _ = ((Nat.log 2 N + 1 : ℕ) : ℝ) * Real.log 2 := by
        push_cast
        rw [Real.log_pow]
        push_cast
        ring

/-- **`|S_{0,2}| ≤ 3(log x + 1)`** for `x ≥ 1` (minarcs 5292 prints `S_{0,w} = 0`; it is `O(1)`
for `η₂`, and `O(log x)` is all the Totals need). -/
theorem s02_norm_le (x α : ℝ) (hx : 1 ≤ x) : ‖s02 x α‖ ≤ 3 * (Real.log x + 1) := by
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hx0 : 0 < x := by linarith
  have h1 : ‖s02 x α‖ ≤ 4 * Real.log 2 * ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n * (1 - fOdd n) := by
    unfold s02
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    unfold wt
    have hg : 0 ≤ Λ n * (1 - fOdd n) :=
      mul_nonneg vonMangoldt_nonneg (by linarith [fOdd_le_one n])
    rw [norm_mul, norm_mul, e_norm, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hg, Real.norm_of_nonneg (eta2_nonneg _)]
    have h := eta2_le ((n : ℝ) / x)
    nlinarith
  have h2 := sum_even_vM_le ⌊x⌋₊
  have h3 : ((Nat.log 2 ⌊x⌋₊ : ℕ) : ℝ) * Real.log 2 ≤ Real.log x := by
    rcases Nat.eq_zero_or_pos ⌊x⌋₊ with h0 | hpos
    · rw [h0, Nat.log_zero_right, Nat.cast_zero, zero_mul]
      exact hlx
    · have hp : 2 ^ Nat.log 2 ⌊x⌋₊ ≤ ⌊x⌋₊ := Nat.pow_log_le_self 2 hpos.ne'
      have hpR : (2 : ℝ) ^ Nat.log 2 ⌊x⌋₊ ≤ x := by
        have h : ((2 ^ Nat.log 2 ⌊x⌋₊ : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hp
        push_cast at h
        exact h.trans (Nat.floor_le hx0.le)
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) hpR
  push_cast at h2
  have h4L2 : (0 : ℝ) ≤ 4 * Real.log 2 := by linarith
  have h4 := mul_le_mul_of_nonneg_left h2 h4L2
  have h5 := mul_le_mul_of_nonneg_left h3 h4L2
  nlinarith [mul_nonneg (sub_nonneg.mpr hl2'.le) hlx,
    mul_pos (sub_pos.mpr hl2') (show (0 : ℝ) < Real.log 2 by linarith)]

/-! ## (2) Links A1-A3 — the per-piece bounds, NAMED -/

/-- **`U` of the first choice** (`eq:humid` 4896-4897): `U = x^{2/3}/(9√(qδ₀))`. -/
noncomputable def uA (Y δ : ℝ) (q : ℕ) : ℝ :=
  Y ^ ((2 : ℝ) / 3) / (9 * Real.sqrt (OC.dz δ * q))

/-- **`V` of the first choice** (`eq:humid` 4901-4904): `V = (9/2)x^{1/3}`. -/
noncomputable def vA (Y : ℝ) : ℝ :=
  9 / 2 * Y ^ ((1 : ℝ) / 3)

/-- **`min(1, c/δ²)`** with Helfgott's `c/0 = ∞` (`c > 0`): `c / max(c, δ²)`. -/
noncomputable def capM (c δ : ℝ) : ℝ :=
  c / max c (δ ^ 2)

/-- **`C_{x,t}`** (`minarcs.tex` 5193-5194). `MinSp.rR x t = 0.27125 C_{x,t} + 0.41415`. -/
noncomputable def cXT (x t : ℝ) : ℝ :=
  Real.log (1 + Real.log (4 * t) / (2 * Real.log (9 * x ^ ((1 : ℝ) / 3) / (2.004 * t))))

/-- **The bound of Link A1 — `eq:therwald`** as CORRECTED in Helfgott's book (`minarctotals.tex`
1434-1441; arXiv `minarcs.tex` 5029-5035 had the extra `min` branch (H2) and `0.0507` for
`0.37864`). -/
noncomputable def bI1 (Y δ : ℝ) (q : ℕ) : ℝ :=
  Y / q * capM 0.798437 δ * ((q : ℝ) / Nat.totient q) *
      (7 / 4 * Real.log (OC.dz δ * q) + 6.11676) +
    Y ^ ((2 : ℝ) / 3) / Real.sqrt (OC.dz δ * q) * (0.67845 * Real.log Y - 1.20818) +
    0.37864 * Y ^ ((2 : ℝ) / 3)

/-- **The bound of Link A2 — `eq:cleson`** as CORRECTED in Helfgott's book
(`minarctotals.tex` 1542-1548: `c_1` replaced by `c_+ = 1 + 8 log 2/(x/UV)`, `ε = 0.07`,
`log δq³`, the `min` branch dropped; arXiv `minarcs.tex` 5092-5102). -/
noncomputable def bI2 (Y δ : ℝ) (q : ℕ) : ℝ :=
  2.49157 * Y / Real.sqrt (OC.dz δ * q) +
    capM (4 * 0.798437) δ * (Y / Nat.totient q) * (3 / 2 * Real.log q + 2.74107) +
    (3.59676 * Real.log (OC.dz δ) + 27.3032 * Real.log q + 91.515) * (Y / (q * OC.dz δ)) +
    (22.9812 * Real.log Y + 411.424) * Y ^ ((2 : ℝ) / 3)

/-- **The bound of Link A3 — `eq:senorburns`** (book `minarctotals.tex` 1710-1717, the union of
`eq:pell` and `eq:meli` 1632-1692 with `ε₁ ≤ 0.002`; arXiv `minarcs.tex` 5179-5256). -/
noncomputable def bII (Y δ : ℝ) (q : ℕ) : ℝ :=
  Y / Real.sqrt (OC.dz δ * Nat.totient q) *
      (Real.sqrt (cXT Y (OC.dz δ * q) * (Real.log (OC.dz δ * q) + 0.002) +
          Real.log (4 * (OC.dz δ * q)) / 2) *
        Real.sqrt (0.30214 * Real.log (OC.dz δ * q) + 0.67506)) +
    2.73908 * Y ^ ((5 : ℝ) / 6)

/-- **Link A1 [TypeI1] — `|S_{I,1}| ≤ eq:therwald`** at the first choice of parameters, under
the Main Theorem's first-case hypotheses. OPEN (`lem:bostb1` with `ρ₀ = 4`, `D = U`, `c₀ = 31.521`,
eq:grara/ronsard/meproz). -/
def TypeI1 : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ α δ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 →
    2 * α = a / q + δ / Y → (q : ℝ) ≤ 3 / 4 * Y ^ ((2 : ℝ) / 3) →
    |δ / Y| ≤ 1 / (q * (3 / 4 * Y ^ ((2 : ℝ) / 3))) → (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6 →
      ‖sI1 Y α (uA Y δ q)‖ ≤ bI1 Y δ q

/-- **Link A2 [TypeI2] — `|S_{I,2}| ≤ eq:cleson`** at the first choice. OPEN (`lem:bosta2` per
`v ≤ V` at scale `x/v`, eq:avamys, eq:rala/trado1/trado2/charol). -/
def TypeI2 : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ α δ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 →
    2 * α = a / q + δ / Y → (q : ℝ) ≤ 3 / 4 * Y ^ ((2 : ℝ) / 3) →
    |δ / Y| ≤ 1 / (q * (3 / 4 * Y ^ ((2 : ℝ) / 3))) → (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6 →
      ‖sI2 Y α (uA Y δ q) (vA Y)‖ ≤ bI2 Y δ q

/-- **Link A3 [TypeII] — `|S_{II}| ≤ eq:senorburns`** at the first choice. OPEN (`prop:kraken`,
eq:vinland1/eriksaga, lem:merkel, the large sieve). -/
def TypeII : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ α δ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 →
    2 * α = a / q + δ / Y → (q : ℝ) ≤ 3 / 4 * Y ^ ((2 : ℝ) / 3) →
    |δ / Y| ≤ 1 / (q * (3 / 4 * Y ^ ((2 : ℝ) / 3))) → (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6 →
      ‖sII Y α (uA Y δ q) (vA Y)‖ ≤ bII Y δ q

/-! ## (3) The target, with its two constants as parameters -/

/-- **`L_{δ,q}` with the constant `cL` a parameter**: `OL.lToscaL` is `lToscaAt 22.7538`. -/
noncomputable def lToscaAt (cL δ : ℝ) (q : ℕ) : ℝ :=
  (Real.log (δ ^ ((7 : ℝ) / 4) * (q : ℝ) ^ ((13 : ℝ) / 4)) + 80 / 9) /
      ((Nat.totient q : ℝ) / q) +
    Real.log ((q : ℝ) ^ (13.6516 : ℝ) * δ ^ (1.7984 : ℝ)) + cL

/-- **`eq:kraw` with its main-term constant `m` and `L`'s constant `cL` parameters**:
`OL.krawL` is `krawAt 0.5 22.7538` (`krawL_eq`). -/
noncomputable def krawAt (m cL x δ : ℝ) (q : ℕ) : ℝ :=
  (MinSp.rR x (OC.dz δ * q) * Real.log (OC.dz δ * q) + m) /
      Real.sqrt (OC.dz δ * Nat.totient q) * x +
    2.5 * x / Real.sqrt (OC.dz δ * q) + 2 * x / (OC.dz δ * q) * lToscaAt cL (OC.dz δ) q +
    3.2 * x ^ ((5 : ℝ) / 6)

/-- **`OL.krawL = krawAt 0.5 22.7538`**, by `rfl`. -/
theorem krawL_eq (x δ : ℝ) (q : ℕ) : OL.krawL x δ q = krawAt 0.5 22.7538 x δ q :=
  rfl

/-- **The first case of `OL.MinMainL` with `(m, cL)` parameters**. -/
def MinMain1At (m cL : ℝ) : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ α δ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 →
    2 * α = a / q + δ / Y → (q : ℝ) ≤ 3 / 4 * Y ^ ((2 : ℝ) / 3) →
    |δ / Y| ≤ 1 / (q * (3 / 4 * Y ^ ((2 : ℝ) / 3))) → (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6 →
      ‖Smooth.smSum HW.eta2 Y α‖ ≤ krawAt m cL Y δ q

/-- **The second case of `OL.MinMainL`** (`q > Y^{1/3}/6`, loosened `1.25h`), a separate Prop. -/
def MinMain2L : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ α δ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 →
    2 * α = a / q + δ / Y → (q : ℝ) ≤ 3 / 4 * Y ^ ((2 : ℝ) / 3) →
    |δ / Y| ≤ 1 / (q * (3 / 4 * Y ^ ((2 : ℝ) / 3))) → Y ^ ((1 : ℝ) / 3) / 6 < q →
      ‖Smooth.smSum HW.eta2 Y α‖ ≤
        0.3409 * Y ^ ((5 : ℝ) / 6) * Real.log Y ^ ((3 : ℝ) / 2) +
          1522.5 * Y ^ ((2 : ℝ) / 3) * Real.log Y

/-- **`OL.MinMainL` IS its first case at `(0.5, 22.7538)` and its second case.** -/
theorem minMainL_iff : OL.MinMainL ↔ MinMain1At 0.5 22.7538 ∧ MinMain2L := by
  constructor
  · intro h
    exact ⟨fun Y hY α δ a q hq hg h2 hQ hδ hy => (h Y hY α δ a q hq hg h2 hQ hδ).1 hy,
      fun Y hY α δ a q hq hg h2 hQ hδ hy => (h Y hY α δ a q hq hg h2 hQ hδ).2 hy⟩
  · rintro ⟨h1, h2⟩ Y hY α δ a q hq hg h2α hQ hδ
    exact ⟨h1 Y hY α δ a q hq hg h2α hQ hδ, h2 Y hY α δ a q hq hg h2α hQ hδ⟩

/-- **Links A5+A9+A10 — the arithmetic of the Totals, as ONE Prop**: at every admissible
`(Y, δ, q)` the piece bounds plus the `S_{0,2}` remainder sum to at most `krawAt m cL`. -/
def ArithAt (m cL : ℝ) : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ δ : ℝ, ∀ q : ℕ, 1 ≤ q → |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3) →
    (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6 →
      bI1 Y δ q + bI2 Y δ q + bII Y δ q + 3 * (Real.log Y + 1) ≤ krawAt m cL Y δ q

/-! ## (4) The arithmetic, PROVED at `(0.811, 45.7575)` -/

/-- `Y^{2/3} = u⁴`, `Y^{5/6} = u⁵`, `Y^{1/3} = u²`, `Y = u⁶`, `log Y = 6 log u`, `u = Y^{1/6}`. -/
theorem rpow_facts (Y : ℝ) (hY : 0 < Y) :
    Y ^ ((2 : ℝ) / 3) = (Y ^ ((1 : ℝ) / 6)) ^ 4 ∧ Y ^ ((5 : ℝ) / 6) = (Y ^ ((1 : ℝ) / 6)) ^ 5 ∧
      Y ^ ((1 : ℝ) / 3) = (Y ^ ((1 : ℝ) / 6)) ^ 2 ∧ Y = (Y ^ ((1 : ℝ) / 6)) ^ 6 ∧
      Real.log Y = 6 * Real.log (Y ^ ((1 : ℝ) / 6)) := by
  have h : ∀ n : ℕ, (Y ^ ((1 : ℝ) / 6)) ^ n = Y ^ ((1 : ℝ) / 6 * n) := fun n =>
    (Real.rpow_mul_natCast hY.le _ n).symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h]
    norm_num
  · rw [h]
    norm_num
  · rw [h]
    norm_num
  · rw [h]
    norm_num
  · rw [Real.log_rpow hY]
    ring

/-- `Y ≥ 3.4·10²³ ⇒ Y^{1/6} ≥ 8000` (`8000⁶ = 2.62·10²³`). -/
theorem u_ge (Y : ℝ) (hY : 3.4e23 ≤ Y) : 8000 ≤ Y ^ ((1 : ℝ) / 6) := by
  have h : (8000 : ℝ) = ((8000 : ℝ) ^ 6) ^ ((1 : ℝ) / 6) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [h]
  exact Real.rpow_le_rpow (by positivity) (by norm_num; linarith) (by norm_num)

/-- `δ₀ = max(2, |δ|/4) ≥ 2`. -/
theorem dz_ge (δ : ℝ) : 2 ≤ OC.dz δ :=
  le_max_left _ _

/-- **`δ₀q ≤ x^{1/3}/3 = 2y`** from `|δ|q ≤ (4/3)x^{1/3}` and `q ≤ x^{1/3}/6` (minarcs
4874-4875). -/
theorem dz_q_le (δ c : ℝ) (q : ℕ) (hdq : |δ| * q ≤ 4 / 3 * c)
    (hqc : (q : ℝ) ≤ c / 6) : OC.dz δ * q ≤ c / 3 := by
  unfold OC.dz
  rcases le_total 2 (|δ| / 4) with h | h
  · rw [max_eq_right h]
    linarith
  · rw [max_eq_left h]
    linarith

/-- **`|δ/Y| ≤ 1/(qQ)`, `Q = (3/4)Y^{2/3}`, gives `|δ|q ≤ (4/3)Y^{1/3}`.** -/
theorem adm_dq (Y δ : ℝ) (q : ℕ) (hY0 : 0 < Y) (hq : 1 ≤ q)
    (hδ : |δ / Y| ≤ 1 / (q * (3 / 4 * Y ^ ((2 : ℝ) / 3)))) :
    |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3) := by
  obtain ⟨e23, -, e13, eY, -⟩ := rpow_facts Y hY0
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hu0 : 0 < Y ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hY0 _
  rw [e23] at hδ
  rw [e13]
  rw [abs_div, abs_of_pos hY0,
    div_le_div_iff₀ hY0 (mul_pos (by linarith : (0 : ℝ) < q) (by positivity)), one_mul] at hδ
  have h2 : (|δ| * q) * (Y ^ ((1 : ℝ) / 6)) ^ 4 ≤
      (4 / 3 * (Y ^ ((1 : ℝ) / 6)) ^ 2) * (Y ^ ((1 : ℝ) / 6)) ^ 4 := by
    nlinarith [hδ, eY]
  exact le_of_mul_le_mul_right h2 (pow_pos hu0 4)

/-- **`V < x/4`** at `V = (9/2)x^{1/3}`, `x ≥ 3.4·10²³` (`eq:herring`), so `S_{0,∞} = 0`. -/
theorem vA_lt (Y : ℝ) (hY : 3.4e23 ≤ Y) : vA Y < Y / 4 := by
  have hY0 : 0 < Y := by linarith
  obtain ⟨-, -, e13, eY, -⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  unfold vA
  rw [e13]
  have h4 : (8000 : ℝ) ^ 4 ≤ (Y ^ ((1 : ℝ) / 6)) ^ 4 := pow_le_pow_left₀ (by norm_num) hu 4
  have h2 : (0 : ℝ) < (Y ^ ((1 : ℝ) / 6)) ^ 2 := pow_pos (by linarith) 2
  have h6 : 18 * (Y ^ ((1 : ℝ) / 6)) ^ 2 < (Y ^ ((1 : ℝ) / 6)) ^ 6 := by
    have h18 : (18 : ℝ) < (Y ^ ((1 : ℝ) / 6)) ^ 4 := by norm_num at h4; linarith
    nlinarith
  linarith [eY]

/-- **`min(1, c/δ²) ≤ 2/δ₀`** for `0 < c ≤ 64` (minarcs 5261-5262; book 1722-1726). -/
theorem capM_le (c δ : ℝ) (hc0 : 0 < c) (hc : c ≤ 64) : capM c δ ≤ 2 / OC.dz δ := by
  unfold capM OC.dz
  have hm : 0 < max c (δ ^ 2) := lt_of_lt_of_le hc0 (le_max_left _ _)
  rcases le_or_gt |δ| 8 with h | h
  · rw [max_eq_left (by linarith : |δ| / 4 ≤ 2), div_le_div_iff₀ hm (by norm_num)]
    nlinarith [le_max_left c (δ ^ 2)]
  · rw [max_eq_right (by linarith : (2 : ℝ) ≤ |δ| / 4), div_le_div_iff₀ hm (by positivity)]
    have hd2 : δ ^ 2 = |δ| ^ 2 := (sq_abs δ).symm
    nlinarith [le_max_right c (δ ^ 2), mul_nonneg (sub_nonneg.mpr h.le) (abs_nonneg δ),
      mul_nonneg (sub_nonneg.mpr hc) (abs_nonneg δ)]

theorem capM_nonneg (c δ : ℝ) (hc0 : 0 < c) : 0 ≤ capM c δ :=
  div_nonneg hc0.le (le_trans hc0.le (le_max_left _ _))

/-- `log 4 ≤ 1.3863`. -/
theorem log4_le : Real.log 4 ≤ 1.3863 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [h]
  linarith [Real.log_two_lt_d9]

/-- **`0 ≤ C_{x,t} ≤ 0.723 + 0.0625 log t`** for `2 ≤ t ≤ x^{1/3}/3` (there
`9x^{1/3}/(2.004t) ≥ 13.47 ≥ e²`). -/
theorem cXT_bounds (x t : ℝ) (hx : 0 < x) (ht : 2 ≤ t) (htx : t ≤ x ^ ((1 : ℝ) / 3) / 3) :
    0 ≤ cXT x t ∧ cXT x t ≤ 0.723 + 0.0625 * Real.log t := by
  have hc : 0 < x ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hx _
  have ht0 : 0 < t := by linarith
  unfold cXT
  have hr : 13.47 ≤ 9 * x ^ ((1 : ℝ) / 3) / (2.004 * t) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have he2 : Real.exp 2 ≤ 7.4 := by
    have h := Real.exp_one_lt_d9
    have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [e]
    nlinarith [Real.exp_pos 1]
  have hD : 2 ≤ Real.log (9 * x ^ ((1 : ℝ) / 3) / (2.004 * t)) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith
  have hl4 : Real.log (4 * t) = Real.log 4 + Real.log t := Real.log_mul (by norm_num) ht0.ne'
  have hlt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have h4 := log4_le
  have h40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hN : 0 ≤ Real.log (4 * t) := by rw [hl4]; linarith
  have hu0 : 0 ≤ Real.log (4 * t) / (2 * Real.log (9 * x ^ ((1 : ℝ) / 3) / (2.004 * t))) :=
    div_nonneg hN (by linarith)
  have hu1 : Real.log (4 * t) / (2 * Real.log (9 * x ^ ((1 : ℝ) / 3) / (2.004 * t))) ≤
      (Real.log 4 + Real.log t) / 4 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num), ← hl4]
    nlinarith [mul_le_mul_of_nonneg_left hD hN]
  constructor
  · exact Real.log_nonneg (by linarith)
  · have hv : 0 < 1 + Real.log (4 * t) /
        (2 * Real.log (9 * x ^ ((1 : ℝ) / 3) / (2.004 * t))) := by linarith
    have h1 := Real.log_le_sub_one_of_pos (show 0 < (1 + Real.log (4 * t) /
        (2 * Real.log (9 * x ^ ((1 : ℝ) / 3) / (2.004 * t)))) / 4 from div_pos hv (by norm_num))
    rw [Real.log_div hv.ne' (by norm_num)] at h1
    linarith

/-- **Link A10 CORRECTED — the AM-GM of `minarcs.tex` 5549-5566 (book 2257-2288)**, at
`√ρ = 1.8434`: `√(C(ℓ+0.002) + (log 4 + ℓ)/2)·√(0.30214ℓ + 0.67506) ≤ (0.27125C + 0.41415)ℓ
+ 0.811`. Helfgott's `0.49911` halves the `√ρ·0.67506/2` summand; the true constant is `0.81019`
(`not_arith_05` shows `0.5` is unreachable). -/
theorem amgm_main (C l L4 : ℝ) (hC0 : 0 ≤ C) (hl : 0 ≤ l) (hC : C ≤ 0.723 + 0.0625 * l)
    (hL0 : 0 ≤ L4) (hL : L4 ≤ 1.3863) :
    Real.sqrt (C * (l + 0.002) + (L4 + l) / 2) * Real.sqrt (0.30214 * l + 0.67506) ≤
      (0.27125 * C + 0.41415) * l + 0.811 := by
  have hA0 : 0 ≤ C * (l + 0.002) + (L4 + l) / 2 :=
    add_nonneg (mul_nonneg hC0 (by linarith)) (by linarith)
  have hB0 : (0 : ℝ) ≤ 0.30214 * l + 0.67506 := by linarith
  have hsA := Real.sq_sqrt hA0
  have hsB := Real.sq_sqrt hB0
  have hkey : 2 * 1.8434 * (Real.sqrt (C * (l + 0.002) + (L4 + l) / 2) *
        Real.sqrt (0.30214 * l + 0.67506)) ≤
      C * (l + 0.002) + (L4 + l) / 2 + 1.8434 ^ 2 * (0.30214 * l + 0.67506) := by
    nlinarith [sq_nonneg (Real.sqrt (C * (l + 0.002) + (L4 + l) / 2) -
      1.8434 * Real.sqrt (0.30214 * l + 0.67506))]
  have hCl : 0 ≤ C * l := mul_nonneg hC0 hl
  nlinarith [hkey, hCl]

/-- **The main term (Link A3's first line) under the corrected A10**: at most
`(R_{x,δ₀q} log δ₀q + 0.811)/√(δ₀φ(q)) · x`. -/
theorem main_le (Y δ : ℝ) (q : ℕ) (hY0 : 0 < Y) (hq : 1 ≤ q)
    (htx : OC.dz δ * q ≤ Y ^ ((1 : ℝ) / 3) / 3) :
    Y / Real.sqrt (OC.dz δ * Nat.totient q) *
        (Real.sqrt (cXT Y (OC.dz δ * q) * (Real.log (OC.dz δ * q) + 0.002) +
            Real.log (4 * (OC.dz δ * q)) / 2) *
          Real.sqrt (0.30214 * Real.log (OC.dz δ * q) + 0.67506)) ≤
      (MinSp.rR Y (OC.dz δ * q) * Real.log (OC.dz δ * q) + 0.811) /
        Real.sqrt (OC.dz δ * Nat.totient q) * Y := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd2 := dz_ge δ
  have ht2 : 2 ≤ OC.dz δ * q := by nlinarith
  have ht0 : 0 < OC.dz δ * q := by linarith
  obtain ⟨hC0, hC1⟩ := cXT_bounds Y (OC.dz δ * q) hY0 ht2 htx
  have hl : 0 ≤ Real.log (OC.dz δ * q) := Real.log_nonneg (by linarith)
  have hl4 : Real.log (4 * (OC.dz δ * q)) = Real.log 4 + Real.log (OC.dz δ * q) :=
    Real.log_mul (by norm_num) ht0.ne'
  have hR : MinSp.rR Y (OC.dz δ * q) = 0.27125 * cXT Y (OC.dz δ * q) + 0.41415 := rfl
  rw [hl4, hR]
  have key := amgm_main (cXT Y (OC.dz δ * q)) (Real.log (OC.dz δ * q)) (Real.log 4) hC0 hl hC1
    (Real.log_nonneg (by norm_num)) log4_le
  have hpos : 0 ≤ Y / Real.sqrt (OC.dz δ * Nat.totient q) :=
    div_nonneg hY0.le (Real.sqrt_nonneg _)
  calc _ ≤ Y / Real.sqrt (OC.dz δ * Nat.totient q) *
        ((0.27125 * cXT Y (OC.dz δ * q) + 0.41415) * Real.log (OC.dz δ * q) + 0.811) :=
        mul_le_mul_of_nonneg_left key hpos
    _ = _ := by ring

/-- **Link A9 — the terms in `1/φ(q)` and `1/q`**, from eq:therwald and eq:cleson (book
1728-1757): at most `(2x/δ₀q)·L` with `L = lToscaAt 45.7575`. The `q/φ(q)` part closes with
`6.11676 + 2.74107 = 8.85783 ≤ 80/9`; the `1/q` part is `(3.59676, 27.3032, 91.515)/2 =
(1.79838, 13.6516, 45.7575) ≤ (1.7984, 13.6516, 45.7575)`. -/
theorem lterms_le (Y δ : ℝ) (q : ℕ) (hY0 : 0 < Y) (hq : 1 ≤ q) :
    Y / q * capM 0.798437 δ * ((q : ℝ) / Nat.totient q) *
        (7 / 4 * Real.log (OC.dz δ * q) + 6.11676) +
      capM (4 * 0.798437) δ * (Y / Nat.totient q) * (3 / 2 * Real.log q + 2.74107) +
      (3.59676 * Real.log (OC.dz δ) + 27.3032 * Real.log q + 91.515) * (Y / (q * OC.dz δ)) ≤
    2 * Y / (OC.dz δ * q) * lToscaAt 45.7575 (OC.dz δ) q := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hφ1 : (1 : ℝ) ≤ Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hφ0 : (0 : ℝ) < Nat.totient q := by linarith
  have hd2 := dz_ge δ
  have hd0 : 0 < OC.dz δ := by linarith
  have hld : 0 ≤ Real.log (OC.dz δ) := Real.log_nonneg (by linarith)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hqR
  have hldq : Real.log (OC.dz δ * q) = Real.log (OC.dz δ) + Real.log q :=
    Real.log_mul hd0.ne' hq0.ne'
  have hlt1 : Real.log (OC.dz δ ^ ((7 : ℝ) / 4) * (q : ℝ) ^ ((13 : ℝ) / 4)) =
      7 / 4 * Real.log (OC.dz δ) + 13 / 4 * Real.log q := by
    rw [Real.log_mul (Real.rpow_pos_of_pos hd0 _).ne' (Real.rpow_pos_of_pos hq0 _).ne',
      Real.log_rpow hd0, Real.log_rpow hq0]
  have hlt2 : Real.log ((q : ℝ) ^ (13.6516 : ℝ) * OC.dz δ ^ (1.7984 : ℝ)) =
      13.6516 * Real.log q + 1.7984 * Real.log (OC.dz δ) := by
    rw [Real.log_mul (Real.rpow_pos_of_pos hq0 _).ne' (Real.rpow_pos_of_pos hd0 _).ne',
      Real.log_rpow hq0, Real.log_rpow hd0]
  have hc1 := capM_le 0.798437 δ (by norm_num) (by norm_num)
  have hc2 := capM_le (4 * 0.798437) δ (by norm_num) (by norm_num)
  have hYφ : 0 ≤ Y / Nat.totient q := div_nonneg hY0.le hφ0.le
  have e1 : Y / q * capM 0.798437 δ * ((q : ℝ) / Nat.totient q) *
      (7 / 4 * Real.log (OC.dz δ * q) + 6.11676) =
      capM 0.798437 δ * (Y / Nat.totient q) *
        (7 / 4 * Real.log (OC.dz δ) + 7 / 4 * Real.log q + 6.11676) := by
    rw [hldq]
    field_simp
  have h1 : Y / q * capM 0.798437 δ * ((q : ℝ) / Nat.totient q) *
      (7 / 4 * Real.log (OC.dz δ * q) + 6.11676) ≤
      2 / OC.dz δ * (Y / Nat.totient q) *
        (7 / 4 * Real.log (OC.dz δ) + 7 / 4 * Real.log q + 6.11676) := by
    rw [e1]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc1 hYφ) (by linarith)
  have h2 : capM (4 * 0.798437) δ * (Y / Nat.totient q) * (3 / 2 * Real.log q + 2.74107) ≤
      2 / OC.dz δ * (Y / Nat.totient q) * (3 / 2 * Real.log q + 2.74107) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc2 hYφ) (by linarith)
  have eR : 2 * Y / (OC.dz δ * q) * lToscaAt 45.7575 (OC.dz δ) q =
      2 / OC.dz δ * (Y / Nat.totient q) *
          (7 / 4 * Real.log (OC.dz δ) + 13 / 4 * Real.log q + 80 / 9) +
        2 * (Y / (q * OC.dz δ)) *
          (13.6516 * Real.log q + 1.7984 * Real.log (OC.dz δ) + 45.7575) := by
    unfold lToscaAt
    rw [hlt1, hlt2]
    field_simp
    ring
  have hP : 0 ≤ 2 / OC.dz δ * (Y / Nat.totient q) :=
    mul_nonneg (div_nonneg (by norm_num) hd0.le) hYφ
  have hQ : 0 ≤ Y / (q * OC.dz δ) := div_nonneg hY0.le (mul_nonneg hq0.le hd0.le)
  rw [eR]
  nlinarith [mul_nonneg hQ hld, hP, h1, h2]

/-- **Links A5+A9 — every `x^{2/3}` term, `S_{II}`'s `2.73908x^{5/6}` and `S_{0,2}`'s
`3(log x + 1)` fit in `3.2x^{5/6}`** for `x ≥ 3.4·10²³` (`u = x^{1/6} ≥ 8000`, `log u ≤ 7 +
u/2978`); at `x = 3.4·10²³` the left side is `2.941x^{5/6}`, so the margin is `0.259x^{5/6}`. -/
theorem low_le (Y s : ℝ) (hY : 3.4e23 ≤ Y) (hs : 1 ≤ s) :
    Y ^ ((2 : ℝ) / 3) / s * (0.67845 * Real.log Y - 1.20818) + 0.37864 * Y ^ ((2 : ℝ) / 3) +
        (22.9812 * Real.log Y + 411.424) * Y ^ ((2 : ℝ) / 3) + 2.73908 * Y ^ ((5 : ℝ) / 6) +
        3 * (Real.log Y + 1) ≤
      3.2 * Y ^ ((5 : ℝ) / 6) := by
  have hY0 : 0 < Y := by linarith
  obtain ⟨e23, e56, -, -, elog⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  rw [e23, e56, elog]
  have hu0 : 0 < Y ^ ((1 : ℝ) / 6) := by linarith
  have he1 : Real.exp 1 ≤ Y ^ ((1 : ℝ) / 6) := by linarith [Real.exp_one_lt_d9]
  have hlu1 : 1 ≤ Real.log (Y ^ ((1 : ℝ) / 6)) := by
    rw [Real.le_log_iff_exp_le hu0]
    exact he1
  have he8 : 2978 ≤ Real.exp 8 := by
    have h := Real.exp_one_gt_d9
    have e : Real.exp 8 = Real.exp 1 ^ 8 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have hp := pow_le_pow_left₀ (by norm_num) h.le 8
    rw [e]
    have hn : (2978 : ℝ) ≤ 2.7182818283 ^ 8 := by norm_num
    linarith
  have hlu2 : Real.log (Y ^ ((1 : ℝ) / 6)) ≤ 7 + Y ^ ((1 : ℝ) / 6) / 2978 := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hu0 (Real.exp_pos 8))
    rw [Real.log_div hu0.ne' (Real.exp_pos 8).ne', Real.log_exp] at h1
    have h2 : Y ^ ((1 : ℝ) / 6) / Real.exp 8 ≤ Y ^ ((1 : ℝ) / 6) / 2978 :=
      div_le_div_of_nonneg_left hu0.le (by norm_num) he8
    linarith
  have hX : 0 ≤ 0.67845 * (6 * Real.log (Y ^ ((1 : ℝ) / 6))) - 1.20818 := by linarith
  have hu4 : 0 ≤ (Y ^ ((1 : ℝ) / 6)) ^ 4 := by positivity
  have ht1 : (Y ^ ((1 : ℝ) / 6)) ^ 4 / s *
        (0.67845 * (6 * Real.log (Y ^ ((1 : ℝ) / 6))) - 1.20818) ≤
      (Y ^ ((1 : ℝ) / 6)) ^ 4 *
        (0.67845 * (6 * Real.log (Y ^ ((1 : ℝ) / 6))) - 1.20818) :=
    mul_le_mul_of_nonneg_right (div_le_self hu4 hs) hX
  have hA := mul_le_mul_of_nonneg_left hlu2 hu4
  have hB := mul_le_mul_of_nonneg_right hu hu4
  have hC : (8000 : ℝ) ^ 4 ≤ (Y ^ ((1 : ℝ) / 6)) ^ 4 := pow_le_pow_left₀ (by norm_num) hu 4
  have hD := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ Y ^ ((1 : ℝ) / 6)) (by norm_num : 1 ≤ 4)
  nlinarith [ht1, hA, hB, hC, hD, hlu2, hu]

/-- **THE ARITHMETIC, PROVED at `(m, cL) = (0.811, 45.7575)`**: the book-corrected piece bounds
plus `3(log x + 1)` are at most `krawAt 0.811 45.7575` on every admissible `(Y, δ, q)`. -/
theorem arith_811 : ArithAt 0.811 45.7575 := by
  intro Y hY δ q hq hdq hqy
  have hY0 : (0 : ℝ) < Y := by linarith
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have htx : OC.dz δ * q ≤ Y ^ ((1 : ℝ) / 3) / 3 := dz_q_le δ _ q hdq hqy
  have hdq1 : (1 : ℝ) ≤ OC.dz δ * q := by nlinarith [dz_ge δ]
  have hs : 1 ≤ Real.sqrt (OC.dz δ * q) := Real.one_le_sqrt.mpr hdq1
  have hM := main_le Y δ q hY0 hq htx
  have hN : 2.49157 * Y / Real.sqrt (OC.dz δ * q) ≤ 2.5 * Y / Real.sqrt (OC.dz δ * q) :=
    div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  have hL := lterms_le Y δ q hY0 hq
  have hE := low_le Y (Real.sqrt (OC.dz δ * q)) hY hs
  unfold bI1 bI2 bII krawAt
  linarith

/-! ## (5) THE COMPOSITION -/

/-- **The Totals spine, generic in `(m, cL)`**: `ArithAt m cL` and the three named piece bounds
give the first case of the Main Theorem with `krawAt m cL`. A0 (`vaughan_split`), `S_{0,∞} = 0`
(`s0i_eq_zero`, `vA_lt`), `|S_{0,2}| ≤ 3(log x+1)` (`s02_norm_le`) and the admissibility
arithmetic (`adm_dq`) are PROVED; the triangle inequality does the rest. -/
theorem minMain1_of_arith (m cL : ℝ) (hA : ArithAt m cL) (h1 : TypeI1) (h2 : TypeI2)
    (h3 : TypeII) : MinMain1At m cL := by
  intro Y hY α δ a q hq hg h2α hqQ hδ hqy
  have hY0 : (0 : ℝ) < Y := by linarith
  have hdq := adm_dq Y δ q hY0 hq hδ
  have hsplit := vaughan_split Y α (uA Y δ q) (vA Y) hY0
  rw [s0i_eq_zero Y α (vA Y) hY0 (vA_lt Y hY), add_zero] at hsplit
  have e1 := h1 Y hY α δ a q hq hg h2α hqQ hδ hqy
  have e2 := h2 Y hY α δ a q hq hg h2α hqQ hδ hqy
  have e3 := h3 Y hY α δ a q hq hg h2α hqQ hδ hqy
  have e4 := s02_norm_le Y α (by linarith)
  have hk := hA Y hY δ q hq hdq hqy
  rw [hsplit]
  have n1 := norm_add_le (sI1 Y α (uA Y δ q) - sI2 Y α (uA Y δ q) (vA Y) +
    sII Y α (uA Y δ q) (vA Y)) (s02 Y α)
  have n2 := norm_add_le (sI1 Y α (uA Y δ q) - sI2 Y α (uA Y δ q) (vA Y))
    (sII Y α (uA Y δ q) (vA Y))
  have n3 := norm_sub_le (sI1 Y α (uA Y δ q)) (sI2 Y α (uA Y δ q) (vA Y))
  linarith

/-- **THE HEADLINE — the first case of the Main Theorem from the three NAMED piece bounds, with
the two constants the pieces actually support**: `main 0.811` (not `0.5`) and `L`'s constant
`45.7575` (not `22.7538`). Application only. -/
theorem minMainL1c_of_pieces (h1 : TypeI1) (h2 : TypeI2) (h3 : TypeII) :
    MinMain1At 0.811 45.7575 :=
  minMain1_of_arith 0.811 45.7575 arith_811 h1 h2 h3

/-! ## (6) Monotonicity, and the FENCE: the typed `0.5` is unreachable from the pieces -/

theorem lToscaAt_mono (cL cL' δ : ℝ) (q : ℕ) (hc : cL ≤ cL') :
    lToscaAt cL δ q ≤ lToscaAt cL' δ q := by
  unfold lToscaAt
  linarith

/-- `krawAt` grows with both constants (for `x ≥ 0`). -/
theorem krawAt_mono (m m' cL cL' x δ : ℝ) (q : ℕ) (hx : 0 ≤ x) (hm : m ≤ m')
    (hc : cL ≤ cL') : krawAt m cL x δ q ≤ krawAt m' cL' x δ q := by
  have hd0 : 0 < OC.dz δ := lt_of_lt_of_le two_pos (dz_ge δ)
  unfold krawAt
  have h1 : (MinSp.rR x (OC.dz δ * q) * Real.log (OC.dz δ * q) + m) /
        Real.sqrt (OC.dz δ * Nat.totient q) * x ≤
      (MinSp.rR x (OC.dz δ * q) * Real.log (OC.dz δ * q) + m') /
        Real.sqrt (OC.dz δ * Nat.totient q) * x :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)) hx
  have h2 : 2 * x / (OC.dz δ * q) * lToscaAt cL (OC.dz δ) q ≤
      2 * x / (OC.dz δ * q) * lToscaAt cL' (OC.dz δ) q :=
    mul_le_mul_of_nonneg_left (lToscaAt_mono cL cL' _ q hc)
      (div_nonneg (by linarith) (mul_nonneg hd0.le (Nat.cast_nonneg _)))
  linarith

/-- `ArithAt` weakens as the constants grow. -/
theorem arithAt_mono (m m' cL cL' : ℝ) (hm : m ≤ m') (hc : cL ≤ cL') (h : ArithAt m cL) :
    ArithAt m' cL' := fun Y hY δ q hq hdq hqy =>
  (h Y hY δ q hq hdq hqy).trans (krawAt_mono m m' cL cL' Y δ q (by linarith) hm hc)

/-- `MinMain1At` weakens as the constants grow. -/
theorem minMain1At_mono (m m' cL cL' : ℝ) (hm : m ≤ m') (hc : cL ≤ cL') (h : MinMain1At m cL) :
    MinMain1At m' cL' := fun Y hY α δ a q hq hg h2 hQ hδ hy =>
  (h Y hY α δ a q hq hg h2 hQ hδ hy).trans (krawAt_mono m m' cL cL' Y δ q (by linarith) hm hc)

/-- `log x ≥ 2` for `x ≥ 3.4·10²³`. -/
theorem log_ge_two (Y : ℝ) (hY : 3.4e23 ≤ Y) : 2 ≤ Real.log Y := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h := Real.exp_one_lt_d9
  have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [e]
  nlinarith [Real.exp_pos 1]

/-- The bound of A1 is nonnegative (every summand is). -/
theorem bI1_nonneg (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q) : 0 ≤ bI1 Y δ q := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd2 := dz_ge δ
  have hl : 0 ≤ Real.log (OC.dz δ * q) := Real.log_nonneg (by nlinarith)
  have hlY := log_ge_two Y hY
  unfold bI1
  have t1 : 0 ≤ Y / q * capM 0.798437 δ * ((q : ℝ) / Nat.totient q) *
      (7 / 4 * Real.log (OC.dz δ * q) + 6.11676) :=
    mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg hY0.le (by linarith))
      (capM_nonneg _ _ (by norm_num))) (div_nonneg (by linarith) (Nat.cast_nonneg _)))
      (by linarith)
  have t2 : 0 ≤ Y ^ ((2 : ℝ) / 3) / Real.sqrt (OC.dz δ * q) * (0.67845 * Real.log Y - 1.20818) :=
    mul_nonneg (div_nonneg (Real.rpow_nonneg hY0.le _) (Real.sqrt_nonneg _)) (by linarith)
  have t3 : 0 ≤ 0.37864 * Y ^ ((2 : ℝ) / 3) := mul_nonneg (by norm_num) (Real.rpow_nonneg hY0.le _)
  linarith

/-- The bound of A2 is at least its first summand `2.49157x/√(δ₀q)`. -/
theorem bI2_ge (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q) :
    2.49157 * Y / Real.sqrt (OC.dz δ * q) ≤ bI2 Y δ q := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd2 := dz_ge δ
  have hld : 0 ≤ Real.log (OC.dz δ) := Real.log_nonneg (by linarith)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hqR
  have hlY := log_ge_two Y hY
  unfold bI2
  have t1 : 0 ≤ capM (4 * 0.798437) δ * (Y / Nat.totient q) * (3 / 2 * Real.log q + 2.74107) :=
    mul_nonneg (mul_nonneg (capM_nonneg _ _ (by norm_num))
      (div_nonneg hY0.le (Nat.cast_nonneg _))) (by linarith)
  have t2 : 0 ≤ (3.59676 * Real.log (OC.dz δ) + 27.3032 * Real.log q + 91.515) *
      (Y / (q * OC.dz δ)) :=
    mul_nonneg (by linarith) (div_nonneg hY0.le (mul_nonneg (by linarith) (by linarith)))
  have t3 : 0 ≤ (22.9812 * Real.log Y + 411.424) * Y ^ ((2 : ℝ) / 3) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hY0.le _)
  linarith

/-- The bound of A3 is at least its main term. -/
theorem bII_ge (Y δ : ℝ) (q : ℕ) (hY0 : 0 < Y) :
    Y / Real.sqrt (OC.dz δ * Nat.totient q) *
        (Real.sqrt (cXT Y (OC.dz δ * q) * (Real.log (OC.dz δ * q) + 0.002) +
            Real.log (4 * (OC.dz δ * q)) / 2) *
          Real.sqrt (0.30214 * Real.log (OC.dz δ * q) + 0.67506)) ≤ bII Y δ q := by
  unfold bII
  have h : 0 ≤ 2.73908 * Y ^ ((5 : ℝ) / 6) := mul_nonneg (by norm_num) (Real.rpow_nonneg hY0.le _)
  linarith

/-- The fence's `√(AB) ≥ 12.48` at `C = log 2`, `ℓ = 28 log 2` (true value `12.48856`). -/
theorem fence_ab : 12.48 ≤
    Real.sqrt (Real.log 2 * (28 * Real.log 2 + 0.002) + 30 * Real.log 2 / 2) *
      Real.sqrt (0.30214 * (28 * Real.log 2) + 0.67506) := by
  have hL := Real.log_two_gt_d9
  have hA0 : 0 ≤ Real.log 2 * (28 * Real.log 2 + 0.002) + 30 * Real.log 2 / 2 := by nlinarith
  have hL2 := pow_le_pow_left₀ (by norm_num) hL.le 2
  have hL3 := pow_le_pow_left₀ (by norm_num) hL.le 3
  rw [← Real.sqrt_mul hA0, Real.le_sqrt' (by norm_num)]
  nlinarith [hL2, hL3]

/-- The fence's `R·ℓ ≤ 11.688` at `C = log 2`, `ℓ = 28 log 2` (true value `11.68698`). -/
theorem fence_R : (0.27125 * Real.log 2 + 0.41415) * (28 * Real.log 2) ≤ 11.688 := by
  have hL := Real.log_two_gt_d9
  have hL' := Real.log_two_lt_d9
  nlinarith

/-- The fence's `L ≤ 123.52` at `δ₀ = 2²⁸`, `q = 1` (true value `123.514`). -/
theorem fence_lT :
    7 / 4 * (28 * Real.log 2) + 80 / 9 + 1.7984 * (28 * Real.log 2) + 45.7575 ≤ 123.52 := by
  have hL' := Real.log_two_lt_d9
  linarith

/-- **THE FENCE — the typed main-term constant `0.5` is UNREACHABLE from the pieces**, even with
`L`'s constant raised to `45.7575`: at `q = 1`, `δ = 2³⁰` (so `δ₀q = t = 2²⁸`) and
`x^{1/3} = (4.008/9)t^{3/2}` (so `C_{x,t} = log 2` exactly), the piece bounds alone exceed
`krawAt 0.5 45.7575` by `0.2407·x/√t` (`scratchpad/mintot/fence.py`). -/
theorem not_arith_05 : ¬ ArithAt 0.5 45.7575 := by
  intro h
  have hL := Real.log_two_gt_d9
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 4.008 / 9 * 4398046511104 := ⟨_, rfl⟩
  have hc0 : 0 < c := by
    rw [hc]
    norm_num
  have hY : (3.4e23 : ℝ) ≤ c ^ 3 := by
    rw [hc]
    norm_num
  have hY0 : 0 < c ^ 3 := by positivity
  have hc13 : (c ^ 3) ^ ((1 : ℝ) / 3) = c := by
    rw [show ((1 : ℝ) / 3) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast hc0.le (by norm_num)
  have hdq : |(1073741824 : ℝ)| * ((1 : ℕ) : ℝ) ≤ 4 / 3 * (c ^ 3) ^ ((1 : ℝ) / 3) := by
    rw [hc13, hc]
    norm_num
  have hqy : ((1 : ℕ) : ℝ) ≤ (c ^ 3) ^ ((1 : ℝ) / 3) / 6 := by
    rw [hc13, hc]
    norm_num
  have H := h (c ^ 3) hY 1073741824 1 le_rfl hdq hqy
  have L1 := bI1_nonneg (c ^ 3) 1073741824 1 hY le_rfl
  have L2 := bI2_ge (c ^ 3) 1073741824 1 hY le_rfl
  have L3 := bII_ge (c ^ 3) 1073741824 1 hY0
  have L4 : 0 ≤ 3 * (Real.log (c ^ 3) + 1) := by linarith [log_ge_two (c ^ 3) hY]
  have hdz : OC.dz 1073741824 = 268435456 := by
    unfold OC.dz
    rw [abs_of_pos (by norm_num), max_eq_right (by norm_num)]
    norm_num
  unfold krawAt at H
  simp only [hdz, Nat.totient_one, Nat.cast_one, mul_one] at H L2 L3
  have hs : Real.sqrt 268435456 = 16384 := by
    rw [show (268435456 : ℝ) = 16384 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hl28 : Real.log 268435456 = 28 * Real.log 2 := by
    rw [show (268435456 : ℝ) = 2 ^ 28 by norm_num, Real.log_pow]
    norm_num
  have hl30 : Real.log (4 * 268435456) = 30 * Real.log 2 := by
    rw [show (4 * 268435456 : ℝ) = 2 ^ 30 by norm_num, Real.log_pow]
    norm_num
  have hcx : cXT (c ^ 3) 268435456 = Real.log 2 := by
    unfold cXT
    have h15 : 9 * c / (2.004 * 268435456) = (2 : ℝ) ^ 15 := by
      rw [hc]
      norm_num
    have hr : 30 * Real.log 2 / (2 * (15 * Real.log 2)) = 1 := by
      rw [div_eq_one_iff_eq (ne_of_gt (by linarith))]
      ring
    rw [hc13, hl30, h15, Real.log_pow, show ((15 : ℕ) : ℝ) = 15 by norm_num, hr]
    norm_num
  have hrR : MinSp.rR (c ^ 3) 268435456 = 0.27125 * Real.log 2 + 0.41415 := by
    rw [show MinSp.rR (c ^ 3) 268435456 = 0.27125 * cXT (c ^ 3) 268435456 + 0.41415 from rfl, hcx]
  have hlT : lToscaAt 45.7575 268435456 1 =
      7 / 4 * (28 * Real.log 2) + 80 / 9 + 1.7984 * (28 * Real.log 2) + 45.7575 := by
    unfold lToscaAt
    simp only [Nat.totient_one, Nat.cast_one, Real.one_rpow, mul_one, one_mul, div_one]
    rw [Real.log_rpow (by norm_num), Real.log_rpow (by norm_num), hl28]
  rw [hs, hrR, hl28, hlT] at H
  rw [hs] at L2
  rw [hs, hcx, hl28, hl30] at L3
  obtain ⟨-, e56, e13, eY, -⟩ := rpow_facts (c ^ 3) hY0
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (c ^ 3) ^ ((1 : ℝ) / 6) := ⟨_, rfl⟩
  rw [← hu] at e56 e13 eY
  have hu0 : 0 < u := by
    rw [hu]
    exact Real.rpow_pos_of_pos hY0 _
  have huc : u ^ 2 = c := by rw [← e13, hc13]
  have hu_ge : 1398800 ≤ u := by
    by_contra hlt
    have hlt' := pow_lt_pow_left₀ (not_le.mp hlt) hu0.le (by norm_num : (2 : ℕ) ≠ 0)
    rw [huc, hc] at hlt'
    norm_num at hlt'
  have h56 : 3.2 * (c ^ 3) ^ ((5 : ℝ) / 6) ≤ 0.038 * (c ^ 3 / 16384) := by
    rw [e56]
    nlinarith [eY, mul_le_mul_of_nonneg_right hu_ge (pow_nonneg hu0.le 5), pow_nonneg hu0.le 5]
  have hK : 0 ≤ c ^ 3 / 16384 := div_nonneg hY0.le (by norm_num)
  linarith only [H, L1, L2, L3, L4, h56, hY0, mul_le_mul_of_nonneg_left fence_ab hK,
    mul_le_mul_of_nonneg_right fence_R hY0.le, mul_le_mul_of_nonneg_right fence_lT hY0.le]

/-- The bound of A1 is at least its `q/φ(q)` summand. -/
theorem bI1_ge_main (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) :
    Y / q * capM 0.798437 δ * ((q : ℝ) / Nat.totient q) *
        (7 / 4 * Real.log (OC.dz δ * q) + 6.11676) ≤ bI1 Y δ q := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlY := log_ge_two Y hY
  unfold bI1
  have t2 : 0 ≤ Y ^ ((2 : ℝ) / 3) / Real.sqrt (OC.dz δ * q) * (0.67845 * Real.log Y - 1.20818) :=
    mul_nonneg (div_nonneg (Real.rpow_nonneg hY0.le _) (Real.sqrt_nonneg _)) (by linarith)
  have t3 : 0 ≤ 0.37864 * Y ^ ((2 : ℝ) / 3) := mul_nonneg (by norm_num) (Real.rpow_nonneg hY0.le _)
  linarith

/-- The bound of A2 is at least its first three summands. -/
theorem bI2_ge_main (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) :
    2.49157 * Y / Real.sqrt (OC.dz δ * q) +
        capM (4 * 0.798437) δ * (Y / Nat.totient q) * (3 / 2 * Real.log q + 2.74107) +
        (3.59676 * Real.log (OC.dz δ) + 27.3032 * Real.log q + 91.515) * (Y / (q * OC.dz δ)) ≤
      bI2 Y δ q := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlY := log_ge_two Y hY
  unfold bI2
  have t3 : 0 ≤ (22.9812 * Real.log Y + 411.424) * Y ^ ((2 : ℝ) / 3) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hY0.le _)
  linarith

/-- Fence-2 numerics: `√(AB) ≥ 3.25` at `ℓ = 8 log 2`, `C ≥ 5/26` (true value `3.2702`). -/
theorem fence2_ab (C : ℝ) (hC : 5 / 26 ≤ C) : 3.25 ≤
    Real.sqrt (C * (8 * Real.log 2 + 0.002) + 10 * Real.log 2 / 2) *
      Real.sqrt (0.30214 * (8 * Real.log 2) + 0.67506) := by
  have hL := Real.log_two_gt_d9
  have hm := mul_le_mul_of_nonneg_right hC (by linarith : (0 : ℝ) ≤ 8 * Real.log 2 + 0.002)
  have hA : (4.53 : ℝ) ≤ C * (8 * Real.log 2 + 0.002) + 10 * Real.log 2 / 2 := by linarith
  have hB : (2.35 : ℝ) ≤ 0.30214 * (8 * Real.log 2) + 0.67506 := by linarith
  rw [← Real.sqrt_mul (by linarith), Real.le_sqrt' (by norm_num)]
  nlinarith [mul_le_mul hA hB (by norm_num) (by linarith)]

/-- Fence-2 numerics: `R·ℓ + 1.5 ≤ 4.156` at `ℓ = 8 log 2`, `C ≤ 5/21` (true value `4.1547`). -/
theorem fence2_R (C : ℝ) (hC : C ≤ 5 / 21) :
    (0.27125 * C + 0.41415) * (8 * Real.log 2) + 1.5 ≤ 4.156 := by
  have hL := Real.log_two_gt_d9
  have hL' := Real.log_two_lt_d9
  nlinarith [mul_le_mul_of_nonneg_right hC (by linarith : (0 : ℝ) ≤ 8 * Real.log 2)]

/-- **THE SECOND FENCE — `L`'s typed constant `22.7538` is UNREACHABLE from the pieces**, even
with the main-term constant raised to `1.5`: at `q = 2⁷`, `δ = 0` (`δ₀ = 2`, `t = 2⁸`,
`capM = 1`) and `9x^{1/3}/(2.004t) = 2²¹` (so `C_{x,t} = log(26/21)`), the `1/q` terms of
eq:cleson (`91.515`, book 1547) exceed what `2x/(δ₀q)·L` allows by `0.098x`
(`scratchpad/mintot/fence2.py`: `2.69x/√t` with the exact `C`). -/
theorem not_arith_typedL : ¬ ArithAt 1.5 22.7538 := by
  intro h
  have hL := Real.log_two_gt_d9
  have hL' := Real.log_two_lt_d9
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2.004 * 256 * 2097152 / 9 := ⟨_, rfl⟩
  have hc0 : 0 < c := by
    rw [hc]
    norm_num
  have hY : (3.4e23 : ℝ) ≤ c ^ 3 := by
    rw [hc]
    norm_num
  have hY0 : 0 < c ^ 3 := by positivity
  have hc13 : (c ^ 3) ^ ((1 : ℝ) / 3) = c := by
    rw [show ((1 : ℝ) / 3) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast hc0.le (by norm_num)
  have hdq : |(0 : ℝ)| * ((128 : ℕ) : ℝ) ≤ 4 / 3 * (c ^ 3) ^ ((1 : ℝ) / 3) := by
    rw [hc13, hc]
    norm_num
  have hqy : ((128 : ℕ) : ℝ) ≤ (c ^ 3) ^ ((1 : ℝ) / 3) / 6 := by
    rw [hc13, hc]
    norm_num
  have H := h (c ^ 3) hY 0 128 (by norm_num) hdq hqy
  have L1 := bI1_ge_main (c ^ 3) 0 128 hY
  have L2 := bI2_ge_main (c ^ 3) 0 128 hY
  have L3 := bII_ge (c ^ 3) 0 128 hY0
  have L4 : 0 ≤ 3 * (Real.log (c ^ 3) + 1) := by linarith [log_ge_two (c ^ 3) hY]
  have hdz : OC.dz 0 = 2 := by
    unfold OC.dz
    rw [abs_zero, zero_div, max_eq_left (by norm_num)]
  have hφ : Nat.totient 128 = 64 := by
    have h7 := Nat.totient_prime_pow Nat.prime_two (by norm_num : 0 < 7)
    simpa using h7
  have hcap : ∀ a : ℝ, 0 < a → capM a 0 = 1 := fun a ha => by
    unfold capM
    rw [show (0 : ℝ) ^ 2 = 0 by norm_num, max_eq_left ha.le, div_self ha.ne']
  have e1 : (2 : ℝ) * 128 = 256 := by norm_num
  have e2 : (2 : ℝ) * 64 = 128 := by norm_num
  have e3 : (128 : ℝ) * 2 = 256 := by norm_num
  have e4 : (4 : ℝ) * 256 = 1024 := by norm_num
  unfold krawAt at H
  simp only [hdz, hφ, Nat.cast_ofNat, hcap 0.798437 (by norm_num),
    hcap (4 * 0.798437) (by norm_num), e1, e2, e3, e4, mul_one, one_mul] at H L1 L2 L3
  have hs : Real.sqrt 256 = 16 := by
    rw [show (256 : ℝ) = 16 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hl256 : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    norm_num
  have hl1024 : Real.log 1024 = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
    norm_num
  have hl128 : Real.log 128 = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
    norm_num
  have hcx : cXT (c ^ 3) 256 = Real.log (26 / 21) := by
    unfold cXT
    have h21 : 9 * c / (2.004 * 256) = (2 : ℝ) ^ 21 := by
      rw [hc]
      norm_num
    have hr : 10 * Real.log 2 / (2 * (21 * Real.log 2)) = 5 / 21 := by
      rw [div_eq_iff (ne_of_gt (by linarith))]
      ring
    rw [hc13, h21, e4, hl1024, Real.log_pow, show ((21 : ℕ) : ℝ) = 21 by norm_num, hr]
    norm_num
  have hC1 : Real.log (26 / 21) ≤ 5 / 21 := by
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 26 / 21 by norm_num)
    linarith
  have hC0 : 5 / 26 ≤ Real.log (26 / 21) := by
    have h1 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 26 / 21 by norm_num)
    have h2 : (1 : ℝ) - (26 / 21)⁻¹ = 5 / 26 := by norm_num
    linarith
  have hrR : MinSp.rR (c ^ 3) 256 = 0.27125 * Real.log (26 / 21) + 0.41415 := by
    rw [show MinSp.rR (c ^ 3) 256 = 0.27125 * cXT (c ^ 3) 256 + 0.41415 from rfl, hcx]
  have hlT : lToscaAt 22.7538 2 128 ≤ 141.99 := by
    unfold lToscaAt
    simp only [hφ, Nat.cast_ofNat]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num),
      Real.log_rpow (by norm_num), Real.log_mul (by positivity) (by positivity),
      Real.log_rpow (by norm_num), Real.log_rpow (by norm_num), hl128]
    linarith
  rw [hs, hl256, hrR] at H
  rw [hl256] at L1
  rw [hs, hl128] at L2
  rw [hcx, hl256, hl1024] at L3
  obtain ⟨-, e56, -, eY, -⟩ := rpow_facts (c ^ 3) hY0
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (c ^ 3) ^ ((1 : ℝ) / 6) := ⟨_, rfl⟩
  rw [← hu] at e56 eY
  have hu0 : 0 < u := by
    rw [hu]
    exact Real.rpow_pos_of_pos hY0 _
  have hu_ge : 10000 ≤ u := by
    by_contra hlt
    have hlt' := pow_lt_pow_left₀ (not_le.mp hlt) hu0.le (by norm_num : (6 : ℕ) ≠ 0)
    rw [← eY, hc] at hlt'
    norm_num at hlt'
  have h56 : 3.2 * (c ^ 3) ^ ((5 : ℝ) / 6) ≤ 0.00032 * c ^ 3 := by
    rw [e56]
    nlinarith [eY, mul_le_mul_of_nonneg_right hu_ge (pow_nonneg hu0.le 5), pow_nonneg hu0.le 5]
  have hs128 : 11.3 ≤ Real.sqrt 128 := by
    rw [Real.le_sqrt' (by norm_num)]
    norm_num
  have hK : 0 ≤ c ^ 3 / Real.sqrt 128 := div_nonneg hY0.le (Real.sqrt_nonneg _)
  have hK1 : c ^ 3 / Real.sqrt 128 ≤ 0.0886 * c ^ 3 := by
    rw [div_le_iff₀ (Real.sqrt_pos.2 (by norm_num))]
    nlinarith [mul_le_mul_of_nonneg_left hs128 hY0.le]
  have hab := fence2_ab (Real.log (26 / 21)) hC0
  have hRb := fence2_R (Real.log (26 / 21)) hC1
  have hT : 0 ≤ 2 * c ^ 3 / 256 := by positivity
  have eq12 : c ^ 3 / 128 * (128 / 64) * (7 / 4 * (8 * Real.log 2) + 6.11676) +
      (2.49157 * c ^ 3 / 16 + c ^ 3 / 64 * (3 / 2 * (7 * Real.log 2) + 2.74107) +
        (3.59676 * Real.log 2 + 27.3032 * (7 * Real.log 2) + 91.515) * (c ^ 3 / 256)) =
      c ^ 3 * (292.71916 * Real.log 2 + 166.81144) / 256 := by ring
  have hlow : c ^ 3 * (292.71916 * 0.6931471803 + 166.81144) / 256 ≤
      c ^ 3 * (292.71916 * Real.log 2 + 166.81144) / 256 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hY0.le) (by norm_num)
  have hnum : 1.44 * c ^ 3 ≤ c ^ 3 * (292.71916 * 0.6931471803 + 166.81144) / 256 := by
    rw [le_div_iff₀ (by norm_num)]
    linarith only [hY0]
  have S1a : 1.44 * c ^ 3 ≤ bI1 (c ^ 3) 0 128 + bI2 (c ^ 3) 0 128 :=
    calc 1.44 * c ^ 3 ≤ c ^ 3 * (292.71916 * Real.log 2 + 166.81144) / 256 := hnum.trans hlow
      _ = c ^ 3 / 128 * (128 / 64) * (7 / 4 * (8 * Real.log 2) + 6.11676) +
          (2.49157 * c ^ 3 / 16 + c ^ 3 / 64 * (3 / 2 * (7 * Real.log 2) + 2.74107) +
            (3.59676 * Real.log 2 + 27.3032 * (7 * Real.log 2) + 91.515) * (c ^ 3 / 256)) :=
          eq12.symm
      _ ≤ bI1 (c ^ 3) 0 128 + bI2 (c ^ 3) 0 128 := add_le_add L1 L2
  have S1b : 3.25 * (c ^ 3 / Real.sqrt 128) ≤ bII (c ^ 3) 0 128 := by
    linarith only [L3, mul_le_mul_of_nonneg_left hab hK]
  have S1 : 1.44 * c ^ 3 + 3.25 * (c ^ 3 / Real.sqrt 128) ≤
      bI1 (c ^ 3) 0 128 + bI2 (c ^ 3) 0 128 + bII (c ^ 3) 0 128 + 3 * (Real.log (c ^ 3) + 1) := by
    linarith only [S1a, S1b, L4]
  have hmain : ((0.27125 * Real.log (26 / 21) + 0.41415) * (8 * Real.log 2) + 1.5) /
      Real.sqrt 128 * c ^ 3 = c ^ 3 / Real.sqrt 128 *
        ((0.27125 * Real.log (26 / 21) + 0.41415) * (8 * Real.log 2) + 1.5) := by ring
  rw [hmain] at H
  have S2 : c ^ 3 / Real.sqrt 128 *
        ((0.27125 * Real.log (26 / 21) + 0.41415) * (8 * Real.log 2) + 1.5) +
        2.5 * c ^ 3 / 16 + 2 * c ^ 3 / 256 * lToscaAt 22.7538 2 128 +
        3.2 * (c ^ 3) ^ ((5 : ℝ) / 6) ≤ 1.2659 * c ^ 3 + 4.156 * (c ^ 3 / Real.sqrt 128) := by
    linarith only [h56, hY0, mul_le_mul_of_nonneg_left hRb hK, mul_le_mul_of_nonneg_left hlT hT]
  linarith only [H, S1, S2, hK1, hY0]

/-- **The typed target's arithmetic is FALSE**: `ArithAt 0.5 22.7538` (the constants of
`OL.krawL`) fails, by `not_arith_05` and monotonicity in `cL`. -/
theorem not_arith_typed : ¬ ArithAt 0.5 22.7538 := fun h =>
  not_arith_05 (arithAt_mono 0.5 0.5 22.7538 45.7575 le_rfl (by norm_num) h)

end Principia.Common.TernaryGoldbach.MT
