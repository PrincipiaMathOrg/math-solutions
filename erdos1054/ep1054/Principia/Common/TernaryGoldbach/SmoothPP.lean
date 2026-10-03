/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.Smoothed
import Principia.Common.TernaryGoldbach.PrimePower

set_option autoImplicit false

/-!
# Link 4 of the smoothed spine, DISCHARGED for ANY weights at a `(log H)²` constant

`Smoothed.lean` reduces `Principia.Erdos1054.Cite_Helfgott_weighted` to Platt plus six named
links. This file **proves one of them, in a weaker-constant form that the composition still
accepts**, and re-proves the composition without it:

  `cite_of_smooth5 : PlattGRH → SupBounds → Summ → CircleIdSmooth → MajorLowerSmooth →
      MinorUpperSmooth → Cite_Helfgott_weighted`

(`PrimePowerSmooth` is gone). `cite5_no_summ` drops `Summ` as well, through
`Smooth.summ_of_major`. The remaining links are unchanged and all still OPEN; nothing here proves
any part of ternary Goldbach.

## What is proved, and at what constant

`pp_crude : SupBounds ηp ηs → ∀ odd H ≥ 10^27, tripleW ηp ηs H (helfgottX H) − ppErr H ≤
citeSum ηp ηs H`, with the explicit error

  `ppErr H = 13.73 · H^{3/2} · (log H)²`.

The stated link `Smooth.PrimePowerSmooth` asks for `7.3306 · H^{3/2} · log H` (one log). That
constant is Helfgott's arithmetic with Rosser–Schoenfeld and **is not what this file proves**:
`PrimePowerSmooth` itself stays OPEN. It is simply not needed, because the composition's margin is
far larger than either error term:

| quantity (in units of `H²`, at `H = 10^27`)          | value                  |
|------------------------------------------------------|------------------------|
| `0.084339·(490/989)²/49 − 0.000422` (the margin)      | `5.0509·10⁻⁷`          |
| stated (7.50) error `7.3306·log H/√H`                 | `1.44·10⁻¹¹`           |
| **this file's** `ppErr H / H² = 13.73·(log H)²/√H`    | `1.678·10⁻⁹`           |
| what `ppErr_le` PROVES for all `H ≥ 10^27`            | `≤ 1.373·10⁻⁸`         |
| margin left after `ppErr_le`                          | `4.9136·10⁻⁷ > 0`      |

(mpmath, 40 digits.) `ppErr_le` goes through `MinorArcBound.log_le_rt32` (`log H ≤ 9.01·H^{1/32}`)
and `2.64^28 = 6.38·10¹¹ ≥ 9.01²·10⁹ = 8.12·10¹⁰`. `Spine.log_sq_le_sqrt_div` would give only
`H²/10⁴`, which does NOT fit: it would charge `1.4·10⁻³ H²` against a `5·10⁻⁷` margin.

## The transfer (map §2.3, `Smoothed.lean` 75–87), checked against the sources

1. **Same index set, same scale.** `tripleW ηp ηs H x` and `citeSum ηp ηs H` both sum over
   `p ∈ Finset.range H`, `q ∈ Finset.range H`, third coordinate the natural `H − p − q`, and
   `PrimePowerSmooth` evaluates `tripleW` at `x = helfgottX H`, the scale hard-wired into
   `citeSum`. Both guards begin with `p + q < H`. The weight arguments agree character for
   character: `ηp (p/x)`, `ηp (q/x)`, `ηs (((H − p − q : ℕ) : ℝ)/x)`. This is not asserted but
   *checked*: `transfer_le` closes by `exact` against the unfolded `citeSum`, so a mismatch in any
   of these would not typecheck.
2. **Good triples agree.** When all three coordinates are odd primes, `Λ n = log n`
   (`vonMangoldt_apply_prime`), so the two summands coincide, and so do the corresponding
   summands of `Spine.lambdaTriple` and `ternaryLogCount`: both sides of `term_transfer` differ
   by `0`.
3. **Bad triples** (`p + q < H`, not all three odd primes): `citeSum` and `ternaryLogCount`
   contribute `0`; `tripleW` contributes `ΛΛΛ·w` with `w = ηp·ηp·ηs`, and `|w| ≤ 1.079955²·1.414
   = 1.6491521… ≤ 1.649153` (`weight_abs_le`, from `SupBounds` alone), while `lambdaTriple`
   contributes `ΛΛΛ ≥ 0`. So `ΛΛΛ·w ≤ 1.649153·ΛΛΛ`. **The bad triples need no primality
   reasoning at all** — only `ΛΛΛ ≥ 0` and the sup bound.
4. Summing: `tripleW − citeSum ≤ 1.649153·(lambdaTriple − ternaryLogCount)` (`transfer_le`), and
   `PrimePower.primePowerRemoval_all 8.32` bounds the bracket by `8.32·H^{3/2}(log H)²`.
   `1.649153 · 8.32 = 13.7209530 ≤ 13.73`.

**The transfer did not fail anywhere.** One point the docstring of `Smoothed.lean` did not state:
step 3 uses only an *upper* bound on `w` (`w ≤ |w|`), never a lower one, so negative weights are
covered too, and the Odd-ness of `H` is never used (`pp_crude_all` is the Odd-free statement;
`pp_crude` reinstates the binder to match the link's shape).

## Non-vacuity (the adversarial pass)

* **The hypothesis is met.** `SupBounds 0 0` is `Smooth.zero_rest.1` (`supBounds_zero`), and —
  a real, nonzero pair — `SupBounds 1 1` (`supBounds_one`, the constant weights `1`).
* **At unit weights the conclusion is the sharp-weight link itself.** `tripleW_one` and
  `citeSum_one` identify `tripleW 1 1 H x = lambdaTriple H` and `citeSum 1 1 H = ternaryLogCount
  H` (the latter by `simp only [mul_one]`, so the two `open Classical` guards agree), and
  `pp_crude_one` derives `Spine.PrimePowerRemoval 13.73` from `pp_crude` alone. So `pp_crude` is
  not a statement about some junk object: at `η ≡ 1` it IS the removal of prime powers and of the
  prime `2` from the ternary count, weaker than `PrimePower.primePowerRemoval_floor` (`8.32`) by
  exactly the sup-norm factor `1.649`, and by nothing else.
* **The error term is not doing the work.** `cite_of_smooth5` charges `ppErr` against the margin
  and still clears `0.000422` with `4.9·10⁻⁷ H²` to spare; `ppErr_le` is the explicit budget line.
-/

namespace Principia.Common.TernaryGoldbach.SmPP

open ArithmeticFunction
open scoped ArithmeticFunction
open Principia.Common.TernaryGoldbach.Smooth
open Principia.Erdos1054 (helfgottX Cite_Helfgott_weighted)

/-! ## The error term -/

/-- **The explicit error of the removal step**: `13.73 · H^{3/2} · (log H)²`. `13.73` is the round
number above `1.649153 · 8.32 = 13.72095…` (sup-norm factor × `PrimePower`'s removal constant). -/
noncomputable def ppErr (H : ℕ) : ℝ :=
  13.73 * ((H : ℝ) * Real.sqrt (H : ℝ)) * Real.log (H : ℝ) ^ 2

/-- `H·√H·(log H)² ≤ H²/10⁹` for `H ≥ 10^27`, via `log H ≤ 9.01·H^{1/32}` (`log_le_rt32`) and
`w = H^{1/64} ≥ 2.64`: the claim is `9.01²·w^100 ≤ w^128/10⁹`, i.e. `9.01²·10⁹ ≤ w^28`, and
`2.64^28 = 6.38·10¹¹ ≥ 8.12·10¹⁰`. The truth at the threshold is `1.22·10⁻¹⁰ H²`. -/
theorem err2_le (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    (H : ℝ) * Real.sqrt (H : ℝ) * Real.log (H : ℝ) ^ 2 ≤ (H : ℝ) ^ 2 / 10 ^ 9 := by
  have hlog := MinorArcBound.log_le_rt32 H hH
  have hL0 : (0 : ℝ) ≤ Real.log (H : ℝ) := le_trans (by norm_num) (Spine.log_ge_61 H hH)
  have hw0 : 0 ≤ MinorArcBound.rt64 H := MinorArcBound.rt64_nonneg H
  have hwge : (264 : ℝ) / 100 ≤ MinorArcBound.rt64 H := MinorArcBound.rt64_ge H hH
  have hsq : Real.sqrt (H : ℝ) = MinorArcBound.rt64 H ^ 32 := (MinorArcBound.rt64_pow32 H).symm
  have hHw : (H : ℝ) = MinorArcBound.rt64 H ^ 64 := (MinorArcBound.rt64_pow64 H).symm
  have hL2 : Real.log (H : ℝ) ^ 2 ≤ ((901 : ℝ) / 100 * MinorArcBound.rt64 H ^ 2) ^ 2 :=
    pow_le_pow_left₀ hL0 hlog 2
  have h28 : ((901 : ℝ) / 100) ^ 2 * 10 ^ 9 ≤ MinorArcBound.rt64 H ^ 28 :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hwge 28)
  have hw100 : (0 : ℝ) ≤ MinorArcBound.rt64 H ^ 100 := pow_nonneg hw0 100
  have hHs : (0 : ℝ) ≤ (H : ℝ) * Real.sqrt (H : ℝ) := by positivity
  calc (H : ℝ) * Real.sqrt (H : ℝ) * Real.log (H : ℝ) ^ 2
      ≤ (H : ℝ) * Real.sqrt (H : ℝ) * ((901 : ℝ) / 100 * MinorArcBound.rt64 H ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hL2 hHs
    _ = ((901 : ℝ) / 100) ^ 2 * MinorArcBound.rt64 H ^ 100 := by rw [hsq, hHw]; ring
    _ ≤ MinorArcBound.rt64 H ^ 28 / 10 ^ 9 * MinorArcBound.rt64 H ^ 100 :=
        mul_le_mul_of_nonneg_right (by linarith) hw100
    _ = (H : ℝ) ^ 2 / 10 ^ 9 := by rw [hHw]; ring

/-- **The budget line**: `ppErr H ≤ 13.73·H²/10⁹ = 1.373·10⁻⁸ H²` for `H ≥ 10^27`, against the
composition's margin `5.05·10⁻⁷ H²`. -/
theorem ppErr_le (H : ℕ) (hH : 10 ^ 27 ≤ H) : ppErr H ≤ 13.73 * ((H : ℝ) ^ 2 / 10 ^ 9) := by
  have h := err2_le H hH
  unfold ppErr
  linarith

/-! ## The transfer from sharp weights -/

/-- **`SupBounds` bounds every product of three weight values** by `1.079955²·1.414 =
1.6491521… ≤ 1.649153`. -/
theorem weight_abs_le (ηp ηs : ℝ → ℝ) (sb : SupBounds ηp ηs) (a b c : ℝ) :
    |ηp a * ηp b * ηs c| ≤ 1.649153 := by
  rw [abs_mul, abs_mul]
  have hab : |ηp a| * |ηp b| ≤ 1.079955 * 1.079955 :=
    mul_le_mul (sb.1 a) (sb.1 b) (abs_nonneg _) (by norm_num)
  calc |ηp a| * |ηp b| * |ηs c| ≤ 1.079955 * 1.079955 * 1.414 :=
        mul_le_mul hab (sb.2 c) (abs_nonneg _) (by norm_num)
    _ ≤ 1.649153 := by norm_num

/-- **The termwise transfer.** One summand of `tripleW` is at most the matching summand of
`citeSum` plus `1.649153` times the matching summand of `lambdaTriple − ternaryLogCount`. On a good
triple (three odd primes) both brackets agree because `Λ = log` there; on a bad triple the
`citeSum` and `ternaryLogCount` summands are `0` and `ΛΛΛ·w ≤ 1.649153·ΛΛΛ`. -/
theorem term_transfer (ηp ηs : ℝ → ℝ) (sb : SupBounds ηp ηs) (H p q : ℕ) (x : ℝ) :
    (if p + q < H then Λ p * Λ q * Λ (H - p - q) *
        ηp ((p : ℝ) / x) * ηp ((q : ℝ) / x) * ηs (((H - p - q : ℕ) : ℝ) / x) else 0)
      ≤ (if p + q < H ∧ p.Prime ∧ q.Prime ∧ (H - p - q).Prime ∧ Odd p ∧ Odd q ∧ Odd (H - p - q)
          then Real.log p * Real.log q * Real.log ((H - p - q : ℕ) : ℝ) *
            ηp ((p : ℝ) / x) * ηp ((q : ℝ) / x) * ηs (((H - p - q : ℕ) : ℝ) / x)
          else 0)
        + 1.649153 * ((if p + q < H then Λ p * Λ q * Λ (H - p - q) else 0)
          - (if p + q < H ∧ p.Prime ∧ q.Prime ∧ (H - p - q).Prime ∧ Odd p ∧ Odd q ∧
                Odd (H - p - q)
              then Real.log p * Real.log q * Real.log ((H - p - q : ℕ) : ℝ) else 0)) := by
  by_cases hpq : p + q < H
  · rw [if_pos hpq, if_pos hpq]
    by_cases hg : p.Prime ∧ q.Prime ∧ (H - p - q).Prime ∧ Odd p ∧ Odd q ∧ Odd (H - p - q)
    · have hall : p + q < H ∧ p.Prime ∧ q.Prime ∧ (H - p - q).Prime ∧ Odd p ∧ Odd q ∧
          Odd (H - p - q) := ⟨hpq, hg⟩
      rw [if_pos hall, if_pos hall, vonMangoldt_apply_prime hg.1,
        vonMangoldt_apply_prime hg.2.1, vonMangoldt_apply_prime hg.2.2.1]
      linarith
    · have hbad : ¬(p + q < H ∧ p.Prime ∧ q.Prime ∧ (H - p - q).Prime ∧ Odd p ∧ Odd q ∧
          Odd (H - p - q)) := fun h => hg h.2
      rw [if_neg hbad, if_neg hbad]
      have hΛ : (0 : ℝ) ≤ Λ p * Λ q * Λ (H - p - q) :=
        mul_nonneg (mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg) vonMangoldt_nonneg
      have hw : ηp ((p : ℝ) / x) * ηp ((q : ℝ) / x) * ηs (((H - p - q : ℕ) : ℝ) / x)
          ≤ 1.649153 :=
        le_trans (le_abs_self _) (weight_abs_le ηp ηs sb _ _ _)
      calc Λ p * Λ q * Λ (H - p - q) * ηp ((p : ℝ) / x) * ηp ((q : ℝ) / x)
            * ηs (((H - p - q : ℕ) : ℝ) / x)
          = Λ p * Λ q * Λ (H - p - q)
            * (ηp ((p : ℝ) / x) * ηp ((q : ℝ) / x) * ηs (((H - p - q : ℕ) : ℝ) / x)) := by
            ring
        _ ≤ Λ p * Λ q * Λ (H - p - q) * 1.649153 := mul_le_mul_of_nonneg_left hw hΛ
        _ = 0 + 1.649153 * (Λ p * Λ q * Λ (H - p - q) - 0) := by ring
  · have hbad : ¬(p + q < H ∧ p.Prime ∧ q.Prime ∧ (H - p - q).Prime ∧ Odd p ∧ Odd q ∧
        Odd (H - p - q)) := fun h => hpq h.1
    rw [if_neg hpq, if_neg hpq, if_neg hbad, if_neg hbad]
    norm_num

/-- **The transfer, summed**: `tripleW − citeSum ≤ 1.649153·(lambdaTriple − ternaryLogCount)` at
`x = helfgottX H`. Closed by `exact` against the unfolded definitions, so the index sets, the
scale `helfgottX H`, and every weight argument of `tripleW` and `citeSum` are checked to agree. -/
theorem transfer_le (ηp ηs : ℝ → ℝ) (sb : SupBounds ηp ηs) (H : ℕ) :
    tripleW ηp ηs H (helfgottX H) - citeSum ηp ηs H
      ≤ 1.649153 * (Spine.lambdaTriple H - ternaryLogCount H) := by
  have key : tripleW ηp ηs H (helfgottX H)
      ≤ citeSum ηp ηs H + 1.649153 * (Spine.lambdaTriple H - ternaryLogCount H) := by
    rw [tripleW, citeSum, Spine.lambdaTriple, ternaryLogCount, ← Finset.sum_sub_distrib,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun q _ => term_transfer ηp ηs sb H p q (helfgottX H)
  linarith

/-! ## LINK 4, DISCHARGED (at the `(log H)²` constant) -/

/-- **Prime-power and parity removal for ANY weights obeying `SupBounds`, without `Odd H`** — the
stronger statement, recorded so the unused parity hypothesis is a theorem rather than a remark. -/
theorem pp_crude_all (ηp ηs : ℝ → ℝ) (sb : SupBounds ηp ηs) :
    ∀ H : ℕ, 10 ^ 27 ≤ H → tripleW ηp ηs H (helfgottX H) - ppErr H ≤ citeSum ηp ηs H := by
  intro H hH
  have ht := transfer_le ηp ηs sb H
  have hr := PrimePower.primePowerRemoval_all 8.32 (le_refl _) H hH
  have hnn : (0 : ℝ) ≤ (H : ℝ) * Real.sqrt (H : ℝ) * Real.log (H : ℝ) ^ 2 := by positivity
  have h1 : Spine.lambdaTriple H - ternaryLogCount H
      ≤ 8.32 * ((H : ℝ) * Real.sqrt (H : ℝ) * Real.log (H : ℝ) ^ 2) := by linarith
  have h2 : 1.649153 * (Spine.lambdaTriple H - ternaryLogCount H)
      ≤ 1.649153 * (8.32 * ((H : ℝ) * Real.sqrt (H : ℝ) * Real.log (H : ℝ) ^ 2)) :=
    mul_le_mul_of_nonneg_left h1 (by norm_num)
  unfold ppErr
  linarith

/-- **`pp_crude` — link 4 of `Smoothed.lean` in the shape of `Smooth.PrimePowerSmooth`, with error
`ppErr H = 13.73·H^{3/2}(log H)²` in place of `7.3306·H^{3/2} log H`.** Holds for every weight pair
obeying `SupBounds`; no property of Helfgott's `η₊`, `η_*` beyond their sup norms is used. -/
theorem pp_crude (ηp ηs : ℝ → ℝ) (sb : SupBounds ηp ηs) :
    ∀ H : ℕ, Odd H → 10 ^ 27 ≤ H →
      tripleW ηp ηs H (helfgottX H) - ppErr H ≤ citeSum ηp ηs H :=
  fun H _ hH => pp_crude_all ηp ηs sb H hH

/-! ## THE SPINE, WITH FIVE LINKS -/

/-- **`Smooth.cite_of_smooth` with `PrimePowerSmooth` REMOVED.** Platt plus five links deliver
`Cite_Helfgott_weighted`; the removal step is `pp_crude`, and the arithmetic is
`0.084339·(490/989)²/49 − 13.73/10⁹ = 0.00042249… ≥ 0.000422`. -/
theorem cite_of_smooth5 (ηp ηs : ℝ → ℝ) (grh : Spine.PlattGRH) (sb : SupBounds ηp ηs)
    (sm : Summ ηp ηs) (ci : CircleIdSmooth ηp ηs) (mj : MajorLowerSmooth ηp ηs)
    (mn : MinorUpperSmooth ηp ηs) : Cite_Helfgott_weighted := by
  refine cite_iff.mpr fun H hodd hH => ⟨ηp, ηs, sb.1, sb.2, ?_⟩
  have hW := weighted_lower ηp ηs grh sm ci mj mn H hodd hH
  have hP := pp_crude ηp ηs sb H hodd hH
  have hH0 : (0 : ℝ) ≤ (490 : ℝ) / 989 * H := by positivity
  have hx2 : ((490 : ℝ) / 989 * H) ^ 2 ≤ helfgottX H ^ 2 := pow_le_pow_left₀ hH0 (helfX_ge H) 2
  have hx2' : (490 : ℝ) ^ 2 / 989 ^ 2 * (H : ℝ) ^ 2 ≤ helfgottX H ^ 2 :=
    le_of_eq_of_le (by ring) hx2
  have hE := ppErr_le H hH
  have hH2 : (0 : ℝ) ≤ (H : ℝ) ^ 2 := sq_nonneg _
  linarith

/-- **Four links and Platt**: `Summ` is supplied by `Smooth.summ_of_major`, as in
`Smooth.cite_no_summ`. -/
theorem cite5_no_summ (ηp ηs : ℝ → ℝ) (grh : Spine.PlattGRH) (sb : SupBounds ηp ηs)
    (ci : CircleIdSmooth ηp ηs) (mj : MajorLowerSmooth ηp ηs) (mn : MinorUpperSmooth ηp ηs) :
    Cite_Helfgott_weighted :=
  cite_of_smooth5 ηp ηs grh sb (summ_of_major ηp ηs grh mj) ci mj mn

/-- The existential form, one weight pair for all `N`, with five links. -/
theorem cite_of_smooth5_ex (grh : Spine.PlattGRH)
    (links : ∃ ηp ηs : ℝ → ℝ, SupBounds ηp ηs ∧ Summ ηp ηs ∧ CircleIdSmooth ηp ηs ∧
      MajorLowerSmooth ηp ηs ∧ MinorUpperSmooth ηp ηs) :
    Cite_Helfgott_weighted := by
  obtain ⟨ηp, ηs, sb, sm, ci, mj, mn⟩ := links
  exact cite_of_smooth5 ηp ηs grh sb sm ci mj mn

/-! ## Non-vacuity -/

/-- **The hypothesis of `pp_crude` is met by the zero weights**: this is `Smooth.zero_rest.1`. -/
theorem supBounds_zero : SupBounds 0 0 := zero_rest.1

/-- **… and by a nonzero pair**: the constant weights `1`. -/
theorem supBounds_one : SupBounds (fun _ => 1) (fun _ => 1) :=
  ⟨fun _ => by norm_num, fun _ => by norm_num⟩

/-- At unit weights `tripleW` is the unweighted `Λ`-triple sum of `Spine`. -/
theorem tripleW_one (H : ℕ) (x : ℝ) :
    tripleW (fun _ => 1) (fun _ => 1) H x = Spine.lambdaTriple H := by
  simp only [tripleW, Spine.lambdaTriple, mul_one]

/-- At unit weights `citeSum` is `ternaryLogCount`, the count over ordered triples of odd primes. -/
theorem citeSum_one (H : ℕ) : citeSum (fun _ => 1) (fun _ => 1) H = ternaryLogCount H := by
  simp only [citeSum, ternaryLogCount, mul_one]

/-- **At unit weights `pp_crude` IS the sharp-weight removal link** `Spine.PrimePowerRemoval`, at
`cPP = 13.73`: so its conclusion is the genuine removal of prime powers and of `2`, not a statement
about a degenerate object. (The library already has `8.32`; the gap is exactly the sup-norm factor
`1.649`.) -/
theorem pp_crude_one : Spine.PrimePowerRemoval 13.73 := by
  intro H hodd hH
  have h := pp_crude (fun _ => 1) (fun _ => 1) supBounds_one H hodd hH
  rw [tripleW_one, citeSum_one] at h
  unfold ppErr at h
  exact h

end Principia.Common.TernaryGoldbach.SmPP
