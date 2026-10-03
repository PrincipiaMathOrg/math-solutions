/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MajorFromPlatt
import Principia.Common.TernaryGoldbach.SingularSeries

set_option autoImplicit false

/-!
# The singular-series bridge: `MajorFromPlatt.SingularSeriesLower (5/4)`, discharged

`SingularSeries.lean` proves the **full** series bound `𝔖₃(N) ≥ 131/100` for odd `N`
(`sing3_ge_sharp`) and leaves its truncated form with a non-effective `R₀`
(`exists_Sing3TailUniform`). `MajorFromPlatt.lean` needs the **truncated** bound at its own cutoff,
`SingularSeriesLower cSing = ∀ H odd ≥ 10²⁷, cSing ≤ singSeriesTrunc H (Pcut H)`. The two modules
were written in parallel and never imported each other. This file joins them, and the join needs
exactly two things: that the two truncations are the *same object*, and an **effective** tail.

## 1. The two truncations are the same object — checked, not assumed

`MajorPlatt.localTerm q H` and `SingularSeries.sing3Local q N` are `μ(q)³c_q(·)/φ(q)³` character for
character, in the same argument order; `MajorPlatt.singSeriesTrunc H P` and
`SingularSeries.sing3Trunc N R` are both `∑ q ∈ Finset.Icc 1 (cutoff)` of their local term, with the
value first and the cutoff second. So `singSeriesTrunc_eq` holds **by `rfl`** — same index set
(`Icc 1 P`, not `range`), same endpoint convention, no off-by-one at `q = 0` or `q = 1`. That was
the
step with the most room to go silently wrong (a `range` against an `Icc`, or a swapped argument
order, would have produced a bridge that compiles and bridges the wrong pair), so it is a named
theorem rather than a `rfl` buried inside a larger proof.

## 2. The effective tail is `16/√R`, not `R^{-1/8}`

`SingularSeries.sing3Maj q = μ(q)²/φ(q)²` dominates `‖T₃(q,N)‖` uniformly in `N`
(`norm_sing3Arith_le_maj`), and the library's `sqfree_totient_strong` (`q^{3/2} ≤ 8φ(q)²`) gives

  `μ(q)²/φ(q)² ≤ 8/(q√q)`  for **every** `q ≥ 1`  (`sing3Maj_le`; `μ(q) = 0` off squarefree),

whose tail telescopes against `16/√·`: `8/(b√b) ≤ 16/√a − 16/√b` for `b = a + 1`, because
`1/√a − 1/√b = 1/(√a√b(√a+√b))` and `√a√b(√a+√b) ≤ 2b√b` (`sqrt_tail_step`). Hence
`∑_{q>R} μ(q)²/φ(q)² ≤ 16/√R` with **no existential**, and `Sing3TailUniform R₀ (16/√R₀)` for every
`R₀ ≥ 1` (`sing3TailUniform_effective`). An earlier draft of `SingularSeries.lean` recorded this
route as giving only `R^{-1/8}` and being "numerically vacuous"; that was wrong by a power of four
and is corrected there. The rate is `R^{-1/2}`.

**The numbers, computed in `python` before any Lean and each recomputed a second way.**
`Pcut H = 300000` for every `H`, so the tail is a *constant*: `16/√(3·10⁵) = 0.0292118697`
(rational check: `16/⌊√(3·10⁵)⌋ = 16/547 = 0.02925`, an upper bound, also `≤ 3/100`). Therefore

  `𝔖₃(H, 3·10⁵) ≥ 131/100 − 0.02921 = 1.2807881`,

so the requested `cSing = 5/4` carries a margin of `0.0307881` (`2.5 %`), and `32/25 = 1.28` is also
reachable — delivered as `singularSeriesLower_holds_sharp`, the largest round constant this route
gives at the real `Pcut`. The threshold for `5/4` is `16/√R ≤ 3/50`, i.e. `9R ≥ 640000`, i.e.
**`R ≥ 71112`**; `Pcut = 3·10⁵` clears it by `4.2×` (in `R`). The bound `16/√R` is itself `4875×`
above the true tail `5.99·10⁻⁶` at `R = 3·10⁵` — lossy and effective, which is the trade that
matters here.

## 3. What this closes, and what it does not

`MajorPlatt.majorArcLower_of_chain` had **five** hypotheses; `majorArcLower_of_platt_chain` below
has
four, and `cite_Helfgott_weighted_of_platt_chain_ss` takes the EP1054 input from **eight** to
**seven**. Nothing here proves any part of ternary Goldbach: `FareyDecomposition`,
`WindowApproxUnder`, `KernelTailBound`, `MinorSupBound` and `PlattGRH` remain open.

## 4. The two defects of `majorArcLower_of_chain`, repaired

**(a) The free rider.** `PlattGRHAt T` at `T = −1` is *provable* (empty box), so a `PlattGRHAt` slot
under an unconstrained `T` reduces nothing to Platt. `majorArcLower_no_platt_at_vacuous_height`
below
exhibits the defect as a theorem — the chain with **no numerical input in its signature at all** —
and `vacuous_height_is_refused` exhibits the repair: `MajorPlatt.PlattGRHAtLeast`, the guarded
bundle that `majorArcLower_of_chain` now takes, *refuses* that exact instance, while
`MajorPlatt.plattGRH_of_plattGRHAtLeast` proves every admissible instance carries `PlattGRH` and
hence a piece of RH. The audit's proposed repair ("have the downstream `Prop` consume the zero
information") was already in place — `WindowApproxUnder cW σ T` is literally `ZeroBoxes T σ → …`.
The hole was the unconstrained height, and the guard is what closes it.

**(b) The constant — AND THE ARGUMENT BELOW WAS WRONG; RETRACTED 2026-09-29.** `cW = 1000` asserts a
relative major-arc error of `1.85·10⁻⁷` at `H = 10²⁷`, which is five orders tighter than the
`3.06 %` Helfgott's §7.4 operates at. An earlier version of this docstring concluded from that that
**no** `cW` reachable through `Spine.pp_slack` "can be true". **That inference is invalid, and the
refutation needs no numerics** (round-4 audit): Helfgott's `3.06 %` is an UPPER bound on the
error he
can AFFORD TO LOSE, not a lower bound on the true major-arc error — if his actual error were `3
%` of
the main term his own theorem would fail. **An upper bound on someone else's budget cannot bound the
actual quantity from below.** So the truth of `WindowApproxUnder 1000 (1/2) T` is **UNKNOWN**: not
proved, and NOT known false. The budget is not at fault either (`0.125H²` is `18.9 %` relative).
`errScale_le_sq_sharp` proves `errScale H ≤ H²/10⁸` — a `5.7×`-margin bound through
`log H ≤ 32·H^{1/32}` and `48 ≤ H^{1/16}` — lifting the ceiling to `cW ≤ 1.25·10⁷`, and
`majorArcLower_of_chain_param` puts `cW`, `cK` and the slack **scale** in the signature with the
budget as a side condition, so no constant is baked in. `errScale ≤ H²/10¹⁰` is false at the
threshold, so `10⁹`/`cW ≤ 1.25·10⁸` (`2.3 %` relative) is the hard ceiling of this scale: it
brackets
Helfgott's `3.06 %` only just, and two independent triangle-inequality estimates (agreeing to
`1.03×`) put the *crude* requirement at `cW ≈ 2.5·10¹⁴`, reachable on this scale only from
`H ≥ 2.5·10³⁸`. **The `H^{3/2}(log H)²` scale has about one order of slack at `10²⁷`; a crude
treatment needs six more.**
-/

namespace Principia.Common.TernaryGoldbach.SingularBridge

open Principia.Common.Goldbach
open Principia.Common.Goldbach.MajorArcMainTerm
open Principia.Common.TernaryGoldbach.Spine

/-! ## Step 0 — the two truncations ARE the same object -/

/-- `MajorPlatt.localTerm` and `SingularSeries.sing3Local` are `μ(q)³c_q(N)/φ(q)³` character for
character, in the same argument order. -/
theorem localTerm_eq (q H : ℕ) : MajorPlatt.localTerm q H = SingularSeries.sing3Local q H := rfl

/-- **The reconciliation.** Both truncations are `∑ q ∈ Finset.Icc 1 (cutoff)` of the same local
term, value first and cutoff second, so they are equal by `rfl`: same index set, same endpoints, no
off-by-one at `q = 0` or `q = 1`. Stated as a theorem because a `range`-versus-`Icc` or a swapped
argument order here would have produced a bridge that compiles and joins the wrong pair. -/
theorem singSeriesTrunc_eq (H P : ℕ) :
    MajorPlatt.singSeriesTrunc H P = SingularSeries.sing3Trunc H P := rfl

/-! ## Step 1 — the effective majorant bound `μ(q)²/φ(q)² ≤ 8/(q√q)` -/

/-- `x^{3/2} = x·√x` for `x > 0`, in the form `sqfree_totient_strong` has to be met in. -/
theorem mul_sqrt_eq_rpow (x : ℝ) (hx : 0 < x) : x * Real.sqrt x = x ^ ((3 : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_add hx,
    Real.rpow_one]

/-- **The effective majorant bound.** `sing3Maj q = μ(q)²/φ(q)² ≤ 8/(q√q)` for every `q ≥ 1`. On
squarefree `q` this is `sqfree_totient_strong` (`q^{3/2} ≤ 8φ(q)²`) together with `μ(q)² ≤ 1`; off
squarefree `μ(q) = 0` and the left side is `0`, which is why the bound needs no squarefreeness
hypothesis and therefore sums over *all* `q`. -/
theorem sing3Maj_le (q : ℕ) (hq : 1 ≤ q) :
    SingularSeries.sing3Maj q ≤ 8 / ((q : ℝ) * Real.sqrt (q : ℝ)) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hpow := mul_sqrt_eq_rpow (q : ℝ) hqR
  have hrpos : (0 : ℝ) < (q : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hqR _
  by_cases hsf : Squarefree q
  · have hφ : (0 : ℝ) < (Nat.totient q : ℝ) := by
      have h := Nat.totient_pos.mpr (show 0 < q by omega)
      exact_mod_cast h
    have hts := sqfree_totient_strong q hsf
    have hμ : (ArithmeticFunction.moebius q : ℝ) ^ 2 ≤ 1 := by
      have h1 : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
      nlinarith [h1, abs_nonneg ((ArithmeticFunction.moebius q : ℤ) : ℝ),
        sq_abs ((ArithmeticFunction.moebius q : ℤ) : ℝ)]
    rw [SingularSeries.sing3Maj, hpow, div_le_div_iff₀ (pow_pos hφ 2) hrpos]
    nlinarith [hts, hμ, hrpos.le, pow_pos hφ 2]
  · have h0 : SingularSeries.sing3Maj q = 0 := by
      rw [SingularSeries.sing3Maj, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
      norm_num
    rw [h0]
    positivity

/-! ## Step 2 — the telescope

The whole tail estimate rests on one inequality, and it is monotonicity in `√a` and nothing more:
`1/√a − 1/√b = 1/(√a√b(√a+√b))` exactly (because `b − a = 1`), and `√a ≤ √b` turns the denominator
into `≤ √b·√b·2√b = 2b√b`. -/

/-- `8/((a+1)√(a+1)) ≤ 16/√a − 16/√(a+1)` for `a > 0`: the telescoping step behind
`∑_{q>R} 8q^{-3/2} ≤ 16/√R`. -/
theorem sqrt_tail_step (a : ℝ) (ha : 0 < a) :
    8 / ((a + 1) * Real.sqrt (a + 1)) ≤ 16 / Real.sqrt a - 16 / Real.sqrt (a + 1) := by
  have hb : (0 : ℝ) < a + 1 := by linarith
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have ht : 0 < Real.sqrt (a + 1) := Real.sqrt_pos.mpr hb
  have hss : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
  have htt : Real.sqrt (a + 1) * Real.sqrt (a + 1) = a + 1 := Real.mul_self_sqrt hb.le
  have hle : Real.sqrt a ≤ Real.sqrt (a + 1) := Real.sqrt_le_sqrt (by linarith)
  have hX : (0 : ℝ) < Real.sqrt a * Real.sqrt (a + 1) * (Real.sqrt a + Real.sqrt (a + 1)) := by
    positivity
  have hprod : (16 / Real.sqrt a - 16 / Real.sqrt (a + 1))
      * (Real.sqrt a * Real.sqrt (a + 1) * (Real.sqrt a + Real.sqrt (a + 1))) = 16 := by
    have h1 : (16 / Real.sqrt a - 16 / Real.sqrt (a + 1))
        * (Real.sqrt a * Real.sqrt (a + 1) * (Real.sqrt a + Real.sqrt (a + 1)))
        = 16 * (Real.sqrt (a + 1) * Real.sqrt (a + 1) - Real.sqrt a * Real.sqrt a) := by
      field_simp
      ring
    rw [h1, hss, htt]
    ring
  have hval : 16 / Real.sqrt a - 16 / Real.sqrt (a + 1)
      = 16 / (Real.sqrt a * Real.sqrt (a + 1) * (Real.sqrt a + Real.sqrt (a + 1))) :=
    (eq_div_iff hX.ne').mpr hprod
  have h1 : Real.sqrt a * Real.sqrt a ≤ Real.sqrt (a + 1) * Real.sqrt (a + 1) :=
    mul_le_mul hle hle hs.le ht.le
  have h2 : Real.sqrt a * Real.sqrt (a + 1) ≤ Real.sqrt (a + 1) * Real.sqrt (a + 1) :=
    mul_le_mul_of_nonneg_right hle ht.le
  have hXle : Real.sqrt a * Real.sqrt (a + 1) * (Real.sqrt a + Real.sqrt (a + 1))
      ≤ 2 * ((a + 1) * Real.sqrt (a + 1)) := by
    have h3 : 2 * ((a + 1) * Real.sqrt (a + 1))
        = 2 * (Real.sqrt (a + 1) * Real.sqrt (a + 1) * Real.sqrt (a + 1)) := by rw [htt]
    rw [h3]
    nlinarith [mul_le_mul_of_nonneg_right h1 ht.le, mul_le_mul_of_nonneg_right h2 ht.le]
  rw [hval, div_le_div_iff₀ (by positivity) hX]
  linarith [hXle]

/-! ## Step 3 — the tail, effectively -/

/-- The telescoped partial sums of the majorant beyond `R`, bounded **uniformly in the number of
terms** — which is what a `tsum` bound needs. -/
theorem maj_sum_range_le (R M : ℕ) (hR : 1 ≤ R) :
    ∑ i ∈ Finset.range M, SingularSeries.sing3Maj (i + (R + 1)) ≤ 16 / Real.sqrt (R : ℝ) := by
  set F : ℕ → ℝ := fun i => 16 / Real.sqrt ((R + i : ℕ) : ℝ) with hF
  have hstep : ∀ i ∈ Finset.range M,
      SingularSeries.sing3Maj (i + (R + 1)) ≤ F i - F (i + 1) := by
    intro i _
    have ha : (0 : ℝ) < ((R + i : ℕ) : ℝ) := by
      have : 0 < R + i := by omega
      exact_mod_cast this
    have hEq : ((R + (i + 1) : ℕ) : ℝ) = ((R + i : ℕ) : ℝ) + 1 := by push_cast; ring
    have hidx : i + (R + 1) = R + (i + 1) := by omega
    have h1 : SingularSeries.sing3Maj (i + (R + 1))
        ≤ 8 / ((((R + i : ℕ) : ℝ) + 1) * Real.sqrt (((R + i : ℕ) : ℝ) + 1)) := by
      have h := sing3Maj_le (R + (i + 1)) (by omega)
      rw [hEq] at h
      rw [hidx]
      exact h
    have h2 := sqrt_tail_step (((R + i : ℕ) : ℝ)) ha
    have h3 : F (i + 1) = 16 / Real.sqrt (((R + i : ℕ) : ℝ) + 1) := by
      simp only [hF]
      rw [hEq]
    rw [h3]
    simp only [hF]
    linarith [h1, h2]
  have hFM : (0 : ℝ) ≤ F M := by simp only [hF]; positivity
  have hF0 : F 0 = 16 / Real.sqrt (R : ℝ) := by simp only [hF, Nat.add_zero]
  calc ∑ i ∈ Finset.range M, SingularSeries.sing3Maj (i + (R + 1))
      ≤ ∑ i ∈ Finset.range M, (F i - F (i + 1)) := Finset.sum_le_sum hstep
    _ = F 0 - F M := Finset.sum_range_sub' F M
    _ ≤ F 0 := by linarith
    _ = 16 / Real.sqrt (R : ℝ) := hF0

/-- **`∑_{q>R} μ(q)²/φ(q)² ≤ 16/√R`, with no existential.** The effective replacement for the
`Summable`-existential inside `SingularSeries.exists_Sing3TailUniform`. -/
theorem maj_tail_le (R : ℕ) (hR : 1 ≤ R) :
    ∑' i : ℕ, SingularSeries.sing3Maj (i + (R + 1)) ≤ 16 / Real.sqrt (R : ℝ) :=
  Real.tsum_le_of_sum_range_le (fun _ => SingularSeries.sing3Maj_nonneg _)
    (fun M => maj_sum_range_le R M hR)

set_option maxHeartbeats 1000000 in
-- Inherited from `SingularSeries.exists_Sing3TailUniform`, whose shape this proof reuses: the
-- `SummationFilter`-parameterised `Summable`/`tsum` API (`sum_add_tsum_nat_add`,
-- `summable_nat_add_iff`, `norm_tsum_le_tsum_norm`, `Summable.tsum_le_tsum`) elaborates slowly on
-- this instance chain and the default 200000 heartbeats is not enough for this one proof.
/-- **`Sing3TailUniform` with an EFFECTIVE `R₀`.** `Sing3TailUniform R₀ (16/√R₀)` for every
`R₀ ≥ 1` — the same statement `SingularSeries.exists_Sing3TailUniform` proves with an unspecified
`R₀`, now with the pair `(R₀, ε)` given explicitly. (The heartbeat bump is inherited from that
proof: the `SummationFilter`-parameterised `Summable`/`tsum` API elaborates slowly on this instance
chain.) -/
theorem sing3TailUniform_effective (R₀ : ℕ) (hR₀ : 1 ≤ R₀) :
    SingularSeries.Sing3TailUniform R₀ (16 / Real.sqrt (R₀ : ℝ)) := by
  intro N R hN hR
  have hN1 : 1 ≤ N := by obtain ⟨k, rfl⟩ := hN; omega
  have hR1 : 1 ≤ R := le_trans hR₀ hR
  have hsumN : Summable (fun q : ℕ => SingularSeries.sing3Arith N q) :=
    Summable.of_norm (SingularSeries.sing3_summable N hN1)
  have hsplit : (∑ i ∈ Finset.range (R + 1), SingularSeries.sing3Arith N i)
      + (∑' i : ℕ, SingularSeries.sing3Arith N (i + (R + 1)))
      = ∑' q : ℕ, SingularSeries.sing3Arith N q :=
    Summable.sum_add_tsum_nat_add (R + 1) hsumN
  have hdiff : SingularSeries.sing3 N - SingularSeries.sing3Trunc N R
      = ∑' i : ℕ, SingularSeries.sing3Arith N (i + (R + 1)) := by
    rw [SingularSeries.sing3Trunc_eq_range, SingularSeries.sing3, ← hsplit]
    ring
  have hnormsum : Summable (fun i : ℕ => ‖SingularSeries.sing3Arith N (i + (R + 1))‖) :=
    (summable_nat_add_iff (R + 1)).mpr (SingularSeries.sing3_summable N hN1)
  have hmajshift : Summable (fun i : ℕ => SingularSeries.sing3Maj (i + (R + 1))) :=
    (summable_nat_add_iff (R + 1)).mpr SingularSeries.sing3Maj_summable
  have hR₀R : (1 : ℝ) ≤ (R₀ : ℝ) := by exact_mod_cast hR₀
  have h0 : (0 : ℝ) < Real.sqrt (R₀ : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hsle : Real.sqrt (R₀ : ℝ) ≤ Real.sqrt (R : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hR)
  have hmono : 16 / Real.sqrt (R : ℝ) ≤ 16 / Real.sqrt (R₀ : ℝ) := by
    rw [div_le_div_iff₀ (lt_of_lt_of_le h0 hsle) h0]
    linarith
  rw [hdiff, ← Real.norm_eq_abs]
  calc ‖∑' i : ℕ, SingularSeries.sing3Arith N (i + (R + 1))‖
      ≤ ∑' i : ℕ, ‖SingularSeries.sing3Arith N (i + (R + 1))‖ := norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' i : ℕ, SingularSeries.sing3Maj (i + (R + 1)) :=
        Summable.tsum_le_tsum (fun i => SingularSeries.norm_sing3Arith_le_maj N _) hnormsum
          hmajshift
    _ ≤ 16 / Real.sqrt (R : ℝ) := maj_tail_le R hR1
    _ ≤ 16 / Real.sqrt (R₀ : ℝ) := hmono

/-! ## Step 4 — the arithmetic at the real cutoff -/

/-- `a ≤ √x` from `a² ≤ x`, the step used four times to descend the root tower. -/
theorem sqrt_ge_of_sq_le {a x : ℝ} (ha : 0 ≤ a) (h : a ^ 2 ≤ x) : a ≤ Real.sqrt x := by
  have h2 : Real.sqrt (a ^ 2) ≤ Real.sqrt x := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq ha] at h2

/-- **`16/√(3·10⁵) ≤ 3/100`.** Via `√(3·10⁵) ≥ 1600/3` (`(1600/3)² = 284444.4 ≤ 3·10⁵`). The truth
is `0.0292118697`; `3/100` is the round constant that delivers `32/25` below, and `3/50` (needed for
`5/4`) is reached from `R ≥ 71112`. -/
theorem tail_at_cutoff_le : (16 : ℝ) / Real.sqrt ((300000 : ℕ) : ℝ) ≤ 3 / 100 := by
  have hc : ((300000 : ℕ) : ℝ) = (300000 : ℝ) := by norm_num
  rw [hc]
  have h1 : ((1600 : ℝ) / 3) ≤ Real.sqrt (300000 : ℝ) :=
    sqrt_ge_of_sq_le (by norm_num) (by norm_num)
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- **The truncated ternary singular series at any cutoff `≥ 3·10⁵` is `≥ 32/25 = 1.28`**, for every
odd `N`. `sing3_ge_sharp` gives `131/100` for the full series and `sing3TailUniform_effective` pays
`3/100` for the truncation. -/
theorem sing3Trunc_ge_at_cutoff (N R : ℕ) (hN : Odd N) (hR : 300000 ≤ R) :
    (32 : ℝ) / 25 ≤ SingularSeries.sing3Trunc N R := by
  have h1 := sing3TailUniform_effective 300000 (by norm_num) N R hN hR
  have h2 := SingularSeries.sing3_ge_sharp N hN
  have h3 : SingularSeries.sing3 N - SingularSeries.sing3Trunc N R
      ≤ 16 / Real.sqrt ((300000 : ℕ) : ℝ) := (abs_le.mp h1).2
  have h4 := tail_at_cutoff_le
  linarith

/-- `SingularSeriesLower` is antitone in its constant. -/
theorem singularSeriesLower_mono {c c' : ℝ} (h : c ≤ c')
    (hss : MajorPlatt.SingularSeriesLower c') : MajorPlatt.SingularSeriesLower c :=
  fun H hodd hH => le_trans h (hss H hodd hH)

/-- **THE SHARP DELIVERABLE.** `MajorPlatt.SingularSeriesLower (32/25)`, with **no hypotheses** —
`32/25 = 1.28` is the largest round constant this route reaches at the real `Pcut = 3·10⁵`
(`131/100 − 16/√(3·10⁵) = 1.2807881`). -/
theorem singularSeriesLower_holds_sharp : MajorPlatt.SingularSeriesLower (32 / 25) := by
  intro H hodd _
  rw [singSeriesTrunc_eq]
  exact sing3Trunc_ge_at_cutoff H (MajorPlatt.Pcut H) hodd
    (le_of_eq (MajorPlatt.Pcut_apply H).symm)

/-- **THE DELIVERABLE, as `MajorFromPlatt` asks for it**: `SingularSeriesLower (5/4)`, with no
hypotheses. Margin over the route's own `1.2807881` is `0.0307881`. -/
theorem singularSeriesLower_holds : MajorPlatt.SingularSeriesLower (5 / 4) :=
  singularSeriesLower_mono (by norm_num) singularSeriesLower_holds_sharp

/-! ## Step 5 — the chain, with the singular series supplied -/

/-- **`majorArcLower_of_chain` with its singular-series slot discharged: five hypotheses become
four.**

**The `cW = 1000` in the `WindowApproxUnder` slot is UNPROVED and of UNKNOWN truth** — see the
retraction in this file's §4(b). It is NOT known false; the earlier claim that it was rested on an
invalid inference. `majorArcLower_of_chain_param` is the form that keeps `cW` a parameter. -/
theorem majorArcLower_of_platt_chain (grh : PlattGRH) (fd : MajorPlatt.FareyDecomposition)
    (wa : MajorPlatt.WindowApproxUnder 1000 (1 / 2) (fun q => 10 ^ 8 / (q : ℝ)))
    (kt : MajorPlatt.KernelTailBound (1 / 10 ^ 5)) :
    MajorArcLower MajorPlatt.Pcut MajorPlatt.Qcut (1 / 2) :=
  MajorPlatt.majorArcLower_of_chain_platt grh fd wa kt singularSeriesLower_holds

/-- The spine, with the singular series supplied: **seven** hypotheses instead of eight.

**The `cW = 1000` in the `WindowApproxUnder` slot is UNPROVED and of UNKNOWN truth** — see the
retraction in this file's §4(b). It is NOT known false; the earlier claim that it was rested on an
invalid inference. `majorArcLower_of_chain_param` is the form that keeps `cW` a parameter. -/
theorem ternaryLogCountLower_of_platt_chain_ss (grh : PlattGRH)
    (fd : MajorPlatt.FareyDecomposition)
    (wa : MajorPlatt.WindowApproxUnder 1000 (1 / 2) (fun q => 10 ^ 8 / (q : ℝ)))
    (kt : MajorPlatt.KernelTailBound (1 / 10 ^ 5)) (cm : CircleMethodIdentity)
    (mn : MinorSupBound MajorPlatt.Pcut MajorPlatt.Qcut (3 / 10)) (pp : PrimePowerRemoval 10) :
    TernaryLogCountLower :=
  MajorPlatt.ternaryLogCountLower_of_platt_chain grh fd wa kt singularSeriesLower_holds cm mn pp

/-- **…and the EP1054 input, at seven hypotheses.** `Principia.Erdos1054.Cite_Helfgott_weighted` —
the last trusted input of the Erdős-1054 chain — now rests on `PlattGRH`, the Farey decomposition,
the window approximation, the kernel truncation, the circle-method identity, the minor-arc sup bound
and prime-power removal. The singular-series slot is gone.

**The `cW = 1000` in the `WindowApproxUnder` slot is UNPROVED and of UNKNOWN truth** — see the
retraction in this file's §4(b). It is NOT known false; the earlier claim that it was rested on an
invalid inference. `majorArcLower_of_chain_param` is the form that keeps `cW` a parameter. -/
theorem cite_Helfgott_weighted_of_platt_chain_ss (grh : PlattGRH)
    (fd : MajorPlatt.FareyDecomposition)
    (wa : MajorPlatt.WindowApproxUnder 1000 (1 / 2) (fun q => 10 ^ 8 / (q : ℝ)))
    (kt : MajorPlatt.KernelTailBound (1 / 10 ^ 5)) (cm : CircleMethodIdentity)
    (mn : MinorSupBound MajorPlatt.Pcut MajorPlatt.Qcut (3 / 10)) (pp : PrimePowerRemoval 10) :
    Principia.Erdos1054.Cite_Helfgott_weighted :=
  MajorPlatt.cite_Helfgott_weighted_of_platt_chain grh fd wa kt singularSeriesLower_holds cm mn pp

/-! ## Step 6 — the free-rider defect, exhibited and repaired

Two theorems, and between them they are the whole demonstration: the degenerate height at which the
chain needs **no** numerical input is exactly the height the guard refuses. -/

/-- **THE DEFECT, AS A THEOREM.** At `T = −1` the zero-box is empty, so the chain reaches
`MajorArcLower Pcut Qcut (1/2)` with **no numerical input anywhere in its signature** — no
`PlattGRH`, no `PlattGRHAt`, nothing. This is what "free rider" meant, and it is why
`MajorPlatt.majorArcLower_of_chain` now takes the *guarded* bundle
`MajorPlatt.PlattGRHAtLeast T` rather than a bare `PlattGRHAt T`. (Note the hypothesis this instance
pays instead: `WindowApproxUnder 1000 (1/2) (fun _ => −1)` is the *unconditional* window bound, the
strongest member of the family, by `MajorPlatt.windowApproxUnder_mono_height`. Nothing is got for
free; the point is that nothing is got from *Platt*.) -/
theorem majorArcLower_no_platt_at_vacuous_height (fd : MajorPlatt.FareyDecomposition)
    (wa : MajorPlatt.WindowApproxUnder 1000 (1 / 2) (fun _ => -1))
    (kt : MajorPlatt.KernelTailBound (1 / 10 ^ 5)) :
    MajorArcLower MajorPlatt.Pcut MajorPlatt.Qcut (1 / 2) :=
  MajorPlatt.majorArcLower_of_reassembly (by norm_num) singularSeriesLower_holds
    (MajorPlatt.majorReassembly_of_chain (by norm_num)
      (MajorPlatt.zeroBoxes_vacuous_of_neg (fun _ => by norm_num)) fd wa kt)

/-- **THE REPAIR, AS A THEOREM.** The height that discharges `PlattGRHAt` for free is refused by the
guard. So the free instance of the chain no longer exists: the unguarded slot was satisfiable at
`T = −1`, the guarded bundle is not, and by
`MajorPlatt.plattGRH_of_plattGRHAtLeast` every height the guard *does* admit carries `PlattGRH` and
hence a piece of the Riemann hypothesis. -/
theorem vacuous_height_is_refused :
    MajorPlatt.PlattGRHAt (fun _ => -1) ∧ ¬ MajorPlatt.PlattGRHAtLeast (fun _ => -1) :=
  ⟨MajorPlatt.plattGRHAt_vacuous_of_neg, MajorPlatt.plattGRHAtLeast_refuses_neg⟩

/-! ## Step 7 — the constant defect: a sharper slack, and a chain with no baked-in `cW`

`Spine.pp_slack` charges `errScale H = H^{3/2}(log H)²` as `H²/10⁴`, which caps `cW ≤ 1250` — and
`cW = 1250` asserts a relative major-arc error of `2.3·10⁻⁷`, five orders below what Helfgott's own
treatment achieves. So the cap, not the budget, is what makes `WindowApproxUnder 1000 (1/2) T`
unbelievable. The route to a sharper cap is a better `log H` bound: `pp_slack` goes through
`log H ≤ 8·H^{1/8}` (lossy by `380×` at the threshold), and two more square roots give
`log H ≤ 32·H^{1/32} = 223` against the true `62.17`. -/

/-- `48 ≤ H^{1/16}` for `H ≥ 10²⁷`, from `48¹⁶ = 7.94·10²⁶ ≤ 10²⁷`. The truth is `48.6968`, so the
`48` is essentially sharp and this is the step that fixes how much the sharper slack can buy. -/
theorem root16_ge (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    (48 : ℝ) ≤ Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt (H : ℝ)))) := by
  have hHR : (10 : ℝ) ^ 27 ≤ (H : ℝ) := by exact_mod_cast hH
  have h1 : (48 : ℝ) ^ 8 ≤ Real.sqrt (H : ℝ) := by
    refine sqrt_ge_of_sq_le (by positivity) ?_
    calc ((48 : ℝ) ^ 8) ^ 2 ≤ (10 : ℝ) ^ 27 := by norm_num
      _ ≤ (H : ℝ) := hHR
  have h2 : (48 : ℝ) ^ 4 ≤ Real.sqrt (Real.sqrt (H : ℝ)) := by
    refine sqrt_ge_of_sq_le (by positivity) ?_
    calc ((48 : ℝ) ^ 4) ^ 2 = (48 : ℝ) ^ 8 := by ring
      _ ≤ Real.sqrt (H : ℝ) := h1
  have h3 : (48 : ℝ) ^ 2 ≤ Real.sqrt (Real.sqrt (Real.sqrt (H : ℝ))) := by
    refine sqrt_ge_of_sq_le (by positivity) ?_
    calc ((48 : ℝ) ^ 2) ^ 2 = (48 : ℝ) ^ 4 := by ring
      _ ≤ Real.sqrt (Real.sqrt (H : ℝ)) := h2
  refine sqrt_ge_of_sq_le (by norm_num) ?_
  calc (48 : ℝ) ^ 2 = (48 : ℝ) ^ 2 := rfl
    _ ≤ Real.sqrt (Real.sqrt (Real.sqrt (H : ℝ))) := h3

set_option maxHeartbeats 800000 in
-- Five nested `Real.sqrt`s with five `Real.sq_sqrt` side conditions, then `norm_num` on `48⁷` and
-- on `(48⁸)²` against `10²⁷` (27-digit literals): the arithmetic is shallow but the terms are wide,
-- and the default 200000 heartbeats does not cover the root tower plus the two big-integer checks.
/-- **The sharper slack lemma: `errScale H ≤ H²/10⁸` for `H ≥ 10²⁷`** — four orders better than
`Spine.pp_slack`, so the budget admits `cW ≤ 1.25·10⁷` instead of `1250`. Route:
`log H = 32·log(H^{1/32}) ≤ 32·H^{1/32}`, hence `(log H)² ≤ 1024·H^{1/16}`, and
`1024·H^{1/16} ≤ H^{1/2}/10⁸` because `H^{1/16} ≥ 48` gives `(H^{1/16})⁷ ≥ 48⁷ = 5.87·10¹¹`, which
is `≥ 1.024·10¹¹`
— a margin of `5.73×`. `errScale H ≤ H²/10¹⁰` is **false** at the threshold
(`log²H = 3865 > 3.16·10³`), so `10⁹` is the hard ceiling of this scale and `10⁸` is one order
inside
it. -/
theorem errScale_le_sq_sharp (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    MajorPlatt.errScale H ≤ (H : ℝ) ^ 2 / 10 ^ 8 := by
  have hHR : (10 : ℝ) ^ 27 ≤ (H : ℝ) := by exact_mod_cast hH
  have hH0 : (0 : ℝ) < (H : ℝ) := by
    have : (0 : ℝ) < (10 : ℝ) ^ 27 := by positivity
    linarith
  have hexp : MajorPlatt.errScale H
      = (H : ℝ) * Real.sqrt (H : ℝ) * Real.log (H : ℝ) ^ 2 := rfl
  rw [hexp]
  set u1 : ℝ := Real.sqrt (H : ℝ) with hu1
  set u2 : ℝ := Real.sqrt u1 with hu2
  set u3 : ℝ := Real.sqrt u2 with hu3
  set u4 : ℝ := Real.sqrt u3 with hu4
  set u5 : ℝ := Real.sqrt u4 with hu5
  have e1 : u1 ^ 2 = (H : ℝ) := by rw [hu1]; exact Real.sq_sqrt hH0.le
  have e2 : u2 ^ 2 = u1 := by rw [hu2]; exact Real.sq_sqrt (by rw [hu1]; positivity)
  have e3 : u3 ^ 2 = u2 := by rw [hu3]; exact Real.sq_sqrt (by rw [hu2]; positivity)
  have e4 : u4 ^ 2 = u3 := by rw [hu4]; exact Real.sq_sqrt (by rw [hu3]; positivity)
  have e5 : u5 ^ 2 = u4 := by rw [hu5]; exact Real.sq_sqrt (by rw [hu4]; positivity)
  have hu4ge : (48 : ℝ) ≤ u4 := by rw [hu4, hu3, hu2, hu1]; exact root16_ge H hH
  have hu4pos : (0 : ℝ) < u4 := by linarith
  have hu5pos : (0 : ℝ) < u5 := by rw [hu5]; exact Real.sqrt_pos.mpr hu4pos
  have hu1nn : (0 : ℝ) ≤ u1 := by rw [hu1]; positivity
  have h32 : u5 ^ 32 = (H : ℝ) := by
    calc u5 ^ 32 = ((((u5 ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 := by ring
      _ = (((u4 ^ 2) ^ 2) ^ 2) ^ 2 := by rw [e5]
      _ = ((u3 ^ 2) ^ 2) ^ 2 := by rw [e4]
      _ = (u2 ^ 2) ^ 2 := by rw [e3]
      _ = u1 ^ 2 := by rw [e2]
      _ = (H : ℝ) := e1
  have hlogeq : Real.log (H : ℝ) = 32 * Real.log u5 := by
    rw [← h32, Real.log_pow]; norm_num
  have hlogu5 : Real.log u5 ≤ u5 - 1 := Real.log_le_sub_one_of_pos hu5pos
  have hlogub : Real.log (H : ℝ) ≤ 32 * u5 := by rw [hlogeq]; linarith
  have hlognn : (0 : ℝ) ≤ Real.log (H : ℝ) := by
    refine Real.log_nonneg ?_
    have : (1 : ℝ) ≤ (10 : ℝ) ^ 27 := by norm_num
    linarith
  have hsq : Real.log (H : ℝ) ^ 2 ≤ 1024 * u4 := by
    have h := mul_self_le_mul_self hlognn hlogub
    calc Real.log (H : ℝ) ^ 2 = Real.log (H : ℝ) * Real.log (H : ℝ) := by ring
      _ ≤ (32 * u5) * (32 * u5) := h
      _ = 1024 * u5 ^ 2 := by ring
      _ = 1024 * u4 := by rw [e5]
  have hu4pow : (1024 : ℝ) * 10 ^ 8 ≤ u4 ^ 7 := by
    calc (1024 : ℝ) * 10 ^ 8 ≤ (48 : ℝ) ^ 7 := by norm_num
      _ ≤ u4 ^ 7 := by gcongr
  have hu1eq : u1 = u4 ^ 8 := by
    calc u1 = u2 ^ 2 := e2.symm
      _ = (u3 ^ 2) ^ 2 := by rw [e3]
      _ = ((u4 ^ 2) ^ 2) ^ 2 := by rw [e4]
      _ = u4 ^ 8 := by ring
  have hkey : (1024 : ℝ) * u4 ≤ u1 / 10 ^ 8 := by
    rw [hu1eq, le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 8)]
    calc (1024 : ℝ) * u4 * 10 ^ 8 = u4 * ((1024 : ℝ) * 10 ^ 8) := by ring
      _ ≤ u4 * u4 ^ 7 := mul_le_mul_of_nonneg_left hu4pow hu4pos.le
      _ = u4 ^ 8 := by ring
  have hlogsq : Real.log (H : ℝ) ^ 2 ≤ u1 / 10 ^ 8 := le_trans hsq hkey
  calc (H : ℝ) * u1 * Real.log (H : ℝ) ^ 2
      ≤ (H : ℝ) * u1 * (u1 / 10 ^ 8) :=
        mul_le_mul_of_nonneg_left hlogsq (by positivity)
    _ = (H : ℝ) * (u1 ^ 2) / 10 ^ 8 := by ring
    _ = (H : ℝ) ^ 2 / 10 ^ 8 := by rw [e1]; ring

/-- **The reassembly with the slack SCALE as a parameter.**
`MajorPlatt.majorReassembly_of_chain` is this at `s = 10⁴` (`Spine.pp_slack`); the conversion is the
only thing that changes, and it was the thing capping `cW` four orders below anything believable. -/
theorem majorReassembly_of_chain_at {cW cK σ s : ℝ} {T : ℕ → ℝ} (hcW : 0 ≤ cW) (hs : 0 < s)
    (hslack : ∀ H : ℕ, 10 ^ 27 ≤ H → MajorPlatt.errScale H ≤ (H : ℝ) ^ 2 / s)
    (zb : MajorPlatt.ZeroBoxes T σ) (fd : MajorPlatt.FareyDecomposition)
    (wa : MajorPlatt.WindowApproxUnder cW σ T) (kt : MajorPlatt.KernelTailBound cK) :
    MajorPlatt.MajorReassembly (cW / s + cK) := by
  intro H hodd hH
  have hstep : ∀ q ∈ Finset.Icc 1 (MajorPlatt.Pcut H),
      ‖MajorPlatt.arcSum H q (MajorPlatt.Qcut H)
          - ((MajorPlatt.localTerm q H : ℝ) : ℂ) * (((H : ℝ) ^ 2 / 2 : ℝ) : ℂ)‖
        ≤ ‖MajorPlatt.arcSum H q (MajorPlatt.Qcut H)
              - ((MajorPlatt.localTerm q H : ℝ) : ℂ)
                  * MajorPlatt.kernelIntegral H q (MajorPlatt.Qcut H)‖
          + ‖((MajorPlatt.localTerm q H : ℝ) : ℂ)
              * (MajorPlatt.kernelIntegral H q (MajorPlatt.Qcut H)
                  - (((H : ℝ) ^ 2 / 2 : ℝ) : ℂ))‖ := by
    intro q _
    have hsplit : MajorPlatt.arcSum H q (MajorPlatt.Qcut H)
          - ((MajorPlatt.localTerm q H : ℝ) : ℂ) * (((H : ℝ) ^ 2 / 2 : ℝ) : ℂ)
        = (MajorPlatt.arcSum H q (MajorPlatt.Qcut H)
              - ((MajorPlatt.localTerm q H : ℝ) : ℂ)
                  * MajorPlatt.kernelIntegral H q (MajorPlatt.Qcut H))
          + ((MajorPlatt.localTerm q H : ℝ) : ℂ)
              * (MajorPlatt.kernelIntegral H q (MajorPlatt.Qcut H)
                  - (((H : ℝ) ^ 2 / 2 : ℝ) : ℂ)) := by ring
    rw [hsplit]
    exact norm_add_le _ _
  rw [fd H hH, MajorPlatt.ofReal_mainTerm, ← Finset.sum_sub_distrib]
  calc ‖∑ q ∈ Finset.Icc 1 (MajorPlatt.Pcut H),
          (MajorPlatt.arcSum H q (MajorPlatt.Qcut H)
            - ((MajorPlatt.localTerm q H : ℝ) : ℂ) * (((H : ℝ) ^ 2 / 2 : ℝ) : ℂ))‖
      ≤ ∑ q ∈ Finset.Icc 1 (MajorPlatt.Pcut H),
          ‖MajorPlatt.arcSum H q (MajorPlatt.Qcut H)
            - ((MajorPlatt.localTerm q H : ℝ) : ℂ) * (((H : ℝ) ^ 2 / 2 : ℝ) : ℂ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.Icc 1 (MajorPlatt.Pcut H),
          (‖MajorPlatt.arcSum H q (MajorPlatt.Qcut H)
              - ((MajorPlatt.localTerm q H : ℝ) : ℂ)
                  * MajorPlatt.kernelIntegral H q (MajorPlatt.Qcut H)‖
            + ‖((MajorPlatt.localTerm q H : ℝ) : ℂ)
                * (MajorPlatt.kernelIntegral H q (MajorPlatt.Qcut H)
                    - (((H : ℝ) ^ 2 / 2 : ℝ) : ℂ))‖) :=
        Finset.sum_le_sum hstep
    _ = (∑ q ∈ Finset.Icc 1 (MajorPlatt.Pcut H),
            ‖MajorPlatt.arcSum H q (MajorPlatt.Qcut H)
              - ((MajorPlatt.localTerm q H : ℝ) : ℂ)
                  * MajorPlatt.kernelIntegral H q (MajorPlatt.Qcut H)‖)
          + ∑ q ∈ Finset.Icc 1 (MajorPlatt.Pcut H),
              ‖((MajorPlatt.localTerm q H : ℝ) : ℂ)
                * (MajorPlatt.kernelIntegral H q (MajorPlatt.Qcut H)
                    - (((H : ℝ) ^ 2 / 2 : ℝ) : ℂ))‖ :=
        Finset.sum_add_distrib
    _ ≤ cW * MajorPlatt.errScale H + cK * (H : ℝ) ^ 2 :=
        add_le_add (wa zb H hodd hH) (kt H hodd hH)
    _ ≤ cW * ((H : ℝ) ^ 2 / s) + cK * (H : ℝ) ^ 2 := by
        have h3 : cW * MajorPlatt.errScale H ≤ cW * ((H : ℝ) ^ 2 / s) :=
          mul_le_mul_of_nonneg_left (hslack H hH) hcW
        linarith
    _ = (cW / s + cK) * (H : ℝ) ^ 2 := by field_simp

/-- **THE HEADLINE WITH NO BAKED-IN CONSTANT.** `MajorArcLower Pcut Qcut (1/2)` from the guarded
numerical input, the three open links at *arbitrary* `cW`, `cK`, and any slack lemma the reader can
supply, with the budget `1/2 + (cW/s + cK) ≤ 5/8` as a visible side condition. The singular-series
slot is discharged.

This is the parametric form of `MajorPlatt.majorArcLower_of_chain`, and it is worth having on
its own
merits: it puts `cW`, `cK` and the slack scale in the signature with the budget as a visible side
condition. **It is NOT a repair of a known-false constant** — see the retraction in §4(b): `cW
= 1000`
is five orders tighter than the tolerance Helfgott's analysis budgets for, which says nothing about
whether it is true. Widening the reachable range is still useful, because it means the chain
does not
depend on the tight constant being the one that holds. Instantiations: `s = 10⁴`
(`Spine.pp_slack`) admits `cW ≤ 1250`; `s = 10⁸`
(`errScale_le_sq_sharp`) admits `cW ≤ 1.25·10⁷`; `s = 10⁹` is the hard ceiling of the
`H^{3/2}(log H)²` scale and admits `cW ≤ 1.25·10⁸`, i.e. `2.3 %` relative error, which is where
Helfgott's `3.06 %` lives. -/
theorem majorArcLower_of_chain_param {cW cK s : ℝ} {T : ℕ → ℝ} (hcW : 0 ≤ cW) (hs : 0 < s)
    (hslack : ∀ H : ℕ, 10 ^ 27 ≤ H → MajorPlatt.errScale H ≤ (H : ℝ) ^ 2 / s)
    (hbudget : 1 / 2 + (cW / s + cK) ≤ (5 / 4) / 2)
    (grh : MajorPlatt.PlattGRHAtLeast T) (fd : MajorPlatt.FareyDecomposition)
    (wa : MajorPlatt.WindowApproxUnder cW (1 / 2) T) (kt : MajorPlatt.KernelTailBound cK) :
    MajorArcLower MajorPlatt.Pcut MajorPlatt.Qcut (1 / 2) :=
  MajorPlatt.majorArcLower_of_reassembly hbudget singularSeriesLower_holds
    (majorReassembly_of_chain_at hcW hs hslack
      (MajorPlatt.zeroBoxes_of_plattGRHAt grh.2) fd wa kt)

/-- The parametric chain at the sharper scale, with the ceiling `cW ≤ 1.25·10⁷` instantiated at a
round `10⁷` and `cK = 10⁻⁵`: `1/2 + (10⁷/10⁸ + 10⁻⁵) = 0.60001 ≤ 0.625`. Ten thousand times the
constant `MajorPlatt.majorArcLower_of_chain` quotes, and still inside the budget — which is the
measurement: the `1000` was never the budget's doing. -/
theorem majorArcLower_of_chain_sharp {T : ℕ → ℝ} (grh : MajorPlatt.PlattGRHAtLeast T)
    (fd : MajorPlatt.FareyDecomposition)
    (wa : MajorPlatt.WindowApproxUnder (10 ^ 7) (1 / 2) T)
    (kt : MajorPlatt.KernelTailBound (1 / 10 ^ 5)) :
    MajorArcLower MajorPlatt.Pcut MajorPlatt.Qcut (1 / 2) :=
  majorArcLower_of_chain_param (by norm_num) (by norm_num) errScale_le_sq_sharp (by norm_num)
    grh fd wa kt

end Principia.Common.TernaryGoldbach.SingularBridge
