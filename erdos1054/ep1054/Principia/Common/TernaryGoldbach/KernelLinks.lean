/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.FareyKernel
import Principia.Common.TernaryGoldbach.SingularBridge
import Principia.Common.TernaryGoldbach.CircleMethod
import Principia.Common.TernaryGoldbach.PrimePower
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

/-!
# Discharging the kernel-tail obligations K1, K2 — and where K3 blocks

`FareyKernel.kernelTailBound_std` reduces `MajorPlatt.KernelTailBound (1/10⁵)` to three named
obligations. **Two of them are theorems here, with no hypotheses:**

* `k1_holds : FareyKernel.FullCircleTriple` — orthogonality. `∫₀¹ U(β)³e(−Hβ) dβ` counts the
  ordered triples from `[1,H]` summing to `H`, and that count is `(H−1)(H−2)/2`.
* `k2_holds : FareyKernel.WindowTailGeom (1/8)` — the geometric truncation tail.

**K3 is not discharged, and the blocking step is named and isolated:** `k3_of_totSq` proves
`TotientSqSum cL → FareyKernel.LocalTermWeightSum cL`, so what is left of K3 is the single
`H`-free finite arithmetic statement

  `TotientSqSum (10⁶) : ∑_{q ≤ 3·10⁵} μ(q)²q²/φ(q)² ≤ 10⁶`.

`KernelTailBound (1/10⁵)` therefore becomes `kernelTailBound_holds`, carrying **one** hypothesis
instead of three, and the recomposed chain `chain_of_totSq` carries **four** (`grh`, `wa`, `mn`,
`ts`) where `FareyKernel.cite_Helfgott_weighted_of_kernel_links` carries nine.

## The numbers, every one recomputed in this session

All figures below come from `k3_numbers.py` (linear sieve for `φ` and the squarefree flag over
`q ≤ 3·10⁵`, plus an exact integer bracket at scale `10⁹` for the one that matters); the figures in
the K3 section below come from `k3_route.py`. Nothing is carried over from a previous round's note.

| quantity | value |
|---|---|
| `∑_{q ≤ 3·10⁵ squarefree} (q/φ(q))²` | `583116.3063`; bracket `[583116.30619, 583116.30638]` |
| `∑_{q ≤ 3·10⁵} (q/φ(q))²` (all `q`) | `1329254.405` |
| `∑_{q ≤ 3·10⁵ squarefree} (q/φ(q))³` | `1329521.457`, so `/8 = 1.66190·10⁵` |
| `max_{q ≤ 3·10⁵} q/φ(q)` | `5.2135` at `q = 270270` |
| chargeable loss, sharp weight | `5.0618·10⁻⁸·H²`, inside `cK = 10⁻⁵` by `197.6×` |
| chargeable loss, loose weight | `1.1541·10⁻⁷·H²`, inside by `86.65×` |
| the Lean chain's own crude total | `1.25·10⁻⁷·H²`, inside by `80×` |

Nine figures of `FareyKernel`'s Link-M3 section were recomputed and all nine agree: `583116.306`,
the bracket, `max q/φ(q) = 5.2135` at `270270`, `5.06·10⁻⁸`, `197.6×`, `1.6619·10⁵` `(= C/8)`,
`7.289·10⁴` `(= A/8)`, the `2.28` weight factor `(= 1329521.457/583116.306 = 2.28003)`, and
`1.15·10⁻⁷` for the loose weight. **One figure there was NOT recomputed and is not endorsed here:**
the `5.11·10⁻¹¹·H²` / `1.96·10⁵×` pair for "the true `H`-dependent Ramanujan weight at
`H = 10²⁷+1`". It plays no part in anything below — `LocalTermWeightSum` uses the `H`-uniform
weight — so it was left alone rather than half-checked.

## THE ROUTE `FareyKernel` RECOMMENDS FOR K3 CANNOT PROVE K3 — a correction

`FareyKernel.LocalTermWeightSum`'s docstring names a route and calls it "the route that works, and
is the one a front should be handed": the divisor identity `q²/φ(q)² = ∑_{d ∣ q} h(d)` with
`h(p) = (2p−1)/(p−1)²`, giving `∑_{q≤P} q²/φ(q)² ≤ P·∏_p(1 + h(p)/p) = 4.4311·P`.

The identity is right and the constant is right — recomputed here, `∏_p(1 + h(p)/p) = 4.4310756`,
and `P·4.4310756 = 1329322.7` against the directly summed all-`q` value `1329254.4`, agreeing to
`0.0051 %`. **But the bound it delivers is `1.3293·10⁶`, which EXCEEDS `cL = 10⁶` by `1.33×`.**
The reason is structural, not a matter of sharpening a constant: that route bounds
`#{q ≤ P : d ∣ q}` by `P/d` and so discards the squarefree restriction on `q`, and
`∑_{q≤P}(q/φ(q))²` over **all** `q` is already `1329254.4 > 10⁶` — `10⁶/1329254.4 = 0.752`. No
estimate that drops squarefreeness can reach `10⁶`, whatever its constants.

So K3 needs the squarefree **density**, quantitatively. The route that does close, worked out and
checked numerically in `k3_route.py` but **not** formalized: keep the divisor identity but restrict
`h` to squarefree arguments, so that

  `∑_{q≤P} μ(q)²q²/φ(q)² = ∑_{d≤P} h(d)·#{q ≤ P : d ∣ q, q squarefree}`

**exactly** — checked to a relative `4.7·10⁻¹⁴`, i.e. to floating point, which is a far stronger
check that the identity is the right one than the `0.005 %` agreement of the majorant above. Then
bound `#{q ≤ P : d ∣ q, q squarefree} ≤ Q(P/d)` with `Q` the squarefree counting function and
`Q(x) ≤ (2/3)x + 2` (inclusion–exclusion on `p = 2, 3`: `1 − 1/4 − 1/9 + 1/36 = 2/3`, and each
floor costs at most `1`). Since `∑_{d≤3·10⁵} h(d)/d = 4.4310219` and `∑_{d≤3·10⁵} h(d) = 120.21`,
that gives `(2/3)·4.4310219·P + 2·120.21 = 8.8644·10⁵ ≤ 10⁶`, **leaving `11.4 %` of the budget
unused** — the `+2` error term costs `240`, which is nothing. (`Q(x) ≤ (3/4)x + 1`, from `p = 2`
alone, gives `9.9710·10⁵`: under `10⁶` by `0.3 %`, which is not a margin anyone should build on.)

In Lean that is a multiplicative-function convolution, a divisor swap, a squarefree-count bound and
an Euler product over the primes `≤ 3·10⁵` that has to be evaluated to `11 %`. The first two are
routine; the Euler product is the work, because it needs the small primes as explicit rationals with
`1 + x ≤ exp x` used only on the tail. The crude one-step `exp(∑_p h(p)/p) = exp(2.1482) = 8.5696`
is `1.93×` the true `4.4311`, and `(2/3)·8.5696·P = 1.714·10⁶` overshoots `10⁶` by `1.71×`. That is
what K3 is waiting on, and it is a day of Lean, not a paragraph.

## What is NOT claimed

Nothing here proves any part of ternary Goldbach. `TotientSqSum` is a `def … : Prop` and is
unproved; `chain_of_totSq` carries it together with `PlattGRH`, `WindowApproxUnder` and
`MinorSupBound`. K1 and K2 are proved outright and in the form the chain charges — neither
`FareyKernel.FullCircleTriple` nor `FareyKernel.WindowTailGeom (1/8)` is restated or weakened here.
-/

namespace Principia.Common.TernaryGoldbach.KernelLinks

open MeasureTheory Principia.Common.Goldbach
open Principia.Common.TernaryGoldbach.Spine
open Principia.Common.TernaryGoldbach.MajorPlatt
open Principia.Common.TernaryGoldbach.FareyKernel

/-! ## Continuity and periodicity of the model integrand -/

theorem cont_ps (H : ℕ) : Continuous (plainSum H) := by
  unfold plainSum
  exact continuous_finsetSum _ (fun n _ => continuous_e.comp (by fun_prop))

theorem cont_mk (H : ℕ) : Continuous (modelKernel H) := by
  unfold modelKernel
  exact ((cont_ps H).pow 3).mul (continuous_e.comp (by fun_prop))

/-- `U(β)³e(−Hβ)` is `1`-periodic — every frequency in it is an integer. This is what lets the
period of the whole-circle integral be moved onto the window in `k2_holds`. -/
theorem mk_periodic (H : ℕ) : Function.Periodic (modelKernel H) 1 := by
  intro β
  have hp : plainSum H (β + 1) = plainSum H β := by
    unfold plainSum
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show (n : ℝ) * (β + 1) = (n : ℝ) * β + (n : ℝ) by ring, ← e_add,
      e_natCast_eq_one, mul_one]
  have he : e (-(H : ℝ) * (β + 1)) = e (-(H : ℝ) * β) := by
    rw [show -(H : ℝ) * (β + 1) = -(H : ℝ) * β + -(H : ℝ) by ring, ← e_add,
      e_negNatCast_eq_one, mul_one]
  simp only [modelKernel, hp, he]

/-! ## K1 — orthogonality

Three moves and one count. The cube expands into a triple sum whose `(a,b,c)` term is
`e((a+b+c−H)β)`; `Goldbach.MinorArc.integral_e` integrates each term to `[a+b+c = H]`; and the
resulting count of ordered triples from `[1,H]` summing to `H` is `(H−1)(H−2)/2`. The count is
done in `ℕ` and cast once, because the identity `2·#triples = (H−1)(H−2)` is false in `ℕ` at
`H = 0` and true from `H = 1` on — `FareyKernel.FullCircleTriple` carries `0 < H` for exactly this
reason. -/

/-- The cube, expanded. Every frequency is an integer, which is the only property used. -/
theorem mk_triple (H : ℕ) (β : ℝ) :
    modelKernel H β
      = ∑ a ∈ Finset.Ioc 0 H, ∑ b ∈ Finset.Ioc 0 H, ∑ c ∈ Finset.Ioc 0 H,
          e ((((a : ℤ) + b + c - (H : ℤ) : ℤ) : ℝ) * β) := by
  simp only [modelKernel, plainSum, pow_three, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  rw [e_add, e_add, e_add]
  congr 1
  push_cast
  ring

/-- The innermost sum: for fixed `a, b` exactly one `c ∈ [1,H]` closes `a+b+c = H`, and it exists
iff `a + b < H` (`c ≤ H` is then automatic). -/
theorem sum_inner (H a b : ℕ) :
    (∑ c ∈ Finset.Ioc 0 H, (if a + b + c = H then (1 : ℂ) else 0))
      = if a + b < H then 1 else 0 := by
  by_cases hab : a + b < H
  · have hmem : H - a - b ∈ Finset.Ioc 0 H := by
      simp only [Finset.mem_Ioc]; omega
    have hzero : ∀ c ∈ Finset.Ioc 0 H, c ≠ H - a - b →
        (if a + b + c = H then (1 : ℂ) else 0) = 0 := by
      intro c hc hne
      simp only [Finset.mem_Ioc] at hc
      exact if_neg (by omega)
    rw [Finset.sum_eq_single_of_mem (H - a - b) hmem hzero, if_pos (by omega), if_pos hab]
  · rw [if_neg hab]
    refine Finset.sum_eq_zero ?_
    intro c hc
    simp only [Finset.mem_Ioc] at hc
    exact if_neg (by omega)

/-- The middle sum: `#{b ∈ [1,H] : a + b < H} = H − a − 1`. -/
theorem sum_mid (H a : ℕ) :
    (∑ b ∈ Finset.Ioc 0 H, (if a + b < H then (1 : ℂ) else 0)) = ((H - a - 1 : ℕ) : ℂ) := by
  have hfil : Finset.filter (fun b => a + b < H) (Finset.Ioc 0 H) = Finset.Ioc 0 (H - a - 1) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    omega
  rw [Finset.sum_boole, hfil, Nat.card_Ioc, Nat.sub_zero]

/-- The outer sum, reindexed `a ↦ H − a`. -/
theorem sum_reidx (H : ℕ) :
    ∑ a ∈ Finset.Ioc 0 H, (H - a - 1) = ∑ k ∈ Finset.range H, (k - 1) := by
  refine Finset.sum_nbij' (i := fun a => H - a) (j := fun k => H - k) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp only [Finset.mem_Ioc] at ha; simp only [Finset.mem_range]; omega
  · intro k hk; simp only [Finset.mem_range] at hk; simp only [Finset.mem_Ioc]; omega
  · intro a ha; simp only [Finset.mem_Ioc] at ha; omega
  · intro k hk; simp only [Finset.mem_range] at hk; omega
  · intro a ha; simp only [Finset.mem_Ioc] at ha; omega

theorem sum_pred (n : ℕ) : ∑ k ∈ Finset.range n, (k - 1) = ∑ j ∈ Finset.range (n - 1), j := by
  rcases n with _ | m
  · simp
  · rw [Finset.sum_range_succ']
    simp

/-- **The triple count, in `ℕ`.** `2·#{(a,b,c) ∈ [1,H]³ : a+b+c = H} = (H−1)(H−2)`, the Gauss sum
after the reindexing. Stated doubled so no division appears in `ℕ`. -/
theorem two_mul_cnt (H : ℕ) :
    2 * (∑ a ∈ Finset.Ioc 0 H, (H - a - 1)) = (H - 1) * (H - 2) := by
  rw [sum_reidx, sum_pred]
  have h := Finset.sum_range_id_mul_two (H - 1)
  have hsub : H - 1 - 1 = H - 2 := by omega
  rw [hsub] at h
  rw [← h]
  ring

/-- The same count against `FareyKernel.tripleCount`, over `ℝ`. `H = 1` is separated out because
`((H−1 : ℕ) : ℝ) = (H : ℝ) − 1` needs `1 ≤ H` and the `H−2` cast needs `2 ≤ H`. -/
theorem cnt_eq (H : ℕ) (hH : 0 < H) :
    ((∑ a ∈ Finset.Ioc 0 H, (H - a - 1) : ℕ) : ℝ) = tripleCount H := by
  rcases Nat.lt_or_ge H 2 with h2 | h2
  · have hH1 : H = 1 := by omega
    subst hH1
    simp [tripleCount]
  · set S : ℕ := ∑ a ∈ Finset.Ioc 0 H, (H - a - 1) with hS
    have h : 2 * S = (H - 1) * (H - 2) := two_mul_cnt H
    have h1 : ((2 * S : ℕ) : ℝ) = (((H - 1) * (H - 2) : ℕ) : ℝ) := by rw [h]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ H),
      Nat.cast_sub (by omega : 2 ≤ H)] at h1
    norm_num at h1
    rw [tripleCount]
    linear_combination h1 / 2

/-- The whole-circle integral, evaluated. Every frequency is an integer, so `integral_e` turns the
triple sum into the count. -/
theorem int_full (H : ℕ) :
    (∫ β in (0 : ℝ)..1, modelKernel H β)
      = ((∑ a ∈ Finset.Ioc 0 H, (H - a - 1) : ℕ) : ℂ) := by
  have hint1 : ∀ a b c : ℕ, IntervalIntegrable
      (fun β : ℝ => e ((((a : ℤ) + b + c - (H : ℤ) : ℤ) : ℝ) * β)) volume 0 1 := by
    intro a b c
    exact (continuous_e.comp (by fun_prop)).intervalIntegrable 0 1
  have hint2 : ∀ a b : ℕ, IntervalIntegrable
      (fun β : ℝ => ∑ c ∈ Finset.Ioc 0 H,
        e ((((a : ℤ) + b + c - (H : ℤ) : ℤ) : ℝ) * β)) volume 0 1 := by
    intro a b
    exact (continuous_finsetSum _
      (fun c _ => continuous_e.comp (by fun_prop))).intervalIntegrable 0 1
  have hint3 : ∀ a : ℕ, IntervalIntegrable
      (fun β : ℝ => ∑ b ∈ Finset.Ioc 0 H, ∑ c ∈ Finset.Ioc 0 H,
        e ((((a : ℤ) + b + c - (H : ℤ) : ℤ) : ℝ) * β)) volume 0 1 := by
    intro a
    exact (continuous_finsetSum _ (fun b _ => continuous_finsetSum _
      (fun c _ => continuous_e.comp (by fun_prop)))).intervalIntegrable 0 1
  have hinner : ∀ a ∈ Finset.Ioc 0 H,
      (∫ β in (0 : ℝ)..1, ∑ b ∈ Finset.Ioc 0 H, ∑ c ∈ Finset.Ioc 0 H,
        e ((((a : ℤ) + b + c - (H : ℤ) : ℤ) : ℝ) * β))
      = ((H - a - 1 : ℕ) : ℂ) := by
    intro a _
    rw [intervalIntegral.integral_finsetSum (fun b _ => hint2 a b)]
    have hb : ∀ b ∈ Finset.Ioc 0 H,
        (∫ β in (0 : ℝ)..1, ∑ c ∈ Finset.Ioc 0 H,
          e ((((a : ℤ) + b + c - (H : ℤ) : ℤ) : ℝ) * β))
        = (if a + b < H then (1 : ℂ) else 0) := by
      intro b _
      rw [intervalIntegral.integral_finsetSum (fun c _ => hint1 a b c)]
      have hc : ∀ c ∈ Finset.Ioc 0 H,
          (∫ β in (0 : ℝ)..1, e ((((a : ℤ) + b + c - (H : ℤ) : ℤ) : ℝ) * β))
          = (if a + b + c = H then (1 : ℂ) else 0) := by
        intro c _
        rw [MinorArc.integral_e ((a : ℤ) + b + c - (H : ℤ))]
        by_cases h : a + b + c = H
        · rw [if_pos (by omega : (a : ℤ) + b + c - (H : ℤ) = 0), if_pos h]
        · rw [if_neg (by omega : ¬((a : ℤ) + b + c - (H : ℤ) = 0)), if_neg h]
      rw [Finset.sum_congr rfl hc, sum_inner H a b]
    rw [Finset.sum_congr rfl hb, sum_mid H a]
  rw [intervalIntegral.integral_congr (fun β _ => mk_triple H β),
    intervalIntegral.integral_finsetSum (fun a _ => hint3 a),
    Finset.sum_congr rfl hinner, ← Nat.cast_sum]

/-- **OBLIGATION K1, DISCHARGED.** `FareyKernel.FullCircleTriple` with no hypotheses. -/
theorem k1_holds : FullCircleTriple := by
  intro H hH
  rw [← intervalIntegral.integral_of_le (zero_le_one' ℝ), int_full H, ← cnt_eq H hH]
  norm_cast

/-! ## K2 — the geometric truncation tail

The window `|β| ≤ w = 1/(q(Q+1))` is one period cut down, so the loss is `∫_{w}^{1−w}` of the same
`1`-periodic integrand. There `|U(β)| ≤ 1/(2‖β‖)` with `‖β‖ = min(β, 1−β)`, hence
`|U³| ≤ 1/(8β³) + 1/(8(1−β)³)` — a majorant whose two halves have the *same* integral over
`[w, 1−w]` (substitute `β ↦ 1−β`; the interval is symmetric), so one antiderivative does the whole
job and the total is `1/(8w²) − 1/(8(1−w)²) = q²(Q+1)²/8 − 1/(8(1−w)²)`. The charged `cT = 1/8` is
met with that second term to spare; `0 < q`, `0 < Q` enter exactly once, to give `w ≤ 1/2`. -/

/-- `dist(β, ℤ) ≥ min(β, 1−β)` on `(0,1)`, in the form `exp_sum_Ioc_min_bound` can be composed
with: every integer is at least `min(β, 1−β)` away. -/
theorem dist_int_ge {β : ℝ} (h0 : 0 < β) (h1 : β < 1) (k : ℤ) :
    min β (1 - β) ≤ |β - (k : ℝ)| := by
  rcases le_or_gt k 0 with hk | hk
  · have hkr : (k : ℝ) ≤ 0 := by exact_mod_cast hk
    rw [abs_of_nonneg (by linarith)]
    have := min_le_left β (1 - β)
    linarith
  · have hkr : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    rw [abs_of_nonpos (by linarith), neg_sub]
    have := min_le_right β (1 - β)
    linarith

/-- `|U(β)| ≤ 1/(2 min(β, 1−β))` on `(0,1)`. The library side is
`Goldbach.MinSum.exp_sum_Ioc_min_bound`; the `β ∈ ℤ` branch is excluded by `0 < β < 1`. -/
theorem ps_bound (H : ℕ) {β : ℝ} (h0 : 0 < β) (h1 : β < 1) :
    ‖plainSum H β‖ ≤ 1 / (2 * min β (1 - β)) := by
  have hmin : 0 < min β (1 - β) := lt_min h0 (by linarith)
  have hne : β - round β ≠ 0 := by
    intro hc
    have h0' : (0 : ℝ) < ((round β : ℤ) : ℝ) := by linarith
    have h1' : ((round β : ℤ) : ℝ) < 1 := by linarith
    have hk0 : (0 : ℤ) < round β := by exact_mod_cast h0'
    have hk1 : (round β : ℤ) < 1 := by exact_mod_cast h1'
    omega
  have hb := MinSum.exp_sum_Ioc_min_bound β H
  rw [if_neg hne] at hb
  have hd : min β (1 - β) ≤ |β - (round β : ℝ)| := dist_int_ge h0 h1 (round β)
  have hstep : (1 : ℝ) / (2 * |β - round β|) ≤ 1 / (2 * min β (1 - β)) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have hps : ‖plainSum H β‖ ≤ 1 / (2 * |β - round β|) :=
    le_trans hb (min_le_right _ _)
  linarith

theorem norm_mk (H : ℕ) (β : ℝ) : ‖modelKernel H β‖ = ‖plainSum H β‖ ^ 3 := by
  rw [modelKernel, norm_mul, norm_pow, e_norm, mul_one]

/-- The majorant of `‖U(β)³e(−Hβ)‖` on `(0,1)`. Written as a *sum* of the two one-sided cubes
rather than `1/(8‖β‖³)` because the sum is what integrates in closed form on a symmetric
interval — and it is a majorant of `1/(8‖β‖³)` for free, since whichever of `β`, `1−β` is the
minimum contributes its own term and the other is positive. -/
noncomputable def maj (β : ℝ) : ℝ := 1 / (8 * β ^ 3) + 1 / (8 * (1 - β) ^ 3)

theorem mk_le_maj (H : ℕ) {β : ℝ} (h0 : 0 < β) (h1 : β < 1) :
    ‖modelKernel H β‖ ≤ maj β := by
  have hmin : 0 < min β (1 - β) := lt_min h0 (by linarith)
  have hb : (0 : ℝ) < 1 - β := by linarith
  have hps := ps_bound H h0 h1
  have hcube : ‖plainSum H β‖ ^ 3 ≤ (1 / (2 * min β (1 - β))) ^ 3 := by
    have hnn : (0 : ℝ) ≤ ‖plainSum H β‖ := norm_nonneg _
    nlinarith [hps, hnn, sq_nonneg (‖plainSum H β‖ + 1 / (2 * min β (1 - β))),
      sq_nonneg (‖plainSum H β‖ - 1 / (2 * min β (1 - β)))]
  rw [norm_mk]
  refine le_trans hcube ?_
  rcases le_total β (1 - β) with hle | hle
  · rw [min_eq_left hle]
    have heq : (1 / (2 * β)) ^ 3 = 1 / (8 * β ^ 3) := by
      rw [div_pow, one_pow, mul_pow]
      norm_num
    have h2 : (0 : ℝ) < 1 / (8 * (1 - β) ^ 3) := by positivity
    rw [maj, heq]
    linarith
  · rw [min_eq_right hle]
    have heq : (1 / (2 * (1 - β))) ^ 3 = 1 / (8 * (1 - β) ^ 3) := by
      rw [div_pow, one_pow, mul_pow]
      norm_num
    have h2 : (0 : ℝ) < 1 / (8 * β ^ 3) := by positivity
    rw [maj, heq]
    linarith

theorem ii_cube {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    IntervalIntegrable (fun β : ℝ => 1 / (8 * β ^ 3)) volume u v := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le huv]
  refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
  intro x hx
  simp only [Set.mem_Icc] at hx
  have hx0 : 0 < x := lt_of_lt_of_le hu hx.1
  positivity

theorem ii_cube' {u : ℝ} (hu : 0 < u) (huv : u ≤ 1 - u) :
    IntervalIntegrable (fun β : ℝ => 1 / (8 * (1 - β) ^ 3)) volume u (1 - u) := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le huv]
  refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
  intro x hx
  simp only [Set.mem_Icc] at hx
  have hx0 : 0 < 1 - x := by linarith [hx.2]
  positivity

/-- `∫_u^v dβ/(8β³) = 1/(16u²) − 1/(16v²)`. The one antiderivative the tail needs. -/
theorem int_cube {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    (∫ β in u..v, 1 / (8 * β ^ 3)) = 1 / (16 * u ^ 2) - 1 / (16 * v ^ 2) := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have h0 : (0 : ℝ) ∉ Set.uIcc u v := by
    rw [Set.uIcc_of_le huv]
    simp only [Set.mem_Icc, not_and, not_le]
    intro hc
    linarith
  have hcong : Set.EqOn (fun β : ℝ => 1 / (8 * β ^ 3))
      (fun β : ℝ => (1 / 8 : ℝ) * β ^ (-3 : ℤ)) (Set.uIcc u v) := by
    intro β hβ
    have hβ0 : β ≠ 0 := fun hc => h0 (hc ▸ hβ)
    have hz : β ^ (-3 : ℤ) = 1 / β ^ 3 := by
      rw [zpow_neg, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) from by norm_num, zpow_natCast, one_div]
    simp only [hz]
    field_simp
  rw [intervalIntegral.integral_congr hcong, intervalIntegral.integral_const_mul,
    integral_zpow (Or.inr ⟨by norm_num, h0⟩)]
  have hu0 : u ≠ 0 := ne_of_gt hu
  have hv0 : v ≠ 0 := ne_of_gt hv
  have he : (-3 : ℤ) + 1 = -2 := by norm_num
  rw [he]
  have hzu : u ^ (-2 : ℤ) = 1 / u ^ 2 := by
    rw [zpow_neg, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from by norm_num, zpow_natCast, one_div]
  have hzv : v ^ (-2 : ℤ) = 1 / v ^ 2 := by
    rw [zpow_neg, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from by norm_num, zpow_natCast, one_div]
  rw [hzu, hzv]
  norm_num
  field_simp
  ring

/-- `∫_w^{1−w} maj = 1/(8w²) − 1/(8(1−w)²)`. The second half of the majorant has the same
integral as the first, because `β ↦ 1−β` maps `[w, 1−w]` onto itself. -/
theorem int_maj {u : ℝ} (hu : 0 < u) (huv : u ≤ 1 - u) :
    (∫ β in u..(1 - u), maj β) = 1 / (8 * u ^ 2) - 1 / (8 * (1 - u) ^ 2) := by
  have hb : 0 < 1 - u := lt_of_lt_of_le hu huv
  have hsplit : (∫ β in u..(1 - u), maj β)
      = (∫ β in u..(1 - u), 1 / (8 * β ^ 3)) + ∫ β in u..(1 - u), 1 / (8 * (1 - β) ^ 3) := by
    simp only [maj]
    exact intervalIntegral.integral_add (ii_cube hu huv) (ii_cube' hu huv)
  have hsecond : (∫ β in u..(1 - u), 1 / (8 * (1 - β) ^ 3))
      = ∫ β in u..(1 - u), 1 / (8 * β ^ 3) := by
    have h := intervalIntegral.integral_comp_sub_left (a := u) (b := 1 - u)
      (f := fun x : ℝ => 1 / (8 * x ^ 3)) 1
    simp only [show (1 : ℝ) - (1 - u) = u from by ring] at h
    exact h
  rw [hsplit, hsecond, int_cube hu huv]
  have h1 : (1 : ℝ) - u ≠ 0 := ne_of_gt hb
  have h2 : u ≠ 0 := ne_of_gt hu
  field_simp
  ring

/-- `w = 1/(q(Q+1)) ≤ 1/2` as soon as `0 < q` and `0 < Q` — the one place the two hypotheses of
`FareyKernel.WindowTailGeom` are spent, and what stops the "window" being wider than a period. -/
theorem hw_half {q Q : ℕ} (hq : 0 < q) (hQ : 0 < Q) :
    halfWidth q Q ≤ 1 - halfWidth q Q := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hprod : (2 : ℝ) ≤ (q : ℝ) * ((Q : ℝ) + 1) := by nlinarith
  have hw : halfWidth q Q = 1 / ((q : ℝ) * ((Q : ℝ) + 1)) := rfl
  have hle : (1 : ℝ) / ((q : ℝ) * ((Q : ℝ) + 1)) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hprod
  rw [hw]
  linarith

/-- **OBLIGATION K2, DISCHARGED.** `FareyKernel.WindowTailGeom (1/8)` with no hypotheses. -/
theorem k2_holds : WindowTailGeom (1 / 8) := by
  intro H q Q hq hQ
  have hw0 : 0 < halfWidth q Q := halfWidth_pos hq
  have hwh : halfWidth q Q ≤ 1 - halfWidth q Q := hw_half hq hQ
  have hneg : -halfWidth q Q ≤ halfWidth q Q := by linarith
  set w : ℝ := halfWidth q Q with hwdef
  have hi1 : IntervalIntegrable (modelKernel H) volume (-w) w :=
    (cont_mk H).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (modelKernel H) volume w (1 - w) :=
    (cont_mk H).intervalIntegrable _ _
  -- move the period onto the window and split off the tail
  have e1 : (∫ β in Set.Ioc (0 : ℝ) 1, modelKernel H β)
      = ∫ β in (0 : ℝ)..(0 + 1), modelKernel H β := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 0 + 1)]
    norm_num
  have e2 : (∫ β in (0 : ℝ)..(0 + 1), modelKernel H β)
      = ∫ β in (-w)..(-w + 1), modelKernel H β :=
    (mk_periodic H).intervalIntegral_add_eq 0 (-w)
  have e3 : (∫ β in (-w)..(-w + 1), modelKernel H β)
      = (∫ β in (-w)..w, modelKernel H β) + ∫ β in w..(1 - w), modelKernel H β := by
    rw [show -w + 1 = 1 - w from by ring]
    exact (intervalIntegral.integral_add_adjacent_intervals hi1 hi2).symm
  have e4 : (∫ β in (-w)..w, modelKernel H β) = kernelIntegral H q Q := by
    rw [kernelIntegral_eq, ← hwdef, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hneg]
  have hsplit : (∫ β in Set.Ioc (0 : ℝ) 1, modelKernel H β) - kernelIntegral H q Q
      = ∫ β in w..(1 - w), modelKernel H β := by
    rw [e1, e2, e3, e4]; ring
  rw [hsplit]
  -- bound the tail by the majorant and integrate it
  have hnorm : ‖∫ β in w..(1 - w), modelKernel H β‖ ≤ ∫ β in w..(1 - w), ‖modelKernel H β‖ :=
    intervalIntegral.norm_integral_le_integral_norm hwh
  have hin : IntervalIntegrable (fun β => ‖modelKernel H β‖) volume w (1 - w) :=
    ((cont_mk H).norm).intervalIntegrable _ _
  have himaj : IntervalIntegrable maj volume w (1 - w) :=
    (ii_cube hw0 hwh).add (ii_cube' hw0 hwh)
  have hmono : (∫ β in w..(1 - w), ‖modelKernel H β‖) ≤ ∫ β in w..(1 - w), maj β := by
    refine intervalIntegral.integral_mono_on hwh hin himaj ?_
    intro x hx
    simp only [Set.mem_Icc] at hx
    exact mk_le_maj H (lt_of_lt_of_le hw0 hx.1) (by linarith [hx.2])
  have hval := int_maj hw0 hwh
  -- `1/(8w²)` is exactly the charged `q²(Q+1)²/8`
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hQr : (0 : ℝ) < (Q : ℝ) + 1 := by positivity
  have hkey : 1 / (8 * w ^ 2) = 1 / 8 * (q : ℝ) ^ 2 * ((Q : ℝ) + 1) ^ 2 := by
    rw [hwdef, show halfWidth q Q = 1 / ((q : ℝ) * ((Q : ℝ) + 1)) from rfl]
    field_simp
  have hrest : (0 : ℝ) < 1 / (8 * (1 - w) ^ 2) := by
    have : (0 : ℝ) < 1 - w := by linarith
    positivity
  linarith [hnorm, hmono, hval, hkey, hrest]

/-! ## K3 — reduced to one `H`-free arithmetic sum, and blocked there

The `H`-dependence and the Ramanujan sum come out for free: the library already proves
`|T₃(q,H)| ≤ μ(q)²/φ(q)²` uniformly in `H` (`SingularSeries.norm_sing3Arith_le_maj`, itself
`|c_q(H)| ≤ φ(q)` for squarefree `q` via `cRam_sq_sqfree`). What is left is a statement about the
integers alone. -/

/-- **The blocking step of K3**, with `H`, the Ramanujan sum and the singular series all gone:
`∑_{q ≤ 3·10⁵} μ(q)²q²/φ(q)² ≤ cL`. Measured `583116.3063` (integer bracket
`[583116.30619, 583116.30638]` at scale `10⁹`), so `cL = 10⁶` carries `1.715×`.

**The squarefree factor `μ(q)²` is load-bearing and cannot be dropped**: the same sum over all `q`
is `1329254.405`, which already exceeds `10⁶`. See this file's header for why that kills the route
`FareyKernel.LocalTermWeightSum`'s docstring recommends, and for the route that does close. -/
def TotientSqSum (cL : ℝ) : Prop :=
  ∑ q ∈ Finset.Icc 1 300000,
      (ArithmeticFunction.moebius q : ℝ) ^ 2 * (q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 ≤ cL

/-- `TotientSqSum` constrains: the `q = 1` term is `1` and every term is `≥ 0`, so no `cL < 1`
satisfies it. It cannot be met degenerately, and `10⁶` is not a free parameter. -/
theorem totSq_one_le {cL : ℝ} (h : TotientSqSum cL) : 1 ≤ cL := by
  have hmem : (1 : ℕ) ∈ Finset.Icc 1 300000 := by
    rw [Finset.mem_Icc]; exact ⟨le_rfl, by norm_num⟩
  have hnn : ∀ q ∈ Finset.Icc 1 300000,
      0 ≤ (ArithmeticFunction.moebius q : ℝ) ^ 2 * (q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 :=
    fun q _ => by positivity
  have hterm : (ArithmeticFunction.moebius 1 : ℝ) ^ 2 * ((1 : ℕ) : ℝ) ^ 2
      / (Nat.totient 1 : ℝ) ^ 2 = 1 := by
    simp
  have hge := Finset.single_le_sum hnn hmem
  rw [hterm] at hge
  exact le_trans hge h

/-- **K3, reduced.** The arithmetic sum implies `FareyKernel.LocalTermWeightSum` at the same
constant, so K3 is exactly `TotientSqSum` and nothing else. -/
theorem k3_of_totSq {cL : ℝ} (h : TotientSqSum cL) : LocalTermWeightSum cL := by
  intro H _ _
  have hP : Pcut H = 300000 := rfl
  rw [hP]
  refine le_trans (Finset.sum_le_sum ?_) h
  intro q _
  have hb := SingularSeries.norm_sing3Arith_le_maj H q
  rw [SingularSeries.sing3Arith_apply, Real.norm_eq_abs, SingularSeries.sing3Maj] at hb
  rw [SingularBridge.localTerm_eq q H]
  have hq2 : (0 : ℝ) ≤ (q : ℝ) ^ 2 := by positivity
  calc |SingularSeries.sing3Local q H| * (q : ℝ) ^ 2
      ≤ ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2) * (q : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hb hq2
    _ = (ArithmeticFunction.moebius q : ℝ) ^ 2 * (q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 := by
        ring

/-! ## The link, and the chain -/

/-- **`MajorPlatt.KernelTailBound (1/10⁵)` from ONE hypothesis**, down from the three of
`FareyKernel.kernelTailBound_std`: K1 and K2 are supplied here as theorems and only the arithmetic
sum `TotientSqSum (10⁶)` remains. The target is unchanged — `cK = 1/10⁵` exactly as the chain
charges it, met by the crude constants `cT = 1/8`, `cL = 10⁶` at `1.25·10⁻⁷·H²`, inside by `80×`
(`k3_numbers.py`). -/
theorem kernelTailBound_holds (ts : TotientSqSum (10 ^ 6)) :
    MajorPlatt.KernelTailBound (1 / 10 ^ 5) :=
  kernelTailBound_std k1_holds k2_holds (k3_of_totSq ts)

/-- **The recomposed chain: FOUR hypotheses.** `grh` (Platt's finite GRH verification, never a Lean
theorem), `wa` (`WindowApproxUnder`, the analytic heart), `mn` (the minor-arc sup) and `ts` (the
finite arithmetic sum of K3).

Everything else is supplied from inside: `FareyDecomposition` by
`FareyKernel.fareyDecomposition_holds`, `KernelTailBound (1/10⁵)` by `kernelTailBound_holds`,
`SingularSeriesLower (5/4)` by `SingularBridge.singularSeriesLower_holds`, `CircleMethodIdentity`
by `CircleMethod.circleMethodIdentity_holds`, `PrimePowerRemoval 10` by
`PrimePower.primePowerRemoval_ten`.

The count: `MajorPlatt.cite_Helfgott_weighted_of_platt_chain` has eight and
`FareyKernel.cite_Helfgott_weighted_of_kernel_links` has nine (it traded one slot for the three
obligations K1–K3); discharging K1 and K2 and reducing K3 to `TotientSqSum` brings it to
**four**. -/
theorem chain_of_totSq (grh : PlattGRH)
    (wa : MajorPlatt.WindowApproxUnder 1000 (1 / 2) (fun q => 10 ^ 8 / (q : ℝ)))
    (mn : MinorSupBound Pcut Qcut (3 / 10)) (ts : TotientSqSum (10 ^ 6)) :
    Principia.Erdos1054.Cite_Helfgott_weighted :=
  MajorPlatt.cite_Helfgott_weighted_of_platt_chain grh fareyDecomposition_holds wa
    (kernelTailBound_holds ts) SingularBridge.singularSeriesLower_holds
    CircleMethod.circleMethodIdentity_holds mn PrimePower.primePowerRemoval_ten

end Principia.Common.TernaryGoldbach.KernelLinks
