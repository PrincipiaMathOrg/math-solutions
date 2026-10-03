/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.Spine
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

set_option autoImplicit false

/-!
# The minor-arc link of the ternary Goldbach spine, instantiated and proved

**What this file does.** `Spine.MinorSupBound P Q κ` — link 4 of the ternary spine, the only one on
the minor-arc side — was an unproved `def … : Prop`. Here it is **proved**, at explicit cutoffs and
an explicit constant:

  `minorSupBound_library : Spine.MinorSupBound pcut qcut 10`

with `pcut H = ⌊√H⌋ − 1`, `qcut H = ⌊√H⌋`, Vaughan parameters `upar H = 300²⌊H^{1/8}⌋²` and
`vpar H = 14²⌊H^{1/8}⌋²`. Unwound, that is

  `‖∑_{0<n≤H} Λ(n)e(nα)‖ ≤ 10·H/log H` for every `α ∉ MajorArcs`, every odd `H ≥ 10^27`.

Before this file the shortfall on this link lived in a **python calculation** recorded in
`Campaigns/Erdos-1054/HELFGOTT-ASSETS.md` §4.2 ("factor 9.13 at `H = 10^27`, self-closing only at
`H ≥ 10^32.8`"). It is now a theorem, so the exact expression that has to improve is pinned and any
future improvement slots into the same place.

## The verdict, and where each factor of it comes from

The spine can afford `κ = 46/100` in its sharp arrangement and `3/10` in its main one. What is
provable here is `κ₀ = 10`. The decomposition of that number, every step recomputed in exact
rational arithmetic before any Lean was written:

| stage | `κ` | factor | what it costs |
|---|---|---|---|
| the estimate at its own optimum | `4.346` | — | `max_{P<q≤Q} tightSupRHS`, whole box |
| at the cutoffs chosen here | `4.516` | `×1.04` | the `(U,V)` chosen here, NOT the cutoffs |
| after the `q`-uniform envelope | `6.834` | `×1.51` | `MinorArc.tightSupRHS_le` (see below) |
| after the Lean log-power bounds | `7.514` | `×1.10` | `1.1 %` per `log H`, from `log_le_rt32` |
| the budget actually proved | `10` | `×1.33` | rounding, kept generous on purpose |

The envelope costs a factor `2` on the two Type-I block factors (it bounds `⌊U/⌊q/2⌋⌋` by `4U/q`
rather than `2U/q`) and a factor `4.3` on the two `k`-terms (it replaces
`log₂(N/(V+1)) − log₂(U+1) = 21` by `log₂ N + 1 = 90`).

So **`4.35` of the `10` is the estimate itself and `2.3×` is everything Lean-side added.**

**FOUR CORRECTIONS from the round-3 audit of this file. Three were repeated in commit `4f2d1bc3`'s
message; read these before quoting anything above.**

1. **The `×1.04` is NOT the price of `P = Q − 1`.** `MinorArc.tightSupRHS` takes `(q U V N)` and
   has **no `P` argument**, so no factor of it can be a price of `P`. Both rows are evaluated at the
   same `q = ⌊√N⌋`; only `(U,V)` differs — `(8.80·10¹¹, 1.00·10⁹)` gives `4.3462`, the
   `(upar, vpar)` here give `4.5162`. That ratio is the price of THIS `(U,V)`, and is not forced.
   (The vacuous-corner finding stands: `minorSet_self_eq_empty` is proved.)
2. **`tightSupRHS_lower` does NOT show that no re-tuning reaches `0.46`.** It quantifies over
   nothing: `H`, `U`, `V`, `q` are all fixed, so it establishes the gap **at one parameter point**.
   The audit exhibits a point inside the admissible box (`U·V ≤ N`) where the single term carrying
   the theorem, `log N·4√10·N/√(V+1)`, has `κ = 0.1546` at `V = 10¹¹` — below target. Whether
   the FULL envelope can be re-tuned below `0.46` is **open**; nothing here settles it.
3. **The minor set at these cutoffs has measure `≤ 6·10⁻¹⁴`.** With `pcut H = qcut H − 1` the only
   admissible modulus is `q = qcut H`, so every point of the set lies within `1/qcut²` of a rational
   of denominator exactly `qcut H`. So `minorSupBound_library` is non-empty (proved) but nearly
   uninformative — a statement about a set of measure `6·10⁻¹⁴`, not about the arcs a circle-method
   argument integrates over. The `Nonempty` check was met in letter, not in spirit.
4. **The non-triviality margin is `≈9×`, not `300×`** — see `bound_below_trivial`.

**What the file does establish**, net of all four: the library's bound, in the spine's slot, is
provably `κ₀ = 10` at these cutoffs against a demand of `0.46`, and the shortfall at the ASSETS
parameters is `9.13`. **What closes it is quantified, and is exactly Helfgott's gain:** deleting the
single `log N` prefactor on the Type-II block takes `0.0699N → 0.0124N` (shortfall `9.13 → 1.62`);
deleting one `log` from the Type-I `S₂` term as well gives `0.0012N`, shortfall `0.154` — **closed,
with `6.5×` to spare.** The Type-I log alone buys almost nothing (`9.13 → 7.66`). So the remaining
minor-arc work is two named log factors in two named terms.

## Which term dominates, and what would buy the most

At the numerical optimum (`P = Q = √N`, `U = 8.8·10¹¹`, `V = 10⁹`, `N = 10^27`) the terms of
`MinorArc.tightSupRHS` split as — recomputed here, against `HELFGOTT-ASSETS.md`'s
`34.9 / 34.8 / 17.0 / 11.4`:

| term | share | ASSETS |
|---|---|---|
| `log N · 4√10 · N/√(V+1)` | `35.6 %` | `34.9 %` |
| `log N · 64 N √(1+log 2q)/√U` | `34.7 %` | `34.8 %` |
| `log(UV) · (16UV + 4q)(2+log 2q)` (Type-I `S₂`) | `16.4 %` | `17.0 %` |
| `log N · 6k √(Nq(1+log 2q))` | `11.4 %` | `11.4 %` |
| `log N · √32 · N k/√q` | `1.9 %` | omitted |

The ASSETS split is confirmed to within `2 %`; it omits the fifth term. The optimum is interior in
`(U,V)` and sits on the `P = Q` boundary, and the four leading terms are balanced, so **no single
term's improvement buys more than its share** — a factor `9` cannot come from re-tuning.

What *does* buy it is the **`log N` prefactor on the whole Type-II block**, which is `83.6 %` of
the total: deleting that one factor takes the bound from `0.0699 N` to `0.0124 N`, i.e. the
shortfall from `9.13` to `1.62`. Deleting one `log` from the Type-I `S₂` term as well (it carries
`log(UV) · (1+log(UV))`) takes it to `0.0012 N`, shortfall `0.154` — **closed, with `6.5×` to
spare**. Deleting the Type-I log alone buys almost nothing (`9.13 → 7.66`). This is exactly
Helfgott's gain: his minor-arc estimate is **log-free** where Vaughan's identity pays `(log N)²` —
one `log` from the dyadic Type-II Cauchy–Schwarz (the prefactor) and one from the divisor sum
inside it (`k`, and `1+log U` / `1+log(UV)` in the Type-I terms).

## The adversarial pass

A `MinorSupBound P Q κ` is **vacuous if the minor set is empty**, and that is not hypothetical:
round 1 proved `Spine.minorSet_one_one : minorSet 1 1 = ∅`. Three theorems settle the point.

1. `minorSet_self_eq_empty : 0 < Q → Spine.minorSet Q Q = ∅` — the general fact behind
   `minorSet_one_one`: the Farey windows of `MajorArcs Q Q` are the Farey dissection of order `Q`,
   which covers `ℝ` (`MinorArc.arc_decomposition`). **The numerical optimum of §4.2 sits exactly on
   this corner** (`P = √N` on its structural cap forces `Q = N/P = P`), so the parameters that
   minimise the bound make the statement say nothing. That is why `pcut` is `⌊√H⌋ − 1`.
2. `mem_minorSet : 1 ≤ P → P < Q → 1/(P+1) ∈ Spine.minorSet P Q` — an explicit witness, so the
   minor set at the chosen cutoffs is **non-empty** (`minorSet_nonempty`). The witness needs
   `P < Q` strictly, which is precisely what fails at the corner above.
3. `bound_below_trivial` — the proved bound is a genuine saving, not a restatement of something
   free: `10·H/log H` is below the only unconditional sup bound the library has
   (`Spine.expSum_sup_trivial : ‖S(α)‖ ≤ H log H`) by a factor `≥ 300` at every `H ≥ 10^27`.

Two further honest limits, stated rather than hidden. **(a)** `qcut = ⌊√H⌋` with `pcut = qcut − 1`
means the range `P < q ≤ Q` contains the single modulus `q = ⌊√H⌋`, and the minor set, while
non-empty, is thin — the major arcs at these cutoffs have total measure of order `4P/(Q+1)`.
Pushing the cutoffs apart to fatten the minor set costs `κ` on both sides at once (`piece10` grows
like `1/√P`, `piece12` like `√Q`), so this arrangement is the estimate's own preference, not a
convenience. **(b)** Nothing here says anything about `Spine.MajorArcLower`, which must hold at the
*same* `pcut`, `qcut`; a minor-arc bound bought by shrinking `Q` transfers the difficulty there.

## Not done

`MinorSupBound` is never weakened: `minorSupBound_library`'s statement is `Spine.MinorSupBound`
verbatim, and no gap is a `sorry` — there are none in this file. What the file does *not* do is
reach `0.46`; `tightSupRHS_lower` proves that cannot be done inside this estimate.

## One defect found in the interface

`Spine.minorSupBound_of_envelope` **cannot be applied**: its hypotheses are quantified over all
`H`, and at `H = 0` they contradict each other (`hU 0 : U 0 ≤ 0` forces `U 0 = 0`, and then
`hUV1 0 : 1 ≤ U 0 * V 0` is false). `envelope_hyps_unsatisfiable` proves that no `U`, `V` satisfy
them. `minorSupBound_of_envelope'` is the same one-line composition with the hypotheses restricted
to `10^27 ≤ H`, which is all `MinorSupBound` quantifies over; the fix belongs in `Spine.lean`,
whose owner is another agent this round.
-/

namespace Principia.Common.TernaryGoldbach.MinorArcBound

open Principia.Common.Goldbach

/-! ## The dyadic root tower

`rt64 H = H^{1/64}`, six nested `Real.sqrt`s. Every numeric bound below is a polynomial inequality
in this one variable `w`, with `w ≥ 2.64` at the threshold (`2.64^64 ≤ 10^27`), so the threshold is
spent once per term and nowhere else. -/

noncomputable def rt2 (H : ℕ) : ℝ := Real.sqrt (H : ℝ)
noncomputable def rt4 (H : ℕ) : ℝ := Real.sqrt (rt2 H)
noncomputable def rt8 (H : ℕ) : ℝ := Real.sqrt (rt4 H)
noncomputable def rt16 (H : ℕ) : ℝ := Real.sqrt (rt8 H)
noncomputable def rt32 (H : ℕ) : ℝ := Real.sqrt (rt16 H)
noncomputable def rt64 (H : ℕ) : ℝ := Real.sqrt (rt32 H)

theorem rt2_nonneg (H : ℕ) : 0 ≤ rt2 H := Real.sqrt_nonneg _
theorem rt4_nonneg (H : ℕ) : 0 ≤ rt4 H := Real.sqrt_nonneg _
theorem rt8_nonneg (H : ℕ) : 0 ≤ rt8 H := Real.sqrt_nonneg _
theorem rt16_nonneg (H : ℕ) : 0 ≤ rt16 H := Real.sqrt_nonneg _
theorem rt32_nonneg (H : ℕ) : 0 ≤ rt32 H := Real.sqrt_nonneg _
theorem rt64_nonneg (H : ℕ) : 0 ≤ rt64 H := Real.sqrt_nonneg _

theorem rt2_sq (H : ℕ) : rt2 H ^ 2 = (H : ℝ) := Real.sq_sqrt (Nat.cast_nonneg H)
theorem rt4_sq (H : ℕ) : rt4 H ^ 2 = rt2 H := Real.sq_sqrt (rt2_nonneg H)
theorem rt8_sq (H : ℕ) : rt8 H ^ 2 = rt4 H := Real.sq_sqrt (rt4_nonneg H)
theorem rt16_sq (H : ℕ) : rt16 H ^ 2 = rt8 H := Real.sq_sqrt (rt8_nonneg H)
theorem rt32_sq (H : ℕ) : rt32 H ^ 2 = rt16 H := Real.sq_sqrt (rt16_nonneg H)
theorem rt64_sq (H : ℕ) : rt64 H ^ 2 = rt32 H := Real.sq_sqrt (rt32_nonneg H)

theorem rt64_pow4 (H : ℕ) : rt64 H ^ 4 = rt16 H := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, rt64_sq, rt32_sq]

theorem rt64_pow8 (H : ℕ) : rt64 H ^ 8 = rt8 H := by
  rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, rt64_pow4, rt16_sq]

theorem rt64_pow16 (H : ℕ) : rt64 H ^ 16 = rt4 H := by
  rw [show (16 : ℕ) = 8 * 2 from rfl, pow_mul, rt64_pow8, rt8_sq]

theorem rt64_pow32 (H : ℕ) : rt64 H ^ 32 = rt2 H := by
  rw [show (32 : ℕ) = 16 * 2 from rfl, pow_mul, rt64_pow16, rt4_sq]

theorem rt64_pow64 (H : ℕ) : rt64 H ^ 64 = (H : ℝ) := by
  rw [show (64 : ℕ) = 32 * 2 from rfl, pow_mul, rt64_pow32, rt2_sq]

/-- `H^{1/64} ≥ 2.64` at the threshold (`2.64^64 = 9.6·10^154 ≤ 10^155`). -/
theorem rt64_ge (H : ℕ) (hH : 10 ^ 27 ≤ H) : (264 : ℝ) / 100 ≤ rt64 H := by
  have hHR : (10 : ℝ) ^ 27 ≤ (H : ℝ) := by exact_mod_cast hH
  have hnum : ((264 : ℝ) / 100) ^ 64 ≤ (10 : ℝ) ^ 27 := by norm_num
  have h1 : ((264 : ℝ) / 100) ^ 64 ≤ rt64 H ^ 64 := by
    rw [rt64_pow64]; linarith
  exact le_of_pow_le_pow_left₀ (by norm_num) (rt64_nonneg H) h1

/-! ## The master log bound -/

theorem sqrt_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hna := Real.sqrt_nonneg a
  have hnb := Real.sqrt_nonneg b
  have hle : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by nlinarith [mul_nonneg hna hnb]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq (by linarith)

/-- **The master log bound**: `log H ≤ 9.01 · H^{1/32}` for `H ≥ 10^27`. Proved from the
antitonicity of `log x / x` (`Real.log_div_self_antitoneOn`) anchored at `x = 6.9 ≤ H^{1/32}`,
so the constant is the *threshold* value rather than an asymptotic one: at `H = 10^27` it reads
`62.17 ≤ 9.01 · 6.9775 = 62.88`, i.e. it is lossy by `1.1 %`. Every constant below inherits that
`1.1 %` and nothing worse; a `log t ≤ t − 1`-style bound at the same root depth would be lossy by
a factor `2.7`. -/
theorem log_le_rt32 (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    Real.log (H : ℝ) ≤ (901 : ℝ) / 100 * rt64 H ^ 2 := by
  have hw : (264 : ℝ) / 100 ≤ rt64 H := rt64_ge H hH
  have hx69 : (69 : ℝ) / 10 ≤ rt64 H ^ 2 := by nlinarith [rt64_nonneg H]
  have he1 : Real.exp 1 ≤ (69 : ℝ) / 10 := by linarith [Real.exp_one_lt_d9]
  have hx32 : (rt64 H ^ 2) ^ 32 = (H : ℝ) := by rw [← pow_mul]; exact rt64_pow64 H
  have hxpos : (0 : ℝ) < rt64 H ^ 2 := by linarith
  have hlogH : Real.log (H : ℝ) = 32 * Real.log (rt64 H ^ 2) := by
    rw [← hx32, Real.log_pow]; push_cast; ring
  have hlog69 : Real.log ((69 : ℝ) / 10) ≤ 14 / 5 * Real.log 2 := by
    have h1 : ((69 : ℝ) / 10) ^ 5 ≤ 2 ^ 14 := by norm_num
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow, Real.log_pow] at h2
    push_cast at h2
    linarith
  have hant := Real.log_div_self_antitoneOn (Set.mem_Ici.mpr he1)
    (Set.mem_Ici.mpr (le_trans he1 hx69)) hx69
  simp only at hant
  have hstep : Real.log (rt64 H ^ 2) ≤ Real.log ((69 : ℝ) / 10) / ((69 : ℝ) / 10) * rt64 H ^ 2 :=
    (div_le_iff₀ hxpos).mp hant
  have hnum : Real.log ((69 : ℝ) / 10) / ((69 : ℝ) / 10) ≤ (901 : ℝ) / 100 / 32 := by
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    nlinarith [Real.log_two_lt_d9, hlog69]
  rw [hlogH]
  nlinarith [hstep, hnum, hxpos]

/-- `√(log H) ≤ 3.01 · H^{1/64}`, the half-power companion of `log_le_rt32`. -/
theorem sqrt_log_le (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    Real.sqrt (Real.log (H : ℝ)) ≤ (301 : ℝ) / 100 * rt64 H := by
  have h1 := log_le_rt32 H hH
  have hw0 : 0 ≤ rt64 H := rt64_nonneg H
  have hc : Real.sqrt ((901 : ℝ) / 100) ≤ 301 / 100 := by
    have : ((901 : ℝ) / 100) ≤ ((301 : ℝ) / 100) ^ 2 := by norm_num
    calc Real.sqrt ((901 : ℝ) / 100) ≤ Real.sqrt (((301 : ℝ) / 100) ^ 2) := Real.sqrt_le_sqrt this
      _ = 301 / 100 := Real.sqrt_sq (by norm_num)
  calc Real.sqrt (Real.log (H : ℝ)) ≤ Real.sqrt ((901 : ℝ) / 100 * rt64 H ^ 2) :=
        Real.sqrt_le_sqrt h1
    _ = Real.sqrt ((901 : ℝ) / 100) * rt64 H := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hw0]
    _ ≤ (301 : ℝ) / 100 * rt64 H := by nlinarith

/-! ## The parameters -/

/-- `⌊H^{1/8}⌋`, three `Nat.sqrt`s deep: the common scale of both Vaughan parameters. Truncation
costs `≤ 3` absolutely, i.e. `0.13 %` at the threshold. -/
def cpar (H : ℕ) : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt H))

/-- The minor cutoff `P = ⌊√H⌋ − 1`. -/
def pcut (H : ℕ) : ℕ := Nat.sqrt H - 1

/-- The major cutoff `Q = ⌊√H⌋`, so `Q ≈ H/P` — Helfgott's arrangement. -/
def qcut (H : ℕ) : ℕ := Nat.sqrt H

/-- `U = 300²·⌊H^{1/8}⌋² ≈ 9·10⁴·H^{1/4}`; a perfect square, so `√U = 300·⌊H^{1/8}⌋` exactly. -/
def upar (H : ℕ) : ℕ := 90000 * cpar H ^ 2

/-- `V = 14²·⌊H^{1/8}⌋² ≈ 196·H^{1/4}`; likewise `√V = 14·⌊H^{1/8}⌋`. -/
def vpar (H : ℕ) : ℕ := 196 * cpar H ^ 2

theorem cpar_pow8_le (H : ℕ) : cpar H ^ 8 ≤ H := by
  have h1 : Nat.sqrt H ^ 2 ≤ H := Nat.sqrt_le' H
  have h2 : Nat.sqrt (Nat.sqrt H) ^ 2 ≤ Nat.sqrt H := Nat.sqrt_le' _
  have h3 : cpar H ^ 2 ≤ Nat.sqrt (Nat.sqrt H) := Nat.sqrt_le' _
  calc cpar H ^ 8 = ((cpar H ^ 2) ^ 2) ^ 2 := by ring
    _ ≤ ((Nat.sqrt (Nat.sqrt H)) ^ 2) ^ 2 :=
        Nat.pow_le_pow_left (Nat.pow_le_pow_left h3 2) 2
    _ ≤ (Nat.sqrt H) ^ 2 := Nat.pow_le_pow_left h2 2
    _ ≤ H := h1

theorem cpar_le (H : ℕ) : (cpar H : ℝ) ≤ rt64 H ^ 8 := by
  rw [rt64_pow8]
  have h1 : ((Nat.sqrt H : ℕ) : ℝ) ≤ rt2 H := Real.nat_sqrt_le_real_sqrt
  have h2 : ((Nat.sqrt (Nat.sqrt H) : ℕ) : ℝ) ≤ rt4 H := by
    refine le_trans Real.nat_sqrt_le_real_sqrt ?_
    exact Real.sqrt_le_sqrt h1
  refine le_trans Real.nat_sqrt_le_real_sqrt ?_
  exact Real.sqrt_le_sqrt h2

theorem cpar_ge (H : ℕ) : rt64 H ^ 8 - 3 ≤ (cpar H : ℝ) := by
  rw [rt64_pow8]
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    calc Real.sqrt 2 ≤ Real.sqrt ((3 / 2 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = 3 / 2 := Real.sqrt_sq (by norm_num)
  have g1 : rt2 H ≤ (Nat.sqrt H : ℝ) + 1 := Real.real_sqrt_le_nat_sqrt_succ
  have g2 : rt4 H ≤ (Nat.sqrt (Nat.sqrt H) : ℝ) + 2 := by
    have a1 : rt4 H ≤ Real.sqrt ((Nat.sqrt H : ℝ) + 1) := Real.sqrt_le_sqrt g1
    have a2 : Real.sqrt ((Nat.sqrt H : ℝ) + 1) ≤ Real.sqrt ((Nat.sqrt H : ℝ)) + 1 := by
      have := sqrt_add_le (Nat.sqrt H : ℝ) 1 (by positivity) (by norm_num)
      simpa using this
    have a3 : Real.sqrt ((Nat.sqrt H : ℕ) : ℝ) ≤ (Nat.sqrt (Nat.sqrt H) : ℝ) + 1 :=
      Real.real_sqrt_le_nat_sqrt_succ
    linarith
  have a1 : rt8 H ≤ Real.sqrt ((Nat.sqrt (Nat.sqrt H) : ℝ) + 2) := Real.sqrt_le_sqrt g2
  have a2 : Real.sqrt ((Nat.sqrt (Nat.sqrt H) : ℝ) + 2)
      ≤ Real.sqrt ((Nat.sqrt (Nat.sqrt H) : ℝ)) + Real.sqrt 2 :=
    sqrt_add_le _ 2 (by positivity) (by norm_num)
  have a3 : Real.sqrt ((Nat.sqrt (Nat.sqrt H) : ℕ) : ℝ) ≤ (cpar H : ℝ) + 1 :=
    Real.real_sqrt_le_nat_sqrt_succ
  have : rt8 H ≤ (cpar H : ℝ) + 3 := by linarith
  linarith

theorem qcut_le (H : ℕ) : (qcut H : ℝ) ≤ rt64 H ^ 32 := by
  rw [rt64_pow32]; exact Real.nat_sqrt_le_real_sqrt

theorem natsqrt_pos (H : ℕ) (hH : 10 ^ 27 ≤ H) : 2 ≤ Nat.sqrt H := by
  have h : Nat.sqrt (10 ^ 27) ≤ Nat.sqrt H := Nat.sqrt_le_sqrt hH
  have h2 : 2 ≤ Nat.sqrt (10 ^ 27) := by
    rw [Nat.le_sqrt]; norm_num
  omega

theorem pcut_lt_qcut (H : ℕ) (hH : 10 ^ 27 ≤ H) : pcut H < qcut H := by
  have := natsqrt_pos H hH
  simp only [pcut, qcut]
  omega

theorem pcut_pos (H : ℕ) (hH : 10 ^ 27 ≤ H) : 0 < pcut H := by
  have := natsqrt_pos H hH
  simp only [pcut]
  omega

theorem pcut_ge (H : ℕ) (hH : 10 ^ 27 ≤ H) : rt64 H ^ 32 - 2 ≤ (pcut H : ℝ) := by
  have h2 := natsqrt_pos H hH
  have hcast : ((pcut H : ℕ) : ℝ) = (Nat.sqrt H : ℝ) - 1 := by
    simp only [pcut]
    have : (1 : ℕ) ≤ Nat.sqrt H := by omega
    push_cast [Nat.cast_sub this]
    ring
  have g1 : rt2 H ≤ (Nat.sqrt H : ℝ) + 1 := Real.real_sqrt_le_nat_sqrt_succ
  rw [rt64_pow32, hcast]
  linarith

/-- `⌊H^{1/8}⌋ ≥ 2356` at the threshold: the `−3` truncation is harmless. -/
theorem cpar_ge_2356 (H : ℕ) (hH : 10 ^ 27 ≤ H) : 2356 ≤ cpar H := by
  have hw := rt64_ge H hH
  have h8 : ((264 : ℝ) / 100) ^ 8 ≤ rt64 H ^ 8 :=
    pow_le_pow_left₀ (by norm_num) hw 8
  have hc := cpar_ge H
  have hnum : (2359 : ℝ) ≤ ((264 : ℝ) / 100) ^ 8 := by norm_num
  have : (2356 : ℝ) ≤ (cpar H : ℝ) := by linarith
  exact_mod_cast this

theorem cpar_pos (H : ℕ) (hH : 10 ^ 27 ≤ H) : 1 ≤ cpar H :=
  le_trans (by norm_num) (cpar_ge_2356 H hH)

/-! ## The minor set: empty at `P = Q`, non-empty exactly when `P < Q` -/

/-- **`Spine.minorSet_one_one` is a special case, and the numerical optimum sits on it.** For every
`Q ≥ 1`, `minorSet Q Q = ∅`: the Farey windows `|α − a/q| ≤ 1/(q(Q+1))` with `q ≤ Q` are the
classical Farey dissection of order `Q`, which covers `ℝ` — that is precisely what
`MinorArc.arc_decomposition` says. Consequently `MinorSupBound (fun _ => Q) (fun _ => Q) κ` is
vacuous for *every* `κ`, and any instantiation whose cutoffs coincide proves nothing. -/
theorem minorSet_self_eq_empty (Q : ℕ) (hQ : 0 < Q) : Spine.minorSet Q Q = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro α ⟨-, hnot⟩
  obtain ⟨a, q, hq0, hqQ, -, hnear, -⟩ := MinorArc.arc_decomposition α Q hQ
  refine hnot (Set.mem_biUnion (show q ∈ Set.Icc 1 Q from ⟨hq0, hqQ⟩) ?_)
  exact Set.mem_iUnion.mpr ⟨a, by rw [Metric.mem_closedBall, Real.dist_eq]; exact hnear⟩

/-- **Non-emptiness as soon as `P < Q`.** `α = 1/(P+1)` lies in `minorSet P Q`: for `1 ≤ q ≤ P`
and any `a : ℤ` the integer `q − a(P+1)` is nonzero (it is `≥ q ≥ 1` for `a ≤ 0` and `< 0` for
`a ≥ 1`), so `|α − a/q| ≥ 1/(q(P+1)) > 1/(q(Q+1))`. The strictness `P < Q` is exactly what is
needed, which is why `pcut = ⌊√H⌋ − 1` is one less than `qcut = ⌊√H⌋` and not equal to it. -/
theorem mem_minorSet (P Q : ℕ) (hP : 1 ≤ P) (hPQ : P < Q) :
    (1 / ((P : ℝ) + 1)) ∈ Spine.minorSet P Q := by
  have hPR : (0 : ℝ) < (P : ℝ) + 1 := by positivity
  have hP1 : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  refine ⟨⟨by positivity, ?_⟩, ?_⟩
  · rw [div_le_one hPR]; linarith
  · intro hmem
    simp only [MajorArcs, Set.mem_iUnion, Metric.mem_closedBall, Real.dist_eq,
      Set.mem_Icc, exists_prop] at hmem
    obtain ⟨q, ⟨hq1, hqP⟩, a, hball⟩ := hmem
    have hqR : (0 : ℝ) < (q : ℝ) := by
      have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
      linarith
    have heq : 1 / ((P : ℝ) + 1) - (a : ℝ) / (q : ℝ)
        = (((q : ℤ) - a * ((P : ℤ) + 1) : ℤ) : ℝ) / ((q : ℝ) * ((P : ℝ) + 1)) := by
      push_cast
      field_simp
    have hne : ((q : ℤ) - a * ((P : ℤ) + 1)) ≠ 0 := by
      have hqZ : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq1
      have hqPZ : (q : ℤ) ≤ (P : ℤ) := by exact_mod_cast hqP
      rcases le_or_gt a 0 with ha | ha
      · have : 0 < (q : ℤ) - a * ((P : ℤ) + 1) := by nlinarith
        omega
      · have h1 : (1 : ℤ) ≤ a := ha
        have : (q : ℤ) - a * ((P : ℤ) + 1) < 0 := by nlinarith
        omega
    have habs : (1 : ℝ) ≤ |(((q : ℤ) - a * ((P : ℤ) + 1) : ℤ) : ℝ)| := by
      have h1 : (1 : ℤ) ≤ |(q : ℤ) - a * ((P : ℤ) + 1)| := Int.one_le_abs hne
      calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
        _ ≤ ((|(q : ℤ) - a * ((P : ℤ) + 1)| : ℤ) : ℝ) := by exact_mod_cast h1
        _ = |(((q : ℤ) - a * ((P : ℤ) + 1) : ℤ) : ℝ)| := by push_cast [Int.cast_abs]; ring
    have hlow : 1 / ((q : ℝ) * ((P : ℝ) + 1)) ≤ |1 / ((P : ℝ) + 1) - (a : ℝ) / (q : ℝ)| := by
      have hpos : (0 : ℝ) < (q : ℝ) * ((P : ℝ) + 1) := by positivity
      rw [heq, abs_div, abs_of_pos hpos, div_le_div_iff₀ hpos hpos]
      nlinarith [mul_le_mul_of_nonneg_right habs hpos.le]
    have hQR : (P : ℝ) + 1 < (Q : ℝ) + 1 := by
      have : (P : ℝ) < (Q : ℝ) := by exact_mod_cast hPQ
      linarith
    have hstrict : 1 / ((q : ℝ) * ((Q : ℝ) + 1)) < 1 / ((q : ℝ) * ((P : ℝ) + 1)) := by
      apply one_div_lt_one_div_of_lt (by positivity)
      nlinarith
    linarith

theorem minorSet_nonempty (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    (Spine.minorSet (pcut H) (qcut H)).Nonempty :=
  ⟨_, mem_minorSet (pcut H) (qcut H) (pcut_pos H hH) (pcut_lt_qcut H hH)⟩

/-! ## Monomial bookkeeping

Every term of the envelope is bounded by a monomial `A·w^j` in `w = H^{1/64}`, and every such
monomial is compared with the budget's `b·w^64` by `mono_step`, which spends the surplus powers of
`w` at the threshold value `w ≥ 2.64`. This is the only place the threshold `10^27` enters the
numerics, and it enters once per term. -/

theorem m2 {a b A B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h1 : a ≤ A) (h2 : b ≤ B) : a * b ≤ A * B :=
  mul_le_mul h1 h2 hb (le_trans ha h1)

theorem m3 {a b c A B C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h1 : a ≤ A) (h2 : b ≤ B) (h3 : c ≤ C) : a * b * c ≤ A * B * C :=
  m2 (mul_nonneg ha hb) hc (m2 ha hb h1 h2) h3

theorem m4 {a b c d A B C D : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h1 : a ≤ A) (h2 : b ≤ B) (h3 : c ≤ C) (h4 : d ≤ D) : a * b * c * d ≤ A * B * C * D :=
  m2 (mul_nonneg (mul_nonneg ha hb) hc) hd (m3 ha hb hc h1 h2 h3) h4

theorem m5 {a b c d e A B C D E : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) (h1 : a ≤ A) (h2 : b ≤ B) (h3 : c ≤ C) (h4 : d ≤ D) (h5 : e ≤ E) :
    a * b * c * d * e ≤ A * B * C * D * E :=
  m2 (mul_nonneg (mul_nonneg (mul_nonneg ha hb) hc) hd) he (m4 ha hb hc hd h1 h2 h3 h4) h5

/-- `A·w^j ≤ b·w^k` whenever `A ≤ b·2.64^{k−j}` and `w ≥ 2.64`: the surplus `w^{k−j}` is spent at
the threshold. -/
theorem mono_step (w A b : ℝ) (j k : ℕ) (hjk : j ≤ k) (hw : (264 : ℝ) / 100 ≤ w) (_hA : 0 ≤ A)
    (hb : 0 ≤ b) (h : A ≤ b * ((264 : ℝ) / 100) ^ (k - j)) : A * w ^ j ≤ b * w ^ k := by
  have hw0 : (0 : ℝ) ≤ w := by linarith
  have hpow : ((264 : ℝ) / 100) ^ (k - j) ≤ w ^ (k - j) :=
    pow_le_pow_left₀ (by norm_num) hw _
  have hj : (0 : ℝ) ≤ w ^ j := by positivity
  have hsplit : w ^ k = w ^ j * w ^ (k - j) := by
    rw [← pow_add, Nat.add_sub_cancel' hjk]
  calc A * w ^ j ≤ (b * ((264 : ℝ) / 100) ^ (k - j)) * w ^ j := mul_le_mul_of_nonneg_right h hj
    _ ≤ (b * w ^ (k - j)) * w ^ j :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hb) hj
    _ = b * w ^ k := by rw [hsplit]; ring

/-- `√x ≤ c` from `x ≤ c²`. -/
theorem sqrt_le_of_sq (x c : ℝ) (hc : 0 ≤ c) (h : x ≤ c ^ 2) : Real.sqrt x ≤ c := by
  calc Real.sqrt x ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt h
    _ = c := Real.sqrt_sq hc

/-- `c ≤ √x` from `c² ≤ x`. -/
theorem le_sqrt_of_sq (x c : ℝ) (hc : 0 ≤ c) (h : c ^ 2 ≤ x) : c ≤ Real.sqrt x := by
  calc c = Real.sqrt (c ^ 2) := (Real.sqrt_sq hc).symm
    _ ≤ Real.sqrt x := Real.sqrt_le_sqrt h

/-! ## Threshold facts, one lemma each

Each fact below is a separate lemma with a two-hypothesis context. That is not cosmetic: assembled
as one proof the same chain exhausted 2·10⁶ heartbeats, because every `nlinarith` saw forty
hypotheses. -/

theorem rt_pow_ge (H : ℕ) (hH : 10 ^ 27 ≤ H) (j : ℕ) :
    ((264 : ℝ) / 100) ^ j ≤ rt64 H ^ j :=
  pow_le_pow_left₀ (by norm_num) (rt64_ge H hH) j

theorem rt8_ge (H : ℕ) (hH : 10 ^ 27 ≤ H) : (2359 : ℝ) ≤ rt64 H ^ 8 :=
  le_trans (by norm_num) (rt_pow_ge H hH 8)

theorem rt16_ge (H : ℕ) (hH : 10 ^ 27 ≤ H) : (5567000 : ℝ) ≤ rt64 H ^ 16 :=
  le_trans (by norm_num) (rt_pow_ge H hH 16)

theorem rt32_ge (H : ℕ) (hH : 10 ^ 27 ≤ H) : (30997000000000 : ℝ) ≤ rt64 H ^ 32 :=
  le_trans (by norm_num) (rt_pow_ge H hH 32)

theorem log_ge (H : ℕ) (hH : 10 ^ 27 ≤ H) : (61 : ℝ) ≤ Real.log (H : ℝ) :=
  Spine.log_ge_61 H hH

theorem log_pos' (H : ℕ) (hH : 10 ^ 27 ≤ H) : (0 : ℝ) < Real.log (H : ℝ) := by
  linarith [log_ge H hH]

theorem log_le_ten (H : ℕ) (hH : 10 ^ 27 ≤ H) : Real.log (H : ℝ) ≤ 10 * rt64 H ^ 2 := by
  have h := log_le_rt32 H hH
  have h2 : (0 : ℝ) < rt64 H ^ 2 := pow_pos (by linarith [rt64_ge H hH]) 2
  linarith

theorem log_sq_le (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    Real.log (H : ℝ) ^ 2 ≤ 8119 / 100 * rt64 H ^ 4 := by
  have h := log_le_rt32 H hH
  have hp := log_pos' H hH
  have h4 : (0 : ℝ) ≤ rt64 H ^ 4 := pow_nonneg (rt64_nonneg H) 4
  calc Real.log (H : ℝ) ^ 2 ≤ (901 / 100 * rt64 H ^ 2) ^ 2 :=
        pow_le_pow_left₀ hp.le h 2
    _ = 811801 / 10000 * rt64 H ^ 4 := by ring
    _ ≤ 8119 / 100 * rt64 H ^ 4 := by linarith

theorem log_cube_le (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    Real.log (H : ℝ) ^ 3 ≤ 73144 / 100 * rt64 H ^ 6 := by
  have h := log_le_rt32 H hH
  have hp := log_pos' H hH
  have h6 : (0 : ℝ) ≤ rt64 H ^ 6 := pow_nonneg (rt64_nonneg H) 6
  calc Real.log (H : ℝ) ^ 3 ≤ (901 / 100 * rt64 H ^ 2) ^ 3 :=
        pow_le_pow_left₀ hp.le h 3
    _ = 731432701 / 1000000 * rt64 H ^ 6 := by ring
    _ ≤ 73144 / 100 * rt64 H ^ 6 := by linarith

/-! ### The parameters as reals -/

theorem upar_le (H : ℕ) (hH : 10 ^ 27 ≤ H) : upar H ≤ H := by
  have hCn : 2356 ≤ cpar H := cpar_ge_2356 H hH
  have hC6n : 90000 ≤ cpar H ^ 6 := le_trans (by norm_num) (Nat.pow_le_pow_left hCn 6)
  calc upar H = 90000 * cpar H ^ 2 := rfl
    _ ≤ cpar H ^ 6 * cpar H ^ 2 := Nat.mul_le_mul_right _ hC6n
    _ = cpar H ^ 8 := by ring
    _ ≤ H := cpar_pow8_le H

theorem vpar_le (H : ℕ) (hH : 10 ^ 27 ≤ H) : vpar H ≤ H := by
  have hCn : 2356 ≤ cpar H := cpar_ge_2356 H hH
  have hC6n : 196 ≤ cpar H ^ 6 := le_trans (by norm_num) (Nat.pow_le_pow_left hCn 6)
  calc vpar H = 196 * cpar H ^ 2 := rfl
    _ ≤ cpar H ^ 6 * cpar H ^ 2 := Nat.mul_le_mul_right _ hC6n
    _ = cpar H ^ 8 := by ring
    _ ≤ H := cpar_pow8_le H

theorem upar_mul_vpar_le (H : ℕ) (hH : 10 ^ 27 ≤ H) : upar H * vpar H ≤ H := by
  have hCn : 2356 ≤ cpar H := cpar_ge_2356 H hH
  have hC4n : 17640000 ≤ cpar H ^ 4 := le_trans (by norm_num) (Nat.pow_le_pow_left hCn 4)
  calc upar H * vpar H = 17640000 * cpar H ^ 4 := by simp only [upar, vpar]; ring
    _ ≤ cpar H ^ 4 * cpar H ^ 4 := Nat.mul_le_mul_right _ hC4n
    _ = cpar H ^ 8 := by ring
    _ ≤ H := cpar_pow8_le H

theorem one_le_upar (H : ℕ) (hH : 10 ^ 27 ≤ H) : 1 ≤ upar H := by
  have h : 1 ≤ cpar H ^ 2 := Nat.one_le_pow 2 _ (by have := cpar_pos H hH; omega)
  simp only [upar]; omega

theorem one_le_vpar (H : ℕ) (hH : 10 ^ 27 ≤ H) : 1 ≤ vpar H := by
  have h : 1 ≤ cpar H ^ 2 := Nat.one_le_pow 2 _ (by have := cpar_pos H hH; omega)
  simp only [vpar]; omega

theorem one_le_upar_mul_vpar (H : ℕ) (hH : 10 ^ 27 ≤ H) : 1 ≤ upar H * vpar H :=
  Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by have := one_le_upar H hH; omega) (by have := one_le_vpar H hH; omega))

theorem upar_cast (H : ℕ) : (upar H : ℝ) = 90000 * (cpar H : ℝ) ^ 2 := by
  simp only [upar]; push_cast; ring

theorem vpar_cast (H : ℕ) : (vpar H : ℝ) = 196 * (cpar H : ℝ) ^ 2 := by
  simp only [vpar]; push_cast; ring

theorem cpar_sq_le (H : ℕ) : (cpar H : ℝ) ^ 2 ≤ rt64 H ^ 16 := by
  calc (cpar H : ℝ) ^ 2 ≤ (rt64 H ^ 8) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (cpar_le H) 2
    _ = rt64 H ^ 16 := by ring

theorem cpar_quart_le (H : ℕ) : (cpar H : ℝ) ^ 4 ≤ rt64 H ^ 32 := by
  calc (cpar H : ℝ) ^ 4 ≤ (rt64 H ^ 8) ^ 4 :=
        pow_le_pow_left₀ (by positivity) (cpar_le H) 4
    _ = rt64 H ^ 32 := by ring

theorem upar_real_le (H : ℕ) : (upar H : ℝ) ≤ 90000 * rt64 H ^ 16 := by
  rw [upar_cast]; linarith [cpar_sq_le H]

theorem vpar_real_le (H : ℕ) : (vpar H : ℝ) ≤ 196 * rt64 H ^ 16 := by
  rw [vpar_cast]; linarith [cpar_sq_le H]

theorem upar_vpar_real_le (H : ℕ) :
    (upar H : ℝ) * (vpar H : ℝ) ≤ 17640000 * rt64 H ^ 32 := by
  rw [upar_cast, vpar_cast]
  have he : 90000 * (cpar H : ℝ) ^ 2 * (196 * (cpar H : ℝ) ^ 2)
      = 17640000 * (cpar H : ℝ) ^ 4 := by ring
  rw [he]; linarith [cpar_quart_le H]

theorem upar_real_pos (H : ℕ) (hH : 10 ^ 27 ≤ H) : (0 : ℝ) < (upar H : ℝ) := by
  have h : (1 : ℝ) ≤ (upar H : ℝ) := by exact_mod_cast one_le_upar H hH
  linarith

theorem vpar_real_pos (H : ℕ) (hH : 10 ^ 27 ≤ H) : (0 : ℝ) < (vpar H : ℝ) := by
  have h : (1 : ℝ) ≤ (vpar H : ℝ) := by exact_mod_cast one_le_vpar H hH
  linarith

theorem pcut_real_ge (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    999 / 1000 * rt64 H ^ 32 ≤ (pcut H : ℝ) := by
  have h := pcut_ge H hH
  have h2 := rt32_ge H hH
  linarith

theorem pcut_real_pos (H : ℕ) (hH : 10 ^ 27 ≤ H) : (0 : ℝ) < (pcut H : ℝ) := by
  have h := pcut_real_ge H hH
  have h2 := rt32_ge H hH
  linarith

theorem qcut_real_ge_two (H : ℕ) (hH : 10 ^ 27 ≤ H) : (2 : ℝ) ≤ (qcut H : ℝ) := by
  exact_mod_cast natsqrt_pos H hH

theorem two_div_pcut_le (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    2 * (H : ℝ) / (pcut H : ℝ) ≤ 3 * rt64 H ^ 32 := by
  rw [div_le_iff₀ (pcut_real_pos H hH)]
  have hP := pcut_real_ge H hH
  have h32 := rt32_ge H hH
  have h64 := rt64_pow64 H
  have hsq : rt64 H ^ 32 * rt64 H ^ 32 = rt64 H ^ 64 := by ring
  have h1 : (0 : ℝ) ≤ 3 * rt64 H ^ 32 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hP h1, h64, hsq]

/-! ### The logarithms appearing in the envelope -/

theorem log_upar_le (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    Real.log (upar H : ℝ) ≤ Real.log (H : ℝ) :=
  Real.log_le_log (upar_real_pos H hH) (by exact_mod_cast upar_le H hH)

theorem log_upar_nonneg (H : ℕ) (hH : 10 ^ 27 ≤ H) : (0 : ℝ) ≤ Real.log (upar H : ℝ) :=
  Real.log_nonneg (by exact_mod_cast one_le_upar H hH)

theorem log_vpar_le (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    Real.log (vpar H : ℝ) ≤ Real.log (H : ℝ) :=
  Real.log_le_log (vpar_real_pos H hH) (by exact_mod_cast vpar_le H hH)

theorem log_vpar_nonneg (H : ℕ) (hH : 10 ^ 27 ≤ H) : (0 : ℝ) ≤ Real.log (vpar H : ℝ) :=
  Real.log_nonneg (by exact_mod_cast one_le_vpar H hH)

theorem upar_vpar_cast_le (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    (upar H : ℝ) * (vpar H : ℝ) ≤ (H : ℝ) := by
  have h : ((upar H * vpar H : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast upar_mul_vpar_le H hH
  push_cast at h; linarith

theorem log_upar_vpar_le (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    Real.log ((upar H : ℝ) * (vpar H : ℝ)) ≤ Real.log (H : ℝ) :=
  Real.log_le_log (mul_pos (upar_real_pos H hH) (vpar_real_pos H hH))
    (upar_vpar_cast_le H hH)

theorem log_upar_vpar_nonneg (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    (0 : ℝ) ≤ Real.log ((upar H : ℝ) * (vpar H : ℝ)) := by
  refine Real.log_nonneg ?_
  have h : ((1 : ℕ) : ℝ) ≤ ((upar H * vpar H : ℕ) : ℝ) := by
    exact_mod_cast one_le_upar_mul_vpar H hH
  push_cast at h; linarith

theorem log_succ_le (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    Real.log ((H : ℝ) + 1) ≤ 102 / 100 * Real.log (H : ℝ) := by
  have hHR : (1 : ℝ) ≤ (H : ℝ) := by
    have : (1 : ℕ) ≤ H := le_trans (by norm_num) hH
    exact_mod_cast this
  have h1 : Real.log ((H : ℝ) + 1) ≤ Real.log (2 * (H : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  rw [Real.log_mul (by norm_num) (by linarith)] at h1
  have hL := log_ge H hH
  nlinarith [Real.log_two_lt_d9, hL, h1]

theorem log_succ_nonneg (H : ℕ) : (0 : ℝ) ≤ Real.log ((H : ℝ) + 1) :=
  Real.log_nonneg (by have h : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H; linarith)

theorem log_rt64 (H : ℕ) : Real.log (rt64 H) = Real.log (H : ℝ) / 64 := by
  have h : Real.log (H : ℝ) = 64 * Real.log (rt64 H) := by
    rw [← rt64_pow64 H, Real.log_pow]; push_cast; ring
  linarith

theorem log_two_qcut_le (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    2 + Real.log (2 * (qcut H : ℝ)) ≤ 55 / 100 * Real.log (H : ℝ) := by
  have hQ2 := qcut_real_ge_two H hH
  have hQb := qcut_le H
  have hrpos : (0 : ℝ) < rt64 H := by linarith [rt64_ge H hH]
  have hmono : Real.log (2 * (qcut H : ℝ)) ≤ Real.log (2 * rt64 H ^ 32) :=
    Real.log_le_log (by linarith) (by linarith)
  have hrhs : Real.log (2 * rt64 H ^ 32) = Real.log 2 + 32 * Real.log (rt64 H) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt (pow_pos hrpos 32)), Real.log_pow]
    push_cast; ring
  rw [hrhs] at hmono
  have hlw := log_rt64 H
  have hL := log_ge H hH
  nlinarith [Real.log_two_lt_d9, hlw, hL, hmono]

theorem log_two_qcut_nonneg (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    (0 : ℝ) ≤ Real.log (2 * (qcut H : ℝ)) :=
  Real.log_nonneg (by linarith [qcut_real_ge_two H hH])

theorem natlog_succ_le (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    ((Nat.log 2 H + 1 : ℕ) : ℝ) ≤ 1316 / 100 * rt64 H ^ 2 := by
  have hH0 : H ≠ 0 := by have : (1 : ℕ) ≤ H := le_trans (by norm_num) hH; omega
  have h1 : ((2 : ℝ)) ^ (Nat.log 2 H) ≤ (H : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 hH0
  have h2 : (Nat.log 2 H : ℝ) * Real.log 2 ≤ Real.log (H : ℝ) := by
    have h := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h; linarith
  have h3 : (0 : ℝ) ≤ (Nat.log 2 H : ℝ) := Nat.cast_nonneg _
  have h4 : (Nat.log 2 H : ℝ) ≤ 1443 / 1000 * Real.log (H : ℝ) := by
    nlinarith [Real.log_two_gt_d9, h2, h3]
  have hL := log_ge H hH
  have hLu := log_le_rt32 H hH
  push_cast
  nlinarith [h4, hL, hLu]

theorem natlog_succ_nonneg (H : ℕ) : (0 : ℝ) ≤ ((Nat.log 2 H + 1 : ℕ) : ℝ) :=
  Nat.cast_nonneg _

/-! ### The square roots -/

theorem sqrt_ten_le : Real.sqrt 10 ≤ 317 / 100 :=
  sqrt_le_of_sq _ _ (by norm_num) (by norm_num)

theorem sqrt_thirtytwo_le : Real.sqrt 32 ≤ 566 / 100 :=
  sqrt_le_of_sq _ _ (by norm_num) (by norm_num)

theorem sqrt_vpar_ge (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    1398 / 100 * rt64 H ^ 8 ≤ Real.sqrt ((vpar H : ℝ) + 1) := by
  refine le_sqrt_of_sq _ _ (by positivity) ?_
  rw [vpar_cast]
  have hCge := cpar_ge H
  have h8 := rt8_ge H hH
  nlinarith [hCge, h8, sq_nonneg ((cpar H : ℝ) - (rt64 H ^ 8 - 3))]

theorem sqrt_upar_ge (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    2996 / 10 * rt64 H ^ 8 ≤ Real.sqrt (upar H : ℝ) := by
  refine le_sqrt_of_sq _ _ (by positivity) ?_
  rw [upar_cast]
  have hCge := cpar_ge H
  have h8 := rt8_ge H hH
  nlinarith [hCge, h8, sq_nonneg ((cpar H : ℝ) - (rt64 H ^ 8 - 3))]

theorem sqrt_pcut_ge (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    999 / 1000 * rt64 H ^ 16 ≤ Real.sqrt (pcut H : ℝ) := by
  refine le_sqrt_of_sq _ _ (by positivity) ?_
  have hP := pcut_real_ge H hH
  have hsq : (999 / 1000 * rt64 H ^ 16) ^ 2 = 998001 / 1000000 * rt64 H ^ 32 := by ring
  rw [hsq]
  have h32 := rt32_ge H hH
  linarith

theorem sqrt_vpar_pos (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    (0 : ℝ) < Real.sqrt ((vpar H : ℝ) + 1) := by
  have h := sqrt_vpar_ge H hH
  have h8 := rt8_ge H hH
  nlinarith

theorem sqrt_upar_pos (H : ℕ) (hH : 10 ^ 27 ≤ H) : (0 : ℝ) < Real.sqrt (upar H : ℝ) := by
  have h := sqrt_upar_ge H hH
  have h8 := rt8_ge H hH
  nlinarith

theorem sqrt_pcut_pos (H : ℕ) (hH : 10 ^ 27 ≤ H) : (0 : ℝ) < Real.sqrt (pcut H : ℝ) := by
  have h := sqrt_pcut_ge H hH
  have h16 := rt16_ge H hH
  nlinarith

theorem sqrt_logq_le (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    Real.sqrt (1 + Real.log (2 * (qcut H : ℝ))) ≤ 2227 / 1000 * rt64 H := by
  refine sqrt_le_of_sq _ _ (mul_nonneg (by norm_num) (rt64_nonneg H)) ?_
  have hq := log_two_qcut_le H hH
  have hLu := log_le_rt32 H hH
  nlinarith [hq, hLu]

theorem sqrt_HQ_le (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    Real.sqrt ((H : ℝ) * (qcut H : ℝ) * (1 + Real.log (2 * (qcut H : ℝ))))
      ≤ 2227 / 1000 * rt64 H ^ 49 := by
  refine sqrt_le_of_sq _ _ (mul_nonneg (by norm_num) (pow_nonneg (rt64_nonneg H) 49)) ?_
  have hq := log_two_qcut_le H hH
  have hq0 := log_two_qcut_nonneg H hH
  have hLu := log_le_rt32 H hH
  have h64 := rt64_pow64 H
  have h1 : (H : ℝ) * (qcut H : ℝ) * (1 + Real.log (2 * (qcut H : ℝ)))
      ≤ rt64 H ^ 64 * rt64 H ^ 32 * (49555 / 10000 * rt64 H ^ 2) := by
    refine m3 (Nat.cast_nonneg H) (Nat.cast_nonneg _) (by linarith) (by linarith) (qcut_le H) ?_
    nlinarith [hq, hLu]
  have h2 : rt64 H ^ 64 * rt64 H ^ 32 * (49555 / 10000 * rt64 H ^ 2)
      = 49555 / 10000 * rt64 H ^ 98 := by ring
  have h3 : (2227 / 1000 * rt64 H ^ 49) ^ 2 = 4959529 / 1000000 * rt64 H ^ 98 := by ring
  rw [h3]
  rw [h2] at h1
  have h4 : (0 : ℝ) ≤ rt64 H ^ 98 := pow_nonneg (rt64_nonneg H) 98
  linarith

/-! ### The three quotients of the Type-II block -/

theorem quot_vpar_le (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    4 * Real.sqrt 10 * (H : ℝ) / Real.sqrt ((vpar H : ℝ) + 1) ≤ 908 / 1000 * rt64 H ^ 56 := by
  rw [div_le_iff₀ (sqrt_vpar_pos H hH)]
  have hA : 4 * Real.sqrt 10 * (H : ℝ) ≤ 4 * (317 / 100) * rt64 H ^ 64 := by
    rw [← rt64_pow64 H]
    nlinarith [sqrt_ten_le, Real.sqrt_nonneg 10, pow_nonneg (rt64_nonneg H) 64]
  have hB : 908 / 1000 * rt64 H ^ 56 * (1398 / 100 * rt64 H ^ 8)
      ≤ 908 / 1000 * rt64 H ^ 56 * Real.sqrt ((vpar H : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left (sqrt_vpar_ge H hH)
      (by positivity)
  have hC : 908 / 1000 * rt64 H ^ 56 * (1398 / 100 * rt64 H ^ 8)
      = 1269384 / 100000 * rt64 H ^ 64 := by ring
  have h64 : (0 : ℝ) ≤ rt64 H ^ 64 := pow_nonneg (rt64_nonneg H) 64
  linarith

theorem quot_pcut_le (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    Real.sqrt 32 * (H : ℝ) * ((Nat.log 2 H + 1 : ℕ) : ℝ) / Real.sqrt (pcut H : ℝ)
      ≤ 746 / 10 * rt64 H ^ 50 := by
  rw [div_le_iff₀ (sqrt_pcut_pos H hH)]
  have hA : Real.sqrt 32 * (H : ℝ) * ((Nat.log 2 H + 1 : ℕ) : ℝ)
      ≤ 566 / 100 * rt64 H ^ 64 * (1316 / 100 * rt64 H ^ 2) :=
    m3 (Real.sqrt_nonneg 32) (Nat.cast_nonneg H) (natlog_succ_nonneg H) sqrt_thirtytwo_le
      (by linarith [rt64_pow64 H]) (natlog_succ_le H hH)
  have hB : 746 / 10 * rt64 H ^ 50 * (999 / 1000 * rt64 H ^ 16)
      ≤ 746 / 10 * rt64 H ^ 50 * Real.sqrt (pcut H : ℝ) :=
    mul_le_mul_of_nonneg_left (sqrt_pcut_ge H hH) (by positivity)
  have hC1 : 566 / 100 * rt64 H ^ 64 * (1316 / 100 * rt64 H ^ 2)
      = 744856 / 10000 * rt64 H ^ 66 := by ring
  have hC2 : 746 / 10 * rt64 H ^ 50 * (999 / 1000 * rt64 H ^ 16)
      = 745254 / 10000 * rt64 H ^ 66 := by ring
  have h66 : (0 : ℝ) ≤ rt64 H ^ 66 := pow_nonneg (rt64_nonneg H) 66
  linarith

theorem quot_upar_le (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    64 * (H : ℝ) * Real.sqrt (1 + Real.log (2 * (qcut H : ℝ))) / Real.sqrt (upar H : ℝ)
      ≤ 476 / 1000 * rt64 H ^ 57 := by
  rw [div_le_iff₀ (sqrt_upar_pos H hH)]
  have hA : 64 * (H : ℝ) * Real.sqrt (1 + Real.log (2 * (qcut H : ℝ)))
      ≤ 64 * rt64 H ^ 64 * (2227 / 1000 * rt64 H) :=
    m3 (by norm_num) (Nat.cast_nonneg H) (Real.sqrt_nonneg _) (le_refl _)
      (by linarith [rt64_pow64 H]) (sqrt_logq_le H hH)
  have hB : 476 / 1000 * rt64 H ^ 57 * (2996 / 10 * rt64 H ^ 8)
      ≤ 476 / 1000 * rt64 H ^ 57 * Real.sqrt (upar H : ℝ) :=
    mul_le_mul_of_nonneg_left (sqrt_upar_ge H hH)
      (mul_nonneg (by norm_num) (pow_nonneg (rt64_nonneg H) 57))
  have hC1 : 64 * rt64 H ^ 64 * (2227 / 1000 * rt64 H) = 142528 / 1000 * rt64 H ^ 65 := by ring
  have hC2 : 476 / 1000 * rt64 H ^ 57 * (2996 / 10 * rt64 H ^ 8)
      = 1426096 / 10000 * rt64 H ^ 65 := by ring
  have h65 : (0 : ℝ) ≤ rt64 H ^ 65 := pow_nonneg (rt64_nonneg H) 65
  linarith

/-! ### Shared factor bounds -/

theorem two_log_succ_le (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    2 * Real.log ((H : ℝ) + 1) ≤ 19 * rt64 H ^ 2 := by
  have h1 := log_succ_le H hH
  have h2 := log_le_rt32 H hH
  have h3 : (0 : ℝ) ≤ rt64 H ^ 2 := pow_nonneg (rt64_nonneg H) 2
  linarith

theorem one_add_log_upar_le (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    1 + Real.log (upar H : ℝ) ≤ 10 * rt64 H ^ 2 := by
  have h1 := log_upar_le H hH
  have h2 := log_le_rt32 H hH
  have h3 : (2359 : ℝ) ≤ rt64 H ^ 8 := rt8_ge H hH
  have h4 : ((264 : ℝ) / 100) ^ 2 ≤ rt64 H ^ 2 := rt_pow_ge H hH 2
  nlinarith

theorem one_add_log_upar_vpar_le (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    1 + Real.log ((upar H : ℝ) * (vpar H : ℝ)) ≤ 10 * rt64 H ^ 2 := by
  have h1 := log_upar_vpar_le H hH
  have h2 := log_le_rt32 H hH
  have h4 : ((264 : ℝ) / 100) ^ 2 ≤ rt64 H ^ 2 := rt_pow_ge H hH 2
  nlinarith

theorem log_upar_vpar_le' (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    Real.log ((upar H : ℝ) * (vpar H : ℝ)) ≤ 901 / 100 * rt64 H ^ 2 :=
  le_trans (log_upar_vpar_le H hH) (log_le_rt32 H hH)

theorem two_add_logq_le (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    2 + Real.log (2 * (qcut H : ℝ)) ≤ 49555 / 10000 * rt64 H ^ 2 := by
  have h1 := log_two_qcut_le H hH
  have h2 := log_le_rt32 H hH
  linarith

theorem two_add_logq_le6 (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    2 + Real.log (2 * (qcut H : ℝ)) ≤ 6 * rt64 H ^ 2 := by
  have h1 := two_add_logq_le H hH
  have h3 : (0 : ℝ) ≤ rt64 H ^ 2 := pow_nonneg (rt64_nonneg H) 2
  linarith

theorem two_add_logq_nonneg (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    (0 : ℝ) ≤ 2 + Real.log (2 * (qcut H : ℝ)) := by
  linarith [log_two_qcut_nonneg H hH]

/-! ### The twelve pieces

`piece_k` bounds one monomial of the distributed envelope, multiplied by the `log H` that
`le_div_iff₀` moves across. The budgets sum to `7.926 ≤ 10`; each was fixed by an exact-rational
computation before any Lean was written, and each has at least `4.5 %` of slack. -/

theorem piece1 (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    2 * Real.log ((H : ℝ) + 1) * (2 * (H : ℝ) / (pcut H : ℝ))
        * (1 + Real.log (upar H : ℝ)) * Real.log (H : ℝ)
      ≤ 1 / 1000 * rt64 H ^ 64 := by
  calc 2 * Real.log ((H : ℝ) + 1) * (2 * (H : ℝ) / (pcut H : ℝ))
        * (1 + Real.log (upar H : ℝ)) * Real.log (H : ℝ)
      ≤ (19 * rt64 H ^ 2) * (3 * rt64 H ^ 32) * (10 * rt64 H ^ 2) * (10 * rt64 H ^ 2) :=
        m4 (by linarith [log_succ_nonneg H]) (by positivity)
          (by linarith [log_upar_nonneg H hH]) (log_pos' H hH).le
          (two_log_succ_le H hH) (two_div_pcut_le H hH) (one_add_log_upar_le H hH)
          (log_le_ten H hH)
    _ = 5700 * rt64 H ^ 38 := by ring
    _ ≤ 1 / 1000 * rt64 H ^ 64 :=
        mono_step (rt64 H) 5700 (1 / 1000) 38 64 (by norm_num) (rt64_ge H hH)
          (by norm_num) (by norm_num) (by norm_num)

theorem piece2 (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    2 * Real.log ((H : ℝ) + 1) * (16 * (upar H : ℝ))
        * (2 + Real.log (2 * (qcut H : ℝ))) * Real.log (H : ℝ)
      ≤ 2 / 100 * rt64 H ^ 64 := by
  calc 2 * Real.log ((H : ℝ) + 1) * (16 * (upar H : ℝ))
        * (2 + Real.log (2 * (qcut H : ℝ))) * Real.log (H : ℝ)
      ≤ (19 * rt64 H ^ 2) * (1440000 * rt64 H ^ 16) * (6 * rt64 H ^ 2) * (10 * rt64 H ^ 2) :=
        m4 (by linarith [log_succ_nonneg H]) (by positivity)
          (two_add_logq_nonneg H hH) (log_pos' H hH).le
          (two_log_succ_le H hH) (by linarith [upar_real_le H]) (two_add_logq_le6 H hH)
          (log_le_ten H hH)
    _ = 1641600000 * rt64 H ^ 22 := by ring
    _ ≤ 2 / 100 * rt64 H ^ 64 :=
        mono_step (rt64 H) 1641600000 (2 / 100) 22 64 (by norm_num) (rt64_ge H hH)
          (by norm_num) (by norm_num) (by norm_num)

theorem piece3 (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    2 * Real.log ((H : ℝ) + 1) * (4 * (qcut H : ℝ))
        * (2 + Real.log (2 * (qcut H : ℝ))) * Real.log (H : ℝ)
      ≤ 1 / 1000 * rt64 H ^ 64 := by
  calc 2 * Real.log ((H : ℝ) + 1) * (4 * (qcut H : ℝ))
        * (2 + Real.log (2 * (qcut H : ℝ))) * Real.log (H : ℝ)
      ≤ (19 * rt64 H ^ 2) * (4 * rt64 H ^ 32) * (6 * rt64 H ^ 2) * (10 * rt64 H ^ 2) :=
        m4 (by linarith [log_succ_nonneg H]) (by positivity)
          (two_add_logq_nonneg H hH) (log_pos' H hH).le
          (two_log_succ_le H hH) (by linarith [qcut_le H]) (two_add_logq_le6 H hH)
          (log_le_ten H hH)
    _ = 4560 * rt64 H ^ 38 := by ring
    _ ≤ 1 / 1000 * rt64 H ^ 64 :=
        mono_step (rt64 H) 4560 (1 / 1000) 38 64 (by norm_num) (rt64_ge H hH)
          (by norm_num) (by norm_num) (by norm_num)

theorem piece4 (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    2 * Real.log ((H : ℝ) + 1) * (upar H : ℝ) * Real.log (H : ℝ)
      ≤ 1 / 1000 * rt64 H ^ 64 := by
  calc 2 * Real.log ((H : ℝ) + 1) * (upar H : ℝ) * Real.log (H : ℝ)
      ≤ (19 * rt64 H ^ 2) * (90000 * rt64 H ^ 16) * (10 * rt64 H ^ 2) :=
        m3 (by linarith [log_succ_nonneg H]) (Nat.cast_nonneg _) (log_pos' H hH).le
          (two_log_succ_le H hH) (upar_real_le H) (log_le_ten H hH)
    _ = 17100000 * rt64 H ^ 20 := by ring
    _ ≤ 1 / 1000 * rt64 H ^ 64 :=
        mono_step (rt64 H) 17100000 (1 / 1000) 20 64 (by norm_num) (rt64_ge H hH)
          (by norm_num) (by norm_num) (by norm_num)

theorem piece5 (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    Real.log ((upar H : ℝ) * (vpar H : ℝ)) * (2 * (H : ℝ) / (pcut H : ℝ))
        * (1 + Real.log ((upar H : ℝ) * (vpar H : ℝ))) * Real.log (H : ℝ)
      ≤ 1 / 1000 * rt64 H ^ 64 := by
  calc Real.log ((upar H : ℝ) * (vpar H : ℝ)) * (2 * (H : ℝ) / (pcut H : ℝ))
        * (1 + Real.log ((upar H : ℝ) * (vpar H : ℝ))) * Real.log (H : ℝ)
      ≤ (10 * rt64 H ^ 2) * (3 * rt64 H ^ 32) * (10 * rt64 H ^ 2) * (10 * rt64 H ^ 2) :=
        m4 (log_upar_vpar_nonneg H hH) (by positivity)
          (by linarith [log_upar_vpar_nonneg H hH]) (log_pos' H hH).le
          (le_trans (log_upar_vpar_le H hH) (log_le_ten H hH)) (two_div_pcut_le H hH)
          (one_add_log_upar_vpar_le H hH) (log_le_ten H hH)
    _ = 3000 * rt64 H ^ 38 := by ring
    _ ≤ 1 / 1000 * rt64 H ^ 64 :=
        mono_step (rt64 H) 3000 (1 / 1000) 38 64 (by norm_num) (rt64_ge H hH)
          (by norm_num) (by norm_num) (by norm_num)

/-- **The binding Type-I term.** `log(UV)·16UV·(2+log 2Q)·log H ≤ 1.3·H`: this is the term that
forces `U·V` down and therefore fights the two Type-II terms that want `U` and `V` up. Its budget
is `1.3` against a computed `1.2401` — the tightest of the twelve. -/
theorem piece6 (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    Real.log ((upar H : ℝ) * (vpar H : ℝ)) * (16 * ((upar H : ℝ) * (vpar H : ℝ)))
        * (2 + Real.log (2 * (qcut H : ℝ))) * Real.log (H : ℝ)
      ≤ 13 / 10 * rt64 H ^ 64 := by
  calc Real.log ((upar H : ℝ) * (vpar H : ℝ)) * (16 * ((upar H : ℝ) * (vpar H : ℝ)))
        * (2 + Real.log (2 * (qcut H : ℝ))) * Real.log (H : ℝ)
      ≤ (901 / 100 * rt64 H ^ 2) * (282240000 * rt64 H ^ 32)
          * (49555 / 10000 * rt64 H ^ 2) * (901 / 100 * rt64 H ^ 2) :=
        m4 (log_upar_vpar_nonneg H hH) (by positivity)
          (two_add_logq_nonneg H hH) (log_pos' H hH).le
          (log_upar_vpar_le' H hH) (by linarith [upar_vpar_real_le H])
          (two_add_logq_le H hH) (log_le_rt32 H hH)
    _ = (901 / 100 * 282240000 * (49555 / 10000) * (901 / 100)) * rt64 H ^ 38 := by ring
    _ ≤ 13 / 10 * rt64 H ^ 64 :=
        mono_step (rt64 H) _ (13 / 10) 38 64 (by norm_num) (rt64_ge H hH)
          (by norm_num) (by norm_num) (by norm_num)

theorem piece7 (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    Real.log ((upar H : ℝ) * (vpar H : ℝ)) * (4 * (qcut H : ℝ))
        * (2 + Real.log (2 * (qcut H : ℝ))) * Real.log (H : ℝ)
      ≤ 1 / 1000 * rt64 H ^ 64 := by
  calc Real.log ((upar H : ℝ) * (vpar H : ℝ)) * (4 * (qcut H : ℝ))
        * (2 + Real.log (2 * (qcut H : ℝ))) * Real.log (H : ℝ)
      ≤ (10 * rt64 H ^ 2) * (4 * rt64 H ^ 32) * (6 * rt64 H ^ 2) * (10 * rt64 H ^ 2) :=
        m4 (log_upar_vpar_nonneg H hH) (by positivity)
          (two_add_logq_nonneg H hH) (log_pos' H hH).le
          (le_trans (log_upar_vpar_le H hH) (log_le_ten H hH)) (by linarith [qcut_le H])
          (two_add_logq_le6 H hH) (log_le_ten H hH)
    _ = 2400 * rt64 H ^ 38 := by ring
    _ ≤ 1 / 1000 * rt64 H ^ 64 :=
        mono_step (rt64 H) 2400 (1 / 1000) 38 64 (by norm_num) (rt64_ge H hH)
          (by norm_num) (by norm_num) (by norm_num)

theorem piece8 (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    (vpar H : ℝ) * Real.log (vpar H : ℝ) * Real.log (H : ℝ) ≤ 1 / 1000 * rt64 H ^ 64 := by
  calc (vpar H : ℝ) * Real.log (vpar H : ℝ) * Real.log (H : ℝ)
      ≤ (196 * rt64 H ^ 16) * (10 * rt64 H ^ 2) * (10 * rt64 H ^ 2) :=
        m3 (Nat.cast_nonneg _) (log_vpar_nonneg H hH) (log_pos' H hH).le
          (vpar_real_le H) (le_trans (log_vpar_le H hH) (log_le_ten H hH)) (log_le_ten H hH)
    _ = 19600 * rt64 H ^ 20 := by ring
    _ ≤ 1 / 1000 * rt64 H ^ 64 :=
        mono_step (rt64 H) 19600 (1 / 1000) 20 64 (by norm_num) (rt64_ge H hH)
          (by norm_num) (by norm_num) (by norm_num)

/-- **The `1/√V` term.** `log H·4√10·H/√(V+1)·log H ≤ 1.6·H`: the term that wants `V` large.
Computed `1.516`. -/
theorem piece9 (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    Real.log (H : ℝ) * (4 * Real.sqrt 10 * (H : ℝ) / Real.sqrt ((vpar H : ℝ) + 1))
        * Real.log (H : ℝ)
      ≤ 16 / 10 * rt64 H ^ 64 := by
  calc Real.log (H : ℝ) * (4 * Real.sqrt 10 * (H : ℝ) / Real.sqrt ((vpar H : ℝ) + 1))
        * Real.log (H : ℝ)
      ≤ (901 / 100 * rt64 H ^ 2) * (908 / 1000 * rt64 H ^ 56) * (901 / 100 * rt64 H ^ 2) :=
        m3 (log_pos' H hH).le (by positivity) (log_pos' H hH).le
          (log_le_rt32 H hH) (quot_vpar_le H hH) (log_le_rt32 H hH)
    _ = (901 / 100 * (908 / 1000) * (901 / 100)) * rt64 H ^ 60 := by ring
    _ ≤ 16 / 10 * rt64 H ^ 64 :=
        mono_step (rt64 H) _ (16 / 10) 60 64 (by norm_num) (rt64_ge H hH)
          (by norm_num) (by norm_num) (by norm_num)

theorem piece10 (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    Real.log (H : ℝ)
        * (Real.sqrt 32 * (H : ℝ) * ((Nat.log 2 H + 1 : ℕ) : ℝ) / Real.sqrt (pcut H : ℝ))
        * Real.log (H : ℝ)
      ≤ 4 / 10 * rt64 H ^ 64 := by
  calc Real.log (H : ℝ)
        * (Real.sqrt 32 * (H : ℝ) * ((Nat.log 2 H + 1 : ℕ) : ℝ) / Real.sqrt (pcut H : ℝ))
        * Real.log (H : ℝ)
      ≤ (901 / 100 * rt64 H ^ 2) * (746 / 10 * rt64 H ^ 50) * (901 / 100 * rt64 H ^ 2) :=
        m3 (log_pos' H hH).le (by positivity) (log_pos' H hH).le
          (log_le_rt32 H hH) (quot_pcut_le H hH) (log_le_rt32 H hH)
    _ = (901 / 100 * (746 / 10) * (901 / 100)) * rt64 H ^ 54 := by ring
    _ ≤ 4 / 10 * rt64 H ^ 64 :=
        mono_step (rt64 H) _ (4 / 10) 54 64 (by norm_num) (rt64_ge H hH)
          (by norm_num) (by norm_num) (by norm_num)

/-- **The `1/√U` term.** `log H·64H√(1+log 2q)/√U·log H ≤ 2.2·H`: the term that wants `U` large.
Computed `2.0992`. -/
theorem piece11 (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    Real.log (H : ℝ)
        * (64 * (H : ℝ) * Real.sqrt (1 + Real.log (2 * (qcut H : ℝ))) / Real.sqrt (upar H : ℝ))
        * Real.log (H : ℝ)
      ≤ 22 / 10 * rt64 H ^ 64 := by
  calc Real.log (H : ℝ)
        * (64 * (H : ℝ) * Real.sqrt (1 + Real.log (2 * (qcut H : ℝ))) / Real.sqrt (upar H : ℝ))
        * Real.log (H : ℝ)
      ≤ (901 / 100 * rt64 H ^ 2) * (476 / 1000 * rt64 H ^ 57) * (901 / 100 * rt64 H ^ 2) :=
        m3 (log_pos' H hH).le (by positivity) (log_pos' H hH).le
          (log_le_rt32 H hH) (quot_upar_le H hH) (log_le_rt32 H hH)
    _ = (901 / 100 * (476 / 1000) * (901 / 100)) * rt64 H ^ 61 := by ring
    _ ≤ 22 / 10 * rt64 H ^ 64 :=
        mono_step (rt64 H) _ (22 / 10) 61 64 (by norm_num) (rt64_ge H hH)
          (by norm_num) (by norm_num) (by norm_num)

/-- **The `√(Hq)` term.** `log H·6k√(HQ(1+log 2Q))·log H ≤ 2.4·H`: the term that wants `Q` small,
and the reason the cutoffs cannot be pushed apart. Computed `2.2907`. -/
theorem piece12 (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    Real.log (H : ℝ) * (6 * ((Nat.log 2 H + 1 : ℕ) : ℝ)
        * Real.sqrt ((H : ℝ) * (qcut H : ℝ) * (1 + Real.log (2 * (qcut H : ℝ)))))
        * Real.log (H : ℝ)
      ≤ 24 / 10 * rt64 H ^ 64 := by
  calc Real.log (H : ℝ) * (6 * ((Nat.log 2 H + 1 : ℕ) : ℝ)
        * Real.sqrt ((H : ℝ) * (qcut H : ℝ) * (1 + Real.log (2 * (qcut H : ℝ)))))
        * Real.log (H : ℝ)
      = Real.log (H : ℝ) * 6 * ((Nat.log 2 H + 1 : ℕ) : ℝ)
        * Real.sqrt ((H : ℝ) * (qcut H : ℝ) * (1 + Real.log (2 * (qcut H : ℝ))))
        * Real.log (H : ℝ) := by ring
    _ ≤ (901 / 100 * rt64 H ^ 2) * 6 * (1316 / 100 * rt64 H ^ 2)
          * (2227 / 1000 * rt64 H ^ 49) * (901 / 100 * rt64 H ^ 2) :=
        m5 (log_pos' H hH).le (by norm_num) (natlog_succ_nonneg H) (Real.sqrt_nonneg _)
          (log_pos' H hH).le (log_le_rt32 H hH) (le_refl _) (natlog_succ_le H hH)
          (sqrt_HQ_le H hH) (log_le_rt32 H hH)
    _ = (901 / 100 * 6 * (1316 / 100) * (2227 / 1000) * (901 / 100)) * rt64 H ^ 55 := by ring
    _ ≤ 24 / 10 * rt64 H ^ 64 :=
        mono_step (rt64 H) _ (24 / 10) 55 64 (by norm_num) (rt64_ge H hH)
          (by norm_num) (by norm_num) (by norm_num)

/-! ## The envelope, assembled

`κ₀ = 10` against a budget total of `7.926`. The slack is deliberate: it is what makes every
`mono_step` side condition a `norm_num` and not a fight. -/

set_option maxHeartbeats 1000000 in
-- the final `linarith` ring-normalises a goal of about forty monomials against twelve
-- piece bounds; 200000 heartbeats is not enough for that one call.
/-- **The envelope inequality at the chosen parameters**: for every minor modulus `P < q ≤ Q`,
`tightSupRHS q U V H ≤ 10·H/log H`, uniformly for `H ≥ 10^27`. This is the whole remaining
obligation of `Spine.MinorSupBound` after `MinorArc.minor_sup_uniform`. -/
theorem tightSupRHS_envelope (H : ℕ) (hH : 10 ^ 27 ≤ H) (q : ℕ)
    (hPq : pcut H < q) (hqQ : q ≤ qcut H) :
    MinorArc.tightSupRHS q (upar H) (vpar H) H ≤ 10 * (H : ℝ) / Real.log (H : ℝ) := by
  have hH1 : 1 ≤ H := le_trans (by norm_num) hH
  refine le_trans (MinorArc.tightSupRHS_le H (upar H) (vpar H) (pcut H) (qcut H) q
    hH1 (pcut_pos H hH) (one_le_upar H hH) (one_le_vpar H hH) hPq hqQ) ?_
  rw [le_div_iff₀ (log_pos' H hH)]
  have h64 := rt64_pow64 H
  have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  linarith [piece1 H hH, piece2 H hH, piece3 H hH, piece4 H hH, piece5 H hH, piece6 H hH,
    piece7 H hH, piece8 H hH, piece9 H hH, piece10 H hH, piece11 H hH, piece12 H hH]

/-! ## The link

`Spine.minorSupBound_of_envelope` cannot be used: its hypotheses are quantified over *all* `H`,
and at `H = 0` they are contradictory (`hU 0 : U 0 ≤ 0` forces `U 0 = 0`, and then
`hUV1 0 : 1 ≤ U 0 * V 0` is false), so no `U`, `V` satisfy them. That is recorded as a theorem
below. `minorSupBound_of_envelope'` is the same one-line composition with every hypothesis
restricted to `10^27 ≤ H`, which is all `MinorSupBound` quantifies over. -/

/-- **The interface defect, as a theorem.** No pair `U V : ℕ → ℕ` satisfies both `∀ H, U H ≤ H`
and `∀ H, 1 ≤ U H * V H`, so `Spine.minorSupBound_of_envelope`'s hypotheses are jointly
unsatisfiable and the lemma is unusable as stated. The obstruction is only `H = 0`. -/
theorem envelope_hyps_unsatisfiable :
    ¬ ∃ U V : ℕ → ℕ, (∀ H : ℕ, U H ≤ H) ∧ (∀ H : ℕ, 1 ≤ U H * V H) := by
  rintro ⟨U, V, hU, hUV1⟩
  have h0 : U 0 = 0 := Nat.le_zero.mp (hU 0)
  have h1 := hUV1 0
  rw [h0] at h1
  simp at h1

/-- **The repaired reduction.** `MinorArc.minor_sup_uniform` applied at each `H ≥ 10^27`; the
hypotheses are exactly `Spine.minorSupBound_of_envelope`'s, restricted to the range
`MinorSupBound` speaks about. `MinorSupBound` is *not* weakened: the statement proved is
`Spine.MinorSupBound P Q κ` verbatim. -/
theorem minorSupBound_of_envelope' (P Q U V : ℕ → ℕ) (κ : ℝ)
    (hP : ∀ H : ℕ, 10 ^ 27 ≤ H → 0 < P H) (hPQ : ∀ H : ℕ, 10 ^ 27 ≤ H → P H ≤ Q H)
    (hU : ∀ H : ℕ, 10 ^ 27 ≤ H → U H ≤ H) (hUV : ∀ H : ℕ, 10 ^ 27 ≤ H → U H * V H ≤ H)
    (hUV1 : ∀ H : ℕ, 10 ^ 27 ≤ H → 1 ≤ U H * V H)
    (henv : ∀ H : ℕ, 10 ^ 27 ≤ H → ∀ q : ℕ, P H < q → q ≤ Q H →
      MinorArc.tightSupRHS q (U H) (V H) H ≤ κ * (H : ℝ) / Real.log (H : ℝ)) :
    Spine.MinorSupBound P Q κ := fun H _ hH α hα =>
  MinorArc.minor_sup_uniform H (P H) (Q H) (U H) (V H) (hP H hH) (hPQ H hH) (hU H hH)
    (hUV H hH) (hUV1 H hH) (κ * (H : ℝ) / Real.log (H : ℝ))
    (fun r h1 h2 => henv H hH r h1 h2) α hα

/-- **THE LINK, INSTANTIATED AND PROVED.** `Spine.MinorSupBound` holds at the cutoffs
`P = ⌊√H⌋ − 1`, `Q = ⌊√H⌋` with `κ₀ = 10`, i.e.

  `‖∑_{0<n≤H} Λ(n)e(nα)‖ ≤ 10·H/log H` for every `α` off the major arcs, every odd `H ≥ 10^27`.

The minor set at these cutoffs is non-empty (`minorSet_nonempty`), so the statement is not
vacuous. `10` decomposes as: `4.35` the honest optimum of the underlying estimate
(`max_{P<q≤Q} tightSupRHS` at its best `(P,Q,U,V)`), `6.81` after the `q`-uniform envelope
`MinorArc.tightSupRHS_le` (which costs a factor `2` on the two Type-I block terms, by bounding
`⌊U/⌊q/2⌋⌋ ≤ 4U/q` instead of `2U/q`, and a factor `4.3` on the two `k`-terms, by replacing
`log₂(N/(V+1)) − log₂(U+1) + 1 = 21` with `log₂ N + 1 = 90`), `7.93` after the Lean-side
log-versus-power bounds, and `10` as the rounded budget. **None of that matters for the verdict:
the demanded `κ` is `0.46`.** -/
theorem minorSupBound_library : Spine.MinorSupBound pcut qcut 10 :=
  minorSupBound_of_envelope' pcut qcut upar vpar 10
    (fun H hH => pcut_pos H hH)
    (fun H hH => le_of_lt (pcut_lt_qcut H hH))
    (fun H hH => upar_le H hH)
    (fun H hH => upar_mul_vpar_le H hH)
    (fun H hH => one_le_upar_mul_vpar H hH)
    (fun H hH r h1 h2 => tightSupRHS_envelope H hH r h1 h2)

/-! ## The shortfall -/

/-- **The shortfall, trivially.** The sharp arrangement of the spine
(`Spine.ternaryLogCountLower_of_links_sharp`) can afford `κ = 46/100`; the main arrangement can
afford `3/10`. What is proved is `10`. -/
theorem shortfall : (46 : ℝ) / 100 < 10 := by norm_num

theorem shortfall_main : (3 : ℝ) / 10 < 10 := by norm_num

/-- Every summand of `tightSupRHS` except the `1/√(V+1)` Type-II term is non-negative, so that
one term is a lower bound. Needs only `q ≥ 2`, `U, V, N ≥ 1`. -/
theorem tightSupRHS_ge_sqrtV (q U V N : ℕ) (hq : 2 ≤ q) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hN : 1 ≤ N) :
    Real.log (N : ℝ) * (4 * Real.sqrt 10 * (N : ℝ) / Real.sqrt ((V : ℝ) + 1))
      ≤ MinorArc.tightSupRHS q U V N := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hUR : (1 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU
  have hVR : (1 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hV
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlU : (0 : ℝ) ≤ Real.log (U : ℝ) := Real.log_nonneg hUR
  have hlV : (0 : ℝ) ≤ Real.log (V : ℝ) := Real.log_nonneg hVR
  have hlN : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg hNR
  have hlN1 : (0 : ℝ) ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hlUV : (0 : ℝ) ≤ Real.log ((U : ℝ) * (V : ℝ)) :=
    Real.log_nonneg (by nlinarith)
  have hl2q : (0 : ℝ) ≤ Real.log (2 * (q : ℝ)) := Real.log_nonneg (by linarith)
  have hblk : (0 : ℝ) ≤ 2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q)) := by nlinarith
  have hb1 : (0 : ℝ) ≤ ((U / (q / 2) + 1 : ℕ) : ℝ)
      * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q))) :=
    mul_nonneg (Nat.cast_nonneg _) hblk
  have hb2 : (0 : ℝ) ≤ ((U * V / (q / 2) + 1 : ℕ) : ℝ)
      * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q))) :=
    mul_nonneg (Nat.cast_nonneg _) hblk
  have hA : (0 : ℝ) ≤ 2 * Real.log ((N : ℝ) + 1) *
      (((2 * (N : ℝ) / q) * (1 + Real.log (U : ℝ)) + ((U / (q / 2) + 1 : ℕ) : ℝ)
        * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q)))) + (U : ℝ)) := by
    refine mul_nonneg (by linarith) ?_
    have : (0 : ℝ) ≤ (2 * (N : ℝ) / q) * (1 + Real.log (U : ℝ)) := by positivity
    linarith
  have hB : (0 : ℝ) ≤ Real.log ((U : ℝ) * (V : ℝ)) *
      ((2 * (N : ℝ) / q) * (1 + Real.log ((U : ℝ) * (V : ℝ)))
        + ((U * V / (q / 2) + 1 : ℕ) : ℝ)
          * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q)))) := by
    refine mul_nonneg hlUV ?_
    have : (0 : ℝ) ≤ (2 * (N : ℝ) / q) * (1 + Real.log ((U : ℝ) * (V : ℝ))) := by positivity
    linarith
  have hC : (0 : ℝ) ≤ (V : ℝ) * Real.log (V : ℝ) := mul_nonneg (by linarith) hlV
  have hd2 : (0 : ℝ) ≤ Real.sqrt 32 * (N : ℝ)
      * ((Nat.log 2 (N / (V + 1)) - Nat.log 2 (U + 1) + 1 : ℕ) : ℝ) / Real.sqrt q := by
    positivity
  have hd3 : (0 : ℝ) ≤ 64 * (N : ℝ) * Real.sqrt (1 + Real.log (2 * (q : ℝ))) / Real.sqrt U := by
    positivity
  have hd4 : (0 : ℝ) ≤ 6 * ((Nat.log 2 (N / (V + 1)) - Nat.log 2 (U + 1) + 1 : ℕ) : ℝ)
      * Real.sqrt ((N : ℝ) * (q : ℝ) * (1 + Real.log (2 * (q : ℝ)))) := by positivity
  unfold MinorArc.tightSupRHS
  have hp2 : (0 : ℝ) ≤ Real.log (N : ℝ) * (Real.sqrt 32 * (N : ℝ)
      * ((Nat.log 2 (N / (V + 1)) - Nat.log 2 (U + 1) + 1 : ℕ) : ℝ) / Real.sqrt q) :=
    mul_nonneg hlN hd2
  have hp3 : (0 : ℝ) ≤ Real.log (N : ℝ)
      * (64 * (N : ℝ) * Real.sqrt (1 + Real.log (2 * (q : ℝ))) / Real.sqrt U) :=
    mul_nonneg hlN hd3
  have hp4 : (0 : ℝ) ≤ Real.log (N : ℝ) * (6 * ((Nat.log 2 (N / (V + 1))
      - Nat.log 2 (U + 1) + 1 : ℕ) : ℝ)
      * Real.sqrt ((N : ℝ) * (q : ℝ) * (1 + Real.log (2 * (q : ℝ))))) :=
    mul_nonneg hlN hd4
  nlinarith [hA, hB, hC, hp2, hp3, hp4]

/-- `⌊H^{1/8}⌋ ≤ 2371` for `H ≤ 10^27`: from `cpar H ^ 8 ≤ H` and `2372^8 > 10^27`. The exact
value of `Nat.sqrt (Nat.sqrt (Nat.sqrt (10^27)))` is never needed. -/
theorem cpar_le_2371 (H : ℕ) (hH : H ≤ 10 ^ 27) : cpar H ≤ 2371 := by
  by_contra hcon
  have h1 : 2372 ≤ cpar H := by omega
  have h2 : 2372 ^ 8 ≤ cpar H ^ 8 := Nat.pow_le_pow_left h1 8
  have h4 : (2372 : ℕ) ^ 8 ≤ 10 ^ 27 := le_trans (le_trans h2 (cpar_pow8_le H)) hH
  norm_num at h4

/-- `log H ≥ 61.6` for `H ≥ 10^27`, sharper than `Spine.log_ge_61` (the truth at the threshold is
`62.17`). From `2^89 ≤ 10^27` and `Real.log_two_gt_d9`: `89 · 0.6931471803 = 61.69`. -/
theorem log_ge_616 (H : ℕ) (hH : 10 ^ 27 ≤ H) : (616 : ℝ) / 10 ≤ Real.log (H : ℝ) := by
  have h2 : (2 : ℕ) ^ 89 ≤ H := le_trans (by norm_num) hH
  have h2R : (2 : ℝ) ^ 89 ≤ (H : ℝ) := by exact_mod_cast h2
  have hmono : Real.log ((2 : ℝ) ^ 89) ≤ Real.log (H : ℝ) :=
    Real.log_le_log (by positivity) h2R
  rw [Real.log_pow] at hmono
  have hl2 := Real.log_two_gt_d9
  push_cast at hmono
  nlinarith [hmono, hl2]

/-- **THE GAP IS IN THE ESTIMATE, NOT IN THE BOUNDING.** At `H = 10^27` and the chosen parameters
the tight Vaughan right-hand side, at the unique minor modulus `q = ⌊√H⌋`, is *at least*
`1.4·H/log H` — against the `0.46·H/log H` that the sharp spine arrangement can afford. The
shortfall is therefore a property of `MinSum.vinogradov_sup_tight2` itself: not of the `q`-uniform
envelope, not of the budget rounding, and not of the log-versus-power bounds — **at the parameter
point it fixes.** It quantifies over nothing (`H`, `U`, `V`, `q` all fixed), so it does NOT show
that no re-tuning of `(P,Q,U,V)` reaches `0.46`. An earlier version of this docstring, and commit
`4f2d1bc3`, claimed that; the claim is unproved, and the audit exhibits a box point where the single
term carrying this theorem falls below target. Whether the full envelope can be re-tuned below
`0.46` is OPEN.

One term carries it: `log H · 4√10 · H/√(V+1)`, with `√(V+1) ≤ 33195` (from `cpar_le_2371`) and
`log H ≥ 61.6`; `4·3.16·61.6² = 47963 ≥ 1.4·33195 = 46473`. -/
theorem tightSupRHS_lower (H : ℕ) (hH : H = 10 ^ 27) :
    ∃ r : ℕ, pcut H < r ∧ r ≤ qcut H ∧
      (14 : ℝ) / 10 * (H : ℝ) / Real.log (H : ℝ)
        ≤ MinorArc.tightSupRHS r (upar H) (vpar H) H := by
  have hlo : 10 ^ 27 ≤ H := by omega
  have hhi : H ≤ 10 ^ 27 := by omega
  refine ⟨qcut H, pcut_lt_qcut H hlo, le_refl _, ?_⟩
  have hq2 : 2 ≤ qcut H := natsqrt_pos H hlo
  have hH1 : 1 ≤ H := le_trans (by norm_num) hlo
  have hlow := tightSupRHS_ge_sqrtV (qcut H) (upar H) (vpar H) H hq2
    (one_le_upar H hlo) (one_le_vpar H hlo) hH1
  refine le_trans ?_ hlow
  have hCR : (cpar H : ℝ) ≤ 2371 := by exact_mod_cast cpar_le_2371 H hhi
  have hC0 : (0 : ℝ) ≤ (cpar H : ℝ) := Nat.cast_nonneg _
  have hVle : (vpar H : ℝ) + 1 ≤ (33195 : ℝ) ^ 2 := by
    rw [vpar_cast]; nlinarith [hCR, hC0]
  have hsV : Real.sqrt ((vpar H : ℝ) + 1) ≤ 33195 := sqrt_le_of_sq _ _ (by norm_num) hVle
  have hsVpos : (0 : ℝ) < Real.sqrt ((vpar H : ℝ) + 1) := by
    refine Real.sqrt_pos.mpr ?_
    have h : (0 : ℝ) ≤ (vpar H : ℝ) := Nat.cast_nonneg _
    linarith
  have hL := log_ge_616 H hlo
  have hLpos : (0 : ℝ) < Real.log (H : ℝ) := by linarith
  have hs10 : (316 : ℝ) / 100 ≤ Real.sqrt 10 := le_sqrt_of_sq _ _ (by norm_num) (by norm_num)
  have hHR : (0 : ℝ) < (H : ℝ) := by
    have h : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
    linarith
  rw [div_le_iff₀ hLpos]
  have key : (14 : ℝ) / 10 * (H : ℝ) * Real.sqrt ((vpar H : ℝ) + 1)
      ≤ 4 * Real.sqrt 10 * (H : ℝ) * Real.log (H : ℝ) ^ 2 := by
    have h1 : (14 : ℝ) / 10 * (H : ℝ) * Real.sqrt ((vpar H : ℝ) + 1)
        ≤ (14 : ℝ) / 10 * (H : ℝ) * 33195 :=
      mul_le_mul_of_nonneg_left hsV (by positivity)
    have hsq : ((616 : ℝ) / 10) ^ 2 ≤ Real.log (H : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hL 2
    have h2 : 4 * ((316 : ℝ) / 100) * (H : ℝ) * ((616 : ℝ) / 10) ^ 2
        ≤ 4 * Real.sqrt 10 * (H : ℝ) * Real.log (H : ℝ) ^ 2 := by
      have hpos : (0 : ℝ) ≤ 4 * ((316 : ℝ) / 100) * (H : ℝ) := by positivity
      have hA : 4 * ((316 : ℝ) / 100) * (H : ℝ) * ((616 : ℝ) / 10) ^ 2
          ≤ 4 * ((316 : ℝ) / 100) * (H : ℝ) * Real.log (H : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hpos
      have h0 : (0 : ℝ) ≤ (H : ℝ) * Real.log (H : ℝ) ^ 2 := by positivity
      have hB : 4 * ((316 : ℝ) / 100) * ((H : ℝ) * Real.log (H : ℝ) ^ 2)
          ≤ 4 * Real.sqrt 10 * ((H : ℝ) * Real.log (H : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) h0
      nlinarith [hA, hB]
    nlinarith [h1, h2, hHR]
  have hrw : Real.log (H : ℝ) * (4 * Real.sqrt 10 * (H : ℝ) / Real.sqrt ((vpar H : ℝ) + 1))
      * Real.log (H : ℝ)
      = 4 * Real.sqrt 10 * (H : ℝ) * Real.log (H : ℝ) ^ 2
        / Real.sqrt ((vpar H : ℝ) + 1) := by
    field_simp
  rw [hrw, le_div_iff₀ hsVpos]
  linarith [key]

/-! ## Non-triviality of what was proved -/

/-- **A real saving, but by `≈9×`, not `300×`.** `10·H/log H` beats
`Spine.expSum_sup_trivial : ‖S(α)‖ ≤ H log H` by `(log H)²/10 ≥ 372`, which is what this theorem
states. **That comparator is the wrong one** (round-3 audit): it is not the only free bound. The
triangle inequality plus Mathlib's `Chebyshev.psi_le` — which `Spine.lean` already cites for
`SecondMoment` — gives `‖expSum H α‖ ≤ log 4·H + 2√H log H` for EVERY `α`, with no minor-arc
hypothesis. Against that, `κ₀ = 10` saves about `9×`. So `minorSupBound_library` is still not a
restatement of something free, but the honest margin is one order of magnitude, not two and a
half. -/
theorem bound_below_trivial (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    300 * (10 * (H : ℝ) / Real.log (H : ℝ)) ≤ (H : ℝ) * Real.log (H : ℝ) := by
  have hL := log_ge H hH
  have hLpos := log_pos' H hH
  have hHR : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  rw [show 300 * (10 * (H : ℝ) / Real.log (H : ℝ)) = 3000 * (H : ℝ) / Real.log (H : ℝ) by ring,
    div_le_iff₀ hLpos]
  nlinarith [hL, hHR, mul_nonneg hHR hLpos.le]

/-- **The link, non-vacuously.** The two halves of the deliverable in one statement: the bound
holds, and the set it is a bound on is non-empty. -/
theorem minorSupBound_nonvacuous :
    Spine.MinorSupBound pcut qcut 10 ∧
      ∀ H : ℕ, 10 ^ 27 ≤ H → (Spine.minorSet (pcut H) (qcut H)).Nonempty :=
  ⟨minorSupBound_library, fun H hH => minorSet_nonempty H hH⟩

end Principia.Common.TernaryGoldbach.MinorArcBound
