/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.GorshSpine

set_option autoImplicit false

/-!
# The spine of the corrected `thm:ostop` (`OL.OstopL`) from its layer-2 links

**`OL.OstopL η₊ η* φ` is COMPOSED here; the named inputs below remain.** Target: `OL.OstopL`
(`OstopL.lean`), Helfgott's `thm:ostop` (`ternvin.tex` 3697-3994) with the F6/F7 repairs and the
corrected `L`. The proof of 3746-3994 is transcribed link by link; every generic step is PROVED.

## The spine

```
 Split   S_{η₊} = S₁ + S₂  (3829-3835), wherever Σ Λ(n)|η₊(n/x)| < ∞      splitLink    PROVED
 Parseval  ∫₀¹ |Σ aₙe(nα)|² = Σ|aₙ|²  for Σ|aₙ| < ∞                       parseval_Ioc PROVED
 Mink    Z ≤ (√Z₁ + √Z₂)²  (the weighted triangle inequality, 3840-3845)  mink, le_sq_* PROVED
 Z₂ ≤ S*(0,x)·Σ|b_n|² ≤ S*(0,x)·E  (3846-3890)        z2_le PROVED from   EBound2      NAMED
 levels  |S*(α)| ≤ G(R) + Σ_{r₀≤r<R}(G(r) − G(r+1))·1[α ∈ 𝔐^{(y)}_{r+1}]  on the minor arcs,
         from GorshL (off the y-arcs) and CoprarL (the annulus A₀)        level_bound  PROVED
 Z₁ ≤ G(R)(S − J₁) + Σ (G(r) − G(r+1))(C(r) − J₁)       C(r) = ∫_{𝔐^{(y)}_{r+1}}|S₁|²  z1_le
 PalanLink  lem:jardinbota at INTEGERS, top level exact, JUMP EXPLICIT    palanLink    PROVED
         G(b)(S−J) + Σ(G(r)−G(r+1))Φ(r) ≤ G(a)(H(a)S−J) + SΣ(H(r+1)−H(r))G(r+1) + S(1−H(b))G(b)
 CoeurY  C(r) ≤ H(r)·S  for r < r₁                                                      NAMED
 top_le  SΣ(H(r+1)−H(r))g(r+1) + S(1−H(R))g(R) ≤ S(2/D·∫_{r₀}^{r₁}g̃/r + coefC·g̃(r₁))
         from sum_int_sharp (GTMonoL), jump_le_coefC_of, TopStepL, floor_big             PROVED
 I0S     (√J − √E)² ≤ J₁ = I₀S  (3942-3962), needs E ≤ J (JgeE)           i0sLink      PROVED
 ostopL_of_links : Palan → Split → I0S → CoeurY → GorshL → GTMonoL → CoprarL → EBound2 →
                   JgeE → TopStepL → OL.OstopL η₊ η* φ
 ostopL_of_layer2 : the same on Helfgott's weights, the generic links discharged
 minorAt_layer2_cheb : OL.minorAt_ostopL_cheb with OstopL supplied by ostopL_of_layer2
```

## Three defects of the typed `OstopL`, found by composing it (each designed around, not hidden)

* **(D1) `r₁` is not an integer.** `prop:palan` sums over `r = r₀,…,r₁` (3659-3688), but
  `r₁ = (3/8)y^{4/15}`. The levels are the integer arcs `𝔐_{8,r}`, so the top level is
  `R = ⌊r₁⌋` and the proof bounds `|S*|` there by `g̃(R)`, not by the `g̃(r₁)` that `M̃` (`OL.mMCL`,
  and `OC.mMC`, `MinSp.mM` before it) types. Since `g̃(R) ≥ g̃(r₁)` the typed `M̃` is not what the
  proof gives. Repair: the telescoped slack of the sum-to-integral comparison
  (`sum_int_sharp`, `≈ g̃(R)/r₀`) pays for `coefC·(g̃(R) − g̃(r₁))` once `√r·g̃(r)` does not
  decrease across the last unit step, which is the NAMED numeric link `TopStepL`. Floating point
  (`scratchpad/ostops/topstep.py`, mpmath 30 digits, gtilde.gt with `lLc`): `d log g̃/d log r` at
  `r₁` is `−0.392` (`y = 10²⁵`), `−0.400` (`10³⁰`), `−0.420` (`10⁴⁰`), `−0.465` (`10¹⁰⁰`), all above
  `−1/2`; the exact top inequality holds with ratio `0.39` at the threshold. The arithmetic the
  composition then needs, `⌊r₁⌋ ≥ 150001(7D_h/30 + 1)`, is PROVED for every `x ≥ 4.9·10²⁶`
  (`floor_big`; ratio `1.475` at the threshold, growing like `y^{4/15}/log y`).
* **(D2) `I₀S ≥ (√J − √E)²` needs `√J ≥ √E`.** The step (3942-3962) is the reverse triangle
  inequality in `L²(𝔐)`; if `J < E` then `(√J − √E)² = (√E − √J)²` can exceed `J₁` (e.g. `J = 0`).
  Helfgott does not state the condition. It is the NAMED link `JgeE`, discharged on Helfgott's
  weights from the chain's own `OC.DrujalLowP J₀` (`J/x ≥ 8.57476`) and the PROVED `Dubistdie`
  (`E/x ≤ 8.4031·10⁻¹²`): `jgeE_helf`.
* **(D3) the `H`-jump.** `prop:palan` assumes `H` continuous with `H(r₁) = 1`; `thm:ostop`'s `H`
  jumps to `1`. `PalanLink` is the DISCRETE form: the top level's cumulative mass is exactly
  `S − J` (Parseval) and the jump term `S(1 − H(R))G(R)` is explicit. It is priced by
  `OC.coefC` through `log(R+1) ≥ log r₁` (`jump_le_coefC_of`, the proof of `OC.jump_le_coefC` with
  `r₁ + 1` replaced by any `t ≥ r₁`).

## EBound2 priced (the owner's Platt directive: prefer in-house)

`E` of `eq:georgic` rests on Rosser-Schoenfeld 1962 Thms 12-13 (`ψ(t) < 1.03883t`,
`ψ(t) − θ(t) < 1.42620√t`, all `t > 0`), NOT on Platt. `eBig` types `0.51942 = 1.03883/2` and
`0.7131 = 1.4262/2`. In-house: Principia's `ψ ≤ 1.11t` (`t ≥ 3·10⁹`, `Chebyshev/Upper.lean`)
prices the small-prime term at `0.555`, `+6.85 %` over `0.51942` (`+1.37 %` on `E` at the
threshold, `E/√x ≈ 186`); and neither Principia nor Mathlib has a uniform `ψ(t) − θ(t) ≤ c√t` for
all `t ≥ 1` (Mathlib's `ψ ≤ (log 4 + 4)t` has the wrong shape). So `eBig` as typed is out of
in-house reach and `EBound2` stays a NAMED citation. Numerically `E` is irrelevant (`≈ 10⁻¹¹x`),
but `Dubistdie`'s typed `8.4031·10⁻¹²` has margin `0.0035 %` (`8.40281`), so an in-house
restatement of `eBig` would ripple into `Dubistdie`, `MinSp.hex_le` and `OC.je_le_p`.

## Constants and margins

`coefC ≤ 7/15` (`coefC_le`: numerator `−3.538215 + (8/15)log 49 = −1.4626`, bounded by `−1.3201`
through `log 49 ≤ 6 log 2`; `coefC = 0.44181` at the threshold); `D_h = log√x − 1.306476 > 7`
(`dh_pos`; `29.4217` at the threshold); `⌊r₁⌋ ≥ 150001(7D_h/30 + 1)` (`floor_big`: `1740595` vs
`1179769`, margin `1.4754` at the threshold); the jump constant `−3.538215` is `OC.jump_le`'s
(exact `−3.53821589`); `J/E ≥ 8.57476/8.4031·10⁻¹² ≈ 1.02·10¹²` (`jgeE_helf`).
-/

namespace Principia.Common.TernaryGoldbach.OS

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach
open scoped ArithmeticFunction

/-! ## (1) Exponential sums over `ℕ`: continuity and Parseval -/

/-- **`∑ₙ aₙ e(nα)`**, an exponential sum over `n : ℕ` with arbitrary coefficients. -/
noncomputable def eSum (a : ℕ → ℂ) (α : ℝ) : ℂ := ∑' n : ℕ, a n * e ((n : ℝ) * α)

/-- **The partial sum `∑_{n<N} aₙ e(nα)`**. -/
noncomputable def pSum (a : ℕ → ℂ) (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, a n * e ((n : ℝ) * α)

/-- `‖aₙ e(nα)‖ = ‖aₙ‖`. -/
theorem norm_term (a : ℕ → ℂ) (n : ℕ) (α : ℝ) : ‖a n * e ((n : ℝ) * α)‖ = ‖a n‖ := by
  rw [norm_mul, e_norm, mul_one]

/-- Absolute summability of the coefficients gives summability at every `α`. -/
theorem summable_term (a : ℕ → ℂ) (ha : Summable fun n => ‖a n‖) (α : ℝ) :
    Summable fun n => a n * e ((n : ℝ) * α) :=
  summable_norm_iff.mp (ha.congr fun n => (norm_term a n α).symm)

/-- **Junk**: if `∑‖aₙ‖` diverges the sum is `0` at EVERY `α` (summability in `ℂ` is absolute,
and `‖aₙe(nα)‖ = ‖aₙ‖` does not see `α`). -/
theorem eSum_junk (a : ℕ → ℂ) (h : ¬ Summable fun n => ‖a n‖) (α : ℝ) : eSum a α = 0 := by
  unfold eSum
  refine tsum_eq_zero_of_not_summable fun hs => h ?_
  exact (summable_norm_iff.mpr hs).congr fun n => norm_term a n α

/-- **`eSum a` is continuous, unconditionally**: a uniform limit if `∑‖aₙ‖ < ∞`, junk `0`
otherwise. -/
theorem eSum_continuous (a : ℕ → ℂ) : Continuous (eSum a) := by
  by_cases h : Summable fun n => ‖a n‖
  · change Continuous fun α : ℝ => ∑' n : ℕ, a n * e ((n : ℝ) * α)
    refine continuous_tsum (fun n => ?_) h fun n α => le_of_eq (norm_term a n α)
    unfold e
    fun_prop
  · have h0 : eSum a = fun _ => 0 := funext (eSum_junk a h)
    rw [h0]
    exact continuous_const

/-- `‖∑ₙ aₙe(nα)‖ ≤ ∑‖aₙ‖`. -/
theorem norm_eSum_le (a : ℕ → ℂ) (ha : Summable fun n => ‖a n‖) (α : ℝ) :
    ‖eSum a α‖ ≤ ∑' n, ‖a n‖ := by
  unfold eSum
  refine le_trans (norm_tsum_le_tsum_norm ?_) (le_of_eq (tsum_congr fun n => norm_term a n α))
  exact ha.congr fun n => (norm_term a n α).symm

/-- `pSum a N` is continuous. -/
theorem pSum_continuous (a : ℕ → ℂ) (N : ℕ) : Continuous (pSum a N) := by
  unfold pSum
  refine continuous_finsetSum _ fun n _ => ?_
  unfold e
  fun_prop

/-- **Parseval for an absolutely summable exponential sum**: `∫₀¹‖∑ₙaₙe(nα)‖² = ∑ₙ‖aₙ‖²`, the
limit of the finite identity `MinorArc.parseval` (the partial sums converge uniformly, with
`|‖S‖² − ‖S_N‖²| ≤ 2(∑‖aₙ‖)·∑_{n≥N}‖aₙ‖`). -/
theorem parseval_eSum (a : ℕ → ℂ) (ha : Summable fun n => ‖a n‖) :
    ∫ α in (0 : ℝ)..1, ‖eSum a α‖ ^ 2 = ∑' n, ‖a n‖ ^ 2 := by
  have hA0 : 0 ≤ ∑' n, ‖a n‖ := tsum_nonneg fun n => norm_nonneg _
  have hle : ∀ n, ‖a n‖ ≤ ∑' n, ‖a n‖ := fun n => ha.le_tsum n fun m _ => norm_nonneg _
  have hsq : Summable fun n => ‖a n‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
      (ha.mul_right (∑' n, ‖a n‖))
    have h1 := hle n
    have h2 := norm_nonneg (a n)
    nlinarith
  have htail : ∀ (N : ℕ) (α : ℝ), ‖eSum a α - pSum a N α‖ ≤ ∑' k, ‖a (k + N)‖ := by
    intro N α
    have h : (∑ i ∈ Finset.range N, a i * e ((i : ℝ) * α)) +
        ∑' i, a (i + N) * e (((i + N : ℕ) : ℝ) * α) = ∑' i, a i * e ((i : ℝ) * α) :=
      (summable_term a ha α).sum_add_tsum_nat_add N
    have e1 : eSum a α - pSum a N α = ∑' k, a (k + N) * e (((k + N : ℕ) : ℝ) * α) := by
      unfold eSum pSum
      rw [← h]
      ring
    rw [e1]
    have hs2 : Summable fun k => ‖a (k + N)‖ := (summable_nat_add_iff N).mpr ha
    refine le_trans (norm_tsum_le_tsum_norm ?_)
      (le_of_eq (tsum_congr fun k => norm_term a (k + N) α))
    exact hs2.congr fun k => (norm_term a (k + N) α).symm
  have hPn : ∀ (N : ℕ) (α : ℝ), ‖pSum a N α‖ ≤ ∑' n, ‖a n‖ := by
    intro N α
    unfold pSum
    calc ‖∑ n ∈ Finset.range N, a n * e ((n : ℝ) * α)‖
        ≤ ∑ n ∈ Finset.range N, ‖a n * e ((n : ℝ) * α)‖ := norm_sum_le _ _
      _ = ∑ n ∈ Finset.range N, ‖a n‖ := Finset.sum_congr rfl fun n _ => norm_term a n α
      _ ≤ ∑' n, ‖a n‖ := ha.sum_le_tsum _ fun n _ => norm_nonneg _
  have hdiff : ∀ (N : ℕ) (α : ℝ),
      |‖pSum a N α‖ ^ 2 - ‖eSum a α‖ ^ 2| ≤ 2 * (∑' n, ‖a n‖) * ∑' k, ‖a (k + N)‖ := by
    intro N α
    have e2 : ‖pSum a N α‖ ^ 2 - ‖eSum a α‖ ^ 2 =
        (‖pSum a N α‖ + ‖eSum a α‖) * (‖pSum a N α‖ - ‖eSum a α‖) := by ring
    have hd : |‖pSum a N α‖ - ‖eSum a α‖| ≤ ∑' k, ‖a (k + N)‖ := by
      rw [abs_sub_comm]
      exact le_trans (abs_norm_sub_norm_le _ _) (htail N α)
    have hs : ‖pSum a N α‖ + ‖eSum a α‖ ≤ 2 * ∑' n, ‖a n‖ := by
      linarith [hPn N α, norm_eSum_le a ha α]
    rw [e2, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact mul_le_mul hs hd (abs_nonneg _) (by linarith)
  have hcS : Continuous fun α => ‖eSum a α‖ ^ 2 := ((eSum_continuous a).norm).pow 2
  have hcP : ∀ N : ℕ, Continuous fun α => ‖pSum a N α‖ ^ 2 := fun N =>
    ((pSum_continuous a N).norm).pow 2
  have hint : ∀ N : ℕ, ‖(∫ α in (0 : ℝ)..1, ‖pSum a N α‖ ^ 2) -
      ∫ α in (0 : ℝ)..1, ‖eSum a α‖ ^ 2‖ ≤ 2 * (∑' n, ‖a n‖) * ∑' k, ‖a (k + N)‖ := by
    intro N
    rw [← intervalIntegral.integral_sub ((hcP N).intervalIntegrable 0 1)
      (hcS.intervalIntegrable 0 1)]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (f := fun α => ‖pSum a N α‖ ^ 2 - ‖eSum a α‖ ^ 2) fun α _ => by
        rw [Real.norm_eq_abs]
        exact hdiff N α
    simpa using h
  have hlim1 : Filter.Tendsto (fun N : ℕ => ∫ α in (0 : ℝ)..1, ‖pSum a N α‖ ^ 2) Filter.atTop
      (nhds (∫ α in (0 : ℝ)..1, ‖eSum a α‖ ^ 2)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have ht := (tendsto_sum_nat_add fun n => ‖a n‖).const_mul (2 * ∑' n, ‖a n‖)
    rw [mul_zero] at ht
    exact squeeze_zero (fun N => norm_nonneg _) hint ht
  have hlim2 : Filter.Tendsto (fun N : ℕ => ∫ α in (0 : ℝ)..1, ‖pSum a N α‖ ^ 2) Filter.atTop
      (nhds (∑' n, ‖a n‖ ^ 2)) :=
    hsq.hasSum.tendsto_sum_nat.congr fun N => (MinorArc.parseval a N).symm
  exact tendsto_nhds_unique hlim1 hlim2

/-- **Parseval on the fundamental domain `(0,1]`**. -/
theorem parseval_Ioc (a : ℕ → ℂ) (ha : Summable fun n => ‖a n‖) :
    ∫ α in Set.Ioc (0 : ℝ) 1, ‖eSum a α‖ ^ 2 = ∑' n, ‖a n‖ ^ 2 := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  exact parseval_eSum a ha

/-! ## (2) Link [Split] — `S_{η₊} = S_{1,η₊} + S_{2,η₊}` (3829-3835), PROVED -/

/-- The coefficients of `S_η(α,x)`: `Λ(n)η(n/x)`. -/
noncomputable def aP (η : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℂ :=
  ((Λ n : ℝ) : ℂ) * ((η ((n : ℝ) / x) : ℝ) : ℂ)

open Classical in
/-- The coefficients of `S_{1,η}` (`OC.s1Sum`): `(log p)η(p/x)` on the primes `p > √x`. -/
noncomputable def a1 (η : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℂ :=
  if n.Prime ∧ Real.sqrt x < (n : ℝ) then ((Real.log n : ℝ) : ℂ) * ((η ((n : ℝ) / x) : ℝ) : ℂ)
  else 0

open Classical in
/-- The coefficients of `S_{2,η}`: `Λ(n)η(n/x)` at every `n` that is not a prime `> √x`. -/
noncomputable def a2 (η : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℂ :=
  if n.Prime ∧ Real.sqrt x < (n : ℝ) then 0 else aP η x n

open Classical in
/-- **`S_{2,η₊}(α,x)`** (3831-3833): the non-prime `n > √x` and all `n ≤ √x`, i.e. every `n`
that is not a prime `> √x`. -/
noncomputable def s2Sum (η : ℝ → ℝ) (x α : ℝ) : ℂ :=
  ∑' n : ℕ, if n.Prime ∧ Real.sqrt x < (n : ℝ) then 0 else
    ((Λ n : ℝ) : ℂ) * ((η ((n : ℝ) / x) : ℝ) : ℂ) * e ((n : ℝ) * α)

open Classical in
/-- **`∫₀¹|S_{2,η₊}|² = ∑_{n not a prime > √x} Λ(n)²η₊(n/x)²`**, the quantity `E` bounds
(3855-3888). -/
noncomputable def s2Sq (η : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, if n.Prime ∧ Real.sqrt x < (n : ℝ) then 0 else Λ n ^ 2 * η ((n : ℝ) / x) ^ 2

/-- `S_η` IS `eSum` of its coefficients, by `rfl`. -/
theorem smSum_eq (η : ℝ → ℝ) (x α : ℝ) : Smooth.smSum η x α = eSum (aP η x) α := rfl

/-- `S_{1,η}` is `eSum` of `a1`. -/
theorem s1Sum_eq (η : ℝ → ℝ) (x α : ℝ) : OC.s1Sum η x α = eSum (a1 η x) α := by
  unfold OC.s1Sum eSum a1
  refine tsum_congr fun n => ?_
  split_ifs <;> ring

/-- `S_{2,η}` is `eSum` of `a2`. -/
theorem s2Sum_eq (η : ℝ → ℝ) (x α : ℝ) : s2Sum η x α = eSum (a2 η x) α := by
  unfold s2Sum eSum a2 aP
  refine tsum_congr fun n => ?_
  split_ifs <;> ring

/-- `‖Λ(n)η(n/x)‖ = Λ(n)|η(n/x)|`. -/
theorem norm_aP (η : ℝ → ℝ) (x : ℝ) (n : ℕ) : ‖aP η x n‖ = Λ n * |η ((n : ℝ) / x)| := by
  unfold aP
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg vonMangoldt_nonneg]

/-- `‖a1‖ ≤ ‖aP‖` (`Λ(p) = log p`). -/
theorem norm_a1_le (η : ℝ → ℝ) (x : ℝ) (n : ℕ) : ‖a1 η x n‖ ≤ ‖aP η x n‖ := by
  unfold a1
  split_ifs with h
  · rw [norm_aP, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, vonMangoldt_apply_prime h.1, abs_of_nonneg (Real.log_natCast_nonneg n)]
  · rw [norm_zero]
    exact norm_nonneg _

/-- `‖a2‖ ≤ ‖aP‖`. -/
theorem norm_a2_le (η : ℝ → ℝ) (x : ℝ) (n : ℕ) : ‖a2 η x n‖ ≤ ‖aP η x n‖ := by
  unfold a2
  split_ifs
  · rw [norm_zero]
    exact norm_nonneg _
  · exact le_rfl

/-- `∑‖a1‖ < ∞` when `∑‖aP‖ < ∞`. -/
theorem summable_a1 (η : ℝ → ℝ) (x : ℝ) (hs : Summable fun n => ‖aP η x n‖) :
    Summable fun n => ‖a1 η x n‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_a1_le η x) hs

/-- `∑‖a2‖ < ∞` when `∑‖aP‖ < ∞`. -/
theorem summable_a2 (η : ℝ → ℝ) (x : ℝ) (hs : Summable fun n => ‖aP η x n‖) :
    Summable fun n => ‖a2 η x n‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_a2_le η x) hs

/-- `∑‖a1‖² = S` (`MinSp.sPr`). -/
theorem sq_a1 (η : ℝ → ℝ) (x : ℝ) : ∑' n, ‖a1 η x n‖ ^ 2 = MinSp.sPr η x := by
  unfold MinSp.sPr
  refine tsum_congr fun n => ?_
  unfold a1
  split_ifs
  · rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      mul_pow, sq_abs, sq_abs]
  · rw [norm_zero]
    ring

/-- `∑‖a2‖² = s2Sq`. -/
theorem sq_a2 (η : ℝ → ℝ) (x : ℝ) : ∑' n, ‖a2 η x n‖ ^ 2 = s2Sq η x := by
  unfold s2Sq
  refine tsum_congr fun n => ?_
  unfold a2
  split_ifs
  · rw [norm_zero]
    ring
  · rw [norm_aP, mul_pow, sq_abs]

/-- **Link [Split]** (3829-3835): wherever `∑Λ(n)|η(n/x)|` converges, `S_η = S_{1,η} + S_{2,η}`
pointwise. PROVED (`splitLink`). Where it diverges `S_η` is junk `0` at every `α`
(`eSum_junk`), which the composition treats separately (`Z = 0` there). -/
def SplitLink : Prop :=
  ∀ (η : ℝ → ℝ) (x : ℝ), (Summable fun n => ‖aP η x n‖) → ∀ α : ℝ,
    Smooth.smSum η x α = OC.s1Sum η x α + s2Sum η x α

/-- **[Split] PROVED**: termwise `Λ(n)η = a1 + a2` (`Λ(p) = log p`), both parts summable. -/
theorem splitLink : SplitLink := by
  intro η x hs α
  rw [smSum_eq, s1Sum_eq, s2Sum_eq]
  unfold eSum
  rw [← (summable_term _ (summable_a1 η x hs) α).tsum_add
    (summable_term _ (summable_a2 η x hs) α)]
  refine tsum_congr fun n => ?_
  unfold a1 a2 aP
  split_ifs with h
  · rw [vonMangoldt_apply_prime h.1]
    ring
  · ring

/-- `‖S_{1,η}(·,x)‖` is continuous. -/
theorem s1_cont (η : ℝ → ℝ) (x : ℝ) : Continuous fun α => ‖OC.s1Sum η x α‖ := by
  simp_rw [s1Sum_eq]
  exact (eSum_continuous _).norm

/-- `‖S_{2,η}(·,x)‖` is continuous. -/
theorem s2_cont (η : ℝ → ℝ) (x : ℝ) : Continuous fun α => ‖s2Sum η x α‖ := by
  simp_rw [s2Sum_eq]
  exact (eSum_continuous _).norm

/-- **Parseval for `S₁`**: `∫_{(0,1]}|S_{1,η}|² = S`. -/
theorem parseval_s1 (η : ℝ → ℝ) (x : ℝ) (hs : Summable fun n => ‖aP η x n‖) :
    ∫ α in Set.Ioc (0 : ℝ) 1, ‖OC.s1Sum η x α‖ ^ 2 = MinSp.sPr η x := by
  simp_rw [s1Sum_eq]
  rw [parseval_Ioc _ (summable_a1 η x hs), sq_a1]

/-- **Parseval for `S₂`**: `∫_{(0,1]}|S_{2,η}|² = s2Sq`. -/
theorem parseval_s2 (η : ℝ → ℝ) (x : ℝ) (hs : Summable fun n => ‖aP η x n‖) :
    ∫ α in Set.Ioc (0 : ℝ) 1, ‖s2Sum η x α‖ ^ 2 = s2Sq η x := by
  simp_rw [s2Sum_eq]
  rw [parseval_Ioc _ (summable_a2 η x hs), sq_a2]

/-- `s2Sq ≥ 0`. -/
theorem s2Sq_nonneg (η : ℝ → ℝ) (x : ℝ) : 0 ≤ s2Sq η x := by
  unfold s2Sq
  refine tsum_nonneg fun n => ?_
  split_ifs
  · exact le_refl 0
  · exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-! ## (3) The arcs: open, measurable, monotone in the level -/

/-- `𝔐_{δ,r}(x)` is open (a union of open intervals). -/
theorem isOpen_arcs (δ : ℝ) (r : ℕ) (x : ℝ) : IsOpen (Smooth.arcs δ r x) := by
  unfold Smooth.arcs
  refine IsOpen.union ?_ ?_ <;>
  exact isOpen_iUnion fun q => isOpen_iUnion fun _ => isOpen_iUnion fun _ =>
    isOpen_iUnion fun a => isOpen_iUnion fun _ => isOpen_Ioo

/-- `𝔐_{δ,r}(x)` is measurable. -/
theorem measurableSet_arcs (δ : ℝ) (r : ℕ) (x : ℝ) : MeasurableSet (Smooth.arcs δ r x) :=
  (isOpen_arcs δ r x).measurableSet

/-- **`𝔐_{δ,r}(x)` grows with the level `r`** (more moduli, wider arcs; `δ ≥ 0`, `x > 0`). -/
theorem arcs_mono_r (δ : ℝ) (hδ : 0 ≤ δ) (r r' : ℕ) (hr : r ≤ r') (x : ℝ) (hx : 0 < x) :
    Smooth.arcs δ r x ⊆ Smooth.arcs δ r' x := by
  intro α hα
  have hrr : (r : ℝ) ≤ r' := by exact_mod_cast hr
  simp only [Smooth.arcs, Set.mem_union, Set.mem_iUnion, Set.mem_Ioo, Set.mem_Icc] at hα ⊢
  rcases hα with ⟨q, ⟨hq1, hq2⟩, ho, a, ha, h1, h2⟩ | ⟨q, ⟨hq1, hq2⟩, he, a, ha, h1, h2⟩
  · have hw : δ * r / (2 * q * x) ≤ δ * r' / (2 * q * x) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrr hδ) (by positivity)
    exact Or.inl ⟨q, ⟨hq1, le_trans hq2 hr⟩, ho, a, ha, by linarith, by linarith⟩
  · have hw : δ * r / (q * x) ≤ δ * r' / (q * x) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrr hδ) (by positivity)
    exact Or.inr ⟨q, ⟨hq1, le_trans hq2 (by omega)⟩, he, a, ha, by linarith, by linarith⟩

/-- A continuous function is integrable on every subset of `[0,1]`. -/
theorem intOn (f : ℝ → ℝ) (hf : Continuous f) (s : Set ℝ) (hs : s ⊆ Set.Icc 0 1) :
    IntegrableOn f s :=
  hf.integrableOn_Icc.mono_set hs

/-! ## (4) `|S_{η*}(α,x)| ≤ S_{η*}(0,x)` -/

/-- **`η* ≥ 0`** from `thm:ostop`'s hypotheses: `η* = (η₂ ∗_M φ)(49·)`, `η₂ ≥ 0`, `φ ≥ 0`. -/
theorem etaS_nonneg (ηs φ : ℝ → ℝ) (hs : ∀ t : ℝ, ηs t = HW.mconv HW.eta2 φ (49 * t))
    (hφ : ∀ t : ℝ, 0 ≤ t → 0 ≤ φ t) (t : ℝ) : 0 ≤ ηs t := by
  rw [hs]
  unfold HW.mconv
  refine setIntegral_nonneg measurableSet_Ioi fun w hw => ?_
  exact div_nonneg (mul_nonneg (HW.eta2_nonneg _) (hφ w (le_of_lt hw))) (le_of_lt hw)

/-- **`|S_{η*}(α,x)| ≤ S_{η*}(0,x)`** for `η* ≥ 0` (junk `0 ≤ S*` if not summable). -/
theorem norm_smSum_le_sStar (ηs : ℝ → ℝ) (h0 : ∀ t : ℝ, 0 ≤ ηs t) (x α : ℝ) :
    ‖Smooth.smSum ηs x α‖ ≤ MinSp.sStar ηs x := by
  rw [smSum_eq]
  by_cases h : Summable fun n => ‖aP ηs x n‖
  · refine le_trans (norm_eSum_le _ h α) (le_of_eq (tsum_congr fun n => ?_))
    rw [norm_aP, abs_of_nonneg (h0 _)]
  · rw [eSum_junk _ h, norm_zero]
    exact tsum_nonneg fun n => mul_nonneg vonMangoldt_nonneg (h0 _)

/-! ## (5) The weighted triangle inequality (3840-3845) -/

/-- `(u+v)² ≤ (1+t)u² + (1+1/t)v²` for `t > 0`. -/
theorem sq_add_le_t (u v t : ℝ) (ht : 0 < t) :
    (u + v) ^ 2 ≤ (1 + t) * u ^ 2 + (1 + 1 / t) * v ^ 2 := by
  have ht' : t ≠ 0 := ht.ne'
  have h : 0 ≤ (t * u - v) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
  have e : (1 + t) * u ^ 2 + (1 + 1 / t) * v ^ 2 - (u + v) ^ 2 = (t * u - v) ^ 2 / t := by
    field_simp
    ring
  linarith

/-- `(1 + c/a)a² + (1 + a/c)c² = (a + c)²`. -/
theorem opt_t (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    (1 + c / a) * a ^ 2 + (1 + 1 / (c / a)) * c ^ 2 = (a + c) ^ 2 := by
  have ha' : a ≠ 0 := ha.ne'
  have hc' : c ≠ 0 := hc.ne'
  field_simp
  ring

/-- **The optimisation over `t`**: `Z ≤ (1+t)A + (1+1/t)B` for all `t > 0` gives
`Z ≤ (√A + √B)²`. -/
theorem le_sq_of_forall_t (Z A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 < t → Z ≤ (1 + t) * A + (1 + 1 / t) * B) :
    Z ≤ (Real.sqrt A + Real.sqrt B) ^ 2 := by
  rcases hA.eq_or_lt with hA0 | hApos
  · subst hA0
    rw [Real.sqrt_zero, zero_add, Real.sq_sqrt hB]
    refine le_of_not_gt fun hc => ?_
    have hd : 0 < Z - B := by linarith
    have ht : 0 < (2 * B + 1) / (Z - B) := div_pos (by linarith) hd
    have h1 := h _ ht
    rw [one_div_div] at h1
    have h2 : (Z - B) / (2 * B + 1) * B < Z - B := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  rcases hB.eq_or_lt with hB0 | hBpos
  · subst hB0
    rw [Real.sqrt_zero, add_zero, Real.sq_sqrt hA]
    refine le_of_not_gt fun hc => ?_
    have hd : 0 < Z - A := by linarith
    have ht : 0 < (Z - A) / (2 * A + 1) := div_pos hd (by linarith)
    have h1 := h _ ht
    have h2 : (Z - A) / (2 * A + 1) * A < Z - A := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  · have ha : 0 < Real.sqrt A := Real.sqrt_pos.2 hApos
    have hc : 0 < Real.sqrt B := Real.sqrt_pos.2 hBpos
    have h1 := h (Real.sqrt B / Real.sqrt A) (div_pos hc ha)
    have e := opt_t _ _ ha hc
    rw [Real.sq_sqrt hA, Real.sq_sqrt hB] at e
    linarith

/-- **The weighted Minkowski step at a fixed `t`**: if `0 ≤ F ≤ w(u+v)²` on `s ⊆ [0,1]`, then
`∫_s F ≤ (1+t)∫_s wu² + (1+1/t)∫_s wv²` (`w, u, v` continuous, `w ≥ 0`). -/
theorem mink (s : Set ℝ) (hsm : MeasurableSet s) (hs : s ⊆ Set.Icc 0 1) (w u v F : ℝ → ℝ)
    (hw : Continuous w) (hu : Continuous u) (hv : Continuous v) (hw0 : ∀ α, 0 ≤ w α)
    (hF0 : ∀ α ∈ s, 0 ≤ F α) (hF : ∀ α ∈ s, F α ≤ w α * (u α + v α) ^ 2) (t : ℝ)
    (ht : 0 < t) :
    ∫ α in s, F α ≤
      (1 + t) * (∫ α in s, w α * u α ^ 2) + (1 + 1 / t) * ∫ α in s, w α * v α ^ 2 := by
  have i1 : IntegrableOn (fun α => w α * u α ^ 2) s := intOn _ (hw.mul (hu.pow 2)) s hs
  have i2 : IntegrableOn (fun α => w α * v α ^ 2) s := intOn _ (hw.mul (hv.pow 2)) s hs
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (i1.const_mul _) (i2.const_mul _)]
  refine integral_mono_of_nonneg (ae_restrict_of_forall_mem hsm hF0)
    ((i1.const_mul _).add (i2.const_mul _)) (ae_restrict_of_forall_mem hsm fun α hα => ?_)
  have h2 := mul_le_mul_of_nonneg_left (sq_add_le_t (u α) (v α) t ht) (hw0 α)
  calc F α ≤ w α * (u α + v α) ^ 2 := hF α hα
    _ ≤ w α * ((1 + t) * u α ^ 2 + (1 + 1 / t) * v α ^ 2) := h2
    _ = (1 + t) * (w α * u α ^ 2) + (1 + 1 / t) * (w α * v α ^ 2) := by ring

/-! ## (6) Link [Palan] — `lem:jardinbota` at integers, the jump explicit, PROVED -/

/-- Telescoping over `Ico`: `∑_{a≤r<b}(F(r) − F(r+1)) = F(a) − F(b)`. -/
theorem tele (F : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    ∑ r ∈ Finset.Ico a b, (F r - F (r + 1)) = F a - F b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, ih]
    ring

/-- Telescoping over `Ico`, increments: `∑_{a≤r<b}(F(r+1) − F(r)) = F(b) − F(a)`. -/
theorem tele' (F : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    ∑ r ∈ Finset.Ico a b, (F (r + 1) - F r) = F b - F a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, ih]
    ring

/-- **Summation by parts** (`eq:marshti`): `∑_{a≤r≤b} f(r)G(r) = G(b)F(b) +
∑_{a≤r<b}(G(r) − G(r+1))F(r)`, `F(r) = ∑_{a≤m≤r} f(m)`: `PalanLink`'s left side IS the
`∑ f(r)g(r)` of `lem:jardinbota`, with `f(r)` the level masses. -/
theorem abel_Ico (a b : ℕ) (hab : a ≤ b) (f G : ℕ → ℝ) :
    ∑ r ∈ Finset.Icc a b, f r * G r = G b * ∑ m ∈ Finset.Icc a b, f m +
      ∑ r ∈ Finset.Ico a b, (G r - G (r + 1)) * ∑ m ∈ Finset.Icc a r, f m := by
  induction b, hab using Nat.le_induction with
  | base => simp [mul_comm]
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
      Finset.sum_Ico_succ_top hn, ih]
    ring

/-- **The identity behind `PalanLink`**: with the cumulative mass `H(r)S − J` below the top and
`S − J` at the top, summation by parts moves the differences onto `H`, and the top's jump
`S(1 − H(b))G(b)` falls out. -/
theorem palan_identity (a b : ℕ) (hab : a ≤ b) (G H : ℕ → ℝ) (S J : ℝ) :
    G b * (S - J) + ∑ r ∈ Finset.Ico a b, (G r - G (r + 1)) * (H r * S - J) =
      G a * (H a * S - J) + S * ∑ r ∈ Finset.Ico a b, (H (r + 1) - H r) * G (r + 1) +
        S * (1 - H b) * G b := by
  induction b, hab using Nat.le_induction with
  | base =>
    simp only [Finset.Ico_self, Finset.sum_empty, mul_zero, add_zero]
    ring
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, Finset.sum_Ico_succ_top hn]
    linear_combination ih

/-- **Link [Palan] — `lem:jardinbota` at INTEGERS in the form `prop:palan` consumes, with the
jump explicit** (3554-3605, 3610-3688; the defect D3 of the module docstring). For levels
`a ≤ r ≤ b`, `G` non-increasing, cumulative masses `Φ(r) ≤ H(r)S − J` below the top and the
top's cumulative mass EXACTLY `S − J` (Parseval): the left side is `∑ f(r)G(r)` (`abel_Ico`), and
it is at most `G(a)(H(a)S − J) + S∑(H(r+1) − H(r))G(r+1) + S(1 − H(b))G(b)`. No continuity of
`H` is assumed; `H(b)` need not be `1`, and the jump `1 − H(b)` is priced by the consumer.
GENERIC; PROVED (`palanLink`). -/
def PalanLink : Prop :=
  ∀ (a b : ℕ), a ≤ b → ∀ (G H Φ : ℕ → ℝ) (S J : ℝ),
    (∀ r ∈ Finset.Ico a b, G (r + 1) ≤ G r) → (∀ r ∈ Finset.Ico a b, Φ r ≤ H r * S - J) →
    G b * (S - J) + ∑ r ∈ Finset.Ico a b, (G r - G (r + 1)) * Φ r ≤
      G a * (H a * S - J) + S * ∑ r ∈ Finset.Ico a b, (H (r + 1) - H r) * G (r + 1) +
        S * (1 - H b) * G b

/-- **[Palan] PROVED**: `Φ ≤ HS − J` against the non-negative weights `G(r) − G(r+1)`, then
`palan_identity`. -/
theorem palanLink : PalanLink := by
  intro a b hab G H Φ S J hG hΦ
  rw [← palan_identity a b hab G H S J]
  have h : ∑ r ∈ Finset.Ico a b, (G r - G (r + 1)) * Φ r ≤
      ∑ r ∈ Finset.Ico a b, (G r - G (r + 1)) * (H r * S - J) :=
    Finset.sum_le_sum fun r hr => mul_le_mul_of_nonneg_left (hΦ r hr) (by linarith [hG r hr])
  linarith

/-- **Separating `C_{φ,3}`**: for `G(r) = (g(r) + c₃)Ly` the `PalanLink` bound splits into
`Ly·[g-part] + Ly·c₃(S − J)` (`∑(H(r+1) − H(r)) = H(b) − H(a)` telescopes). -/
theorem palan_c3 (a b : ℕ) (hab : a ≤ b) (g H : ℕ → ℝ) (c3 L y S J : ℝ) :
    (g a + c3) * L * y * (H a * S - J) +
        S * ∑ r ∈ Finset.Ico a b, (H (r + 1) - H r) * ((g (r + 1) + c3) * L * y) +
      S * (1 - H b) * ((g b + c3) * L * y) =
    L * y * (g a * (H a * S - J) +
        S * (∑ r ∈ Finset.Ico a b, (H (r + 1) - H r) * g (r + 1) + (1 - H b) * g b)) +
      L * y * c3 * (S - J) := by
  have ht := tele' H a b hab
  have hs : ∑ r ∈ Finset.Ico a b, (H (r + 1) - H r) * ((g (r + 1) + c3) * L * y) =
      L * y * ∑ r ∈ Finset.Ico a b, (H (r + 1) - H r) * g (r + 1) +
        L * y * c3 * ∑ r ∈ Finset.Ico a b, (H (r + 1) - H r) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  rw [hs, ht]
  ring

/-! ## (7) The level bound on the minor arcs (`eq:bertru` at every level + `CoprarL`) -/

/-- **The level bound**: if `|S*(α)| ≤ G(s)` whenever `α` is off the level-`s` arcs (`a ≤ s ≤ b`)
and also `≤ G(a)` on the level-`a` arcs (the annulus), then with nested arcs and `G`
non-increasing, `|S*(α)| ≤ G(b) + ∑_{a≤r<b}(G(r) − G(r+1))·1[α ∈ Y_{r+1}]`: the least level
`s` with `α ∈ Y_s` pins `|S*(α)| ≤ G(s−1)`, and the sum telescopes from `s−1`. GENERIC. -/
theorem level_bound (Y : ℕ → Set ℝ) (a b : ℕ) (hab : a + 1 ≤ b)
    (hY : ∀ s s' : ℕ, a ≤ s → s ≤ s' → Y s ⊆ Y s') (G : ℕ → ℝ)
    (hG : ∀ r ∈ Finset.Ico a b, G (r + 1) ≤ G r) (v α : ℝ)
    (hoff : ∀ s : ℕ, a ≤ s → s ≤ b → α ∉ Y s → v ≤ G s) (hin : α ∈ Y a → v ≤ G a) :
    v ≤ G b + ∑ r ∈ Finset.Ico a b,
      (G r - G (r + 1)) * (Y (r + 1)).indicator (fun _ => (1 : ℝ)) α := by
  have hterm : ∀ r ∈ Finset.Ico a b,
      0 ≤ (G r - G (r + 1)) * (Y (r + 1)).indicator (fun _ => (1 : ℝ)) α := by
    intro r hr
    refine mul_nonneg (by linarith [hG r hr]) ?_
    by_cases h : α ∈ Y (r + 1) <;> simp [h]
  have key : ∀ ℓ : ℕ, a ≤ ℓ → ℓ ≤ b → (∀ r : ℕ, ℓ ≤ r → r < b → α ∈ Y (r + 1)) →
      G ℓ ≤ G b + ∑ r ∈ Finset.Ico a b,
        (G r - G (r + 1)) * (Y (r + 1)).indicator (fun _ => (1 : ℝ)) α := by
    intro ℓ haℓ hℓb hmem
    have h1 : ∑ r ∈ Finset.Ico ℓ b,
        (G r - G (r + 1)) * (Y (r + 1)).indicator (fun _ => (1 : ℝ)) α = G ℓ - G b := by
      rw [← tele G ℓ b hℓb]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [Finset.mem_Ico] at hr
      rw [Set.indicator_of_mem (hmem r hr.1 hr.2), mul_one]
    have h2 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_left haℓ)
      (fun r hr _ => hterm r hr)
    linarith
  by_cases hb : α ∈ Y b
  · classical
    have hex : ∃ s : ℕ, a ≤ s ∧ α ∈ Y s := ⟨b, by omega, hb⟩
    have hs : a ≤ Nat.find hex ∧ α ∈ Y (Nat.find hex) := Nat.find_spec hex
    have hsb : Nat.find hex ≤ b := Nat.find_min' hex ⟨by omega, hb⟩
    have hmem : ∀ ℓ : ℕ, Nat.find hex ≤ ℓ + 1 → α ∈ Y (ℓ + 1) :=
      fun ℓ h => hY _ (ℓ + 1) hs.1 h hs.2
    rcases Nat.eq_or_lt_of_le hs.1 with hsa | hsa
    · have hin' : α ∈ Y a := by
        rw [hsa]
        exact hs.2
      exact le_trans (hin hin') (key a le_rfl (by omega) fun r hr _ => hmem r (by omega))
    · have hnot : α ∉ Y (Nat.find hex - 1) := fun h =>
        Nat.find_min hex (by omega : Nat.find hex - 1 < Nat.find hex) ⟨by omega, h⟩
      exact le_trans (hoff _ (by omega) (by omega) hnot)
        (key _ (by omega) (by omega) fun r hr _ => hmem r (by omega))
  · have h0 := Finset.sum_nonneg hterm
    linarith [hoff b (by omega) le_rfl hb]

/-! ## (8) The sum-to-integral comparison, sharp (the integral term of `M̃`, via `GTMonoL`) -/

/-- `g/u` is interval-integrable where `g` is antitone and `u ≥ a > 0`. -/
theorem gdiv_int (g : ℝ → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hg : AntitoneOn g (Set.Icc a b)) : IntervalIntegrable (fun u => g u / u) volume a b := by
  have h1 : IntervalIntegrable g volume a b :=
    AntitoneOn.intervalIntegrable (by rwa [Set.uIcc_of_le hab])
  have h2 : ContinuousOn (fun u : ℝ => u⁻¹) (Set.uIcc a b) := by
    refine continuousOn_inv₀.mono fun u hu => ?_
    rw [Set.uIcc_of_le hab] at hu
    exact ne_of_gt (lt_of_lt_of_le ha hu.1)
  have h3 := h1.mul_continuousOn h2
  simpa [div_eq_mul_inv] using h3

/-- **The sharp comparison**: for `g` non-increasing on `[a,b]`, `a ≥ 1` (no sign needed),
`∑_{a≤r<b}(log(r+2) − log(r+1))g(r+1) + g(b)·Tel ≤ ∫_a^b g(u)/u du`, where
`Tel = (log(a+1) − log a) − (log(b+1) − log b)` is the telescoped concavity slack of `log`
(`log(r+1) − log r ≥ log(r+2) − log(r+1)`). It is this slack that pays for the integer top
level (defect D1). GENERIC. -/
theorem sum_int_sharp (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (g : ℝ → ℝ)
    (hg : AntitoneOn g (Set.Icc (a : ℝ) b)) :
    ∑ r ∈ Finset.Ico a b, (Real.log ((r : ℝ) + 2) - Real.log ((r : ℝ) + 1)) * g ((r : ℝ) + 1) +
      g b * ((Real.log ((a : ℝ) + 1) - Real.log a) - (Real.log ((b : ℝ) + 1) - Real.log b)) ≤
    ∫ u in (a : ℝ)..(b : ℝ), g u / u := by
  have hint : ∀ k ∈ Set.Ico a b,
      IntervalIntegrable (fun u => g u / u) volume (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast le_trans ha hk.1
    have hak : (a : ℝ) ≤ k := by exact_mod_cast hk.1
    have hkb : ((k + 1 : ℕ) : ℝ) ≤ b := by exact_mod_cast hk.2
    exact gdiv_int g k ((k + 1 : ℕ) : ℝ) (by linarith) (by push_cast; linarith)
      (hg.mono (Set.Icc_subset_Icc hak hkb))
  have hsplit : ∑ k ∈ Finset.Ico a b, ∫ u in (k : ℝ)..((k + 1 : ℕ) : ℝ), g u / u =
      ∫ u in (a : ℝ)..(b : ℝ), g u / u :=
    intervalIntegral.sum_integral_adjacent_intervals_Ico hab hint
  have htel : ∑ r ∈ Finset.Ico a b, ((Real.log ((r : ℝ) + 1) - Real.log r) -
      (Real.log (((r + 1 : ℕ) : ℝ) + 1) - Real.log ((r + 1 : ℕ) : ℝ))) =
      (Real.log ((a : ℝ) + 1) - Real.log a) - (Real.log ((b : ℝ) + 1) - Real.log b) :=
    tele (fun r : ℕ => Real.log ((r : ℝ) + 1) - Real.log r) a b hab
  rw [← htel, Finset.mul_sum, ← Finset.sum_add_distrib, ← hsplit]
  refine Finset.sum_le_sum fun r hr => ?_
  rw [Finset.mem_Ico] at hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast le_trans ha hr.1
  have har : (a : ℝ) ≤ r := by exact_mod_cast hr.1
  have hrb : (r : ℝ) + 1 ≤ b := by exact_mod_cast hr.2
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have e1 : ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 := by push_cast; ring
  have e3 : (r : ℝ) + 1 + 1 = (r : ℝ) + 2 := by ring
  rw [e1, e3]
  have hc : g b ≤ g ((r : ℝ) + 1) :=
    hg ⟨by linarith, hrb⟩ ⟨hab', le_rfl⟩ hrb
  have hδ : Real.log ((r : ℝ) + 2) - Real.log ((r : ℝ) + 1) ≤
      Real.log ((r : ℝ) + 1) - Real.log r := by
    have h1 : Real.log ((r : ℝ) * ((r : ℝ) + 2)) ≤ Real.log (((r : ℝ) + 1) ^ 2) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h1
    push_cast at h1
    linarith
  have hlow : g ((r : ℝ) + 1) * (Real.log ((r : ℝ) + 1) - Real.log r) ≤
      ∫ u in (r : ℝ)..((r : ℝ) + 1), g u / u := by
    have hconst : ∫ u in (r : ℝ)..((r : ℝ) + 1), g ((r : ℝ) + 1) / u =
        g ((r : ℝ) + 1) * (Real.log ((r : ℝ) + 1) - Real.log r) := by
      simp_rw [div_eq_mul_inv]
      rw [intervalIntegral.integral_const_mul, integral_inv_of_pos (by positivity)
        (by positivity), Real.log_div (by positivity) (by positivity)]
    rw [← hconst]
    refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ fun u hu => ?_
    · refine ContinuousOn.intervalIntegrable ?_
      refine continuousOn_const.div continuousOn_id fun u hu => ?_
      rw [Set.uIcc_of_le (by linarith)] at hu
      exact ne_of_gt (lt_of_lt_of_le (by linarith) hu.1)
    · exact gdiv_int g r ((r : ℝ) + 1) (by linarith) (by linarith)
        (hg.mono (Set.Icc_subset_Icc har hrb))
    · have hu0 : 0 < u := lt_of_lt_of_le (by linarith) hu.1
      exact div_le_div_of_nonneg_right (hg ⟨by linarith [hu.1], by linarith [hu.2]⟩
        ⟨by linarith, hrb⟩ hu.2) hu0.le
  have hδ0 : 0 ≤ (Real.log ((r : ℝ) + 1) - Real.log r) -
      (Real.log ((r : ℝ) + 2) - Real.log ((r : ℝ) + 1)) := by linarith
  have hm := mul_le_mul_of_nonneg_right hc hδ0
  linarith

/-- **`Tel ≥ 1/(a+1) − 1/b`** (`log(1 + 1/a) ≥ 1/(a+1)`, `log(1 + 1/b) ≤ 1/b`). -/
theorem tel_bound (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    1 / ((a : ℝ) + 1) - 1 / (b : ℝ) ≤
      (Real.log ((a : ℝ) + 1) - Real.log a) - (Real.log ((b : ℝ) + 1) - Real.log b) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have h1 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < ((a : ℝ) + 1) / a by positivity)
  rw [Real.log_div (by positivity) ha0.ne', inv_div] at h1
  have h1' : 1 - (a : ℝ) / ((a : ℝ) + 1) = 1 / ((a : ℝ) + 1) := by
    rw [one_sub_div (by positivity)]
    congr 1
    ring
  have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((b : ℝ) + 1) / b by positivity)
  rw [Real.log_div (by positivity) hb0.ne'] at h2
  have h2' : ((b : ℝ) + 1) / b - 1 = 1 / b := by
    rw [div_sub_one hb0.ne']
    congr 1
    ring
  linarith

/-! ## (9) Helfgott's numbers: `H`, the jump, the top step -/

/-- **`H(r) = (log(r+1) + c⁺)/(log √x + c⁻)`**, `c⁺ = 2.05315`, `c⁻ = −1.306476`: `cor:coeur`'s
bound as `OC.CoeurY` types it (`coeurY_iff`), at the level `r : ℕ`. -/
noncomputable def hC (x : ℝ) (r : ℕ) : ℝ :=
  (Real.log ((r : ℝ) + 1) + 2.05315) / (Real.log (Real.sqrt x) - 1.306476)

/-- **`H(r₀) = OC.hR0C x`**: the typed `H̃(r₀)` of `M̃`. -/
theorem hC_r0 (x : ℝ) : hC x 150000 = OC.hR0C x := by
  unfold hC OC.hR0C
  norm_num

/-- **`OC.CoeurY` IS the bound `C(r) ≤ H(r)S`**, by `Iff.rfl`. -/
theorem coeurY_iff (ηp : ℝ → ℝ) : OC.CoeurY ηp ↔
    ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ r : ℕ, 150000 ≤ r → (r : ℝ) < MinSp.r1y (x / 49) →
      ∫ α in Set.Ioc (0 : ℝ) 1 ∩ Smooth.arcs 8 (r + 1) (x / 49), ‖OC.s1Sum ηp x α‖ ^ 2 ≤
        hC x r * MinSp.sPr ηp x :=
  Iff.rfl

/-- `log 49 ≤ 6 log 2`. -/
theorem log49_le : Real.log 49 ≤ 6 * Real.log 2 := by
  have h1 : Real.log (49 : ℝ) ≤ Real.log ((2 : ℝ) ^ 6) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at h1
  push_cast at h1
  linarith

/-- **`D_h = log √x − 1.306476 > 7`** for `x ≥ 4.9·10²⁶` (`log(x/49) > 17`). -/
theorem dh_pos (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : 7 < Real.log (Real.sqrt x) - 1.306476 := by
  have hx0 := MinSp.x_pos x hx
  rw [Real.log_sqrt hx0.le]
  have h := GS.log_gt (x / 49) (MinSp.y_ge x hx)
  have h49 : Real.log (x / 49) ≤ Real.log x :=
    Real.log_le_log (by positivity) (by linarith)
  linarith

/-- **`coefC ≤ 7/15`**: its second summand is negative (`−3.538215 + (8/15)log 49 < 0`). -/
theorem coefC_le (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : OC.coefC x ≤ 7 / 15 := by
  unfold OC.coefC
  have hl2 := Real.log_two_lt_d9
  have h49 := log49_le
  have hD : 0 < Real.log x - 2 * 1.306476 := by
    have h := dh_pos x hx
    rw [Real.log_sqrt (MinSp.x_pos x hx).le] at h
    linarith
  have hn : -3.538215 + 8 / 15 * Real.log 49 ≤ 0 := by linarith
  have h := div_nonpos_iff.mpr (Or.inr ⟨hn, hD.le⟩)
  linarith

/-- **The jump at ANY `t ≥ r₁`**: `1 − (log t + c⁺)/(log √x + c⁻) ≤ coefC x`. The proof of
`OC.jump_le_coefC` with `log(r₁+1)` replaced by `log t ≥ log r₁`; at `t = ⌊r₁⌋ + 1` it prices
the integer top level's jump `1 − H(⌊r₁⌋)` (defect D3). -/
theorem jump_le_coefC_of (x t : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (ht : MinSp.r1y (x / 49) ≤ t) :
    1 - (Real.log t + 2.05315) / (Real.log (Real.sqrt x) - 1.306476) ≤ OC.coefC x := by
  have hx0 : 0 < x := MinSp.x_pos x hx
  have hL : 3 ≤ Real.log x := by
    have h := dh_pos x hx
    rw [Real.log_sqrt hx0.le] at h
    linarith
  have hy0 : 0 < x / 49 := div_pos hx0 (by norm_num)
  have hr1 : 0 < MinSp.r1y (x / 49) := by
    unfold MinSp.r1y
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hy0 _)
  have hlr : Real.log (MinSp.r1y (x / 49)) =
      Real.log (3 / 8) + 4 / 15 * (Real.log x - Real.log 49) := by
    unfold MinSp.r1y
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hy0 _).ne', Real.log_rpow hy0,
      Real.log_div hx0.ne' (by norm_num)]
  have hmono : Real.log (MinSp.r1y (x / 49)) ≤ Real.log t := Real.log_le_log hr1 ht
  have hj := OC.jump_le
  have hD : 0 < Real.log x - 2 * 1.306476 := by linarith
  have hsq : Real.log (Real.sqrt x) - 1.306476 = (Real.log x - 2 * 1.306476) / 2 := by
    rw [Real.log_sqrt hx0.le]
    ring
  rw [hsq]
  unfold OC.coefC
  refine OC.jump_alg _ _ _ hD ?_
  rw [hlr] at hmono
  linarith

/-- `(x/49)^{4/15} ≥ 4·10⁶` for `x/49 ≥ 10²⁵` (`(4·10⁶)¹⁵ ≤ 10¹⁰⁰`). -/
theorem rpow_ge_4e6 (y : ℝ) (hy : 10 ^ 25 ≤ y) : (4e6 : ℝ) ≤ y ^ ((4 : ℝ) / 15) := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have h1 : (4e6 : ℝ) ^ (15 : ℕ) ≤ y ^ (4 : ℕ) :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hy 4)
  have h2 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 1 / 15)
  have e1 : ((4e6 : ℝ) ^ (15 : ℕ)) ^ ((1 : ℝ) / 15) = 4e6 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have e2 : (y ^ (4 : ℕ)) ^ ((1 : ℝ) / 15) = y ^ ((4 : ℝ) / 15) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
    norm_num
  rw [e1, e2] at h2
  exact h2

/-- **The integer top level is high enough**: `⌊r₁⌋ ≥ 150001(7D_h/30 + 1)` for every
`x ≥ 4.9·10²⁶` (`r₁ = (3/8)u`, `u = (x/49)^{4/15} ≥ 4·10⁶`, `log u ≤ log 4·10⁶ + u/4·10⁶ − 1`,
`log 4·10⁶ ≤ 22 log 2`, `log 49 ≤ 6 log 2`). Ratio `1.475` at the threshold. -/
theorem floor_big (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) :
    150001 * (7 * (Real.log (Real.sqrt x) - 1.306476) / 30 + 1) ≤
      (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := by
  have hx0 := MinSp.x_pos x hx
  have hy := MinSp.y_ge x hx
  have hy0 : 0 < x / 49 := div_pos hx0 (by norm_num)
  have hu := rpow_ge_4e6 (x / 49) hy
  have hu0 : 0 < (x / 49) ^ ((4 : ℝ) / 15) := by linarith
  have hlu : Real.log ((x / 49) ^ ((4 : ℝ) / 15)) = 4 / 15 * Real.log (x / 49) :=
    Real.log_rpow hy0 _
  have hlx : Real.log x = Real.log 49 + Real.log (x / 49) := by
    rw [← Real.log_mul (by norm_num) hy0.ne']
    congr 1
    ring
  have hls : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx0.le
  have hl2 := Real.log_two_lt_d9
  have h49 := log49_le
  have hlc : Real.log ((x / 49) ^ ((4 : ℝ) / 15) / 4e6) ≤
      (x / 49) ^ ((4 : ℝ) / 15) / 4e6 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hdiv : Real.log ((x / 49) ^ ((4 : ℝ) / 15) / 4e6) =
      Real.log ((x / 49) ^ ((4 : ℝ) / 15)) - Real.log 4e6 :=
    Real.log_div hu0.ne' (by norm_num)
  have hl4 : Real.log (4e6 : ℝ) ≤ 22 * Real.log 2 := by
    have h1 : Real.log (4e6 : ℝ) ≤ Real.log ((2 : ℝ) ^ 22) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have hfl := Nat.sub_one_lt_floor (MinSp.r1y (x / 49))
  have hr1 : MinSp.r1y (x / 49) = 3 / 8 * (x / 49) ^ ((4 : ℝ) / 15) := rfl
  rw [hls, hlx]
  linarith

/-- **The top step, algebra**: `s·g_R ≤ t·g₁`, `0 < s ≤ t`, `t² − s² ≤ 1`, `g_R ≥ 0` give
`2s²(g_R − g₁) ≤ g_R`. With `s = √⌊r₁⌋`, `t = √r₁` (`TopStepL`): `g̃(R) − g̃(r₁) ≤ g̃(R)/(2R)`. -/
theorem top_step_alg (s t gR g1 : ℝ) (hs : 0 < s) (hst : s ≤ t) (h1 : t ^ 2 - s ^ 2 ≤ 1)
    (hg : 0 ≤ gR) (hsg : s * gR ≤ t * g1) : 2 * s ^ 2 * (gR - g1) ≤ gR := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have h2 : t * (gR - g1) ≤ (t - s) * gR := by linarith
  have h4 : 2 * s ^ 2 * (t - s) ≤ t := by
    have h5 : 2 * s ^ 2 ≤ t * (t + s) := by nlinarith
    have hts0 : 0 ≤ t - s := by linarith
    have h6 : 2 * s ^ 2 * (t - s) ≤ t * (t + s) * (t - s) :=
      mul_le_mul_of_nonneg_right h5 hts0
    have h7 : t * (t + s) * (t - s) ≤ t * 1 := by
      have h8 : (t + s) * (t - s) ≤ 1 := by nlinarith
      calc t * (t + s) * (t - s) = t * ((t + s) * (t - s)) := by ring
        _ ≤ t * 1 := mul_le_mul_of_nonneg_left h8 ht.le
    linarith
  have h6 : t * (2 * s ^ 2 * (gR - g1)) ≤ t * gR := by
    calc t * (2 * s ^ 2 * (gR - g1)) = 2 * s ^ 2 * (t * (gR - g1)) := by ring
      _ ≤ 2 * s ^ 2 * ((t - s) * gR) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (2 * s ^ 2 * (t - s)) * gR := by ring
      _ ≤ t * gR := mul_le_mul_of_nonneg_right h4 hg
  exact le_of_mul_le_mul_left h6 ht

/-- **The top, combined** (pure algebra): the sharp sum bound, the jump `≤ cf ≤ 7/15`, the top
step `2R(g_R − g₁) ≤ g_R`, `Tel ≥ 1/A₀ − 1/R` and `R ≥ A₀(7D_h/30 + 1)` give
`Sg/D_h + j·g_R ≤ B/D_h + cf·g₁`. -/
theorem top_combine (Sg A B Dh jR cf gR g1 Tel R A0 : ℝ) (hDh : 0 < Dh) (hA0 : 0 < A0)
    (hSg : Sg + gR * Tel ≤ A) (hAB : A ≤ B) (hj : jR ≤ cf) (hcf : cf ≤ 7 / 15)
    (hgR : 0 ≤ gR) (hg1 : g1 ≤ gR) (hstep : 2 * R * (gR - g1) ≤ gR)
    (hTel : 1 / A0 - 1 / R ≤ Tel) (hR : A0 * (7 * Dh / 30 + 1) ≤ R) :
    Sg / Dh + jR * gR ≤ B / Dh + cf * g1 := by
  have hR0 : 0 < R := by nlinarith
  have h1 : Sg / Dh ≤ (B - gR * Tel) / Dh := div_le_div_of_nonneg_right (by linarith) hDh.le
  have h2 : jR * gR ≤ cf * gR := mul_le_mul_of_nonneg_right hj hgR
  have h3 : cf * (gR - g1) ≤ 7 / 15 * (gR - g1) := mul_le_mul_of_nonneg_right hcf (by linarith)
  have h4 : 7 * Dh ≤ 30 * R * Tel := by
    have h6 : 30 * R * (1 / A0 - 1 / R) ≤ 30 * R * Tel :=
      mul_le_mul_of_nonneg_left hTel (by linarith)
    have hinv : R * (1 / R) = 1 := mul_one_div_cancel hR0.ne'
    have h5 : 30 * R * (1 / A0 - 1 / R) = 30 * (R / A0) - 30 := by
      rw [mul_sub, show 30 * R * (1 / R) = 30 * (R * (1 / R)) by ring, hinv]
      ring
    have h7 : 7 * Dh / 30 + 1 ≤ R / A0 := by
      rw [le_div_iff₀ hA0]
      linarith
    linarith
  have h7 : 7 / 15 * (gR - g1) * Dh ≤ gR * Tel := by
    have h8 : 30 * R * (7 / 15 * (gR - g1) * Dh) ≤ 30 * R * (gR * Tel) := by
      calc 30 * R * (7 / 15 * (gR - g1) * Dh) = 7 * Dh * (2 * R * (gR - g1)) := by ring
        _ ≤ 7 * Dh * gR := mul_le_mul_of_nonneg_left hstep (by linarith)
        _ ≤ 30 * R * Tel * gR := mul_le_mul_of_nonneg_right h4 hgR
        _ = 30 * R * (gR * Tel) := by ring
    exact le_of_mul_le_mul_left h8 (by linarith)
  have h9 : 7 / 15 * (gR - g1) ≤ gR * Tel / Dh := by
    rw [le_div_iff₀ hDh]
    exact h7
  have e : (B - gR * Tel) / Dh = B / Dh - gR * Tel / Dh := by ring
  linarith

/-- `C_{φ,3}(K) ≥ 0` for `1/K ≥ 0`. -/
theorem cPhi3_nonneg (φ : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ 1 / K) : 0 ≤ MinSp.cPhi3 φ K :=
  mul_nonneg (div_nonneg (by norm_num) (MajSp.l1_nonneg φ))
    (intervalIntegral.integral_nonneg hK fun w _ => abs_nonneg _)

/-- `r₁(y) ≥ 0`. -/
theorem r1y_nonneg (y : ℝ) (hy : 0 ≤ y) : 0 ≤ MinSp.r1y y := by
  unfold MinSp.r1y
  positivity

/-- **`g̃ ≥ 0` on `[1000, r₁(y)]`** for `φ ≥ 0`: every piece of `OL.gTL` averages a positive
`gYL` (`OL.gYL_pos`: the arguments stay in `[175, (wy)^{1/3}/6]`, `GS.arg_le_r1y`,
`GS.r1y_le_third`, `GS.scale_ge`) against `φ ≥ 0`, or is `∫|φ| ≥ 0`. -/
theorem gTL_nonneg (φ : ℝ → ℝ) (hφ0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ φ t) (y r : ℝ) (hy : 10 ^ 25 ≤ y)
    (hr : 1000 ≤ r) (hr1 : r ≤ MinSp.r1y y) : 0 ≤ OL.gTL φ y r := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hr0 : 0 < r := by linarith
  have hl17 := GS.log_gt y hy
  have hK0 : 0 < 1 / MinSp.kK y := by
    unfold MinSp.kK
    have : 0 < Real.log y := by linarith
    positivity
  have hK1 : 1 / MinSp.kK y ≤ 1 := by
    unfold MinSp.kK
    rw [div_le_one (by linarith)]
    linarith
  have hr1000 : 1000 / r ≤ 1 := by
    rw [div_le_one hr0]
    exact hr
  have hw1 : max (1 / MinSp.kK y) (1000 / r) ≤ 1 := max_le hK1 hr1000
  unfold OL.gTL
  refine div_nonneg ?_ (MajSp.l1_nonneg φ)
  refine add_nonneg (add_nonneg ?_ ?_) (mul_nonneg (by norm_num) ?_)
  · refine intervalIntegral.integral_nonneg hw1 fun w hw => ?_
    have hw0 : 0 < w := lt_of_lt_of_le (lt_of_lt_of_le hK0 (le_max_left _ _)) hw.1
    have hY : 3.4e23 ≤ w * y := GS.scale_ge y w hy (le_trans (le_max_left _ _) hw.1)
    have h1000 : 1000 ≤ w * r := by
      have h := mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) hw.1) hr0.le
      rw [div_mul_cancel₀ _ hr0.ne'] at h
      exact h
    have harg := GS.arg_le_r1y y w r hy0 hw0 hr1
    rw [min_eq_left hw.2] at harg
    exact mul_nonneg (OL.gYL_pos (w * y) (w * r) (by positivity) (by linarith)
      (le_trans harg (GS.r1y_le_third _ hY))).le (hφ0 w hw0.le)
  · refine setIntegral_nonneg measurableSet_Ioi fun w (hw : 1 < w) => ?_
    have hY : 3.4e23 ≤ w * y := by nlinarith
    have harg := GS.arg_le_r1y y w r hy0 (by linarith) hr1
    rw [min_eq_right hw.le, one_mul] at harg
    exact mul_nonneg (OL.gYL_pos (w * y) r (by positivity) (by linarith)
      (le_trans harg (GS.r1y_le_third _ hY))).le (hφ0 w (by linarith))
  · exact intervalIntegral.integral_nonneg (le_max_left _ _) fun w _ => abs_nonneg _

/-- `g̃` at the level `r : ℕ`. -/
noncomputable def gN (φ : ℝ → ℝ) (x : ℝ) (r : ℕ) : ℝ := OL.gTL φ (x / 49) r

/-- **Link [TopStep] — `√r·g̃(r)` does not decrease across the last unit step**:
`√⌊r₁⌋·g̃(⌊r₁⌋) ≤ √r₁·g̃(r₁)` for every `y ≥ 10²⁵`. What the integer top level needs (defect D1:
the proof bounds the tail by `g̃(⌊r₁⌋)`, `M̃` types `g̃(r₁)`). NUMERIC, NAMED: `d log g̃/d log r`
at `r₁` is `−0.392` (`y = 10²⁵`) … `−0.465` (`10¹⁰⁰`) in floating point (module docstring),
i.e. `√r·g̃(r)` increases there; a `lem:vinc`-type derivative bound would discharge it. -/
def TopStepL (φ : ℝ → ℝ) : Prop :=
  ∀ y : ℝ, 10 ^ 25 ≤ y →
    Real.sqrt (⌊MinSp.r1y y⌋₊ : ℝ) * OL.gTL φ y ⌊MinSp.r1y y⌋₊ ≤
      Real.sqrt (MinSp.r1y y) * OL.gTL φ y (MinSp.r1y y)

/-- **The top of `prop:palan` on Helfgott's numbers**: the `PalanLink` sum and jump at the
integer top `R = ⌊r₁⌋` are at most `M̃`'s `2/(log x + 2c⁻)·∫_{r₀}^{r₁}g̃/r + coefC·g̃(r₁)`. From
`sum_int_sharp` (`GTMonoL`), `jump_le_coefC_of` (`t = R + 1 ≥ r₁`), `coefC_le`, `TopStepL`
(`top_step_alg`), `tel_bound`, `floor_big`; the combination is `top_combine`. -/
theorem top_le (φ : ℝ → ℝ) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x)
    (hanti : AntitoneOn (OL.gTL φ (x / 49)) (Set.Icc 150000 (MinSp.r1y (x / 49))))
    (hg1 : 0 ≤ OL.gTL φ (x / 49) (MinSp.r1y (x / 49)))
    (hts : Real.sqrt (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) * OL.gTL φ (x / 49) ⌊MinSp.r1y (x / 49)⌋₊ ≤
      Real.sqrt (MinSp.r1y (x / 49)) * OL.gTL φ (x / 49) (MinSp.r1y (x / 49))) :
    ∑ r ∈ Finset.Ico 150000 ⌊MinSp.r1y (x / 49)⌋₊, (hC x (r + 1) - hC x r) * gN φ x (r + 1) +
        (1 - hC x ⌊MinSp.r1y (x / 49)⌋₊) * gN φ x ⌊MinSp.r1y (x / 49)⌋₊ ≤
      2 / (Real.log x - 2 * 1.306476) * OL.intGTL φ (x / 49) +
        OC.coefC x * OL.gTL φ (x / 49) (MinSp.r1y (x / 49)) := by
  have hx0 := MinSp.x_pos x hx
  have hy0 : 0 < x / 49 := div_pos hx0 (by norm_num)
  have hDh := dh_pos x hx
  have hRb := floor_big x hx
  have hr10 := r1y_nonneg (x / 49) hy0.le
  have hRr1 : (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) ≤ MinSp.r1y (x / 49) := Nat.floor_le hr10
  have hr1R : MinSp.r1y (x / 49) < (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hR150 : (150001 : ℝ) ≤ (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := by nlinarith
  have hRn : 150000 ≤ ⌊MinSp.r1y (x / 49)⌋₊ := by
    have h : (150000 : ℝ) ≤ (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := by linarith
    exact_mod_cast h
  have e150 : ((150000 : ℕ) : ℝ) = 150000 := by norm_num
  have hantiR : AntitoneOn (OL.gTL φ (x / 49))
      (Set.Icc ((150000 : ℕ) : ℝ) (⌊MinSp.r1y (x / 49)⌋₊ : ℝ)) := by
    rw [e150]
    exact hanti.mono (Set.Icc_subset_Icc le_rfl hRr1)
  have hgR1 : OL.gTL φ (x / 49) (MinSp.r1y (x / 49)) ≤
      OL.gTL φ (x / 49) (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) :=
    hanti ⟨by linarith, hRr1⟩ ⟨by linarith, le_rfl⟩ hRr1
  have hgR : 0 ≤ OL.gTL φ (x / 49) (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := le_trans hg1 hgR1
  have hsh := sum_int_sharp 150000 ⌊MinSp.r1y (x / 49)⌋₊ (by norm_num) hRn
    (OL.gTL φ (x / 49)) hantiR
  have hext : ∫ u in ((150000 : ℕ) : ℝ)..(⌊MinSp.r1y (x / 49)⌋₊ : ℝ), OL.gTL φ (x / 49) u / u ≤
      OL.intGTL φ (x / 49) := by
    rw [e150]
    unfold OL.intGTL
    have hint1 : IntervalIntegrable (fun u => OL.gTL φ (x / 49) u / u) volume 150000
        (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) :=
      gdiv_int _ _ _ (by norm_num) (by linarith) (hanti.mono (Set.Icc_subset_Icc le_rfl hRr1))
    have hint2 : IntervalIntegrable (fun u => OL.gTL φ (x / 49) u / u) volume
        (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) (MinSp.r1y (x / 49)) :=
      gdiv_int _ _ _ (by linarith) hRr1 (hanti.mono (Set.Icc_subset_Icc (by linarith) le_rfl))
    rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
    have hnn : 0 ≤ ∫ u in (⌊MinSp.r1y (x / 49)⌋₊ : ℝ)..(MinSp.r1y (x / 49)),
        OL.gTL φ (x / 49) u / u := by
      refine intervalIntegral.integral_nonneg hRr1 fun u hu => ?_
      have hu0 : 0 < u := by linarith [hu.1]
      exact div_nonneg (le_trans hg1 (hanti ⟨by linarith [hu.1], hu.2⟩ ⟨by linarith, le_rfl⟩
        hu.2)) hu0.le
    linarith
  have hsum : ∑ r ∈ Finset.Ico 150000 ⌊MinSp.r1y (x / 49)⌋₊,
      (hC x (r + 1) - hC x r) * gN φ x (r + 1) =
      (∑ r ∈ Finset.Ico 150000 ⌊MinSp.r1y (x / 49)⌋₊,
        (Real.log ((r : ℝ) + 2) - Real.log ((r : ℝ) + 1)) * OL.gTL φ (x / 49) ((r : ℝ) + 1)) /
        (Real.log (Real.sqrt x) - 1.306476) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun r _ => ?_
    unfold hC gN
    have e1 : ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 := by push_cast; ring
    have e2 : (r : ℝ) + 1 + 1 = (r : ℝ) + 2 := by ring
    rw [e1, e2]
    field_simp
    ring
  have hj : 1 - hC x ⌊MinSp.r1y (x / 49)⌋₊ ≤ OC.coefC x := by
    unfold hC
    exact jump_le_coefC_of x _ hx hr1R.le
  have hstep : 2 * (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) * (OL.gTL φ (x / 49) (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) -
      OL.gTL φ (x / 49) (MinSp.r1y (x / 49))) ≤
      OL.gTL φ (x / 49) (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := by
    have hs0 : 0 < Real.sqrt (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := Real.sqrt_pos.2 (by linarith)
    have hst : Real.sqrt (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) ≤ Real.sqrt (MinSp.r1y (x / 49)) :=
      Real.sqrt_le_sqrt hRr1
    have h1 : Real.sqrt (MinSp.r1y (x / 49)) ^ 2 -
        Real.sqrt (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) ^ 2 ≤ 1 := by
      rw [Real.sq_sqrt hr10, Real.sq_sqrt (by linarith)]
      linarith
    have h := top_step_alg _ _ _ _ hs0 hst h1 hgR hts
    rwa [Real.sq_sqrt (by linarith)] at h
  have hTel := tel_bound 150000 ⌊MinSp.r1y (x / 49)⌋₊ (by norm_num) (by omega)
  have hRb' : (((150000 : ℕ) : ℝ) + 1) * (7 * (Real.log (Real.sqrt x) - 1.306476) / 30 + 1) ≤
      (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := by
    rw [e150]
    norm_num
    linarith
  have hD2 : 2 / (Real.log x - 2 * 1.306476) * OL.intGTL φ (x / 49) =
      OL.intGTL φ (x / 49) / (Real.log (Real.sqrt x) - 1.306476) := by
    rw [Real.log_sqrt hx0.le]
    have hD : Real.log x - 2 * 1.306476 ≠ 0 := by
      have h := hDh
      rw [Real.log_sqrt hx0.le] at h
      intro h0
      linarith
    field_simp
  have hgN : gN φ x ⌊MinSp.r1y (x / 49)⌋₊ = OL.gTL φ (x / 49) (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := rfl
  rw [hsum, hD2, hgN]
  exact top_combine _ _ _ _ _ _ _ _ _ _ _ (by linarith) (by positivity) hsh hext hj
    (coefC_le x hx) hgR hgR1 hstep hTel hRb'

/-! ## (10) Link [I0S] — `I₀S ≥ (√J − √E)²` (3942-3962), PROVED -/

/-- **The reverse triangle inequality, in numbers**: `J ≤ (√J₁ + √J₂)²`, `J₂ ≤ E ≤ J` give
`(√J − √E)² ≤ J₁`. The hypothesis `E ≤ J` is what Helfgott leaves implicit (defect D2). -/
theorem i0s_real (J J1 J2 E : ℝ) (hJ1 : 0 ≤ J1)
    (hJ : J ≤ (Real.sqrt J1 + Real.sqrt J2) ^ 2) (hJ2E : J2 ≤ E) (hEJ : E ≤ J) :
    (Real.sqrt J - Real.sqrt E) ^ 2 ≤ J1 := by
  have hs0 : 0 ≤ Real.sqrt J1 + Real.sqrt J2 := by positivity
  have h1 : Real.sqrt J ≤ Real.sqrt J1 + Real.sqrt J2 := by
    have h := Real.sqrt_le_sqrt hJ
    rwa [Real.sqrt_sq hs0] at h
  have h2 : Real.sqrt J2 ≤ Real.sqrt E := Real.sqrt_le_sqrt hJ2E
  have h3 : Real.sqrt E ≤ Real.sqrt J := Real.sqrt_le_sqrt hEJ
  have h4 : Real.sqrt J - Real.sqrt E ≤ Real.sqrt J1 := by linarith
  have h5 := pow_le_pow_left₀ (by linarith) h4 2
  rwa [Real.sq_sqrt hJ1] at h5

/-- **Link [I0S]** (3942-3962): where `∑Λ(n)|η₊(n/x)| < ∞`, `∫|S₂|² ≤ E` and `E ≤ J`,
`(√J − √E)² ≤ J₁ = ∫_{𝔐_{8,r₀}}|S₁|²` (`= I₀S`). PROVED (`i0sLink`); the side condition
`E ≤ J` is supplied by the NAMED `JgeE`. -/
def I0SLink : Prop :=
  ∀ (ηp b : ℝ → ℝ) (x : ℝ), 49 * 10 ^ 25 ≤ x → (Summable fun n => ‖aP ηp x n‖) →
    s2Sq ηp x ≤ MinSp.eBig b x → MinSp.eBig b x ≤ x * MajSp.amaj ηp x →
      MinSp.pJE ηp b x ≤ ∫ α in Smooth.majorSet x, ‖OC.s1Sum ηp x α‖ ^ 2

/-- **[I0S] PROVED**: `J = ∫_𝔐|S₁ + S₂|² ≤ (√J₁ + √J₂)²` (`mink` with weight `1`,
`le_sq_of_forall_t`), `J₂ ≤ ∫₀¹|S₂|² = s2Sq ≤ E` (Parseval), then `i0s_real`. -/
theorem i0sLink : I0SLink := by
  intro ηp b x hx hsum hE2 hEJ
  have hx0 := MinSp.x_pos x hx
  have hmaj : MeasurableSet (Smooth.majorSet x) :=
    measurableSet_Ioc.inter (measurableSet_arcs _ _ _)
  have hsubM : Smooth.majorSet x ⊆ Set.Icc 0 1 := fun α h => Set.Ioc_subset_Icc_self h.1
  have hc1 := s1_cont ηp x
  have hc2 := s2_cont ηp x
  have hJeq : x * MajSp.amaj ηp x = ∫ α in Smooth.majorSet x, ‖Smooth.smSum ηp x α‖ ^ 2 := by
    unfold MajSp.amaj
    field_simp
  have hJ1 : 0 ≤ ∫ α in Smooth.majorSet x, ‖OC.s1Sum ηp x α‖ ^ 2 :=
    setIntegral_nonneg hmaj fun α _ => sq_nonneg _
  have hJ2 : 0 ≤ ∫ α in Smooth.majorSet x, ‖s2Sum ηp x α‖ ^ 2 :=
    setIntegral_nonneg hmaj fun α _ => sq_nonneg _
  have hF : ∀ α ∈ Smooth.majorSet x, ‖Smooth.smSum ηp x α‖ ^ 2 ≤
      (fun _ => (1 : ℝ)) α * (‖OC.s1Sum ηp x α‖ + ‖s2Sum ηp x α‖) ^ 2 := by
    intro α _
    rw [one_mul, splitLink ηp x hsum α]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
  have hmk : ∫ α in Smooth.majorSet x, ‖Smooth.smSum ηp x α‖ ^ 2 ≤
      (Real.sqrt (∫ α in Smooth.majorSet x, ‖OC.s1Sum ηp x α‖ ^ 2) +
        Real.sqrt (∫ α in Smooth.majorSet x, ‖s2Sum ηp x α‖ ^ 2)) ^ 2 := by
    refine le_sq_of_forall_t _ _ _ hJ1 hJ2 fun t ht => ?_
    have h := mink (Smooth.majorSet x) hmaj hsubM (fun _ => 1) (fun α => ‖OC.s1Sum ηp x α‖)
      (fun α => ‖s2Sum ηp x α‖) (fun α => ‖Smooth.smSum ηp x α‖ ^ 2) continuous_const hc1 hc2
      (fun _ => zero_le_one) (fun α _ => sq_nonneg _) hF t ht
    simpa only [one_mul] using h
  have hJ2E : ∫ α in Smooth.majorSet x, ‖s2Sum ηp x α‖ ^ 2 ≤ MinSp.eBig b x := by
    have h : ∫ α in Smooth.majorSet x, ‖s2Sum ηp x α‖ ^ 2 ≤
        ∫ α in Set.Ioc (0 : ℝ) 1, ‖s2Sum ηp x α‖ ^ 2 :=
      setIntegral_mono_set (intOn _ (hc2.pow 2) _ Set.Ioc_subset_Icc_self)
        (ae_restrict_of_forall_mem measurableSet_Ioc fun α _ => sq_nonneg _)
        Set.inter_subset_left.eventuallyLE
    rw [parseval_s2 ηp x hsum] at h
    linarith
  unfold MinSp.pJE
  rw [hJeq] at hEJ ⊢
  exact i0s_real _ _ _ _ hJ1 hmk hJ2E hEJ

/-! ## (11) The named links of layer 2 not already typed -/

/-- **Link [EBound2] — the `E` bound** (3846-3890): `∫₀¹|S_{2,η}|² = s2Sq ≤ E` (`MinSp.eBig`),
for every `η` with `|η| ≤ 1.079955`, `|η(t)t| ≤ 1.19073` (which make `C_{η,0}`, `C_{η,1}`
genuine integrals). CITED: Rosser-Schoenfeld 1962 Thms 12 (`ψ(t) < 1.03883t`) and 13
(`ψ(t) − θ(t) < 1.42620√t`) with partial summation against the non-increasing `sup_{r≥t}|η|²`.
NOT Platt. In-house pricing in the module docstring: out of reach at `eBig`'s typed constants.
NAMED. -/
def EBound2 (η : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → |η t| ≤ 1.079955) → (∀ t : ℝ, 0 ≤ t → |η t * t| ≤ 1.19073) →
    ∀ b : ℝ → ℝ, MinSp.SupFn η b → ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → s2Sq η x ≤ MinSp.eBig b x

/-- **Link [JgeE] — `E ≤ J`**, the side condition of `I₀S ≥ (√J − √E)²` (defect D2). On
Helfgott's weights `J/x ≥ 8.57476` and `E/x ≤ 8.4031·10⁻¹²`: DISCHARGED from the chain's own
`OC.DrujalLowP` and the proved `Dubistdie` (`jgeE_helf`). -/
def JgeE (ηp : ℝ → ℝ) : Prop :=
  ∀ b : ℝ → ℝ, MinSp.SupFn ηp b → ∀ x : ℝ, 49 * 10 ^ 25 ≤ x →
    MinSp.eBig b x ≤ x * MajSp.amaj ηp x

/-! ## (12) The two halves of `Z` -/

/-- **`Z₂ ≤ S*(0,x)·E`** (3846-3890): `|S*| ≤ S*(0,x)`, `∫_𝔪|S₂|² ≤ ∫₀¹|S₂|² = s2Sq ≤ E`. -/
theorem z2_le (ηp ηs : ℝ → ℝ) (x : ℝ) (hsum : Summable fun n => ‖aP ηp x n‖)
    (hηs0 : ∀ t : ℝ, 0 ≤ ηs t) (E : ℝ) (hE : s2Sq ηp x ≤ E) :
    ∫ α in Smooth.minorSet x, ‖Smooth.smSum ηs x α‖ * ‖s2Sum ηp x α‖ ^ 2 ≤
      MinSp.sStar ηs x * E := by
  have hmin : MeasurableSet (Smooth.minorSet x) :=
    measurableSet_Ioc.diff (measurableSet_arcs _ _ _)
  have hsubm : Smooth.minorSet x ⊆ Set.Icc 0 1 := fun α h => Set.Ioc_subset_Icc_self h.1
  have hc2 : Continuous fun α => ‖s2Sum ηp x α‖ ^ 2 := (s2_cont ηp x).pow 2
  have hS0 : 0 ≤ MinSp.sStar ηs x := tsum_nonneg fun n => mul_nonneg vonMangoldt_nonneg (hηs0 _)
  have h1 : ∫ α in Smooth.minorSet x, ‖Smooth.smSum ηs x α‖ * ‖s2Sum ηp x α‖ ^ 2 ≤
      ∫ α in Smooth.minorSet x, MinSp.sStar ηs x * ‖s2Sum ηp x α‖ ^ 2 :=
    integral_mono_of_nonneg
      (ae_restrict_of_forall_mem hmin fun α _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))
      ((intOn _ hc2 _ hsubm).const_mul _)
      (ae_restrict_of_forall_mem hmin fun α _ =>
        mul_le_mul_of_nonneg_right (norm_smSum_le_sStar ηs hηs0 x α) (sq_nonneg _))
  rw [integral_const_mul] at h1
  have h2 : ∫ α in Smooth.minorSet x, ‖s2Sum ηp x α‖ ^ 2 ≤
      ∫ α in Set.Ioc (0 : ℝ) 1, ‖s2Sum ηp x α‖ ^ 2 :=
    setIntegral_mono_set (intOn _ hc2 _ Set.Ioc_subset_Icc_self)
      (ae_restrict_of_forall_mem measurableSet_Ioc fun α _ => sq_nonneg _)
      Set.sdiff_subset.eventuallyLE
  rw [parseval_s2 ηp x hsum] at h2
  calc ∫ α in Smooth.minorSet x, ‖Smooth.smSum ηs x α‖ * ‖s2Sum ηp x α‖ ^ 2
      ≤ MinSp.sStar ηs x * ∫ α in Smooth.minorSet x, ‖s2Sum ηp x α‖ ^ 2 := h1
    _ ≤ MinSp.sStar ηs x * s2Sq ηp x := mul_le_mul_of_nonneg_left h2 hS0
    _ ≤ MinSp.sStar ηs x * E := mul_le_mul_of_nonneg_left hE hS0

/-- **`C(r) = ∫_{𝔐^{(y)}_{8,r+1}∩(0,1]}|S₁|²`**, the cumulative `ℓ²` mass `CoeurY` bounds. -/
noncomputable def cumC (ηp : ℝ → ℝ) (x : ℝ) (r : ℕ) : ℝ :=
  ∫ α in Set.Ioc (0 : ℝ) 1 ∩ Smooth.arcs 8 (r + 1) (x / 49), ‖OC.s1Sum ηp x α‖ ^ 2

/-- **`J₁ = I₀S = ∫_{𝔐_{8,r₀}(x)∩(0,1]}|S₁|²`**. -/
noncomputable def jOne (ηp : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ α in Smooth.majorSet x, ‖OC.s1Sum ηp x α‖ ^ 2

/-- **`Z₁` against the level bound**: integrating `|S*(α)| ≤ G(R) + ∑(G(r) − G(r+1))1_{Y_{r+1}}`
against `|S₁|²` over the minor arcs gives `G(R)(S − J₁) + ∑(G(r) − G(r+1))(C(r) − J₁)`
(Parseval for the total, `𝔐_{8,r₀}(x) ⊆ 𝔐^{(y)}_{8,r+1}` for the rest). -/
theorem z1_le (ηp ηs : ℝ → ℝ) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (R : ℕ) (G : ℕ → ℝ)
    (hsum : Summable fun n => ‖aP ηp x n‖)
    (hlev : ∀ α ∈ Smooth.minorSet x, ‖Smooth.smSum ηs x α‖ ≤ G R +
      ∑ r ∈ Finset.Ico 150000 R,
        (G r - G (r + 1)) * (Smooth.arcs 8 (r + 1) (x / 49)).indicator (fun _ => (1 : ℝ)) α) :
    ∫ α in Smooth.minorSet x, ‖Smooth.smSum ηs x α‖ * ‖OC.s1Sum ηp x α‖ ^ 2 ≤
      G R * (MinSp.sPr ηp x - jOne ηp x) +
        ∑ r ∈ Finset.Ico 150000 R, (G r - G (r + 1)) * (cumC ηp x r - jOne ηp x) := by
  have hx0 := MinSp.x_pos x hx
  have hy0 : 0 < x / 49 := div_pos hx0 (by norm_num)
  have hfc : Continuous fun α => ‖OC.s1Sum ηp x α‖ ^ 2 := (s1_cont ηp x).pow 2
  have hmin : MeasurableSet (Smooth.minorSet x) :=
    measurableSet_Ioc.diff (measurableSet_arcs _ _ _)
  have hmaj : MeasurableSet (Smooth.majorSet x) :=
    measurableSet_Ioc.inter (measurableSet_arcs _ _ _)
  have hsubm : Smooth.minorSet x ⊆ Set.Icc 0 1 := fun α h => Set.Ioc_subset_Icc_self h.1
  have hIf : IntegrableOn (fun α => ‖OC.s1Sum ηp x α‖ ^ 2) (Smooth.minorSet x) :=
    intOn _ hfc _ hsubm
  have hY : ∀ r : ℕ, MeasurableSet (Smooth.arcs 8 (r + 1) (x / 49)) :=
    fun r => measurableSet_arcs _ _ _
  have hint : ∀ r ∈ Finset.Ico 150000 R, Integrable (fun α => (G r - G (r + 1)) *
      (Smooth.arcs 8 (r + 1) (x / 49)).indicator (fun α => ‖OC.s1Sum ηp x α‖ ^ 2) α)
      (volume.restrict (Smooth.minorSet x)) :=
    fun r _ => (hIf.indicator (hY r)).const_mul _
  have hpt : ∀ α ∈ Smooth.minorSet x,
      ‖Smooth.smSum ηs x α‖ * ‖OC.s1Sum ηp x α‖ ^ 2 ≤
        G R * ‖OC.s1Sum ηp x α‖ ^ 2 + ∑ r ∈ Finset.Ico 150000 R, (G r - G (r + 1)) *
          (Smooth.arcs 8 (r + 1) (x / 49)).indicator (fun α => ‖OC.s1Sum ηp x α‖ ^ 2) α := by
    intro α hα
    have h1 := mul_le_mul_of_nonneg_right (hlev α hα) (sq_nonneg ‖OC.s1Sum ηp x α‖)
    refine le_trans h1 (le_of_eq ?_)
    rw [add_mul, Finset.sum_mul]
    refine congrArg (G R * ‖OC.s1Sum ηp x α‖ ^ 2 + ·) (Finset.sum_congr rfl fun r _ => ?_)
    by_cases h : α ∈ Smooth.arcs 8 (r + 1) (x / 49)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      ring
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
      ring
  have hInt : ∫ α in Smooth.minorSet x, ‖Smooth.smSum ηs x α‖ * ‖OC.s1Sum ηp x α‖ ^ 2 ≤
      ∫ α in Smooth.minorSet x, (G R * ‖OC.s1Sum ηp x α‖ ^ 2 +
        ∑ r ∈ Finset.Ico 150000 R, (G r - G (r + 1)) *
          (Smooth.arcs 8 (r + 1) (x / 49)).indicator (fun α => ‖OC.s1Sum ηp x α‖ ^ 2) α) :=
    integral_mono_of_nonneg
      (ae_restrict_of_forall_mem hmin fun α _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))
      ((hIf.const_mul (G R)).add (integrable_finsetSum _ hint))
      (ae_restrict_of_forall_mem hmin hpt)
  rw [integral_add (hIf.const_mul _) (integrable_finsetSum _ hint), integral_const_mul,
    integral_finsetSum _ hint] at hInt
  have hm1 : ∫ α in Smooth.minorSet x, ‖OC.s1Sum ηp x α‖ ^ 2 =
      MinSp.sPr ηp x - jOne ηp x := by
    have hset : Smooth.minorSet x = Set.Ioc (0 : ℝ) 1 \ Smooth.majorSet x := by
      ext α
      simp only [Smooth.minorSet, Smooth.majorSet, Set.mem_sdiff, Set.mem_inter_iff]
      tauto
    rw [hset, setIntegral_sdiff hmaj (intOn _ hfc _ Set.Ioc_subset_Icc_self)
      Set.inter_subset_left, parseval_s1 ηp x hsum]
    rfl
  have hm2 : ∀ r ∈ Finset.Ico 150000 R, ∫ α in Smooth.minorSet x, (G r - G (r + 1)) *
      (Smooth.arcs 8 (r + 1) (x / 49)).indicator (fun α => ‖OC.s1Sum ηp x α‖ ^ 2) α =
      (G r - G (r + 1)) * (cumC ηp x r - jOne ηp x) := by
    intro r hr
    rw [Finset.mem_Ico] at hr
    rw [integral_const_mul, integral_indicator (hY r), Measure.restrict_restrict (hY r)]
    have hsub : Smooth.majorSet x ⊆ Set.Ioc 0 1 ∩ Smooth.arcs 8 (r + 1) (x / 49) :=
      fun α h => ⟨h.1, arcs_mono_r 8 (by norm_num) 150000 (r + 1) (by omega) (x / 49) hy0
        (OC.arcs_x_sub_y 150000 x hx0 h.2)⟩
    have hset : Smooth.arcs 8 (r + 1) (x / 49) ∩ Smooth.minorSet x =
        (Set.Ioc 0 1 ∩ Smooth.arcs 8 (r + 1) (x / 49)) \ Smooth.majorSet x := by
      ext α
      simp only [Smooth.minorSet, Smooth.majorSet, Set.mem_sdiff, Set.mem_inter_iff]
      tauto
    rw [hset, setIntegral_sdiff hmaj (intOn _ hfc _ fun α h => Set.Ioc_subset_Icc_self h.1) hsub]
    rfl
  rw [hm1, Finset.sum_congr rfl hm2] at hInt
  exact hInt

/-- **The assembly of `Z₁`**: `z1_le`, `PalanLink`, `palan_c3`, the top bound `T₀`, `H(r₀) = h₀`
and `pJ ≤ J₁` give `Z₁ ≤ Ly(g(a)(h₀S − pJ) + T₀S + c₃(S − pJ))`. -/
theorem z1_assemble (hpal : PalanLink) (a R : ℕ) (haR : a ≤ R) (G g H Φ : ℕ → ℝ)
    (c3 L y S J1 Z1 T0 h0 pJ : ℝ) (hG : ∀ r, G r = (g r + c3) * L * y)
    (hanti : ∀ r ∈ Finset.Ico a R, G (r + 1) ≤ G r)
    (hΦ : ∀ r ∈ Finset.Ico a R, Φ r ≤ H r * S - J1)
    (h1 : Z1 ≤ G R * (S - J1) + ∑ r ∈ Finset.Ico a R, (G r - G (r + 1)) * Φ r)
    (htop : ∑ r ∈ Finset.Ico a R, (H (r + 1) - H r) * g (r + 1) + (1 - H R) * g R ≤ T0)
    (hHa : H a = h0) (hJ : pJ ≤ J1) (hLy : 0 ≤ L * y) (hS : 0 ≤ S) (hga : 0 ≤ g a)
    (hc3 : 0 ≤ c3) :
    Z1 ≤ L * y * (g a * (h0 * S - pJ) + T0 * S + c3 * (S - pJ)) := by
  have h2 := hpal a R haR G H Φ S J1 hanti hΦ
  have h2' : G a * (H a * S - J1) + S * ∑ r ∈ Finset.Ico a R, (H (r + 1) - H r) * G (r + 1) +
      S * (1 - H R) * G R =
      L * y * (g a * (H a * S - J1) +
        S * (∑ r ∈ Finset.Ico a R, (H (r + 1) - H r) * g (r + 1) + (1 - H R) * g R)) +
      L * y * c3 * (S - J1) := by
    simp only [hG]
    exact palan_c3 a R haR g H c3 L y S J1
  have e1 : g a * (H a * S - J1) ≤ g a * (h0 * S - pJ) := by
    rw [hHa]
    exact mul_le_mul_of_nonneg_left (by linarith) hga
  have e2 : S * (∑ r ∈ Finset.Ico a R, (H (r + 1) - H r) * g (r + 1) + (1 - H R) * g R) ≤
      T0 * S := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right htop hS
  have e3 : c3 * (S - J1) ≤ c3 * (S - pJ) := mul_le_mul_of_nonneg_left (by linarith) hc3
  have e4 := mul_le_mul_of_nonneg_left (add_le_add (add_le_add e1 e2) e3) hLy
  calc Z1 ≤ _ := h1
    _ ≤ _ := h2
    _ = _ := h2'
    _ = L * y * (g a * (H a * S - J1) +
        S * (∑ r ∈ Finset.Ico a R, (H (r + 1) - H r) * g (r + 1) + (1 - H R) * g R) +
        c3 * (S - J1)) := by ring
    _ ≤ _ := e4

/-- **The level weight `G(s) = (g̃(s) + C_{φ,3}(K))|φ|₁y`** — `OL.GorshL`'s right side at level
`s`. -/
noncomputable def gG (φ : ℝ → ℝ) (x : ℝ) (s : ℕ) : ℝ :=
  (OL.gTL φ (x / 49) s + MinSp.cPhi3 φ (MinSp.kK (x / 49))) * MajSp.l1 φ * (x / 49)

/-- **`Z₁ ≤ |φ|₁(x/49)(M̃ + T)`** — `prop:palan` for `S₁` (3891-3941), from `GorshL`, `CoprarL`
(the level bound), `CoeurY`, `PalanLink`, `GTMonoL`, `TopStepL` and `I0SLink`. -/
theorem z1_bound (ηp ηs φ b : ℝ → ℝ) (hpal : PalanLink) (hi0 : I0SLink) (hco : OC.CoeurY ηp)
    (hgo : OL.GorshL ηs φ) (hgm : OL.GTMonoL φ) (hcp : OL.CoprarL ηs φ) (hts : TopStepL φ)
    (hsd : ∀ t : ℝ, ηs t = HW.mconv HW.eta2 φ (49 * t)) (hφ0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ φ t)
    (hφi : IntegrableOn φ (Set.Ioi 0)) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x)
    (hsum : Summable fun n => ‖aP ηp x n‖) (hE2 : s2Sq ηp x ≤ MinSp.eBig b x)
    (hEJ : MinSp.eBig b x ≤ x * MajSp.amaj ηp x) :
    ∫ α in Smooth.minorSet x, ‖Smooth.smSum ηs x α‖ * ‖OC.s1Sum ηp x α‖ ^ 2 ≤
      MajSp.l1 φ * x / 49 * (OL.mMCL φ ηp b x + MinSp.tT φ ηp b x) := by
  have hx0 := MinSp.x_pos x hx
  have hy := MinSp.y_ge x hx
  have hy0 : 0 < x / 49 := div_pos hx0 (by norm_num)
  have hanti := hgm (x / 49) hy
  have hr10 := r1y_nonneg (x / 49) hy0.le
  have hRb := floor_big x hx
  have hDh := dh_pos x hx
  have hRr1 : (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) ≤ MinSp.r1y (x / 49) := Nat.floor_le hr10
  have hR150 : (150001 : ℝ) ≤ (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := by nlinarith
  have hRn : 150000 + 1 ≤ ⌊MinSp.r1y (x / 49)⌋₊ := by exact_mod_cast hR150
  have hg1 : 0 ≤ OL.gTL φ (x / 49) (MinSp.r1y (x / 49)) :=
    gTL_nonneg φ hφ0 _ _ hy (by linarith) le_rfl
  have e150 : ((150000 : ℕ) : ℝ) = 150000 := by norm_num
  have hga : 0 ≤ OL.gTL φ (x / 49) ((150000 : ℕ) : ℝ) := by
    rw [e150]
    exact le_trans hg1 (hanti ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith))
  have hK0 : 0 ≤ 1 / MinSp.kK (x / 49) := by
    unfold MinSp.kK
    have := GS.log_gt (x / 49) hy
    positivity
  have hc3 := cPhi3_nonneg φ (MinSp.kK (x / 49)) hK0
  have hLy : 0 ≤ MajSp.l1 φ * (x / 49) := mul_nonneg (MajSp.l1_nonneg φ) hy0.le
  have hS0 := MinSp.sPr_nonneg ηp x
  have hGanti : ∀ r ∈ Finset.Ico 150000 ⌊MinSp.r1y (x / 49)⌋₊, gG φ x (r + 1) ≤ gG φ x r := by
    intro r hr
    rw [Finset.mem_Ico] at hr
    have hr0 : (150000 : ℝ) ≤ r := by exact_mod_cast hr.1
    have hr1 : ((r + 1 : ℕ) : ℝ) ≤ (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := by exact_mod_cast hr.2
    have hrr : (r : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by push_cast; linarith
    have h := hanti ⟨hr0, by linarith⟩ ⟨by linarith, by linarith⟩ hrr
    unfold gG
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith)
      (MajSp.l1_nonneg φ)) hy0.le
  have hlev : ∀ α ∈ Smooth.minorSet x, ‖Smooth.smSum ηs x α‖ ≤
      gG φ x ⌊MinSp.r1y (x / 49)⌋₊ + ∑ r ∈ Finset.Ico 150000 ⌊MinSp.r1y (x / 49)⌋₊,
        (gG φ x r - gG φ x (r + 1)) *
          (Smooth.arcs 8 (r + 1) (x / 49)).indicator (fun _ => (1 : ℝ)) α := by
    intro α hα
    refine level_bound (fun s => Smooth.arcs 8 s (x / 49)) 150000 _ hRn
      (fun s s' _ h => arcs_mono_r 8 (by norm_num) s s' h _ hy0) (gG φ x) hGanti _ α
      (fun s hs1 hs2 hsα => ?_) (fun hin => ?_)
    · have hs : (s : ℝ) ≤ MinSp.r1y (x / 49) :=
        le_trans (by exact_mod_cast hs2) hRr1
      exact hgo hsd hφ0 hφi x hx s hs1 hs α hsα
    · have hA0 : α ∈ OC.annA0 x := ⟨hα.1, hin, hα.2⟩
      have h := hcp hsd hφ0 hφi x hx α hA0
      unfold gG
      rw [e150]
      exact h
  have hstep1 := z1_le ηp ηs x hx _ (gG φ x) hsum hlev
  have hΦ : ∀ r ∈ Finset.Ico 150000 ⌊MinSp.r1y (x / 49)⌋₊,
      cumC ηp x r - jOne ηp x ≤ hC x r * MinSp.sPr ηp x - jOne ηp x := by
    intro r hr
    rw [Finset.mem_Ico] at hr
    have hrl : (r : ℝ) < MinSp.r1y (x / 49) :=
      lt_of_lt_of_le (by exact_mod_cast hr.2) hRr1
    exact sub_le_sub_right (hco x hx r hr.1 hrl) _
  have htop := top_le φ x hx hanti hg1 (hts (x / 49) hy)
  have hJ := hi0 ηp b x hx hsum hE2 hEJ
  have hZ := z1_assemble hpal 150000 _ (by omega) (gG φ x) (gN φ x) (hC x)
    (fun r => cumC ηp x r - jOne ηp x) (MinSp.cPhi3 φ (MinSp.kK (x / 49))) (MajSp.l1 φ)
    (x / 49) (MinSp.sPr ηp x) (jOne ηp x) _ _ (OC.hR0C x) (MinSp.pJE ηp b x) (fun r => rfl)
    hGanti hΦ hstep1 htop (hC_r0 x) hJ hLy hS0 hga hc3
  refine le_trans hZ (le_of_eq ?_)
  unfold OL.mMCL MinSp.tT gN
  push_cast
  ring

/-! ## (13) THE COMPOSITION -/

/-- **`OL.OstopL η₊ η* φ` from its layer-2 links** (the corrected `thm:ostop`, 3746-3994):
`Z ≤ (√Z₁ + √Z₂)²` (`SplitLink`, `mink`), `Z₂ ≤ S*(0,x)E` (`EBound2`, `z2_le`),
`Z₁ ≤ |φ|₁(x/49)(M̃ + T)` (`z1_bound`), then `le_sq_of_forall_t`. Where `∑Λ(n)|η₊(n/x)|`
diverges, `S_{η₊}` is junk `0` and so is `Z`. Generic in `(η₊, η*, φ)`. -/
theorem ostopL_of_links (ηp ηs φ : ℝ → ℝ) (hpal : PalanLink) (hspl : SplitLink)
    (hi0 : I0SLink) (hco : OC.CoeurY ηp) (hgo : OL.GorshL ηs φ) (hgm : OL.GTMonoL φ)
    (hcp : OL.CoprarL ηs φ) (heb : EBound2 ηp)
    (hs1 : ∀ t : ℝ, 0 ≤ t → |ηp t| ≤ 1.079955) (hs2 : ∀ t : ℝ, 0 ≤ t → |ηp t * t| ≤ 1.19073)
    (hjE : JgeE ηp) (hts : TopStepL φ) : OL.OstopL ηp ηs φ := by
  intro hoh b hb x hx
  obtain ⟨hsd, -, hφ0, hφi, -, -, -⟩ := hoh
  by_cases hsum : Summable fun n => ‖aP ηp x n‖
  swap
  · have h0 : MinSp.zMin ηp ηs x = 0 := by
      unfold MinSp.zMin
      simp [smSum_eq, eSum_junk _ hsum]
    rw [h0]
    positivity
  have hηs0 : ∀ t : ℝ, 0 ≤ ηs t := etaS_nonneg ηs φ hsd hφ0
  have hmin : MeasurableSet (Smooth.minorSet x) :=
    measurableSet_Ioc.diff (measurableSet_arcs _ _ _)
  have hsubm : Smooth.minorSet x ⊆ Set.Icc 0 1 := fun α h => Set.Ioc_subset_Icc_self h.1
  have hcs : Continuous fun α => ‖Smooth.smSum ηs x α‖ := (eSum_continuous (aP ηs x)).norm
  have hE2 := heb hs1 hs2 b hb x hx
  have hZ1 := z1_bound ηp ηs φ b hpal hi0 hco hgo hgm hcp hts hsd hφ0 hφi x hx hsum hE2
    (hjE b hb x hx)
  have hZ2 := z2_le ηp ηs x hsum hηs0 _ hE2
  have hZ1n : 0 ≤ ∫ α in Smooth.minorSet x, ‖Smooth.smSum ηs x α‖ * ‖OC.s1Sum ηp x α‖ ^ 2 :=
    setIntegral_nonneg hmin fun α _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hZ2n : 0 ≤ ∫ α in Smooth.minorSet x, ‖Smooth.smSum ηs x α‖ * ‖s2Sum ηp x α‖ ^ 2 :=
    setIntegral_nonneg hmin fun α _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hF : ∀ α ∈ Smooth.minorSet x, ‖Smooth.smSum ηs x α‖ * ‖Smooth.smSum ηp x α‖ ^ 2 ≤
      ‖Smooth.smSum ηs x α‖ * (‖OC.s1Sum ηp x α‖ + ‖s2Sum ηp x α‖) ^ 2 := by
    intro α _
    rw [hspl ηp x hsum α]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2) (norm_nonneg _)
  refine le_sq_of_forall_t _ _ _ (le_trans hZ1n hZ1) (le_trans hZ2n hZ2) fun t ht => ?_
  have hm := mink (Smooth.minorSet x) hmin hsubm (fun α => ‖Smooth.smSum ηs x α‖)
    (fun α => ‖OC.s1Sum ηp x α‖) (fun α => ‖s2Sum ηp x α‖)
    (fun α => ‖Smooth.smSum ηs x α‖ * ‖Smooth.smSum ηp x α‖ ^ 2) hcs (s1_cont ηp x)
    (s2_cont ηp x) (fun α => norm_nonneg _) (fun α _ => mul_nonneg (norm_nonneg _)
      (sq_nonneg _)) hF t ht
  have h1t : 0 ≤ 1 + t := by linarith
  have h2t : 0 ≤ 1 + 1 / t := by positivity
  calc MinSp.zMin ηp ηs x
      ≤ (1 + t) * (∫ α in Smooth.minorSet x, ‖Smooth.smSum ηs x α‖ * ‖OC.s1Sum ηp x α‖ ^ 2) +
        (1 + 1 / t) * ∫ α in Smooth.minorSet x,
          ‖Smooth.smSum ηs x α‖ * ‖s2Sum ηp x α‖ ^ 2 := hm
    _ ≤ (1 + t) * (MajSp.l1 φ * x / 49 * (OL.mMCL φ ηp b x + MinSp.tT φ ηp b x)) +
        (1 + 1 / t) * (MinSp.sStar ηs x * MinSp.eBig b x) :=
      add_le_add (mul_le_mul_of_nonneg_left hZ1 h1t) (mul_le_mul_of_nonneg_left hZ2 h2t)

/-- **THE HEADLINE: `OL.OstopL η₊ η* φ` on Helfgott's weights from the named layer-2 links**:
`ostopL_of_links` with `PalanLink`, `SplitLink`, `I0SLink` discharged (`palanLink`,
`splitLink`, `i0sLink`) and the sup norms of `η₊` from `EN.supN_helf`. OPEN: `OC.CoeurY`
(`cor:coeur` at `δ₀ = 392`), `OL.GorshL` (or `GS.gorshL_of_open`), `OL.GTMonoL`, `OL.CoprarL`,
`EBound2` (Rosser-Schoenfeld 12-13), `JgeE` (discharged by `jgeE_helf` from the chain's
`DrujalLowP`), `TopStepL` (numeric). Application only. -/
theorem ostopL_of_layer2 (hco : OC.CoeurY HW.etaPlus) (hgo : OL.GorshL HW.etaStar HW.phi)
    (hgm : OL.GTMonoL HW.phi) (hcp : OL.CoprarL HW.etaStar HW.phi) (heb : EBound2 HW.etaPlus)
    (hjE : JgeE HW.etaPlus) (hts : TopStepL HW.phi) :
    OL.OstopL HW.etaPlus HW.etaStar HW.phi :=
  ostopL_of_links HW.etaPlus HW.etaStar HW.phi palanLink splitLink i0sLink hco hgo hgm hcp heb
    EN.supN_helf.1 EN.supN_helf.2.1 hjE hts

/-- **`JgeE` on Helfgott's weights, DISCHARGED from the chain's own hypotheses**: `E ≤ 8.4031·
10⁻¹²x` (`DB.dubistdie_all`, proved) and `J ≥ J₀x` (`OC.DrujalLowP J₀`, the link
`OL.minorAt_ostopL_cheb` already takes, with its cheap hypotheses discharged exactly as in
`OL.minor_of_mnum_L`), `J₀ ≥ 8.4031·10⁻¹²`. -/
theorem jgeE_helf (J₀ : ℝ) (hJ0 : 8.4031e-12 ≤ J₀) (pf : RT.PlattFull)
    (hm : RT.HelfMajFull HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (hdl : OC.DrujalLowP J₀ HW.etaPlus HW.etaCirc) : JgeE HW.etaPlus := by
  intro b hb x hx
  obtain ⟨mp, -, -⟩ := hm pf
  have hsn := EN.supN_helf
  have hrg := RW.regW_helf
  obtain ⟨hlo1, hlo2, hdiff, hl3, -, -, -, -, -⟩ := EN.normsB27_helf BS.band_sharp
  have hx0 := MinSp.x_pos x hx
  have hE := DB.dubistdie_all HW.etaPlus hsn.1 hsn.2.1 b hb x hx
  have hA := hdl hrg.1 hsn.1 DS.l1_etaPlus_sharp hrg.2.2.2.2.1 hrg.2.2.2.2.2.1
    hrg.2.2.2.2.2.2 hlo1 hlo2 hdiff hl3 x hx (MajSp.et_plus HW.etaPlus mp _ hx)
    (MajSp.eb_plus HW.etaPlus mp _ hx)
  have h1 : 8.4031e-12 * x ≤ J₀ * x := mul_le_mul_of_nonneg_right hJ0 hx0.le
  have h2 : J₀ * x ≤ MajSp.amaj HW.etaPlus x * x := mul_le_mul_of_nonneg_right hA hx0.le
  linarith [mul_comm x (MajSp.amaj HW.etaPlus x)]

/-- **`OL.OstopL` with `GorshL` itself composed** (`GS.gorshL_of_open`): the inputs are the
minarcs Main Theorem with `L` repaired, Rosser-Schoenfeld Thm 15, `GYMono`, `HLeG`, `Austeria`
in place of `GorshL`. Application only. -/
theorem ostopL_of_open (hco : OC.CoeurY HW.etaPlus) (hmm : OL.MinMainL) (h15 : GS.RS62Thm15)
    (hmo : GS.GYMono) (hhl : GS.HLeG) (hau : GS.Austeria) (hgm : OL.GTMonoL HW.phi)
    (hcp : OL.CoprarL HW.etaStar HW.phi) (heb : EBound2 HW.etaPlus) (hjE : JgeE HW.etaPlus)
    (hts : TopStepL HW.phi) : OL.OstopL HW.etaPlus HW.etaStar HW.phi :=
  ostopL_of_layer2 hco (GS.gorshL_of_open HW.etaStar HW.phi hmm h15 hmo hhl hau) hgm hcp heb
    hjE hts

/-- **The Chebyshev-split minor target `RT.MinorUpperAt 1.0154` from layer 2**:
`OL.minorAt_ostopL_cheb` with `OL.OstopL` supplied by `ostopL_of_layer2` and `JgeE` by
`jgeE_helf` (from the SAME `DrujalLowP 8.57476` the headline already takes). OPEN:
`RT.PlattFull`, `RT.HelfMajFull`, `OL.FelipaAt 0.6406`, `OC.DrujalLowP 8.57476`,
`OL.MNumL HW.phi 8.54 0.8095 0.6406`, and the layer-2 links `OC.CoeurY`, `OL.GorshL`,
`OL.GTMonoL`, `OL.CoprarL`, `EBound2`, `TopStepL`. Application only. -/
theorem minorAt_layer2_cheb (pf : RT.PlattFull)
    (hm : RT.HelfMajFull HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (hfe : OL.FelipaAt 0.6406 HW.etaPlus) (hdl : OC.DrujalLowP 8.57476 HW.etaPlus HW.etaCirc)
    (hmn : OL.MNumL HW.phi 8.54 0.8095 0.6406) (hco : OC.CoeurY HW.etaPlus)
    (hgo : OL.GorshL HW.etaStar HW.phi) (hgm : OL.GTMonoL HW.phi)
    (hcp : OL.CoprarL HW.etaStar HW.phi) (heb : EBound2 HW.etaPlus) (hts : TopStepL HW.phi) :
    RT.MinorUpperAt 1.0154 HW.etaPlus HW.etaStar :=
  OL.minorAt_ostopL_cheb pf hm hfe
    (ostopL_of_layer2 hco hgo hgm hcp heb (jgeE_helf 8.57476 (by norm_num) pf hm hdl) hts) hdl
    hmn

end Principia.Common.TernaryGoldbach.OS
