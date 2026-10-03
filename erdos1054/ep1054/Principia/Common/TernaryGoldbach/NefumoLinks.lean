/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.NefumoSpine
import Principia.Common.TernaryGoldbach.ArcIntSpine
import Mathlib.Analysis.Fourier.Convolution

set_option autoImplicit false

/-!
# Links of `NefumoSpine` DISCHARGED: `ArcsReal`, `TailLink` (to `GatTail`), `HostoW` at `(η∘, η*)`

`NefumoSpine.nefumoW_of_links` reduces `RW.NefumoW` to eight links. This file proves three of
them, so that at Helfgott's weights
**`nefumoW_helf_rest : Massacre → GatTail → T3W η₊ η* → JokoW η₊ η* → RW.NefumoW η₊ η* η∘`** —
two arithmetic statements about `∑ μ²(q)/φ(q)²` and the two weight links whose printed proofs
are not valid in general (`NefumoSpine`, findings 1 and 2). Nothing here proves those four.

* **`arcsReal : ArcsReal`**, for every continuous `1`-periodic `f`: `AI.reduce_of` (disjoint arcs,
  the window, periodicity) and `AI.changeVar`, from `ArcIntSpine` (`ternvin.tex` 1272–1315).
* **`tailLink_of_gat : GatTail → TailLink`** (`eq:rusko`, `eq:boussole`, 1099–1142). `GatTail`
  is the arithmetic content of `eq:gat1o`/`eq:gat1e` (5713–5726) in the form 1121–1142 uses it:
  what the arcs miss of `𝔖₃(N)` at `δ` is `≤ 4.31004·max(1/r, |δ|/(δ₀r/2))`. The rest is
  analysis, PROVED: `sum_window` moves `∑_q` inside `∫_ℝ`; under `Madge`, `|η̂∘|²` and `|δ||η̂∘|²`
  are integrable (`maj_le`: `(1+|δ|)|η̂∘|² ≤ 4(|η∘|₁² + |η∘'''|₁²)/(1+δ²)`); on `[−4, 4]` Plancherel
  gives `|η∘|₂²/r`, beyond it `Madge` and `∫_4^∞ δ⁻⁵ = 1/1024` give `2L²/(64π⁶·600000·1024)`,
  and `(2π)⁶ ≥ (6.28)⁶` closes against `0.0012L²/(δ₀⁵r)` (`int_psi_le`).
  `GatTail` is TRUE with room: the missed mass is `≤ 0.394` of the bound at every tested `δ`
  (`scratchpad/nefumo/gattail.py`, exact sieve to `10⁷`, full series `2.8264200`).
* **`hostoW_helf : HostoW η∘ η*`** (`eq:hosto`, 1166–1178): `η∘ ∗ η∘` is continuous (compact
  support), in `L¹`, with transform `(𝓕η∘)² ∈ L¹` (`DP.integrable_ft_circ`), so Fourier inversion
  holds everywhere (`Continuous.fourierInv_fourier_eq`); one Fubini swap against `η* ∈ L¹` and
  `CT.ccon_eq` (`C(y) = ∫ (η∘∗η∘)(y−v)η*(v) dv`) finish. The generic `Hosto` stays OPEN: Mathlib's
  convolution theorem (`Real.fourier_mul_convolution_eq`) asks for continuous factors, and a
  general `η ∈ L¹ ∩ L²` on `(0,∞)` extended by `0` need not be.

## What remains for `RW.NefumoW HW.etaPlus HW.etaStar HW.etaCirc`

| link | kind | why it is open |
|---|---|---|
| `Massacre` | arithmetic | `∑_{q∈Qs} μ²/φ² = 2.8264114 ≤ 2.82643`; an Euler-product certificate |
| `GatTail` | arithmetic | tail sums of `μ²/φ²` (`lem:sidio`, `eq:merleau`) |
| `T3W η₊ η*` | weight | FALSE in general; TRUE here (`0.1001 ≤ 0.3332`, `NefumoSpine` finding 1) |
| `JokoW η₊ η*` | weight | `NefumoJoko.jokoW_of_links`: from `DPoint`, `SummW`, `ZvsL` |
-/

namespace Principia.Common.TernaryGoldbach.NF

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach Set
open scoped ArithmeticFunction

/-! ## [Arcs], PROVED -/

/-- **[Arcs] for every continuous `1`-periodic `f`**: `AI.reduce_of` splits `∫_𝔐` into the
arcs, `AI.changeVar` rescales each. -/
theorem arcsReal : ArcsReal := by
  intro x hx f hc hp
  have hx0 : 0 < x := AI.x_pos hx
  rw [AI.reduce_of AI.arcsDisjoint AI.windowCover AI.periodicShift x hx f hc hp]
  have e1 : AI.arcIdx = AI.Qs.sigma AI.cop := by
    unfold AI.arcIdx
    rfl
  have e2 : AI.Qs = Qs := by
    unfold AI.Qs Qs
    rfl
  have e3 : AI.cop = cop := by
    funext q
    unfold AI.cop cop
    rfl
  rw [e1, e2, e3, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h1 : ∀ a ∈ cop q, ∫ α in AI.arc x ⟨q, a⟩, f α =
      (∫ δ in (-wq q)..(wq q), f (pt x q a δ)) / x :=
    fun a _ => AI.changeVar x hx0 f ((a : ℝ) / q) (wq q) (wq_nonneg q)
  have hint : ∀ a ∈ cop q, IntervalIntegrable (fun δ => f (pt x q a δ)) volume
      (-wq q) (wq q) :=
    fun a _ => (hc.comp (continuous_pt x q a)).intervalIntegrable _ _
  rw [Finset.sum_congr rfl h1, ← Finset.sum_div, ← intervalIntegral.integral_finsetSum hint]

/-! ## [Tail] = [GatTail] + analysis -/

/-- `W_N(δ) = ∑_{q ∈ Qs, δ ∈ (−w_q, w_q]} T₃(q, N)`: the part of `𝔖₃(N)` the arcs keep at `δ`. -/
noncomputable def win (N : ℕ) (δ : ℝ) : ℝ :=
  ∑ q ∈ Qs, if δ ∈ Set.Ioc (-wq q) (wq q) then SingularSeries.sing3Local q N else 0

/-- **[GatTail]** (`eq:gat1o`, `eq:gat1e`, 5713–5726, as used at 1121–1142): what the arcs miss
at `δ` is `≤ 4.31004/min(r, δ₀r/2|δ|)`. OPEN; pure number theory. -/
def GatTail : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ δ : ℝ,
    |SingularSeries.sing3 N - win N δ| ≤ 4.31004 * max (1 / 150000) (|δ| / 600000)

/-- **Moving the `q`-sum inside the integral** (`eq:rusko`). -/
theorem sum_window (N : ℕ) (G : ℝ → ℂ) (hG : Integrable G) :
    ∑ q ∈ Qs, ((SingularSeries.sing3Local q N : ℝ) : ℂ) * (∫ δ in (-wq q)..(wq q), G δ) =
      ∫ δ, ((win N δ : ℝ) : ℂ) * G δ := by
  have h1 : ∀ q ∈ Qs, ((SingularSeries.sing3Local q N : ℝ) : ℂ) *
      (∫ δ in (-wq q)..(wq q), G δ) = ∫ δ, (Set.Ioc (-wq q) (wq q)).indicator
        (fun δ => ((SingularSeries.sing3Local q N : ℝ) : ℂ) * G δ) δ := by
    intro q _
    rw [intervalIntegral.integral_of_le (by linarith [wq_nonneg q]),
      integral_indicator measurableSet_Ioc, integral_const_mul]
  rw [Finset.sum_congr rfl h1, ← integral_finsetSum _ fun q _ =>
    (hG.const_mul _).indicator measurableSet_Ioc]
  refine integral_congr_ae (Filter.Eventually.of_forall fun δ => ?_)
  beta_reduce
  unfold win
  rw [Complex.ofReal_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases h : δ ∈ Set.Ioc (-wq q) (wq q)
  · rw [Set.indicator_of_mem h, if_pos h]
  · rw [Set.indicator_of_notMem h, if_neg h, Complex.ofReal_zero, zero_mul]

/-- The polynomial core of the majorant: `u ≤ a`, `u(2πt)³ ≤ L` give
`(1+t)u²(1+t²) ≤ 4(a² + L²)`. -/
theorem maj_poly (t u a L : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (hua : u ≤ a)
    (huL : t ≠ 0 → u * (2 * Real.pi * t) ^ 3 ≤ L) :
    (1 + t) * u ^ 2 * (1 + t ^ 2) ≤ 4 * (a ^ 2 + L ^ 2) := by
  rcases le_or_gt t 1 with h1 | h1
  · have hA : (1 + t) * (1 + t ^ 2) ≤ 4 := by nlinarith
    have hB : u ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hu hua 2
    have hC : (1 + t) * u ^ 2 * (1 + t ^ 2) = u ^ 2 * ((1 + t) * (1 + t ^ 2)) := by ring
    rw [hC]
    nlinarith [sq_nonneg L, sq_nonneg u]
  · have hL := huL (by linarith)
    have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have ht3 : t ^ 3 ≤ (2 * Real.pi * t) ^ 3 := by
      rw [mul_pow]
      nlinarith [pow_le_pow_left₀ (by norm_num) hpi 3, pow_nonneg ht 3]
    have hut : u * t ^ 3 ≤ L := le_trans (mul_le_mul_of_nonneg_left ht3 hu) hL
    have hut0 : 0 ≤ u * t ^ 3 := mul_nonneg hu (pow_nonneg ht 3)
    have hsq : (u * t ^ 3) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hut0 hut 2
    have h2a : 1 + t ≤ 2 * t := by linarith
    have h2b : 1 + t ^ 2 ≤ 2 * t ^ 2 := by nlinarith
    have h36 : t ^ 3 ≤ t ^ 6 := pow_le_pow_right₀ h1.le (by norm_num)
    have hA : (1 + t) * (1 + t ^ 2) ≤ 4 * t ^ 6 := by
      have := mul_le_mul h2a h2b (by positivity) (by positivity)
      nlinarith
    have hC : (1 + t) * u ^ 2 * (1 + t ^ 2) = u ^ 2 * ((1 + t) * (1 + t ^ 2)) := by ring
    rw [hC]
    have hD : u ^ 2 * ((1 + t) * (1 + t ^ 2)) ≤ u ^ 2 * (4 * t ^ 6) :=
      mul_le_mul_of_nonneg_left hA (sq_nonneg u)
    nlinarith [sq_nonneg a]

/-- **The majorant**: under `Madge`, `(1+|δ|)|η̂∘(−δ)|² ≤ 4(|η∘|₁² + |η∘'''|₁²)/(1+δ²)`. -/
theorem maj_le (ηo : ℝ → ℝ) (md : Madge ηo) (δ : ℝ) :
    (1 + |δ|) * ‖MajSp.mainFT ηo δ‖ ^ 2 ≤
      4 * (MajSp.l1 ηo ^ 2 + MajSp.l1 (iteratedDeriv 3 ηo) ^ 2) * (1 + δ ^ 2)⁻¹ := by
  have hpos : 0 < 1 + δ ^ 2 := by positivity
  have h := maj_poly |δ| ‖MajSp.mainFT ηo δ‖ (MajSp.l1 ηo) (MajSp.l1 (iteratedDeriv 3 ηo))
    (abs_nonneg δ) (norm_nonneg _) (norm_mainFT_le ηo δ) (fun ht => by
      have hδ : δ ≠ 0 := fun h0 => ht (by rw [h0, abs_zero])
      have hden : 0 < (2 * Real.pi * |δ|) ^ 3 :=
        pow_pos (mul_pos (mul_pos two_pos Real.pi_pos) (abs_pos.mpr hδ)) 3
      have := md δ hδ
      rwa [le_div_iff₀ hden] at this)
  rw [sq_abs] at h
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  exact h


/-- `|η̂∘|²` and `|δ|·|η̂∘|²` are integrable on `ℝ` under `Madge` (`η∘ ∈ L¹`). -/
theorem integrable_F2 (ηo : ℝ → ℝ) (ho1 : Integrable ηo (volume.restrict (Set.Ioi 0)))
    (md : Madge ηo) :
    Integrable (fun δ => ‖MajSp.mainFT ηo δ‖ ^ 2) ∧
      Integrable (fun δ => |δ| * ‖MajSp.mainFT ηo δ‖ ^ 2) := by
  have cF := (continuous_mainFT_of ηo ho1).norm
  have iK := integrable_inv_one_add_sq.const_mul
    (4 * (MajSp.l1 ηo ^ 2 + MajSp.l1 (iteratedDeriv 3 ηo) ^ 2))
  refine ⟨iK.mono' (cF.pow 2).aestronglyMeasurable (ae_of_all _ fun δ => ?_),
    iK.mono' ((continuous_abs.mul (cF.pow 2)).aestronglyMeasurable) (ae_of_all _ fun δ => ?_)⟩
  · rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h := maj_le ηo md δ
    nlinarith [abs_nonneg δ, sq_nonneg ‖MajSp.mainFT ηo δ‖,
      mul_nonneg (abs_nonneg δ) (sq_nonneg ‖MajSp.mainFT ηo δ‖)]
  · rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg δ) (sq_nonneg _))]
    have h := maj_le ηo md δ
    nlinarith [abs_nonneg δ, sq_nonneg ‖MajSp.mainFT ηo δ‖]

/-- **The weighted tail integral** (`eq:boussole`, 1125–1142): with
`|F(δ)| ≤ L/(2π|δ|)³`, `∫ max(1/r, |δ|/(δ₀r/2))|F|² ≤ ℓ²/r + 2L²/(64π⁶·600000·1024)`, where
`∫_{−4}^{4}|F|² ≤ ℓ²` (the arcs' window at `δ₀/2 = 4`). -/
theorem int_psi_le (F : ℝ → ℂ)
    (iψ : Integrable fun δ => max (1 / 150000) (|δ| / 600000) * ‖F δ‖ ^ 2)
    (L lo : ℝ) (hdec : ∀ δ, δ ≠ 0 → ‖F δ‖ ≤ L / (2 * Real.pi * |δ|) ^ 3)
    (hB : ∫ δ in (-4 : ℝ)..4, ‖F δ‖ ^ 2 ≤ lo ^ 2) :
    ∫ δ, max (1 / 150000) (|δ| / 600000) * ‖F δ‖ ^ 2 ≤
      lo ^ 2 / 150000 + L ^ 2 / (64 * Real.pi ^ 6 * 600000) * (2 / 1024) := by
  have hπ := Real.pi_pos
  have hpt : ∀ ξ : ℝ, 4 < ξ → ∀ s : ℝ, |s| = ξ →
      max (1 / 150000) (|s| / 600000) * ‖F s‖ ^ 2 ≤
        L ^ 2 / (64 * Real.pi ^ 6 * 600000) * ξ ^ (-5 : ℝ) := by
    intro ξ hξ s hs
    have hξ0 : 0 < ξ := by linarith
    have hs0 : s ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hs
      linarith
    have hmax : max (1 / 150000) (|s| / 600000) = ξ / 600000 := by
      rw [hs]
      exact max_eq_right (by linarith)
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (hdec s hs0) 2
    rw [hs] at h1
    rw [hmax, show (-5 : ℝ) = -((5 : ℕ) : ℝ) by norm_num, Real.rpow_neg hξ0.le,
      Real.rpow_natCast]
    have e1 : (L / (2 * Real.pi * ξ) ^ 3) ^ 2 = L ^ 2 / (64 * Real.pi ^ 6 * ξ ^ 6) := by
      field_simp
      ring
    rw [e1] at h1
    have h2 : ξ / 600000 * ‖F s‖ ^ 2 ≤ ξ / 600000 * (L ^ 2 / (64 * Real.pi ^ 6 * ξ ^ 6)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    refine le_trans h2 (le_of_eq ?_)
    field_simp
  have hIc : IntegrableOn (fun ξ : ℝ => L ^ 2 / (64 * Real.pi ^ 6 * 600000) * ξ ^ (-5 : ℝ))
      (Set.Ioi 4) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).const_mul _
  have hIB : ∫ ξ in Set.Ioi (4 : ℝ), L ^ 2 / (64 * Real.pi ^ 6 * 600000) * ξ ^ (-5 : ℝ) =
      L ^ 2 / (64 * Real.pi ^ 6 * 600000) * (1 / 1024) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)]
    norm_num
  have hR : ∫ ξ in Set.Ioi (4 : ℝ), max (1 / 150000) (|ξ| / 600000) * ‖F ξ‖ ^ 2 ≤
      ∫ ξ in Set.Ioi (4 : ℝ), L ^ 2 / (64 * Real.pi ^ 6 * 600000) * ξ ^ (-5 : ℝ) :=
    setIntegral_mono_on iψ.integrableOn hIc measurableSet_Ioi fun ξ hξ =>
      hpt ξ hξ ξ (abs_of_pos (by linarith [(Set.mem_Ioi.mp hξ)]))
  have hneg : Integrable fun ξ => max (1 / 150000) (|-ξ| / 600000) * ‖F (-ξ)‖ ^ 2 :=
    iψ.comp_neg
  have hL' : ∫ ξ in Set.Ioi (4 : ℝ), max (1 / 150000) (|-ξ| / 600000) * ‖F (-ξ)‖ ^ 2 ≤
      ∫ ξ in Set.Ioi (4 : ℝ), L ^ 2 / (64 * Real.pi ^ 6 * 600000) * ξ ^ (-5 : ℝ) :=
    setIntegral_mono_on hneg.integrableOn hIc measurableSet_Ioi fun ξ hξ =>
      hpt ξ hξ (-ξ) (by rw [abs_neg, abs_of_pos (by linarith [(Set.mem_Ioi.mp hξ)])])
  have hs1 := intervalIntegral.integral_Iic_add_Ioi (b := (4 : ℝ)) iψ.integrableOn
    iψ.integrableOn
  have hs2 := intervalIntegral.integral_Iic_sub_Iic (a := (-4 : ℝ)) (b := 4)
    iψ.integrableOn iψ.integrableOn
  have hs3 := integral_comp_neg_Ioi 4
    (fun ξ => max (1 / 150000) (|ξ| / 600000) * ‖F ξ‖ ^ 2)
  have hmid : ∫ ξ in (-4 : ℝ)..4, max (1 / 150000) (|ξ| / 600000) * ‖F ξ‖ ^ 2 =
      (1 / 150000) * ∫ ξ in (-4 : ℝ)..4, ‖F ξ‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun ξ hξ => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hξ
    have habs : |ξ| ≤ 4 := abs_le.mpr ⟨hξ.1, hξ.2⟩
    have hmax : max (1 / 150000) (|ξ| / 600000) = 1 / 150000 := max_eq_left (by linarith)
    rw [hmax]
  rw [hIB] at hR hL'
  have hBm : (1 / 150000) * ∫ ξ in (-4 : ℝ)..4, ‖F ξ‖ ^ 2 ≤ lo ^ 2 / 150000 := by linarith
  rw [hmid] at hs2
  linarith

/-- **[Tail] from [GatTail]**: the completion of the `q`-sum is analysis (`sum_window`, `Madge`,
Plancherel on `[−4, 4]`, the `δ⁻⁵` tails) once the arithmetic tail `GatTail` is granted. -/
theorem tailLink_of_gat (gt : GatTail) : TailLink := by
  intro ηo ηs ho1 ho2 hs1 md N hN y
  obtain ⟨iF, iT⟩ := integrable_F2 ηo ho1 md
  have cF := (continuous_mainFT_of ηo ho1).norm
  have hGc := continuous_gO ηo ηs ho1 hs1 y
  have hGle : ∀ δ, ‖gO ηo ηs y δ‖ ≤ MajSp.l1 ηs * ‖MajSp.mainFT ηo δ‖ ^ 2 := by
    intro δ
    unfold gO
    rw [norm_mul, norm_mul, norm_pow, e_norm, mul_one]
    have := norm_mainFT_le ηs δ
    nlinarith [sq_nonneg ‖MajSp.mainFT ηo δ‖]
  have hG : Integrable (gO ηo ηs y) :=
    (iF.const_mul (MajSp.l1 ηs)).mono' hGc.aestronglyMeasurable (ae_of_all _ hGle)
  have hWm : Measurable (win N) := by
    unfold win
    exact Finset.measurable_sum _ fun q _ =>
      Measurable.ite measurableSet_Ioc measurable_const measurable_const
  have hWb : ∀ δ, ‖((win N δ : ℝ) : ℂ)‖ ≤ ∑ q ∈ Qs, |SingularSeries.sing3Local q N| := by
    intro δ
    rw [Complex.norm_real, Real.norm_eq_abs]
    unfold win
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun q _ => ?_)
    split_ifs
    · exact le_rfl
    · rw [abs_zero]
      exact abs_nonneg _
  have hWG : Integrable fun δ => ((win N δ : ℝ) : ℂ) * gO ηo ηs y δ :=
    hG.bdd_mul (Complex.measurable_ofReal.comp hWm).aestronglyMeasurable (ae_of_all _ hWb)
  have iψ : Integrable fun δ => max (1 / 150000) (|δ| / 600000) *
      ‖MajSp.mainFT ηo δ‖ ^ 2 := by
    refine ((iF.const_mul (1 / 150000)).add (iT.const_mul (1 / 600000))).mono'
      ((continuous_const.max (continuous_abs.div_const _)).mul
        (cF.pow 2)).aestronglyMeasurable (ae_of_all _ fun δ => ?_)
    have hX : 0 ≤ ‖MajSp.mainFT ηo δ‖ ^ 2 := sq_nonneg _
    have hm : max (1 / 150000) (|δ| / 600000) ≤ 1 / 150000 + |δ| / 600000 :=
      max_le (by linarith [abs_nonneg δ]) (by norm_num)
    have hm0 : 0 ≤ max (1 / 150000) (|δ| / 600000) := le_trans (by norm_num) (le_max_left _ _)
    rw [Real.norm_of_nonneg (mul_nonneg hm0 hX)]
    have := mul_le_mul_of_nonneg_right hm hX
    simp only [Pi.add_apply]
    nlinarith
  rw [sum_window N _ hG, ← integral_const_mul, ← integral_sub hWG (hG.const_mul _)]
  have hbound : ∀ δ, ‖((win N δ : ℝ) : ℂ) * gO ηo ηs y δ -
      ((SingularSeries.sing3 N : ℝ) : ℂ) * gO ηo ηs y δ‖ ≤
        (4.31004 * MajSp.l1 ηs) * (max (1 / 150000) (|δ| / 600000) *
          ‖MajSp.mainFT ηo δ‖ ^ 2) := by
    intro δ
    rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_sub_comm]
    have h1 := gt N hN δ
    have hm0 : 0 ≤ 4.31004 * max (1 / 150000) (|δ| / 600000) :=
      mul_nonneg (by norm_num) (le_trans (by norm_num) (le_max_left _ _))
    calc |SingularSeries.sing3 N - win N δ| * ‖gO ηo ηs y δ‖
        ≤ 4.31004 * max (1 / 150000) (|δ| / 600000) *
            (MajSp.l1 ηs * ‖MajSp.mainFT ηo δ‖ ^ 2) :=
          mul_le_mul h1 (hGle δ) (norm_nonneg _) hm0
      _ = (4.31004 * MajSp.l1 ηs) * (max (1 / 150000) (|δ| / 600000) *
            ‖MajSp.mainFT ηo δ‖ ^ 2) := by ring
  refine le_trans (norm_integral_le_of_norm_le (iψ.const_mul _) (ae_of_all _ hbound)) ?_
  rw [integral_const_mul]
  have hB : ∫ δ in (-4 : ℝ)..4, ‖MajSp.mainFT ηo δ‖ ^ 2 ≤ MajSp.l2 ηo ^ 2 :=
    DP.mardiQ_of ηo ho1 (DP.sq_integrable_of_memLp _ ho2) 4 (by norm_num)
  have hI := int_psi_le (MajSp.mainFT ηo) iψ (MajSp.l1 (iteratedDeriv 3 ηo)) (MajSp.l2 ηo) md hB
  have hπ6 : (3.14 : ℝ) ^ 6 ≤ Real.pi ^ 6 := pow_le_pow_left₀ (by norm_num) Real.pi_gt_d2.le 6
  have hc : MajSp.l1 (iteratedDeriv 3 ηo) ^ 2 / (64 * Real.pi ^ 6 * 600000) ≤
      MajSp.l1 (iteratedDeriv 3 ηo) ^ 2 / (64 * 3.14 ^ 6 * 600000) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by nlinarith)
  have hl1 := MajSp.l1_nonneg ηs
  have hL2 := sq_nonneg (MajSp.l1 (iteratedDeriv 3 ηo))
  have hfin : 4.31004 * (MajSp.l2 ηo ^ 2 / 150000 +
      MajSp.l1 (iteratedDeriv 3 ηo) ^ 2 / (64 * 3.14 ^ 6 * 600000) * (2 / 1024)) ≤
        (4.31004 * MajSp.l2 ηo ^ 2 + 0.0012 * MajSp.l1 (iteratedDeriv 3 ηo) ^ 2 / 8 ^ 5) /
          150000 := by
    have hk : (4.31004 : ℝ) * (2 / 1024) / (64 * 3.14 ^ 6 * 600000) ≤ 0.0012 / 8 ^ 5 / 150000 := by
      norm_num
    have e1 : 4.31004 * (MajSp.l2 ηo ^ 2 / 150000 +
        MajSp.l1 (iteratedDeriv 3 ηo) ^ 2 / (64 * 3.14 ^ 6 * 600000) * (2 / 1024)) =
          4.31004 / 150000 * MajSp.l2 ηo ^ 2 + 4.31004 * (2 / 1024) / (64 * 3.14 ^ 6 * 600000) *
            MajSp.l1 (iteratedDeriv 3 ηo) ^ 2 := by ring
    have e2 : (4.31004 * MajSp.l2 ηo ^ 2 + 0.0012 * MajSp.l1 (iteratedDeriv 3 ηo) ^ 2 / 8 ^ 5) /
        150000 = 4.31004 / 150000 * MajSp.l2 ηo ^ 2 + 0.0012 / 8 ^ 5 / 150000 *
          MajSp.l1 (iteratedDeriv 3 ηo) ^ 2 := by ring
    rw [e1, e2]
    have := mul_le_mul_of_nonneg_right hk hL2
    linarith
  have hI' : ∫ δ, max (1 / 150000) (|δ| / 600000) * ‖MajSp.mainFT ηo δ‖ ^ 2 ≤
      MajSp.l2 ηo ^ 2 / 150000 +
        MajSp.l1 (iteratedDeriv 3 ηo) ^ 2 / (64 * 3.14 ^ 6 * 600000) * (2 / 1024) := by
    nlinarith
  have := mul_le_mul_of_nonneg_left hI' (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4.31004) hl1)
  nlinarith


/-! ## [Hosto] at Helfgott's weights, PROVED -/

section Hosto

open scoped FourierTransform

/-- `η∘` on `ℝ`, complex-valued (`= DP.zext η∘`). -/
noncomputable def fC : ℝ → ℂ := fun t => ((HW.etaCirc t : ℝ) : ℂ)

/-- `η*` on `ℝ`, complex-valued (`= DP.zext η*`). -/
noncomputable def sC : ℝ → ℂ := fun t => ((HW.etaStar t : ℝ) : ℂ)

/-- `η∘ ∗ η∘` (Mathlib's convolution, `L = ·`). -/
noncomputable def cC : ℝ → ℂ := MeasureTheory.convolution fC fC (ContinuousLinearMap.mul ℂ ℂ) volume

theorem zext_star : DP.zext HW.etaStar = sC := by
  funext t
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · rw [DP.zext, indicator_of_mem ht]
    rfl
  · rw [DP.zext, indicator_of_notMem ht]
    unfold sC
    rw [CT.star_zero t ht, Complex.ofReal_zero]

theorem integrable_fC : Integrable fC := by
  have h := DP.integrable_zext_circ
  rwa [DP.zext_circ] at h

theorem continuous_fC : Continuous fC := by
  have h := DP.continuous_zext_circ
  rwa [DP.zext_circ] at h

theorem integrable_sC : Integrable sC := CT.integrable_star.ofReal

/-- `(η∘ ∗ η∘)(u) = CT.selfConv u`. -/
theorem cC_eq (u : ℝ) : cC u = ((CT.selfConv u : ℝ) : ℂ) := by
  unfold cC CT.selfConv
  rw [MeasureTheory.convolution_def, ← integral_complex_ofReal]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [ContinuousLinearMap.mul_apply', fC]
  push_cast
  ring

theorem continuous_cC : Continuous cC :=
  HasCompactSupport.continuous_convolution_left (ContinuousLinearMap.mul ℂ ℂ)
    (CT.hcs_circ.comp_left Complex.ofReal_zero) continuous_fC
    continuous_fC.locallyIntegrable

theorem integrable_cC : Integrable cC :=
  integrable_fC.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) integrable_fC

/-- `𝓕(η∘ ∗ η∘) = (𝓕η∘)²` (Mathlib's convolution theorem; `η∘` is continuous). -/
theorem fourier_cC (ξ : ℝ) : 𝓕 cC ξ = 𝓕 fC ξ * 𝓕 fC ξ :=
  Real.fourier_mul_convolution_eq integrable_fC integrable_fC continuous_fC continuous_fC ξ

theorem integrable_fourier_cC : Integrable (𝓕 cC) := by
  have hF : Integrable (𝓕 fC) := by
    have h := DP.integrable_ft_circ
    rwa [DP.zext_circ] at h
  have hb : ∀ ξ, ‖𝓕 fC ξ‖ ≤ ∫ t, ‖fC t‖ := FourierBessel.norm_fourier_le fC
  have h := hF.mul_bdd hF.aestronglyMeasurable (ae_of_all _ hb)
  have e : 𝓕 cC = fun ξ => 𝓕 fC ξ * 𝓕 fC ξ := funext fourier_cC
  rw [e]
  exact h

/-- **`eq:hosto` at Helfgott's `(η∘, η*)`**: `∫ η̂∘(−δ)²η̂*(−δ)e(−δy) dδ = C_{η∘,η*}(y)`. Fourier
inversion for `η∘ ∗ η∘` (continuous, `L¹`, transform `(𝓕η∘)² ∈ L¹`), one Fubini swap against
`η* ∈ L¹`, and `CT.ccon_eq`. -/
theorem hostoW_helf : HostoW HW.etaCirc HW.etaStar := by
  intro y
  have hF : ∀ δ, MajSp.mainFT HW.etaCirc δ = 𝓕 fC (-δ) := fun δ => by
    rw [DP.mainFT_eq, DP.zext_circ]
    rfl
  have hS : ∀ δ, MajSp.mainFT HW.etaStar δ = 𝓕 sC (-δ) := fun δ => by
    rw [DP.mainFT_eq, zext_star]
  -- (1) substitute `ξ = −δ`
  have h1 : ∫ δ, gO HW.etaCirc HW.etaStar y δ =
      ∫ ξ, 𝓕 cC ξ * 𝓕 sC ξ * e (ξ * y) := by
    rw [← integral_neg_eq_self (fun ξ => 𝓕 cC ξ * 𝓕 sC ξ * e (ξ * y)) volume]
    refine integral_congr_ae (ae_of_all _ fun δ => ?_)
    simp only
    unfold gO
    rw [hF, hS, fourier_cC, neg_mul]
    ring
  -- (2) Fubini
  have hker : Integrable (Function.uncurry fun ξ v : ℝ =>
      𝓕 cC ξ * e (ξ * y) * (Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) * sC v))
      (volume.prod volume) := by
    have hb : Integrable (fun p : ℝ × ℝ => ‖𝓕 cC p.1‖ * ‖sC p.2‖) (volume.prod volume) :=
      integrable_fourier_cC.norm.mul_prod integrable_sC.norm
    have hcF : Continuous (𝓕 cC) := FourierBessel.continuous_fourier _ integrable_cC
    have hm : AEStronglyMeasurable (Function.uncurry fun ξ v : ℝ =>
        𝓕 cC ξ * e (ξ * y) * (Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) * sC v))
        (volume.prod volume) := by
      have hc : Continuous fun p : ℝ × ℝ =>
          𝓕 cC p.1 * e (p.1 * y) * Complex.exp (↑(-2 * Real.pi * p.2 * p.1) * Complex.I) := by
        have := Spine.continuous_e
        fun_prop
      have hs : AEStronglyMeasurable (fun p : ℝ × ℝ => sC p.2) (volume.prod volume) :=
        integrable_sC.aestronglyMeasurable.comp_snd
      have := hc.aestronglyMeasurable.mul hs
      refine this.congr (ae_of_all _ fun p => ?_)
      simp only [Function.uncurry, Pi.mul_apply]
      ring
    refine hb.mono' hm (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry]
    rw [norm_mul, norm_mul, norm_mul, e_norm, mul_one, Complex.norm_exp_ofReal_mul_I, one_mul]
  have h2 : ∫ ξ, 𝓕 cC ξ * 𝓕 sC ξ * e (ξ * y) =
      ∫ v, (∫ ξ, Complex.exp (↑(2 * Real.pi * (y - v) * ξ) * Complex.I) * 𝓕 cC ξ) * sC v := by
    have e1 : ∀ ξ, 𝓕 cC ξ * 𝓕 sC ξ * e (ξ * y) = ∫ v, 𝓕 cC ξ * e (ξ * y) *
        (Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) * sC v) := by
      intro ξ
      rw [FourierBessel.fourier_eq_exp sC ξ, integral_const_mul]
      ring
    rw [integral_congr_ae (ae_of_all _ e1), integral_integral_swap hker]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    simp only
    rw [← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    simp only
    have hexp : e (ξ * y) * Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) =
        Complex.exp (↑(2 * Real.pi * (y - v) * ξ) * Complex.I) := by
      unfold e
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc 𝓕 cC ξ * e (ξ * y) * (Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) * sC v)
        = 𝓕 cC ξ * (e (ξ * y) * Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I)) * sC v := by
          ring
      _ = Complex.exp (↑(2 * Real.pi * (y - v) * ξ) * Complex.I) * 𝓕 cC ξ * sC v := by
          rw [hexp]
          ring
  -- (3) inversion
  have hinv := continuous_cC.fourierInv_fourier_eq integrable_cC integrable_fourier_cC
  have h3 : ∀ v, ∫ ξ, Complex.exp (↑(2 * Real.pi * (y - v) * ξ) * Complex.I) * 𝓕 cC ξ =
      cC (y - v) := fun v => by
    rw [← FourierBessel.fourierInv_eq_exp, hinv]
  -- (4) back to `ccon`
  rw [h1, h2, CT.ccon_eq, ← integral_complex_ofReal]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only
  rw [h3, cC_eq]
  unfold sC
  push_cast
  ring

end Hosto

/-! ## The compositions -/

/-- **`RW.NefumoW` with [Arcs] and [Tail] discharged**: [Massacre], [GatTail] and the weight links
remain. Application only. -/
theorem nefumoW_of_rest (ms : Massacre) (gt : GatTail) (ηp ηs ηo : ℝ → ℝ) (oi : OInt ηo)
    (md : Madge ηo) (hw : HostoW ηo ηs) (t3 : T3W ηp ηs) (jk : JokoW ηp ηs) :
    RW.NefumoW ηp ηs ηo :=
  nefumoW_of_links arcsReal ms (tailLink_of_gat gt) ηp ηs ηo oi md hw t3 jk

/-- **`RW.NefumoW` at Helfgott's weights from four links**: two arithmetic (`Massacre`,
`GatTail`) and two weight links (`T3W`, `JokoW` at `(η₊, η*)`). Application only. -/
theorem nefumoW_helf_rest (ms : Massacre) (gt : GatTail) (t3 : T3W HW.etaPlus HW.etaStar)
    (jk : JokoW HW.etaPlus HW.etaStar) : RW.NefumoW HW.etaPlus HW.etaStar HW.etaCirc :=
  nefumoW_helf arcsReal ms (tailLink_of_gat gt) hostoW_helf t3 jk

end Principia.Common.TernaryGoldbach.NF
