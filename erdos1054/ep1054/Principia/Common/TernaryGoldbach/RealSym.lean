/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajHaus
import Mathlib.Analysis.Calculus.Deriv.Star

set_option autoImplicit false

/-!
# `HM.RealSym` PROVED: the zeros of `L(s, χ)` for a real `χ` are symmetric under conjugation

`HelfMajHaus.hausierer_of'` reduces `HM.Hausierer` to `AbelZeros` and `RealSym`. `RealSym` asks,
for a real Dirichlet character `χ` (`HM.IsRealChar`: `χ(a)` real for every `a`), that
`s ∈ zeroSet χ → s̄ ∈ zeroSet χ` and `zmult χ s̄ = zmult χ s`.

* `lseries_conj`: `conj L(s̄) = L(s)` on `Re s > 1`, termwise: `χ(n)` is real and
  `conj(n^{s̄}) = n^s` (`Complex.cpow_conj`, `arg n = 0`).
* `lfun_conj`: `L(s̄, χ) = conj L(s, χ)` for every `s ≠ 1`. `L` and `conj ∘ L ∘ conj` are analytic
  on the connected set `ℂ ∖ {1}` and agree near `2`, so the identity theorem applies.
* `analyticOrderAt_cc`: the analytic order of `conj ∘ f ∘ conj` at `z` equals that of `f` at `z̄`,
  from the characterisation `f = (w − z₀)ⁿ g`, `g(z₀) ≠ 0`.
* `realSym : HM.RealSym`.
-/

namespace Principia.Common.TernaryGoldbach.RSy

open Complex Filter Topology
open scoped ComplexConjugate

/-- `conj ∘ f ∘ conj`. -/
noncomputable def cc (f : ℂ → ℂ) : ℂ → ℂ := conj ∘ f ∘ conj

theorem cc_apply (f : ℂ → ℂ) (w : ℂ) : cc f w = conj (f (conj w)) := rfl

theorem cc_cc (f : ℂ → ℂ) : cc (cc f) = f := by
  funext w
  simp [cc]

/-- `conj ∘ f ∘ conj` is analytic at `z` when `f` is analytic at `z̄`. -/
theorem analyticAt_cc {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f (conj z)) :
    AnalyticAt ℂ (cc f) z := by
  rw [analyticAt_iff_eventually_differentiableAt] at hf ⊢
  have h := (Complex.continuous_conj.tendsto z).eventually hf
  exact h.mono fun w hw => differentiableAt_conj_conj_iff.mpr hw

/-- **The analytic order of `conj ∘ f ∘ conj` at `z` is that of `f` at `z̄`.** -/
theorem analyticOrderAt_cc (f : ℂ → ℂ) (z : ℂ) :
    analyticOrderAt (cc f) z = analyticOrderAt f (conj z) := by
  by_cases hf : AnalyticAt ℂ f (conj z)
  · have hc := analyticAt_cc hf
    by_cases htop : analyticOrderAt f (conj z) = ⊤
    · rw [htop, analyticOrderAt_eq_top]
      rw [analyticOrderAt_eq_top] at htop
      have h := (Complex.continuous_conj.tendsto z).eventually htop
      exact h.mono fun w hw => by rw [cc_apply, hw, map_zero]
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
      rw [← hn]
      obtain ⟨g, hg, hg0, hfg⟩ := (hf.analyticOrderAt_eq_natCast (n := n)).mp hn.symm
      refine (hc.analyticOrderAt_eq_natCast (n := n)).mpr ⟨cc g, analyticAt_cc (by simpa using hg),
        by simpa [cc_apply] using hg0, ?_⟩
      have h := (Complex.continuous_conj.tendsto z).eventually hfg
      refine h.mono fun w hw => ?_
      rw [cc_apply, hw, smul_eq_mul, smul_eq_mul, map_mul, map_pow, map_sub, conj_conj, conj_conj,
        cc_apply]
  · have hc : ¬ AnalyticAt ℂ (cc f) z := by
      intro h
      apply hf
      have := analyticAt_cc (f := cc f) (z := conj z) (by simpa using h)
      rwa [cc_cc] at this
    rw [analyticOrderAt_of_not_analyticAt hf, analyticOrderAt_of_not_analyticAt hc]

variable {q : ℕ} [NeZero q]

/-- `conj (n^{s̄}) = n^s` for a natural number `n`. -/
theorem conj_natCast_cpow (n : ℕ) (s : ℂ) : conj ((n : ℂ) ^ conj s) = (n : ℂ) ^ s := by
  rw [cpow_conj (n : ℂ) s (by rw [natCast_arg]; exact Real.pi_ne_zero.symm), conj_natCast,
    conj_conj]

omit [NeZero q] in
/-- **The Dirichlet series of a real character commutes with conjugation**, for `Re s > 1`. -/
theorem lseries_conj (χ : DirichletCharacter ℂ q) (hχ : HM.IsRealChar χ) (s : ℂ) :
    conj (LSeries (fun n : ℕ => χ n) (conj s)) = LSeries (fun n : ℕ => χ n) s := by
  unfold LSeries
  rw [Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  unfold LSeries.term
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn, if_neg hn, map_div₀, hχ, conj_natCast_cpow]

/-- **`L(s̄, χ) = conj L(s, χ)` for a real `χ` and `s ≠ 1`**, by the identity theorem on
`ℂ ∖ {1}`. -/
theorem lfun_conj (χ : DirichletCharacter ℂ q) (hχ : HM.IsRealChar χ) (s : ℂ) (hs : s ≠ 1) :
    DirichletCharacter.LFunction χ (conj s) = conj (DirichletCharacter.LFunction χ s) := by
  set L := DirichletCharacter.LFunction χ with hL
  have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hLan : AnalyticOnNhd ℂ L {1}ᶜ := (analyticOnNhd_iff_differentiableOn hU).mpr
    fun w hw =>
      (DirichletCharacter.differentiableAt_LFunction χ w (Or.inl hw)).differentiableWithinAt
  have hcan : AnalyticOnNhd ℂ (cc L) {1}ᶜ := by
    intro w hw
    refine analyticAt_cc (hLan (conj w) ?_)
    intro h
    apply hw
    have : conj (conj w) = conj 1 := by rw [h]
    simpa using this
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; exact Cardinal.one_lt_two) 1).isPreconnected
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  have hev : L =ᶠ[𝓝 2] cc L := by
    have hre : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
    filter_upwards [hre] with w hw
    have hw' : 1 < (conj w).re := by rwa [conj_re]
    rw [cc_apply, hL, DirichletCharacter.LFunction_eq_LSeries χ hw,
      DirichletCharacter.LFunction_eq_LSeries χ hw', lseries_conj χ hχ w]
  have heq := hLan.eqOn_of_preconnected_of_eventuallyEq hcan hconn h2 hev
  have hs' : conj s ∈ ({1}ᶜ : Set ℂ) := by
    intro h
    apply hs
    have : conj (conj s) = conj 1 := by rw [Set.mem_singleton_iff.mp h]
    simpa using this
  rw [heq hs', cc_apply, conj_conj]

/-- **`HM.RealSym` PROVED.** -/
theorem realSym : HM.RealSym := by
  intro q _ χ hχ s
  have hL : ∀ w : ℂ, w ≠ 1 →
      DirichletCharacter.LFunction χ (conj w) = conj (DirichletCharacter.LFunction χ w) :=
    fun w hw => lfun_conj χ hχ w hw
  constructor
  · rintro ⟨h0, hre0, hre1⟩
    have hs1 : s ≠ 1 := by
      intro h
      rw [h, one_re] at hre1
      exact lt_irrefl _ hre1
    refine ⟨?_, by rwa [conj_re], by rwa [conj_re]⟩
    rw [hL s hs1, h0, map_zero]
  · unfold HM.zmult
    by_cases hs1 : s = 1
    · rw [hs1, map_one]
    · have hs1' : conj s ≠ 1 := by
        intro h
        apply hs1
        have : conj (conj s) = conj 1 := by rw [h]
        simpa using this
      have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 (conj s)]
          cc (DirichletCharacter.LFunction χ) := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hs1'] with w hw
        rw [cc_apply]
        have hw' : conj w ≠ 1 := by
          intro h
          apply hw
          have : conj (conj w) = conj 1 := by rw [h]
          simpa using this
        have h := hL (conj w) hw'
        rw [conj_conj] at h
        exact h
      have hord : analyticOrderAt (DirichletCharacter.LFunction χ) (conj s) =
          analyticOrderAt (DirichletCharacter.LFunction χ) s := by
        rw [analyticOrderAt_congr hev, analyticOrderAt_cc, conj_conj]
      unfold analyticOrderNatAt
      rw [hord]

end Principia.Common.TernaryGoldbach.RSy
