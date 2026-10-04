/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.AgamonRectRes
import Principia.Common.TernaryGoldbach.AgamonLDFE

set_option autoImplicit false

/-!
# Local residues of `−(L'/L)·Φ·x^s`

Generic facts feeding `EF.Rectangle`:
* `logDeriv_sub_order`: at a point where `f` is analytic of finite order `n`,
  `f'/f − n/(s − p)` is bounded on a punctured neighbourhood (`f = (s − p)^n g`, `g(p) ≠ 0`);
* `logDeriv_sub_pole`: if `f = g/(s − p)` near `p` with `g` analytic, `g(p) ≠ 0`, then
  `f'/f + 1/(s − p)` is bounded there (the simple pole of `ζ` at `1`);
* `mul_principal`: a principal part `c/(s − p)` of `F` becomes `c·h(p)/(s − p)` for `F·h`, `h`
  analytic at `p` (the dslope of `h` is bounded).
-/

namespace Principia.Common.TernaryGoldbach.AG

open Complex Set Filter Topology Asymptotics

/-- A function continuous at `p` is bounded on a punctured neighbourhood. -/
theorem bigO_one_of_contAt {g : ℂ → ℂ} {p : ℂ} (hg : ContinuousAt g p) :
    g =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
  (hg.norm.isBoundedUnder_le.isBigO_one ℂ).mono nhdsWithin_le_nhds

/-- `logDeriv g` is continuous at `p` if `g` is analytic at `p` with `g(p) ≠ 0`. -/
theorem continuousAt_logDeriv {g : ℂ → ℂ} {p : ℂ} (hg : AnalyticAt ℂ g p) (hgp : g p ≠ 0) :
    ContinuousAt (logDeriv g) p := by
  have h1 : ContinuousAt (deriv g) p := hg.deriv.continuousAt
  exact h1.div hg.continuousAt hgp

/-- **`f'/f − n/(s − p) = O(1)`** near a point of finite analytic order `n`. -/
theorem logDeriv_sub_order {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p)
    (hord : analyticOrderAt f p ≠ ⊤) :
    (logDeriv f - fun s => (analyticOrderNatAt f p : ℂ) / (s - p)) =O[𝓝[≠] p]
      (1 : ℂ → ℂ) := by
  obtain ⟨g, hg, hgp, hfg⟩ := (hf.analyticOrderAt_ne_top).mp hord
  set n := analyticOrderNatAt f p with hn
  have hev : ∀ᶠ z in 𝓝 p, (f z = (z - p) ^ n • g z) ∧ AnalyticAt ℂ g z ∧ g z ≠ 0 :=
    hfg.and (hg.eventually_analyticAt.and (hg.continuousAt.eventually_ne hgp))
  obtain ⟨U, hUsub, hUo, hpU⟩ := eventually_nhds_iff.mp hev
  have heq : (logDeriv f - fun s => (n : ℂ) / (s - p)) =ᶠ[𝓝[≠] p] logDeriv g := by
    filter_upwards [nhdsWithin_le_nhds (hUo.mem_nhds hpU), self_mem_nhdsWithin] with z hzU hzp
    obtain ⟨-, hgz, hgz0⟩ := hUsub z hzU
    have hzp' : z - p ≠ 0 := sub_ne_zero.mpr hzp
    have hloc : f =ᶠ[𝓝 z] fun w => (w - p) ^ n * g w := by
      filter_upwards [hUo.mem_nhds hzU] with w hw
      rw [(hUsub w hw).1, smul_eq_mul]
    have hd1 : DifferentiableAt ℂ (fun w : ℂ => (w - p) ^ n) z := by fun_prop
    have hlog : logDeriv f z = logDeriv (fun w : ℂ => (w - p) ^ n) z + logDeriv g z := by
      rw [logDeriv_apply, logDeriv_apply, hloc.deriv_eq, hloc.eq_of_nhds]
      rw [← logDeriv_apply, ← logDeriv_apply,
        logDeriv_mul (f := fun w : ℂ => (w - p) ^ n) (g := g) z (pow_ne_zero n hzp') hgz0 hd1
          hgz.differentiableAt]
    have hpow : logDeriv (fun w : ℂ => (w - p) ^ n) z = (n : ℂ) / (z - p) := by
      rw [logDeriv_fun_pow (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w - p) z),
        logDeriv_apply]
      have hd : deriv (fun w : ℂ => w - p) z = 1 := by
        simp
      rw [hd]
      field_simp
    simp only [Pi.sub_apply]
    rw [hlog, hpow]
    ring
  exact (bigO_one_of_contAt (continuousAt_logDeriv hg hgp)).congr' heq.symm
    (Eventually.of_forall fun _ => rfl)

/-- **`f'/f + 1/(s − p) = O(1)`** near a simple pole `f = g/(s − p)`, `g(p) ≠ 0`. -/
theorem logDeriv_sub_pole {f g : ℂ → ℂ} {p : ℂ} (hg : AnalyticAt ℂ g p) (hgp : g p ≠ 0)
    (hfg : ∀ᶠ z in 𝓝[≠] p, f z = g z / (z - p)) :
    (logDeriv f - fun s => (-1 : ℂ) / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have hev : ∀ᶠ z in 𝓝 p, AnalyticAt ℂ g z ∧ g z ≠ 0 :=
    hg.eventually_analyticAt.and (hg.continuousAt.eventually_ne hgp)
  obtain ⟨U, hUsub, hUo, hpU⟩ := eventually_nhds_iff.mp hev
  -- the punctured neighbourhood where `f = g/(s − p)`
  obtain ⟨V, hVsub, hVo, hpV⟩ : ∃ V : Set ℂ, (∀ z ∈ V, z ≠ p → f z = g z / (z - p)) ∧
      IsOpen V ∧ p ∈ V := by
    rw [eventually_nhdsWithin_iff, eventually_nhds_iff] at hfg
    obtain ⟨V, hV, hVo, hpV⟩ := hfg
    exact ⟨V, fun z hz hzp => hV z hz hzp, hVo, hpV⟩
  have heq : (logDeriv f - fun s => (-1 : ℂ) / (s - p)) =ᶠ[𝓝[≠] p] logDeriv g := by
    filter_upwards [nhdsWithin_le_nhds ((hUo.inter hVo).mem_nhds ⟨hpU, hpV⟩),
      self_mem_nhdsWithin] with z hz hzp
    obtain ⟨hgz, hgz0⟩ := hUsub z hz.1
    have hzp' : z - p ≠ 0 := sub_ne_zero.mpr hzp
    have hloc : f =ᶠ[𝓝 z] fun w => g w / (w - p) := by
      filter_upwards [(hVo.inter isOpen_compl_singleton).mem_nhds ⟨hz.2, hzp⟩] with w hw
      exact hVsub w hw.1 hw.2
    have hd1 : DifferentiableAt ℂ (fun w : ℂ => w - p) z := by fun_prop
    have hlog : logDeriv f z = logDeriv g z - logDeriv (fun w : ℂ => w - p) z := by
      rw [logDeriv_apply, logDeriv_apply, hloc.deriv_eq, hloc.eq_of_nhds]
      rw [← logDeriv_apply, ← logDeriv_apply,
        logDeriv_div (f := g) (g := fun w : ℂ => w - p) z hgz0 hzp' hgz.differentiableAt hd1]
    have hlin : logDeriv (fun w : ℂ => w - p) z = 1 / (z - p) := by
      rw [logDeriv_apply]
      simp
    simp only [Pi.sub_apply]
    rw [hlog, hlin]
    ring
  exact (bigO_one_of_contAt (continuousAt_logDeriv hg hgp)).congr' heq.symm
    (Eventually.of_forall fun _ => rfl)

/-- **Principal parts multiply by an analytic factor**: if `F − c/(s − p) = O(1)` and `h` is
differentiable at `p`, then `F·h − c·h(p)/(s − p) = O(1)`. -/
theorem mul_principal {F h : ℂ → ℂ} {p c : ℂ}
    (hF : (F - fun s => c / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) (hh : DifferentiableAt ℂ h p) :
    ((fun s => F s * h s) - fun s => c * h p / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have hhb : h =O[𝓝[≠] p] (1 : ℂ → ℂ) := bigO_one_of_contAt hh.continuousAt
  have hds : (dslope h p) =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
    bigO_one_of_contAt (continuousAt_dslope_same.mpr hh)
  have h0 : (fun s => (F s - c / (s - p)) * h s) =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
    (hF.mul hhb).congr' (Eventually.of_forall fun _ => rfl)
      (Eventually.of_forall fun _ => by simp)
  have h1 := h0.add (hds.const_mul_left c)
  refine h1.congr' ?_ (Eventually.of_forall fun _ => by simp)
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hsp : s - p ≠ 0 := sub_ne_zero.mpr hs
  simp only [Pi.sub_apply, dslope_of_ne _ hs, slope_def_field]
  field_simp
  ring

end Principia.Common.TernaryGoldbach.AG
