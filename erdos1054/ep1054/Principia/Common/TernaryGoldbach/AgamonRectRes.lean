/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.PNT.Medium.ResidueCalcOnRectangles

set_option autoImplicit false

/-!
# The residue theorem on a rectangle with finitely many simple poles

**`rect_residue_finset`**: if `f` is holomorphic on the closed rectangle minus a finite set `P` of
interior points, and at each `p ∈ P` the difference `f − c(p)/(s − p)` is bounded on a punctured
neighbourhood, then `RectangleIntegral' f z w = ∑_{p ∈ P} c(p)`.

PNT+ (Kontorovich–Tao et al.) proves the one-pole case `ResidueTheoremOnRectangleWithSimplePole'`
(ported in `Common/PNT/Medium/ResidueCalcOnRectangles`); the finite case here is an induction on
`P`: subtract the principal part at one pole, remove the singularity there
(`existsDifferentiableOn_of_bddAbove` on a small neighbourhood avoiding the other poles), apply the
induction hypothesis, and add back `RectangleIntegral'(c/(s − p)) = c`
(`ResidueTheoremInRectangle`). This is the "port" half of `EF.Rectangle`; PNT+'s general
`RectangleIntegral'_eq_sumResiduesIn` (meromorphic normal forms) is not needed.
-/

namespace Principia.Common.TernaryGoldbach.AG

open Complex Set Filter Topology Asymptotics

/-- A principal part `c/(s − p₀)` is bounded near every `p ≠ p₀`. -/
theorem principal_isBigO_one {p p₀ c : ℂ} (h : p ≠ p₀) :
    (fun s : ℂ => c / (s - p₀)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have hc : ContinuousAt (fun s : ℂ => c / (s - p₀)) p :=
    continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr h)
  exact (hc.norm.isBoundedUnder_le.isBigO_one ℂ).mono nhdsWithin_le_nhds

/-- **The residue theorem on a rectangle, finitely many simple poles.** -/
theorem rect_residue_finset {z w : ℂ} (hzw1 : z.re ≤ w.re) (hzw2 : z.im ≤ w.im)
    (P : Finset ℂ) (c : ℂ → ℂ) :
    ∀ f : ℂ → ℂ, (∀ p ∈ P, Rectangle z w ∈ 𝓝 p) → HolomorphicOn f (Rectangle z w \ ↑P) →
      (∀ p ∈ P, (f - fun s => c p / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) →
        RectangleIntegral' f z w = ∑ p ∈ P, c p := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    intro f _ hf _
    rw [Finset.coe_empty, sdiff_empty] at hf
    rw [Finset.sum_empty, RectangleIntegral', hf.vanishesOnRectangle subset_rfl, smul_zero]
  | insert p₀ P' hp₀ ih =>
    intro f hint hf hloc
    have hint₀ : Rectangle z w ∈ 𝓝 p₀ := hint p₀ (Finset.mem_insert_self _ _)
    have hint' : ∀ p ∈ P', Rectangle z w ∈ 𝓝 p := fun p hp =>
      hint p (Finset.mem_insert_of_mem hp)
    set g : ℂ → ℂ := f - fun s => c p₀ / (s - p₀) with hg
    -- `g` is holomorphic off the poles
    have hgh : HolomorphicOn g (Rectangle z w \ ↑(insert p₀ P')) := by
      refine hf.sub ?_
      intro s hs
      have hs0 : s ≠ p₀ := fun h => hs.2 (by rw [h]; simp)
      have hne : s - p₀ ≠ 0 := sub_ne_zero.mpr hs0
      exact (show DifferentiableAt ℂ (fun u : ℂ => c p₀ / (u - p₀)) s by
        fun_prop (disch := exact hne)).differentiableWithinAt
    -- a neighbourhood of `p₀` where `g` is bounded and holomorphic off `p₀`
    obtain ⟨V, hV, hVb⟩ := IsBigO_to_BddAbove (hloc p₀ (Finset.mem_insert_self _ _))
    have hP'c : (↑P' : Set ℂ)ᶜ ∈ 𝓝 p₀ :=
      (P'.finite_toSet.isClosed.isOpen_compl).mem_nhds (by simpa using hp₀)
    set s : Set ℂ := V ∩ Rectangle z w ∩ (↑P')ᶜ with hs
    have hsn : s ∈ 𝓝 p₀ := Filter.inter_mem (Filter.inter_mem hV hint₀) hP'c
    have hgs : HolomorphicOn g (s \ {p₀}) := hgh.mono fun x hx => by
      refine ⟨hx.1.1.2, ?_⟩
      intro hmem
      rcases Finset.mem_insert.mp hmem with h | h
      · exact hx.2 h
      · exact hx.1.2 h
    have hgb : BddAbove (norm ∘ g '' (s \ {p₀})) :=
      BddAbove.mono (image_mono fun x (hx : x ∈ s \ {p₀}) =>
        (⟨hx.1.1.1, hx.2⟩ : x ∈ V \ {p₀})) hVb
    obtain ⟨G, hG, hGe⟩ := existsDifferentiableOn_of_bddAbove hsn hgs hgb
    -- `F = g` off `p₀`, holomorphic at `p₀`
    set F : ℂ → ℂ := Function.update g p₀ (G p₀) with hF
    have hFG : EqOn F G s := by
      intro x hx
      by_cases h : x = p₀
      · rw [h, hF, Function.update_self]
      · rw [hF, Function.update_of_ne h]
        exact hGe ⟨hx, h⟩
    have hFp₀ : DifferentiableAt ℂ F p₀ :=
      ((hG.congr hFG).differentiableAt hsn)
    have hFoff : ∀ x, x ≠ p₀ → F =ᶠ[𝓝 x] g := by
      intro x hx
      filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
      rw [hF, Function.update_of_ne hy]
    have hFh : HolomorphicOn F (Rectangle z w \ ↑P') := by
      intro x hx
      by_cases h : x = p₀
      · rw [h]
        exact hFp₀.differentiableWithinAt
      · have hgx : DifferentiableWithinAt ℂ g (Rectangle z w \ ↑(insert p₀ P')) x := by
          refine hgh x ⟨hx.1, ?_⟩
          intro hmem
          rcases Finset.mem_insert.mp hmem with h' | h'
          · exact h h'
          · exact hx.2 h'
        have hFx := hgx.congr_of_eventuallyEq ((hFoff x h).filter_mono nhdsWithin_le_nhds)
          (by rw [hF, Function.update_of_ne h])
        refine hFx.mono_of_mem_nhdsWithin ?_
        have e : Rectangle z w \ ↑(insert p₀ P') = (Rectangle z w \ ↑P') ∩ {p₀}ᶜ := by
          ext y
          constructor
          · rintro ⟨h1, h2⟩
            refine ⟨⟨h1, fun h3 => h2 ?_⟩, fun h3 => h2 ?_⟩
            · exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp h3))
            · rw [Set.mem_singleton_iff.mp h3]
              exact Finset.mem_coe.mpr (Finset.mem_insert_self _ _)
          · rintro ⟨⟨h1, h2⟩, h3⟩
            refine ⟨h1, fun h4 => ?_⟩
            rcases Finset.mem_insert.mp (Finset.mem_coe.mp h4) with h5 | h5
            · exact h3 (Set.mem_singleton_iff.mpr h5)
            · exact h2 (Finset.mem_coe.mpr h5)
        rw [e]
        exact inter_mem_nhdsWithin _ (isOpen_compl_singleton.mem_nhds h)
    -- local conditions for `F` at the remaining poles
    have hFloc : ∀ p ∈ P', (F - fun s => c p / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
      intro p hp
      have hpne : p ≠ p₀ := fun h => hp₀ (h ▸ hp)
      have h1 := hloc p (Finset.mem_insert_of_mem hp)
      have h2 := (h1.sub (principal_isBigO_one (c := c p₀) hpne))
      refine h2.congr' ?_ (Eventually.of_forall fun _ => rfl)
      filter_upwards [(hFoff p hpne).filter_mono nhdsWithin_le_nhds] with y hy
      simp only [Pi.sub_apply, hy, hg]
      ring
    have hIH := ih F hint' hFh hFloc
    -- reassemble
    have hborder : ∀ x ∈ RectangleBorder z w, x ∉ (↑(insert p₀ P') : Set ℂ) := by
      intro x hx hmem
      have := hint x (by simpa using hmem)
      exact not_mem_rectangleBorder_of_rectangle_mem_nhds this hx
    have hEq : EqOn f (F + fun s => c p₀ / (s - p₀)) (RectangleBorder z w) := by
      intro x hx
      have hxp : x ≠ p₀ := fun h => hborder x hx (by rw [h]; simp)
      simp only [Pi.add_apply, hF, Function.update_of_ne hxp, hg, Pi.sub_apply]
      ring
    have hFB : RectangleBorderIntegrable F z w := by
      refine ContinuousOn.rectangleBorder_integrable (hFh.continuousOn.mono ?_)
      intro x hx
      refine ⟨rectangleBorder_subset_rectangle z w hx, fun hmem => hborder x hx ?_⟩
      exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hmem))
    have t2 : HolomorphicOn (fun s ↦ c p₀ / (s - p₀)) (Rectangle z w \ {p₀}) := by
      intro x hx
      have hne : x - p₀ ≠ 0 := sub_ne_zero.mpr hx.2
      exact (show DifferentiableAt ℂ (fun u : ℂ => c p₀ / (u - p₀)) x by
        fun_prop (disch := exact hne)).differentiableWithinAt
    have hPB : RectangleBorderIntegrable (fun s ↦ c p₀ / (s - p₀)) z w :=
      HolomorphicOn.rectangleBorderIntegrable' t2 hint₀
    rw [RectangleIntegral'_congr hEq, RectangleIntegral', RectangleBorderIntegrable.add hFB hPB,
      smul_add, Finset.sum_insert hp₀]
    have hres := ResidueTheoremInRectangle (c := c p₀) hzw1 hzw2 hint₀
    rw [RectangleIntegral'] at hres hIH
    rw [hres, hIH]
    ring

end Principia.Common.TernaryGoldbach.AG
