/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Spine
import Principia.Erdos1054.Density
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

/-!
# Erdős 1054 (EP1054.tex) — the proof of Theorem 1.2 (`thm:small-values`), lines 1862–1884

Discharges the `Thm12` package of `Principia.Erdos1054.Spine`.

Leaf (from the definitions and Mathlib alone):
* `leaf_Claim_SvCauchySchwarz` (lines 1863–1868) — `#S = ∑_{u ∈ s(S)} R(u)`
  (`Finset.card_eq_sum_card_image`), then Cauchy–Schwarz `(∑ R)^2 ≤ #s(S) · ∑ R^2`
  (`sq_sum_le_card_mul_sum_sq`).

Links (from exactly the dependencies the spine names):
* `link_Claim_SvImageCount` (lines 1870–1876) — the images `s(𝒜_d(X))`, `d ∈ 𝒟_X`, are disjoint
  subsets of `s(𝒜(X))`, so `#s(𝒜(X)) ≥ ∑_d #s(𝒜_d(X)) ≥ c' (X/log Y) ∑_d 1/d ≥ c' c₃ X`.
  The last step divides by `log Y`, so it needs `log Y > 0`: `Y = y(X^{1/120}) > 1` once
  `log log X^{1/120} > 1` (`one_lt_Ycut`, threshold `X ≥ exp(120 e²)`), since `L/log L > 1` for
  `L > 1`.
* `link_Claim_SvWitness` (lines 1877–1882) — `M ∈ 𝒜(X) ⊆ 𝒜₀(X)` gives a tuple with `M = pqrk` and
  `1 ≤ M ≤ X`; `eq:sv-two-sided` at `t = M` gives `1/δ < s(M)/M < C_δ`, hence `M < δ s(M)` and
  `s(M) < C_δ M ≤ C_δ X`; `s(M) > 0` forces `M ≠ 1`, so `M ≥ 2` and `eq:sv-basic` applies.
* `link_SvFamilyTarget` (lines 1217–1222) — `D` from `eq:sv-D`, `𝒜` from `lem:sv-regular`,
  `A = 𝒜(X)`; the two claims give the witness bounds and the image count; `𝒜(X) ⊆ 𝒜₀(X) ⊆ [1, X]`
  from the regular-family hypothesis.
* `link_Thm_SmallValues_lowerDens` (line 79) — `le_lowerDens_of_forall_ge` (`Density.lean`).
* `link_Thm_SmallValues_upperDens` (lines 169–171) — the same, then `lowerDens ≤ upperDens`.

Not in this package but proved here as a helper (so that no name clashes with the owner of that
obligation): `Thm12.thm_SmallValues_of_family : Spine.Link_Thm_SmallValues` — the rescaling
`X ↦ X/C_δ` for `0 < δ ≤ 1`, and `𝓔_1 ⊆ 𝓔_δ` for `δ > 1` (lines 1882–1883). It is also
exported as `link_Thm_SmallValues` (end of file), so that a name-based consumer finds it.
-/

namespace Principia.Erdos1054.Proofs.Thm12

open Principia.Erdos1054 Finset

/-! ## Cauchy–Schwarz for an image -/

/-- Cauchy–Schwarz applied to the fibre decomposition of `S` under `s`:
`(#S)^2 ≤ #s(S) · ∑_{u ∈ s(S)} #{M ∈ S : s(M) = u}^2`. -/
theorem sq_card_le_card_image_mul_sum_sq (S : Finset ℕ) (s : ℕ → ℕ) :
    ((S.card : ℕ) : ℝ) ^ 2 ≤
      ((S.image s).card : ℝ) *
        ∑ u ∈ S.image s, (((S.filter (fun M => s M = u)).card : ℕ) : ℝ) ^ 2 := by
  have hfib : S.card = ∑ u ∈ S.image s, (S.filter (fun M => s M = u)).card :=
    Finset.card_eq_sum_card_image s S
  have hcast : ((S.card : ℕ) : ℝ) =
      ∑ u ∈ S.image s, (((S.filter (fun M => s M = u)).card : ℕ) : ℝ) := by
    rw [hfib, Nat.cast_sum]
  rw [hcast]
  exact sq_sum_le_card_mul_sum_sq

/-! ## Disjoint images -/

/-- Pairwise disjoint images of subsets of `A` have total size at most `#g(A)`. -/
theorem sum_card_image_le_card_image (𝒟 : Finset ℕ) (Ad : ℕ → Finset ℕ) (A : Finset ℕ)
    (g : ℕ → ℕ) (hsub : ∀ d ∈ 𝒟, Ad d ⊆ A)
    (hdisj : ∀ d ∈ 𝒟, ∀ e ∈ 𝒟, d ≠ e → Disjoint ((Ad d).image g) ((Ad e).image g)) :
    ∑ d ∈ 𝒟, ((Ad d).image g).card ≤ (A.image g).card := by
  have hbig : (𝒟.biUnion (fun d => (Ad d).image g)) ⊆ A.image g := by
    intro u hu
    obtain ⟨d, hd, hud⟩ := Finset.mem_biUnion.1 hu
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.1 hud
    exact Finset.mem_image_of_mem g (hsub d hd hM)
  calc ∑ d ∈ 𝒟, ((Ad d).image g).card
      = (𝒟.biUnion (fun d => (Ad d).image g)).card :=
        (Finset.card_biUnion (fun d hd e he hne => hdisj d hd e he hne)).symm
    _ ≤ (A.image g).card := Finset.card_le_card hbig

/-! ## The level `Y = y(X^{1/120})` exceeds `1` for large `X` -/

theorem logIt_two (x : ℝ) : logIt 2 x = Real.log (Real.log x) := rfl

theorem logIt_three (x : ℝ) : logIt 3 x = Real.log (Real.log (Real.log x)) := rfl

/-- `y(u) = L / log L > 1` when `L = log log u > 1` (`log L ≤ L − 1 < L`, `log L > 0`). -/
theorem one_lt_yOf {u : ℝ} (h : 1 < Real.log (Real.log u)) : 1 < SV.yOf u := by
  unfold SV.yOf
  rw [logIt_two, logIt_three]
  have hL : 0 < Real.log (Real.log (Real.log u)) := Real.log_pos h
  rw [one_lt_div hL]
  have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < Real.log (Real.log u))
  linarith

/-- `Y = y(X^{1/120}) > 1` for `X ≥ exp(120 e²)`: then `log X^{1/120} ≥ e²`, so
`log log X^{1/120} ≥ 2`. -/
theorem one_lt_Ycut {X : ℝ} (hX : Real.exp (120 * Real.exp 2) ≤ X) : 1 < SV.Ycut X := by
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hlogX : 120 * Real.exp 2 ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).2 hX
  have hu : Real.log (X ^ ((1 : ℝ) / 120)) = Real.log X / 120 := by
    rw [Real.log_rpow hXpos]
    ring
  have h2 : Real.exp 2 ≤ Real.log (X ^ ((1 : ℝ) / 120)) := by
    rw [hu]
    linarith
  have h3 : 2 ≤ Real.log (Real.log (X ^ ((1 : ℝ) / 120))) :=
    (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 2) h2)).2 h2
  exact one_lt_yOf (by linarith)

/-! ## Membership in `𝒜₀(X)` -/

theorem natCast_le_of_le_floor {M : ℕ} {X : ℝ} (h1 : 1 ≤ M) (h : M ≤ ⌊X⌋₊) : (M : ℝ) ≤ X := by
  have hX : 1 ≤ X := Nat.floor_pos.1 (by omega)
  exact (Nat.cast_le.2 h).trans (Nat.floor_le (by linarith))

open Classical in
theorem mem_A0 {D : ℕ} {X : ℝ} {M : ℕ} (h : M ∈ S4a.A0 D X) :
    1 ≤ M ∧ M ≤ ⌊X⌋₊ ∧ ∃ p q r k : ℕ, S4a.A0Tuple D X p q r k ∧ M = p * q * r * k := by
  obtain ⟨hI, hex⟩ := Finset.mem_filter.1 h
  rw [Finset.mem_Icc] at hI
  exact ⟨hI.1, hI.2, hex⟩

theorem sig_one : sig 1 = 1 := ArithmeticFunction.isMultiplicative_sigma.map_one

theorem aliquot_one : aliquot 1 = 0 := by
  show sig 1 - 1 = 0
  rw [sig_one]

/-- A positive aliquot sum forces `M ≥ 2` (given `M ≥ 1`). -/
theorem two_le_of_aliquot_pos {M : ℕ} (h1 : 1 ≤ M) (h : 0 < aliquot M) : 2 ≤ M := by
  by_contra hlt
  have hM : M = 1 := by omega
  rw [hM, aliquot_one] at h
  exact lt_irrefl 0 h

end Principia.Erdos1054.Proofs.Thm12

namespace Principia.Erdos1054.Proofs

open Principia.Erdos1054 Finset

/-! ## The package obligations -/

/-- **`Claim_SvCauchySchwarz`** (EP1054.tex lines 1863–1868), a leaf. -/
theorem leaf_Claim_SvCauchySchwarz : Principia.Erdos1054.Claim_SvCauchySchwarz := by
  intro S s
  exact Thm12.sq_card_le_card_image_mul_sum_sq S s

/-- **`Claim_SvWitness`** (EP1054.tex lines 1877–1882), from `Eq_SvBasic` and `Eq_SvTwoSided`. -/
theorem link_Claim_SvWitness : Principia.Erdos1054.Spine.Link_Claim_SvWitness := by
  intro hBasic hTwo δ hδ hδ1 D hD 𝒜 h𝒜
  obtain ⟨c, hc, B, hB, X₀, hX₀⟩ := h𝒜
  obtain ⟨Cδ, hCδ, X₁, hX₁⟩ := hTwo δ hδ hδ1 D hD
  refine ⟨Cδ, hCδ, max X₀ X₁, fun X hX M hM => ?_⟩
  have hX0 : X₀ ≤ X := le_of_max_le_left hX
  have hX1 : X₁ ≤ X := le_of_max_le_right hX
  obtain ⟨hM1, hMX, p, q, r, k, htup, hMeq⟩ := Thm12.mem_A0 ((hX₀ X hX0).1 hM)
  obtain ⟨hlo, hhi⟩ := hX₁ X hX1 p q r k htup M (Or.inr (Or.inr (Or.inr hMeq)))
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  have hlo' : 1 / δ * M < (aliquot M : ℝ) := (lt_div_iff₀ hMpos).1 hlo
  have hhi' : (aliquot M : ℝ) < Cδ * M := (div_lt_iff₀ hMpos).1 hhi
  have hMlt : (M : ℝ) < δ * aliquot M :=
    calc (M : ℝ) = δ * (1 / δ * M) := by rw [← mul_assoc, mul_one_div_cancel hδ.ne', one_mul]
      _ < δ * aliquot M := mul_lt_mul_of_pos_left hlo' hδ
  have hspos : (0 : ℝ) < (aliquot M : ℝ) :=
    lt_trans (mul_pos (one_div_pos.2 hδ) hMpos) hlo'
  have hM2 : 2 ≤ M := Thm12.two_le_of_aliquot_pos hM1 (by exact_mod_cast hspos)
  obtain ⟨hR, hf⟩ := hBasic M hM2
  refine ⟨hR, hf, hMlt, ?_⟩
  calc (aliquot M : ℝ) < Cδ * M := hhi'
    _ ≤ Cδ * X := mul_le_mul_of_nonneg_left (Thm12.natCast_le_of_le_floor hM1 hMX) hCδ.le

/-- **`Claim_SvImageCount`** (EP1054.tex lines 1870–1876), from `Lem_SvClasses` and
`Claim_SvClassImage`. -/
theorem link_Claim_SvImageCount : Principia.Erdos1054.Spine.Link_Claim_SvImageCount := by
  intro hClasses hImage δ hδ hδ1 D hD 𝒜 h𝒜
  obtain ⟨c, c₁, c₂, c₃, hc, hc₁, hc₂, hc₃, X₀, hX₀⟩ := hClasses δ hδ hδ1 D hD 𝒜 h𝒜
  obtain ⟨c', hc', X₁, hX₁⟩ := hImage δ hδ hδ1 D hD 𝒜 h𝒜 c c₁ c₂ c₃ hc hc₁ hc₂ hc₃
  refine ⟨c' * c₃, mul_pos hc' hc₃, max X₀ (max X₁ (Real.exp (120 * Real.exp 2))), ?_⟩
  intro X hX
  have hX0 : X₀ ≤ X := le_of_max_le_left hX
  have hX1 : X₁ ≤ X := le_of_max_le_left (le_of_max_le_right hX)
  have hX2 : Real.exp (120 * Real.exp 2) ≤ X := le_of_max_le_right (le_of_max_le_right hX)
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX2
  have hL : 0 < Real.log (SV.Ycut X) := Real.log_pos (Thm12.one_lt_Ycut hX2)
  have hLne : Real.log (SV.Ycut X) ≠ 0 := hL.ne'
  obtain ⟨𝒟, h𝒟⟩ := hX₀ X hX0
  have hper := hX₁ X hX1 𝒟 h𝒟
  obtain ⟨-, ⟨-, hsum⟩, hdisj⟩ := h𝒟
  have hsub : (∑ d ∈ 𝒟, (((SV.classFin (𝒜 X) X d).image aliquot).card : ℝ)) ≤
      (((𝒜 X).image aliquot).card : ℝ) := by
    have := Thm12.sum_card_image_le_card_image 𝒟 (fun d => SV.classFin (𝒜 X) X d) (𝒜 X)
      aliquot (fun d _ => Finset.filter_subset _ _) hdisj
    exact_mod_cast this
  calc c' * c₃ * X
      = c' * c₃ * X * (Real.log (SV.Ycut X) / Real.log (SV.Ycut X)) := by
        rw [div_self hLne, mul_one]
    _ = c' * X / Real.log (SV.Ycut X) * (c₃ * Real.log (SV.Ycut X)) := by ring
    _ ≤ c' * X / Real.log (SV.Ycut X) * ∑ d ∈ 𝒟, (1 : ℝ) / d :=
        mul_le_mul_of_nonneg_left hsum (div_nonneg (mul_nonneg hc'.le hXpos.le) hL.le)
    _ = ∑ d ∈ 𝒟, c' * (X / ((d : ℝ) * Real.log (SV.Ycut X))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        ring
    _ ≤ ∑ d ∈ 𝒟, (((SV.classFin (𝒜 X) X d).image aliquot).card : ℝ) :=
        Finset.sum_le_sum hper
    _ ≤ (((𝒜 X).image aliquot).card : ℝ) := hsub

/-- **`SvFamilyTarget`** (EP1054.tex lines 1217–1222), from `Eq_SvD`, `Lem_SvRegular`,
`Claim_SvImageCount`, `Claim_SvWitness`. -/
theorem link_SvFamilyTarget : Principia.Erdos1054.Spine.Link_SvFamilyTarget := by
  intro hEqD hReg hImg hWit δ hδ hδ1
  obtain ⟨D, hD⟩ := hEqD δ hδ hδ1
  obtain ⟨𝒜, h𝒜⟩ := hReg δ hδ hδ1 D hD
  obtain ⟨c, hc, X₀, hX₀⟩ := hImg δ hδ hδ1 D hD 𝒜 h𝒜
  obtain ⟨C, hC, X₁, hX₁⟩ := hWit δ hδ hδ1 D hD 𝒜 h𝒜
  obtain ⟨c₀, hc₀, B, hB, X₂, hX₂⟩ := h𝒜
  refine ⟨C, hC, c, hc, max X₀ (max X₁ X₂), fun X hX => ⟨𝒜 X, ?_, ?_, ?_⟩⟩
  · intro n hn
    obtain ⟨hn1, hnX, -⟩ :=
      Thm12.mem_A0 ((hX₂ X (le_of_max_le_right (le_of_max_le_right hX))).1 hn)
    exact ⟨hn1, Thm12.natCast_le_of_le_floor hn1 hnX⟩
  · intro n hn
    obtain ⟨-, -, hlt, hsC⟩ := hX₁ X (le_of_max_le_left (le_of_max_le_right hX)) n hn
    exact ⟨(div_lt_iff₀ hδ).2 (lt_of_lt_of_eq hlt (mul_comm _ _)), hsC.le⟩
  · exact hX₀ X (le_of_max_le_left hX)

/-- **`Thm_SmallValues_lowerDens`** (EP1054.tex line 79), from `Thm_SmallValues`. -/
theorem link_Thm_SmallValues_lowerDens :
    Principia.Erdos1054.Spine.Link_Thm_SmallValues_lowerDens := by
  intro h δ hδ
  obtain ⟨c, hc, X₀, hX₀⟩ := h δ hδ
  exact lt_of_lt_of_le hc (le_lowerDens_of_forall_ge hX₀)

/-- **`Thm_SmallValues_upperDens`** (EP1054.tex lines 169–171), from `Thm_SmallValues`. -/
theorem link_Thm_SmallValues_upperDens :
    Principia.Erdos1054.Spine.Link_Thm_SmallValues_upperDens := by
  intro h δ hδ
  obtain ⟨c, hc, X₀, hX₀⟩ := h δ hδ
  exact lt_of_lt_of_le hc ((le_lowerDens_of_forall_ge hX₀).trans (lowerDens_le_upperDens _))

end Principia.Erdos1054.Proofs

namespace Principia.Erdos1054.Proofs.Thm12

open Principia.Erdos1054 Finset

/-! ## The rescaling step (not in this package; a helper, see the module docstring) -/

/-- Theorem 1.2 for `0 < δ ≤ 1` from the construction target: every `s(n)`, `n ∈ A`, lies in
`𝓔_δ ∩ [1, C_δ X]` (`s(n) > n/δ > 0` forces `n ≥ 2`, then `f(s(n)) ≤ n < δ s(n)`), so
`cnt 𝓔_δ (C_δ X) ≥ #s(A) ≥ c X`; put `Y = C_δ X`. -/
theorem card_image_le_cnt (hBasic : Eq_SvBasic) {δ C X Y : ℝ} (hδ : 0 < δ) (hXY : C * X = Y)
    (A : Finset ℕ) (hA1 : ∀ n ∈ A, 1 ≤ n ∧ (n : ℝ) ≤ X)
    (hA2 : ∀ n ∈ A, (n : ℝ) / δ < (aliquot n : ℝ) ∧ (aliquot n : ℝ) ≤ C * X) :
    (A.image aliquot).card ≤ cnt (smallRatioSet δ) Y := by
  classical
  apply Finset.card_le_card
  intro N hN
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hN
  obtain ⟨hn1, -⟩ := hA1 n hn
  obtain ⟨hlt, hle⟩ := hA2 n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hspos : (0 : ℝ) < (aliquot n : ℝ) := lt_of_le_of_lt (div_nonneg hnpos.le hδ.le) hlt
  have hs1 : 0 < aliquot n := by exact_mod_cast hspos
  have hn2 : 2 ≤ n := two_le_of_aliquot_pos hn1 hs1
  obtain ⟨hR, hf⟩ := hBasic n hn2
  have hnlt : (n : ℝ) < δ * aliquot n :=
    lt_of_lt_of_eq ((div_lt_iff₀ hδ).1 hlt) (mul_comm _ _)
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨hs1, Nat.le_floor ?_⟩, hR, ?_⟩
  · rw [← hXY]
    exact hle
  · calc (f (aliquot n) : ℝ) ≤ n := by exact_mod_cast hf
      _ ≤ δ * aliquot n := hnlt.le

/-- Theorem 1.2 for `0 < δ ≤ 1` from the construction target (rescaling `Y = C_δ X`). -/
theorem small_of_family (hFam : SvFamilyTarget) (hBasic : Eq_SvBasic) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → c * X ≤ (cnt (smallRatioSet δ) X : ℝ) := by
  obtain ⟨C, hC, c, hc, X₀, hX₀⟩ := hFam δ hδ hδ1
  have hCne : C ≠ 0 := hC.ne'
  refine ⟨c / C, div_pos hc hC, C * X₀, fun Y hY => ?_⟩
  have hXY : C * (Y / C) = Y := by field_simp
  have hX : X₀ ≤ Y / C := (le_div_iff₀ hC).2 (by linarith [mul_comm X₀ C])
  obtain ⟨A, hA1, hA2, hAc⟩ := hX₀ (Y / C) hX
  have hcard : (A.image aliquot).card ≤ cnt (smallRatioSet δ) Y :=
    card_image_le_cnt hBasic hδ hXY A hA1 hA2
  calc c / C * Y = c * (Y / C) := by ring
    _ ≤ ((A.image aliquot).card : ℝ) := hAc
    _ ≤ (cnt (smallRatioSet δ) Y : ℝ) := by exact_mod_cast hcard

/-- **`Link_Thm_SmallValues`** (EP1054.tex lines 1217–1222, 1882–1883): the range `0 < δ ≤ 1` is
`small_of_family`; for `δ > 1`, `𝓔_1 ⊆ 𝓔_δ`. Declared as a helper, because `Thm_SmallValues`
is not an obligation of this package. -/
theorem thm_SmallValues_of_family : Principia.Erdos1054.Spine.Link_Thm_SmallValues := by
  intro hFam hBasic δ hδ
  by_cases hδ1 : δ ≤ 1
  · exact small_of_family hFam hBasic hδ hδ1
  · replace hδ1 : 1 < δ := not_le.1 hδ1
    obtain ⟨c, hc, X₀, hX₀⟩ := small_of_family hFam hBasic one_pos le_rfl
    have hsub : smallRatioSet 1 ⊆ smallRatioSet δ := fun N hN =>
      ⟨hN.1, hN.2.trans (mul_le_mul_of_nonneg_right hδ1.le (Nat.cast_nonneg N))⟩
    refine ⟨c, hc, X₀, fun X hX => (hX₀ X hX).trans ?_⟩
    exact_mod_cast cnt_mono hsub X

end Principia.Erdos1054.Proofs.Thm12

namespace Principia.Erdos1054.Proofs

/-- **`Link_Thm_SmallValues`** (Theorem 1.2, EP1054.tex lines 1217–1222, 1882–1883), under the
`link_` name that name-based consumers look for (LEAN-PROGRESS F2). The proof is
`Thm12.thm_SmallValues_of_family`. -/
theorem link_Thm_SmallValues : Principia.Erdos1054.Spine.Link_Thm_SmallValues :=
  Thm12.thm_SmallValues_of_family

end Principia.Erdos1054.Proofs
