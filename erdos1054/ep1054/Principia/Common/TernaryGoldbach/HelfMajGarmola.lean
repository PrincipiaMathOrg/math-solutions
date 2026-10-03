/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajSpine

set_option autoImplicit false

/-!
# `lem:garmola` for a decreasing weight, corrected — PROVED from the zero count

`HM.garmolaDecr_holds : HM.GarmolaDecr`. The link `GarmolaDecr` of `HelfMajSpine.lean` is
`ZeroCount → …`, i.e. partial summation over the non-trivial zeros GIVEN the explicit zero count
`eq:melos`; this file proves it, so `ZeroCount` is the only input left behind the zero tails.
`helfMajR_of_links'` is the headline of `HelfMajSpine.lean` with the link discharged: eighteen
named links.

## The statement (majarcs 3306–3380, corrected)

For `y ≥ 1`, `F ≥ 0` measurable and non-increasing on `[y,∞)`, and every primitive `χ` mod `q`:
`∑_{|Im ρ| > y} F(|Im ρ|) ≤ ∫_y^∞ F(t)(max((1/π) log(qt/2π), 0) + 1/(2t)) dt + 2F(y)g(y)`,
`g(T) = 0.5 log qT + 17.7`, zeros counted with multiplicity, two-sided (flag F2), and with BOTH
boundary terms `F(y)g(y)` (flag N1: the printed `f(y)g(y) − ∫f'g` is `2f(y)g(y) + ∫fg'`).

## The proof (layer cake, no summation by parts, no limits)

1. `F(|Im ρ|) = |{s : 0 < s < F(|Im ρ|)}|` (Lebesgue measure), so every FINITE partial sum of the
   zero sum is `∫_s ∑_ρ 1[0 < s < F(|Im ρ|)] ds` (`lintegral_finsetSum`) — the tsum over the
   (uncountable) index `ℂ` is never swapped with the integral; it is a supremum of finite sums.
2. `core_pt`: for fixed `s`, the finitely many zeros with `F(|Im ρ|) > s` all satisfy
   `y < |Im ρ| ≤ t*`, `t*` their largest ordinate, and `F(t*) > s`; so their count is at most
   `N(t*) − N(y) ≤ 2g(y) + ∫_y^{t*} gw` (`count_le`, from `ZeroCount` at `y` and `t*` and the
   fundamental theorem of calculus for `(T/π) log(qT/2πe) + g(T)`, `MZ_ftc`), and
   `(y, t*] ⊆ {u > y : F(u) > s}` because `F` is non-increasing.
3. Integrate over `s ∈ (0, F(y))` and swap (Tonelli): `∫_s ∫_{u > y} 1[s < F(u)] gw(u) =
   ∫_{u > y} F(u) gw(u)`.
-/

namespace Principia.Common.TernaryGoldbach.HM

open MeasureTheory Set
open scoped ENNReal

section Garmola

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- The zero sum as a sum over `ℂ` of an indicator. -/
theorem zsum_eq_tsum (A : Set ℂ) (w : ℂ → ℝ≥0∞) :
    zsum χ A w = ∑' s : ℂ, (zeroSet χ ∩ A).indicator (fun s => zmult χ s * w s) s :=
  tsum_subtype (zeroSet χ ∩ A) (fun s => zmult χ s * w s)

/-- `N(t) = N(y) + #{y < |Im ρ| ≤ t}` for `y ≤ t`. -/
theorem zcount_split {y t : ℝ} (hyt : y ≤ t) :
    zcount χ t = zcount χ y + zsum χ {s | y < |s.im| ∧ |s.im| ≤ t} (fun _ => 1) := by
  unfold zcount
  have hset : zeroSet χ ∩ {s : ℂ | |s.im| ≤ t} = (zeroSet χ ∩ {s : ℂ | |s.im| ≤ y}) ∪
      (zeroSet χ ∩ {s : ℂ | y < |s.im| ∧ |s.im| ≤ t}) := by
    ext s
    simp only [mem_inter_iff, mem_setOf_eq, mem_union]
    constructor
    · rintro ⟨hz, h⟩
      by_cases h' : |s.im| ≤ y
      · exact Or.inl ⟨hz, h'⟩
      · exact Or.inr ⟨hz, lt_of_not_ge h', h⟩
    · rintro (⟨hz, h⟩ | ⟨hz, _, h2⟩)
      · exact ⟨hz, h.trans hyt⟩
      · exact ⟨hz, h2⟩
  have hd : Disjoint (zeroSet χ ∩ {s : ℂ | |s.im| ≤ y})
      (zeroSet χ ∩ {s : ℂ | y < |s.im| ∧ |s.im| ≤ t}) :=
    Set.disjoint_left.mpr fun s h1 h2 => absurd h1.2 (not_le.mpr h2.2.1)
  rw [zsum_eq_tsum, zsum_eq_tsum, zsum_eq_tsum, hset, indicator_union_of_disjoint hd,
    ENNReal.tsum_add]

end Garmola

/-- `M(T) = (T/π) log(qT/2πe)` is `(T/π)(log(qT/2π) − 1)`. -/
theorem MZ_eq (Q T : ℝ) (hQT : Q * T ≠ 0) :
    T / Real.pi * Real.log (Q * T / (2 * Real.pi * Real.exp 1)) =
      T / Real.pi * (Real.log (Q * T / (2 * Real.pi)) - 1) := by
  rw [← div_div, Real.log_div (div_ne_zero hQT (by positivity)) (Real.exp_pos 1).ne',
    Real.log_exp]

/-- **The main term of the zero count, by the fundamental theorem of calculus**:
`[M(t) + g(t)] − [M(y) + g(y)] = ∫_y^t ((1/π) log(qu/2π) + 1/(2u)) du ≤ ∫_y^t gw`. -/
theorem MZ_ftc {Q y t : ℝ} (hQ : 0 < Q) (hy : 0 < y) (hyt : y ≤ t) :
    (t / Real.pi * (Real.log (Q * t / (2 * Real.pi)) - 1) + gZ Q t) -
        (y / Real.pi * (Real.log (Q * y / (2 * Real.pi)) - 1) + gZ Q y) ≤
      ∫ u in y..t, gw Q u := by
  have hpos : ∀ u ∈ uIcc y t, 0 < u := fun u hu => by
    rw [uIcc_of_le hyt] at hu
    linarith [hu.1]
  have hd : ∀ u ∈ uIcc y t, HasDerivAt
      (fun u => u / Real.pi * (Real.log (Q * u / (2 * Real.pi)) - 1) + gZ Q u)
      (Real.log (Q * u / (2 * Real.pi)) / Real.pi + 1 / (2 * u)) u := by
    intro u hu
    have hu0 := hpos u hu
    have h1 : HasDerivAt (fun u => Q * u / (2 * Real.pi)) (Q * 1 / (2 * Real.pi)) u :=
      ((hasDerivAt_id u).const_mul Q).div_const (2 * Real.pi)
    have h2 := (h1.log (by positivity)).sub_const 1
    have h3 := ((hasDerivAt_id u).div_const Real.pi).mul h2
    have h4 : HasDerivAt (fun u => Q * u) (Q * 1) u := (hasDerivAt_id u).const_mul Q
    have h5 := ((h4.log (by positivity)).const_mul 0.5).add_const 17.7
    have h6 := h3.add h5
    unfold gZ
    refine h6.congr_deriv ?_
    have hQu : Q * u ≠ 0 := by positivity
    simp only [id]
    field_simp
    ring
  have hc : ContinuousOn (fun u => Real.log (Q * u / (2 * Real.pi)) / Real.pi + 1 / (2 * u))
      (uIcc y t) := by
    refine ContinuousOn.add ?_ ?_
    · refine ContinuousOn.div_const (ContinuousOn.log ?_ fun u hu => ?_) _
      · fun_prop
      · have := hpos u hu
        positivity
    · refine ContinuousOn.div continuousOn_const (by fun_prop) fun u hu => ?_
      have := hpos u hu
      positivity
  have hg : ContinuousOn (gw Q) (uIcc y t) := by
    unfold gw
    refine ContinuousOn.add ?_ ?_
    · refine ContinuousOn.sup (ContinuousOn.div_const (ContinuousOn.log ?_ fun u hu => ?_) _)
        continuousOn_const
      · fun_prop
      · have := hpos u hu
        positivity
    · refine ContinuousOn.div continuousOn_const (by fun_prop) fun u hu => ?_
      have := hpos u hu
      positivity
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  refine intervalIntegral.integral_mono_on hyt hc.intervalIntegrable hg.intervalIntegrable
    fun u _ => ?_
  unfold gw
  linarith [le_max_left (Real.log (Q * u / (2 * Real.pi)) / Real.pi) 0]

section Garmola2

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- **The count between two heights**: `#{y < |Im ρ| ≤ t} ≤ 2g(y) + ∫_y^t gw` from `ZeroCount`
at `y` and `t` (`|N(T) − M(T)| ≤ g(T)`) and `MZ_ftc`. -/
theorem count_le (hZC : ZeroCount) (hχ : χ.IsPrimitive) {y t : ℝ} (hy : 1 ≤ y) (hyt : y ≤ t) :
    zsum χ {s | y < |s.im| ∧ |s.im| ≤ t} (fun _ => 1) ≤
      ENNReal.ofReal (2 * gZ q y) + ∫⁻ u in Ioc y t, ENNReal.ofReal (gw q u) := by
  obtain ⟨hNt, hNt'⟩ := hZC q χ hχ t (by linarith)
  obtain ⟨hNy, hNy'⟩ := hZC q χ hχ y hy
  have hsplit := zcount_split χ hyt
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hQ0 : (0 : ℝ) < q := by linarith
  have hB : zsum χ {s | y < |s.im| ∧ |s.im| ≤ t} (fun _ => 1) ≠ ⊤ := by
    intro h
    rw [h, add_top] at hsplit
    exact hNt hsplit
  have hreal : (zsum χ {s | y < |s.im| ∧ |s.im| ≤ t} (fun _ => 1)).toReal =
      (zcount χ t).toReal - (zcount χ y).toReal := by
    rw [hsplit, ENNReal.toReal_add hNy hB]
    ring
  rw [MZ_eq (q : ℝ) t (mul_pos hQ0 (by linarith)).ne'] at hNt'
  rw [MZ_eq (q : ℝ) y (mul_pos hQ0 (by linarith)).ne'] at hNy'
  have hftc := MZ_ftc (Q := (q : ℝ)) hQ0 (by linarith) hyt
  have hb1 := (abs_le.mp hNt').2
  have hb2 := (abs_le.mp hNy').1
  have hle : (zsum χ {s | y < |s.im| ∧ |s.im| ≤ t} (fun _ => 1)).toReal ≤
      2 * gZ q y + ∫ u in y..t, gw q u := by
    rw [hreal]
    linarith
  have hgw : ∀ u ∈ Ioc y t, 0 ≤ gw q u := fun u hu => by
    have hu0 : 0 < u := by linarith [hu.1]
    unfold gw
    have := le_max_right (Real.log (q * u / (2 * Real.pi)) / Real.pi) 0
    have : 0 ≤ 1 / (2 * u) := by positivity
    linarith
  have hgwc : ContinuousOn (gw q) (Icc y t) := by
    unfold gw
    refine ContinuousOn.add ?_ ?_
    · refine ContinuousOn.sup (ContinuousOn.div_const (ContinuousOn.log ?_ fun u hu => ?_) _)
        continuousOn_const
      · fun_prop
      · have : 0 < u := by linarith [hu.1]
        positivity
    · refine ContinuousOn.div continuousOn_const (by fun_prop) fun u hu => ?_
      have : 0 < u := by linarith [hu.1]
      positivity
  have hint : IntegrableOn (gw q) (Ioc y t) :=
    (hgwc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hlint : ENNReal.ofReal (∫ u in y..t, gw q u) = ∫⁻ u in Ioc y t, ENNReal.ofReal (gw q u) := by
    rw [intervalIntegral.integral_of_le hyt]
    exact ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hgw))
  have hgy : 0 ≤ 2 * gZ q y := by
    have := gZ_nonneg (q := (q : ℝ)) (T := y) (by nlinarith)
    linarith
  calc zsum χ {s | y < |s.im| ∧ |s.im| ≤ t} (fun _ => 1)
      = ENNReal.ofReal (zsum χ {s | y < |s.im| ∧ |s.im| ≤ t} (fun _ => 1)).toReal :=
        (ENNReal.ofReal_toReal hB).symm
    _ ≤ ENNReal.ofReal (2 * gZ q y + ∫ u in y..t, gw q u) := ENNReal.ofReal_le_ofReal hle
    _ ≤ ENNReal.ofReal (2 * gZ q y) + ENNReal.ofReal (∫ u in y..t, gw q u) :=
        ENNReal.ofReal_add_le
    _ = ENNReal.ofReal (2 * gZ q y) + ∫⁻ u in Ioc y t, ENNReal.ofReal (gw q u) := by rw [hlint]

/-- **The layer at height `s`**: the finitely many zeros of a finite set `S` whose weight exceeds
`s` number at most `2g(y) + ∫_{u > y, F(u) > s} gw`, and there are none unless `s < F(y)`. -/
theorem core_pt (hZC : ZeroCount) (hχ : χ.IsPrimitive) {F : ℝ → ℝ} {y : ℝ} (hy : 1 ≤ y)
    (hF : AntitoneOn F (Ici y)) (S : Finset ℂ) (s : ℝ) :
    ∑ ρ ∈ S, (zeroSet χ ∩ {z | y < |z.im|}).indicator
        (fun z => zmult χ z * (Ioo 0 (F |z.im|)).indicator 1 s) ρ ≤
      (Ioo 0 (F y)).indicator (fun s => ENNReal.ofReal (2 * gZ q y) +
        ∫⁻ u in Ioi y ∩ {u | s < F u}, ENNReal.ofReal (gw q u)) s := by
  classical
  set S' := S.filter (fun ρ => ρ ∈ zeroSet χ ∩ {z | y < |z.im|} ∧ s ∈ Ioo 0 (F |ρ.im|)) with hS'
  by_cases hne : S'.Nonempty
  · obtain ⟨ρ₀, hρ₀, heq⟩ := Finset.exists_mem_eq_sup' hne (fun ρ => |ρ.im|)
    have hρ₀' := (Finset.mem_filter.mp hρ₀).2
    have hyt : y < |ρ₀.im| := hρ₀'.1.2
    have hs0 : 0 < s := hρ₀'.2.1
    have hst : s < F |ρ₀.im| := hρ₀'.2.2
    have hFy : F |ρ₀.im| ≤ F y := hF (mem_Ici.mpr le_rfl) (mem_Ici.mpr hyt.le) hyt.le
    have hmem : s ∈ Ioo 0 (F y) := ⟨hs0, lt_of_lt_of_le hst hFy⟩
    rw [indicator_of_mem hmem]
    have hsub : Ioc y |ρ₀.im| ⊆ Ioi y ∩ {u | s < F u} := fun u hu => by
      refine ⟨hu.1, ?_⟩
      have : F |ρ₀.im| ≤ F u := hF (mem_Ici.mpr hu.1.le) (mem_Ici.mpr hyt.le) hu.2
      change s < F u
      linarith
    calc ∑ ρ ∈ S, (zeroSet χ ∩ {z | y < |z.im|}).indicator
          (fun z => zmult χ z * (Ioo 0 (F |z.im|)).indicator 1 s) ρ
        ≤ ∑ ρ ∈ S, (zeroSet χ ∩ {z | y < |z.im| ∧ |z.im| ≤ |ρ₀.im|}).indicator
            (fun z => zmult χ z * (fun _ => (1 : ℝ≥0∞)) z) ρ := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          by_cases h : ρ ∈ S'
          · have h' := (Finset.mem_filter.mp h).2
            have hle : |ρ.im| ≤ |ρ₀.im| := by
              rw [← heq]
              exact Finset.le_sup' (fun ρ => |ρ.im|) h
            have hm2 : ρ ∈ zeroSet χ ∩ {z | y < |z.im| ∧ |z.im| ≤ |ρ₀.im|} :=
              ⟨h'.1.1, h'.1.2, hle⟩
            rw [indicator_of_mem h'.1, indicator_of_mem hm2, indicator_of_mem h'.2]
            simp
          · have h0 : (zeroSet χ ∩ {z | y < |z.im|}).indicator
                (fun z => zmult χ z * (Ioo 0 (F |z.im|)).indicator 1 s) ρ = 0 := by
              by_cases hz : ρ ∈ zeroSet χ ∩ {z | y < |z.im|}
              · rw [indicator_of_mem hz]
                have hs : s ∉ Ioo 0 (F |ρ.im|) := fun hs =>
                  h (Finset.mem_filter.mpr ⟨hρ, hz, hs⟩)
                rw [indicator_of_notMem hs, mul_zero]
              · exact indicator_of_notMem hz _
            rw [h0]
            exact zero_le
      _ ≤ ∑' ρ, (zeroSet χ ∩ {z | y < |z.im| ∧ |z.im| ≤ |ρ₀.im|}).indicator
            (fun z => zmult χ z * (fun _ => (1 : ℝ≥0∞)) z) ρ := ENNReal.sum_le_tsum S
      _ = zsum χ {z | y < |z.im| ∧ |z.im| ≤ |ρ₀.im|} (fun _ => 1) := (zsum_eq_tsum χ _ _).symm
      _ ≤ ENNReal.ofReal (2 * gZ q y) + ∫⁻ u in Ioc y |ρ₀.im|, ENNReal.ofReal (gw q u) :=
          count_le χ hZC hχ hy hyt.le
      _ ≤ ENNReal.ofReal (2 * gZ q y) +
            ∫⁻ u in Ioi y ∩ {u | s < F u}, ENNReal.ofReal (gw q u) :=
          add_le_add le_rfl (lintegral_mono_set hsub)
  · have h0 : ∀ ρ ∈ S, (zeroSet χ ∩ {z | y < |z.im|}).indicator
        (fun z => zmult χ z * (Ioo 0 (F |z.im|)).indicator 1 s) ρ = 0 := by
      intro ρ hρ
      by_cases hz : ρ ∈ zeroSet χ ∩ {z | y < |z.im|}
      · rw [indicator_of_mem hz]
        have hs : s ∉ Ioo 0 (F |ρ.im|) := fun hs =>
          hne ⟨ρ, Finset.mem_filter.mpr ⟨hρ, hz, hs⟩⟩
        rw [indicator_of_notMem hs, mul_zero]
      · exact indicator_of_notMem hz _
    rw [Finset.sum_eq_zero h0]
    exact zero_le

end Garmola2

/-- `gw Q` is measurable. -/
theorem measurable_gw (Q : ℝ) : Measurable (gw Q) := by
  unfold gw
  fun_prop

/-- **Tonelli for the layers**: `∫_{s > 0} ∫_{u > y, F(u) > s} gw = ∫_{u > y} F(u) gw(u)`. -/
theorem layer_swap {F : ℝ → ℝ} {y Q : ℝ} (hFm : Measurable F) (hF0 : ∀ t, y ≤ t → 0 ≤ F t) :
    ∫⁻ s in Ioi 0, ∫⁻ u in Ioi y ∩ {u | s < F u}, ENNReal.ofReal (gw Q u) =
      ∫⁻ u in Ioi y, ENNReal.ofReal (F u * gw Q u) := by
  have hms : ∀ s : ℝ, MeasurableSet {u | s < F u} := fun s => measurableSet_lt measurable_const hFm
  have e1 : ∀ s : ℝ, ∫⁻ u in Ioi y ∩ {u | s < F u}, ENNReal.ofReal (gw Q u) =
      ∫⁻ u in Ioi y, {u | s < F u}.indicator (fun u => ENNReal.ofReal (gw Q u)) u := by
    intro s
    rw [lintegral_indicator (hms s), Measure.restrict_restrict (hms s), inter_comm]
  simp_rw [e1]
  have huc : Function.uncurry (fun (s u : ℝ) => {u | s < F u}.indicator
      (fun u => ENNReal.ofReal (gw Q u)) u) =
      {p : ℝ × ℝ | p.1 < F p.2}.indicator (fun p => ENNReal.ofReal (gw Q p.2)) := by
    funext p
    simp only [Function.uncurry, indicator_apply, mem_setOf_eq]
  have hm : Measurable (Function.uncurry (fun (s u : ℝ) => {u | s < F u}.indicator
      (fun u => ENNReal.ofReal (gw Q u)) u)) := by
    rw [huc]
    exact ((measurable_gw Q).ennreal_ofReal.comp measurable_snd).indicator
      (measurableSet_lt measurable_fst (hFm.comp measurable_snd))
  rw [lintegral_lintegral_swap hm.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hFu : 0 ≤ F u := hF0 u (le_of_lt hu)
  have e2 : (fun s : ℝ => {u | s < F u}.indicator (fun u => ENNReal.ofReal (gw Q u)) u) =
      (Iio (F u)).indicator (fun _ => ENNReal.ofReal (gw Q u)) := by
    funext s
    simp only [indicator_apply, mem_setOf_eq, mem_Iio]
  rw [e2, lintegral_indicator_const measurableSet_Iio, Measure.restrict_apply measurableSet_Iio,
    Iio_inter_Ioi, Real.volume_Ioo, sub_zero, ENNReal.ofReal_mul hFu, mul_comm]

section Garmola3

/-- `zmult` is finite. -/
theorem zmult_ne_top {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : zmult χ s ≠ ⊤ := by
  unfold zmult
  exact ENNReal.natCast_ne_top _

/-- **`lem:garmola` for a decreasing weight, corrected — PROVED from the zero count.** -/
theorem garmolaDecr_holds : GarmolaDecr := by
  intro hZC q _ χ hχ F y hy hFm hF hF0
  classical
  have hlayer : ∀ ρ : ℂ, (zeroSet χ ∩ {z : ℂ | y < |z.im|}).indicator
      (fun z => zmult χ z * ENNReal.ofReal (F |z.im|)) ρ =
      ∫⁻ s, (zeroSet χ ∩ {z : ℂ | y < |z.im|}).indicator
        (fun z => zmult χ z * (Ioo 0 (F |z.im|)).indicator 1 s) ρ := by
    intro ρ
    by_cases hρ : ρ ∈ zeroSet χ ∩ {z : ℂ | y < |z.im|}
    · simp only [indicator_of_mem hρ]
      rw [lintegral_const_mul' _ _ (zmult_ne_top χ ρ), lintegral_indicator_one measurableSet_Ioo,
        Real.volume_Ioo, sub_zero]
    · simp only [indicator_of_notMem hρ, lintegral_zero]
  have hmeas : ∀ ρ : ℂ, Measurable (fun s => (zeroSet χ ∩ {z : ℂ | y < |z.im|}).indicator
      (fun z => zmult χ z * (Ioo 0 (F |z.im|)).indicator 1 s) ρ) := by
    intro ρ
    by_cases hρ : ρ ∈ zeroSet χ ∩ {z : ℂ | y < |z.im|}
    · simp only [indicator_of_mem hρ]
      exact measurable_const.mul (measurable_one.indicator measurableSet_Ioo)
    · simp only [indicator_of_notMem hρ]
      exact measurable_const
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hg0 : 0 ≤ 2 * gZ q y := by
    have := gZ_nonneg (q := (q : ℝ)) (T := y) (by nlinarith)
    linarith
  have hFy := hF0 y le_rfl
  rw [zsum_eq_tsum, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun S => ?_
  calc ∑ ρ ∈ S, (zeroSet χ ∩ {z : ℂ | y < |z.im|}).indicator
        (fun z => zmult χ z * ENNReal.ofReal (F |z.im|)) ρ
      = ∑ ρ ∈ S, ∫⁻ s, (zeroSet χ ∩ {z : ℂ | y < |z.im|}).indicator
          (fun z => zmult χ z * (Ioo 0 (F |z.im|)).indicator 1 s) ρ :=
        Finset.sum_congr rfl fun ρ _ => hlayer ρ
    _ = ∫⁻ s, ∑ ρ ∈ S, (zeroSet χ ∩ {z : ℂ | y < |z.im|}).indicator
          (fun z => zmult χ z * (Ioo 0 (F |z.im|)).indicator 1 s) ρ :=
        (lintegral_finsetSum S fun ρ _ => hmeas ρ).symm
    _ ≤ ∫⁻ s, (Ioo 0 (F y)).indicator (fun s => ENNReal.ofReal (2 * gZ q y) +
          ∫⁻ u in Ioi y ∩ {u | s < F u}, ENNReal.ofReal (gw q u)) s :=
        lintegral_mono fun s => core_pt χ hZC hχ hy hF S s
    _ = ∫⁻ s in Ioo 0 (F y), (ENNReal.ofReal (2 * gZ q y) +
          ∫⁻ u in Ioi y ∩ {u | s < F u}, ENNReal.ofReal (gw q u)) :=
        lintegral_indicator measurableSet_Ioo _
    _ = ENNReal.ofReal (2 * gZ q y) * volume (Ioo 0 (F y)) +
          ∫⁻ s in Ioo 0 (F y), ∫⁻ u in Ioi y ∩ {u | s < F u}, ENNReal.ofReal (gw q u) := by
        rw [lintegral_add_left measurable_const, setLIntegral_const]
    _ ≤ ENNReal.ofReal (2 * gZ q y) * volume (Ioo 0 (F y)) +
          ∫⁻ s in Ioi 0, ∫⁻ u in Ioi y ∩ {u | s < F u}, ENNReal.ofReal (gw q u) :=
        add_le_add le_rfl (lintegral_mono_set Ioo_subset_Ioi_self)
    _ = ENNReal.ofReal (2 * gZ q y) * volume (Ioo 0 (F y)) +
          ∫⁻ u in Ioi y, ENNReal.ofReal (F u * gw q u) := by
        rw [layer_swap hFm hF0]
    _ = (∫⁻ u in Ioi y, ENNReal.ofReal (F u * gw q u)) +
          ENNReal.ofReal (2 * F y * gZ q y) := by
        rw [Real.volume_Ioo, sub_zero, ← ENNReal.ofReal_mul hg0, add_comm,
          show 2 * gZ q y * F y = 2 * F y * gZ q y by ring]

end Garmola3

/-- **THE HEADLINE WITH `GarmolaDecr` DISCHARGED**: `MR.HelfMajR η₊ (η₂ ∗_M φ)` from eighteen named
links (`HelfMajSpine.helfMajR_of_links` applied to `garmolaDecr_holds`). -/
theorem helfMajR_of_links' (hEF : ExplicitFormula) (hZC : ZeroCount) (hHs : Hausierer)
    (pr : PlusReg) (pn : PlusNorms) (pd : PlusDecay) (pt : PlusTailInt)
    (fr : PhiReg) (fn : PhiNorms) (fd : PhiDecay) (ft : PhiTailInt) (ko : Kolona)
    (mo : Eta2Moments) (mr : MalReg) (mn : MalNorms) (md : MalDecay) (mt : MalTailInt)
    (mm : MalMain) : MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi) :=
  helfMajR_of_links hEF hZC hHs garmolaDecr_holds pr pn pd pt fr fn fd ft ko mo mr mn md mt mm

end Principia.Common.TernaryGoldbach.HM
