/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.PSieveBasic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

set_option autoImplicit false

/-!
# The arc integral of a periodic function over `oeArcs h L`, as a sum over the moduli

`∫_{(0,1] ∩ oeArcs h L} F = ∑_{q} ∫_{−h/ρ(q)}^{h/ρ(q)} ∑_{0 ≤ a < q, (a,q)=1} F(a/q + β) dβ`
(`arc_reduce`) for `F` continuous and `1`-periodic, `h > 0`, `L ≥ 1`, `hL ≤ 1/2`. Here
`ρ(q) = 2q` for odd `q` and `ρ(q) = q` for even `q`, so the arc about `a/q` has half-width
`h/ρ(q)` and the moduli are exactly the `q ≥ 1` with `ρ(q) ≤ 2L` (`oeArcs_eq`).

This is the first and last step of `prop:bellen` (`ternvin.tex` 2508-2519 and 2588-2602): the
decomposition of `∫_𝔐` into arcs (which the source writes as `eq:malkr`, "=" — it IS an equality
here, `arcs_disjoint` proving the arcs disjoint under `hL ≤ 1/2`, which the source's
`δ₀Q₀² ≤ x/2` gives) and, at `h = 1/2Q`, `L = Q`, the source's closing disjointness check
(2588-2600). Three silent facts are proved, as in `TernaryGoldbach.ArcIntSpine`: disjointness,
the window `(−h/2, 1−h/2]` containing every arc whole, and the `1`-periodicity that moves
`(0,1]` onto that window.
-/

namespace Principia.Common.PSieve

open MeasureTheory

/-- **`ρ(q) = 2q` for odd `q`, `q` for even `q`**: the arc about `a/q` has half-width `h/ρ(q)`. -/
noncomputable def rho (q : ℕ) : ℝ := if Odd q then 2 * q else q

/-- The residues `0 ≤ a < q` coprime to `q`. -/
def cop (q : ℕ) : Finset ℕ := (Finset.range q).filter (fun a => Nat.Coprime a q)

/-- **The moduli of `oeArcs h L`** below `N`: `1 ≤ q ≤ N`, `ρ(q) ≤ 2L`. -/
noncomputable def fam (N : ℕ) (L : ℝ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun q => rho q ≤ 2 * L)

/-- **`T_q(β) = ∑_{0 ≤ a < q, (a,q)=1} F(a/q + β)`**. -/
noncomputable def tS (F : ℝ → ℝ) (q : ℕ) (β : ℝ) : ℝ := ∑ a ∈ cop q, F ((a : ℝ) / q + β)

/-- The arcs, indexed by `(q, a)`. -/
noncomputable def idx (N : ℕ) (L : ℝ) : Finset (Σ _ : ℕ, ℕ) := (fam N L).sigma cop

/-- **The arc about `a/q`**: `(a/q − h/ρ(q), a/q + h/ρ(q))`. -/
noncomputable def arc (h : ℝ) (i : Σ _ : ℕ, ℕ) : Set ℝ :=
  Set.Ioo (((i.2 : ℕ) : ℝ) / i.1 - h / rho i.1) (((i.2 : ℕ) : ℝ) / i.1 + h / rho i.1)

/-- **The window** `(−h/2, 1 − h/2]`. -/
def win (h : ℝ) : Set ℝ := Set.Ioc (-(h / 2)) (-(h / 2) + 1)

/-! ## `ρ` -/

/-- `ρ(q) = 2q` for odd `q`. -/
theorem rho_odd {q : ℕ} (hq : Odd q) : rho q = 2 * q := by
  unfold rho
  rw [if_pos hq]

/-- `ρ(q) = q` for even `q`. -/
theorem rho_even {q : ℕ} (hq : Even q) : rho q = q := by
  unfold rho
  rw [if_neg (Nat.not_odd_iff_even.mpr hq)]

/-- `q ≤ ρ(q) ≤ 2q`. -/
theorem rho_bounds (q : ℕ) : (q : ℝ) ≤ rho q ∧ rho q ≤ 2 * q := by
  rcases Nat.even_or_odd q with h | h
  · rw [rho_even h]
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    constructor <;> linarith
  · rw [rho_odd h]
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    constructor <;> linarith

/-- `ρ(q) ≥ 2` for `q ≥ 1` (odd: `2q ≥ 2`; even: `q ≥ 2`). -/
theorem two_le_rho {q : ℕ} (hq : 1 ≤ q) : 2 ≤ rho q := by
  rcases Nat.even_or_odd q with h | h
  · rw [rho_even h]
    obtain ⟨k, hk⟩ := h
    have : 2 ≤ q := by omega
    exact_mod_cast this
  · rw [rho_odd h]
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith

/-- `ρ(q) > 0` for `q ≥ 1`. -/
theorem rho_pos {q : ℕ} (hq : 1 ≤ q) : 0 < rho q := lt_of_lt_of_le two_pos (two_le_rho hq)

/-- `oeArcs` in terms of `ρ`: the moduli `q ≥ 1` with `ρ(q) ≤ 2L`, half-widths `h/ρ(q)`. -/
theorem oeArcs_eq (h L : ℝ) :
    oeArcs h L = ⋃ q : ℕ, ⋃ (_ : 1 ≤ q ∧ rho q ≤ 2 * L), ⋃ a : ℤ, ⋃ (_ : Int.gcd a q = 1),
      Set.Ioo ((a : ℝ) / q - h / rho q) ((a : ℝ) / q + h / rho q) := by
  ext α
  simp only [oeArcs, Set.mem_union, Set.mem_iUnion, Set.mem_Ioo, exists_prop]
  constructor
  · rintro (⟨q, ⟨h1, h2, ho⟩, a, ha, hw⟩ | ⟨q, ⟨h1, h2, he⟩, a, ha, hw⟩)
    · refine ⟨q, ⟨h1, by rw [rho_odd ho]; linarith⟩, a, ha, ?_⟩
      rw [rho_odd ho]
      exact hw
    · refine ⟨q, ⟨h1, by rw [rho_even he]; exact h2⟩, a, ha, ?_⟩
      rw [rho_even he]
      exact hw
  · rintro ⟨q, ⟨h1, h2⟩, a, ha, hw⟩
    rcases Nat.even_or_odd q with he | ho
    · rw [rho_even he] at h2 hw
      exact Or.inr ⟨q, ⟨h1, h2, he⟩, a, ha, hw⟩
    · rw [rho_odd ho] at h2 hw
      exact Or.inl ⟨q, ⟨h1, by linarith, ho⟩, a, ha, hw⟩

/-! ## [Disjoint] -/

/-- **Reduced fractions are determined by their value.** -/
theorem eq_of_cross {q q' a a' : ℕ} (ha : Nat.Coprime a q) (ha' : Nat.Coprime a' q')
    (hq : 0 < q) (h : a * q' = a' * q) : q = q' ∧ a = a' := by
  have h1 : q ∣ q' := by
    have h3 : q ∣ q' * a := by
      rw [mul_comm, h]
      exact dvd_mul_left q a'
    exact ha.symm.dvd_of_dvd_mul_right h3
  have h2 : q' ∣ q := by
    have h3 : q' ∣ q * a' := by
      rw [mul_comm, ← h]
      exact dvd_mul_left q' a
    exact ha'.symm.dvd_of_dvd_mul_right h3
  have hqq : q = q' := Nat.dvd_antisymm h1 h2
  subst hqq
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right hq h⟩

/-- A residue coprime to an even modulus is odd. -/
theorem odd_of_cop_even {a q : ℕ} (ha : Nat.Coprime a q) (hq : Even q) : Odd a := by
  rcases Nat.even_or_odd a with he | ho
  · exfalso
    have h2 : 2 ∣ Nat.gcd a q := Nat.dvd_gcd (even_iff_two_dvd.mp he) (even_iff_two_dvd.mp hq)
    rw [ha] at h2
    omega
  · exact ho

/-- **The arc-width budget**: for `q, q'` moduli of `oeArcs h L` (`hL ≤ 1/2`) and distinct reduced
`a/q ≠ a'/q'`, `(h/ρ(q) + h/ρ(q'))·qq' ≤ |aq' − a'q|`: odd–odd `≤ hL`, odd–even `≤ 2hL`, and
even–even `≤ 4hL ≤ 2 ≤ |aq' − a'q|` (both numerators odd, so the cross difference is even). -/
theorem width_budget (h L : ℝ) (hh : 0 < h) (hhL : h * L ≤ 1 / 2) {q q' a a' : ℕ}
    (hq : 1 ≤ q) (hq' : 1 ≤ q') (hr : rho q ≤ 2 * L) (hr' : rho q' ≤ 2 * L)
    (ha : Nat.Coprime a q) (ha' : Nat.Coprime a' q') (hne : a * q' ≠ a' * q) :
    (h / rho q + h / rho q') * (q * q') ≤ |(a : ℝ) * q' - a' * q| := by
  have hn : (a : ℤ) * q' - a' * q ≠ 0 := by
    intro h0
    apply hne
    have h3 : (a : ℤ) * q' = a' * q := by linarith
    exact_mod_cast h3
  have h1 : (1 : ℝ) ≤ |(a : ℝ) * q' - a' * q| := by
    have h5 : (1 : ℝ) ≤ |(((a : ℤ) * q' - a' * q : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    push_cast at h5
    exact h5
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq0' : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hL0 : 0 < L := by
    have := two_le_rho hq
    linarith
  rcases Nat.even_or_odd q with he | ho <;> rcases Nat.even_or_odd q' with he' | ho'
  · -- even–even: the cross difference is even
    rw [rho_even he] at hr ⊢
    rw [rho_even he'] at hr' ⊢
    have hao := odd_of_cop_even ha he
    have hao' := odd_of_cop_even ha' he'
    obtain ⟨k, hk⟩ := he
    obtain ⟨k', hk'⟩ := he'
    have h2 : (2 : ℝ) ≤ |(a : ℝ) * q' - a' * q| := by
      have hd : (a : ℤ) * q' - a' * q = 2 * ((a : ℤ) * k' - a' * k) := by
        rw [hk, hk']
        push_cast
        ring
      have hn2 : (a : ℤ) * k' - a' * k ≠ 0 := by
        intro h0
        apply hn
        rw [hd, h0, mul_zero]
      have h6 : (1 : ℝ) ≤ |(((a : ℤ) * k' - a' * k : ℤ) : ℝ)| := by
        exact_mod_cast Int.one_le_abs hn2
      have h7 : |(a : ℝ) * q' - a' * q| = 2 * |(((a : ℤ) * k' - a' * k : ℤ) : ℝ)| := by
        have h8 : (a : ℝ) * q' - a' * q = 2 * (((a : ℤ) * k' - a' * k : ℤ) : ℝ) := by
          have := congrArg (fun z : ℤ => (z : ℝ)) hd
          push_cast at this ⊢
          linarith
        rw [h8, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    have e : (h / q + h / q') * (q * q') = h * (q' + q) := by
      field_simp
    rw [e]
    nlinarith
  · -- even q, odd q'
    rw [rho_even he] at hr ⊢
    rw [rho_odd ho'] at hr' ⊢
    have e : (h / q + h / (2 * q')) * (q * q') = h * (q' + q / 2) := by
      field_simp
    rw [e]
    nlinarith
  · -- odd q, even q'
    rw [rho_odd ho] at hr ⊢
    rw [rho_even he'] at hr' ⊢
    have e : (h / (2 * q) + h / q') * (q * q') = h * (q' / 2 + q) := by
      field_simp
    rw [e]
    nlinarith
  · -- odd–odd
    rw [rho_odd ho] at hr ⊢
    rw [rho_odd ho'] at hr' ⊢
    have e : (h / (2 * q) + h / (2 * q')) * (q * q') = h * (q' / 2 + q / 2) := by
      field_simp
    rw [e]
    nlinarith

/-- **[Disjoint]**: the arcs of `idx N L` are pairwise disjoint when `hL ≤ 1/2`. -/
theorem arcs_disjoint (h L : ℝ) (N : ℕ) (hh : 0 < h) (hhL : h * L ≤ 1 / 2) :
    (↑(idx N L) : Set (Σ _ : ℕ, ℕ)).PairwiseDisjoint (arc h) := by
  rintro ⟨q, a⟩ hi ⟨q', a'⟩ hj hne
  simp only [idx, Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, fam, cop,
    Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hi hj
  obtain ⟨⟨⟨hq1, -⟩, hr⟩, -, hca⟩ := hi
  obtain ⟨⟨⟨hq1', -⟩, hr'⟩, -, hca'⟩ := hj
  have hne' : a * q' ≠ a' * q := by
    intro h0
    obtain ⟨rfl, rfl⟩ := eq_of_cross hca hca' (by omega) h0
    exact hne rfl
  have hb := width_budget h L hh hhL hq1 hq1' hr hr' hca hca' hne'
  refine Set.disjoint_left.mpr fun α h1 h2 => ?_
  simp only [arc, Set.mem_Ioo] at h1 h2
  obtain ⟨h1l, h1r⟩ := h1
  obtain ⟨h2l, h2r⟩ := h2
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hq0' : (0 : ℝ) < q' := by exact_mod_cast hq1'
  have hqq : (0 : ℝ) < q * q' := mul_pos hq0 hq0'
  have e1 : (a : ℝ) / q * (q * q') = a * q' := by rw [← mul_assoc, div_mul_cancel₀ _ hq0.ne']
  have e2 : (a' : ℝ) / q' * (q * q') = a' * q := by
    rw [mul_comm (q : ℝ) q', ← mul_assoc, div_mul_cancel₀ _ hq0'.ne']
  have d1 : ((a : ℝ) / q - a' / q') * (q * q') < (h / rho q + h / rho q') * (q * q') :=
    mul_lt_mul_of_pos_right (by linarith) hqq
  have d2 : ((a' : ℝ) / q' - a / q) * (q * q') < (h / rho q + h / rho q') * (q * q') :=
    mul_lt_mul_of_pos_right (by linarith) hqq
  rw [sub_mul, e1, e2] at d1
  rw [sub_mul, e1, e2] at d2
  have h6 : |(a : ℝ) * q' - a' * q| < (h / rho q + h / rho q') * (q * q') :=
    abs_lt.mpr ⟨by linarith, by linarith⟩
  linarith

/-! ## [Cover] -/

/-- **Membership in `idx`**. -/
theorem mem_idx {N : ℕ} {L : ℝ} {i : Σ _ : ℕ, ℕ} :
    i ∈ idx N L ↔ (1 ≤ i.1 ∧ i.1 ≤ N) ∧ rho i.1 ≤ 2 * L ∧ i.2 < i.1 ∧ Nat.Coprime i.2 i.1 := by
  simp only [idx, fam, cop, Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_range]
  tauto

/-- `h/ρ(q) ≤ h/2` for `q ≥ 1`. -/
theorem w_le (h : ℝ) (hh : 0 < h) {q : ℕ} (hq : 1 ≤ q) : h / rho q ≤ h / 2 :=
  div_le_div_of_nonneg_left hh.le two_pos (two_le_rho hq)

/-- `q·h/ρ(q) ≤ h`. -/
theorem qw_le (h : ℝ) (hh : 0 < h) {q : ℕ} (hq : 1 ≤ q) : (q : ℝ) * (h / rho q) ≤ h := by
  have hr := rho_pos hq
  rw [mul_div_assoc', div_le_iff₀ hr]
  have := (rho_bounds q).1
  nlinarith

/-- **[Cover]**: inside the window the arcs of `oeArcs h L` are exactly those of `idx N L`. -/
theorem win_cover (h L : ℝ) (N : ℕ) (hh : 0 < h) (hL : 1 ≤ L) (hhL : h * L ≤ 1 / 2)
    (hN : 2 * L < N + 1) : win h ∩ oeArcs h L = ⋃ i ∈ idx N L, arc h i := by
  have hh1 : h ≤ 1 / 2 := by nlinarith
  ext α
  rw [oeArcs_eq]
  simp only [win, Set.mem_inter_iff, Set.mem_Ioc, Set.mem_iUnion, Set.mem_Ioo, exists_prop]
  constructor
  · rintro ⟨⟨hw1, hw2⟩, q, ⟨hq1, hr⟩, a, hg, h1, h2⟩
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
    have hwq := w_le h hh hq1
    have hqL : (q : ℝ) ≤ 2 * L := le_trans (rho_bounds q).1 hr
    have hqN : q ≤ N := by
      have : (q : ℝ) < N + 1 := lt_of_le_of_lt hqL hN
      exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
    have hlt : (a : ℝ) / q < 1 := by linarith
    have hgt : -h < (a : ℝ) / q := by linarith
    have ha1 : (a : ℝ) < q := by rwa [div_lt_one hq0] at hlt
    have ha0 : (-1 : ℝ) < a := by
      have h3 : -h * q < a := (lt_div_iff₀ hq0).mp hgt
      have h4 : h * q ≤ 1 := by nlinarith
      linarith
    have haZ : (-1 : ℤ) < a := by exact_mod_cast ha0
    have haq : a < (q : ℤ) := by exact_mod_cast ha1
    obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ a)
    rw [Int.cast_natCast] at h1 h2
    have hbq : b < q := by omega
    refine ⟨⟨q, b⟩, mem_idx.mpr ⟨⟨hq1, hqN⟩, hr, hbq, ?_⟩, h1, h2⟩
    exact Nat.coprime_iff_gcd_eq_one.mpr (by rwa [Int.gcd_natCast_natCast] at hg)
  · rintro ⟨⟨q, b⟩, hi, h1, h2⟩
    obtain ⟨⟨hq1, -⟩, hr, hbq, hcop⟩ := mem_idx.mp hi
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
    have hwq := w_le h hh hq1
    have hb0 : (0 : ℝ) ≤ (b : ℝ) / q := by positivity
    have hbR : (b : ℝ) + 1 ≤ q := by exact_mod_cast hbq
    have hbq1 : (b : ℝ) / q + 1 / q ≤ 1 := by
      rw [← add_div, div_le_one hq0]
      exact hbR
    have hqL : (q : ℝ) ≤ 2 * L := le_trans (rho_bounds q).1 hr
    have hsmall : h / rho q + h / 2 ≤ 1 / q := by
      rw [le_div_iff₀ hq0]
      have hqw := qw_le h hh hq1
      have e : (h / rho q + h / 2) * q = q * (h / rho q) + q * h / 2 := by ring
      rw [e]
      nlinarith
    refine ⟨⟨by linarith, by linarith⟩, q, ⟨hq1, hr⟩, (b : ℤ), ?_, ?_, ?_⟩
    · rw [Int.gcd_natCast_natCast]
      exact hcop
    · rw [Int.cast_natCast]
      exact h1
    · rw [Int.cast_natCast]
      exact h2

/-! ## [Periodic] -/

/-- **`oeArcs h L` is `1`-periodic** (shift `a` by `kq`). -/
theorem mem_oe_add_int (h L α : ℝ) (k : ℤ) (hα : α ∈ oeArcs h L) : α + k ∈ oeArcs h L := by
  rw [oeArcs_eq] at hα ⊢
  simp only [Set.mem_iUnion, Set.mem_Ioo, exists_prop] at hα ⊢
  obtain ⟨q, ⟨hq1, hr⟩, a, hg, h1, h2⟩ := hα
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hc : ((a + k * q : ℤ) : ℝ) / q = (a : ℝ) / q + k := by
    push_cast
    rw [add_div, mul_div_cancel_right₀ _ hq0]
  refine ⟨q, ⟨hq1, hr⟩, a + k * q, ?_, ?_, ?_⟩
  · rw [Int.gcd_add_mul_right_left]
    exact hg
  · rw [hc]
    linarith
  · rw [hc]
    linarith

/-- The integrand restricted to `oeArcs h L` is `1`-periodic when the integrand is. -/
theorem periodic_ind (h L : ℝ) (F : ℝ → ℝ) (hF : ∀ α, F (α + 1) = F α) :
    Function.Periodic ((oeArcs h L).indicator F) 1 := by
  intro α
  by_cases hα : α ∈ oeArcs h L
  · have h' : α + 1 ∈ oeArcs h L := by
      have h3 := mem_oe_add_int h L α 1 hα
      rwa [Int.cast_one] at h3
    rw [Set.indicator_of_mem h', Set.indicator_of_mem hα, hF]
  · have h' : α + 1 ∉ oeArcs h L := by
      intro h1
      have h3 := mem_oe_add_int h L (α + 1) (-1) h1
      rw [Int.cast_neg, Int.cast_one, add_neg_cancel_right] at h3
      exact hα h3
    rw [Set.indicator_of_notMem h', Set.indicator_of_notMem hα]

/-- `oeArcs h L` is open, hence measurable. -/
theorem measurableSet_oe (h L : ℝ) : MeasurableSet (oeArcs h L) := by
  refine IsOpen.measurableSet ?_
  unfold oeArcs
  refine IsOpen.union ?_ ?_ <;>
  exact isOpen_iUnion fun q => isOpen_iUnion fun _ => isOpen_iUnion fun a =>
    isOpen_iUnion fun _ => isOpen_Ioo

/-- **[Periodic]**: `∫_{(0,1] ∩ 𝔐} F = ∫_{(−h/2, 1−h/2] ∩ 𝔐} F` for `1`-periodic `F`. -/
theorem periodic_shift (h L : ℝ) (F : ℝ → ℝ) (hF : ∀ α, F (α + 1) = F α) :
    ∫ α in Set.Ioc (0 : ℝ) 1 ∩ oeArcs h L, F α = ∫ α in win h ∩ oeArcs h L, F α := by
  have hM := measurableSet_oe h L
  have e1 : ∫ α in Set.Ioc (0 : ℝ) 1 ∩ oeArcs h L, F α =
      ∫ α in Set.Ioc (0 : ℝ) 1, (oeArcs h L).indicator F α := by
    rw [setIntegral_indicator hM]
  have e2 : ∫ α in Set.Ioc (0 : ℝ) 1, (oeArcs h L).indicator F α =
      ∫ α in (0 : ℝ)..0 + 1, (oeArcs h L).indicator F α := by
    rw [zero_add, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have e3 := (periodic_ind h L F hF).intervalIntegral_add_eq 0 (-(h / 2))
  have e4 : ∫ α in (-(h / 2))..(-(h / 2) + 1), (oeArcs h L).indicator F α =
      ∫ α in win h ∩ oeArcs h L, F α := by
    rw [intervalIntegral.integral_of_le (by linarith), setIntegral_indicator hM]
    rfl
  exact e1.trans (e2.trans (e3.trans e4))

/-! ## The reduction -/

/-- **Change of variables on one arc**: `∫_{(c−w, c+w)} F = ∫_{−w}^{w} F(c + β) dβ`. -/
theorem arc_cv (F : ℝ → ℝ) (c w : ℝ) (hw : 0 ≤ w) :
    ∫ α in Set.Ioo (c - w) (c + w), F α = ∫ β in (-w)..w, F (c + β) := by
  rw [intervalIntegral.integral_comp_add_left F c, ← sub_eq_add_neg,
    intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]

/-- **THE ARC REDUCTION**: for `F` continuous and `1`-periodic, `h > 0`, `L ≥ 1`, `hL ≤ 1/2`,
`2L < N + 1`: `∫_{(0,1] ∩ oeArcs h L} F = ∑_{q ∈ fam N L} ∫_{−h/ρ(q)}^{h/ρ(q)} T_q(β) dβ`. -/
theorem arc_reduce (F : ℝ → ℝ) (hc : Continuous F) (hp : ∀ α, F (α + 1) = F α) (h L : ℝ)
    (N : ℕ) (hh : 0 < h) (hL : 1 ≤ L) (hhL : h * L ≤ 1 / 2) (hN : 2 * L < N + 1) :
    ∫ α in Set.Ioc (0 : ℝ) 1 ∩ oeArcs h L, F α =
      ∑ q ∈ fam N L, ∫ β in (-(h / rho q))..(h / rho q), tS F q β := by
  rw [periodic_shift h L F hp, win_cover h L N hh hL hhL hN,
    integral_biUnion_finset (s := arc h) (idx N L) (fun i _ => measurableSet_Ioo)
      (arcs_disjoint h L N hh hhL)
      (fun i _ => hc.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self)]
  unfold idx
  rw [Finset.sum_sigma]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
  have hw : 0 ≤ h / rho q := div_nonneg hh.le (rho_pos hq1).le
  have hint : ∀ a ∈ cop q, IntervalIntegrable (fun β => F ((a : ℝ) / q + β)) volume
      (-(h / rho q)) (h / rho q) := fun a _ =>
    (hc.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  unfold tS
  rw [intervalIntegral.integral_finsetSum hint]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact arc_cv F _ _ hw

end Principia.Common.PSieve
