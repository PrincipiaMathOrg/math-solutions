/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.DrujalSpine
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

set_option autoImplicit false

/-!
# `DS.ArcInt` for EVERY weight: the spine of `ternvin.tex` 1272–1315, all links PROVED

`DS.ArcInt η` is the integration step of `lem:drujal` (`eq:juto`): per-arc bounds
`|∑_{(a,q)=1} |S_η(a/q+δ/x)|² − μ²(q)/φ(q)·x²|η̂(−δ)|²| ≤ errq q` on every arc of `𝔐_{8,r}`
integrate to `|A_η(x) − L_{r,δ₀}| ≤ (∑_{q odd} (δ₀r/q)·errq q + ∑_{q even} (2δ₀r/q)·errq q)/x²`.
This file writes that step as five links, composes them (`arcInt_of_links`), PROVES every link,
and so proves `arcInt_all : ∀ η, DS.ArcInt η` — generic in the weight, under nothing but the
summability of `∑ Λ(n)|η(n/x)|` that `ArcInt` itself supplies.

## The spine

```
 [Disjoint] the arcs (a/q ± wd q/x), (q,a) ∈ arcIdx, are pairwise disjoint at x ≥ 4.9·10²⁶
            (|a/q − a'/q'| ≥ 1/qq' and q·wd q ≤ 1.2·10⁶, so it suffices that 1.2·10⁶(q+q') ≤ x)
 [Cover]    (−c, 1−c] ∩ 𝔐_{8,r} = ⋃_{(q,a)} (a/q ± wd q/x),  c = 600000/x, 0 ≤ a < q, (a,q) = 1
 [Periodic] ∫_{(0,1] ∩ 𝔐} f = ∫_{(−c,1−c] ∩ 𝔐} f  for 1-periodic f  (𝔐 is 1-periodic)
   ⇒ ∫_𝔐 |S|² = ∑_{(q,a)} ∫_{a/q−wd q/x}^{a/q+wd q/x} |S|²          (reduce_of)
 [ChangeVar] ∫_{c−w/x}^{c+w/x} f = (1/x)∫_{−w}^{w} f(c+δ/x) dδ
   ⇒ ∑_a ∫_{arc (q,a)} |S|² = (1/x)∫_{−wd q}^{wd q} arcSq(q,δ) dδ       (collect_of)
 [Compare]  |g − h| ≤ b on [−w,w] ⇒ |∫g − ∫h| ≤ 2wb, with h = cQ·x²|η̂|²,  ∫h = cQ·x²·I_q(wd q)
 [Summation] A_η = ∑_q J_q/x², L = ∑_q cQ·I_q(wd q), 2·wd q = δ₀r/q (odd), 2δ₀r/q (even)
   ⇒ ArcInt η
```

`wd q = gcd(q,2)·600000/q` is `ArcInt`'s own bound on `|δ|`, verbatim, and `DS.arcSq`'s index set
`{0 ≤ a < q : (a,q) = 1}` is used verbatim (`cop`), so nothing is re-encoded.

## Two facts the source uses silently, both proved here

1. **Disjointness.** `eq:juto` replaces `∫_𝔐` by a sum over the arcs without comment. The arcs of
   `𝔐_{8,150000}` are disjoint once `δ₀r(q + q') ≤ x` for all moduli, i.e. at `x ≥ 7.2·10¹¹`
   (`arcsDisjoint` is stated at the file's `x ≥ 4.9·10²⁶`).
2. **Periodicity.** `amaj` integrates over `(0,1] ∩ 𝔐`, where the arc about `0/1` is cut in two
   (`(0, c)` and `(1 − c, 1]`). `eq:juto` integrates over the whole arc about `0`. They agree
   because `S_η(α + 1) = S_η(α)` and `𝔐` is `1`-periodic (`mem_arcs_add_int`); the window
   `(−c, 1−c]` contains every arc whole.

## Integrability, and why no hypothesis on `η` is needed

`|S_η(·,x)|²` is continuous under the summability `ArcInt` supplies (`Smooth.continuous_smSum`).
`δ ↦ |η̂(−δ)|²` is continuous for EVERY `η` (`continuous_mainFT`): for `η ∈ L¹(0,∞)` by dominated
convergence, and otherwise `MajSp.mainFT η ≡ 0` — the integrand `η(t)e(δt)` is integrable iff
`η` is, since `e(δt)` is unimodular and invertible. So `ArcInt` holds for every weight, integrable
or not.
-/

namespace Principia.Common.TernaryGoldbach.AI

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach
open scoped ArithmeticFunction

/-! ## The objects -/

/-- **The `δ`-half-width of the arc of modulus `q`**: `gcd(q,2)·δ₀r/2q = gcd(q,2)·600000/q`. This is
`DS.ArcInt`'s bound on `|δ|`, verbatim (`600000/q` for odd `q`, `1200000/q` for even `q`). -/
noncomputable def wd (q : ℕ) : ℝ := (Nat.gcd q 2 : ℝ) * 600000 / q

/-- **The moduli of `𝔐_{8,r}`**: the odd `q ≤ r` and the even `q ≤ 2r`. -/
def Qs : Finset ℕ := DS.oddQ ∪ DS.evenQ

/-- **The residues of modulus `q`**: `0 ≤ a < q`, `(a,q) = 1` — `DS.arcSq`'s index set, verbatim. -/
def cop (q : ℕ) : Finset ℕ := (Finset.range q).filter (fun a => Nat.Coprime a q)

/-- **The arcs of `𝔐_{8,r}` inside the window**, indexed by `(q, a)`. IRREDUCIBLE: it is a
computable `Finset` built from `150000`-element sets, and elaborating even `hi : i ∈ arcIdx`
against itself ran out of recursion depth while it was reducible (measured: the reducible
`Qs ×ˢ Qs` fails the same way, the irreducible `Qs.sigma cop` does not). Everything goes through
`mem_arcIdx` and `arcIdx_eq`. -/
@[irreducible] def arcIdx : Finset (Σ _ : ℕ, ℕ) := Qs.sigma cop

/-- The definition of `arcIdx`, as an equation. -/
theorem arcIdx_eq : arcIdx = Qs.sigma cop := by
  delta arcIdx
  rfl

/-- **The arc about `a/q`**: `(a/q − wd q/x, a/q + wd q/x)`. -/
noncomputable def arc (x : ℝ) (i : Σ _ : ℕ, ℕ) : Set ℝ :=
  Set.Ioo (((i.2 : ℕ) : ℝ) / i.1 - wd i.1 / x) (((i.2 : ℕ) : ℝ) / i.1 + wd i.1 / x)

/-- **The window** `(−c, 1 − c]`, `c = 600000/x` the half-width of the arc about `0`. -/
noncomputable def win (x : ℝ) : Set ℝ := Set.Ioc (-(600000 / x)) (-(600000 / x) + 1)

/-- **`|S_η(α,x)|²`**, the integrand of `A_η`. -/
noncomputable def sqS (η : ℝ → ℝ) (x α : ℝ) : ℝ := ‖Smooth.smSum η x α‖ ^ 2

/-! ## The links -/

/-- **Link [Disjoint]**: the arcs indexed by `arcIdx` are pairwise disjoint at `x ≥ 4.9·10²⁶`. -/
def ArcsDisjoint : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → (↑arcIdx : Set (Σ _ : ℕ, ℕ)).PairwiseDisjoint (arc x)

/-- **Link [Cover]**: inside the window `(−c, 1−c]` the major arcs are exactly the arcs of
`arcIdx`, each whole. -/
def WindowCover : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → win x ∩ Smooth.majArcs x = ⋃ i ∈ arcIdx, arc x i

/-- **Link [Periodic]**: for a `1`-periodic `f`, the integral over `(0,1] ∩ 𝔐` equals the integral
over `(−c, 1−c] ∩ 𝔐` (`𝔐` is `1`-periodic). -/
def PeriodicShift : Prop :=
  ∀ x : ℝ, ∀ f : ℝ → ℝ, (∀ α, f (α + 1) = f α) →
    ∫ α in Smooth.majorSet x, f α = ∫ α in win x ∩ Smooth.majArcs x, f α

/-- **Link [ChangeVar]**: `α = c + δ/x` maps `(−w, w)` onto the arc `(c − w/x, c + w/x)`. -/
def ChangeVar : Prop :=
  ∀ x : ℝ, 0 < x → ∀ (f : ℝ → ℝ) (c w : ℝ), 0 ≤ w →
    ∫ α in Set.Ioo (c - w / x) (c + w / x), f α = (∫ δ in (-w)..w, f (c + δ / x)) / x

/-- **Link [Compare]**: a pointwise bound `|g − h| ≤ b` on `[−w, w]` integrates to `2wb`. -/
def ArcCompare : Prop :=
  ∀ (g h : ℝ → ℝ) (w b : ℝ), 0 ≤ w → Continuous g → Continuous h →
    (∀ δ, |δ| ≤ w → |g δ - h δ| ≤ b) →
      |(∫ δ in (-w)..w, g δ) - ∫ δ in (-w)..w, h δ| ≤ 2 * w * b

/-- **Link [Summation]**: the per-modulus comparisons, summed with the arc lengths `2·wd q`, give
the conclusion of `DS.ArcInt`. -/
def Summation : Prop :=
  ∀ (η : ℝ → ℝ) (x : ℝ) (J errq : ℕ → ℝ), x ≠ 0 →
    MajSp.amaj η x = (∑ q ∈ Qs, J q) / x ^ 2 →
    (∀ q ∈ Qs, |J q - DS.cQ q * x ^ 2 * DS.iQ η (wd q)| ≤ 2 * wd q * errq q) →
      |MajSp.amaj η x - DS.lRD η| ≤
        (∑ q ∈ DS.oddQ, 1200000 / (q : ℝ) * errq q +
          ∑ q ∈ DS.evenQ, 2400000 / (q : ℝ) * errq q) / x ^ 2

/-! ## Arithmetic of the moduli -/

/-- `x ≥ 4.9·10²⁶ ⇒ x > 0`. -/
theorem x_pos {x : ℝ} (hx : 49 * 10 ^ 25 ≤ x) : 0 < x := lt_of_lt_of_le (by norm_num) hx

/-- `wd q ≥ 0`. -/
theorem wd_nonneg (q : ℕ) : 0 ≤ wd q := by
  unfold wd
  positivity

/-- `q·wd q = gcd(q,2)·600000`. -/
theorem wd_mul (q : ℕ) (hq : q ≠ 0) : (q : ℝ) * wd q = (Nat.gcd q 2 : ℝ) * 600000 := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  unfold wd
  rw [mul_div_assoc', mul_div_cancel_left₀ _ hq']

/-- `gcd(q,2) ≤ 2`. -/
theorem gcd_le_two (q : ℕ) : (Nat.gcd q 2 : ℝ) ≤ 2 := by
  exact_mod_cast Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_right q 2)

/-- `q·wd q ≤ 1.2·10⁶`. -/
theorem qwd_le (q : ℕ) (hq : 1 ≤ q) : (q : ℝ) * wd q ≤ 1200000 := by
  rw [wd_mul q (by omega)]
  have := gcd_le_two q
  linarith

/-- `wd q ≤ 600000` (`gcd(q,2) ≤ q`): no arc is wider than the one about `0`. -/
theorem wd_le (q : ℕ) (hq : 1 ≤ q) : wd q ≤ 600000 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hg : Nat.gcd q 2 ≤ q := Nat.le_of_dvd hq (Nat.gcd_dvd_left q 2)
  have hgR : (Nat.gcd q 2 : ℝ) ≤ q := by exact_mod_cast hg
  unfold wd
  rw [div_le_iff₀ hq0]
  linarith

/-- The two kinds of modulus. -/
theorem Qs_cases {q : ℕ} (hq : q ∈ Qs) :
    (Odd q ∧ 1 ≤ q ∧ q ≤ 150000 ∧ Nat.gcd q 2 = 1) ∨
      (Even q ∧ 1 ≤ q ∧ q ≤ 300000 ∧ Nat.gcd q 2 = 2) := by
  rcases Finset.mem_union.mp hq with h | h
  · obtain ⟨h1, ho⟩ := Finset.mem_filter.mp h
    obtain ⟨h2, h3⟩ := Finset.mem_Icc.mp h1
    exact Or.inl ⟨ho, h2, h3, Nat.coprime_two_right.mpr ho⟩
  · obtain ⟨h1, he⟩ := Finset.mem_filter.mp h
    obtain ⟨h2, h3⟩ := Finset.mem_Icc.mp h1
    exact Or.inr ⟨he, h2, h3, Nat.gcd_eq_right (even_iff_two_dvd.mp he)⟩

/-- `1 ≤ q ≤ 300000` on the moduli. -/
theorem Qs_bounds {q : ℕ} (hq : q ∈ Qs) : 1 ≤ q ∧ q ≤ 300000 := by
  rcases Qs_cases hq with ⟨-, h1, h2, -⟩ | ⟨-, h1, h2, -⟩
  · exact ⟨h1, by omega⟩
  · exact ⟨h1, h2⟩

/-- **The moduli are exactly `ArcInt`'s range** `1 ≤ q ≤ r·gcd(q,2)` (this direction). -/
theorem Qs_range {q : ℕ} (hq : q ∈ Qs) : 1 ≤ q ∧ q ≤ 150000 * Nat.gcd q 2 := by
  rcases Qs_cases hq with ⟨-, h1, h2, hg⟩ | ⟨-, h1, h2, hg⟩
  · rw [hg]
    exact ⟨h1, by omega⟩
  · rw [hg]
    exact ⟨h1, by omega⟩

/-- The odd and even moduli are disjoint. -/
theorem disj_oe : Disjoint DS.oddQ DS.evenQ := by
  rw [Finset.disjoint_left]
  intro q h1 h2
  exact Nat.not_even_iff_odd.mpr (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2

/-- `wd q = 600000/q` on the odd moduli. -/
theorem wd_odd {q : ℕ} (hq : q ∈ DS.oddQ) : wd q = 600000 / q := by
  have hg : Nat.gcd q 2 = 1 := Nat.coprime_two_right.mpr (Finset.mem_filter.mp hq).2
  unfold wd
  rw [hg, Nat.cast_one, one_mul]

/-- `wd q = 1200000/q` on the even moduli. -/
theorem wd_even {q : ℕ} (hq : q ∈ DS.evenQ) : wd q = 1200000 / q := by
  have hg : Nat.gcd q 2 = 2 := Nat.gcd_eq_right (even_iff_two_dvd.mp (Finset.mem_filter.mp hq).2)
  unfold wd
  rw [hg]
  norm_num

/-- **Membership in `arcIdx`**, stated so that no proof ever has to unfold the (computable)
`Finset.sigma` of `150000`-element sets. -/
theorem mem_arcIdx {i : Σ _ : ℕ, ℕ} :
    i ∈ arcIdx ↔ i.1 ∈ Qs ∧ i.2 < i.1 ∧ Nat.Coprime i.2 i.1 := by
  have hP : arcIdx = Qs.sigma cop := arcIdx_eq
  have hc : ∀ q, cop q = (Finset.range q).filter (fun a => Nat.Coprime a q) := fun _ => rfl
  rw [hP, Finset.mem_sigma, hc, Finset.mem_filter, Finset.mem_range]

/-- The odd radius of `Smooth.arcs 8 150000` is `wd q / x`. -/
theorem rad_odd {q : ℕ} {x : ℝ} (hq : q ≠ 0) (hx : x ≠ 0) (hg : Nat.gcd q 2 = 1) :
    (8 : ℝ) * ((150000 : ℕ) : ℝ) / (2 * (q : ℝ) * x) = wd q / x := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  unfold wd
  rw [hg, Nat.cast_one, one_mul, div_div,
    div_eq_div_iff (mul_ne_zero (mul_ne_zero two_ne_zero hq') hx) (mul_ne_zero hq' hx)]
  push_cast
  ring

/-- The even radius of `Smooth.arcs 8 150000` is `wd q / x`. -/
theorem rad_even {q : ℕ} {x : ℝ} (hq : q ≠ 0) (hx : x ≠ 0) (hg : Nat.gcd q 2 = 2) :
    (8 : ℝ) * ((150000 : ℕ) : ℝ) / ((q : ℝ) * x) = wd q / x := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  unfold wd
  rw [hg, div_div, div_eq_div_iff (mul_ne_zero hq' hx) (mul_ne_zero hq' hx)]
  push_cast
  ring

/-! ## [Disjoint] -/

/-- **Reduced fractions are determined by their value**: `a/q = a'/q'` in lowest terms forces
`(q, a) = (q', a')`. -/
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

/-- **[Disjoint], PROVED.** Distinct reduced fractions with moduli `≤ 300000` are `≥ 1/qq'` apart,
while the two half-widths sum to `(q·wd q·q' + q'·wd q'·q)/(xqq') ≤ 7.2·10¹¹/(xqq')`. -/
theorem arcsDisjoint : ArcsDisjoint := by
  intro x hx
  have hx0 : 0 < x := x_pos hx
  rintro ⟨q, a⟩ hi ⟨q', a'⟩ hj hne
  obtain ⟨hq, -, hca⟩ : q ∈ Qs ∧ a < q ∧ Nat.Coprime a q := mem_arcIdx.mp (Finset.mem_coe.mp hi)
  obtain ⟨hq', -, hca'⟩ : q' ∈ Qs ∧ a' < q' ∧ Nat.Coprime a' q' :=
    mem_arcIdx.mp (Finset.mem_coe.mp hj)
  obtain ⟨hq1, hq2⟩ := Qs_bounds hq
  obtain ⟨hq1', hq2'⟩ := Qs_bounds hq'
  have hne' : a * q' ≠ a' * q := by
    intro h
    obtain ⟨rfl, rfl⟩ := eq_of_cross hca hca' (by omega) h
    exact hne rfl
  refine Set.disjoint_left.mpr fun α h1 h2 => ?_
  simp only [arc, Set.mem_Ioo] at h1 h2
  obtain ⟨h1l, h1r⟩ := h1
  obtain ⟨h2l, h2r⟩ := h2
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hq0' : (0 : ℝ) < q' := by exact_mod_cast hq1'
  have hqR : (q : ℝ) ≤ 300000 := by exact_mod_cast hq2
  have hqR' : (q' : ℝ) ≤ 300000 := by exact_mod_cast hq2'
  have hA := qwd_le q hq1
  have hB := qwd_le q' hq1'
  have hkey : (wd q / x + wd q' / x) * (q * q') ≤ 1 := by
    have e : (wd q / x + wd q' / x) * (q * q') = ((q * wd q) * q' + (q' * wd q') * q) / x := by
      ring
    rw [e, div_le_one hx0]
    have h3 : (q * wd q) * q' ≤ 1200000 * 300000 := mul_le_mul hA hqR' hq0'.le (by norm_num)
    have h4 : (q' * wd q') * q ≤ 1200000 * 300000 := mul_le_mul hB hqR hq0.le (by norm_num)
    linarith
  have e1 : (a : ℝ) / q * (q * q') = a * q' := by rw [← mul_assoc, div_mul_cancel₀ _ hq0.ne']
  have e2 : (a' : ℝ) / q' * (q * q') = a' * q := by
    rw [mul_comm (q : ℝ) q', ← mul_assoc, div_mul_cancel₀ _ hq0'.ne']
  have hqq : (0 : ℝ) < q * q' := mul_pos hq0 hq0'
  have d1 : ((a : ℝ) / q - a' / q') * (q * q') < (wd q / x + wd q' / x) * (q * q') :=
    mul_lt_mul_of_pos_right (by linarith) hqq
  have d2 : ((a' : ℝ) / q' - a / q) * (q * q') < (wd q / x + wd q' / x) * (q * q') :=
    mul_lt_mul_of_pos_right (by linarith) hqq
  rw [sub_mul, e1, e2] at d1
  rw [sub_mul, e1, e2] at d2
  have hn : (a : ℤ) * q' - a' * q ≠ 0 := by
    intro h
    apply hne'
    have h3 : (a : ℤ) * q' = a' * q := by linarith
    exact_mod_cast h3
  have h5 : (1 : ℝ) ≤ |(((a : ℤ) * q' - a' * q : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hn
  push_cast at h5
  have h6 : |(a : ℝ) * q' - a' * q| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  linarith

/-! ## [Cover] -/

/-- An arc of `𝔐_{8,r}` meeting the window is one of `arcIdx`'s: its centre has `0 ≤ a < q`. -/
theorem cover_fwd (x α : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (q : ℕ) (hq : q ∈ Qs) (a : ℤ)
    (hg : Int.gcd a q = 1) (hw : α ∈ win x)
    (h1 : (a : ℝ) / q - wd q / x < α) (h2 : α < (a : ℝ) / q + wd q / x) :
    α ∈ ⋃ i ∈ arcIdx, arc x i := by
  have hx0 : 0 < x := x_pos hx
  obtain ⟨hq1, hq2⟩ := Qs_bounds hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hqR : (q : ℝ) ≤ 300000 := by exact_mod_cast hq2
  have hwx : wd q / x ≤ 600000 / x := div_le_div_of_nonneg_right (wd_le q hq1) hx0.le
  obtain ⟨hw1, hw2⟩ := hw
  have hlt : (a : ℝ) / q < 1 := by linarith
  have hgt : -2 * (600000 / x) < (a : ℝ) / q := by linarith
  have hcq : 600000 / x * q ≤ 1 / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hx0]
    linarith
  have ha1 : (a : ℝ) < q := by rwa [div_lt_one hq0] at hlt
  have ha0 : (-1 : ℝ) < a := by
    have h3 : -2 * (600000 / x) * q < a := (lt_div_iff₀ hq0).mp hgt
    have h4 : -2 * (600000 / x) * q = -2 * (600000 / x * q) := by ring
    linarith
  have haZ : (-1 : ℤ) < a := by exact_mod_cast ha0
  have haq : a < (q : ℤ) := by exact_mod_cast ha1
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ a)
  rw [Int.cast_natCast] at h1 h2
  rw [Set.mem_iUnion₂]
  refine ⟨⟨q, b⟩, mem_arcIdx.mpr ⟨hq, show b < q by omega, ?_⟩, ?_⟩
  · exact Nat.coprime_iff_gcd_eq_one.mpr (by rwa [Int.gcd_natCast_natCast] at hg)
  · exact ⟨h1, h2⟩

/-- Every arc of `arcIdx` lies in the window and in `𝔐_{8,r}`. -/
theorem cover_bwd (x α : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (i : Σ _ : ℕ, ℕ) (hi : i ∈ arcIdx)
    (hα : α ∈ arc x i) : α ∈ win x ∩ Smooth.majArcs x := by
  obtain ⟨q, b⟩ := i
  obtain ⟨hq, hbq', hcop⟩ : q ∈ Qs ∧ b < q ∧ Nat.Coprime b q := mem_arcIdx.mp hi
  simp only [arc, Set.mem_Ioo] at hα
  obtain ⟨h1, h2⟩ := hα
  have hx0 : 0 < x := x_pos hx
  obtain ⟨hq1, hq2⟩ := Qs_bounds hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hqR : (q : ℝ) ≤ 300000 := by exact_mod_cast hq2
  have hwx : wd q / x ≤ 600000 / x := div_le_div_of_nonneg_right (wd_le q hq1) hx0.le
  have hb0 : (0 : ℝ) ≤ (b : ℝ) / q := by positivity
  have hbR : (b : ℝ) + 1 ≤ q := by exact_mod_cast hbq'
  have hbq1 : (b : ℝ) / q + 1 / q ≤ 1 := by
    rw [← add_div, div_le_one hq0]
    exact hbR
  have hsmall : wd q / x + 600000 / x ≤ 1 / q := by
    rw [le_div_iff₀ hq0]
    have hqw := qwd_le q hq1
    have e : (wd q / x + 600000 / x) * q = ((q : ℝ) * wd q + 600000 * q) / x := by ring
    rw [e, div_le_one hx0]
    linarith
  refine ⟨⟨by linarith, by linarith⟩, ?_⟩
  simp only [Smooth.majArcs, Smooth.arcs, Set.mem_union, Set.mem_iUnion, Set.mem_Ioo]
  rcases Qs_cases hq with ⟨ho, -, hq2', hg⟩ | ⟨he, -, hq2', hg⟩
  · refine Or.inl ⟨q, ⟨hq1, hq2'⟩, ho, (b : ℤ), ?_, ?_, ?_⟩
    · rw [Int.gcd_natCast_natCast]
      exact hcop
    · rw [Int.cast_natCast, rad_odd (by omega) hx0.ne' hg]
      exact h1
    · rw [Int.cast_natCast, rad_odd (by omega) hx0.ne' hg]
      exact h2
  · refine Or.inr ⟨q, ⟨hq1, by omega⟩, he, (b : ℤ), ?_, ?_, ?_⟩
    · rw [Int.gcd_natCast_natCast]
      exact hcop
    · rw [Int.cast_natCast, rad_even (by omega) hx0.ne' hg]
      exact h1
    · rw [Int.cast_natCast, rad_even (by omega) hx0.ne' hg]
      exact h2

/-- **[Cover], PROVED.** -/
theorem windowCover : WindowCover := by
  intro x hx
  have hx0 : 0 < x := x_pos hx
  ext α
  constructor
  · rintro ⟨hw, hm⟩
    simp only [Smooth.majArcs, Smooth.arcs, Set.mem_union, Set.mem_iUnion, Set.mem_Ioo] at hm
    rcases hm with ⟨q, hq, ho, a, hg, h1, h2⟩ | ⟨q, hq, he, a, hg, h1, h2⟩
    · have hQ : q ∈ Qs := Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq.1, hq.2⟩, ho⟩)
      have hq0 : q ≠ 0 := by
        have := hq.1
        omega
      rw [rad_odd hq0 hx0.ne' (Nat.coprime_two_right.mpr ho)] at h1 h2
      exact cover_fwd x α hx q hQ a hg hw h1 h2
    · have hq2 : q ≤ 300000 := by
        have := hq.2
        omega
      have hQ : q ∈ Qs := Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq.1, hq2⟩, he⟩)
      have hq0 : q ≠ 0 := by
        have := hq.1
        omega
      rw [rad_even hq0 hx0.ne' (Nat.gcd_eq_right (even_iff_two_dvd.mp he))] at h1 h2
      exact cover_fwd x α hx q hQ a hg hw h1 h2
  · intro h
    rw [Set.mem_iUnion₂] at h
    obtain ⟨i, hi, hα⟩ := h
    exact cover_bwd x α hx i hi hα

/-! ## [Periodic] -/

/-- **`𝔐` is `1`-periodic** (shift `a` by `kq`; `(a + kq, q) = (a, q)`). -/
theorem mem_arcs_add_int (x α : ℝ) (k : ℤ) (h : α ∈ Smooth.majArcs x) :
    α + k ∈ Smooth.majArcs x := by
  simp only [Smooth.majArcs, Smooth.arcs, Set.mem_union, Set.mem_iUnion, Set.mem_Ioo] at h ⊢
  rcases h with ⟨q, hq, ho, a, hg, h1, h2⟩ | ⟨q, hq, he, a, hg, h1, h2⟩
  · have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hq.1; omega)
    have hc : ((a + k * q : ℤ) : ℝ) / q = (a : ℝ) / q + k := by
      push_cast
      rw [add_div, mul_div_cancel_right₀ _ hq0]
    refine Or.inl ⟨q, hq, ho, a + k * q, ?_, ?_, ?_⟩
    · rw [Int.gcd_add_mul_right_left]
      exact hg
    · rw [hc]
      linarith
    · rw [hc]
      linarith
  · have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hq.1; omega)
    have hc : ((a + k * q : ℤ) : ℝ) / q = (a : ℝ) / q + k := by
      push_cast
      rw [add_div, mul_div_cancel_right₀ _ hq0]
    refine Or.inr ⟨q, hq, he, a + k * q, ?_, ?_, ?_⟩
    · rw [Int.gcd_add_mul_right_left]
      exact hg
    · rw [hc]
      linarith
    · rw [hc]
      linarith

/-- The integrand restricted to `𝔐` is `1`-periodic when the integrand is. -/
theorem periodic_ind (x : ℝ) (f : ℝ → ℝ) (hf : ∀ α, f (α + 1) = f α) :
    Function.Periodic ((Smooth.majArcs x).indicator f) 1 := by
  intro α
  by_cases h : α ∈ Smooth.majArcs x
  · have h' : α + 1 ∈ Smooth.majArcs x := by
      have h3 := mem_arcs_add_int x α 1 h
      rwa [Int.cast_one] at h3
    rw [Set.indicator_of_mem h', Set.indicator_of_mem h, hf]
  · have h' : α + 1 ∉ Smooth.majArcs x := by
      intro h1
      have h3 := mem_arcs_add_int x (α + 1) (-1) h1
      rw [Int.cast_neg, Int.cast_one, add_neg_cancel_right] at h3
      exact h h3
    rw [Set.indicator_of_notMem h', Set.indicator_of_notMem h]

/-- **[Periodic], PROVED.** `(0,1]` and `(−c, 1−c]` are both periods; `Function.Periodic`'s
interval integral does not depend on the starting point. -/
theorem periodicShift : PeriodicShift := by
  intro x f hf
  have hM := Smooth.measurableSet_maj x
  have e1 : ∫ α in Smooth.majorSet x, f α =
      ∫ α in Set.Ioc (0 : ℝ) 1, (Smooth.majArcs x).indicator f α :=
    (setIntegral_indicator hM).symm
  have e2 : ∫ α in Set.Ioc (0 : ℝ) 1, (Smooth.majArcs x).indicator f α =
      ∫ α in (0 : ℝ)..0 + 1, (Smooth.majArcs x).indicator f α := by
    rw [zero_add, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have e3 := (periodic_ind x f hf).intervalIntegral_add_eq 0 (-(600000 / x))
  have e4 : ∫ α in (-(600000 / x))..(-(600000 / x) + 1), (Smooth.majArcs x).indicator f α =
      ∫ α in win x ∩ Smooth.majArcs x, f α :=
    (intervalIntegral.integral_of_le (by linarith)).trans (setIntegral_indicator hM)
  exact e1.trans (e2.trans (e3.trans e4))

/-! ## [ChangeVar] and [Compare] -/

/-- **[ChangeVar], PROVED.** `intervalIntegral.integral_comp_add_div`, and `Ioo` vs `Ioc`. -/
theorem changeVar : ChangeVar := by
  intro x hx f c w hw
  have hle : c - w / x ≤ c + w / x := by
    have := div_nonneg hw hx.le
    linarith
  have h1 : ∫ α in Set.Ioo (c - w / x) (c + w / x), f α =
      ∫ α in (c - w / x)..(c + w / x), f α := by
    rw [intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo]
  have h2 : ∫ δ in (-w)..w, f (c + δ / x) = x * ∫ α in (c - w / x)..(c + w / x), f α := by
    rw [intervalIntegral.integral_comp_add_div f hx.ne' c, smul_eq_mul, neg_div,
      ← sub_eq_add_neg]
  rw [h1, h2, mul_div_cancel_left₀ _ hx.ne']

/-- **[Compare], PROVED.** `‖∫_{−w}^{w} (g − h)‖ ≤ b·|w − (−w)|`. -/
theorem arcCompare : ArcCompare := by
  intro g h w b hw hg hh hb
  have hin : ∀ δ ∈ Set.uIoc (-w) w, ‖g δ - h δ‖ ≤ b := by
    intro δ hδ
    rw [Real.norm_eq_abs]
    refine hb δ (abs_le.mpr ?_)
    rcases Set.mem_uIoc.mp hδ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const hin
  rw [intervalIntegral.integral_sub (hg.intervalIntegrable _ _) (hh.intervalIntegrable _ _),
    Real.norm_eq_abs, sub_neg_eq_add, abs_of_nonneg (by linarith : (0 : ℝ) ≤ w + w)] at h1
  calc |(∫ δ in (-w)..w, g δ) - ∫ δ in (-w)..w, h δ| ≤ b * (w + w) := h1
    _ = 2 * w * b := by ring

/-! ## [Summation] -/

/-- `L_{r,δ₀}` over `Qs`: `lRD η = ∑_{q ∈ Qs} cQ q·I_q(wd q)`. -/
theorem lRD_eq_Qs (η : ℝ → ℝ) : DS.lRD η = ∑ q ∈ Qs, DS.cQ q * DS.iQ η (wd q) := by
  have hQ : Qs = DS.oddQ ∪ DS.evenQ := rfl
  rw [hQ, Finset.sum_union disj_oe]
  unfold DS.lRD
  congr 1
  · exact Finset.sum_congr rfl fun q hq => by rw [wd_odd hq]
  · exact Finset.sum_congr rfl fun q hq => by rw [wd_even hq]

/-- The arc lengths: `∑_{q ∈ Qs} 2·wd q·errq q` is `ArcInt`'s right side (times `x²`). -/
theorem rhs_eq (errq : ℕ → ℝ) : ∑ q ∈ Qs, 2 * wd q * errq q =
    ∑ q ∈ DS.oddQ, 1200000 / (q : ℝ) * errq q + ∑ q ∈ DS.evenQ, 2400000 / (q : ℝ) * errq q := by
  have hQ : Qs = DS.oddQ ∪ DS.evenQ := rfl
  rw [hQ, Finset.sum_union disj_oe]
  congr 1
  · refine Finset.sum_congr rfl fun q hq => ?_
    rw [wd_odd hq]
    ring
  · refine Finset.sum_congr rfl fun q hq => ?_
    rw [wd_even hq]
    ring

/-- **[Summation], PROVED.** `A − L = ∑_q (J_q − cQ·x²·I_q)/x²` and the triangle inequality. -/
theorem summation : Summation := by
  intro η x J errq hx0 hA hJ
  have hx2 : 0 < x ^ 2 := lt_of_le_of_ne (sq_nonneg x) (Ne.symm (pow_ne_zero 2 hx0))
  have e : ∑ q ∈ Qs, DS.cQ q * x ^ 2 * DS.iQ η (wd q) =
      x ^ 2 * ∑ q ∈ Qs, DS.cQ q * DS.iQ η (wd q) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  have hdiff : MajSp.amaj η x - DS.lRD η =
      (∑ q ∈ Qs, (J q - DS.cQ q * x ^ 2 * DS.iQ η (wd q))) / x ^ 2 := by
    rw [hA, lRD_eq_Qs η, Finset.sum_sub_distrib, e, sub_div, mul_div_cancel_left₀ _ hx2.ne']
  rw [hdiff, abs_div, abs_of_pos hx2, ← rhs_eq errq]
  exact div_le_div_of_nonneg_right
    ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hJ)) hx2.le

/-! ## The analytic facts the composition needs (all proved) -/

/-- `e(n) = 1` for `n ∈ ℕ`. -/
theorem e_nat (n : ℕ) : e (n : ℝ) = 1 := (e_eq_one_iff (n : ℝ)).mpr ⟨n, (Int.cast_natCast n).symm⟩

/-- **`S_η(α + 1, x) = S_η(α, x)`**: the frequencies are integers. -/
theorem smSum_add_one (η : ℝ → ℝ) (x α : ℝ) :
    Smooth.smSum η x (α + 1) = Smooth.smSum η x α := by
  unfold Smooth.smSum
  refine tsum_congr fun n => ?_
  rw [mul_add, mul_one, ← e_add, e_nat n, mul_one]

/-- `|S_η|²` is `1`-periodic. -/
theorem sqS_periodic (η : ℝ → ℝ) (x : ℝ) (α : ℝ) : sqS η x (α + 1) = sqS η x α := by
  unfold sqS
  rw [smSum_add_one]

/-- `|S_η|²` is continuous under summability. -/
theorem continuous_sqS (η : ℝ → ℝ) (x : ℝ)
    (hs : Summable (fun n : ℕ => Λ n * |η ((n : ℝ) / x)|)) : Continuous (sqS η x) :=
  (Smooth.continuous_smSum η x hs).norm.pow 2

/-- `δ ↦ ∑_{(a,q)=1} |S_η(a/q + δ/x)|²` is continuous under summability. -/
theorem continuous_arcSq (η : ℝ → ℝ) (x : ℝ)
    (hs : Summable (fun n : ℕ => Λ n * |η ((n : ℝ) / x)|)) (q : ℕ) :
    Continuous fun δ => DS.arcSq η x q δ := by
  unfold DS.arcSq
  exact continuous_finsetSum _ fun a _ =>
    ((Smooth.continuous_smSum η x hs).comp
      (continuous_const.add (continuous_id.div_const x))).norm.pow 2

/-- **`δ ↦ η̂(−δ)` is continuous for EVERY `η`**: dominated convergence when `η ∈ L¹(0,∞)`, and
`MajSp.mainFT η ≡ 0` otherwise (`η(t)e(δt)` integrable forces `η` integrable). -/
theorem continuous_mainFT (η : ℝ → ℝ) : Continuous (MajSp.mainFT η) := by
  by_cases hη : Integrable η (volume.restrict (Set.Ioi 0))
  · have hc : ∀ t : ℝ, Continuous fun δ : ℝ => ((η t : ℝ) : ℂ) * e (δ * t) := fun t =>
      continuous_const.mul (Spine.continuous_e.comp (continuous_mul_const t))
    change Continuous fun δ => ∫ t in Set.Ioi (0 : ℝ), ((η t : ℝ) : ℂ) * e (δ * t)
    exact continuous_of_dominated
      (fun δ => (Complex.continuous_ofReal.comp_aestronglyMeasurable hη.aestronglyMeasurable).mul
        (Spine.continuous_e.comp (continuous_const_mul δ)).aestronglyMeasurable)
      (fun δ => Filter.Eventually.of_forall fun t =>
        le_of_eq (by rw [norm_mul, e_norm, mul_one, Complex.norm_real]))
      hη.norm (Filter.Eventually.of_forall hc)
  · have he0 : e 0 = 1 := by simp [e]
    have h0 : ∀ δ, MajSp.mainFT η δ = 0 := by
      intro δ
      unfold MajSp.mainFT
      refine integral_undef fun hi => hη ?_
      have h1 : AEStronglyMeasurable (fun t => ((η t : ℝ) : ℂ) * e (δ * t) * e (-(δ * t)))
          (volume.restrict (Set.Ioi 0)) :=
        hi.aestronglyMeasurable.mul
          (Spine.continuous_e.comp (continuous_const_mul δ).neg).aestronglyMeasurable
      have h2 : (fun t => (((η t : ℝ) : ℂ) * e (δ * t) * e (-(δ * t))).re) = η := by
        funext t
        rw [mul_assoc, e_add, add_neg_cancel, he0, mul_one, Complex.ofReal_re]
      have hm : AEStronglyMeasurable η (volume.restrict (Set.Ioi 0)) := by
        have h3 := Complex.continuous_re.comp_aestronglyMeasurable h1
        rwa [h2] at h3
      exact hi.norm.mono' hm (Filter.Eventually.of_forall fun t =>
        le_of_eq (by rw [norm_mul, e_norm, mul_one, Complex.norm_real]))
    have h00 : MajSp.mainFT η = fun _ => 0 := funext h0
    rw [h00]
    exact continuous_const

/-! ## The composition -/

/-- **`∫_𝔐 f = ∑_{(q,a)} ∫_{arc} f`** for continuous `1`-periodic `f`: [Periodic], [Cover],
[Disjoint]. -/
theorem reduce_of (dj : ArcsDisjoint) (cv : WindowCover) (ps : PeriodicShift) (x : ℝ)
    (hx : 49 * 10 ^ 25 ≤ x) (f : ℝ → ℝ) (hc : Continuous f) (hp : ∀ α, f (α + 1) = f α) :
    ∫ α in Smooth.majorSet x, f α = ∑ i ∈ arcIdx, ∫ α in arc x i, f α := by
  rw [ps x f hp, cv x hx]
  exact integral_biUnion_finset arcIdx (fun i _ => measurableSet_Ioo) (dj x hx)
    (fun i _ => hc.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self)

/-- **The arcs of one modulus, collected**: [ChangeVar] on each arc, then the finite sum under the
integral gives `DS.arcSq`. -/
theorem collect_of (ch : ChangeVar) (x : ℝ) (hx0 : 0 < x) (η : ℝ → ℝ)
    (hs : Summable (fun n : ℕ => Λ n * |η ((n : ℝ) / x)|)) (q : ℕ) :
    ∑ a ∈ cop q, ∫ α in arc x ⟨q, a⟩, sqS η x α =
      (∫ δ in (-wd q)..(wd q), DS.arcSq η x q δ) / x := by
  have h1 : ∀ a ∈ cop q, ∫ α in arc x ⟨q, a⟩, sqS η x α =
      (∫ δ in (-wd q)..(wd q), sqS η x ((a : ℝ) / q + δ / x)) / x :=
    fun a _ => ch x hx0 (sqS η x) ((a : ℝ) / q) (wd q) (wd_nonneg q)
  have hint : ∀ a ∈ cop q, IntervalIntegrable (fun δ => sqS η x ((a : ℝ) / q + δ / x))
      volume (-wd q) (wd q) := fun a _ =>
    ((continuous_sqS η x hs).comp
      (continuous_const.add (continuous_id.div_const x))).intervalIntegrable _ _
  calc ∑ a ∈ cop q, ∫ α in arc x ⟨q, a⟩, sqS η x α
      = ∑ a ∈ cop q, (∫ δ in (-wd q)..(wd q), sqS η x ((a : ℝ) / q + δ / x)) / x :=
        Finset.sum_congr rfl h1
    _ = (∑ a ∈ cop q, ∫ δ in (-wd q)..(wd q), sqS η x ((a : ℝ) / q + δ / x)) / x := by
        rw [Finset.sum_div]
    _ = (∫ δ in (-wd q)..(wd q), ∑ a ∈ cop q, sqS η x ((a : ℝ) / q + δ / x)) / x := by
        rw [intervalIntegral.integral_finsetSum hint]
    _ = (∫ δ in (-wd q)..(wd q), DS.arcSq η x q δ) / x := rfl

/-- **`A_η(x) = ∑_q J_q / x²`** from the reduction and the per-modulus collection. -/
theorem amaj_eq (η : ℝ → ℝ) (x : ℝ) (J : ℕ → ℝ)
    (hred : ∫ α in Smooth.majorSet x, sqS η x α = ∑ i ∈ arcIdx, ∫ α in arc x i, sqS η x α)
    (hmod : ∀ q ∈ Qs, ∑ a ∈ cop q, ∫ α in arc x ⟨q, a⟩, sqS η x α = J q / x) :
    MajSp.amaj η x = (∑ q ∈ Qs, J q) / x ^ 2 := by
  have h1 : MajSp.amaj η x = (∫ α in Smooth.majorSet x, sqS η x α) / x := rfl
  have hP : arcIdx = Qs.sigma cop := arcIdx_eq
  rw [h1, hred, hP, Finset.sum_sigma, Finset.sum_congr rfl hmod, ← Finset.sum_div, div_div,
    ← pow_two]

/-- **The per-modulus comparison**: [Compare] with `g = arcSq`, `h = cQ·x²·|η̂|²`. -/
theorem compare_of (cm : ArcCompare) (η : ℝ → ℝ) (x : ℝ)
    (hs : Summable (fun n : ℕ => Λ n * |η ((n : ℝ) / x)|)) (q : ℕ) (b : ℝ)
    (hb : ∀ δ, |δ| ≤ wd q →
      |DS.arcSq η x q δ - DS.cQ q * x ^ 2 * ‖MajSp.mainFT η δ‖ ^ 2| ≤ b) :
    |(∫ δ in (-wd q)..(wd q), DS.arcSq η x q δ) - DS.cQ q * x ^ 2 * DS.iQ η (wd q)| ≤
      2 * wd q * b := by
  have h := cm (fun δ => DS.arcSq η x q δ)
    (fun δ => DS.cQ q * x ^ 2 * ‖MajSp.mainFT η δ‖ ^ 2) (wd q) b (wd_nonneg q)
    (continuous_arcSq η x hs q) (continuous_const.mul ((continuous_mainFT η).norm.pow 2)) hb
  rw [intervalIntegral.integral_const_mul] at h
  exact h

/-- **`DS.ArcInt` FROM THE SPINE**: [Disjoint], [Cover], [Periodic] reduce `∫_𝔐 |S|²` to the arcs
(`reduce_of`); [ChangeVar] collects each modulus into `∫ arcSq` (`collect_of`); [Compare] prices
each modulus (`compare_of`); [Summation] sums. -/
theorem arcInt_of_links (dj : ArcsDisjoint) (cv : WindowCover) (ps : PeriodicShift)
    (ch : ChangeVar) (cm : ArcCompare) (su : Summation) (η : ℝ → ℝ) : DS.ArcInt η := by
  intro x hx hs errq herr
  have hx0 : 0 < x := x_pos hx
  exact su η x (fun q => ∫ δ in (-wd q)..(wd q), DS.arcSq η x q δ) errq hx0.ne'
    (amaj_eq η x _ (reduce_of dj cv ps x hx (sqS η x) (continuous_sqS η x hs) (sqS_periodic η x))
      (fun q _ => collect_of ch x hx0 η hs q))
    (fun q hq => compare_of cm η x hs q (errq q)
      (fun δ hδ => herr q (Qs_range hq).1 (Qs_range hq).2 δ hδ))

/-- **`DS.ArcInt η` for EVERY weight `η`** (`ternvin.tex` 1272–1315, `eq:juto`): the composition
fed by the five proved links. -/
theorem arcInt_all (η : ℝ → ℝ) : DS.ArcInt η :=
  arcInt_of_links arcsDisjoint windowCover periodicShift changeVar arcCompare summation η

/-- **`DS.ArcInt HW.etaPlus`**, Helfgott's `η₊`. -/
theorem arcInt_helf : DS.ArcInt HW.etaPlus := arcInt_all HW.etaPlus

/-! ## What the reduction says exactly (the adversarial pass)

`ArcInt` is an inequality; the reduction behind it is an EQUATION, and stating it shows the proof
does not pass through anything degenerate: `A_η(x)` is exactly the sum over the moduli of the
`δ`-integrals of `DS.arcSq`, and the index set is not empty (it contains the arc about `0/1`). -/

/-- **`A_η(x) = ∑_{q} ∫_{−wd q}^{wd q} arcSq(q,δ) dδ / x²`, EXACTLY**, for every summable weight. -/
theorem amaj_decomp (η : ℝ → ℝ) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x)
    (hs : Summable (fun n : ℕ => Λ n * |η ((n : ℝ) / x)|)) :
    MajSp.amaj η x = (∑ q ∈ Qs, ∫ δ in (-wd q)..(wd q), DS.arcSq η x q δ) / x ^ 2 :=
  amaj_eq η x _ (reduce_of arcsDisjoint windowCover periodicShift x hx (sqS η x)
    (continuous_sqS η x hs) (sqS_periodic η x))
    (fun q _ => collect_of changeVar x (x_pos hx) η hs q)

/-- The arc about `0/1` is one of `arcIdx`'s. -/
theorem zero_mem_arcIdx : (⟨1, 0⟩ : Σ _ : ℕ, ℕ) ∈ arcIdx :=
  mem_arcIdx.mpr ⟨Finset.mem_union_left _
    (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl 1, by norm_num⟩, odd_one⟩),
    Nat.one_pos, Nat.coprime_zero_left 1 |>.mpr rfl⟩

end Principia.Common.TernaryGoldbach.AI
