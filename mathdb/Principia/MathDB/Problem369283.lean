import Principia.MathDB.Problem369283Scalar

/-!
# MathDB #369283 — the generalized Cauchy–Schwarz inequality for real powers `p ≥ 2`

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/369283/solution.tex`, proving Conjecture 5.1 of Johnston, Plosker,
Torrance and Varona: for every `n`, real `p ≥ 2` and `v, w ∈ [0, ∞)ⁿ`,

`‖v^p‖ ‖w^p‖ − ⟨v^p, w^p⟩ ≤ ‖v‖^p ‖w‖^p − ⟨v, w⟩^p`

(entrywise powers, Euclidean norm and inner product).  `jptv` proves it for all nonnegative vectors
(the source asks for positive ones), including `n = 0`.

**Route (the write-up's, without the normalization).**  A *PSD triple* `(α, ξ, β)` has
`α, ξ, β ≥ 0` and `ξ² ≤ αβ` — an entrywise-nonnegative `2 × 2` positive semidefinite matrix.
`superadd` is the write-up's Lemma: `(F(α₁,α₂), F(ξ₁,ξ₂), F(β₁,β₂))` is a PSD triple, with
`F(u, v) = (u+v)^p − u^p − v^p`, from the scalar core `F_sq` and monotonicity.  Summing the triples
`(vᵢ², vᵢwᵢ, wᵢ²)` (`sum_triples`) gives `(c^p − d)² ≤ (X^p − A)(Y^p − B)` with `X = ‖v‖²`,
`A = ‖v^p‖²`, `c = ⟨v,w⟩`, `d = ⟨v^p,w^p⟩`, and the two-term Cauchy–Schwarz inequality
`√A√B + √(P−A)√(Q−B) ≤ √P√Q` (`two_term`) finishes, with no normalization of `v, w`.

**Absent:** the write-up's Tasks 2 onward (equality cases, exponents below 2).
-/

namespace Principia.MathDB.P369283

open Finset

/-- An entrywise-nonnegative `2 × 2` positive semidefinite matrix `[[α, ξ], [ξ, β]]`. -/
abbrev PSDT (α ξ β : ℝ) : Prop := 0 ≤ α ∧ 0 ≤ ξ ∧ 0 ≤ β ∧ ξ ^ 2 ≤ α * β

/-- The generalized Cauchy–Schwarz inequality for real powers (Conjecture 5.1 of JPTV). -/
def JPTVConj : Prop :=
  ∀ (n : ℕ) (p : ℝ), 2 ≤ p → ∀ v w : Fin n → ℝ, (∀ i, 0 ≤ v i) → (∀ i, 0 ≤ w i) →
    Real.sqrt (∑ i, (v i ^ p) ^ 2) * Real.sqrt (∑ i, (w i ^ p) ^ 2) - ∑ i, v i ^ p * w i ^ p
      ≤ Real.sqrt (∑ i, v i ^ 2) ^ p * Real.sqrt (∑ i, w i ^ 2) ^ p - (∑ i, v i * w i) ^ p

theorem F_zero_left (p v : ℝ) (hp : 2 ≤ p) : F p 0 v = 0 := by
  simp [F, Real.zero_rpow (by linarith : p ≠ 0)]

theorem F_nonneg (p u v : ℝ) (hp : 2 ≤ p) (hu : 0 ≤ u) (hv : 0 ≤ v) : 0 ≤ F p u v := by
  have := F_mono_left p 0 u v hp le_rfl hu hv
  rwa [F_zero_left p v hp] at this

theorem F_symm (p u v : ℝ) : F p u v = F p v u := by
  unfold F
  rw [add_comm]
  ring

theorem PSDT.add {α ξ β α' ξ' β' : ℝ} (h : PSDT α ξ β) (h' : PSDT α' ξ' β') :
    PSDT (α + α') (ξ + ξ') (β + β') := by
  obtain ⟨ha, hx, hb, hs⟩ := h
  obtain ⟨ha', hx', hb', hs'⟩ := h'
  refine ⟨add_nonneg ha ha', add_nonneg hx hx', add_nonneg hb hb', ?_⟩
  have hcross : 2 * (ξ * ξ') ≤ α * β' + α' * β := by
    have h4 : (2 * (ξ * ξ')) ^ 2 ≤ (α * β' + α' * β) ^ 2 := by
      have hm : (ξ * ξ') ^ 2 ≤ (α * β) * (α' * β') := by
        rw [mul_pow]
        exact mul_le_mul hs hs' (sq_nonneg _) (mul_nonneg ha hb)
      nlinarith [sq_nonneg (α * β' - α' * β)]
    nlinarith [mul_nonneg hx hx', mul_nonneg ha hb', mul_nonneg ha' hb]
  nlinarith

/-- **The write-up's Lemma** (`2 × 2` superadditivity of entrywise powers `p ≥ 2`). -/
theorem superadd (p : ℝ) (hp : 2 ≤ p) {α1 ξ1 β1 α2 ξ2 β2 : ℝ} (h1 : PSDT α1 ξ1 β1)
    (h2 : PSDT α2 ξ2 β2) : PSDT (F p α1 α2) (F p ξ1 ξ2) (F p β1 β2) := by
  obtain ⟨ha1, hx1, hb1, hs1⟩ := h1
  obtain ⟨ha2, hx2, hb2, hs2⟩ := h2
  have hle1 : ξ1 ≤ Real.sqrt (α1 * β1) := by
    have := Real.abs_le_sqrt hs1
    rwa [abs_of_nonneg hx1] at this
  have hle2 : ξ2 ≤ Real.sqrt (α2 * β2) := by
    have := Real.abs_le_sqrt hs2
    rwa [abs_of_nonneg hx2] at this
  have hmono : F p ξ1 ξ2 ≤ F p (Real.sqrt (α1 * β1)) (Real.sqrt (α2 * β2)) := by
    calc F p ξ1 ξ2 ≤ F p (Real.sqrt (α1 * β1)) ξ2 := F_mono_left p _ _ _ hp hx1 hle1 hx2
      _ = F p ξ2 (Real.sqrt (α1 * β1)) := F_symm _ _ _
      _ ≤ F p (Real.sqrt (α2 * β2)) (Real.sqrt (α1 * β1)) :=
          F_mono_left p _ _ _ hp hx2 hle2 (Real.sqrt_nonneg _)
      _ = F p (Real.sqrt (α1 * β1)) (Real.sqrt (α2 * β2)) := F_symm _ _ _
  have hsq := F_sq p α1 β1 α2 β2 hp ha1 hb1 ha2 hb2
  have hF0 := F_nonneg p ξ1 ξ2 hp hx1 hx2
  refine ⟨F_nonneg p _ _ hp ha1 ha2, hF0, F_nonneg p _ _ hp hb1 hb2, ?_⟩
  exact (pow_le_pow_left₀ hF0 hmono 2).trans hsq

/-- Summing PSD triples: the sums and the "power defects" are PSD triples. -/
theorem sum_triples (p : ℝ) (hp : 2 ≤ p) {ι : Type*} [DecidableEq ι] (α ξ β : ι → ℝ)
    (h : ∀ i, PSDT (α i) (ξ i) (β i)) (s : Finset ι) :
    PSDT (∑ i ∈ s, α i) (∑ i ∈ s, ξ i) (∑ i ∈ s, β i) ∧
      PSDT ((∑ i ∈ s, α i) ^ p - ∑ i ∈ s, α i ^ p) ((∑ i ∈ s, ξ i) ^ p - ∑ i ∈ s, ξ i ^ p)
        ((∑ i ∈ s, β i) ^ p - ∑ i ∈ s, β i ^ p) := by
  have hp0 : p ≠ 0 := by linarith
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty, Real.zero_rpow hp0, sub_zero]
    exact ⟨⟨le_rfl, le_rfl, le_rfl, by norm_num⟩, ⟨le_rfl, le_rfl, le_rfl, by norm_num⟩⟩
  | insert a s ha ih =>
    obtain ⟨hS, hD⟩ := ih
    simp only [sum_insert ha]
    refine ⟨(h a).add hS, ?_⟩
    have hF := superadd p hp (h a) hS
    have e : ∀ x : ι → ℝ, (x a + ∑ i ∈ s, x i) ^ p - (x a ^ p + ∑ i ∈ s, x i ^ p)
        = F p (x a) (∑ i ∈ s, x i) + ((∑ i ∈ s, x i) ^ p - ∑ i ∈ s, x i ^ p) := by
      intro x
      unfold F
      ring
    rw [e α, e ξ, e β]
    exact hF.add hD

/-- `√A√B + √(P−A)√(Q−B) ≤ √P√Q` for `0 ≤ A ≤ P`, `0 ≤ B ≤ Q`. -/
theorem two_term (A B P Q : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hAP : A ≤ P) (hBQ : B ≤ Q) :
    Real.sqrt A * Real.sqrt B + Real.sqrt (P - A) * Real.sqrt (Q - B)
      ≤ Real.sqrt P * Real.sqrt Q := by
  have hPA : 0 ≤ P - A := by linarith
  have hQB : 0 ≤ Q - B := by linarith
  have ha := Real.sq_sqrt hA
  have hb := Real.sq_sqrt hB
  have ha' := Real.sq_sqrt hPA
  have hb' := Real.sq_sqrt hQB
  rw [← Real.sqrt_mul (show 0 ≤ P by linarith) Q]
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  have e : (Real.sqrt A * Real.sqrt B + Real.sqrt (P - A) * Real.sqrt (Q - B)) ^ 2
      + (Real.sqrt A * Real.sqrt (Q - B) - Real.sqrt (P - A) * Real.sqrt B) ^ 2
      = (Real.sqrt A ^ 2 + Real.sqrt (P - A) ^ 2) * (Real.sqrt B ^ 2 + Real.sqrt (Q - B) ^ 2) := by
    ring
  rw [ha, hb, ha', hb'] at e
  nlinarith [e, sq_nonneg (Real.sqrt A * Real.sqrt (Q - B) - Real.sqrt (P - A) * Real.sqrt B)]

theorem rpow_sq (x p : ℝ) (hx : 0 ≤ x) : (x ^ 2) ^ p = (x ^ p) ^ 2 := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx, mul_comm, Real.rpow_mul hx,
    Real.rpow_natCast]

theorem sqrt_rpow (x p : ℝ) (hx : 0 ≤ x) : Real.sqrt (x ^ p) = Real.sqrt x ^ p := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx, ← Real.rpow_mul hx, mul_comm]

/-- **MathDB #369283: Conjecture 5.1 of Johnston–Plosker–Torrance–Varona holds** for every real
`p ≥ 2` and all nonnegative vectors. -/
theorem jptv : JPTVConj := by
  intro n p hp v w hv hw
  have hT : ∀ i, PSDT (v i ^ 2) (v i * w i) (w i ^ 2) := fun i =>
    ⟨sq_nonneg _, mul_nonneg (hv i) (hw i), sq_nonneg _, le_of_eq (mul_pow _ _ _)⟩
  obtain ⟨_, hD⟩ := sum_triples p hp (fun i => v i ^ 2) (fun i => v i * w i) (fun i => w i ^ 2)
    hT univ
  try simp only at hD
  have eA : ∑ i, (v i ^ 2) ^ p = ∑ i, (v i ^ p) ^ 2 :=
    sum_congr rfl fun i _ => rpow_sq (v i) p (hv i)
  have eB : ∑ i, (w i ^ 2) ^ p = ∑ i, (w i ^ p) ^ 2 :=
    sum_congr rfl fun i _ => rpow_sq (w i) p (hw i)
  have eD : ∑ i, (v i * w i) ^ p = ∑ i, v i ^ p * w i ^ p :=
    sum_congr rfl fun i _ => Real.mul_rpow (hv i) (hw i)
  rw [eA, eB, eD] at hD
  obtain ⟨hPA, hcd, hQB, hsq⟩ := hD
  set X := ∑ i, v i ^ 2
  set Y := ∑ i, w i ^ 2
  set A := ∑ i, (v i ^ p) ^ 2
  set B := ∑ i, (w i ^ p) ^ 2
  set c := ∑ i, v i * w i
  set d := ∑ i, v i ^ p * w i ^ p
  have hX0 : 0 ≤ X := sum_nonneg fun i _ => sq_nonneg _
  have hY0 : 0 ≤ Y := sum_nonneg fun i _ => sq_nonneg _
  have hA0 : 0 ≤ A := sum_nonneg fun i _ => sq_nonneg _
  have hB0 : 0 ≤ B := sum_nonneg fun i _ => sq_nonneg _
  have h1 : c ^ p - d ≤ Real.sqrt (X ^ p - A) * Real.sqrt (Y ^ p - B) := by
    rw [← Real.sqrt_mul hPA]
    have := Real.abs_le_sqrt hsq
    rwa [abs_of_nonneg hcd] at this
  have h2 := two_term A B (X ^ p) (Y ^ p) hA0 hB0 (by linarith) (by linarith)
  rw [sqrt_rpow X p hX0, sqrt_rpow Y p hY0] at h2
  linarith

end Principia.MathDB.P369283
