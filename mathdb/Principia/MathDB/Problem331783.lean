import Mathlib

set_option autoImplicit false

namespace Principia.MathDB.P331783

/-! ### The recurrence collapses when `β = 0` -/

/-- One step of `z_{n+1} = (α + α z_n + β z_{n−1})/(1 + z_n)`. -/
noncomputable def step (α β zprev zcur : ℂ) : ℂ := (α + α * zcur + β * zprev) / (1 + zcur)

/-- **THE COLLAPSE.**  At `β = 0` the numerator is `α(1 + z_n)`, so the step is the constant `α`
wherever the source's own denominator is nonzero. -/
theorem step_eq_of_beta_zero (α zprev zcur : ℂ) (h : 1 + zcur ≠ 0) :
    step α 0 zprev zcur = α := by
  unfold step
  field_simp
  ring

/-- A forward solution: everywhere-defined, satisfying the recurrence. -/
def IsSolution (α β : ℂ) (z : ℕ → ℂ) : Prop :=
  (∀ n, 1 + z (n + 1) ≠ 0) ∧ ∀ n, z (n + 2) = step α β (z n) (z (n + 1))

/-- **Every solution is constant from index two on**, when `β = 0`. -/
theorem solution_const (α : ℂ) (z : ℕ → ℂ) (hz : IsSolution α 0 z) :
    ∀ n, z (n + 2) = α := by
  obtain ⟨hden, hrec⟩ := hz
  intro n
  rw [hrec n, step_eq_of_beta_zero α (z n) (z (n + 1)) (hden n)]

/-- Hence every solution is eventually constant. -/
theorem solution_eventually_const (α : ℂ) (z : ℕ → ℂ) (hz : IsSolution α 0 z) :
    ∃ N c, ∀ n, N ≤ n → z n = c := by
  refine ⟨2, α, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact solution_const α z hz m

/-! ### The state-space map has a constant second iterate -/

/-- `F(x, y) = (y, α)`, the state map at `β = 0`. -/
def F (α : ℂ) : ℂ × ℂ → ℂ × ℂ := fun p => (p.2, α)

theorem F_sq (α : ℂ) (p : ℂ × ℂ) : F α (F α p) = (α, α) := rfl

/-- **Any two forward orbits agree exactly from step two on** — so there is no persistent
separation of nearby orbits and no Li–Yorke scrambled pair. -/
theorem orbits_agree (α : ℂ) (p q : ℂ × ℂ) (n : ℕ) (hn : 2 ≤ n) :
    (F α)^[n] p = (F α)^[n] q := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [Function.iterate_add_apply, Function.iterate_add_apply]
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
  rw [F_sq, F_sq]

/-! ### The conjecture and its refutation -/

/-- Hassan **Conjecture 5.1** (p. 13), forward direction, with *chaotic* replaced by the weakest
thing every notion of chaos implies: some everywhere-defined solution is **not** eventually
constant.  Refuting this weaker statement refutes the printed one a fortiori. -/
def Conjecture51 : Prop :=
  ∀ α β : ℂ, ‖β‖ < ‖α + 1‖ →
    ∃ z : ℕ → ℂ, IsSolution α β z ∧ ¬ ∃ N c, ∀ n, N ≤ n → z n = c

/-- **THE CONJECTURE IS FALSE**, at `α = i`, `β = 0`: the strict inequality holds because
`‖1 + i‖ = √2 > 0`, yet every admissible solution equals `i` from index two on. -/
theorem conjecture51_false : ¬ Conjecture51 := by
  intro h
  have hlt : ‖(0 : ℂ)‖ < ‖Complex.I + 1‖ := by
    rw [norm_zero]
    have : ‖Complex.I + 1‖ ^ 2 = 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq_apply]
      ring
    nlinarith [norm_nonneg (Complex.I + 1), this]
  obtain ⟨z, hz, hnc⟩ := h Complex.I 0 hlt
  exact hnc (solution_eventually_const Complex.I z hz)

end Principia.MathDB.P331783
