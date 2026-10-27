import Mathlib

set_option autoImplicit false

namespace Principia.MathDB.P333489

/-- The parameter, `α = β = γ = τ = −2/3`. -/
noncomputable def tau : ℂ := -2 / 3

/-- The three-cycle `0, −1, −2`, indexed by `ℤ` so the delayed entry needs no truncated
subtraction. -/
noncomputable def z (n : ℤ) : ℂ := if n % 3 = 0 then 0 else if n % 3 = 1 then -1 else -2

theorem z_congr {a b : ℤ} (h : a % 3 = b % 3) : z a = z b := by
  simp only [z, h]

theorem z_zero : z 0 = 0 := by norm_num [z]
theorem z_one : z 1 = -1 := by norm_num [z]
theorem z_two : z 2 = -2 := by norm_num [z]

theorem z_periodic (n : ℤ) : z (n + 3) = z n := z_congr (by omega)

/-- Every denominator is nonzero: `τ − z n` is `−2/3`, `1/3` or `4/3`. -/
theorem denom_ne_zero (n : ℤ) : tau - z n ≠ 0 := by
  have h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  simp only [z, tau]
  rcases h with h | h | h <;> simp only [h] <;> norm_num

/-- **The three-cycle solves the recurrence**, for every delay `k ≡ 1 (mod 3)`. -/
theorem recurrence (k : ℤ) (hk : k % 3 = 1) (n : ℤ) :
    z (n + 1) = tau * (1 + z (n - k)) / (tau - z n) := by
  have hshift : z (n - k) = z (n - 1) := z_congr (by omega)
  have h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rw [hshift]
  rcases h with h | h | h
  · rw [z_congr (show (n + 1) % 3 = 1 % 3 by omega),
      z_congr (show (n - 1) % 3 = 2 % 3 by omega), z_congr (show n % 3 = 0 % 3 by omega)]
    norm_num [z, tau]
  · rw [z_congr (show (n + 1) % 3 = 2 % 3 by omega),
      z_congr (show (n - 1) % 3 = 0 % 3 by omega), z_congr (show n % 3 = 1 % 3 by omega)]
    norm_num [z, tau]
  · rw [z_congr (show (n + 1) % 3 = 0 % 3 by omega),
      z_congr (show (n - 1) % 3 = 1 % 3 by omega), z_congr (show n % 3 = 2 % 3 by omega)]
    norm_num [z, tau]

/-- A shift is a period **iff** it is divisible by three: the three entries are distinct. -/
theorem period_iff (p : ℤ) : (∀ n, z (n + p) = z n) ↔ 3 ∣ p := by
  constructor
  · intro h
    by_contra hp
    have h1 : p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases h1 with hc | hc
    · have := h 0
      rw [z_congr (show (0 + p) % 3 = 1 % 3 by omega)] at this
      rw [z_one, z_zero] at this
      norm_num at this
    · have := h 0
      rw [z_congr (show (0 + p) % 3 = 2 % 3 by omega)] at this
      rw [z_two, z_zero] at this
      norm_num at this
  · rintro ⟨c, rfl⟩ n
    exact z_congr (by omega)

/-- **`k + 3` is not a period**, because `k + 3 ≡ 1 (mod 3)`. -/
theorem not_period (k : ℤ) (hk : k % 3 = 1) : ¬ ∀ n, z (n + (k + 3)) = z n := by
  rw [period_iff]
  omega

/-! ## The conjecture, and its refutation -/

/-- Hassan Conjecture 3.2 in the equal-parameter case: for every delay `k ≥ 1`, every nonconstant
everywhere-defined solution of `z_{n+1} = τ(1 + z_{n−k})/(τ − z_n)` has `k + 3` as a period. -/
def Conjecture32 : Prop :=
  ∀ (k : ℤ), 1 ≤ k → ∀ (τ : ℂ) (w : ℤ → ℂ), τ ≠ 0 → (∀ n, τ - w n ≠ 0) →
    (∀ n, w (n + 1) = τ * (1 + w (n - k)) / (τ - w n)) →
    (¬ ∃ c, ∀ n, w n = c) → ∀ n, w (n + (k + 3)) = w n

/-- **THE CONJECTURE IS FALSE.**  At delay `k = 1` the three-cycle `0, −1, −2` with `τ = −2/3` is
an everywhere-defined nonconstant solution of least period three, and `4` is not a period of it. -/
theorem conjecture32_false : ¬ Conjecture32 := by
  intro h
  have htau : tau ≠ 0 := by norm_num [tau]
  have hnonconst : ¬ ∃ c, ∀ n, z n = c := by
    rintro ⟨c, hc⟩
    have h0 := hc 0
    have h1 := hc 1
    rw [z_zero] at h0
    rw [z_one] at h1
    rw [← h0] at h1
    norm_num at h1
  exact not_period 1 (by norm_num)
    (h 1 le_rfl tau z htau denom_ne_zero (recurrence 1 (by norm_num)) hnonconst)

end Principia.MathDB.P333489
