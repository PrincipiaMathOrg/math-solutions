import Mathlib

set_option autoImplicit false

namespace Principia.MathDB.P323297

/-- `B n k = C(n,k)·C(n+k,k)`, the array in Guo–Zeng's defining equation. -/
def B (n k : ℕ) : ℕ := n.choose k * (n + k).choose k

/-- **THE KEY DIVISIBILITY.**  `p ∣ B (p−2) k` for `2 ≤ k ≤ p−2`.  The write-up argues that
`C(p−2+k, k) = (p−1)p(p+1)⋯(p−2+k)/k!` has one factor `p` upstairs and none downstairs; in Mathlib
this is `Nat.Prime.dvd_choose_add` after one `choose_symm` step, with no valuation computation. -/
theorem p_dvd_B {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk2 : 2 ≤ k) (hkp : k ≤ p - 2) :
    p ∣ B (p - 2) k := by
  have h := hp.dvd_choose_add (a := p - 2) (b := k) (by omega) (by omega) (by omega)
  have e : ((p - 2) + k) - k = p - 2 := by omega
  have hs := Nat.choose_symm (n := (p - 2) + k) (k := k) (by omega)
  rw [e] at hs
  rw [hs] at h
  exact Dvd.dvd.mul_left h _

/-! ### The base index `a = B (p−2) 1` -/

/-- `a = (p−2)(p−1) = 2 − 3p + p²`, exactly as the write-up computes it. -/
theorem a_eq (p : ℤ) : (p - 2) * (p - 1) = 2 - 3 * p + p ^ 2 := by ring

/-- `a ≡ 2 (mod p)`, in the cleared form the next step uses. -/
theorem a_sub_two (p : ℤ) : (p - 2) * (p - 1) - 2 = p * (p - 3) := by ring

/-- Hence `p ∤ a`, because `p ≥ 5` does not divide `2`. -/
theorem not_dvd_a {p : ℤ} (hp5 : 5 ≤ p) : ¬ p ∣ (p - 2) * (p - 1) := by
  intro h
  have hd : p ∣ (p - 2) * (p - 1) - 2 := by
    rw [a_sub_two]; exact dvd_mul_right p (p - 3)
  have e : (p - 2) * (p - 1) - ((p - 2) * (p - 1) - 2) = 2 := by ring
  have h2 : p ∣ (2 : ℤ) := by
    have := dvd_sub h hd
    rwa [e] at this
  have := Int.le_of_dvd (by norm_num) h2
  omega

/-! ### The first-order coefficient is invertible mod `p` -/

/-- `−3·d·2^{d−1}` is nonzero mod `p` when `p ≥ 5` is prime and `p ∤ d`.  This is what makes
`a^d − 2^d` divisible by `p` but not by `p²`. -/
theorem coeff_not_dvd {p d : ℤ} {e : ℕ} (hp : Prime p) (hp5 : 5 ≤ p) (hd : ¬ p ∣ d) :
    ¬ p ∣ (-3 * d * 2 ^ e) := by
  intro h
  rcases (hp.dvd_mul.mp h) with h1 | h2
  · rcases (hp.dvd_mul.mp h1) with h3 | h4
    · have := Int.le_of_dvd (by norm_num) ((dvd_neg).mp h3)
      omega
    · exact hd h4
  · have := hp.dvd_of_dvd_pow h2
    have := Int.le_of_dvd (by norm_num) this
    omega

/-! ### The valuation step, which is the engine of the theorem -/

/-- **From `p^s ∣ D·a^s·w` with `p ∤ a`, `p ∣ w` and `p² ∤ w`, conclude `p^(s−1) ∣ D`.**  This is
the write-up's closing inference, and it is where `r > s` has already been used to discard the
`p^r` term. -/
theorem valuation_step {p D a w : ℤ} {s : ℕ} (hp : Prime p) (hs : 1 ≤ s)
    (hdvd : p ^ s ∣ D * a ^ s * w) (ha : ¬ p ∣ a) (hw : p ∣ w) (hw2 : ¬ p ^ 2 ∣ w) :
    p ^ (s - 1) ∣ D := by
  obtain ⟨w', rfl⟩ := hw
  have hw' : ¬ p ∣ w' := by
    intro h
    obtain ⟨t, rfl⟩ := h
    exact hw2 ⟨t, by ring⟩
  have hcop : IsCoprime p a := (hp.coprime_iff_not_dvd).mpr ha
  have hcops : IsCoprime (p ^ s) (a ^ s) := hcop.pow
  have h1 : p ^ s ∣ D * w' * p := by
    have : D * a ^ s * (p * w') = (D * w' * p) * a ^ s := by ring
    rw [this] at hdvd
    exact (IsCoprime.dvd_of_dvd_mul_right hcops hdvd)
  have hps : p ^ s = p ^ (s - 1) * p := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hps] at h1
  have h2 : p ^ (s - 1) ∣ D * w' := by
    exact (mul_dvd_mul_iff_right (hp.ne_zero)).mp h1
  have hcop' : IsCoprime (p ^ (s - 1)) w' := ((hp.coprime_iff_not_dvd).mpr hw').pow_left
  exact hcop'.dvd_of_dvd_mul_right h2

end Principia.MathDB.P323297
