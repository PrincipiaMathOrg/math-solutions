import Mathlib

/-!
# MathDB #355408 — Maier's Bessel-number formula for generalized Eulerian triangles

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/355408/solution.tex`, proving Conjecture 4.20 of R. S. Maier,
*Triangular recurrences, generalized Eulerian numbers, and related number triangles* (Adv. Appl.
Math. 146 (2023) 102485, arXiv:2207.10224v2, Definitions 4.4, 4.6 and Conjecture 4.20, p. 44).

Everything lives in ONE module on purpose: each module costs about fifteen minutes of Mathlib
loading on the verification runner, and the row needs more pieces than a ninety-minute job can
afford as separate files.

**The chain.**
* `Eg` is the generalized Eulerian triangle of the write-up's (1); `rise` and `step` are
  `(x)_n = x(x+1)⋯(x+n−1)` and `x(x+2)⋯(x+2n−2)`.
* `spine`: any `H` obeying the write-up's (7) with the right apex gives
  `E_{n,k}(−1,2;c+m,m) = q (c+m)_n H_{n,k}` — the shape of (2).
* `Sg` is the generalized Stirling triangle and `Sg_diag` its diagonal closed form
  `S_{2ℓ+t,ℓ+t}(1,2;0) · 2^ℓ ℓ! t! = (2ℓ+t)!`, the first half of the write-up's (3), proved in the
  parametrization `m = 2ℓ + t` so that no natural subtraction occurs.
* `aa_rec` and `aa_shift` are the coefficient facts behind the write-up's (5) and (6); `Pk_ode`
  and `Pk_contig` are those identities themselves, the first by the telescoping
  `uu (ℓ+1) = vv ℓ` with `uu 0 = 0` and `vv p = 0` (the latter because `ζ ≤ 1`).
* `apex` is the write-up's (9) — `P_0(1) = q⁻¹` — proved WITHOUT Chu–Vandermonde: the sum obeys
  a `c`-shift recurrence which, after clearing the step-two denominators, is a Pascal relation
  (`Bt_rec`) plus a telescoping.
* `Qk_ode`, `Qk_contig` transport (5) and (6) to the variable `z` of the write-up's (8), and the
  coefficient-move lemmas (`coeff_deriv_move`, `coeff_deriv_move2`, `coeff_shift_up`) are what
  that computation runs on.

Checked in SymPy before formalizing: the identity itself (90 cases, `p ≤ 2`, `ζ ∈ {0,1}`,
`n ≤ 4`), both closed forms of (3), the two coefficient relations (128 cases), the apex and its
recurrence, the Pascal relation, and the `K + L = 0` cancellation of (8).

**Absent:** the write-up's (7) itself, hence the final assembly, and its Tasks 2–5.
-/

namespace Principia.MathDB.P355408

open Finset Polynomial

variable {K : Type*} [Field K] [CharZero K]

/- ### Spine -/

/-- The rising factorial `(x)_n = x(x+1)⋯(x+n−1)`. -/
def rise (x : K) : ℕ → K
  | 0 => 1
  | n + 1 => rise x n * (x + n)

/-- The step-two factorial `x(x+2)⋯(x+2n−2)`. -/
def step (x : K) : ℕ → K
  | 0 => 1
  | n + 1 => step x n * (x + 2 * n)

theorem rise_succ (x : K) (n : ℕ) : rise x (n + 1) = rise x n * (x + n) := rfl

theorem step_succ (x : K) (n : ℕ) : step x (n + 1) = step x n * (x + 2 * n) := rfl

/-- The generalized Eulerian triangle, the write-up's (1). -/
def Eg (a b c0 cinf : K) : ℕ → ℕ → K
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => (-a * n + c0) * Eg a b c0 cinf n 0
  | n + 1, k + 1 => (-a * n + b * (k + 1) + c0) * Eg a b c0 cinf n (k + 1)
      + ((a + b) * n - b * k + cinf) * Eg a b c0 cinf n k

theorem Eg_succ_zero (a b c0 cinf : K) (n : ℕ) :
    Eg a b c0 cinf (n + 1) 0 = (-a * n + c0) * Eg a b c0 cinf n 0 := rfl

theorem Eg_succ_succ (a b c0 cinf : K) (n k : ℕ) :
    Eg a b c0 cinf (n + 1) (k + 1) = (-a * n + b * (k + 1) + c0) * Eg a b c0 cinf n (k + 1)
      + ((a + b) * n - b * k + cinf) * Eg a b c0 cinf n k := rfl

/-- **The spine.**  Any solution of the write-up's (7), normalized at the apex, is the generalized
Eulerian triangle at `(a,b,c₀,c_∞) = (−1,2,c+m,m)`, scaled by `q (c+m)_n`. -/
theorem spine (c m q : K) (H : ℕ → ℕ → K)
    (hvan : ∀ k, H 0 (k + 1) = 0)
    (hH0 : ∀ n : ℕ, H (n + 1) 0 = H n 0)
    (hH : ∀ n k : ℕ, ((n : K) + c + m) * H (n + 1) (k + 1)
      = ((n : K) + 2 * (k + 1) + c + m) * H n (k + 1)
        + ((n : K) - 2 * (k + 1) + 2 + m) * H n k)
    (hApex : q * H 0 0 = 1) :
    ∀ n k : ℕ, Eg (-1 : K) 2 (c + m) m n k = q * rise (c + m) n * H n k := by
  intro n
  induction n with
  | zero =>
    intro k
    rcases k with _ | k
    · show (1 : K) = q * rise (c + m) 0 * H 0 0
      rw [show rise (c + m) 0 = 1 from rfl, mul_one]
      exact hApex.symm
    · show (0 : K) = q * rise (c + m) 0 * H 0 (k + 1)
      rw [hvan k, mul_zero]
  | succ n ih =>
    intro k
    rw [rise_succ]
    rcases k with _ | k
    · rw [Eg_succ_zero, ih 0, hH0 n]
      ring
    · rw [Eg_succ_succ, ih (k + 1), ih k]
      have h := hH n k
      have hq : q * (rise (c + m) n * (c + m + n)) * H (n + 1) (k + 1)
          = q * rise (c + m) n * (((n : K) + c + m) * H (n + 1) (k + 1)) := by ring
      rw [hq, h]
      push_cast
      ring

/- ### Stirling -/

/-- The generalized Stirling triangle `S_{n,j}(a,b;r)` of the write-up. -/
def Sg (a b r : K) : ℕ → ℕ → K
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => (-a * n + r) * Sg a b r n 0
  | n + 1, k + 1 => (-a * n + b * (k + 1) + r) * Sg a b r n (k + 1) + Sg a b r n k

theorem Sg_succ_zero (a b r : K) (n : ℕ) :
    Sg a b r (n + 1) 0 = (-a * n + r) * Sg a b r n 0 := rfl

theorem Sg_succ_succ (a b r : K) (n k : ℕ) :
    Sg a b r (n + 1) (k + 1)
      = (-a * n + b * (k + 1) + r) * Sg a b r n (k + 1) + Sg a b r n k := rfl

theorem Sg_eq_zero (a b r : K) (n k : ℕ) (h : n < k) : Sg a b r n k = 0 := by
  induction n generalizing k with
  | zero =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rfl
  | succ n ih =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Sg_succ_succ, ih (k + 1) (by omega), ih k (by omega)]
    ring

/-- The apex of the diagonal: `S_{n,n}(1,2;0) = 1`. -/
theorem Sg_diag_top (n : ℕ) : Sg (1 : K) 2 0 n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Sg_succ_succ, Sg_eq_zero (1 : K) 2 0 n (n + 1) (by omega), ih]
    ring

/-- Below the diagonal band the entries vanish: `S_{n,j}(1,2;0) = 0` when `2j < n`. -/
theorem Sg_lo (n j : ℕ) (h : 2 * j < n) : Sg (1 : K) 2 0 n j = 0 := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    rcases j with _ | j
    · rw [Sg_succ_zero]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · norm_num
      · rw [ih 0 (by omega)]
        ring
    · rcases Nat.lt_or_ge (2 * (j + 1)) n with hlt | hge
      · rw [Sg_succ_succ, ih (j + 1) hlt, ih j (by omega)]
        ring
      · have hn : n = 2 * (j + 1) := by omega
        rw [Sg_succ_succ, ih j (by omega), hn]
        push_cast
        ring

/-- **The write-up's `B_{m,m−ℓ} = m!/(2^ℓ ℓ!(m−2ℓ)!)`**, denominator-free, at `m = 2ℓ + t`. -/
theorem Sg_diag (l t : ℕ) :
    Sg (1 : K) 2 0 (2 * l + t) (l + t) * (2 ^ l * (l.factorial : K) * (t.factorial : K))
      = ((2 * l + t).factorial : K) := by
  suffices H : ∀ m l t : ℕ, 2 * l + t = m →
      Sg (1 : K) 2 0 (2 * l + t) (l + t) * (2 ^ l * (l.factorial : K) * (t.factorial : K))
        = ((2 * l + t).factorial : K) from H _ l t rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro l t hm
    match l, t with
    | 0, t => simp [Sg_diag_top]
    | l + 1, 0 =>
      -- `m = 2l + 2`: the lower neighbour vanishes, the upper is the `(l, 1)` case
      have e1 := ih (2 * l + 1) (by omega) l 1 rfl
      have hz := Sg_lo (K := K) (2 * l + 1) l (by omega)
      have hf1 : (((1 : ℕ).factorial : ℕ) : K) = 1 := by norm_num
      have hfl : (((l + 1).factorial : ℕ) : K) = ((l : K) + 1) * (l.factorial : K) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have hfM : (((2 * l + 1 + 1).factorial : ℕ) : K)
          = (2 * (l : K) + 2) * (((2 * l + 1).factorial : ℕ) : K) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [show 2 * (l + 1) + 0 = 2 * l + 1 + 1 by ring, show l + 1 + 0 = l + 1 by ring,
        Sg_succ_succ, hz, hfM, hfl, pow_succ]
      rw [hf1] at e1
      push_cast at e1 ⊢
      linear_combination (2 * (l : K) + 2) * e1
    | l + 1, t + 1 =>
      -- `m = 2l + t + 3`: both neighbours sit at `2l + t + 2`
      have e1 := ih (2 * l + (t + 2)) (by omega) l (t + 2) rfl
      have e2 := ih (2 * (l + 1) + t) (by omega) (l + 1) t rfl
      rw [show 2 * l + (t + 2) = 2 * l + t + 2 by ring,
        show l + (t + 2) = l + t + 2 by ring] at e1
      rw [show 2 * (l + 1) + t = 2 * l + t + 2 by ring,
        show l + 1 + t = l + t + 1 by ring] at e2
      have hfl : (((l + 1).factorial : ℕ) : K) = ((l : K) + 1) * (l.factorial : K) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have hft1 : (((t + 1).factorial : ℕ) : K) = ((t : K) + 1) * (t.factorial : K) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have hft2 : (((t + 2).factorial : ℕ) : K)
          = ((t : K) + 2) * (((t + 1).factorial : ℕ) : K) := by
        rw [show t + 2 = (t + 1) + 1 from rfl, Nat.factorial_succ]
        push_cast
        ring
      have hfM : (((2 * l + t + 2 + 1).factorial : ℕ) : K)
          = (2 * (l : K) + t + 3) * (((2 * l + t + 2).factorial : ℕ) : K) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [show 2 * (l + 1) + (t + 1) = 2 * l + t + 2 + 1 by ring,
        show l + 1 + (t + 1) = l + t + 1 + 1 by ring, Sg_succ_succ,
        show l + t + 1 + 1 = l + t + 2 by ring, hfM, hfl, hft1, pow_succ]
      rw [hft2, hft1] at e1
      rw [hfl] at e2
      push_cast at e1 e2 ⊢
      linear_combination (2 * (l : K) + 2) * e1 + ((t : K) + 1) * e2

theorem coeff_mul_derivative (h p : K[X]) (k : ℕ) :
    (h * derivative p).coeff k
      = ((k : K) + 1) * (h * p).coeff (k + 1) - (derivative h * p).coeff k := by
  have hd : (derivative (h * p)).coeff k = (h * p).coeff (k + 1) * ((k : K) + 1) := by
    rw [coeff_derivative]
  rw [derivative_mul, coeff_add] at hd
  linear_combination hd

/- ### Coeff -/

/-- `B_{m,m−ℓ}` in closed form, at `m = 2p + ζ`. -/
def Bc (p zeta l : ℕ) : K :=
  ((2 * p + zeta).factorial : K)
    / (2 ^ l * (l.factorial : K) * ((2 * (p - l) + zeta).factorial : K))

theorem factorial_ne_zero (n : ℕ) : ((n.factorial : ℕ) : K) ≠ 0 :=
  Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)

/-- `Bc` is the diagonal entry of the Stirling triangle, the write-up's `B_{m,m−ℓ}`. -/
theorem Bc_eq_Sg (p zeta l : ℕ) (hl : l ≤ p) :
    Sg (1 : K) 2 0 (2 * p + zeta) (2 * p + zeta - l) = Bc p zeta l := by
  have h := Sg_diag (K := K) l (2 * (p - l) + zeta)
  have h1 : 2 * l + (2 * (p - l) + zeta) = 2 * p + zeta := by omega
  have h2 : l + (2 * (p - l) + zeta) = 2 * p + zeta - l := by omega
  rw [h1, h2] at h
  rw [Bc, eq_div_iff (by
    have h2' : (2 : K) ^ l ≠ 0 := pow_ne_zero l (by norm_num)
    exact mul_ne_zero (mul_ne_zero h2' (factorial_ne_zero l))
      (factorial_ne_zero (2 * (p - l) + zeta)))]
  exact h

/-- Each factor of `step` is nonzero when every `step` is. -/
theorem step_factor_ne_zero (c : K) (j : ℕ) (hs : ∀ i : ℕ, step (c + 1) i ≠ 0) :
    c + 1 + 2 * (j : K) ≠ 0 := by
  intro h0
  apply hs (j + 1)
  rw [step_succ, h0, mul_zero]

/-- The coefficient of `y^{m−2ℓ}` in `P_k`. -/
def aa (c : K) (p zeta k l : ℕ) : K := Bc p zeta l / step (c + 1) (k + l)

/-- The `c`-free half of the write-up's coefficient equation: a ratio of closed forms. -/
theorem Bc_rec (p zeta l : ℕ) (hl : l < p) :
    2 * ((l : K) + 1) * Bc p zeta (l + 1)
      = ((2 * (p - l) + zeta : ℕ) : K) * (((2 * (p - l) + zeta : ℕ) : K) - 1) * Bc p zeta l := by
  obtain ⟨s, rfl⟩ : ∃ s, p = l + 1 + s := ⟨p - l - 1, by omega⟩
  unfold Bc
  rw [show l + 1 + s - (l + 1) = s by omega, show l + 1 + s - l = s + 1 by omega]
  have hfl : (((l + 1).factorial : ℕ) : K) = ((l : K) + 1) * (l.factorial : K) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hE : ((2 * (s + 1) + zeta).factorial : K)
      = ((2 * (s + 1) + zeta : ℕ) : K) * (((2 * (s + 1) + zeta : ℕ) : K) - 1)
        * ((2 * s + zeta).factorial : K) := by
    rw [show 2 * (s + 1) + zeta = (2 * s + zeta) + 1 + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast
    ring
  rw [hfl, hE, pow_succ]
  have h2 : (2 : K) ^ l ≠ 0 := pow_ne_zero l (by norm_num)
  have hl1 : ((l : K) + 1) ≠ 0 := by
    have : ((l + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    push_cast at this
    exact this
  have hfn : ((l.factorial : ℕ) : K) ≠ 0 := factorial_ne_zero l
  have hfs : (((2 * s + zeta).factorial : ℕ) : K) ≠ 0 := factorial_ne_zero _
  have hEne : ((2 * (s + 1) + zeta : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hE1 : ((2 * (s + 1) + zeta : ℕ) : K) - 1 ≠ 0 := by
    have hc : ((2 * (s + 1) + zeta : ℕ) : K) - 1 = ((2 * (s + 1) + zeta - 1 : ℕ) : K) := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hc]
    exact Nat.cast_ne_zero.2 (by omega)
  field_simp <;> ring

/-- **The write-up's coefficient equation**, which is its (5) read off `y^{m−2ℓ}`. -/
theorem aa_rec (c : K) (p zeta k l : ℕ) (hl : l < p)
    (hs : ∀ j : ℕ, step (c + 1) j ≠ 0) :
    2 * ((l : K) + 1) * (c + 2 * k + 2 * l + 1) * aa c p zeta k (l + 1)
      = ((2 * (p - l) + zeta : ℕ) : K) * (((2 * (p - l) + zeta : ℕ) : K) - 1)
        * aa c p zeta k l := by
  have hfac : c + 2 * (k : K) + 2 * l + 1 = c + 1 + 2 * ((k + l : ℕ) : K) := by
    push_cast
    ring
  have hne : c + 1 + 2 * ((k + l : ℕ) : K) ≠ 0 := step_factor_ne_zero c (k + l) hs
  have hsk := hs (k + l)
  have h1 : 2 * ((l : K) + 1) * (c + 1 + 2 * ((k + l : ℕ) : K)) * aa c p zeta k (l + 1)
      = 2 * ((l : K) + 1) * Bc p zeta (l + 1) / step (c + 1) (k + l) := by
    unfold aa
    rw [show k + (l + 1) = (k + l) + 1 by ring, step_succ]
    field_simp <;> ring
  have h2 : ((2 * (p - l) + zeta : ℕ) : K) * (((2 * (p - l) + zeta : ℕ) : K) - 1)
        * aa c p zeta k l
      = ((2 * (p - l) + zeta : ℕ) : K) * (((2 * (p - l) + zeta : ℕ) : K) - 1) * Bc p zeta l
        / step (c + 1) (k + l) := by
    unfold aa
    rw [mul_div_assoc]
  rw [hfac, h1, h2]
  congr 1
  linear_combination Bc_rec (K := K) p zeta l hl

/-- **The write-up's (6)**, as the ratio of two step-two denominators. -/
theorem aa_shift (c : K) (p zeta k l : ℕ) (hs : ∀ j : ℕ, step (c + 1) j ≠ 0) :
    aa c p zeta k l = (c + 2 * (k + 1) + 2 * l - 1) * aa c p zeta (k + 1) l := by
  have hfac : c + 2 * ((k : K) + 1) + 2 * l - 1 = c + 1 + 2 * ((k + l : ℕ) : K) := by
    push_cast
    ring
  have hstep : step (c + 1) (k + 1 + l)
      = step (c + 1) (k + l) * (c + 2 * ((k : K) + 1) + 2 * l - 1) := by
    rw [show k + 1 + l = (k + l) + 1 by ring, step_succ, hfac]
    try push_cast
    try ring
  have hsk := hs (k + l)
  have hne : c + 2 * ((k : K) + 1) + 2 * l - 1 ≠ 0 := by
    rw [hfac]
    exact step_factor_ne_zero c (k + l) hs
  unfold aa
  rw [hstep]
  field_simp <;> ring

/- ### P -/

/-- The exponent `e_ℓ = m − 2ℓ` at `m = 2p + ζ`. -/
def ee (p zeta l : ℕ) : ℕ := 2 * (p - l) + zeta

theorem ee_def (p zeta l : ℕ) : ee p zeta l = 2 * (p - l) + zeta := rfl

/-- The auxiliary polynomial `P_k` of the write-up's (4). -/
noncomputable def Pk (c : K) (p zeta k : ℕ) : K[X] :=
  ∑ l ∈ range (p + 1), C (aa c p zeta k l) * X ^ ee p zeta l

/-- The write-up's `β`. -/
def bb (c : K) (p zeta k : ℕ) : K := 2 * ((2 * p + zeta : ℕ) : K) + c + 2 * k - 2

/-- The write-up's `γ = mα`. -/
def gg (c : K) (p zeta k : ℕ) : K :=
  ((2 * p + zeta : ℕ) : K) * (c + 2 * k + ((2 * p + zeta : ℕ) : K) - 1)

/-- What the operator leaves on `y^{e_ℓ}`. -/
noncomputable def uu (c : K) (p zeta k l : ℕ) : K :=
  aa c p zeta k l * (((ee p zeta l : ℕ) : K) * (((ee p zeta l : ℕ) : K) - 1)
    - bb c p zeta k * ((ee p zeta l : ℕ) : K) + gg c p zeta k)

/-- What the operator drops onto `y^{e_ℓ−2}`. -/
noncomputable def vv (c : K) (p zeta k l : ℕ) : K :=
  aa c p zeta k l * ((ee p zeta l : ℕ) : K) * (((ee p zeta l : ℕ) : K) - 1)

theorem derivative_term (a : K) (e : ℕ) :
    X * derivative (C a * X ^ e) = C (a * e) * X ^ e := by
  rcases e with _ | e
  · simp
  · rw [derivative_C_mul, derivative_X_pow, show (e + 1) - 1 = e by omega, map_mul]
    push_cast
    ring

/-- **The write-up's (6)**: the contiguous relation between `P_k` and `P_{k+1}`. -/
theorem Pk_contig (c : K) (p zeta k : ℕ) (hs : ∀ j : ℕ, step (c + 1) j ≠ 0) :
    Pk c p zeta k
      = C (c + 2 * (k + 1) + ((2 * p + zeta : ℕ) : K) - 1) * Pk c p zeta (k + 1)
        - X * derivative (Pk c p zeta (k + 1)) := by
  unfold Pk
  rw [derivative_sum, Finset.mul_sum, Finset.mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun l hl => ?_
  rw [mem_range] at hl
  have he : ((ee p zeta l : ℕ) : K) = ((2 * p + zeta : ℕ) : K) - 2 * l := by
    have h1 : ee p zeta l + 2 * l = 2 * p + zeta := by
      rw [ee_def]
      omega
    have hc : ((ee p zeta l : ℕ) : K) + 2 * (l : K) = ((2 * p + zeta : ℕ) : K) := by
      exact_mod_cast h1
    linear_combination hc
  rw [derivative_term, aa_shift c p zeta k l hs, ← mul_assoc, ← C_mul, ← sub_mul, ← C_sub]
  congr 2
  rw [he]
  ring

/-- The operator `(y²−1)∂² − β y ∂ + γ` on a single monomial. -/
theorem ode_term (a b g : K) (e : ℕ) :
    (X ^ 2 - 1) * derivative (derivative (C a * X ^ e)) - C b * X * derivative (C a * X ^ e)
        + C g * (C a * X ^ e)
      = C (a * (((e : ℕ) : K) * (((e : ℕ) : K) - 1) - b * ((e : ℕ) : K) + g)) * X ^ e
        - C (a * ((e : ℕ) : K) * (((e : ℕ) : K) - 1)) * X ^ (e - 2) := by
  match e with
  | 0 =>
    simp [map_mul]
    try ring
  | 1 =>
    rw [derivative_C_mul, derivative_X_pow]
    simp [map_mul]
    try ring
  | (e + 2) =>
    rw [derivative_C_mul, derivative_X_pow, derivative_C_mul, derivative_C_mul,
      derivative_X_pow, show e + 2 - 1 = e + 1 by omega, show e + 1 - 1 = e by omega,
      show e + 2 - 2 = e by omega]
    have hC : (C (((e : ℕ) : K) + 1) : K[X]) = C (((e : ℕ) : K) + 2) - 1 := by
      rw [show (((e : ℕ) : K) + 1) = (((e : ℕ) : K) + 2) - 1 by ring, map_sub, map_one]
    simp only [map_mul, map_add, map_sub, map_one]
    push_cast
    rw [hC]
    ring

/-- `uu` in factored form: `aa(k,ℓ)(e_ℓ − m)(e_ℓ − α)`. -/
theorem uu_eq (c : K) (p zeta k l : ℕ) :
    uu c p zeta k l = aa c p zeta k l * (((ee p zeta l : ℕ) : K) - ((2 * p + zeta : ℕ) : K))
      * (((ee p zeta l : ℕ) : K) - (c + 2 * k + ((2 * p + zeta : ℕ) : K) - 1)) := by
  unfold uu bb gg
  ring

/-- **The write-up's (5)**: the differential equation satisfied by `P_k`. -/
theorem Pk_ode (c : K) (p zeta k : ℕ) (hz : zeta ≤ 1) (hs : ∀ j : ℕ, step (c + 1) j ≠ 0) :
    (X ^ 2 - 1) * derivative (derivative (Pk c p zeta k))
        - C (bb c p zeta k) * X * derivative (Pk c p zeta k)
        + C (gg c p zeta k) * Pk c p zeta k = 0 := by
  have hexpand : (X ^ 2 - 1) * derivative (derivative (Pk c p zeta k))
      - C (bb c p zeta k) * X * derivative (Pk c p zeta k) + C (gg c p zeta k) * Pk c p zeta k
      = ∑ l ∈ range (p + 1), (C (uu c p zeta k l) * X ^ ee p zeta l
          - C (vv c p zeta k l) * X ^ (ee p zeta l - 2)) := by
    unfold Pk
    rw [derivative_sum, derivative_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun l _ => ?_
    rw [uu, vv]
    exact ode_term _ _ _ _
  have h0 : uu c p zeta k 0 = 0 := by
    rw [uu_eq]
    have : ee p zeta 0 = 2 * p + zeta := by
      rw [ee_def]
      omega
    rw [this]
    ring
  have hp : vv c p zeta k p = 0 := by
    unfold vv
    have hep : ee p zeta p = zeta := by
      rw [ee_def]
      omega
    rw [hep]
    interval_cases zeta <;> norm_num
  have hcoef : ∀ l, l < p → uu c p zeta k (l + 1) = vv c p zeta k l := by
    intro l hl
    have hrec := aa_rec c p zeta k l hl hs
    have hc1 : ((ee p zeta (l + 1) : ℕ) : K) = ((ee p zeta l : ℕ) : K) - 2 := by
      have : ee p zeta l = ee p zeta (l + 1) + 2 := by
        rw [ee_def, ee_def]
        omega
      rw [this]
      push_cast
      ring
    have hcm : ((ee p zeta l : ℕ) : K) = ((2 * p + zeta : ℕ) : K) - 2 * l := by
      have h1 : ee p zeta l + 2 * l = 2 * p + zeta := by
        rw [ee_def]
        omega
      have hc : ((ee p zeta l : ℕ) : K) + 2 * (l : K) = ((2 * p + zeta : ℕ) : K) := by
        exact_mod_cast h1
      linear_combination hc
    have hee : 2 * (p - l) + zeta = ee p zeta l := rfl
    rw [hee, hcm] at hrec
    rw [uu_eq, vv, hc1, hcm]
    push_cast at hrec ⊢
    linear_combination hrec
  rw [hexpand, sum_sub_distrib, sub_eq_zero,
    Finset.sum_range_succ' (fun l => C (uu c p zeta k l) * X ^ ee p zeta l) p,
    Finset.sum_range_succ (fun l => C (vv c p zeta k l) * X ^ (ee p zeta l - 2)) p,
    h0, hp]
  simp only [map_zero, zero_mul, add_zero, zero_add]
  refine sum_congr rfl fun l hl => ?_
  rw [mem_range] at hl
  have hidx : ee p zeta (l + 1) = ee p zeta l - 2 := by
    rw [ee_def, ee_def]
    omega
  rw [hidx, hcoef l hl]

/- ### Apex -/

/-- `B_{m,m−ℓ}`, trimmed to zero off `ℓ ≤ p`. -/
noncomputable def Bt (p zeta l : ℕ) : K := if l ≤ p then Bc p zeta l else 0

theorem Bt_zero (p zeta : ℕ) : Bt p zeta 0 = (1 : K) := by
  unfold Bt Bc
  rw [if_pos (by omega), Nat.sub_zero, pow_zero, Nat.factorial_zero]
  rw [Nat.cast_one, one_mul, one_mul, div_self (factorial_ne_zero _)]

theorem Bt_out (p zeta l : ℕ) (h : p < l) : Bt p zeta l = (0 : K) := by
  unfold Bt
  rw [if_neg (by omega)]

/-- Every `step` is nonzero when every factor is. -/
theorem step_ne_zero (c : K) (hf : ∀ j : ℕ, c + 1 + 2 * (j : K) ≠ 0) (n : ℕ) :
    step (c + 1) n ≠ 0 := by
  induction n with
  | zero =>
    rw [show step (c + 1) 0 = 1 from rfl]
    exact one_ne_zero
  | succ n ih =>
    rw [step_succ]
    exact mul_ne_zero ih (hf n)

/-- **The Pascal relation** for the trimmed closed form (it uses `ζ ≤ 1`). -/
theorem Bt_rec (p zeta l : ℕ) (hz : zeta ≤ 1) :
    (Bt (p + 1) zeta (l + 1) : K)
      = Bt p zeta (l + 1) + (4 * (p : K) + 2 * zeta - 2 * l + 1) * Bt p zeta l := by
  have h2 : ∀ j : ℕ, (2 : K) ^ j ≠ 0 := fun j => pow_ne_zero j (by norm_num)
  rcases Nat.lt_or_ge l p with hlp | hlp
  · obtain ⟨s, rfl⟩ : ∃ s, p = l + 1 + s := ⟨p - l - 1, by omega⟩
    unfold Bt Bc
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega),
      show l + 1 + s + 1 - (l + 1) = s + 1 by omega, show l + 1 + s - (l + 1) = s by omega,
      show l + 1 + s - l = s + 1 by omega]
    have hnum : ((2 * (l + 1 + s + 1) + zeta).factorial : K)
        = ((2 * (l + 1 + s) + zeta : ℕ) + 2 : K) * ((2 * (l + 1 + s) + zeta : ℕ) + 1 : K)
          * ((2 * (l + 1 + s) + zeta).factorial : K) := by
      rw [show 2 * (l + 1 + s + 1) + zeta = (2 * (l + 1 + s) + zeta) + 1 + 1 by ring,
        Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    have hE : ((2 * (s + 1) + zeta).factorial : K)
        = ((2 * (s + 1) + zeta : ℕ) : K) * (((2 * (s + 1) + zeta : ℕ) : K) - 1)
          * ((2 * s + zeta).factorial : K) := by
      rw [show 2 * (s + 1) + zeta = (2 * s + zeta) + 1 + 1 by ring, Nat.factorial_succ,
        Nat.factorial_succ]
      push_cast
      ring
    have hfl : (((l + 1).factorial : ℕ) : K) = ((l : K) + 1) * (l.factorial : K) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [hnum, hE, hfl, pow_succ]
    have hfn : ((l.factorial : ℕ) : K) ≠ 0 := factorial_ne_zero l
    have hfs : (((2 * s + zeta).factorial : ℕ) : K) ≠ 0 := factorial_ne_zero _
    have hl1 : ((l : K) + 1) ≠ 0 := by
      have hc : ((l + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      push_cast at hc
      exact hc
    have hEne : ((2 * (s + 1) + zeta : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hE1 : ((2 * (s + 1) + zeta : ℕ) : K) - 1 ≠ 0 := by
      have hc : ((2 * (s + 1) + zeta : ℕ) : K) - 1 = ((2 * (s + 1) + zeta - 1 : ℕ) : K) := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      rw [hc]
      exact Nat.cast_ne_zero.2 (by omega)
    field_simp
    push_cast
    ring
  · rcases Nat.eq_or_lt_of_le hlp with he | hlt
    · -- `ℓ = p`: the lower neighbour vanishes and the closed forms meet at `t = 0`
      have hlp' : l = p := he.symm
      subst hlp'
      rw [Bt_out l zeta (l + 1) (by omega), zero_add]
      unfold Bt Bc
      rw [if_pos (by omega), if_pos (by omega), show l + 1 - (l + 1) = 0 by omega,
        show l - l = 0 by omega]
      have hnum : ((2 * (l + 1) + zeta).factorial : K)
          = ((2 * l + zeta : ℕ) + 2 : K) * ((2 * l + zeta : ℕ) + 1 : K)
            * ((2 * l + zeta).factorial : K) := by
        rw [show 2 * (l + 1) + zeta = (2 * l + zeta) + 1 + 1 by ring, Nat.factorial_succ,
          Nat.factorial_succ]
        push_cast
        ring
      have hfl : (((l + 1).factorial : ℕ) : K) = ((l : K) + 1) * (l.factorial : K) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [hnum, hfl, pow_succ]
      have hfn : ((l.factorial : ℕ) : K) ≠ 0 := factorial_ne_zero l
      have hfz : (((2 * 0 + zeta).factorial : ℕ) : K) ≠ 0 := factorial_ne_zero _
      have hl1 : ((l : K) + 1) ≠ 0 := by
        have hc : ((l + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
        push_cast at hc
        exact hc
      field_simp
      interval_cases zeta <;> push_cast <;> ring
    · rw [Bt_out _ _ _ (by omega), Bt_out _ _ _ (by omega), Bt_out _ _ _ (by omega)]
      ring

/-- The write-up's `P_0(1)`, as a sum. -/
noncomputable def Ssum (c : K) (p zeta : ℕ) : K :=
  ∑ l ∈ range (p + 1), Bt p zeta l / step (c + 1) l


theorem step_shift (c : K) (l : ℕ) : step (c + 1) (l + 1) = (c + 1) * step (c + 2 + 1) l := by
  induction l with
  | zero =>
    rw [step_succ, show step (c + 1) 0 = 1 from rfl, show step (c + 2 + 1) 0 = 1 from rfl]
    push_cast
    ring
  | succ l ih =>
    rw [step_succ, ih, step_succ, ← mul_assoc]
    congr 1
    push_cast
    ring

/-- **The `c`-shift recurrence** for the apex sum. -/
theorem Ssum_rec (c : K) (p zeta : ℕ) (hz : zeta ≤ 1) (hf : ∀ j : ℕ, c + 1 + 2 * (j : K) ≠ 0) :
    Ssum c (p + 1) zeta = (c + 4 * p + 2 * zeta + 2) / (c + 1) * Ssum (c + 2) p zeta := by
  have hsne : ∀ l : ℕ, step (c + 1) l ≠ 0 := step_ne_zero c hf
  have hc1 : (c + 1 : K) ≠ 0 := by
    have := hf 0
    push_cast at this
    simpa using this
  have hfl : ∀ l : ℕ, step (c + 1) (l + 1) = step (c + 1) l * (c + 1 + 2 * (l : K)) := by
    intro l
    rw [step_succ]
  -- the shifted sum, rewritten over the unshifted denominators
  have hR : Ssum (c + 2) p zeta
      = (c + 1) * ∑ l ∈ range (p + 1), Bt p zeta l / step (c + 1) (l + 1) := by
    unfold Ssum
    rw [Finset.mul_sum]
    refine sum_congr rfl fun l _ => ?_
    rw [step_shift]
    have h2 : step (c + 2 + 1) l ≠ 0 := by
      intro h0
      apply hsne (l + 1)
      rw [step_shift, h0, mul_zero]
    field_simp
  -- the top sum, split by the Pascal relation
  have hL : Ssum c (p + 1) zeta
      = 1 + ∑ l ∈ range (p + 1),
          (Bt p zeta (l + 1) + (4 * (p : K) + 2 * zeta - 2 * l + 1) * Bt p zeta l)
            / step (c + 1) (l + 1) := by
    unfold Ssum
    rw [Finset.sum_range_succ' (fun l => Bt (p + 1) zeta l / step (c + 1) l) (p + 1), Bt_zero,
      show step (c + 1) 0 = 1 from rfl, div_one, add_comm]
    congr 1
    exact sum_congr rfl fun l _ => by rw [Bt_rec p zeta l hz]
  have hsum_add : ∑ l ∈ range (p + 1),
      (Bt p zeta (l + 1) + (4 * (p : K) + 2 * zeta - 2 * l + 1) * Bt p zeta l)
        / step (c + 1) (l + 1)
      = (∑ l ∈ range (p + 1), Bt p zeta (l + 1) / step (c + 1) (l + 1))
        + ∑ l ∈ range (p + 1),
            (4 * (p : K) + 2 * zeta - 2 * l + 1) * Bt p zeta l / step (c + 1) (l + 1) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun l _ => by rw [add_div]
  have htel : ∑ l ∈ range (p + 1), Bt p zeta (l + 1) / step (c + 1) (l + 1)
      = Ssum c p zeta - 1 := by
    have h1 : ∑ l ∈ range (p + 1 + 1), Bt p zeta l / step (c + 1) l
        = (∑ l ∈ range (p + 1), Bt p zeta (l + 1) / step (c + 1) (l + 1))
          + Bt p zeta 0 / step (c + 1) 0 :=
      Finset.sum_range_succ' (fun l => Bt p zeta l / step (c + 1) l) (p + 1)
    rw [Finset.sum_range_succ (fun l => Bt p zeta l / step (c + 1) l) (p + 1),
      Bt_out p zeta (p + 1) (by omega), zero_div, add_zero] at h1
    rw [Bt_zero, show step (c + 1) 0 = 1 from rfl, div_one] at h1
    unfold Ssum
    rw [h1]
    ring
  have hA : ∑ l ∈ range (p + 1), ((c : K) + 2 * l + 1) * (Bt p zeta l / step (c + 1) (l + 1))
      = Ssum c p zeta := by
    unfold Ssum
    refine sum_congr rfl fun l _ => ?_
    have h1 : step (c + 1) (l + 1) = step (c + 1) l * (c + 1 + 2 * (l : K)) := step_succ _ _
    have h2 : step (c + 1) l ≠ 0 := hsne l
    have h3 : (c + 1 + 2 * (l : K)) ≠ 0 := hf l
    rw [h1]
    field_simp
    ring
  have key : ∀ l ∈ range (p + 1),
      ((c : K) + 2 * l + 1) * (Bt p zeta l / step (c + 1) (l + 1))
        + (4 * (p : K) + 2 * zeta - 2 * l + 1) * Bt p zeta l / step (c + 1) (l + 1)
      = (c + 4 * p + 2 * zeta + 2) * (Bt p zeta l / step (c + 1) (l + 1)) := by
    intro l _
    have hne : step (c + 1) (l + 1) ≠ 0 := hsne (l + 1)
    field_simp
    ring
  calc Ssum c (p + 1) zeta
      = (∑ l ∈ range (p + 1), ((c : K) + 2 * l + 1) * (Bt p zeta l / step (c + 1) (l + 1)))
        + ∑ l ∈ range (p + 1),
            (4 * (p : K) + 2 * zeta - 2 * l + 1) * Bt p zeta l / step (c + 1) (l + 1) := by
        rw [hL, hsum_add, htel, hA]
        ring
    _ = ∑ l ∈ range (p + 1), (((c : K) + 2 * l + 1) * (Bt p zeta l / step (c + 1) (l + 1))
          + (4 * (p : K) + 2 * zeta - 2 * l + 1) * Bt p zeta l / step (c + 1) (l + 1)) :=
        (sum_add_distrib).symm
    _ = ∑ l ∈ range (p + 1), (c + 4 * p + 2 * zeta + 2) * (Bt p zeta l / step (c + 1) (l + 1)) :=
        sum_congr rfl key
    _ = (c + 4 * p + 2 * zeta + 2) * ∑ l ∈ range (p + 1), Bt p zeta l / step (c + 1) (l + 1) :=
        (Finset.mul_sum _ _ _).symm
    _ = (c + 4 * p + 2 * zeta + 2) / (c + 1) * Ssum (c + 2) p zeta := by
        rw [hR]
        field_simp

/-- **The write-up's (9)**, by induction instead of Chu–Vandermonde. -/
theorem apex (c : K) (p zeta : ℕ) (hz : zeta ≤ 1) (hf : ∀ j : ℕ, c + 1 + 2 * (j : K) ≠ 0) :
    Ssum c p zeta = step (c + 2 * p + 2 * zeta) p / step (c + 1) p := by
  induction p generalizing c with
  | zero =>
    unfold Ssum
    rw [sum_range_one, Bt_zero, show step (c + 1) 0 = (1 : K) from rfl,
      show step (c + 2 * ((0 : ℕ) : K) + 2 * ((zeta : ℕ) : K)) 0 = (1 : K) from rfl]
    try norm_num
  | succ p ih =>
    have hf2 : ∀ j : ℕ, c + 2 + 1 + 2 * (j : K) ≠ 0 := by
      intro j
      intro h0
      apply hf (j + 1)
      push_cast at h0 ⊢
      linear_combination h0
    have hsne : ∀ l : ℕ, step (c + 1) l ≠ 0 := step_ne_zero c hf
    have hc1 : (c + 1 : K) ≠ 0 := by
      have := hf 0
      push_cast at this
      simpa using this
    have hs2 : ∀ l : ℕ, step (c + 2 + 1) l ≠ 0 := step_ne_zero (c + 2) hf2
    rw [Ssum_rec c p zeta hz hf, ih (c + 2) hf2, step_succ, step_shift]
    rw [show c + 2 * ((p + 1 : ℕ) : K) + 2 * zeta = c + 2 + 2 * (p : K) + 2 * zeta by
      push_cast
      ring]
    field_simp
    ring

/- ### H -/

/-- The write-up's `U = 1 + z/2`, cleared of denominators: `W = 2U = 2 + z`.  Working with `W`
keeps every coefficient of the reduction integral, which is what lets `ring` close the
cancellation (8); with `U` the factor `2⁻¹` is an opaque atom and `(1/2)·2 = 1` is invisible. -/
noncomputable def Wz : K[X] := 2 + X

/-- `P_k(1 + z)`. -/
noncomputable def Qk (c : K) (p zeta k : ℕ) : K[X] := (Pk c p zeta k).comp (1 + X)

/-- The write-up's `H_{n,k} = n!/(n−k)! · [zᵏ] U^{n−k} P_k(1+z)`, written over `W = 2U`. -/
noncomputable def Hnk (c : K) (p zeta n k : ℕ) : K :=
  if k ≤ n then ((n.factorial : K) / ((2 : K) ^ (n - k) * ((n - k).factorial : K)))
    * ((Wz : K[X]) ^ (n - k) * Qk c p zeta k).coeff k else 0

theorem Wz_eval_zero : (Wz : K[X]).eval 0 = 2 := by
  unfold Wz
  simp only [eval_add, eval_ofNat, eval_X, add_zero]

/-- Off the triangle at `n = 0`. -/
theorem Hnk_zero_succ (c : K) (p zeta k : ℕ) : Hnk c p zeta 0 (k + 1) = 0 := by
  unfold Hnk
  rw [if_neg (by omega)]

/-- The zero column is constant: `[z⁰](Wᵗ Q₀) = 2ᵗ Q₀(0)`, and the `2ᵗ` cancels the scalar. -/
theorem Hnk_succ_zero (c : K) (p zeta n : ℕ) :
    Hnk c p zeta (n + 1) 0 = Hnk c p zeta n 0 := by
  have hco : ∀ t : ℕ, ((Wz : K[X]) ^ t * Qk c p zeta 0).coeff 0
      = (2 : K) ^ t * (Qk c p zeta 0).eval 0 := by
    intro t
    rw [coeff_zero_eq_eval_zero, eval_mul, eval_pow, Wz_eval_zero]
  have h2 : ∀ t : ℕ, (2 : K) ^ t ≠ 0 := fun t => pow_ne_zero t (by norm_num)
  have hfn1 : (((n + 1).factorial : ℕ) : K) ≠ 0 := factorial_ne_zero _
  have hfn : ((n.factorial : ℕ) : K) ≠ 0 := factorial_ne_zero _
  unfold Hnk
  rw [if_pos (by omega), if_pos (by omega), Nat.sub_zero, Nat.sub_zero, hco, hco]
  field_simp

/- ### Q -/

theorem Qk_deriv (c : K) (p zeta k : ℕ) :
    derivative (Qk c p zeta k) = (derivative (Pk c p zeta k)).comp (1 + X) := by
  unfold Qk
  rw [derivative_comp]
  simp

/-- **The write-up's (6)** in the variable `z`. -/
theorem Qk_contig (c : K) (p zeta k : ℕ) (hs : ∀ j : ℕ, step (c + 1) j ≠ 0) :
    Qk c p zeta k
      = C (c + 2 * (k + 1) + ((2 * p + zeta : ℕ) : K) - 1) * Qk c p zeta (k + 1)
        - (1 + X) * derivative (Qk c p zeta (k + 1)) := by
  have h := congrArg (fun q : K[X] => q.comp (1 + X)) (Pk_contig c p zeta k hs)
  simp only [sub_comp, mul_comp, C_comp, X_comp, one_comp, add_comp] at h
  rw [Qk_deriv]
  unfold Qk
  exact h

theorem X_mul_Wz (K : Type*) [Field K] [CharZero K] :
    (X : K[X]) * (Wz : K[X]) = (1 + X) ^ 2 - 1 := by
  unfold Wz
  ring

/-- **The write-up's (5)** in the variable `z`, where `y² − 1 = z W`. -/
theorem Qk_ode (c : K) (p zeta k : ℕ) (hz : zeta ≤ 1) (hs : ∀ j : ℕ, step (c + 1) j ≠ 0) :
    X * (Wz : K[X]) * derivative (derivative (Qk c p zeta k))
        - C (bb c p zeta k) * (1 + X) * derivative (Qk c p zeta k)
        + C (gg c p zeta k) * Qk c p zeta k = 0 := by
  have h := congrArg (fun q : K[X] => q.comp (1 + X)) (Pk_ode c p zeta k hz hs)
  simp only [sub_comp, add_comp, mul_comp, pow_comp, C_comp, X_comp, one_comp, zero_comp] at h
  have hd2 : derivative ((derivative (Pk c p zeta k)).comp (1 + X))
      = (derivative (derivative (Pk c p zeta k))).comp (1 + X) := by
    rw [derivative_comp]
    simp
  rw [Qk_deriv, hd2]
  unfold Qk
  rw [X_mul_Wz]
  exact h

/- ### Rec -/

theorem derivative_Wz : derivative (Wz : K[X]) = 1 := by
  unfold Wz
  simp

theorem derivative_Wz_pow (M : ℕ) :
    derivative ((Wz : K[X]) ^ M) = C (M : K) * (Wz : K[X]) ^ (M - 1) := by
  rw [derivative_pow, derivative_Wz, mul_one]

/-- Shifting an index down is multiplication by `X`. -/
theorem coeff_shift_up (f : K[X]) (j : ℕ) : f.coeff j = (X * f).coeff (j + 1) := by
  rw [coeff_X_mul]

/-- Moving one derivative off the right factor. -/
theorem coeff_deriv_move (h q : K[X]) (j : ℕ) :
    (h * derivative q).coeff j
      = ((j : K) + 1) * (h * q).coeff (j + 1) - (derivative h * q).coeff j :=
  coeff_mul_derivative h q j

/-- The second-derivative move, twice. -/
theorem coeff_deriv_move2 (h q : K[X]) (j : ℕ) :
    (h * derivative (derivative q)).coeff j
      = ((j : K) + 1) * ((j : K) + 2) * (h * q).coeff (j + 2)
        - 2 * ((j : K) + 1) * (derivative h * q).coeff (j + 1)
        + (derivative (derivative h) * q).coeff j := by
  have h1 : (h * derivative (derivative q)).coeff j
      = ((j : K) + 1) * (h * derivative q).coeff (j + 1)
        - (derivative h * derivative q).coeff j := coeff_deriv_move h (derivative q) j
  have h2 : (h * derivative q).coeff (j + 1)
      = ((j : K) + 2) * (h * q).coeff (j + 2) - (derivative h * q).coeff (j + 1) := by
    have hm := coeff_deriv_move h q (j + 1)
    rw [show ((j : ℕ) + 1 + 1) = j + 2 from rfl] at hm
    push_cast at hm ⊢
    linear_combination hm
  have h3 : (derivative h * derivative q).coeff j
      = ((j : K) + 1) * (derivative h * q).coeff (j + 1)
        - (derivative (derivative h) * q).coeff j := coeff_deriv_move (derivative h) q j
  rw [h1, h2, h3]
  ring

/-- Pulling a scalar out of a coefficient of `W^M · (C a · g) · Q`. -/
theorem coeff_C_term (a : K) (g Q : K[X]) (M j : ℕ) :
    ((Wz : K[X]) ^ M * (C a * g) * Q).coeff j = a * ((Wz : K[X]) ^ M * g * Q).coeff j := by
  have h : (Wz : K[X]) ^ M * (C a * g) * Q = C a * ((Wz : K[X]) ^ M * g * Q) := by ring
  rw [h, coeff_C_mul]


theorem deriv_h2 (M : ℕ) :
    derivative (X * (Wz : K[X]) ^ (M + 2))
      = (Wz : K[X]) ^ (M + 2) + C (((M : ℕ) + 2 : ℕ) : K) * X * (Wz : K[X]) ^ (M + 1) := by
  rw [derivative_mul, derivative_X, derivative_Wz_pow, show M + 2 - 1 = M + 1 by omega]
  ring

theorem deriv_h2_two (M : ℕ) :
    derivative (derivative (X * (Wz : K[X]) ^ (M + 2)))
      = C (2 * (((M : ℕ) + 2 : ℕ) : K)) * (Wz : K[X]) ^ (M + 1)
        + C ((((M : ℕ) + 2 : ℕ) : K) * (((M : ℕ) + 1 : ℕ) : K)) * X * (Wz : K[X]) ^ M := by
  rw [deriv_h2]
  simp only [derivative_add, derivative_mul, derivative_C, derivative_X, derivative_Wz_pow,
    zero_mul, mul_zero, zero_add, add_zero, one_mul, mul_one]
  rw [show M + 2 - 1 = M + 1 by omega, show M + 1 - 1 = M by omega]
  simp only [map_mul, map_ofNat]
  ring

theorem deriv_h3 (M : ℕ) (a : K) :
    derivative ((Wz : K[X]) ^ (M + 1) * (C a * (1 + X)))
      = C ((((M : ℕ) + 1 : ℕ) : K)) * (Wz : K[X]) ^ M * (C a * (1 + X))
        + (Wz : K[X]) ^ (M + 1) * C a := by
  rw [derivative_mul, derivative_Wz_pow, show M + 1 - 1 = M by omega, derivative_mul,
    derivative_C, derivative_add, derivative_one, derivative_X]
  ring

/-- The contiguous term of the write-up's (8), with the derivative moved off `Q`. -/
theorem contig_term (c : K) (p zeta k M : ℕ) (hs : ∀ j : ℕ, step (c + 1) j ≠ 0) :
    ((Wz : K[X]) ^ (M + 1) * Qk c p zeta k).coeff k
      = (c + 2 * ((k : K) + 1) + ((2 * p + zeta : ℕ) : K) - 1)
          * ((Wz : K[X]) ^ M * (X * Wz) * Qk c p zeta (k + 1)).coeff (k + 1)
        - ((k : K) + 1) * ((Wz : K[X]) ^ M * (Wz * (1 + X)) * Qk c p zeta (k + 1)).coeff (k + 1)
        + ((Wz : K[X]) ^ M * (X * (C ((((M : ℕ) + 1 : ℕ) : K)) * (1 + X) + Wz))
            * Qk c p zeta (k + 1)).coeff (k + 1) := by
  set Q := Qk c p zeta (k + 1) with hQ
  set al : K := c + 2 * ((k : K) + 1) + ((2 * p + zeta : ℕ) : K) - 1 with hal
  have hcont : Qk c p zeta k = C al * Q - (1 + X) * derivative Q := by
    rw [hQ, hal]
    have hc := Qk_contig c p zeta k hs
    push_cast at hc ⊢
    exact hc
  have h0 : (Wz : K[X]) ^ (M + 1) * Qk c p zeta k
      = C al * ((Wz : K[X]) ^ (M + 1) * Q)
        - ((Wz : K[X]) ^ (M + 1) * (C (1 : K) * (1 + X))) * derivative Q := by
    rw [hcont, map_one]
    ring
  rw [h0, coeff_sub, coeff_C_mul, coeff_deriv_move, deriv_h3,
    coeff_shift_up ((Wz : K[X]) ^ (M + 1) * Q) k,
    coeff_shift_up ((C ((((M : ℕ) + 1 : ℕ) : K)) * (Wz : K[X]) ^ M * (C (1 : K) * (1 + X))
      + (Wz : K[X]) ^ (M + 1) * C (1 : K)) * Q) k]
  have e1 : X * ((Wz : K[X]) ^ (M + 1) * Q) = (Wz : K[X]) ^ M * (X * Wz) * Q := by ring
  have e2 : (Wz : K[X]) ^ (M + 1) * (C (1 : K) * (1 + X)) * Q
      = (Wz : K[X]) ^ M * (Wz * (1 + X)) * Q := by
    rw [map_one]
    ring
  have e3 : X * ((C ((((M : ℕ) + 1 : ℕ) : K)) * (Wz : K[X]) ^ M * (C (1 : K) * (1 + X))
        + (Wz : K[X]) ^ (M + 1) * C (1 : K)) * Q)
      = (Wz : K[X]) ^ M * (X * (C ((((M : ℕ) + 1 : ℕ) : K)) * (1 + X) + Wz)) * Q := by
    rw [map_one]
    ring
  rw [e1, e2, e3]
  ring

/-- The `Q''` term of the write-up's (8). -/
theorem ode_second (c : K) (p zeta k M : ℕ) :
    ((Wz : K[X]) ^ (M + 1) * (X * Wz * derivative (derivative (Qk c p zeta (k + 1))))).coeff k
      = ((k : K) + 1) * ((k : K) + 2)
          * ((Wz : K[X]) ^ M * (Wz ^ 2) * Qk c p zeta (k + 1)).coeff (k + 1)
        - 2 * ((k : K) + 1)
          * ((Wz : K[X]) ^ M * (Wz ^ 2 + C ((((M : ℕ) + 2 : ℕ) : K)) * (X * Wz))
              * Qk c p zeta (k + 1)).coeff (k + 1)
        + ((Wz : K[X]) ^ M
            * (X * (C (2 * ((((M : ℕ) + 2 : ℕ) : K))) * Wz
                + C (((((M : ℕ) + 2 : ℕ) : K)) * ((((M : ℕ) + 1 : ℕ) : K))) * X))
            * Qk c p zeta (k + 1)).coeff (k + 1) := by
  set Q := Qk c p zeta (k + 1) with hQ
  have hrw : (Wz : K[X]) ^ (M + 1) * (X * Wz * derivative (derivative Q))
      = (X * (Wz : K[X]) ^ (M + 2)) * derivative (derivative Q) := by ring
  rw [hrw, coeff_deriv_move2, deriv_h2_two, deriv_h2]
  have h1 : (X * (Wz : K[X]) ^ (M + 2)) * Q = X * ((Wz : K[X]) ^ M * Wz ^ 2 * Q) := by ring
  have h2 : ((Wz : K[X]) ^ (M + 2)
        + C ((((M : ℕ) + 2 : ℕ) : K)) * X * (Wz : K[X]) ^ (M + 1)) * Q
      = (Wz : K[X]) ^ M * (Wz ^ 2 + C ((((M : ℕ) + 2 : ℕ) : K)) * (X * Wz)) * Q := by ring
  have h3 : X * ((C (2 * ((((M : ℕ) + 2 : ℕ) : K))) * (Wz : K[X]) ^ (M + 1)
        + C (((((M : ℕ) + 2 : ℕ) : K)) * ((((M : ℕ) + 1 : ℕ) : K))) * X * (Wz : K[X]) ^ M) * Q)
      = (Wz : K[X]) ^ M * (X * (C (2 * ((((M : ℕ) + 2 : ℕ) : K))) * Wz
          + C (((((M : ℕ) + 2 : ℕ) : K)) * ((((M : ℕ) + 1 : ℕ) : K))) * X)) * Q := by ring
  rw [h1, coeff_X_mul, h2,
    coeff_shift_up ((C (2 * ((((M : ℕ) + 2 : ℕ) : K))) * (Wz : K[X]) ^ (M + 1)
      + C (((((M : ℕ) + 2 : ℕ) : K)) * ((((M : ℕ) + 1 : ℕ) : K))) * X * (Wz : K[X]) ^ M) * Q) k,
    h3]

/-- The `Q'` term of the write-up's (8). -/
theorem ode_first (c : K) (p zeta k M : ℕ) (a : K) :
    ((Wz : K[X]) ^ (M + 1) * (C a * (1 + X) * derivative (Qk c p zeta (k + 1)))).coeff k
      = ((k : K) + 1)
          * ((Wz : K[X]) ^ M * (C a * ((1 + X) * Wz)) * Qk c p zeta (k + 1)).coeff (k + 1)
        - ((Wz : K[X]) ^ M
            * (X * (C ((((M : ℕ) + 1 : ℕ) : K)) * (C a * (1 + X)) + C a * Wz))
            * Qk c p zeta (k + 1)).coeff (k + 1) := by
  set Q := Qk c p zeta (k + 1) with hQ
  have hrw : (Wz : K[X]) ^ (M + 1) * (C a * (1 + X) * derivative Q)
      = ((Wz : K[X]) ^ (M + 1) * (C a * (1 + X))) * derivative Q := by ring
  rw [hrw, coeff_deriv_move, deriv_h3]
  have h1 : (Wz : K[X]) ^ (M + 1) * (C a * (1 + X)) * Q
      = (Wz : K[X]) ^ M * (C a * ((1 + X) * Wz)) * Q := by ring
  have h2 : X * ((C ((((M : ℕ) + 1 : ℕ) : K)) * (Wz : K[X]) ^ M * (C a * (1 + X))
        + (Wz : K[X]) ^ (M + 1) * C a) * Q)
      = (Wz : K[X]) ^ M * (X * (C ((((M : ℕ) + 1 : ℕ) : K)) * (C a * (1 + X)) + C a * Wz))
          * Q := by ring
  rw [h1, coeff_shift_up ((C ((((M : ℕ) + 1 : ℕ) : K)) * (Wz : K[X]) ^ M * (C a * (1 + X))
    + (Wz : K[X]) ^ (M + 1) * C a) * Q) k, h2]

/-- The `γ` term of the write-up's (8). -/
theorem ode_gamma (c : K) (p zeta k M : ℕ) (a : K) :
    ((Wz : K[X]) ^ (M + 1) * (C a * Qk c p zeta (k + 1))).coeff k
      = ((Wz : K[X]) ^ M * (X * (C a * Wz)) * Qk c p zeta (k + 1)).coeff (k + 1) := by
  have hpoly : X * ((Wz : K[X]) ^ (M + 1) * (C a * Qk c p zeta (k + 1)))
      = (Wz : K[X]) ^ M * (X * (C a * Wz)) * Qk c p zeta (k + 1) := by ring
  rw [coeff_shift_up _ k, hpoly]


/-- The multiplier the displayed side of the write-up's (8) collects into (`W`-normalized). -/
noncomputable def Gpoly (c : K) (p zeta k M : ℕ) : K[X] :=
  C ((((k : K) + 1 + M) + c + ((2 * p + zeta : ℕ) : K)) * ((k : K) + 1 + M + 1)) * Wz
    - C (2 * ((((k : K) + 1 + M) + 2 * ((k : K) + 1) + c + ((2 * p + zeta : ℕ) : K))
        * ((M : K) + 1)))
    - C ((((k : K) + 1 + M) - 2 * ((k : K) + 1) + 2 + ((2 * p + zeta : ℕ) : K))
        * (c + 2 * ((k : K) + 1) + ((2 * p + zeta : ℕ) : K) - 1)) * (X * Wz)
    + C ((((k : K) + 1 + M) - 2 * ((k : K) + 1) + 2 + ((2 * p + zeta : ℕ) : K))
        * ((k : K) + 1)) * (Wz * (1 + X))
    - C ((((k : K) + 1 + M) - 2 * ((k : K) + 1) + 2 + ((2 * p + zeta : ℕ) : K)))
        * (X * (C ((((M : ℕ) + 1 : ℕ) : K)) * (1 + X) + Wz))

/-- The multiplier the ODE side of the write-up's (8) collects into (`W`-normalized). -/
noncomputable def Lpoly (c : K) (p zeta k M : ℕ) : K[X] :=
  C (((k : K) + 1) * ((k : K) + 2)) * (Wz ^ 2)
    - C (2 * ((k : K) + 1)) * (Wz ^ 2 + C ((((M : ℕ) + 2 : ℕ) : K)) * (X * Wz))
    + (X * (C (2 * ((((M : ℕ) + 2 : ℕ) : K))) * Wz
        + C (((((M : ℕ) + 2 : ℕ) : K)) * ((((M : ℕ) + 1 : ℕ) : K))) * X))
    - C ((k : K) + 1) * (C (bb c p zeta (k + 1)) * ((1 + X) * Wz))
    + (X * (C ((((M : ℕ) + 1 : ℕ) : K)) * (C (bb c p zeta (k + 1)) * (1 + X))
        + C (bb c p zeta (k + 1)) * Wz))
    + (X * (C (gg c p zeta (k + 1)) * Wz))

/-- **The write-up's `K + L = 0`**, with every coefficient integral. -/
theorem Gpoly_add_Lpoly (c : K) (p zeta k M : ℕ) :
    Gpoly c p zeta k M + Lpoly c p zeta k M = 0 := by
  unfold Gpoly Lpoly bb gg Wz
  push_cast
  simp only [map_add, map_sub, map_mul, map_one, map_ofNat]
  ring

/-- The displayed side, collected into one coefficient. -/
theorem coeff_Gpoly (c : K) (p zeta k M : ℕ) :
    ((Wz : K[X]) ^ M * Gpoly c p zeta k M * Qk c p zeta (k + 1)).coeff (k + 1)
      = (((k : K) + 1 + M) + c + ((2 * p + zeta : ℕ) : K)) * ((k : K) + 1 + M + 1)
          * ((Wz : K[X]) ^ M * Wz * Qk c p zeta (k + 1)).coeff (k + 1)
        - 2 * ((((k : K) + 1 + M) + 2 * ((k : K) + 1) + c + ((2 * p + zeta : ℕ) : K))
            * ((M : K) + 1)) * ((Wz : K[X]) ^ M * 1 * Qk c p zeta (k + 1)).coeff (k + 1)
        - ((((k : K) + 1 + M) - 2 * ((k : K) + 1) + 2 + ((2 * p + zeta : ℕ) : K))
            * (c + 2 * ((k : K) + 1) + ((2 * p + zeta : ℕ) : K) - 1))
            * ((Wz : K[X]) ^ M * (X * Wz) * Qk c p zeta (k + 1)).coeff (k + 1)
        + ((((k : K) + 1 + M) - 2 * ((k : K) + 1) + 2 + ((2 * p + zeta : ℕ) : K))
            * ((k : K) + 1))
            * ((Wz : K[X]) ^ M * (Wz * (1 + X)) * Qk c p zeta (k + 1)).coeff (k + 1)
        - (((k : K) + 1 + M) - 2 * ((k : K) + 1) + 2 + ((2 * p + zeta : ℕ) : K))
            * ((Wz : K[X]) ^ M * (X * (C ((((M : ℕ) + 1 : ℕ) : K)) * (1 + X) + Wz))
                * Qk c p zeta (k + 1)).coeff (k + 1) := by
  have hpoly : (Wz : K[X]) ^ M * Gpoly c p zeta k M * Qk c p zeta (k + 1)
      = C ((((k : K) + 1 + M) + c + ((2 * p + zeta : ℕ) : K)) * ((k : K) + 1 + M + 1))
          * ((Wz : K[X]) ^ M * Wz * Qk c p zeta (k + 1))
        - C (2 * ((((k : K) + 1 + M) + 2 * ((k : K) + 1) + c + ((2 * p + zeta : ℕ) : K))
            * ((M : K) + 1))) * ((Wz : K[X]) ^ M * 1 * Qk c p zeta (k + 1))
        - C ((((k : K) + 1 + M) - 2 * ((k : K) + 1) + 2 + ((2 * p + zeta : ℕ) : K))
            * (c + 2 * ((k : K) + 1) + ((2 * p + zeta : ℕ) : K) - 1))
            * ((Wz : K[X]) ^ M * (X * Wz) * Qk c p zeta (k + 1))
        + C ((((k : K) + 1 + M) - 2 * ((k : K) + 1) + 2 + ((2 * p + zeta : ℕ) : K))
            * ((k : K) + 1)) * ((Wz : K[X]) ^ M * (Wz * (1 + X)) * Qk c p zeta (k + 1))
        - C ((((k : K) + 1 + M) - 2 * ((k : K) + 1) + 2 + ((2 * p + zeta : ℕ) : K)))
            * ((Wz : K[X]) ^ M * (X * (C ((((M : ℕ) + 1 : ℕ) : K)) * (1 + X) + Wz))
                * Qk c p zeta (k + 1)) := by
    unfold Gpoly
    ring
  rw [hpoly]
  simp only [coeff_add, coeff_sub, coeff_C_mul]

/-- The ODE side, collected into one coefficient. -/
theorem coeff_Lpoly (c : K) (p zeta k M : ℕ) :
    ((Wz : K[X]) ^ M * Lpoly c p zeta k M * Qk c p zeta (k + 1)).coeff (k + 1)
      = ((k : K) + 1) * ((k : K) + 2)
          * ((Wz : K[X]) ^ M * (Wz ^ 2) * Qk c p zeta (k + 1)).coeff (k + 1)
        - 2 * ((k : K) + 1)
          * ((Wz : K[X]) ^ M * (Wz ^ 2 + C ((((M : ℕ) + 2 : ℕ) : K)) * (X * Wz))
              * Qk c p zeta (k + 1)).coeff (k + 1)
        + ((Wz : K[X]) ^ M
            * (X * (C (2 * ((((M : ℕ) + 2 : ℕ) : K))) * Wz
                + C (((((M : ℕ) + 2 : ℕ) : K)) * ((((M : ℕ) + 1 : ℕ) : K))) * X))
            * Qk c p zeta (k + 1)).coeff (k + 1)
        - ((k : K) + 1)
          * ((Wz : K[X]) ^ M * (C (bb c p zeta (k + 1)) * ((1 + X) * Wz))
              * Qk c p zeta (k + 1)).coeff (k + 1)
        + ((Wz : K[X]) ^ M
            * (X * (C ((((M : ℕ) + 1 : ℕ) : K)) * (C (bb c p zeta (k + 1)) * (1 + X))
                + C (bb c p zeta (k + 1)) * Wz)) * Qk c p zeta (k + 1)).coeff (k + 1)
        + ((Wz : K[X]) ^ M * (X * (C (gg c p zeta (k + 1)) * Wz))
            * Qk c p zeta (k + 1)).coeff (k + 1) := by
  have hpoly : (Wz : K[X]) ^ M * Lpoly c p zeta k M * Qk c p zeta (k + 1)
      = C (((k : K) + 1) * ((k : K) + 2))
          * ((Wz : K[X]) ^ M * (Wz ^ 2) * Qk c p zeta (k + 1))
        - C (2 * ((k : K) + 1))
          * ((Wz : K[X]) ^ M * (Wz ^ 2 + C ((((M : ℕ) + 2 : ℕ) : K)) * (X * Wz))
              * Qk c p zeta (k + 1))
        + ((Wz : K[X]) ^ M
            * (X * (C (2 * ((((M : ℕ) + 2 : ℕ) : K))) * Wz
                + C (((((M : ℕ) + 2 : ℕ) : K)) * ((((M : ℕ) + 1 : ℕ) : K))) * X))
            * Qk c p zeta (k + 1))
        - C ((k : K) + 1)
          * ((Wz : K[X]) ^ M * (C (bb c p zeta (k + 1)) * ((1 + X) * Wz))
              * Qk c p zeta (k + 1))
        + ((Wz : K[X]) ^ M
            * (X * (C ((((M : ℕ) + 1 : ℕ) : K)) * (C (bb c p zeta (k + 1)) * (1 + X))
                + C (bb c p zeta (k + 1)) * Wz)) * Qk c p zeta (k + 1))
        + ((Wz : K[X]) ^ M * (X * (C (gg c p zeta (k + 1)) * Wz))
            * Qk c p zeta (k + 1)) := by
    unfold Lpoly
    ring
  rw [hpoly]
  simp only [coeff_add, coeff_sub, coeff_C_mul]

/-- **The write-up's (8)**: the factorial-free form of its recurrence, at `n = k+1+M`. -/
theorem rec_coeff (c : K) (p zeta k M : ℕ) (hz : zeta ≤ 1)
    (hs : ∀ j : ℕ, step (c + 1) j ≠ 0) :
    (((k : K) + 1 + M) + c + ((2 * p + zeta : ℕ) : K)) * ((k : K) + 1 + M + 1)
        * ((Wz : K[X]) ^ M * Wz * Qk c p zeta (k + 1)).coeff (k + 1)
      = 2 * ((((k : K) + 1 + M) + 2 * ((k : K) + 1) + c + ((2 * p + zeta : ℕ) : K))
            * ((M : K) + 1))
          * ((Wz : K[X]) ^ M * 1 * Qk c p zeta (k + 1)).coeff (k + 1)
        + (((k : K) + 1 + M) - 2 * ((k : K) + 1) + 2 + ((2 * p + zeta : ℕ) : K))
          * ((Wz : K[X]) ^ (M + 1) * Qk c p zeta k).coeff k := by
  have hcontig := contig_term c p zeta k M hs
  have hode : ((Wz : K[X]) ^ (M + 1)
      * (X * Wz * derivative (derivative (Qk c p zeta (k + 1)))
        - C (bb c p zeta (k + 1)) * (1 + X) * derivative (Qk c p zeta (k + 1))
        + C (gg c p zeta (k + 1)) * Qk c p zeta (k + 1))).coeff k = 0 := by
    rw [Qk_ode c p zeta (k + 1) hz hs, mul_zero, coeff_zero]
  rw [mul_add, mul_sub, coeff_add, coeff_sub, ode_second, ode_first, ode_gamma] at hode
  have hGL : ((Wz : K[X]) ^ M * Gpoly c p zeta k M * Qk c p zeta (k + 1)).coeff (k + 1)
      + ((Wz : K[X]) ^ M * Lpoly c p zeta k M * Qk c p zeta (k + 1)).coeff (k + 1) = 0 := by
    rw [← coeff_add, ← add_mul, ← mul_add, Gpoly_add_Lpoly, mul_zero, zero_mul, coeff_zero]
  rw [coeff_Gpoly, coeff_Lpoly] at hGL
  linear_combination hGL - hode
    - (((k : K) + 1 + M) - 2 * ((k : K) + 1) + 2 + ((2 * p + zeta : ℕ) : K)) * hcontig


/-- Coefficients of `W · Q` and of `(X · W) · Q`, used at the `N = 0` edge. -/
theorem coeff_Wz_mul (Q : K[X]) (j : ℕ) :
    ((Wz : K[X]) * Q).coeff (j + 1) = 2 * Q.coeff (j + 1) + Q.coeff j := by
  have h : (Wz : K[X]) * Q = C (2 : K) * Q + X * Q := by
    unfold Wz
    rw [show (C (2 : K) : K[X]) = 2 from map_ofNat C 2]
    ring
  rw [h, coeff_add, coeff_C_mul, coeff_X_mul]

/-- **The `N = 0` edge of the write-up's (8)** — its `k = n+1` case, where the middle term drops
out.  The write-up passes through `U^{-1}` here; over polynomials the same computation simply has
no `W` factor at all. -/
theorem rec_coeff_edge (c : K) (p zeta k : ℕ) (hz : zeta ≤ 1)
    (hs : ∀ j : ℕ, step (c + 1) j ≠ 0) :
    ((k : K) + c + ((2 * p + zeta : ℕ) : K)) * ((k : K) + 1)
        * (Qk c p zeta (k + 1)).coeff (k + 1)
      = (((2 * p + zeta : ℕ) : K) - k) * (Qk c p zeta k).coeff k := by
  set Q := Qk c p zeta (k + 1) with hQ
  set m : K := ((2 * p + zeta : ℕ) : K) with hm
  -- the contiguous relation, read off at `[zᵏ]`
  have hcont : (Qk c p zeta k).coeff k
      = (c + 2 * ((k : K) + 1) + m - 1) * Q.coeff k
        - (((k : K) + 1) * (((1 : K[X]) + X) * Q).coeff (k + 1) - ((1 : K[X]) * Q).coeff k) := by
    have h0 : Qk c p zeta k
        = C (c + 2 * ((k : K) + 1) + m - 1) * Q - (1 + X) * derivative Q := by
      rw [hQ, hm]
      have hc := Qk_contig c p zeta k hs
      push_cast at hc ⊢
      exact hc
    rw [h0, coeff_sub, coeff_C_mul, coeff_deriv_move]
    simp only [derivative_add, derivative_one, derivative_X, zero_add]
  -- the ODE, read off at `[zᵏ]`
  have hode : (X * (Wz : K[X]) * derivative (derivative Q)
      - C (bb c p zeta (k + 1)) * (1 + X) * derivative Q
      + C (gg c p zeta (k + 1)) * Q).coeff k = 0 := by
    rw [Qk_ode c p zeta (k + 1) hz hs, coeff_zero]
  rw [coeff_add, coeff_sub] at hode
  -- the `Q''` term
  have h2 : (X * (Wz : K[X]) * derivative (derivative Q)).coeff k
      = ((k : K) + 1) * ((k : K) + 2) * (2 * Q.coeff (k + 1) + Q.coeff k)
        - 2 * ((k : K) + 1) * (2 * Q.coeff (k + 1) + 2 * Q.coeff k)
        + 2 * Q.coeff k := by
    rw [coeff_deriv_move2]
    have e1 : X * (Wz : K[X]) * Q = X * ((Wz : K[X]) * Q) := by ring
    have e2 : derivative (X * (Wz : K[X])) = 2 + 2 * X := by
      rw [derivative_mul, derivative_X, derivative_Wz]
      unfold Wz
      ring
    have e3 : derivative (derivative (X * (Wz : K[X]))) = 2 := by
      rw [e2, derivative_add, derivative_mul, derivative_X, derivative_ofNat]
      ring
    rw [e1, coeff_X_mul, coeff_Wz_mul, e3, e2]
    have e4 : ((2 : K[X]) + 2 * X) * Q = C (2 : K) * Q + X * (C (2 : K) * Q) := by
      rw [show (C (2 : K) : K[X]) = 2 from map_ofNat C 2]
      ring
    have e5 : (2 : K[X]) * Q = C (2 : K) * Q := by
      rw [show (C (2 : K) : K[X]) = 2 from map_ofNat C 2]
    rw [e4, coeff_add, coeff_C_mul, coeff_X_mul, coeff_C_mul, e5, coeff_C_mul] <;> ring
  -- the `Q'` term
  have h1 : (C (bb c p zeta (k + 1)) * (1 + X) * derivative Q).coeff k
      = bb c p zeta (k + 1)
        * (((k : K) + 1) * (Q.coeff (k + 1) + Q.coeff k) - Q.coeff k) := by
    have e0 : C (bb c p zeta (k + 1)) * (1 + X) * derivative Q
        = (C (bb c p zeta (k + 1)) * (1 + X)) * derivative Q := by ring
    rw [e0, coeff_deriv_move]
    have e1 : C (bb c p zeta (k + 1)) * (1 + X) * Q
        = C (bb c p zeta (k + 1)) * Q + X * (C (bb c p zeta (k + 1)) * Q) := by ring
    have e2 : derivative (C (bb c p zeta (k + 1)) * (1 + X)) * Q
        = C (bb c p zeta (k + 1)) * Q := by
      rw [derivative_mul, derivative_C, derivative_add, derivative_one, derivative_X]
      ring
    rw [e1, coeff_add, coeff_C_mul, coeff_X_mul, coeff_C_mul, e2, coeff_C_mul]
    ring
  -- the `γ` term
  have h0 : (C (gg c p zeta (k + 1)) * Q).coeff k = gg c p zeta (k + 1) * Q.coeff k := by
    rw [coeff_C_mul]
  rw [h2, h1, h0] at hode
  have hb : bb c p zeta (k + 1) = 2 * m + c + 2 * ((k : K) + 1) - 2 := by
    unfold bb
    rw [hm]
    push_cast
    ring
  have hg : gg c p zeta (k + 1) = m * (c + 2 * ((k : K) + 1) + m - 1) := by
    unfold gg
    rw [hm]
    push_cast
    ring
  rw [hb, hg] at hode
  rw [hcont]
  have e6 : ((1 : K[X]) + X) * Q = Q + X * Q := by ring
  have e7 : (1 : K[X]) * Q = Q := by ring
  rw [e6, coeff_add, coeff_X_mul, e7]
  linear_combination -hode

/-- **The write-up's (7)** for `H`, restoring the factorials that `rec_coeff` cleared.  This is
the last hypothesis of `spine`. -/
theorem Hnk_rec (c : K) (p zeta : ℕ) (hz : zeta ≤ 1) (hs : ∀ j : ℕ, step (c + 1) j ≠ 0)
    (n k : ℕ) :
    ((n : K) + c + ((2 * p + zeta : ℕ) : K)) * Hnk c p zeta (n + 1) (k + 1)
      = ((n : K) + 2 * ((k : K) + 1) + c + ((2 * p + zeta : ℕ) : K))
          * Hnk c p zeta n (k + 1)
        + ((n : K) - 2 * ((k : K) + 1) + 2 + ((2 * p + zeta : ℕ) : K))
          * Hnk c p zeta n k := by
  rcases Nat.lt_or_ge n (k + 1) with hlt | hge
  · -- `n ≤ k`: either everything vanishes, or `n = k` and the middle term drops out
    rcases Nat.lt_or_ge n k with hlt2 | hge2
    · unfold Hnk
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      ring
    · have hnk : n = k := by omega
      subst hnk
      have hedge := rec_coeff_edge c p zeta n hz hs
      unfold Hnk
      rw [if_pos (by omega), if_neg (by omega), if_pos (by omega),
        show n + 1 - (n + 1) = 0 by omega, show n - n = 0 by omega]
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, one_mul, div_one]
      have hf : ((n + 1).factorial : K) = ((n : K) + 1) * (n.factorial : K) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [hf]
      linear_combination (n.factorial : K) * hedge
  · -- `k + 1 ≤ n`: the general case, from `rec_coeff`
    obtain ⟨M, rfl⟩ : ∃ M, n = k + 1 + M := ⟨n - k - 1, by omega⟩
    have hrec := rec_coeff c p zeta k M hz hs
    have hw1 : (Wz : K[X]) ^ M * Wz = (Wz : K[X]) ^ (M + 1) := by ring
    have hw2 : (Wz : K[X]) ^ M * 1 = (Wz : K[X]) ^ M := by ring
    rw [hw1, hw2] at hrec
    unfold Hnk
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega),
      show k + 1 + M + 1 - (k + 1) = M + 1 by omega, show k + 1 + M - (k + 1) = M by omega,
      show k + 1 + M - k = M + 1 by omega]
    have hfn : (((k + 1 + M + 1).factorial : ℕ) : K)
        = (((k : K) + 1 + M) + 1) * (((k + 1 + M).factorial : ℕ) : K) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have h2ne : (2 : K) ^ M ≠ 0 := pow_ne_zero M (by norm_num)
    have hMne : ((M.factorial : ℕ) : K) ≠ 0 := factorial_ne_zero M
    have hM1 : ((M : K) + 1) ≠ 0 := by
      have hc : ((M + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      push_cast at hc
      exact hc
    -- put the middle term over the SAME denominator as the other two, so that `ring` sees one
    -- inverse atom rather than two unrelated ones
    have hmid : (((k + 1 + M).factorial : ℕ) : K) / ((2 : K) ^ M * ((M.factorial : ℕ) : K))
        = (((k + 1 + M).factorial : ℕ) : K) * (2 * ((M : K) + 1))
            / ((2 : K) ^ (M + 1) * (((M + 1).factorial : ℕ) : K)) := by
      rw [Nat.factorial_succ, pow_succ]
      push_cast
      field_simp <;> ring
    rw [hfn, hmid]
    set Dn : K := (2 : K) ^ (M + 1) * (((M + 1).factorial : ℕ) : K) with hDn
    set E : K := (((k + 1 + M).factorial : ℕ) : K) with hE
    push_cast at hrec ⊢
    linear_combination (E / Dn) * hrec

/-- `P_0(1)` is the apex sum. -/
theorem Pk_eval_one (c : K) (p zeta : ℕ) : (Pk c p zeta 0).eval 1 = Ssum c p zeta := by
  unfold Pk Ssum
  rw [eval_finset_sum]
  refine sum_congr rfl fun l hl => ?_
  rw [mem_range] at hl
  rw [eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]
  unfold aa Bt
  rw [if_pos (by omega), Nat.zero_add]

/-- `H_{0,0} = P_0(1)`, the apex of the triangle. -/
theorem Hnk_apex (c : K) (p zeta : ℕ) : Hnk c p zeta 0 0 = Ssum c p zeta := by
  unfold Hnk
  rw [if_pos (by omega), Nat.sub_zero, pow_zero, Nat.factorial_zero]
  simp only [Nat.cast_one, one_mul, mul_one, div_one, pow_zero]
  rw [coeff_zero_eq_eval_zero]
  unfold Qk
  rw [eval_comp]
  simp only [eval_add, eval_one, eval_X, add_zero]
  exact Pk_eval_one c p zeta

/-- **MathDB #355408 — Conjecture 4.20 of Maier.**  For `m = 2p + ζ` with `ζ ≤ 1`, at generic `c`,

`E_{n,k}(−1,2;c+m,m) = q (c+m)_n H_{n,k}`,  `q = (c+1)⟨p⟩ / (c+2p+2ζ)⟨p⟩`,

with `H` the write-up's array (its (4)).  This is the write-up's (2) with its right side written
through `H`; `Hnk` is `n!/(n−k)! [zᵏ] (1+z/2)^{n−k} P_k(1+z)` over `W = 2 + z`. -/
theorem main (c : K) (p zeta : ℕ) (hz : zeta ≤ 1) (hgen : ∀ j : ℕ, c + (j : K) ≠ 0) (n k : ℕ) :
    Eg (-1 : K) 2 (c + ((2 * p + zeta : ℕ) : K)) ((2 * p + zeta : ℕ) : K) n k
      = (step (c + 1) p / step (c + 2 * (p : K) + 2 * (zeta : K)) p)
        * rise (c + ((2 * p + zeta : ℕ) : K)) n * Hnk c p zeta n k := by
  have hf : ∀ j : ℕ, c + 1 + 2 * (j : K) ≠ 0 := by
    intro j h0
    refine hgen (2 * j + 1) ?_
    push_cast
    linear_combination h0
  have hf2 : ∀ j : ℕ, c + 2 * (p : K) + 2 * (zeta : K) + 2 * (j : K) ≠ 0 := by
    intro j h0
    refine hgen (2 * p + 2 * zeta + 2 * j) ?_
    push_cast
    linear_combination h0
  have hs : ∀ j : ℕ, step (c + 1) j ≠ 0 := step_ne_zero c hf
  have hsA : step (c + 1) p ≠ 0 := hs p
  have hsB : step (c + 2 * (p : K) + 2 * (zeta : K)) p ≠ 0 := by
    have hB : ∀ j : ℕ, (c + 2 * (p : K) + 2 * (zeta : K) - 1) + 1 + 2 * (j : K) ≠ 0 := by
      intro j h0
      exact hf2 j (by linear_combination h0)
    have := step_ne_zero (c + 2 * (p : K) + 2 * (zeta : K) - 1) hB p
    rwa [show c + 2 * (p : K) + 2 * (zeta : K) - 1 + 1
      = c + 2 * (p : K) + 2 * (zeta : K) by ring] at this
  refine spine c ((2 * p + zeta : ℕ) : K) _ (Hnk c p zeta) (Hnk_zero_succ c p zeta)
    (Hnk_succ_zero c p zeta) (fun n' k' => Hnk_rec c p zeta hz hs n' k') ?_ n k
  rw [Hnk_apex, apex c p zeta hz hf]
  have hstep : step (c + 2 * (p : ℕ) + 2 * (zeta : ℕ)) p
      = step (c + 2 * (p : K) + 2 * (zeta : K)) p := by
    push_cast
    ring_nf
  rw [hstep]
  field_simp

end Principia.MathDB.P355408
