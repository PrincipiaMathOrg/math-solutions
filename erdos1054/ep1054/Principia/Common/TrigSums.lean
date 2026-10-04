/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TrigSumK

set_option autoImplicit false

/-!
# `lem:gotog`, `lem:couscous` and `lem:thina` — the trigonometric-sum lemmas, PROVED

Helfgott, arXiv:1501.05438, `typeI.tex` 49-457. Throughout `α = a/q + β/(qQ)` with
`(a, q) = 1`, `|β| ≤ 1`. The three bounds the minor-arc Type I lemmas consume:

* **T1 = `lem:gotog`, second bound** (`eq:betblu`): over `q` consecutive integers,
  `∑ min(A, C/sin²(παn)) ≤ 3A + (4q/π)√(AC)`. PROVED SHARPER, with `2A` (`gotog_sharp`), and in
  the book's form (`gotog`).
* **T2 = `lem:couscous`, first bound** (`eq:dijkre`): over `y₁ < n ≤ y₂`, `q ∤ n`, with
  `y₂ - y₁ ≤ q`, `y₂ ≤ Q/2`, `∑ min(A, C/sin²(παn)) ≤ (20/3π²)Cq²` (`couscous`). The hypothesis
  `q ≤ Q` of the book is not needed.
* **T3 = `lem:thina`** (`eq:shtru`): on the same range,
  `∑ min(B/|sin(παn)|, C/sin²(παn)) ≤ (2Bq/π)·max(2, log(Ce³q/(Bπ)))` (`thina`).

All three are stated for nonnegative terms `t n` obeying the bounds — `t n ≤ A`,
`t n·sin²(παn) ≤ C`, `t n·|sin(παn)| ≤ B` — which is the book's `min(…)` without the junk value
`C/0 = 0` of Lean's division at a zero of `sin`.

## The route (not the book's)

**Labels.** Each `n` gets a natural label `κ n`, injective on the range, with `‖αn‖` (distance
to the nearest integer) at least `(κ n - 1)/(2q)` (T1) or `κ n/(2q)`, `1 ≤ κ n < q` (T2, T3):
writing `qαn = an + c + ε` with `|ε| ≤ 1/2`, the residues `an mod q` are distinct, and the
interleaving `z ↦ 2z | -2z - 1` (`lab`) orders the integers by distance from `-c`. So the sum is
at most a sum over the sample points `kh`, `h = π/(2q)`, and `TrigSumK.lean` bounds those.

**Why T1 improves.** The labels give `‖αn‖ ≥ (κ - 1)/2q` with only two labels (`0`, `1`) left
unbounded, where the book bounds three residues trivially. The book's own argument also has a
small slip there: for even `q` the residue `r = q/2` is assigned distance `(q/2 - 1/2 + qδ₂)/q`,
but `qδ₂ ≤ 1/2` only gives `(q/2 - 1)/q`. The label route does not meet it.
-/

namespace Principia.Common.TrigSum

open Real Finset

/-! ## 1. Labels -/

/-- **A labelled sum**: if `t i ≤ F (κ i)` with `κ` injective into `[0, M)` and `F ≥ 0`, then
`∑ t ≤ ∑_{k < M} F k`. -/
theorem sum_le_of_label {ι : Type*} (S : Finset ι) (t : ι → ℝ) (κ : ι → ℕ) (F : ℕ → ℝ)
    (M : ℕ) (hinj : Set.InjOn κ S) (hκ : ∀ i ∈ S, κ i < M) (hF : ∀ k, 0 ≤ F k)
    (ht : ∀ i ∈ S, t i ≤ F (κ i)) : ∑ i ∈ S, t i ≤ ∑ k ∈ range M, F k := by
  calc ∑ i ∈ S, t i ≤ ∑ i ∈ S, F (κ i) := sum_le_sum ht
    _ = ∑ k ∈ S.image κ, F k := (sum_image hinj).symm
    _ ≤ ∑ k ∈ range M, F k := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro k hk
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hk
        exact mem_range.mpr (hκ i hi)
      · intro k _ _; exact hF k

/-- The interleaving label: for `b`, `z ≥ 0 ↦ 2z`, `z < 0 ↦ -2z - 1`; for `¬b`, mirrored. -/
def lab (b : Bool) (z : ℤ) : ℤ :=
  if b then (if 0 ≤ z then 2 * z else -2 * z - 1) else (if z ≤ 0 then -2 * z else 2 * z - 1)

theorem lab_nonneg (b : Bool) (z : ℤ) : 0 ≤ lab b z := by
  unfold lab; split_ifs <;> omega

theorem lab_inj (b : Bool) {z w : ℤ} (h : lab b z = lab b w) : z = w := by
  unfold lab at h; split_ifs at h <;> omega

/-- `lab b z / 2 ≤ |z + c|` when `|c| ≤ 1/2` and `b ↔ c ≥ 0`. -/
theorem lab_le_abs (b : Bool) (z : ℤ) (c : ℝ) (hc : |c| ≤ 1 / 2) (hb : b = true ↔ 0 ≤ c) :
    (lab b z : ℝ) / 2 ≤ |z + c| := by
  rw [abs_le] at hc
  unfold lab
  cases b with
  | true =>
    have hc0 : 0 ≤ c := hb.mp rfl
    simp only [if_true]
    split_ifs with hz
    · have hz' : (0 : ℝ) ≤ z := by exact_mod_cast hz
      push_cast
      rw [abs_of_nonneg (by linarith)]; linarith
    · have hz' : (z : ℝ) ≤ -1 := by exact_mod_cast (by omega : z ≤ -1)
      push_cast
      rw [abs_of_neg (by linarith)]; linarith
  | false =>
    have hc0 : c < 0 := by
      by_contra hh
      exact Bool.false_ne_true (hb.mpr (not_lt.mp hh))
    simp only [Bool.false_eq_true, if_false]
    split_ifs with hz
    · have hz' : (z : ℝ) ≤ 0 := by exact_mod_cast hz
      push_cast
      rw [abs_of_neg (by linarith)]; linarith
    · have hz' : (1 : ℝ) ≤ z := by exact_mod_cast (by omega : 1 ≤ z)
      push_cast
      rw [abs_of_pos (by linarith)]; linarith

/-- Two points of a window of length `q` whose `a`-multiples agree mod `q` coincide. -/
theorem eq_of_window (a : ℤ) (q : ℕ) (hcop : Int.gcd a q = 1) (lo n n' : ℤ)
    (hn : lo < n ∧ n ≤ lo + q) (hn' : lo < n' ∧ n' ≤ lo + q) (hd : (q : ℤ) ∣ a * n - a * n') :
    n = n' := by
  have h1 : (q : ℤ) ∣ a * (n - n') := by rw [mul_sub]; exact hd
  have h2 : (q : ℤ) ∣ n - n' :=
    Int.dvd_of_dvd_mul_right_of_gcd_one h1 (by rw [Int.gcd_comm]; exact hcop)
  have h3 : |n - n'| < q := by rw [abs_lt]; constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd h2 h3
  omega

/-- `((x.toNat : ℕ) : ℝ) = x` for `x ≥ 0`. -/
theorem cast_toNat {x : ℤ} (hx : 0 ≤ x) : ((x.toNat : ℕ) : ℝ) = (x : ℝ) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hx]

/-- **T1 labels**: over `n₀ < n ≤ n₀ + q`, an injective `κ` with
`‖αn‖ ≥ (κ n - 1)/(2q)`. -/
theorem gotog_labels (α β Q : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    (hα : α = a / q + β / (q * Q)) (hβ : |β| ≤ 1) (hqQ : (q : ℝ) ≤ Q) (n0 : ℤ) :
    ∃ κ : ℤ → ℕ, Set.InjOn κ (Ioc n0 (n0 + q)) ∧ ∀ n ∈ Ioc n0 (n0 + q),
      ((κ n : ℝ) - 1) / (2 * q) ≤ |α * n - round (α * n)| := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hQ0 : 0 < Q := lt_of_lt_of_le hq0 hqQ
  set m0 : ℝ := n0 + (q + 1) / 2 with hm0
  set c : ℝ := β * m0 / Q with hc
  set b : Bool := decide (0 ≤ c - round c) with hb
  have hc' : |c - round c| ≤ 1 / 2 := abs_sub_round c
  have hbiff : b = true ↔ 0 ≤ c - round c := by rw [hb]; exact decide_eq_true_iff
  refine ⟨fun n => (lab b (a * n - q * round (α * n) + round c)).toNat, ?_, ?_⟩
  · intro n hn n' hn' h
    simp only at h
    have h3 : lab b (a * n - q * round (α * n) + round c) =
        lab b (a * n' - q * round (α * n') + round c) := by
      rw [← Int.toNat_of_nonneg (lab_nonneg b _), h, Int.toNat_of_nonneg (lab_nonneg b _)]
    have h4 := lab_inj b h3
    apply eq_of_window a q hcop n0 n n' (mem_Ioc.mp hn) (mem_Ioc.mp hn')
    exact ⟨round (α * n) - round (α * n'), by rw [mul_sub]; linarith⟩
  · intro n hn
    obtain ⟨hn1, hn2⟩ := mem_Ioc.mp hn
    simp only
    set m := round (α * n) with hm
    set z : ℤ := a * n - q * m + round c with hz
    have hlab0 := lab_nonneg b z
    rw [cast_toNat hlab0]
    have hlo : (n0 : ℝ) + 1 ≤ n := by exact_mod_cast (by omega : n0 + 1 ≤ n)
    have hhi : (n : ℝ) ≤ n0 + q := by exact_mod_cast hn2
    -- `qαn = an + c + ε`, `|ε| ≤ 1/2`
    have hF1 : (q : ℝ) * (α * n) = a * n + c + β * (n - m0) / Q := by
      rw [hα, hc]; field_simp; ring
    have hF2 : |β * (n - m0) / Q| ≤ 1 / 2 := by
      have hd : |(n : ℝ) - m0| ≤ (q - 1) / 2 := by
        rw [abs_le]; constructor <;> linarith
      rw [abs_div, abs_mul, abs_of_pos hQ0, div_le_iff₀ hQ0]
      have := mul_le_mul hβ hd (abs_nonneg _) zero_le_one
      linarith
    have hF3 : (q : ℝ) * (α * n - m) = (z + (c - round c)) + β * (n - m0) / Q := by
      rw [hz]; push_cast; linarith
    have hF4 := lab_le_abs b z (c - round c) hc' hbiff
    have hF5 : (lab b z : ℝ) / 2 - 1 / 2 ≤ q * |α * n - m| := by
      have e : (q : ℝ) * |α * n - m| = |(z + (c - round c)) + β * (n - m0) / Q| := by
        rw [← hF3, abs_mul, abs_of_pos hq0]
      have := abs_add_le ((z : ℝ) + (c - round c) + β * (n - m0) / Q) (-(β * (n - m0) / Q))
      rw [abs_neg, add_neg_cancel_right] at this
      linarith
    rw [div_le_iff₀ (by positivity)]
    linarith

/-- **T2/T3 labels**: over `n₁ < n ≤ n₂`, `q ∤ n` (`0 ≤ n₁`, `n₂ - n₁ ≤ q`, `n₂ ≤ Q/2`), an
injective `κ` with `1 ≤ κ n < q` and `‖αn‖ ≥ κ n/(2q)`. -/
theorem couscous_labels (α β Q : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    (hα : α = a / q + β / (q * Q)) (hβ : |β| ≤ 1) (n1 n2 : ℤ) (hn1 : 0 ≤ n1)
    (hn12 : n2 - n1 ≤ q) (hn2 : (n2 : ℝ) ≤ Q / 2) :
    ∃ κ : ℤ → ℕ, Set.InjOn κ ((Ioc n1 n2).filter (fun n => ¬ (q : ℤ) ∣ n)) ∧
      ∀ n ∈ (Ioc n1 n2).filter (fun n => ¬ (q : ℤ) ∣ n),
        1 ≤ κ n ∧ κ n < q ∧ (κ n : ℝ) / (2 * q) ≤ |α * n - round (α * n)| := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hqz : (q : ℤ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  set L : ℤ → ℤ := fun n => if 0 ≤ β then min (2 * (a * n % q)) (2 * q - 2 * (a * n % q) - 1)
    else min (2 * (a * n % q) - 1) (2 * q - 2 * (a * n % q)) with hL
  -- the residue facts
  have hres : ∀ n ∈ (Ioc n1 n2).filter (fun n => ¬ (q : ℤ) ∣ n),
      1 ≤ a * n % q ∧ a * n % q < q := by
    intro n hn
    obtain ⟨-, hnd⟩ := mem_filter.mp hn
    refine ⟨?_, Int.emod_lt_of_pos _ (by omega)⟩
    have h0 := Int.emod_nonneg (a * n) hqz
    rcases h0.lt_or_eq with h | h
    · omega
    · exfalso
      apply hnd
      exact Int.dvd_of_dvd_mul_right_of_gcd_one (Int.dvd_of_emod_eq_zero h.symm)
        (by rw [Int.gcd_comm]; exact hcop)
  have hLb : ∀ n ∈ (Ioc n1 n2).filter (fun n => ¬ (q : ℤ) ∣ n), 1 ≤ L n ∧ L n ≤ q - 1 := by
    intro n hn
    obtain ⟨h1, h2⟩ := hres n hn
    simp only [hL]
    split_ifs <;> rw [min_def] <;> split_ifs <;> omega
  refine ⟨fun n => (L n).toNat, ?_, ?_⟩
  · intro n hn n' hn' h
    simp only at h
    have hL0 := (hLb n hn).1
    have hL0' := (hLb n' hn').1
    have h3 : L n = L n' := by
      rw [← Int.toNat_of_nonneg (by omega : 0 ≤ L n), h,
        Int.toNat_of_nonneg (by omega : 0 ≤ L n')]
    obtain ⟨r1, r2⟩ := hres n hn
    obtain ⟨r1', r2'⟩ := hres n' hn'
    have hr : a * n % q = a * n' % q := by
      simp only [hL] at h3
      split_ifs at h3 <;> rw [min_def, min_def] at h3 <;> split_ifs at h3 <;> omega
    have hmod : Int.ModEq q (a * n) (a * n') := hr
    have hd := hmod.dvd
    obtain ⟨hn1', -⟩ := mem_filter.mp hn
    obtain ⟨hn1'', -⟩ := mem_filter.mp hn'
    have hw := mem_Ioc.mp hn1'
    have hw' := mem_Ioc.mp hn1''
    exact (eq_of_window a q hcop n1 n' n ⟨hw'.1, by omega⟩ ⟨hw.1, by omega⟩ hd).symm
  · intro n hn
    obtain ⟨hL1, hL2⟩ := hLb n hn
    obtain ⟨r1, r2⟩ := hres n hn
    obtain ⟨hnw, -⟩ := mem_filter.mp hn
    obtain ⟨hn1l, hn2l⟩ := mem_Ioc.mp hnw
    refine ⟨?_, ?_, ?_⟩
    · show 1 ≤ (L n).toNat
      omega
    · show (L n).toNat < q
      omega
    show ((L n).toNat : ℝ) / (2 * q) ≤ |α * n - round (α * n)|
    rw [cast_toNat (by omega : 0 ≤ L n)]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hnQ : (n : ℝ) ≤ Q / 2 := le_trans (by exact_mod_cast hn2l) hn2
    have hQ0 : 0 < Q := by linarith
    set r : ℤ := a * n % q with hr
    set m := round (α * n) with hm
    set j : ℤ := m - a * n / q with hj
    have hdiv : a * n % q + q * (a * n / q) = a * n := Int.emod_add_mul_ediv (a * n) q
    have hrR : (r : ℝ) + q * ((a * n / q : ℤ) : ℝ) = (a : ℝ) * n := by
      have := congrArg (fun x : ℤ => (x : ℝ)) hdiv
      push_cast at this
      linarith
    set e : ℝ := β * n / Q with he
    have he1 : |e| ≤ 1 / 2 := by
      rw [he, abs_div, abs_mul, abs_of_pos hQ0, div_le_iff₀ hQ0,
        abs_of_pos (by linarith : (0 : ℝ) < n)]
      have := mul_le_mul_of_nonneg_right hβ (by linarith : (0 : ℝ) ≤ n)
      linarith
    rw [abs_le] at he1
    have hqa : (q : ℝ) * (α * n) = a * n + e := by
      rw [hα, he]; field_simp
    have hF : (q : ℝ) * (α * n - m) = r + e - q * j := by
      rw [mul_sub, hqa, hj]; push_cast; linarith
    have hRr1 : (1 : ℝ) ≤ r := by exact_mod_cast r1
    have hRr2 : (r : ℝ) + 1 ≤ q := by exact_mod_cast (by omega : r + 1 ≤ q)
    -- `|r + e - qj| ≥ L/2`
    have hkey : (L n : ℝ) / 2 ≤ |(r : ℝ) + e - q * j| := by
      have hLle : ((0 ≤ β) → (L n : ℝ) ≤ 2 * r ∧ (L n : ℝ) ≤ 2 * q - 2 * r - 1) ∧
          (¬ (0 ≤ β) → (L n : ℝ) ≤ 2 * r - 1 ∧ (L n : ℝ) ≤ 2 * q - 2 * r) := by
        constructor
        · intro hβ0
          have h1 : L n = min (2 * r) (2 * q - 2 * r - 1) := by simp only [hL, if_pos hβ0, hr]
          constructor
          · have := min_le_left (2 * r) (2 * (q : ℤ) - 2 * r - 1)
            rw [← h1] at this; exact_mod_cast this
          · have := min_le_right (2 * r) (2 * (q : ℤ) - 2 * r - 1)
            rw [← h1] at this; exact_mod_cast this
        · intro hβ0
          have h1 : L n = min (2 * r - 1) (2 * q - 2 * r) := by simp only [hL, if_neg hβ0, hr]
          constructor
          · have := min_le_left (2 * r - 1) (2 * (q : ℤ) - 2 * r)
            rw [← h1] at this; exact_mod_cast this
          · have := min_le_right (2 * r - 1) (2 * (q : ℤ) - 2 * r)
            rw [← h1] at this; exact_mod_cast this
      rcases le_or_gt j 0 with hj0 | hj0
      · have hjR : (j : ℝ) ≤ 0 := by exact_mod_cast hj0
        have hqj : (q : ℝ) * j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq0.le hjR
        by_cases hβ0 : 0 ≤ β
        · have he0 : 0 ≤ e := by rw [he]; positivity
          obtain ⟨k1, -⟩ := hLle.1 hβ0
          rw [abs_of_pos (by linarith)]; linarith
        · obtain ⟨k1, -⟩ := hLle.2 hβ0
          rw [abs_of_pos (by linarith)]; linarith
      · have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj0
        have hqj : (q : ℝ) ≤ q * j := by nlinarith
        by_cases hβ0 : 0 ≤ β
        · obtain ⟨-, k2⟩ := hLle.1 hβ0
          rw [abs_of_neg (by linarith)]; linarith
        · have he0 : e ≤ 0 := by
            rw [he]
            exact div_nonpos_of_nonpos_of_nonneg
              (mul_nonpos_of_nonpos_of_nonneg (le_of_lt (not_le.mp hβ0)) (by linarith))
              hQ0.le
          obtain ⟨-, k2⟩ := hLle.2 hβ0
          rw [abs_of_neg (by linarith)]; linarith
    have e2 : (q : ℝ) * |α * n - m| = |(r : ℝ) + e - q * j| := by
      rw [← hF, abs_mul, abs_of_pos hq0]
    rw [div_le_iff₀ (by positivity)]
    linarith

/-! ## 2. From a distance to a sine -/

/-- If `κ h ≤ π/2`, `κ/(2q) ≤ ‖x‖` and `h = π/(2q)`, then `sin(κh)² ≤ sin²(πx)` and
`0 < sin(κh)` (for `κ ≥ 1`). -/
theorem sin_sq_le_of_dist (x : ℝ) (q : ℕ) (hq : 1 ≤ q) (k : ℝ) (hk : 0 < k)
    (hd : k / (2 * q) ≤ |x - round x|) :
    0 < sin (k * (π / (2 * q))) ∧ sin (k * (π / (2 * q))) ≤ |sin (π * x)| := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hw := abs_sub_round x
  have hd0 : 0 < k / (2 * q) := by positivity
  have hd2 : k / (2 * q) ≤ 1 / 2 := hd.trans hw
  have e : k * (π / (2 * q)) = π * (k / (2 * q)) := by ring
  rw [e]
  refine ⟨sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [pi_pos]), ?_⟩
  exact sin_pi_le_abs_sin x (k / (2 * q)) (round x) hd0.le hd hw

/-! ## 3. The three lemmas -/

/-- **T1 — `lem:gotog`, second bound, SHARPENED to `2A`**: for `α = a/q + β/(qQ)`, `(a,q) = 1`,
`|β| ≤ 1`, `1 ≤ q ≤ Q`, and nonnegative `t` with `t n ≤ A`, `t n·sin²(παn) ≤ C` on the window,
`∑_{n₀ < n ≤ n₀ + q} t n ≤ 2A + (4q/π)√(AC)`. -/
theorem gotog_sharp (α β Q A C : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    (hα : α = a / q + β / (q * Q)) (hβ : |β| ≤ 1) (hqQ : (q : ℝ) ≤ Q) (hA : 0 ≤ A)
    (hC : 0 ≤ C) (n0 : ℤ) (t : ℤ → ℝ) (htA : ∀ n ∈ Ioc n0 (n0 + q), t n ≤ A)
    (htC : ∀ n ∈ Ioc n0 (n0 + q), t n * sin (π * (α * n)) ^ 2 ≤ C) :
    ∑ n ∈ Ioc n0 (n0 + q), t n ≤ 2 * A + 4 * q / π * √(A * C) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set h : ℝ := π / (2 * q) with hh
  have hh0 : 0 < h := by positivity
  obtain ⟨κ, hinj, hκ⟩ := gotog_labels α β Q a q hq hcop hα hβ hqQ n0
  set G : ℕ → ℝ := fun k => if k ≤ 1 then A else min A (C / sin (((k : ℝ) - 1) * h) ^ 2)
    with hG
  have hG0 : ∀ k, 0 ≤ G k := by
    intro k; simp only [hG]; split_ifs
    · exact hA
    · exact le_min hA (by positivity)
  have hκlt : ∀ n ∈ Ioc n0 (n0 + q), κ n < q + 2 := by
    intro n hn
    have h1 := (hκ n hn).trans (abs_sub_round _)
    rw [div_le_iff₀ (by positivity)] at h1
    have : (κ n : ℝ) < q + 2 := by linarith
    exact_mod_cast this
  have htG : ∀ n ∈ Ioc n0 (n0 + q), t n ≤ G (κ n) := by
    intro n hn
    simp only [hG]
    split_ifs with h1
    · exact htA n hn
    · have h2 : (2 : ℝ) ≤ κ n := by exact_mod_cast (by omega : 2 ≤ κ n)
      obtain ⟨hs0, hs1⟩ := sin_sq_le_of_dist (α * n) q hq ((κ n : ℝ) - 1) (by linarith)
        (hκ n hn)
      have hsq : sin (((κ n : ℝ) - 1) * h) ^ 2 ≤ sin (π * (α * n)) ^ 2 := by
        rw [← sq_abs (sin (π * (α * n)))]; exact pow_le_pow_left₀ hs0.le hs1 2
      have hpos : 0 < sin (π * (α * n)) ^ 2 := lt_of_lt_of_le (by positivity) hsq
      refine le_min (htA n hn) ?_
      have : t n ≤ C / sin (π * (α * n)) ^ 2 := by rw [le_div_iff₀ hpos]; exact htC n hn
      exact this.trans (div_le_div_of_nonneg_left hC (by positivity) hsq)
  have hS := sum_le_of_label _ t κ G (q + 2) hinj hκlt hG0 htG
  rw [sum_range_succ', sum_range_succ'] at hS
  have hGk : ∀ k : ℕ, G (k + 1 + 1) = min A (C / sin (((k : ℝ) + 1) * h) ^ 2) := by
    intro k; simp only [hG]
    rw [if_neg (by omega)]; push_cast; ring_nf
  simp only [hGk] at hS
  have hG1 : G (0 + 1) = A := by simp [hG]
  have hG00 : G 0 = A := by simp [hG]
  rw [hG1, hG00] at hS
  have hTA := sum_min_csc_sq_le A C h q hA hC hh0 (by rw [hh]; field_simp; ring_nf; rfl)
  have e : 2 * √(A * C) / h = 4 * q / π * √(A * C) := by rw [hh]; field_simp; ring
  rw [e] at hTA
  linarith

/-- **T1 in the book's form** (`eq:betblu`, second bound): `≤ 3A + (4q/π)√(AC)`. -/
theorem gotog (α β Q A C : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    (hα : α = a / q + β / (q * Q)) (hβ : |β| ≤ 1) (hqQ : (q : ℝ) ≤ Q) (hA : 0 ≤ A)
    (hC : 0 ≤ C) (n0 : ℤ) (t : ℤ → ℝ) (htA : ∀ n ∈ Ioc n0 (n0 + q), t n ≤ A)
    (htC : ∀ n ∈ Ioc n0 (n0 + q), t n * sin (π * (α * n)) ^ 2 ≤ C) :
    ∑ n ∈ Ioc n0 (n0 + q), t n ≤ 3 * A + 4 * q / π * √(A * C) := by
  have := gotog_sharp α β Q A C a q hq hcop hα hβ hqQ hA hC n0 t htA htC
  linarith

/-- **T2 — `lem:couscous`, first bound** (`eq:dijkre`): for `α = a/q + β/(qQ)`, `(a,q) = 1`,
`|β| ≤ 1`, integers `0 ≤ n₁`, `n₂ - n₁ ≤ q`, `n₂ ≤ Q/2`, and nonnegative `t` with
`t n·sin²(παn) ≤ C`, `∑_{n₁ < n ≤ n₂, q ∤ n} t n ≤ (20/(3π²))·C·q²`. -/
theorem couscous (α β Q C : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    (hα : α = a / q + β / (q * Q)) (hβ : |β| ≤ 1) (hC : 0 ≤ C) (n1 n2 : ℤ) (hn1 : 0 ≤ n1)
    (hn12 : n2 - n1 ≤ q) (hn2 : (n2 : ℝ) ≤ Q / 2) (t : ℤ → ℝ)
    (htC : ∀ n ∈ (Ioc n1 n2).filter (fun n => ¬ (q : ℤ) ∣ n),
      t n * sin (π * (α * n)) ^ 2 ≤ C) :
    ∑ n ∈ (Ioc n1 n2).filter (fun n => ¬ (q : ℤ) ∣ n), t n ≤ 20 / (3 * π ^ 2) * C * q ^ 2 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set h : ℝ := π / (2 * q) with hh
  obtain ⟨κ, hinj, hκ⟩ := couscous_labels α β Q a q hq hcop hα hβ n1 n2 hn1 hn12 hn2
  set F : ℕ → ℝ := fun k => if k = 0 then 0 else C / sin ((k : ℝ) * h) ^ 2 with hF
  have hF0 : ∀ k, 0 ≤ F k := by
    intro k; simp only [hF]; split_ifs
    · exact le_rfl
    · positivity
  have htF : ∀ n ∈ (Ioc n1 n2).filter (fun n => ¬ (q : ℤ) ∣ n), t n ≤ F (κ n) := by
    intro n hn
    obtain ⟨h1, -, h3⟩ := hκ n hn
    simp only [hF, if_neg (by omega : κ n ≠ 0)]
    have h1' : (0 : ℝ) < κ n := by exact_mod_cast h1
    obtain ⟨hs0, hs1⟩ := sin_sq_le_of_dist (α * n) q hq (κ n) h1' h3
    have hsq : sin ((κ n : ℝ) * h) ^ 2 ≤ sin (π * (α * n)) ^ 2 := by
      rw [← sq_abs (sin (π * (α * n)))]; exact pow_le_pow_left₀ hs0.le hs1 2
    have hpos : 0 < sin (π * (α * n)) ^ 2 := lt_of_lt_of_le (by positivity) hsq
    have : t n ≤ C / sin (π * (α * n)) ^ 2 := by rw [le_div_iff₀ hpos]; exact htC n hn
    exact this.trans (div_le_div_of_nonneg_left hC (by positivity) hsq)
  have hS := sum_le_of_label _ t κ F q hinj (fun n hn => (hκ n hn).2.1) hF0 htF
  have hR : 0 ≤ 20 / (3 * π ^ 2) * C * q ^ 2 := by positivity
  rcases Nat.lt_or_ge q 2 with hq2 | hq2
  · -- `q = 1`: the range is empty
    have hq1 : q = 1 := by omega
    have : (Ioc n1 n2).filter (fun n => ¬ (q : ℤ) ∣ n) = ∅ := by
      rw [filter_eq_empty_iff]; intro n _; rw [hq1]; simp
    rw [this, sum_empty]; exact hR
  · obtain ⟨p, rfl⟩ : ∃ p, q = p + 2 := ⟨q - 2, by omega⟩
    rw [sum_range_succ'] at hS
    have hFk : ∀ k : ℕ, F (k + 1) = C * (1 / sin (((k : ℝ) + 1) * h) ^ 2) := by
      intro k; simp only [hF, if_neg (Nat.succ_ne_zero k)]; push_cast; ring
    simp only [hFk] at hS
    rw [show F 0 = 0 by simp [hF], add_zero, ← mul_sum] at hS
    have hh4 : h ≤ π / 4 := by
      rw [hh, div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (2 : ℝ) ≤ ((p + 2 : ℕ) : ℝ) := by exact_mod_cast hq2
      nlinarith [pi_pos]
    have hM : (((p + 1 : ℕ) : ℝ) + 1 / 2) * h ≤ π / 2 := by
      rw [hh]; push_cast
      rw [show ((p : ℝ) + 1 + 1 / 2) * (π / (2 * (p + 2))) = π / 2 * ((p + 3 / 2) / (p + 2))
        by field_simp; ring]
      have : ((p : ℝ) + 3 / 2) / (p + 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      nlinarith [pi_pos]
    have hTS := sum_csc_sq_le h (p + 1) (by positivity) hh4 hM
    have e : 5 / (3 * h ^ 2) = 20 / (3 * π ^ 2) * ((p + 2 : ℕ) : ℝ) ^ 2 := by
      rw [hh]; field_simp; ring
    rw [e] at hTS
    calc ∑ n ∈ (Ioc n1 n2).filter (fun n => ¬ ((p + 2 : ℕ) : ℤ) ∣ n), t n
        ≤ C * ∑ x ∈ range (p + 1), 1 / sin (((x : ℝ) + 1) * h) ^ 2 := hS
      _ ≤ C * (20 / (3 * π ^ 2) * ((p + 2 : ℕ) : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hTS hC
      _ = 20 / (3 * π ^ 2) * C * ((p + 2 : ℕ) : ℝ) ^ 2 := by ring

/-- **T3 — `lem:thina`** (`eq:shtru`): under the hypotheses of `couscous`, for nonnegative `t`
with `t n·|sin(παn)| ≤ B` and `t n·sin²(παn) ≤ C`,
`∑_{n₁ < n ≤ n₂, q ∤ n} t n ≤ (2Bq/π)·max(2, log(Ce³q/(Bπ)))`. -/
theorem thina (α β Q B C : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    (hα : α = a / q + β / (q * Q)) (hβ : |β| ≤ 1) (hB : 0 ≤ B) (hC : 0 ≤ C) (n1 n2 : ℤ)
    (hn1 : 0 ≤ n1) (hn12 : n2 - n1 ≤ q) (hn2 : (n2 : ℝ) ≤ Q / 2) (t : ℤ → ℝ)
    (htB : ∀ n ∈ (Ioc n1 n2).filter (fun n => ¬ (q : ℤ) ∣ n), t n * |sin (π * (α * n))| ≤ B)
    (htC : ∀ n ∈ (Ioc n1 n2).filter (fun n => ¬ (q : ℤ) ∣ n),
      t n * sin (π * (α * n)) ^ 2 ≤ C) :
    ∑ n ∈ (Ioc n1 n2).filter (fun n => ¬ (q : ℤ) ∣ n), t n ≤
      2 * B * q / π * max 2 (log (C * exp 3 * q / (B * π))) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set h : ℝ := π / (2 * q) with hh
  obtain ⟨κ, hinj, hκ⟩ := couscous_labels α β Q a q hq hcop hα hβ n1 n2 hn1 hn12 hn2
  have hsinpos : ∀ k : ℕ, 0 < k → k < q → 0 < sin ((k : ℝ) * h) := by
    intro k hk hkq
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have hkq' : (k : ℝ) < q := by exact_mod_cast hkq
    apply sin_pos_of_pos_of_lt_pi (by positivity)
    rw [hh, show (k : ℝ) * (π / (2 * q)) = π * (k / (2 * q)) by ring]
    have : (k : ℝ) / (2 * q) < 1 := by rw [div_lt_one (by positivity)]; linarith
    nlinarith [pi_pos]
  set F : ℕ → ℝ := fun k => if k = 0 ∨ q ≤ k then 0 else
    min (B / sin ((k : ℝ) * h)) (C / sin ((k : ℝ) * h) ^ 2) with hF
  have hF0 : ∀ k, 0 ≤ F k := by
    intro k; simp only [hF]; split_ifs with hk
    · exact le_rfl
    · obtain ⟨hk1, hk2⟩ := not_or.mp hk
      have := hsinpos k (Nat.pos_of_ne_zero hk1) (not_le.mp hk2)
      exact le_min (by positivity) (by positivity)
  have hR : 0 ≤ 2 * B * q / π * max 2 (log (C * exp 3 * q / (B * π))) :=
    mul_nonneg (by positivity) (le_trans (by norm_num) (le_max_left _ _))
  have htF : ∀ n ∈ (Ioc n1 n2).filter (fun n => ¬ (q : ℤ) ∣ n), t n ≤ F (κ n) := by
    intro n hn
    obtain ⟨h1, h2, h3⟩ := hκ n hn
    simp only [hF, if_neg (by omega : ¬ (κ n = 0 ∨ q ≤ κ n))]
    have h1' : (0 : ℝ) < κ n := by exact_mod_cast h1
    obtain ⟨hs0, hs1⟩ := sin_sq_le_of_dist (α * n) q hq (κ n) h1' h3
    have hsq : sin ((κ n : ℝ) * h) ^ 2 ≤ sin (π * (α * n)) ^ 2 := by
      rw [← sq_abs (sin (π * (α * n)))]; exact pow_le_pow_left₀ hs0.le hs1 2
    have hpos1 : 0 < |sin (π * (α * n))| := lt_of_lt_of_le hs0 hs1
    have hpos : 0 < sin (π * (α * n)) ^ 2 := lt_of_lt_of_le (by positivity) hsq
    refine le_min ?_ ?_
    · have : t n ≤ B / |sin (π * (α * n))| := by rw [le_div_iff₀ hpos1]; exact htB n hn
      exact this.trans (div_le_div_of_nonneg_left hB hs0 hs1)
    · have : t n ≤ C / sin (π * (α * n)) ^ 2 := by rw [le_div_iff₀ hpos]; exact htC n hn
      exact this.trans (div_le_div_of_nonneg_left hC (by positivity) hsq)
  have hS := sum_le_of_label _ t κ F q hinj (fun n hn => (hκ n hn).2.1) hF0 htF
  rcases Nat.lt_or_ge q 2 with hq2 | hq2
  · have hq1 : q = 1 := by omega
    have : (Ioc n1 n2).filter (fun n => ¬ (q : ℤ) ∣ n) = ∅ := by
      rw [filter_eq_empty_iff]; intro n _; rw [hq1]; simp
    rw [this, sum_empty]; exact hR
  · obtain ⟨p, rfl⟩ : ∃ p, q = p + 2 := ⟨q - 2, by omega⟩
    rw [sum_range_succ'] at hS
    have hFk : ∀ k ∈ range (p + 1), F (k + 1) =
        min (B / sin (((k : ℝ) + 1) * h)) (C / sin (((k : ℝ) + 1) * h) ^ 2) := by
      intro k hk
      have hk' := mem_range.mp hk
      simp only [hF, if_neg (by omega : ¬ (k + 1 = 0 ∨ p + 2 ≤ k + 1))]
      push_cast; ring_nf
    rw [sum_congr rfl hFk, show F 0 = 0 by simp [hF], add_zero] at hS
    have hh4 : h ≤ π / 4 := by
      rw [hh, div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (2 : ℝ) ≤ ((p + 2 : ℕ) : ℝ) := by exact_mod_cast hq2
      nlinarith [pi_pos]
    have hM : (((p + 1 : ℕ) : ℝ) + 1 / 2) * h ≤ π / 2 := by
      rw [hh]; push_cast
      rw [show ((p : ℝ) + 1 + 1 / 2) * (π / (2 * (p + 2))) = π / 2 * ((p + 3 / 2) / (p + 2))
        by field_simp; ring]
      have : ((p : ℝ) + 3 / 2) / (p + 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      nlinarith [pi_pos]
    have hTL := sum_min_csc_le B C h (p + 1) hB hC (by positivity) hh4 hM
    have e1 : B / h = 2 * B * ((p + 2 : ℕ) : ℝ) / π := by rw [hh]; field_simp
    have e2 : C * exp 3 / (2 * B * h) = C * exp 3 * ((p + 2 : ℕ) : ℝ) / (B * π) := by
      have hq' : ((p + 2 : ℕ) : ℝ) ≠ 0 := by positivity
      have e3 : 2 * B * h = B * π / ((p + 2 : ℕ) : ℝ) := by rw [hh]; field_simp
      rw [e3, div_div_eq_mul_div]
    rw [e1, e2] at hTL
    linarith

end Principia.Common.TrigSum
