/-
MathDB #330197 — Polanco's Conjecture 1: the Beatty logarithm bound by `π²/6`.

For all irrational `a, b > 1`,

    |log(a/b) − ∑_{n≥1} (a{(n+1)/a} − b{(n+1)/b}) / (n(n+1))|  <  π²/6.

The write-up's route is to introduce `R(a) = ∑_{m≥1} (a/⌊am⌋ − 1/m)`, show `0 < R(a) < π²/6`,
and prove the identity `a ∑_{n≥1} {(n+1)/a}/(n(n+1)) = log a + 1 − R(a)`, so that the bracketed
quantity is exactly `R(a) − R(b)`.

WHAT IS PROVED HERE.  The whole `R`-side is proved outright, including the bound by the
conjecture's own constant `π²/6` (Mathlib's `hasSum_zeta_two`): the term identity
`a/⌊am⌋ − 1/m = {am}/(m⌊am⌋)`, its strict positivity (this is where irrationality enters — the
term vanishes exactly when `am` is an integer), the comparison `term a m ≤ 1/m²`, summability,
and `0 < R(a) ≤ π²/6`.  The series identity is the one carried hypothesis.

A SIMPLIFICATION OF THE SOURCE.  The write-up proves the STRICT bound `R(a) < π²/6`, taking care
to *"preserve the positive gap in the first term and use a non-strict upper bound for the rest"*.
That strictness is not needed: the conjecture's conclusion is about `|R(a) − R(b)|`, and
`0 < R(b)` already supplies the strict inequality (`abs_sub_lt_of_pos_of_le`).  So the
non-strict `R(a) ≤ π²/6` suffices, and no term-by-term gap argument is required.

Sibling row: `Problem330198.lean` refutes **Conjecture 2** of the same paper — the bound by `1`
on the *same* quantity `E(a,b)` — with `‖E‖ ≥ 1 + 3397/92400`, about `1.0368`, which is
consistent with the `π²/6`, about `1.6449`, proved here.  The write-up says so itself.

Reference: G. Polanco, *The logarithm of irrational numbers and Beatty sequences*, Acta Arith.
179 (2017), 101–123; preprint arXiv:1503.08512v1 (2015), Conjecture 1, p. 4 / journal p. 104.
-/
import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order

set_option autoImplicit false

namespace Principia.MathDB.P330197

/-! ## 1. The summand of `R` -/

/-- Polanco's `m`-th term `a/⌊am⌋ − 1/m`.  At `m = 0` both summands are `0` under Lean's
division convention, which matches `hasSum_zeta_two`'s indexing over all of `ℕ`. -/
noncomputable def term (a : ℝ) (m : ℕ) : ℝ := a / (⌊a * m⌋ : ℝ) - 1 / m

/-- `R(a) = ∑_{m≥1} (a/⌊am⌋ − 1/m)`, as a sum over `ℕ` whose `m = 0` term is `0`. -/
noncomputable def R (a : ℝ) : ℝ := ∑' m : ℕ, term a m

@[simp] theorem term_zero (a : ℝ) : term a 0 = 0 := by simp [term]

/-- `⌊am⌋ ≥ m`, the inequality the whole comparison rests on. -/
theorem floor_ge (a : ℝ) (ha : 1 ≤ a) (m : ℕ) : (m : ℤ) ≤ ⌊a * m⌋ := by
  rw [Int.le_floor]
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  push_cast
  nlinarith

theorem floor_pos (a : ℝ) (ha : 1 ≤ a) {m : ℕ} (hm : 1 ≤ m) : 0 < ⌊a * m⌋ := by
  have h1 := floor_ge a ha m
  have h2 : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  omega

theorem fract_eq_sub (x : ℝ) : Int.fract x = x - (⌊x⌋ : ℝ) := by
  have := Int.floor_add_fract x
  linarith

/-- The term is the fractional part over `m⌊am⌋`. -/
theorem term_eq (a : ℝ) (ha : 1 ≤ a) {m : ℕ} (hm : 1 ≤ m) :
    term a m = Int.fract (a * m) / ((m : ℝ) * (⌊a * m⌋ : ℝ)) := by
  have hF : (0 : ℤ) < ⌊a * m⌋ := floor_pos a ha hm
  have hFR : (0 : ℝ) < (⌊a * m⌋ : ℝ) := by exact_mod_cast hF
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [term, fract_eq_sub]
  -- `field_simp` closes this; a trailing `ring` would error "No goals".
  field_simp

/-- **Strict positivity, and this is the only place irrationality is used.** -/
theorem term_pos (a : ℝ) (hirr : Irrational a) (ha : 1 ≤ a) {m : ℕ} (hm : 1 ≤ m) :
    0 < term a m := by
  have hF : (0 : ℤ) < ⌊a * m⌋ := floor_pos a ha hm
  have hFR : (0 : ℝ) < (⌊a * m⌋ : ℝ) := by exact_mod_cast hF
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hirrm : Irrational (a * m) := hirr.mul_natCast (by omega)
  have hfr : Int.fract (a * m) ≠ 0 := by
    intro h
    rw [Int.fract_eq_zero_iff] at h
    obtain ⟨z, hz⟩ := h
    exact hirrm.ne_int z hz.symm
  have hpos : 0 < Int.fract (a * m) :=
    lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hfr)
  rw [term_eq a ha hm]
  exact div_pos hpos (by positivity)

theorem term_nonneg (a : ℝ) (hirr : Irrational a) (ha : 1 ≤ a) (m : ℕ) : 0 ≤ term a m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · simp [h]
  · exact (term_pos a hirr ha h).le

/-- The comparison with the Basel summand. -/
theorem term_le (a : ℝ) (ha : 1 ≤ a) (m : ℕ) : term a m ≤ 1 / (m : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos m with h | h
  · simp [h]
  · have hF : (0 : ℤ) < ⌊a * m⌋ := floor_pos a ha h
    have hFR : (0 : ℝ) < (⌊a * m⌋ : ℝ) := by exact_mod_cast hF
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast h
    have hge : (m : ℝ) ≤ (⌊a * m⌋ : ℝ) := by exact_mod_cast floor_ge a ha m
    -- `div_le_div_iff` is not available at this pin; the current name is `div_le_div_iff₀`.
    rw [term_eq a ha h, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : Int.fract (a * m) < 1 := Int.fract_lt_one _
    nlinarith

/-! ## 2. Summability and the bound by `π²/6` -/

theorem summable_basel : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 2) :=
  hasSum_zeta_two.summable

theorem summable_term (a : ℝ) (hirr : Irrational a) (ha : 1 ≤ a) : Summable (term a) :=
  Summable.of_nonneg_of_le (term_nonneg a hirr ha) (term_le a ha) summable_basel

/-- `R(a) ≤ π²/6`.  The source proves the strict form; see the header for why that is not
needed. -/
theorem R_le (a : ℝ) (hirr : Irrational a) (ha : 1 ≤ a) : R a ≤ Real.pi ^ 2 / 6 := by
  have h := (summable_term a hirr ha).tsum_le_tsum (term_le a ha) summable_basel
  rwa [hasSum_zeta_two.tsum_eq] at h

/-- `0 < R(a)`, from the single term at `m = 1`. -/
theorem R_pos (a : ℝ) (hirr : Irrational a) (ha : 1 ≤ a) : 0 < R a := by
  have h1 : term a 1 ≤ R a :=
    (summable_term a hirr ha).le_tsum 1 (fun j _ => term_nonneg a hirr ha j)
  exact lt_of_lt_of_le (term_pos a hirr ha (le_refl 1)) h1

/-! ## 3. The order step — where the source's strictness turns out to be unnecessary -/

/-- **`0 < x, y ≤ S` already gives `|x − y| < S`.**  The strictness comes from positivity of the
*other* value, not from a strict upper bound, so the write-up's term-by-term gap argument for
`R(a) < π²/6` is not needed for the conjecture. -/
theorem abs_sub_lt_of_pos_of_le {x y S : ℝ} (hx : 0 < x) (hxS : x ≤ S)
    (hy : 0 < y) (hyS : y ≤ S) : |x - y| < S := by
  rw [abs_lt]
  constructor <;> linarith

theorem abs_R_sub_lt (a b : ℝ) (hia : Irrational a) (hib : Irrational b)
    (ha : 1 ≤ a) (hb : 1 ≤ b) : |R a - R b| < Real.pi ^ 2 / 6 :=
  abs_sub_lt_of_pos_of_le (R_pos a hia ha) (R_le a hia ha) (R_pos b hib hb) (R_le b hib hb)

/-! ## 4. Polanco's Conjecture 1 -/

/-- The quantity the conjecture bounds. -/
noncomputable def E (a b : ℝ) : ℝ :=
  Real.log (a / b) -
    ∑' n : ℕ, (a * Int.fract ((n + 1) / a) - b * Int.fract ((n + 1) / b)) / ((n : ℝ) * (n + 1))

/-- Polanco's Conjecture 1 (arXiv:1503.08512v1, p. 4). -/
def Conjecture1 : Prop :=
  ∀ a b : ℝ, Irrational a → Irrational b → 1 < a → 1 < b → |E a b| < Real.pi ^ 2 / 6

/-- **The conjecture, modulo the series identity.**  `Identity` is the write-up's equation
(identity) in the combined form it is used: the bracketed quantity is `R(a) − R(b)`.  It is the
one obligation not discharged here, and it is what the finite summation identity plus the
harmonic asymptotics `H_N − H_M → log a` are for. -/
def Identity : Prop :=
  ∀ a b : ℝ, Irrational a → Irrational b → 1 < a → 1 < b → E a b = R a - R b

theorem conjecture1_of_identity (hid : Identity) : Conjecture1 := by
  intro a b hia hib ha hb
  rw [hid a b hia hib ha hb]
  exact abs_R_sub_lt a b hia hib ha.le hb.le

/-! ## 5. Not formalised: the effective remainder

The write-up also gives an *"analytic error bound, not a numerical assumption"* — truncating `R`
at `L` terms costs less than `1/L`, from `0 < R(a) − R_L(a) < ∑_{m>L} 1/m² < 1/L`.  That is NOT
proved here.  The per-term half is already `term_le`, and a lemma restricting it to `m > L` would
be a vacuous restatement — the bound holds for every `m`, so the hypothesis `L < m` goes unused
(`check_unused_hypotheses` flagged exactly that, and the wrapper was deleted rather than silenced).
The real content is the tail sum `∑_{m>L} 1/m² < 1/L`, which wants a telescoping comparison with
`1/(m(m−1))`; that is unwritten work, not absent theory. -/

end Principia.MathDB.P330197
