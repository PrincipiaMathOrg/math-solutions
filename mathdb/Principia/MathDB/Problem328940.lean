/-
MathDB #328940 — consecutive attraction for augmented happy functions.

Fix odd `b > 2` and odd `c > 0`.  Let `σ(n)` be the sum of the SQUARES of the base-`b` digits of
`n`, and `S(n) = c + σ(n)` the augmented happy function.  Conjecture 3.3 of Baker Swart, Beck,
Crook, Eubanks-Turner, Grundman, Mei and Zack (*Augmented generalized happy functions*,
arXiv:1410.0297v2; Rocky Mountain J. Math. 47 (2017) 403–417) asks for arbitrarily long runs of
consecutive integers attracted to a given cycle.  The write-up proves the stronger statement that
every cycle basin contains a translate of *every* finite set of positive integers.

WHAT IS PROVED HERE — the write-up's own parity equation, which it flags as load-bearing.
Its equation (parity) is `S(n) ≡ n + 1 (mod 2)`, and the sentence that follows is *"Thus an
admissible map changes the parity of every input in the same way"* — that invariance is what
makes the pair-reduction lemma work at all, since it is what keeps `w mod 2` fixed.  It is
elementary and fully proved here:

* `sq_modEq_self` — `d² ≡ d (mod 2)`, the only arithmetic input;
* `digits_sum_modEq` — for ODD `b`, `n ≡ (base-b digit sum) (mod 2)`, from `b ≡ 1 (mod 2)` via
  `Nat.ofDigits_modEq'` and `Nat.ofDigits_one`;
* `sigma_modEq` — hence `σ(n) ≡ n (mod 2)`, because squaring is the identity mod 2;
* `S_modEq` — hence `S(n) ≡ n + 1 (mod 2)` for odd `c`;
* `S_preserves_diff_parity` — the form the argument actually consumes: `S` preserves whether two
  inputs have equal parity, so the `ε = w mod 2` of the pair lemma is invariant.  The other
  generator `I(n) = n + 1` shifts parity identically (`I_parity`), so every admissible map does.

ALSO PROVED — the write-up's "consequently".  `consecutiveRuns_of_conjecture33` derives the
arbitrarily-long-consecutive-runs statement from the finite-translate statement, by taking the
finite set to be `{1, …, L}`.  That is a real derivation, not a restatement.

CARRIED.  `Conjecture33` itself.  Its proof is the construction of an adjacent pair in every
basin via a congruence mod `(b−1)²` with an explicit base-`b` carry pattern, plus pair reduction
and digit-prefix lifting — none of which is in reach here.  Per the spine rule it is a named
hypothesis, never a `sorry`.
-/
import Mathlib.Data.Nat.Digits.Lemmas

set_option autoImplicit false

namespace Principia.MathDB.P328940

/-! ## 1. The function -/

/-- `σ(n)`: the sum of the squares of the base-`b` digits of `n`. -/
def sigma (b n : ℕ) : ℕ := ((Nat.digits b n).map (fun d => d ^ 2)).sum

/-- The augmented happy function `S(n) = c + σ(n)`. -/
def S (b c n : ℕ) : ℕ := c + sigma b n

/-- The other generator of an admissible map. -/
def I (n : ℕ) : ℕ := n + 1

/-! ## 2. The parity equation -/

/-- Squaring is the identity mod 2 — the only arithmetic input. -/
theorem sq_modEq_self (d : ℕ) : d ^ 2 ≡ d [MOD 2] := by
  show d ^ 2 % 2 = d % 2
  rw [pow_two, Nat.mul_mod]
  rcases Nat.mod_two_eq_zero_or_one d with h | h <;> rw [h]

theorem sum_map_sq_modEq (L : List ℕ) :
    (L.map (fun d => d ^ 2)).sum ≡ L.sum [MOD 2] := by
  induction L with
  | nil => rfl
  | cons a t ih => simpa using (sq_modEq_self a).add ih

/-- For ODD `b`, a number is congruent to its base-`b` digit sum mod 2.  (This is the mod-2 case
of the usual "digit sum mod `b − 1`" fact, and odd `b` is exactly what makes `b ≡ 1 (mod 2)`.) -/
theorem digits_sum_modEq (b n : ℕ) (hb : b % 2 = 1) :
    (Nat.digits b n).sum ≡ n [MOD 2] := by
  have h : b ≡ 1 [MOD 2] := by show b % 2 = 1 % 2; omega
  have h2 := Nat.ofDigits_modEq' b 1 2 h (Nat.digits b n)
  rw [Nat.ofDigits_one, Nat.ofDigits_digits] at h2
  exact h2.symm

theorem sigma_modEq (b n : ℕ) (hb : b % 2 = 1) : sigma b n ≡ n [MOD 2] :=
  (sum_map_sq_modEq _).trans (digits_sum_modEq b n hb)

/-- **The write-up's equation (parity)**: `S(n) ≡ n + 1 (mod 2)` for odd `b` and odd `c`. -/
theorem S_modEq (b c n : ℕ) (hb : b % 2 = 1) (hc : c % 2 = 1) :
    S b c n ≡ n + 1 [MOD 2] := by
  have hc' : c ≡ 1 [MOD 2] := by show c % 2 = 1 % 2; omega
  have h := hc'.add (sigma_modEq b n hb)
  rwa [Nat.add_comm 1 n] at h

/-- `I` shifts parity the same way `S` does. -/
theorem I_parity (n : ℕ) : I n % 2 = (n + 1) % 2 := rfl

/-- **The form the pair lemma actually consumes.**  `S` preserves whether two inputs have equal
parity, which is what keeps `ε = w mod 2` invariant under an admissible map. -/
theorem S_preserves_diff_parity (b c : ℕ) (hb : b % 2 = 1) (hc : c % 2 = 1) (m n : ℕ) :
    (S b c m % 2 = S b c n % 2) ↔ (m % 2 = n % 2) := by
  have hm : S b c m % 2 = (m + 1) % 2 := S_modEq b c m hb hc
  have hn : S b c n % 2 = (n + 1) % 2 := S_modEq b c n hb hc
  rw [hm, hn]
  omega

/-- and so does `I`, so every admissible map does. -/
theorem I_preserves_diff_parity (m n : ℕ) :
    (I m % 2 = I n % 2) ↔ (m % 2 = n % 2) := by
  rw [I_parity, I_parity]
  omega

/-! ## 3. The conjecture, and its stated consequence -/

/-- `u` is a periodic point of `S` — the write-up's "point on a cycle". -/
def IsPeriodic (b c u : ℕ) : Prop := ∃ k, 0 < k ∧ (S b c)^[k] u = u

/-- The basin of `u`: the positive integers whose orbit reaches `u`. -/
def Basin (b c u : ℕ) : Set ℕ := {n | 0 < n ∧ ∃ k, (S b c)^[k] n = u}

/-- **Conjecture 3.3**, in the write-up's strengthened form: every cycle basin contains a
translate of every finite set of positive integers. -/
def Conjecture33 (b c : ℕ) : Prop :=
  ∀ u : ℕ, IsPeriodic b c u → ∀ T : Finset ℕ, (∀ t ∈ T, 0 < t) →
    ∃ n : ℕ, ∀ t ∈ T, (t + n) ∈ Basin b c u

/-- The stated consequence: arbitrarily long runs of consecutive attracted integers. -/
def ConsecutiveRuns (b c : ℕ) : Prop :=
  ∀ u : ℕ, IsPeriodic b c u → ∀ L : ℕ, ∃ m : ℕ, 0 < m ∧ ∀ i, i < L → (m + i) ∈ Basin b c u

/-- **The write-up's "consequently", proved.**  Apply the finite-translate statement to
`{1, …, L}`; the translate is then a run of `L` consecutive integers. -/
theorem consecutiveRuns_of_conjecture33 (b c : ℕ) (h : Conjecture33 b c) :
    ConsecutiveRuns b c := by
  intro u hu L
  obtain ⟨n, hn⟩ := h u hu ((Finset.range L).image (fun i => i + 1)) (by
    intro t ht
    simp only [Finset.mem_image, Finset.mem_range] at ht
    obtain ⟨i, _, rfl⟩ := ht
    omega)
  refine ⟨1 + n, by omega, ?_⟩
  intro i hi
  have hmem : (i + 1) ∈ (Finset.range L).image (fun j => j + 1) := by
    simp only [Finset.mem_image, Finset.mem_range]
    exact ⟨i, hi, rfl⟩
  have := hn (i + 1) hmem
  have hidx : i + 1 + n = 1 + n + i := by omega
  rwa [hidx] at this

end Principia.MathDB.P328940
