import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The truncated negative binomial series and its truncation identity

`U b d m = ∑_{p<m} C(d+p, p) b^p` is the degree-`m` truncation of `(1-b)^{-(d+1)}`, and

  `trunc : (1-b)^(d+1) * U b d (c+1) + b^(c+1) * U (1-b) c (d+1) = 1`

is the exact identity that replaces "the two truncations multiply to `1` modulo `b^(c+1)`".
Both hold over an arbitrary `CommRing`, with no `ℕ`-subtraction anywhere, so there are no
degenerate index cases.

Promoted out of the MathDB campaign (`Principia/MathDB/Problem334350.lean`), where it was
built as the combinatorial heart of Svinin's generalized power-sum identity, and then
consumed a second time by `Problem360642.lean` for Fröberg's Hilbert-coefficient
conjecture -- the two problems share nothing but this identity, which is what made the
cross-problem import it previously required a structural smell.  It mentions neither
problem, so it belongs here.

**How it is used.**  Substituting `b = u` and `b = X` for two series that are truncated
inverses of the SAME polynomial, and multiplying the two exact relations crosswise, proves
that the truncations agree to the required order without ever inverting anything or leaving
`Polynomial`/`CommRing`.  See `Problem360642.key`.
-/

namespace Principia.Common

open Finset

variable {R : Type*} [CommRing R]

/-- `U b d m = ∑_{p<m} C(d+p, p) b^p`: the truncated negative binomial series.
No `ℕ`-subtraction appears, so there are no degenerate index cases. -/
def U (b : R) (d m : ℕ) : R := ∑ p ∈ range m, ((d + p).choose p : R) * b ^ p

lemma U_succ (b : R) (d m : ℕ) :
    U b d (m + 1) = U b d m + ((d + m).choose m : R) * b ^ m := by
  simp [U, Finset.sum_range_succ]

lemma U_zero (b : R) (d : ℕ) : U b d 0 = 0 := by simp [U]

lemma U_one (b : R) (d : ℕ) : U b d 1 = 1 := by simp [U]

/-- `U x 0 m` is the geometric sum. -/
lemma U_base (x : R) (m : ℕ) : U x 0 m = ∑ p ∈ range m, x ^ p := by
  simp [U]

/-- Pascal plus the two symmetries, at the exact indices the induction needs. -/
lemma choose_pascal_symm (c d : ℕ) :
    (c + d + 2).choose (d + 1) = (c + d + 1).choose (c + 1) + (c + d + 1).choose (d + 1) := by
  have h : (c + d + 2).choose (d + 1) = (c + d + 1).choose d + (c + d + 1).choose (d + 1) := by
    have : c + d + 2 = (c + d + 1) + 1 := by omega
    rw [this, Nat.choose_succ_succ']
  have h2 : (c + d + 1).choose d = (c + d + 1).choose (c + 1) := by
    have hle : d ≤ c + d + 1 := by omega
    have := Nat.choose_symm hle
    have hsub : c + d + 1 - d = c + 1 := by omega
    rw [hsub] at this
    omega
  omega

lemma choose_symm_left (c d : ℕ) :
    (c + d + 2).choose (d + 1) = (c + d + 2).choose (c + 1) := by
  have hle : d + 1 ≤ c + d + 2 := by omega
  have := Nat.choose_symm hle
  have hsub : c + d + 2 - (d + 1) = c + 1 := by omega
  rw [hsub] at this
  omega

/-- The step lemma driving the truncation identity. -/
lemma U_step (x : R) (c d : ℕ) :
    (1 - x) * U x (c + 1) (d + 1) - U x c (d + 1)
      = -(x ^ (d + 1) * ((c + d + 1).choose (c + 1) : R)) := by
  induction d with
  | zero => simp [U_one]
  | succ d ih =>
      rw [U_succ x (c + 1) (d + 1), U_succ x c (d + 1)]
      have hcast : ((c + d + 2).choose (d + 1) : R)
          = ((c + d + 1).choose (c + 1) : R) + ((c + d + 1).choose (d + 1) : R) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → R) (choose_pascal_symm c d)
      have hcast2 : ((c + d + 2).choose (d + 1) : R) = ((c + d + 2).choose (c + 1) : R) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → R) (choose_symm_left c d)
      have e1 : c + 1 + (d + 1) = c + d + 2 := by omega
      have e2 : c + (d + 1) = c + d + 1 := by omega
      rw [e1, e2]
      have e3 : c + d + 1 + 1 = c + d + 2 := by omega
      rw [e3]
      linear_combination ih + x ^ (d + 1) * hcast - x ^ (d + 2) * hcast2

/-- The truncation identity: the write-up's display (binomial), in a form with no
`ℕ`-subtraction.  `a = c+1`, `j = d+1`. -/
theorem trunc (b : R) (c d : ℕ) :
    (1 - b) ^ (d + 1) * U b d (c + 1) + b ^ (c + 1) * U (1 - b) c (d + 1) = 1 := by
  induction c with
  | zero =>
      rw [U_one, U_base]
      have hg : (∑ p ∈ range (d + 1), (1 - b) ^ p) * ((1 - b) - 1) = (1 - b) ^ (d + 1) - 1 :=
        geom_sum_mul _ _
      linear_combination -hg
  | succ c ih =>
      rw [U_succ]
      have hstep := U_step (1 - b) c d
      have hb : (1 : R) - (1 - b) = b := by ring
      rw [hb] at hstep
      have e1 : d + (c + 1) = c + d + 1 := by omega
      rw [e1]
      linear_combination ih + b ^ (c + 1) * hstep

end Principia.Common
