import Mathlib

set_option autoImplicit false

namespace Principia.Common

open Finset

/-!
# A Rothe-type convolution depends only on the sum of its two shifts

For an integer `m`, write `A_i(x) = C(x + m·i, i)` with `C` the GENERALIZED binomial coefficient
(`Ring.choose`, a polynomial in the upper index, so nonzero at negative upper index).  The
convolution

    `F_j(x, y) = ∑_{k ≤ j} A_{j-k}(x) · A_k(y)`

**depends only on `x + y`.**  For `m = 0` this is Vandermonde; for general `m` it is the identity
that the generalized binomial series produces by Lagrange inversion, and that is how it is usually
proved.

**It does not need Lagrange inversion.**  The proof here is an induction on `j` resting on one
instance of Pascal's rule, and it is short enough to state in full:

* `A_i(x) - A_i(x-1) = A_{i-1}(x + m - 1)` (`rothe_shift`) -- this is `Ring.choose_succ_succ`
  and nothing else, because `(x-1) + m·i + 1 = x + m·i` and `(x+m-1) + m·(i-1) = x - 1 + m·i`;
* summing it against `A_k(y)` gives `F_j(x,y) - F_j(x-1,y) = F_{j-1}(x+m-1, y)`, and against
  `A_{j-k}(x)` gives `F_j(x,y+1) - F_j(x,y) = F_{j-1}(x, y+m)`;
* hence `F_j(x-1,y+1) - F_j(x,y) = F_{j-1}(x-1, y+m) - F_{j-1}(x+m-1, y)`, **whose two argument
  pairs have the same sum**, so it vanishes by the inductive hypothesis.

The base case is `F_0 = 1`.  Note the induction needs the FULL statement ("depends only on the
sum") as its hypothesis, not merely invariance under a unit shift: the step produces two pairs
differing by `m`, not by `1`.

Promoted here rather than into a campaign because it mentions nothing but `Ring.choose`.
-/

/-- `A_i(x) = C(x + m·i, i)`, the generalized binomial with its upper index shifted by `m·i`. -/
noncomputable def rothe (m : ℤ) (i : ℕ) (x : ℤ) : ℤ := Ring.choose (x + m * (i : ℤ)) i

@[simp] theorem rothe_zero (m : ℤ) (x : ℤ) : rothe m 0 x = 1 := by
  simp [rothe]

/-- The convolution `F_j(x, y) = ∑_{k ≤ j} A_{j-k}(x)·A_k(y)`. -/
noncomputable def rotheConv (m : ℤ) (j : ℕ) (x y : ℤ) : ℤ :=
  ∑ k ∈ Finset.range (j + 1), rothe m (j - k) x * rothe m k y

@[simp] theorem rotheConv_zero (m : ℤ) (x y : ℤ) : rotheConv m 0 x y = 1 := by
  simp [rotheConv]

/-- **Pascal, in the shape the induction needs.** -/
theorem rothe_shift (m : ℤ) (i : ℕ) (x : ℤ) :
    rothe m (i + 1) x - rothe m (i + 1) (x - 1) = rothe m i (x + m - 1) := by
  have hp := Ring.choose_succ_succ (x - 1 + m * ((i : ℤ) + 1)) i
  have e1 : x - 1 + m * ((i : ℤ) + 1) + 1 = x + m * ((i + 1 : ℕ) : ℤ) := by push_cast; ring
  have e2 : x - 1 + m * ((i : ℤ) + 1) = x + m - 1 + m * (i : ℤ) := by ring
  have e3 : x - 1 + m * ((i : ℤ) + 1) = x - 1 + m * ((i + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e1] at hp
  rw [e3] at hp
  simp only [rothe]
  rw [hp, ← e3, e2]
  ring

/-- The `x`-difference drops the degree. -/
theorem rotheConv_sub_left (m : ℤ) (j : ℕ) (x y : ℤ) :
    rotheConv m (j + 1) x y - rotheConv m (j + 1) (x - 1) y
      = rotheConv m j (x + m - 1) y := by
  simp only [rotheConv, ← Finset.sum_sub_distrib]
  rw [Finset.sum_range_succ]
  have hlast : rothe m (j + 1 - (j + 1)) x * rothe m (j + 1) y
      - rothe m (j + 1 - (j + 1)) (x - 1) * rothe m (j + 1) y = 0 := by
    simp
  rw [hlast, add_zero]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hkj : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hidx : j + 1 - k = (j - k) + 1 := by omega
  rw [hidx, ← sub_mul, rothe_shift]

/-- The `y`-difference drops the degree. -/
theorem rotheConv_sub_right (m : ℤ) (j : ℕ) (x y : ℤ) :
    rotheConv m (j + 1) x (y + 1) - rotheConv m (j + 1) x y
      = rotheConv m j x (y + m) := by
  simp only [rotheConv, ← Finset.sum_sub_distrib]
  rw [Finset.sum_range_succ']
  have hfirst : rothe m (j + 1 - 0) x * rothe m 0 (y + 1)
      - rothe m (j + 1 - 0) x * rothe m 0 y = 0 := by
    simp
  rw [hfirst, add_zero]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hidx : j + 1 - (k + 1) = j - k := by omega
  have hs := rothe_shift m k (y + 1)
  have e1 : y + 1 - 1 = y := by ring
  have e2 : y + 1 + m - 1 = y + m := by ring
  rw [e1, e2] at hs
  rw [hidx, ← mul_sub, hs]

/-- **The theorem: the convolution depends only on `x + y`.** -/
theorem rotheConv_eq_of_add_eq (m : ℤ) :
    ∀ (j : ℕ) (x y x' y' : ℤ), x + y = x' + y' →
      rotheConv m j x y = rotheConv m j x' y' := by
  intro j
  induction j with
  | zero => intro x y x' y' _; simp
  | succ j ih =>
    -- along a fixed sum the value does not change when `x` drops by one
    have hstep : ∀ s x : ℤ,
        rotheConv m (j + 1) x (s - x) = rotheConv m (j + 1) (x - 1) (s - (x - 1)) := by
      intro s x
      have h1 : rotheConv m (j + 1) x (s - x) - rotheConv m (j + 1) (x - 1) (s - x)
          = rotheConv m j (x + m - 1) (s - x) := rotheConv_sub_left m j x (s - x)
      have hy : s - (x - 1) = (s - x) + 1 := by ring
      have h2 : rotheConv m (j + 1) (x - 1) ((s - x) + 1)
          - rotheConv m (j + 1) (x - 1) (s - x)
          = rotheConv m j (x - 1) ((s - x) + m) := rotheConv_sub_right m j (x - 1) (s - x)
      have hsum : (x + m - 1) + (s - x) = (x - 1) + ((s - x) + m) := by ring
      have hIH := ih (x + m - 1) (s - x) (x - 1) ((s - x) + m) hsum
      rw [hy]
      linarith [h1, h2, hIH]
    -- so it is constant along the line, by induction on the integer displacement
    have hconst : ∀ (s : ℤ) (d : ℤ) (x : ℤ),
        rotheConv m (j + 1) x (s - x) = rotheConv m (j + 1) (x + d) (s - (x + d)) := by
      intro s d
      induction d using Int.induction_on with
      | zero => intro x; norm_num
      | succ k hk =>
        intro x
        have h := hstep s (x + ((k : ℤ) + 1))
        have e : x + ((k : ℤ) + 1) - 1 = x + (k : ℤ) := by ring
        rw [e] at h
        exact (hk x).trans h.symm
      | pred k hk =>
        intro x
        have h := hstep s (x + (-(k : ℤ)))
        have e : x + (-(k : ℤ)) - 1 = x + (-(k : ℤ) - 1) := by ring
        rw [e] at h
        exact (hk x).trans h
    intro x y x' y' hxy
    have h := hconst (x + y) (x' - x) x
    rw [show x + (x' - x) = x' from by ring] at h
    rw [show x + y - x = y from by ring, show x + y - x' = y' from by omega] at h
    exact h

end Principia.Common
