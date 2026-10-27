import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# MathDB #338918 -- an alternating Turan inequality for the Euler numbers (SPINE)

Write-up `mathdb-open-problems/problems/338918/solution.tex`,
*An alternating Turan inequality for the Euler numbers*, 21 September 2026
(source audit updated 22 September 2026).
Source: A. D. Sokal, accepted manuscript, **Conjecture 3.3**.

With `sec t + tan t = sum_n E_n t^n / n!` and `e n = E n / n!`, the conjecture is

  `(-1)^(n-1) (e_n e_{n+j+k} - e_{n+j} e_{n+k}) > 0`   for `n >= 0`, `j, k >= 1`.

**The sign is written `(-1)^(n+1)`, and that is not cosmetic.**  The two exponents have the
same parity, but over `Nat` the literal `(-1)^(n-1)` truncates at `n = 0` to `(-1)^0 = 1`,
where the source means `(-1)^(-1) = -1`.  Checked: at `n = 0`, `j = k = 1` the difference
`e_0 e_2 - e_1 e_1 = -1/2`, so the naive transcription would assert a FALSE statement while
looking like the source.  This is the 215 check doing its job.

**What is proved.**  `main` is the conjecture, in full, for all `n, j, k` -- as an
IMPLICATION from the two facts the write-up itself imports from Sokal rather than proves,
which are carried as fields of `Setup`:

* `parity` -- the partial-fraction form `e n = c a^n B(n+1)` for even `n`, `L(n+1)` for odd
  `n`, with `c = 4/pi`, `a = 2/pi`, `B` the Dirichlet beta and `L` the lambda function
  (Sokal (3.3)-(3.5), (3.16));
* `sameEven` / `sameOdd` -- strict log-concavity of `(e_{2m})` and strict log-convexity of
  `(e_{2m+1})` (Sokal Proposition 3.2).

The remaining fields (`Bpos`, `Blt`, `Bstep`, `Lgt`, `Lstep`) are the write-up's own Lemma 1,
which it proves from the alternating-series and termwise bounds.  **All five are now PROVED**
here -- `beta_pos`, `beta_lt_one` and `beta_step` under `IsBeta B`, and `one_lt_lam`, `lam_step`
outright -- `IsBeta` is shown SATISFIABLE by `exists_isBeta`, and `setup_of_parity` spends all
five, so `main_of_parity` is the conjecture from the two Sokal imports alone.  The row stays
CONDITIONAL and is not counted as fully verified, because those two are still assumed.

**What the module contributes** is the write-up's Theorem proof, which is the part that is
neither classical nor imported: the cancellation of the common factor `c^2 a^(2n+j+k)`
(`diff_eq` -- the two products carry the SAME power of `a`, which is why the whole problem
collapses to a comparison of `B` and `L` values), and the parity case analysis
(`case_even_even`, `case_odd_odd`, `case_even_odd`, assembled by `main` using the symmetry
of the expression in `j` and `k`).  `B_lt_of_even` and `L_lt_of_even` iterate the two-step
monotonicity `j/2` times, which is the only inductive content.

Writing it this way made the work-list exact, and the work-list is now down to its last
item: the five `B`/`L` fields are proved, so what is still owed for this row is precisely the
two Sokal imports -- `parity` and Proposition 3.2 -- which, unlike the five, are statements
about the Euler numbers themselves and not only about `B(s) = sum_r (-1)^r/(2r+1)^s` and
`L(s) = sum_r 1/(2r+1)^s`.

Values checked first in `Campaigns/MathDB-Formalization/verify_338918.py`.
-/

namespace Principia.MathDB.P338918

variable {e B L : ℕ → ℝ} {c a : ℝ}

/-- The source's data and its two imported classical inputs. -/
structure Setup (e B L : ℕ → ℝ) (c a : ℝ) : Prop where
  cpos : 0 < c
  apos : 0 < a
  /-- Sokal (3.3)-(3.5), (3.16): `e n = c a^n B(n+1)` for even `n`, with `L` for odd `n`. -/
  parity : ∀ n, e n = c * a ^ n * (if Even n then B (n + 1) else L (n + 1))
  Bpos : ∀ s, 1 ≤ s → 0 < B s
  Blt : ∀ s, 1 ≤ s → B s < 1
  Bstep : ∀ s, 1 ≤ s → B s < B (s + 2)
  Lgt : ∀ s, 2 ≤ s → 1 < L s
  Lstep : ∀ s, 2 ≤ s → L (s + 2) < L s
  /-- Sokal Proposition 3.2: `(e_{2m})` is strictly log-concave. -/
  sameEven : ∀ m u v : ℕ, 1 ≤ u → 1 ≤ v →
    e (2 * m) * e (2 * (m + u + v)) < e (2 * (m + u)) * e (2 * (m + v))
  /-- and `(e_{2m+1})` is strictly log-convex. -/
  sameOdd : ∀ m u v : ℕ, 1 ≤ u → 1 ≤ v →
    e (2 * (m + u) + 1) * e (2 * (m + v) + 1) < e (2 * m + 1) * e (2 * (m + u + v) + 1)

/-- `F m` is the factor of `e m` other than `c a^m`. -/
noncomputable def F (B L : ℕ → ℝ) (m : ℕ) : ℝ := if Even m then B (m + 1) else L (m + 1)

theorem B_lt_of_even (S : Setup e B L c a) :
    ∀ u s : ℕ, 1 ≤ u → 1 ≤ s → B s < B (s + 2 * u) := by
  intro u
  induction u with
  | zero => intro s hu; omega
  | succ u ih =>
      intro s _ hs
      rcases Nat.eq_zero_or_pos u with rfl | hu
      · simpa using S.Bstep s hs
      · have h1 : B s < B (s + 2 * u) := ih s hu hs
        have h2 : B (s + 2 * u) < B (s + 2 * u + 2) := S.Bstep _ (by omega)
        have : s + 2 * u + 2 = s + 2 * (u + 1) := by omega
        rw [this] at h2
        linarith

theorem L_lt_of_even (S : Setup e B L c a) :
    ∀ u s : ℕ, 1 ≤ u → 2 ≤ s → L (s + 2 * u) < L s := by
  intro u
  induction u with
  | zero => intro s hu; omega
  | succ u ih =>
      intro s _ hs
      rcases Nat.eq_zero_or_pos u with rfl | hu
      · simpa using S.Lstep s hs
      · have h1 : L (s + 2 * u) < L s := ih s hu hs
        have h2 : L (s + 2 * u + 2) < L (s + 2 * u) := S.Lstep _ (by omega)
        have : s + 2 * u + 2 = s + 2 * (u + 1) := by omega
        rw [this] at h2
        linarith

/-- The common positive factor `c^2 a^{2n+j+k}` cancels from both products. -/
theorem diff_eq (S : Setup e B L c a) (n j k : ℕ) :
    e n * e (n + j + k) - e (n + j) * e (n + k)
      = c ^ 2 * (a ^ n * a ^ (n + j + k))
        * (F B L n * F B L (n + j + k) - F B L (n + j) * F B L (n + k)) := by
  have h : a ^ (n + j) * a ^ (n + k) = a ^ n * a ^ (n + j + k) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [S.parity n, S.parity (n + j + k), S.parity (n + j), S.parity (n + k)]
  simp only [F]
  set p := (if Even n then B (n + 1) else L (n + 1))
  set q := (if Even (n + j + k) then B (n + j + k + 1) else L (n + j + k + 1))
  set r := (if Even (n + j) then B (n + j + 1) else L (n + j + 1))
  set t := (if Even (n + k) then B (n + k + 1) else L (n + k + 1))
  linear_combination (-(c ^ 2 * r * t)) * h

theorem cfac_pos (S : Setup e B L c a) (n j k : ℕ) :
    0 < c ^ 2 * (a ^ n * a ^ (n + j + k)) := by
  have h1 : 0 < c ^ 2 := pow_pos S.cpos 2
  have h2 : 0 < a ^ n := pow_pos S.apos n
  have h3 : 0 < a ^ (n + j + k) := pow_pos S.apos _
  positivity

/-- The write-up's cancellation, in the form the sign argument consumes. -/
theorem sign_of_diff (S : Setup e B L c a) (n j k : ℕ)
    (h : F B L n * F B L (n + j + k) - F B L (n + j) * F B L (n + k) < 0) :
    e n * e (n + j + k) - e (n + j) * e (n + k) < 0 := by
  rw [diff_eq S]
  exact mul_neg_of_pos_of_neg (cfac_pos S n j k) h

theorem sign_of_diff' (S : Setup e B L c a) (n j k : ℕ)
    (h : 0 < F B L n * F B L (n + j + k) - F B L (n + j) * F B L (n + k)) :
    0 < e n * e (n + j + k) - e (n + j) * e (n + k) := by
  rw [diff_eq S]
  exact mul_pos (cfac_pos S n j k) h

theorem F_even (m : ℕ) (h : Even m) : F B L m = B (m + 1) := by
  simp [F, h]

theorem F_odd (m : ℕ) (h : ¬ Even m) : F B L m = L (m + 1) := by
  simp [F, h]

/-- `j` and `k` both even: the same-parity log-concavity/convexity of the source. -/
theorem case_even_even (S : Setup e B L c a) (n j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k)
    (hje : Even j) (hke : Even k) :
    0 < (-1 : ℝ) ^ (n + 1) * (e n * e (n + j + k) - e (n + j) * e (n + k)) := by
  obtain ⟨u, hu⟩ := hje
  obtain ⟨v, hv⟩ := hke
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨m, hm⟩ := hn
    have hs : ((-1 : ℝ)) ^ (n + 1) = -1 := Odd.neg_one_pow ⟨m, by omega⟩
    have h1 : n = 2 * m := by omega
    have h2 : n + j + k = 2 * (m + u + v) := by omega
    have h3 : n + j = 2 * (m + u) := by omega
    have h4 : n + k = 2 * (m + v) := by omega
    rw [hs, h2, h3, h4, h1]
    have := S.sameEven m u v (by omega) (by omega)
    linarith
  · obtain ⟨m, hm⟩ := hn
    have hs : ((-1 : ℝ)) ^ (n + 1) = 1 := Even.neg_one_pow ⟨m + 1, by omega⟩
    have h1 : n = 2 * m + 1 := by omega
    have h2 : n + j + k = 2 * (m + u + v) + 1 := by omega
    have h3 : n + j = 2 * (m + u) + 1 := by omega
    have h4 : n + k = 2 * (m + v) + 1 := by omega
    rw [hs, h2, h3, h4, h1]
    have := S.sameOdd m u v (by omega) (by omega)
    linarith

/-- `j` and `k` both odd: a product of two `B` values is below `1`, a product of two `L`
values is above it. -/
theorem case_odd_odd (S : Setup e B L c a) (n j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k)
    (hjo : ¬ Even j) (hko : ¬ Even k) :
    0 < (-1 : ℝ) ^ (n + 1) * (e n * e (n + j + k) - e (n + j) * e (n + k)) := by
  have hjk : Even (j + k) := Odd.add_odd (Nat.not_even_iff_odd.mp hjo)
    (Nat.not_even_iff_odd.mp hko)
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨m, hm⟩ := hn
    have hs : ((-1 : ℝ)) ^ (n + 1) = -1 := Odd.neg_one_pow ⟨m, by omega⟩
    have e1 : F B L n = B (n + 1) := F_even n ⟨m, by omega⟩
    have e2 : F B L (n + j + k) = B (n + j + k + 1) := F_even _ (by
      obtain ⟨w, hw⟩ := hjk; exact ⟨m + w, by omega⟩)
    have e3 : F B L (n + j) = L (n + j + 1) := F_odd _ (by
      rw [Nat.not_even_iff_odd]
      obtain ⟨w, hw⟩ := Nat.not_even_iff_odd.mp hjo
      exact ⟨m + w, by omega⟩)
    have e4 : F B L (n + k) = L (n + k + 1) := F_odd _ (by
      rw [Nat.not_even_iff_odd]
      obtain ⟨w, hw⟩ := Nat.not_even_iff_odd.mp hko
      exact ⟨m + w, by omega⟩)
    have hb1 := S.Bpos (n + 1) (by omega)
    have hb2 := S.Blt (n + 1) (by omega)
    have hb3 := S.Bpos (n + j + k + 1) (by omega)
    have hb4 := S.Blt (n + j + k + 1) (by omega)
    have hl1 := S.Lgt (n + j + 1) (by omega)
    have hl2 := S.Lgt (n + k + 1) (by omega)
    have hneg : F B L n * F B L (n + j + k) - F B L (n + j) * F B L (n + k) < 0 := by
      rw [e1, e2, e3, e4]; nlinarith
    have := sign_of_diff S n j k hneg
    rw [hs]; linarith
  · obtain ⟨m, hm⟩ := hn
    have hs : ((-1 : ℝ)) ^ (n + 1) = 1 := Even.neg_one_pow ⟨m + 1, by omega⟩
    have e1 : F B L n = L (n + 1) := F_odd n (by
      rw [Nat.not_even_iff_odd]; exact ⟨m, by omega⟩)
    have e2 : F B L (n + j + k) = L (n + j + k + 1) := F_odd _ (by
      rw [Nat.not_even_iff_odd]
      obtain ⟨w, hw⟩ := hjk; exact ⟨m + w, by omega⟩)
    have e3 : F B L (n + j) = B (n + j + 1) := F_even _ (by
      obtain ⟨w, hw⟩ := Nat.not_even_iff_odd.mp hjo; exact ⟨m + w + 1, by omega⟩)
    have e4 : F B L (n + k) = B (n + k + 1) := F_even _ (by
      obtain ⟨w, hw⟩ := Nat.not_even_iff_odd.mp hko; exact ⟨m + w + 1, by omega⟩)
    have hl1 := S.Lgt (n + 1) (by omega)
    have hl2 := S.Lgt (n + j + k + 1) (by omega)
    have hb1 := S.Bpos (n + j + 1) (by omega)
    have hb2 := S.Blt (n + j + 1) (by omega)
    have hb3 := S.Bpos (n + k + 1) (by omega)
    have hb4 := S.Blt (n + k + 1) (by omega)
    have hpos : 0 < F B L n * F B L (n + j + k) - F B L (n + j) * F B L (n + k) := by
      rw [e1, e2, e3, e4]; nlinarith
    have := sign_of_diff' S n j k hpos
    rw [hs]; linarith

/-- `j` even, `k` odd: the two comparisons come from iterating the source's two-step
monotonicity `j/2` times, in opposite directions for `B` and for `L`. -/
theorem case_even_odd (S : Setup e B L c a) (n j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k)
    (hje : Even j) (hko : ¬ Even k) :
    0 < (-1 : ℝ) ^ (n + 1) * (e n * e (n + j + k) - e (n + j) * e (n + k)) := by
  obtain ⟨u, hu⟩ := hje
  have hu1 : 1 ≤ u := by omega
  obtain ⟨w, hw⟩ := Nat.not_even_iff_odd.mp hko
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨m, hm⟩ := hn
    have hs : ((-1 : ℝ)) ^ (n + 1) = -1 := Odd.neg_one_pow ⟨m, by omega⟩
    have e1 : F B L n = B (n + 1) := F_even n ⟨m, by omega⟩
    have e3 : F B L (n + j) = B (n + j + 1) := F_even _ ⟨m + u, by omega⟩
    have e4 : F B L (n + k) = L (n + k + 1) := F_odd _ (by
      rw [Nat.not_even_iff_odd]; exact ⟨m + w, by omega⟩)
    have e2 : F B L (n + j + k) = L (n + j + k + 1) := F_odd _ (by
      rw [Nat.not_even_iff_odd]; exact ⟨m + u + w, by omega⟩)
    have hB : B (n + 1) < B (n + j + 1) := by
      have h := B_lt_of_even S u (n + 1) hu1 (by omega)
      have hx : n + 1 + 2 * u = n + j + 1 := by omega
      rwa [hx] at h
    have hL : L (n + j + k + 1) < L (n + k + 1) := by
      have h := L_lt_of_even S u (n + k + 1) hu1 (by omega)
      have hx : n + k + 1 + 2 * u = n + j + k + 1 := by omega
      rwa [hx] at h
    have hb0 := S.Bpos (n + 1) (by omega)
    have hl0 := S.Lgt (n + j + k + 1) (by omega)
    have hneg : F B L n * F B L (n + j + k) - F B L (n + j) * F B L (n + k) < 0 := by
      rw [e1, e2, e3, e4]; nlinarith
    have := sign_of_diff S n j k hneg
    rw [hs]; linarith
  · obtain ⟨m, hm⟩ := hn
    have hs : ((-1 : ℝ)) ^ (n + 1) = 1 := Even.neg_one_pow ⟨m + 1, by omega⟩
    have e1 : F B L n = L (n + 1) := F_odd n (by
      rw [Nat.not_even_iff_odd]; exact ⟨m, by omega⟩)
    have e3 : F B L (n + j) = L (n + j + 1) := F_odd _ (by
      rw [Nat.not_even_iff_odd]; exact ⟨m + u, by omega⟩)
    have e4 : F B L (n + k) = B (n + k + 1) := F_even _ ⟨m + w + 1, by omega⟩
    have e2 : F B L (n + j + k) = B (n + j + k + 1) := F_even _ ⟨m + u + w + 1, by omega⟩
    have hL : L (n + j + 1) < L (n + 1) := by
      have h := L_lt_of_even S u (n + 1) hu1 (by omega)
      have hx : n + 1 + 2 * u = n + j + 1 := by omega
      rwa [hx] at h
    have hB : B (n + k + 1) < B (n + j + k + 1) := by
      have h := B_lt_of_even S u (n + k + 1) hu1 (by omega)
      have hx : n + k + 1 + 2 * u = n + j + k + 1 := by omega
      rwa [hx] at h
    have hb0 := S.Bpos (n + k + 1) (by omega)
    have hl0 := S.Lgt (n + j + 1) (by omega)
    have hpos : 0 < F B L n * F B L (n + j + k) - F B L (n + j) * F B L (n + k) := by
      rw [e1, e2, e3, e4]; nlinarith
    have := sign_of_diff' S n j k hpos
    rw [hs]; linarith

/-- **The write-up's Theorem (Sokal Conjecture 3.3).**  For all `n ≥ 0` and `j, k ≥ 1`,
`(-1)^{n-1}(e_n e_{n+j+k} - e_{n+j} e_{n+k}) > 0`.  The sign is written `(-1)^{n+1}`,
which has the same parity: over `ℕ` the literal `(-1)^{n-1}` would read `(-1)^0 = 1` at
`n = 0` and state the OPPOSITE of the source, whose value there is `-1`. -/
theorem main (S : Setup e B L c a) (n j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    0 < (-1 : ℝ) ^ (n + 1) * (e n * e (n + j + k) - e (n + j) * e (n + k)) := by
  by_cases hje : Even j
  · by_cases hke : Even k
    · exact case_even_even S n j k hj hk hje hke
    · exact case_even_odd S n j k hj hk hje hke
  · by_cases hke : Even k
    · have hsym : e n * e (n + j + k) - e (n + j) * e (n + k)
          = e n * e (n + k + j) - e (n + k) * e (n + j) := by
        rw [show n + j + k = n + k + j from by omega]; ring
      rw [hsym]
      exact case_even_odd S n k j hk hj hke hje
    · exact case_odd_odd S n j k hj hk hje hke

/-! ### Two of the seven carried fields, discharged

`L` is absolutely convergent on the whole range the spine uses (`s ≥ 2`), so it is a genuine
`tsum` and `Lgt`/`Lstep` can be proved outright.  **`B` cannot be written as a `tsum` at
all**: at `s = 1` the series `∑ (-1)^r/(2r+1)` is only CONDITIONALLY convergent (its sum is
`π/4`, Leibniz), so `Summable` fails and `tsum` would return its junk value `0`.  Mathlib
carries that series as a limit of partial sums, `Real.tendsto_sum_pi_div_four` in
`Mathlib/Analysis/Real/Pi/Leibniz.lean`, and the `B` fields therefore need a
`Filter.Tendsto` formulation rather than a `tsum` one.  The spine uses `B (n+1)` with
`n ≥ 0`, so `s = 1` is genuinely in range and cannot be sidestepped.
-/

/-- `lam s = ∑_{r≥0} 1/(2r+1)^s`, the lambda function.  Absolutely convergent for `s ≥ 2`,
which is the whole range the spine's `L` fields use. -/
noncomputable def lam (s : ℕ) : ℝ := ∑' r : ℕ, (1 : ℝ) / ((2 * r + 1 : ℕ) : ℝ) ^ s

theorem lam_summable (s : ℕ) (hs : 2 ≤ s) :
    Summable (fun r : ℕ => (1 : ℝ) / ((2 * r + 1 : ℕ) : ℝ) ^ s) := by
  have hbase : Summable (fun r : ℕ => (1 : ℝ) / ((r : ℝ) + 1) ^ 2) := by
    have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    refine ((summable_nat_add_iff 1).2 h).congr (fun r => ?_)
    push_cast
    ring_nf
  refine Summable.of_nonneg_of_le (fun r => by positivity) (fun r => ?_) hbase
  have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have h1 : (0 : ℝ) < ((r : ℝ) + 1) ^ 2 := by positivity
  have h2 : ((r : ℝ) + 1) ≤ ((2 * r + 1 : ℕ) : ℝ) := by push_cast; linarith
  have h3 : ((r : ℝ) + 1) ^ 2 ≤ ((2 * r + 1 : ℕ) : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by linarith) h2 2
  have h4 : ((2 * r + 1 : ℕ) : ℝ) ^ 2 ≤ ((2 * r + 1 : ℕ) : ℝ) ^ s := by
    refine pow_le_pow_right₀ ?_ hs
    push_cast
    linarith
  exact one_div_le_one_div_of_le h1 (by linarith)

theorem one_lt_lam (s : ℕ) (hs : 2 ≤ s) : 1 < lam s := by
  have hsum := lam_summable s hs
  have htail : Summable (fun r : ℕ => (1 : ℝ) / ((2 * (r + 1) + 1 : ℕ) : ℝ) ^ s) :=
    (summable_nat_add_iff 1).2 hsum
  have hT : (0 : ℝ) < ∑' r : ℕ, (1 : ℝ) / ((2 * (r + 1) + 1 : ℕ) : ℝ) ^ s := by
    have h := Summable.tsum_lt_tsum_of_nonneg (i := 0) (f := fun _ : ℕ => (0 : ℝ))
      (fun _ => le_refl 0) (fun r => by positivity) (by positivity) htail
    simpa using h
  rw [lam, hsum.tsum_eq_zero_add]
  have h0 : (1 : ℝ) / ((2 * 0 + 1 : ℕ) : ℝ) ^ s = 1 := by norm_num
  rw [h0]
  linarith

theorem lam_step (s : ℕ) (hs : 2 ≤ s) : lam (s + 2) < lam s := by
  have h1 := lam_summable (s + 2) (by omega)
  have h2 := lam_summable s hs
  rw [lam, lam]
  refine Summable.tsum_lt_tsum_of_nonneg (i := 1) (fun r => by positivity) (fun r => ?_) ?_ h2
  · have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    have hb : (1 : ℝ) ≤ ((2 * r + 1 : ℕ) : ℝ) := by push_cast; linarith
    have hp : (0 : ℝ) < ((2 * r + 1 : ℕ) : ℝ) ^ s := by
      have : (0 : ℝ) < ((2 * r + 1 : ℕ) : ℝ) := by linarith
      positivity
    exact one_div_le_one_div_of_le hp (pow_le_pow_right₀ hb (by omega))
  · have h3 : ((2 * 1 + 1 : ℕ) : ℝ) = 3 := by norm_num
    rw [h3]
    have hp : (0 : ℝ) < (3 : ℝ) ^ s := by positivity
    exact one_div_lt_one_div_of_lt hp (pow_lt_pow_right₀ (by norm_num) (by omega))

open Filter

/-! ### Two more carried fields, discharged: `Bpos` and `Blt`

`B` is carried as the LIMIT of its alternating partial sums rather than as a `tsum`, for the
reason recorded above.  Mathlib's alternating-series partial-sum bounds
(`Antitone.alternating_series_le_tendsto`, `Antitone.tendsto_le_alternating_series`) then
bracket `B s` between consecutive partial sums, and the first three of them already give
both bounds: `1 - 3^{-s} ≤ B s ≤ 1 - 3^{-s} + 5^{-s}`, with `3^{-s} < 1` and
`5^{-s} < 3^{-s}` for `s ≥ 1`.
-/

/-- The Dirichlet beta terms `a_r = 1/(2r+1)^s`. -/
noncomputable def bterm (s r : ℕ) : ℝ := 1 / ((2 * r + 1 : ℕ) : ℝ) ^ s

theorem bterm_pos (s r : ℕ) : 0 < bterm s r := by
  rw [bterm]
  have : (0 : ℝ) < ((2 * r + 1 : ℕ) : ℝ) := by positivity
  positivity

theorem bterm_antitone (s : ℕ) : Antitone (bterm s) := by
  intro a b hab
  rw [bterm, bterm]
  have h1 : (0 : ℝ) < ((2 * a + 1 : ℕ) : ℝ) ^ s := by
    have : (0 : ℝ) < ((2 * a + 1 : ℕ) : ℝ) := by positivity
    positivity
  refine one_div_le_one_div_of_le h1 ?_
  refine pow_le_pow_left₀ (le_of_lt (by positivity)) ?_ s
  exact_mod_cast Nat.cast_le.2 (by omega : 2 * a + 1 ≤ 2 * b + 1)

theorem bterm_tendsto (s : ℕ) (hs : 1 ≤ s) : Tendsto (bterm s) atTop (nhds 0) := by
  refine squeeze_zero (fun r => le_of_lt (bterm_pos s r)) (fun r => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  rw [bterm]
  have hr : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  refine one_div_le_one_div_of_le hr ?_
  calc ((r : ℝ) + 1) ≤ ((2 * r + 1 : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) r]
    _ = ((2 * r + 1 : ℕ) : ℝ) ^ 1 := (pow_one _).symm
    _ ≤ ((2 * r + 1 : ℕ) : ℝ) ^ s := by
        refine pow_le_pow_right₀ ?_ hs
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) r]

/-- `B s` is the LIMIT of the alternating partial sums.  It is deliberately NOT a `tsum`:
at `s = 1` this is the Leibniz series for `π/4`, which converges only conditionally, so
`Summable` is false there and `∑'` would silently return its junk value `0`. -/
def IsBeta (B : ℕ → ℝ) : Prop :=
  ∀ s : ℕ, 1 ≤ s →
    Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * bterm s i) atTop
      (nhds (B s))

variable {B : ℕ → ℝ}

theorem three_pow_lt (s : ℕ) (hs : 1 ≤ s) : (1 : ℝ) < 3 ^ s := by
  calc (1 : ℝ) < 3 := by norm_num
    _ = 3 ^ 1 := (pow_one 3).symm
    _ ≤ 3 ^ s := pow_le_pow_right₀ (by norm_num) hs

theorem bterm_one (s : ℕ) : bterm s 1 = 1 / 3 ^ s := by
  rw [bterm]; norm_num

theorem bterm_two (s : ℕ) : bterm s 2 = 1 / 5 ^ s := by
  rw [bterm]; norm_num

theorem bterm_zero (s : ℕ) : bterm s 0 = 1 := by
  rw [bterm]; norm_num

/-- **`0 < B s`** for `s ≥ 1`: the second partial sum `1 - 3^{-s}` is a lower bound. -/
theorem beta_pos (h : IsBeta B) (s : ℕ) (hs : 1 ≤ s) : 0 < B s := by
  have hb := Antitone.alternating_series_le_tendsto (h s hs) (bterm_antitone s) 1
  rw [show 2 * 1 = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_one] at hb
  rw [bterm_zero, bterm_one] at hb
  have h3 := three_pow_lt s hs
  have h3p : (0 : ℝ) < 3 ^ s := by positivity
  have : (1 : ℝ) / 3 ^ s < 1 := by
    rw [div_lt_one h3p]; exact h3
  simp only [pow_zero, one_mul, pow_one] at hb
  linarith

/-- **`B s < 1`** for `s ≥ 1`: the third partial sum `1 - 3^{-s} + 5^{-s}` is an upper
bound, and `5^{-s} < 3^{-s}`. -/
theorem beta_lt_one (h : IsBeta B) (s : ℕ) (hs : 1 ≤ s) : B s < 1 := by
  have hb := Antitone.tendsto_le_alternating_series (h s hs) (bterm_antitone s) 1
  rw [show 2 * 1 + 1 = 3 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one] at hb
  rw [bterm_zero, bterm_one, bterm_two] at hb
  have h3p : (0 : ℝ) < 3 ^ s := by positivity
  have h5p : (0 : ℝ) < 5 ^ s := by positivity
  have hlt : (1 : ℝ) / 5 ^ s < 1 / 3 ^ s := by
    refine one_div_lt_one_div_of_lt h3p ?_
    exact pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  simp only [pow_zero, one_mul, pow_one, pow_two] at hb
  linarith

/-! ### The third `B` field: `Bstep`

The write-up derives `B s < B (s+2)` by pairing the terms of the DIFFERENCE series, whose
terms `h_s(2r+1) = (2r+1)^{-s} - (2r+1)^{-s-2}` are antitone only from index `1` (they
start at `h_s(1) = 0`), so Mathlib's partial-sum bounds -- which need global `Antitone` --
do not apply without an index shift.  None of that is needed: the two bracket bounds
already proved SEPARATE the two values, since `9 · 3^s < 8 · 5^s` gives
`1 - 3^{-s} + 5^{-s} < 1 - 3^{-(s+2)}`.
-/

/-- The second partial sum is a lower bound. -/
theorem beta_lower (h : IsBeta B) (s : ℕ) (hs : 1 ≤ s) : 1 - 1 / 3 ^ s ≤ B s := by
  have hb := Antitone.alternating_series_le_tendsto (h s hs) (bterm_antitone s) 1
  rw [show 2 * 1 = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_one,
    bterm_zero, bterm_one] at hb
  simpa using hb

/-- The third partial sum is an upper bound. -/
theorem beta_upper (h : IsBeta B) (s : ℕ) (hs : 1 ≤ s) :
    B s ≤ 1 - 1 / 3 ^ s + 1 / 5 ^ s := by
  have hb := Antitone.tendsto_le_alternating_series (h s hs) (bterm_antitone s) 1
  rw [show 2 * 1 + 1 = 3 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, bterm_zero, bterm_one, bterm_two] at hb
  simp only [pow_zero, one_mul, pow_one, pow_two, neg_mul, one_mul] at hb
  linarith

/-- `9 * 3^s < 8 * 5^s` for `s ≥ 1`, the only arithmetic the step lemma needs. -/
theorem nine_three_lt (s : ℕ) (hs : 1 ≤ s) : 9 * (3 : ℝ) ^ s < 8 * 5 ^ s := by
  induction s with
  | zero => omega
  | succ s ih =>
      rcases Nat.eq_zero_or_pos s with rfl | hpos
      · norm_num
      · have h := ih hpos
        have h5 : (0 : ℝ) < 5 ^ s := by positivity
        rw [pow_succ, pow_succ]
        nlinarith

/-- **`B s < B (s+2)`**, the write-up's Lemma 1 step, from the SAME two bracket bounds:
`B s ≤ 1 - 3^{-s} + 5^{-s}` and `1 - 3^{-(s+2)} ≤ B (s+2)`, separated because
`9 · 3^s < 8 · 5^s`. -/
theorem beta_step (h : IsBeta B) (s : ℕ) (hs : 1 ≤ s) : B s < B (s + 2) := by
  have hup := beta_upper h s hs
  have hlow := beta_lower h (s + 2) (by omega)
  have h3 : (0 : ℝ) < 3 ^ s := by positivity
  have h5 : (0 : ℝ) < 5 ^ s := by positivity
  have hkey : 1 - 1 / (3 : ℝ) ^ s + 1 / 5 ^ s < 1 - 1 / 3 ^ (s + 2) := by
    have hn := nine_three_lt s hs
    rw [show (3 : ℝ) ^ (s + 2) = 9 * 3 ^ s from by ring]
    have h9 : (0 : ℝ) < 9 * 3 ^ s := by positivity
    have step : 1 / (5 : ℝ) ^ s + 1 / (9 * 3 ^ s) < 1 / 3 ^ s := by
      rw [div_add_div _ _ (ne_of_gt h5) (ne_of_gt h9),
        div_lt_div_iff₀ (by positivity) h3]
      nlinarith [mul_lt_mul_of_pos_right hn h3, h3, h5]
    linarith
  linarith

section Assembly

/-! ### `IsBeta` is SATISFIABLE, and the five fields are now spent

Two things were missing after the five `B`/`L` fields were discharged, and neither is a
mathematical gap in the write-up — both are gaps in the Lean.

**First, nothing proved `IsBeta` non-vacuous.**  Every `B` field above is stated under
`IsBeta B`, which *characterises* `B` as the limit of the alternating partial sums but never
exhibits one; an unsatisfiable spec would make all five theorems vacuously true.  It is
satisfiable, and the module already contained both halves of the proof: `bterm_antitone` and
`bterm_tendsto` are exactly the hypotheses of Mathlib's alternating series test
(`Antitone.tendsto_alternating_series_of_tendsto_zero`), whose conclusion is literally
`IsBeta`'s body.  `exists_isBeta` assembles them.  Note this is where the `tsum`-free design
pays: the test needs only antitone terms tending to zero, so it covers `s = 1`, where the
series is Leibniz's and `Summable` is false.

**Second, the five discharged fields were consumed by nothing.**  `Setup` still demanded all
seven, so `main` could not see that five of them were theorems.  `setup_of_parity` builds a
`Setup` from `IsBeta B` plus only `parity`, `sameEven` and `sameOdd`, and `main_of_parity` is
then the conjecture itself from **three** carried facts instead of seven — and the three that
remain are exactly the ones the write-up imports from Sokal rather than proving.
-/

theorem exists_tendsto_alt (s : ℕ) (hs : 1 ≤ s) :
    ∃ l : ℝ, Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * bterm s i) atTop
      (nhds l) :=
  (bterm_antitone s).tendsto_alternating_series_of_tendsto_zero (bterm_tendsto s hs)

/-- **`IsBeta` is satisfiable.**  Without this every `B` field above could be vacuous. -/
theorem exists_isBeta : ∃ B : ℕ → ℝ, IsBeta B := by
  have h : ∀ s : ℕ, ∃ l : ℝ, 1 ≤ s →
      Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * bterm s i) atTop (nhds l) := by
    intro s
    rcases Nat.lt_or_ge s 1 with hs | hs
    · exact ⟨0, fun h => absurd h (by omega)⟩
    · obtain ⟨l, hl⟩ := exists_tendsto_alt s hs
      exact ⟨l, fun _ => hl⟩
  choose B hB using h
  exact ⟨B, fun s hs => hB s hs⟩

/-- **Five of `Setup`'s seven fields are now theorems.**  What remains to be supplied is
`parity` and the two Sokal log-concavity facts. -/
theorem setup_of_parity {e : ℕ → ℝ} {B : ℕ → ℝ} {c a : ℝ} (hB : IsBeta B)
    (hc : 0 < c) (ha : 0 < a)
    (hparity : ∀ n, e n = c * a ^ n * (if Even n then B (n + 1) else lam (n + 1)))
    (hEven : ∀ m u v : ℕ, 1 ≤ u → 1 ≤ v →
      e (2 * m) * e (2 * (m + u + v)) < e (2 * (m + u)) * e (2 * (m + v)))
    (hOdd : ∀ m u v : ℕ, 1 ≤ u → 1 ≤ v →
      e (2 * (m + u) + 1) * e (2 * (m + v) + 1) < e (2 * m + 1) * e (2 * (m + u + v) + 1)) :
    Setup e B lam c a where
  cpos := hc
  apos := ha
  parity := hparity
  Bpos := fun s hs => beta_pos hB s hs
  Blt := fun s hs => beta_lt_one hB s hs
  Bstep := fun s hs => beta_step hB s hs
  Lgt := fun s hs => one_lt_lam s hs
  Lstep := fun s hs => lam_step s hs
  sameEven := hEven
  sameOdd := hOdd

/-- **Sokal's Conjecture 3.3 from THREE carried facts instead of seven**: the partial-fraction
form `parity`, and the strict log-concavity/log-convexity of the even- and odd-index
subsequences.  Everything else the spine used is now proved. -/
theorem main_of_parity {e : ℕ → ℝ} {B : ℕ → ℝ} {c a : ℝ} (hB : IsBeta B)
    (hc : 0 < c) (ha : 0 < a)
    (hparity : ∀ n, e n = c * a ^ n * (if Even n then B (n + 1) else lam (n + 1)))
    (hEven : ∀ m u v : ℕ, 1 ≤ u → 1 ≤ v →
      e (2 * m) * e (2 * (m + u + v)) < e (2 * (m + u)) * e (2 * (m + v)))
    (hOdd : ∀ m u v : ℕ, 1 ≤ u → 1 ≤ v →
      e (2 * (m + u) + 1) * e (2 * (m + v) + 1) < e (2 * m + 1) * e (2 * (m + u + v) + 1))
    (n j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    0 < (-1 : ℝ) ^ (n + 1) * (e n * e (n + j + k) - e (n + j) * e (n + k)) :=
  main (setup_of_parity hB hc ha hparity hEven hOdd) n j k hj hk

end Assembly

end Principia.MathDB.P338918
