import Principia.Common.TanhMajorant

/-!
# A spaced sequence has bounded majorant sum

`\sum_l g(e^{-x_l}) <= 127/600` whenever `x` is positive and grows by a factor of at least `16`
at every step, where `g` is the majorant of `Principia.Common.TanhMajorant`.

Promoted out of MathDB #360139 (the Fibonacci characteristic function), which paid for it.
**Nothing here mentions a substitution, a Fibonacci word or a generating function**: every
statement quantifies over an arbitrary `x : \N -> \R` satisfying `Spaced`, and the campaign
supplied such an `x` from Fibonacci growth -- that instantiation stays behind in the campaign.

**The constant is exact, not rounded.**  `127/600 = 1/15 + 1/8 + 1/50` is the sum of the three
pieces of the split: a backward geometric sum below the threshold (`back_bound`), the single
worst term at it (`gfun_le_eighth`), and an exponential tail above it (`tail_bound`).  Knowing
that the constant decomposes this way is what tells you the split to make; `spacing_pieces`
records the arithmetic so the decomposition is checkable rather than asserted.

`spacingLemma` is the assembly: `Nat.find` locates the first index where `x` exceeds the
threshold, and the sum splits there.
-/

namespace Principia.Common

open Real

/-- The three pieces of the spacing split sum to `127/600` EXACTLY — the write-up's constant
is not a rounded bound but the sum `1/15 + 1/8 + 1/50`. -/
theorem spacing_pieces : (1 : ℝ) / 15 + 1 / 8 + 1 / 50 = 127 / 600 := by norm_num

/-- The spacing hypothesis: the exponents grow by a factor of at least `16`. -/
def Spaced (x : ℕ → ℝ) : Prop := (∀ ℓ, 0 < x ℓ) ∧ ∀ ℓ, 16 * x ℓ ≤ x (ℓ + 1)

/-- The write-up's spacing lemma, carried.  Its three pieces are `gfun_exp_le_quarter`,
`gfun_le_eighth` and `gfun_le_self`, all proved above; what is carried is the summation
bookkeeping (a backward geometric sum, a one-term middle range, and an exponential tail). -/
def SpacingLemma : Prop :=
  ∀ x : ℕ → ℝ, Spaced x → ∀ n : ℕ,
    ∑ ℓ ∈ Finset.range n, gfun (exp (-x ℓ)) ≤ 127 / 600

/-! ### The spacing lemma, discharged

`SpacingLemma` was carried.  Its three pointwise ingredients were already proved; what was
missing was the summation, and the write-up's constant says exactly how to do it:

    127/600 = 1/8 + 1/15 + 1/50     (`spacing_pieces`, already in this file)

Take `M` to be the first index with `x M > 4`.  Then

* `below_bound` — the terms before `M` give `1/8 + 1/15`: the last of them by
  `gfun_le_eighth`, and the rest by `back_bound`, since `16^{M-l}·x l ≤ x M ≤ 4` forces
  `g ≤ x l/4 ≤ (1/16)^{M-l}`, whose reflected sum is `(1/16)·∑(1/16)^l ≤ 1/15`;
* `tail_bound` — the terms from `M` on give `1/50`, because `4·16ʲ ≥ 4 + 60j` makes the tail
  geometric with ratio `exp(-60) ≤ 1/1000`, and `exp(-4) < 1/54`, so the tail is at most
  `(1000/999)·(1/54) = 500/26973 < 1/50`.

**The threshold matters and 4 is not arbitrary**: any threshold near `1` would pay
`exp(-1) = 0.368` on the tail alone, 174% of the whole target.  Checked numerically first in
`Campaigns/MathDB-Formalization/verify_360139_spacing.py`, including the exact rational
chain `1/8 + 1/15 + 500/26973 = 226793/1078920 ≤ 127/600`. -/


/-- `(1-r)·∑_{i<m} rⁱ = 1 - rᵐ`, by induction; avoids depending on a `geom_sum` name. -/
theorem geom_telescope (r : ℝ) (m : ℕ) :
    (1 - r) * ∑ i ∈ Finset.range m, r ^ i = 1 - r ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    ring

/-- The partial geometric sum is below its limit. -/
theorem geom_bound {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (m : ℕ) :
    ∑ i ∈ Finset.range m, r ^ i ≤ 1 / (1 - r) := by
  have hd : (0 : ℝ) < 1 - r := by linarith
  have ht := geom_telescope r m
  have hrm : (0 : ℝ) ≤ r ^ m := pow_nonneg h0 m
  rw [le_div_iff₀ hd, mul_comm]
  linarith [ht]

/-- `16ʲ·x k ≤ x (k+j)`: the spacing compounds. -/
theorem spaced_growth {x : ℕ → ℝ} (h : Spaced x) (k j : ℕ) :
    16 ^ j * x k ≤ x (k + j) := by
  obtain ⟨hpos, hgrow⟩ := h
  induction j with
  | zero => simp
  | succ i ih =>
    have h1 : 16 * (16 ^ i * x k) ≤ 16 * x (k + i) := by linarith
    have h2 : 16 * x (k + i) ≤ x (k + i + 1) := hgrow (k + i)
    calc (16 : ℝ) ^ (i + 1) * x k = 16 * (16 ^ i * x k) := by ring
      _ ≤ 16 * x (k + i) := h1
      _ ≤ x (k + i + 1) := h2
      _ = x (k + (i + 1)) := by ring_nf

/-- `exp 4 > 54`, from `Real.exp_one_gt_d9`. -/
theorem exp_four_gt : (54 : ℝ) < exp 4 := by
  have h1 : (2.7182818283 : ℝ) < exp 1 := Real.exp_one_gt_d9
  have h4 : (exp 1) ^ (4 : ℕ) = exp 4 := by
    rw [Real.exp_one_pow]; norm_num
  have hpow : (2.7182818283 : ℝ) ^ (4 : ℕ) ≤ (exp 1) ^ (4 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) (le_of_lt h1) 4
  have hnum : (54 : ℝ) < (2.7182818283 : ℝ) ^ (4 : ℕ) := by norm_num
  rw [← h4]
  linarith

/-- `exp 60 > 1000`, crudely: `exp 1 > 2` and `2^60` is enormous. -/
theorem exp_sixty_gt : (1000 : ℝ) < exp 60 := by
  have h1 : (2 : ℝ) < exp 1 := by
    have := Real.exp_one_gt_d9; linarith
  have h60 : (exp 1) ^ (60 : ℕ) = exp 60 := by
    rw [Real.exp_one_pow]; norm_num
  have hpow : (2 : ℝ) ^ (60 : ℕ) ≤ (exp 1) ^ (60 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) (le_of_lt h1) 60
  have hnum : (1000 : ℝ) < (2 : ℝ) ^ (60 : ℕ) := by norm_num
  rw [← h60]
  linarith

/-- `4·16ʲ ≥ 4 + 60j`, the step that makes the tail geometric with a tiny ratio. -/
theorem pow_ge_linear (j : ℕ) : (4 : ℝ) + 60 * j ≤ 4 * 16 ^ j := by
  induction j with
  | zero => norm_num
  | succ i ih =>
    have h16 : (1 : ℝ) ≤ 16 ^ i := one_le_pow₀ (by norm_num)
    push_cast at ih ⊢
    calc (4 : ℝ) + 60 * ((i : ℝ) + 1) = (4 + 60 * i) + 60 := by ring
      _ ≤ 4 * 16 ^ i + 60 := by linarith
      _ ≤ 4 * 16 ^ (i + 1) := by
          have : (4 : ℝ) * 16 ^ (i + 1) = 4 * 16 ^ i + 60 * 16 ^ i := by ring
          rw [this]
          linarith

/-- **The tail.**  Past an index where `x` has already exceeded `4`, the whole remaining sum
is below `1/50`. -/
theorem tail_bound {x : ℕ → ℝ} (h : Spaced x) {L : ℕ} (hL : 4 ≤ x L) (m : ℕ) :
    ∑ j ∈ Finset.range m, gfun (exp (-x (L + j))) ≤ 1 / 50 := by
  have hstep : ∀ j ∈ Finset.range m,
      gfun (exp (-x (L + j))) ≤ exp (-4) * (exp (-60)) ^ j := by
    intro j _
    have hxj : (4 : ℝ) + 60 * j ≤ x (L + j) := by
      have hg := spaced_growth h L j
      have : (4 : ℝ) * 16 ^ j ≤ 16 ^ j * x L := by
        have h16 : (0 : ℝ) < 16 ^ j := by positivity
        nlinarith [pow_ge_linear j]
      linarith [pow_ge_linear j]
    have hexp : exp (-x (L + j)) ≤ exp (-(4 + 60 * j)) := by
      apply Real.exp_le_exp.mpr; linarith
    have hg := gfun_le_self (le_of_lt (Real.exp_pos (-x (L + j))))
    have hrw : exp (-(4 + 60 * (j : ℝ))) = exp (-4) * (exp (-60)) ^ j := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    calc gfun (exp (-x (L + j))) ≤ exp (-x (L + j)) := hg
      _ ≤ exp (-(4 + 60 * (j : ℝ))) := hexp
      _ = exp (-4) * (exp (-60)) ^ j := hrw
  have hsum := Finset.sum_le_sum hstep
  have hr0 : (0 : ℝ) ≤ exp (-60) := le_of_lt (Real.exp_pos _)
  have hr1 : exp (-60) < 1 / 1000 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
    simpa using exp_sixty_gt
  have hgb : ∑ j ∈ Finset.range m, (exp (-60)) ^ j ≤ 1 / (1 - exp (-60)) :=
    geom_bound hr0 (by linarith) m
  have he4 : exp (-4) < 1 / 54 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
    simpa using exp_four_gt
  have he4pos : (0 : ℝ) < exp (-4) := Real.exp_pos _
  have hden : (0 : ℝ) < 1 - exp (-60) := by linarith
  have hfinal : exp (-4) * (1 / (1 - exp (-60))) ≤ 1 / 50 := by
    rw [mul_one_div, div_le_div_iff₀ hden (by norm_num)]
    nlinarith [he4, hr1, he4pos]
  calc ∑ j ∈ Finset.range m, gfun (exp (-x (L + j)))
      ≤ ∑ j ∈ Finset.range m, exp (-4) * (exp (-60)) ^ j := hsum
    _ = exp (-4) * ∑ j ∈ Finset.range m, (exp (-60)) ^ j := by rw [Finset.mul_sum]
    _ ≤ exp (-4) * (1 / (1 - exp (-60))) := by
        exact mul_le_mul_of_nonneg_left hgb (le_of_lt he4pos)
    _ ≤ 1 / 50 := hfinal

/-- **The backward piece.**  If `x M ≤ 4` then `x l ≤ 4/16^{M-l}` for every `l < M`, so
`g ≤ x l/4 ≤ (1/16)^{M-l}`; reflecting the range turns that into `(1/16)·∑ (1/16)^l`. -/
theorem back_bound {x : ℕ → ℝ} (h : Spaced x) {M : ℕ} (hM : x M ≤ 4) :
    ∑ l ∈ Finset.range M, gfun (exp (-x l)) ≤ 1 / 15 := by
  have hpos := h.1
  have hstep : ∀ l ∈ Finset.range M, gfun (exp (-x l)) ≤ (1 / 16 : ℝ) ^ (M - l) := by
    intro l hl
    have hlM : l < M := Finset.mem_range.mp hl
    have hg := spaced_growth h l (M - l)
    rw [show l + (M - l) = M from by omega] at hg
    have hb : (16 : ℝ) ^ (M - l) * x l ≤ 4 := le_trans hg hM
    have hq := gfun_exp_le_quarter (le_of_lt (hpos l))
    have hkey : x l / 4 ≤ (1 / 16 : ℝ) ^ (M - l) := by
      rw [div_pow, one_pow,
        div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) (by positivity)]
      nlinarith [hb]
    linarith
  have hsum := Finset.sum_le_sum hstep
  have hre : ∑ l ∈ Finset.range M, (1 / 16 : ℝ) ^ (M - l)
      = ∑ l ∈ Finset.range M, (1 / 16 : ℝ) ^ (l + 1) := by
    rw [← Finset.sum_range_reflect (fun l => (1 / 16 : ℝ) ^ (M - l)) M]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    have hlM : l < M := Finset.mem_range.mp hl
    congr 1
    omega
  have hgeo : ∑ l ∈ Finset.range M, (1 / 16 : ℝ) ^ (l + 1)
      = (1 / 16 : ℝ) * ∑ l ∈ Finset.range M, (1 / 16 : ℝ) ^ l := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  have hgb : ∑ l ∈ Finset.range M, (1 / 16 : ℝ) ^ l ≤ 1 / (1 - 1 / 16) :=
    geom_bound (by norm_num) (by norm_num) M
  calc ∑ l ∈ Finset.range M, gfun (exp (-x l))
      ≤ ∑ l ∈ Finset.range M, (1 / 16 : ℝ) ^ (M - l) := hsum
    _ = (1 / 16 : ℝ) * ∑ l ∈ Finset.range M, (1 / 16 : ℝ) ^ l := by rw [hre, hgeo]
    _ ≤ (1 / 16 : ℝ) * (1 / (1 - 1 / 16)) :=
        mul_le_mul_of_nonneg_left hgb (by norm_num)
    _ = 1 / 15 := by norm_num

/-- **Below the threshold.**  The last term by `gfun_le_eighth`, the rest by `back_bound`. -/
theorem below_bound {x : ℕ → ℝ} (h : Spaced x) {M : ℕ} (hbelow : ∀ k, k < M → x k ≤ 4) :
    ∑ l ∈ Finset.range M, gfun (exp (-x l)) ≤ 1 / 8 + 1 / 15 := by
  cases M with
  | zero => norm_num
  | succ m =>
    rw [Finset.sum_range_succ]
    have h1 : gfun (exp (-x m)) ≤ 1 / 8 :=
      gfun_le_eighth (le_of_lt (Real.exp_pos _))
    have h2 : ∑ l ∈ Finset.range m, gfun (exp (-x l)) ≤ 1 / 15 :=
      back_bound h (hbelow m (Nat.lt_succ_self m))
    linarith

/-- **The carried `SpacingLemma`, discharged.** -/
theorem spacingLemma : SpacingLemma := by
  classical
  intro x hx n
  by_cases hall : ∀ k, k < n → x k ≤ 4
  · have hb := below_bound hx hall
    linarith
  · push_neg at hall
    obtain ⟨l0, hl0n, hl0⟩ := hall
    have hex : ∃ l, 4 < x l := ⟨l0, hl0⟩
    have hMspec : 4 < x (Nat.find hex) := Nat.find_spec hex
    have hbelow : ∀ k, k < Nat.find hex → x k ≤ 4 := fun k hk =>
      not_lt.mp (Nat.find_min hex hk)
    have hMlt : Nat.find hex < n := lt_of_le_of_lt (Nat.find_le hl0) hl0n
    obtain ⟨k, hk⟩ : ∃ k, n = Nat.find hex + k := ⟨n - Nat.find hex, by omega⟩
    rw [hk, Finset.sum_range_add]
    have hb := below_bound hx hbelow
    have ht := tail_bound hx (le_of_lt hMspec) k
    linarith

end Principia.Common
