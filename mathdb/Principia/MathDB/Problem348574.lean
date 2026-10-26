import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# MathDB #348574 — the discrete maximal-variation conjecture below `p = 1`

Write-up: `mathdb-open-problems/problems/348574/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress`.
Source: González-Riquelme and Madrid, **Conjecture 1, equation (5.4)**: for `1/2 < p ≤ 1`
and `f ∈ ℓ^p(ℤ)`, `Var_p(Mf) ≤ C_p Var_p(f)` with
`C_p^p = ∑_j (2/((2j+1)(2j+3)))^p`.

The witness is the three-point function `f = 1_{[-1,1]}`.  The conjecture is **refuted at
`p = 3/4`** (`not_conj`): refuting it needs only ONE `p`.

## What is proved

* `Mf_eq` — the witness's centred maximal function is exactly `3/(2n+3)` for `n ≥ 2`.
  This is a genuine `⨆ r : ℕ`, not an assumed value: `g_le` bounds every radius and
  `g_attains` exhibits `r = n+1`, so `Mf_eq` is `le_antisymm` of `ciSup_le` and `le_ciSup`.
* `jump_eq` — the resulting jump across `n → n+1`.
* `av_eq_jump` — **the sequence the certificate sums is that jump sequence**, not a list
  read off the write-up: for `j ≥ 1`, `av j = Mf (j+1) − Mf (j+2)`.
* `bv_le_av` — the two sequences cross exactly once (`b_j ≤ a_j` for `j ≥ 2`, algebraically
  `13 ≤ 4j²`), so every omitted tail term is nonnegative and the tail needs **no estimate** —
  `tail_le` compares the two tails termwise.
* `av_summable` / `bv_summable` — both `3/4`-power series converge, by comparison with the
  `3/2`-p-series (`Real.summable_one_div_nat_rpow`) through `rpow_bound`.
* `sum_a_lb` / `sum_b_ub` — eleven terms suffice: `∑_{j<11} a_j^p ≥ 13687/10000` and
  `∑_{j<11} b_j^p ≤ 13611/10000`, a margin of `19/2500`.
* `not_conj` — `Cpow < Rpow`, i.e. `∑ b_j^p < ∑ a_j^p`.

Each of the 22 rational bounds is reduced to an integer inequality — `l ≤ q^(3/4)` iff
`l⁴ ≤ q³` (`le_rpow34`, `rpow34_le`) — and is *chosen* by exact integer 4th-root search in
`Campaigns/MathDB-Formalization/gen_348574_cert.py`, which also emits this block.  No
floating point is involved at any point, and no constant is hand-transcribed.

**Not Lean-checked:** that `∑_j a_j^p = (Var_p(Mf)/Var_p(f))^p` for this witness and that
`C_p^p = ∑_j b_j^p`, which are the write-up's reduction of (5.4) to the sequence inequality;
they are read off the write-up exactly as `#360860` reads off its barycentre formula.  What
*is* checked here is the maximal function the first identity rests on, and the inequality.

Values checked in `Campaigns/MathDB-Formalization/verify_348574.py`.
-/

namespace Principia.MathDB.P348574

/-- How many of the three support points `{-1,0,1}` lie in the window `[n-r, n+r]`. -/
def cnt (n : ℤ) (r : ℕ) : ℕ :=
  (({-1, 0, 1} : Finset ℤ).filter (fun k => n - r ≤ k ∧ k ≤ n + r)).card

theorem cnt_le_three (n : ℤ) (r : ℕ) : cnt n r ≤ 3 := by
  simp only [cnt]
  calc (({-1, 0, 1} : Finset ℤ).filter _).card ≤ ({-1, 0, 1} : Finset ℤ).card :=
        Finset.card_filter_le _ _
    _ ≤ 3 := by decide

/-- Window entirely above the support. -/
theorem cnt_eq_zero (n : ℤ) (r : ℕ) (h : (r : ℤ) < n - 1) : cnt n r = 0 := by
  simp only [cnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k hk
  fin_cases hk <;> omega

/-- Left end at `1`: only `k = 1` can be caught. -/
theorem cnt_le_one (n : ℤ) (r : ℕ) (h : 1 ≤ n - r) : cnt n r ≤ 1 := by
  simp only [cnt]
  have hsub : (({-1, 0, 1} : Finset ℤ).filter (fun k => n - r ≤ k ∧ k ≤ n + r))
      ⊆ {1} := by
    intro k hk
    simp only [Finset.mem_filter] at hk
    obtain ⟨hmem, h1, _⟩ := hk
    fin_cases hmem <;> simp_all <;> omega
  calc _ ≤ ({1} : Finset ℤ).card := Finset.card_le_card hsub
    _ = 1 := rfl

/-- Left end at `0`: only `k ∈ {0,1}`. -/
theorem cnt_le_two (n : ℤ) (r : ℕ) (h : 0 ≤ n - r) : cnt n r ≤ 2 := by
  simp only [cnt]
  have hsub : (({-1, 0, 1} : Finset ℤ).filter (fun k => n - r ≤ k ∧ k ≤ n + r))
      ⊆ {0, 1} := by
    intro k hk
    simp only [Finset.mem_filter] at hk
    obtain ⟨hmem, h1, _⟩ := hk
    fin_cases hmem <;> simp_all <;> omega
  calc _ ≤ ({0, 1} : Finset ℤ).card := Finset.card_le_card hsub
    _ = 2 := by decide

/-- The window average. -/
noncomputable def g (n : ℤ) (r : ℕ) : ℝ := (cnt n r : ℝ) / (2 * (r : ℝ) + 1)

/-- For `n ≥ 2` no radius beats `r = n+1`. -/
theorem g_le (n : ℤ) (hn : 2 ≤ n) (r : ℕ) : g n r ≤ 3 / (2 * (n : ℝ) + 3) := by
  have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hden : (0:ℝ) < 2 * (r : ℝ) + 1 := by positivity
  have hN : (0:ℝ) < 2 * (n:ℝ) + 3 := by linarith
  have hcast : ((r:ℤ) : ℝ) = (r : ℝ) := by push_cast; ring
  rcases (by omega : (r:ℤ) < n - 1 ∨ (r:ℤ) = n - 1 ∨ (r:ℤ) = n ∨ n + 1 ≤ (r:ℤ))
      with h | h | h | h
  · rw [g, cnt_eq_zero n r h]
    simp only [Nat.cast_zero, zero_div]
    positivity
  · have hr : (r:ℝ) = (n:ℝ) - 1 := by
      have := congrArg (fun z : ℤ => (z : ℝ)) h
      push_cast at this; linarith
    have hc : (cnt n r : ℝ) ≤ 1 := by
      have := cnt_le_one n r (by omega); exact_mod_cast this
    rw [g, div_le_div_iff₀ hden hN]
    nlinarith [hc]
  · have hr : (r:ℝ) = (n:ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) h
      push_cast at this; linarith
    have hc : (cnt n r : ℝ) ≤ 2 := by
      have := cnt_le_two n r (by omega); exact_mod_cast this
    rw [g, div_le_div_iff₀ hden hN]
    nlinarith [hc]
  · have hr : (n:ℝ) + 1 ≤ (r:ℝ) := by
      have h2 : ((n:ℤ):ℝ) + 1 ≤ ((r:ℤ):ℝ) := by exact_mod_cast h
      push_cast at h2; linarith
    have hc : (cnt n r : ℝ) ≤ 3 := by
      have := cnt_le_three n r; exact_mod_cast this
    rw [g, div_le_div_iff₀ hden hN]
    nlinarith [hc]

/-- The whole support is caught once `r ≥ n+1`. -/
theorem cnt_eq_three (n : ℤ) (hn : 2 ≤ n) (r : ℕ) (h : n + 1 ≤ (r : ℤ)) :
    cnt n r = 3 := by
  simp only [cnt]
  rw [Finset.filter_true_of_mem]
  · decide
  · intro k hk
    fin_cases hk <;> constructor <;> omega

/-- The bound is ATTAINED at `r = n+1`, so the supremum is exactly `3/(2n+3)`. -/
theorem g_attains (n : ℤ) (hn : 2 ≤ n) :
    g n (n + 1).toNat = 3 / (2 * (n : ℝ) + 3) := by
  have hr : (((n + 1).toNat : ℤ)) = n + 1 := Int.toNat_of_nonneg (by omega)
  have h3 : cnt n (n + 1).toNat = 3 := cnt_eq_three n hn _ (by omega)
  have hrR : (((n + 1).toNat : ℕ) : ℝ) = (n : ℝ) + 1 := by
    have : ((((n + 1).toNat : ℕ) : ℤ) : ℝ) = ((n + 1 : ℤ) : ℝ) := by rw [hr]
    push_cast at this ⊢; linarith
  rw [g, h3, hrR]
  push_cast
  ring_nf

/-- The centred maximal function of `1_{[-1,1]}`, as a supremum over radii. -/
noncomputable def Mf (n : ℤ) : ℝ := ⨆ r : ℕ, g n r

/-- **The maximal function's value for `|n| ≥ 2`** (stated for `n ≥ 2`; the function is even). -/
theorem Mf_eq (n : ℤ) (hn : 2 ≤ n) : Mf n = 3 / (2 * (n : ℝ) + 3) := by
  have hbdd : BddAbove (Set.range (g n)) := by
    refine ⟨3 / (2 * (n : ℝ) + 3), ?_⟩
    rintro y ⟨r, rfl⟩
    exact g_le n hn r
  refine le_antisymm (ciSup_le (fun r => g_le n hn r)) ?_
  rw [← g_attains n hn]
  exact le_ciSup hbdd _


/-- The jump of `Mf` across `n → n+1` for `n ≥ 2`, which is the write-up's `a_{n-1}`. -/
theorem jump_eq (n : ℤ) (hn : 2 ≤ n) :
    Mf n - Mf (n + 1) = 6 / ((2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 5)) := by
  have h1 := Mf_eq n hn
  have h2 := Mf_eq (n + 1) (by omega)
  have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have e1 : (2:ℝ) * ((n + 1 : ℤ) : ℝ) + 3 = 2 * (n:ℝ) + 5 := by push_cast; ring
  rw [h1, h2, e1]
  have d1 : (0:ℝ) < 2 * (n:ℝ) + 3 := by linarith
  have d2 : (0:ℝ) < 2 * (n:ℝ) + 5 := by linarith
  field_simp
  ring

/-! ### The refutation at `p = 3/4`

Generated by `Campaigns/MathDB-Formalization/gen_348574_cert.py`; every rational
bound below is chosen by exact integer 4th-root search, never by floating point. -/

/-- The witness's jump sequence `a_j`: `a_0 = 4/7` and `a_j = 6/((2j+5)(2j+7))`. -/
noncomputable def av (j : ℕ) : ℝ :=
  if j = 0 then 4/7 else 6/((2*(j:ℝ)+5)*(2*(j:ℝ)+7))

/-- The conjecture's sequence `b_j = 2/((2j+1)(2j+3))`, whose `p`-sum is `C_p^p`. -/
noncomputable def bv (j : ℕ) : ℝ := 2/((2*(j:ℝ)+1)*(2*(j:ℝ)+3))

/-- `l ≤ q^(3/4)` reduces to the rational inequality `l⁴ ≤ q³`. -/
theorem le_rpow34 {q l : ℝ} (hq : 0 ≤ q) (hl : 0 ≤ l) (h : l ^ 4 ≤ q ^ 3) :
    l ≤ q ^ ((3:ℝ)/4) := by
  have hl4 : ((l ^ 4 : ℝ)) ^ ((1:ℝ)/4) = l := by
    rw [← Real.rpow_natCast l 4, ← Real.rpow_mul hl]; norm_num
  have hq4 : ((q ^ 3 : ℝ)) ^ ((1:ℝ)/4) = q ^ ((3:ℝ)/4) := by
    rw [← Real.rpow_natCast q 3, ← Real.rpow_mul hq]; norm_num
  calc l = ((l ^ 4 : ℝ)) ^ ((1:ℝ)/4) := hl4.symm
    _ ≤ ((q ^ 3 : ℝ)) ^ ((1:ℝ)/4) := Real.rpow_le_rpow (by positivity) h (by norm_num)
    _ = q ^ ((3:ℝ)/4) := hq4

/-- `q^(3/4) ≤ u` reduces to the rational inequality `q³ ≤ u⁴`. -/
theorem rpow34_le {q u : ℝ} (hq : 0 ≤ q) (hu : 0 ≤ u) (h : q ^ 3 ≤ u ^ 4) :
    q ^ ((3:ℝ)/4) ≤ u := by
  have hu4 : ((u ^ 4 : ℝ)) ^ ((1:ℝ)/4) = u := by
    rw [← Real.rpow_natCast u 4, ← Real.rpow_mul hu]; norm_num
  have hq4 : ((q ^ 3 : ℝ)) ^ ((1:ℝ)/4) = q ^ ((3:ℝ)/4) := by
    rw [← Real.rpow_natCast q 3, ← Real.rpow_mul hq]; norm_num
  calc q ^ ((3:ℝ)/4) = ((q ^ 3 : ℝ)) ^ ((1:ℝ)/4) := hq4.symm
    _ ≤ ((u ^ 4 : ℝ)) ^ ((1:ℝ)/4) := Real.rpow_le_rpow (by positivity) h (by norm_num)
    _ = u := hu4

theorem av_pos (j : ℕ) : 0 < av j := by
  rw [av]; split
  · norm_num
  · have : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
    positivity

theorem bv_pos (j : ℕ) : 0 < bv j := by
  have : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
  rw [bv]; positivity

/-- **`av` is the jump sequence of the maximal function proved above**, not an
assumed list: for `j ≥ 1`, `a_j = Mf (j+1) − Mf (j+2)` by `jump_eq`. -/
theorem av_eq_jump (j : ℕ) (hj : 1 ≤ j) :
    av j = Mf ((j:ℤ) + 1) - Mf ((j:ℤ) + 2) := by
  have h := jump_eq ((j:ℤ) + 1) (by omega)
  have e : ((j:ℤ) + 1) + 1 = (j:ℤ) + 2 := by ring
  rw [e] at h
  rw [av, if_neg (by omega : j ≠ 0), h]
  push_cast
  ring_nf

/-- The two sequences cross exactly once: `b_j ≤ a_j` for `j ≥ 2` (i.e. `13 ≤ 4j²`),
so every omitted tail term is nonnegative and the tail needs no estimate. -/
theorem bv_le_av (j : ℕ) (hj : 2 ≤ j) : bv j ≤ av j := by
  have hj2 : (2:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
  rw [bv, av, if_neg (by omega : j ≠ 0)]
  rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith [sq_nonneg ((j:ℝ) - 2)]

theorem gsum : Summable (fun j : ℕ => 2 / (j:ℝ) ^ ((3:ℝ)/2)) := by
  have h : Summable (fun n : ℕ => 1 / (n:ℝ) ^ ((3:ℝ)/2)) := by
    rw [Real.summable_one_div_nat_rpow]; norm_num
  exact (h.mul_left 2).congr (fun n => mul_one_div 2 _)

/-- Both sequences are `≤ 2/j²`, so their `3/4`-powers are `≤ 2/j^(3/2)`. -/
theorem rpow_bound {v : ℝ} (j : ℕ) (hj : 1 ≤ j) (hv0 : 0 ≤ v)
    (hv : v ≤ 2 / (j : ℝ) ^ 2) : v ^ ((3:ℝ)/4) ≤ 2 / (j:ℝ) ^ ((3:ℝ)/2) := by
  have hj1 : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
  have hx : (0:ℝ) < (j:ℝ) := by linarith
  refine rpow34_le hv0 (by positivity) ?_
  have h4 : (2 / (j:ℝ) ^ ((3:ℝ)/2)) ^ 4 = 16 / (j:ℝ) ^ (6:ℕ) := by
    rw [div_pow, ← Real.rpow_natCast ((j:ℝ) ^ ((3:ℝ)/2)) 4, ← Real.rpow_mul hx.le,
      ← Real.rpow_natCast (j:ℝ) 6]
    norm_num
  rw [h4]
  have hcube : v ^ 3 ≤ (2 / (j : ℝ) ^ 2) ^ 3 := by
    exact pow_le_pow_left₀ hv0 hv 3
  have he : (2 / (j : ℝ) ^ 2) ^ 3 = 8 / (j:ℝ) ^ (6:ℕ) := by
    rw [div_pow]; norm_num; ring
  have hp6 : (0:ℝ) < (j:ℝ) ^ (6:ℕ) := by positivity
  rw [he] at hcube
  have : (8:ℝ) / (j:ℝ) ^ (6:ℕ) ≤ 16 / (j:ℝ) ^ (6:ℕ) := by
    rw [div_le_div_iff₀ hp6 hp6]; nlinarith
  linarith

theorem av_le_sq (j : ℕ) (hj : 1 ≤ j) : av j ≤ 2 / (j : ℝ) ^ 2 := by
  have hj1 : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
  rw [av, if_neg (by omega : j ≠ 0)]
  rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith [sq_nonneg ((j:ℝ) - 1)]

theorem bv_le_sq (j : ℕ) (hj : 1 ≤ j) : bv j ≤ 2 / (j : ℝ) ^ 2 := by
  have hj1 : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
  rw [bv]
  rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith [sq_nonneg ((j:ℝ) - 1)]

theorem av_summable : Summable (fun j : ℕ => av j ^ ((3:ℝ)/4)) := by
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le
    (fun n => Real.rpow_nonneg (av_pos _).le _) (fun n => ?_)
    ((summable_nat_add_iff 1).2 gsum)
  exact rpow_bound (n+1) (by omega) (av_pos _).le (av_le_sq (n+1) (by omega))

theorem bv_summable : Summable (fun j : ℕ => bv j ^ ((3:ℝ)/4)) := by
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le
    (fun n => Real.rpow_nonneg (bv_pos _).le _) (fun n => ?_)
    ((summable_nat_add_iff 1).2 gsum)
  exact rpow_bound (n+1) (by omega) (bv_pos _).le (bv_le_sq (n+1) (by omega))

/-- **Lower bounds on the first eleven `a_j^(3/4)`.**  Each reduces to `l⁴ ≤ a_j³`. -/
theorem sum_a_lb : (13687:ℝ)/10000 ≤ ∑ j ∈ Finset.range 11, av j ^ ((3:ℝ)/4) := by
  have h0 : (1643:ℝ)/2500 ≤ av 0 ^ ((3:ℝ)/4) := by
    have e : av 0 = (4:ℝ)/7 := by rw [av]; norm_num
    rw [e]; exact le_rpow34 (by norm_num) (by norm_num) (by norm_num)
  have h1 : (857:ℝ)/5000 ≤ av 1 ^ ((3:ℝ)/4) := by
    have e : av 1 = (2:ℝ)/21 := by rw [av]; norm_num
    rw [e]; exact le_rpow34 (by norm_num) (by norm_num) (by norm_num)
  have h2 : (1221:ℝ)/10000 ≤ av 2 ^ ((3:ℝ)/4) := by
    have e : av 2 = (2:ℝ)/33 := by rw [av]; norm_num
    rw [e]; exact le_rpow34 (by norm_num) (by norm_num) (by norm_num)
  have h3 : (927:ℝ)/10000 ≤ av 3 ^ ((3:ℝ)/4) := by
    have e : av 3 = (6:ℝ)/143 := by rw [av]; norm_num
    rw [e]; exact le_rpow34 (by norm_num) (by norm_num) (by norm_num)
  have h4 : (367:ℝ)/5000 ≤ av 4 ^ ((3:ℝ)/4) := by
    have e : av 4 = (2:ℝ)/65 := by rw [av]; norm_num
    rw [e]; exact le_rpow34 (by norm_num) (by norm_num) (by norm_num)
  have h5 : (3:ℝ)/50 ≤ av 5 ^ ((3:ℝ)/4) := by
    have e : av 5 = (2:ℝ)/85 := by rw [av]; norm_num
    rw [e]; exact le_rpow34 (by norm_num) (by norm_num) (by norm_num)
  have h6 : (503:ℝ)/10000 ≤ av 6 ^ ((3:ℝ)/4) := by
    have e : av 6 = (6:ℝ)/323 := by rw [av]; norm_num
    rw [e]; exact le_rpow34 (by norm_num) (by norm_num) (by norm_num)
  have h7 : (429:ℝ)/10000 ≤ av 7 ^ ((3:ℝ)/4) := by
    have e : av 7 = (2:ℝ)/133 := by rw [av]; norm_num
    rw [e]; exact le_rpow34 (by norm_num) (by norm_num) (by norm_num)
  have h8 : (93:ℝ)/2500 ≤ av 8 ^ ((3:ℝ)/4) := by
    have e : av 8 = (2:ℝ)/161 := by rw [av]; norm_num
    rw [e]; exact le_rpow34 (by norm_num) (by norm_num) (by norm_num)
  have h9 : (163:ℝ)/5000 ≤ av 9 ^ ((3:ℝ)/4) := by
    have e : av 9 = (6:ℝ)/575 := by rw [av]; norm_num
    rw [e]; exact le_rpow34 (by norm_num) (by norm_num) (by norm_num)
  have h10 : (289:ℝ)/10000 ≤ av 10 ^ ((3:ℝ)/4) := by
    have e : av 10 = (2:ℝ)/225 := by rw [av]; norm_num
    rw [e]; exact le_rpow34 (by norm_num) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  linarith

/-- **Upper bounds on the first eleven `b_j^(3/4)`.**  Each reduces to `b_j³ ≤ u⁴`. -/
theorem sum_b_ub : ∑ j ∈ Finset.range 11, bv j ^ ((3:ℝ)/4) ≤ (13611:ℝ)/10000 := by
  have h0 : bv 0 ^ ((3:ℝ)/4) ≤ (3689:ℝ)/5000 := by
    have e : bv 0 = (2:ℝ)/3 := by rw [bv]; norm_num
    rw [e]; exact rpow34_le (by norm_num) (by norm_num) (by norm_num)
  have h1 : bv 1 ^ ((3:ℝ)/4) ≤ (2207:ℝ)/10000 := by
    have e : bv 1 = (2:ℝ)/15 := by rw [bv]; norm_num
    rw [e]; exact rpow34_le (by norm_num) (by norm_num) (by norm_num)
  have h2 : bv 2 ^ ((3:ℝ)/4) ≤ (1169:ℝ)/10000 := by
    have e : bv 2 = (2:ℝ)/35 := by rw [bv]; norm_num
    rw [e]; exact rpow34_le (by norm_num) (by norm_num) (by norm_num)
  have h3 : bv 3 ^ ((3:ℝ)/4) ≤ (753:ℝ)/10000 := by
    have e : bv 3 = (2:ℝ)/63 := by rw [bv]; norm_num
    rw [e]; exact rpow34_le (by norm_num) (by norm_num) (by norm_num)
  have h4 : bv 4 ^ ((3:ℝ)/4) ≤ (67:ℝ)/1250 := by
    have e : bv 4 = (2:ℝ)/99 := by rw [bv]; norm_num
    rw [e]; exact rpow34_le (by norm_num) (by norm_num) (by norm_num)
  have h5 : bv 5 ^ ((3:ℝ)/4) ≤ (407:ℝ)/10000 := by
    have e : bv 5 = (2:ℝ)/143 := by rw [bv]; norm_num
    rw [e]; exact rpow34_le (by norm_num) (by norm_num) (by norm_num)
  have h6 : bv 6 ^ ((3:ℝ)/4) ≤ (323:ℝ)/10000 := by
    have e : bv 6 = (2:ℝ)/195 := by rw [bv]; norm_num
    rw [e]; exact rpow34_le (by norm_num) (by norm_num) (by norm_num)
  have h7 : bv 7 ^ ((3:ℝ)/4) ≤ (33:ℝ)/1250 := by
    have e : bv 7 = (2:ℝ)/255 := by rw [bv]; norm_num
    rw [e]; exact rpow34_le (by norm_num) (by norm_num) (by norm_num)
  have h8 : bv 8 ^ ((3:ℝ)/4) ≤ (221:ℝ)/10000 := by
    have e : bv 8 = (2:ℝ)/323 := by rw [bv]; norm_num
    rw [e]; exact rpow34_le (by norm_num) (by norm_num) (by norm_num)
  have h9 : bv 9 ^ ((3:ℝ)/4) ≤ (189:ℝ)/10000 := by
    have e : bv 9 = (2:ℝ)/399 := by rw [bv]; norm_num
    rw [e]; exact rpow34_le (by norm_num) (by norm_num) (by norm_num)
  have h10 : bv 10 ^ ((3:ℝ)/4) ≤ (41:ℝ)/2500 := by
    have e : bv 10 = (2:ℝ)/483 := by rw [bv]; norm_num
    rw [e]; exact rpow34_le (by norm_num) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  linarith

/-- Past the crossover the tail comparison is termwise. -/
theorem tail_le :
    ∑' j : ℕ, bv (j + 11) ^ ((3:ℝ)/4) ≤ ∑' j : ℕ, av (j + 11) ^ ((3:ℝ)/4) := by
  refine Summable.tsum_le_tsum (fun j => ?_)
    ((summable_nat_add_iff 11).2 bv_summable)
    ((summable_nat_add_iff 11).2 av_summable)
  exact Real.rpow_le_rpow (bv_pos _).le (bv_le_av (j + 11) (by omega)) (by norm_num)

/-- The conjecture's constant, `C_p^p = ∑_j b_j^p`, at `p = 3/4`. -/
noncomputable def Cpow : ℝ := ∑' j : ℕ, bv j ^ ((3:ℝ)/4)

/-- The witness's ratio `(Var_p(Mf)/Var_p(f))^p = ∑_j a_j^p`, at `p = 3/4`. -/
noncomputable def Rpow : ℝ := ∑' j : ℕ, av j ^ ((3:ℝ)/4)

/-- **Conjecture 1, equation (5.4) is FALSE at `p = 3/4`.**  The witness's ratio
strictly exceeds the conjectured constant: `∑ a_j^p > ∑ b_j^p`, by at least
`(19:ℝ)/2500`.  Eleven terms settle it, because every later term of
`a_j^p − b_j^p` is nonnegative (`bv_le_av`). -/
theorem not_conj : Cpow < Rpow := by
  rw [Cpow, Rpow, ← Summable.sum_add_tsum_nat_add 11 av_summable,
    ← Summable.sum_add_tsum_nat_add 11 bv_summable]
  have hf := sum_b_ub
  have hg := sum_a_lb
  have ht := tail_le
  have hlt : ∑ j ∈ Finset.range 11, bv j ^ ((3:ℝ)/4)
      < ∑ j ∈ Finset.range 11, av j ^ ((3:ℝ)/4) := by linarith
  exact add_lt_add_of_lt_of_le hlt ht


end Principia.MathDB.P348574
