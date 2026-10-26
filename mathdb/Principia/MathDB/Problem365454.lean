import Principia.Common.BesselJ0
import Principia.Common.RpowRational
import Principia.MathDB.Problem365454Cert

set_option autoImplicit false

/-!
# MathDB #365454 — nonnegativity of the truncated Bessel kernel

Write-up `mathdb-open-problems/problems/365454/solution.tex` on the `mathdb-results` branch of
`antoshashakov/Principia-Math-In-Progress` (fetched 2026-09-25).

With `j_m` the `m`-th positive zero of `J₀`,

    K_M^α(x) = ∑_{m=1}^M (1 - m/(M+1)) · j_m^α · J₀(j_m x),

Acosta Babb's Conjecture 1 (order zero) asks whether this is nonnegative for all `M ≥ 1`,
`0 ≤ x ≤ 1`, `0 ≤ α ≤ 1/2`.  The write-up refutes it at `M = 2`, `α = 2/5`, `x = 99/100`, with
`K_2^(2/5)(99/100) < -641/5250000`.

## This module is the SPINE

The chain from four numeric facts to the refutation is written first, with the arithmetic left as
named hypotheses.  What it makes visible:

**The refutation is LINEAR in the two Bessel values once their signs are known.**  `K_2` is a
two-term sum; the whole of the write-up's final display is `linarith` from `A > 0`, `B < 0`, an
upper bound on `j₁^(2/5)` and a lower bound on `j₂^(2/5)`.  Nothing about Bessel functions enters
after those four facts.

**The value bounds need the bracket, not a Lipschitz estimate.**  `J0_lt_of_besselP` and
`lt_J0_of_besselP` derive them from `Principia.Common.besselP_le_J0_le_besselP`, which holds
POINTWISE on `[0,6]`.  The write-up instead transfers values from a nearby rational point using
`|J₀'| ≤ 1`, proved from the integral representation `J₀(t) = (1/π)∫₀^π cos(t sin θ)dθ`; that
representation is not needed here, and neither is any derivative of `J₀`.

## What remains

The four hypotheses of `conjecture_false_of_certificate`, and the `FirstZeros j 2` witness.
Every one of
them is a comparison of a rational number against `besselP 12` or `besselP 13` evaluated at a
rational point, or against a rational power — finite arithmetic, once the enclosures of `j₁` and
`j₂` are established (`probe_365454_lipschitz.py` measures that step at 21 cells).
-/

namespace Principia.MathDB.P365454

open Principia.Common Finset

/-- `j` lists the first `M` positive zeros of `J₀`, in increasing order.  The conjecture is *about*
this enumeration, so it is a parameter of the statement rather than a construction.

**Why bounded by `M`.**  `K_M` mentions only `j 1, …, j M`.  An earlier version of this structure
constrained `j m` for EVERY `m`, which made refuting `∀ j, … j → …` depend on exhibiting an
enumeration of infinitely many zeros — an obligation created by the encoding, not by the problem.
With the bound, refuting at `M = 2` needs exactly the two zeros already enclosed. -/
structure FirstZeros (j : ℕ → ℝ) (M : ℕ) : Prop where
  pos : ∀ m, 1 ≤ m → m ≤ M → 0 < j m
  isZero : ∀ m, 1 ≤ m → m ≤ M → J0 (j m) = 0
  step : ∀ m, 1 ≤ m → m + 1 ≤ M → j m < j (m + 1)
  first : ∀ z, 0 < z → z < j 1 → J0 z ≠ 0
  between : ∀ m, 1 ≤ m → m + 1 ≤ M → ∀ z, j m < z → z < j (m + 1) → J0 z ≠ 0

/-- The truncated Bessel kernel `K_M^α`. -/
noncomputable def K (j : ℕ → ℝ) (M : ℕ) (α x : ℝ) : ℝ :=
  ∑ m ∈ Icc 1 M, (1 - (m : ℝ) / ((M : ℝ) + 1)) * (j m) ^ α * J0 (j m * x)

/-- **Acosta Babb's Conjecture 1**, order zero. -/
def Conjecture : Prop :=
  ∀ M : ℕ, 1 ≤ M → ∀ j : ℕ → ℝ, FirstZeros j M → ∀ α x : ℝ,
    0 ≤ α → α ≤ 1 / 2 → 0 ≤ x → x ≤ 1 → 0 ≤ K j M α x

/-- An upper bound on the bracketing polynomial is an upper bound on `J₀`. -/
theorem J0_lt_of_besselP {z c : ℝ} (hz0 : 0 ≤ z) (hz6 : z ≤ 6) (h : besselP 12 z < c) :
    J0 z < c :=
  lt_of_le_of_lt (besselP_le_J0_le_besselP hz0 hz6).2 h

/-- A lower bound on the bracketing polynomial is a lower bound on `J₀`. -/
theorem lt_J0_of_besselP {z c : ℝ} (hz0 : 0 ≤ z) (hz6 : z ≤ 6) (h : c < besselP 13 z) :
    c < J0 z :=
  lt_of_lt_of_le h (besselP_le_J0_le_besselP hz0 hz6).1

/-! ### The write-up's table of six exact comparisons

Each is one evaluation of a rational polynomial at a rational point.  `verify_365454.py` checks all
six independently; the thinnest margin is `4.5e-07`, at `L₂'`. -/

theorem besselP13_L1 : (1 : ℝ) / 100000 < besselP 13 (24048 / 10000) := by
  simp only [besselP, jterm, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.factorial]

theorem besselP12_U1 : besselP 12 (24049 / 10000) < -(3 / 100000) := by
  simp only [besselP, jterm, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.factorial]

theorem besselP12_L2 : besselP 12 (55200 / 10000) < -(2 / 100000) := by
  simp only [besselP, jterm, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.factorial]

theorem besselP13_U2 : (7 : ℝ) / 1000000 < besselP 13 (55201 / 10000) := by
  simp only [besselP, jterm, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.factorial]

theorem besselP12_astar : besselP 12 (23808 / 10000) < 63 / 5000 := by
  simp only [besselP, jterm, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.factorial]

theorem besselP12_bstar : besselP 12 (54649 / 10000) < -(47 / 2500) := by
  simp only [besselP, jterm, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.factorial]

/-! ### The four sign facts

These are what the enclosures are built from, and they are the only place the bracket is used. -/

theorem J0_pos_L1 : 0 < J0 (24048 / 10000) :=
  lt_J0_of_besselP (by norm_num) (by norm_num) (by linarith [besselP13_L1])

theorem J0_neg_U1 : J0 (24049 / 10000) < 0 :=
  J0_lt_of_besselP (by norm_num) (by norm_num) (by linarith [besselP12_U1])

theorem J0_neg_L2 : J0 (55200 / 10000) < 0 :=
  J0_lt_of_besselP (by norm_num) (by norm_num) (by linarith [besselP12_L2])

theorem J0_pos_U2 : 0 < J0 (55201 / 10000) :=
  lt_J0_of_besselP (by norm_num) (by norm_num) (by linarith [besselP13_U2])

/-! ### From the certificates to `J₀`

Each certificate is about `bpoly` in `u = z^2/4`; `besselP_eq_bpoly` and the bracket carry it to
`J₀`.  The `u`-interval is chosen to contain the image of the `z`-interval, which is what the two
`nlinarith` steps check. -/

/-- **No zero of `J₀` strictly between the two enclosed ones.** -/
theorem J0_neg_mid {z : ℝ} (h1 : 24049 / 10000 ≤ z) (h2 : z ≤ 55200 / 10000) : J0 z < 0 := by
  have hz0 : (0 : ℝ) ≤ z := by linarith
  have hz6 : z ≤ 6 := by linarith
  have hu1 : (7229 : ℝ) / 5000 ≤ z ^ 2 / 4 := by nlinarith
  have hu2 : z ^ 2 / 4 ≤ (4761 : ℝ) / 625 := by nlinarith
  refine J0_lt_of_besselP hz0 hz6 ?_
  rw [besselP_eq_bpoly]
  exact bpoly12_neg_mid hu1 hu2

/-- **No zero of `J₀` below the first one.** -/
theorem J0_pos_low {z : ℝ} (h1 : 0 ≤ z) (h2 : z ≤ 24048 / 10000) : 0 < J0 z := by
  have hz6 : z ≤ 6 := by linarith
  have hu1 : (0 : ℝ) ≤ z ^ 2 / 4 := by positivity
  have hu2 : z ^ 2 / 4 ≤ (2259009 : ℝ) / 1562500 := by nlinarith
  refine lt_J0_of_besselP h1 hz6 ?_
  rw [besselP_eq_bpoly]
  exact bpoly13_pos_low hu1 hu2

/-! ### Existence of the two zeros

The intermediate value theorem on the sign facts.  This is the EXISTENCE half of the `FirstZeros`
obligation; the uniqueness/indexing half still needs the exclusion grid. -/

theorem exists_zero_I1 : ∃ z ∈ Set.Ioo (24048 / 10000 : ℝ) (24049 / 10000), J0 z = 0 := by
  have hsub : Set.Icc (24048 / 10000 : ℝ) (24049 / 10000) ⊆ Set.Icc (0 : ℝ) 6 :=
    Set.Icc_subset_Icc (by norm_num) (by norm_num)
  have hmem : (0 : ℝ) ∈ Set.Ioo (J0 (24049 / 10000)) (J0 (24048 / 10000)) :=
    ⟨J0_neg_U1, J0_pos_L1⟩
  have hsub2 := intermediate_value_Ioo' (by norm_num : (24048 / 10000 : ℝ) ≤ 24049 / 10000)
    (continuousOn_J0.mono hsub)
  obtain ⟨z, hz, hfz⟩ := hsub2 hmem
  exact ⟨z, hz, hfz⟩

theorem exists_zero_I2 : ∃ z ∈ Set.Ioo (55200 / 10000 : ℝ) (55201 / 10000), J0 z = 0 := by
  have hsub : Set.Icc (55200 / 10000 : ℝ) (55201 / 10000) ⊆ Set.Icc (0 : ℝ) 6 :=
    Set.Icc_subset_Icc (by norm_num) (by norm_num)
  have hmem : (0 : ℝ) ∈ Set.Ioo (J0 (55200 / 10000)) (J0 (55201 / 10000)) :=
    ⟨J0_neg_L2, J0_pos_U2⟩
  have hsub2 := intermediate_value_Ioo (by norm_num : (55200 / 10000 : ℝ) ≤ 55201 / 10000)
    (continuousOn_J0.mono hsub)
  obtain ⟨z, hz, hfz⟩ := hsub2 hmem
  exact ⟨z, hz, hfz⟩

/-! ### The two power comparisons

`j₁^(2/5) < 10/7` and `49/25 < j₂^(2/5)` reduce to the integer-power comparisons
`U₁² < (10/7)⁵` and `L₂² > (49/25)⁵`, both `norm_num`. -/

theorem rpow_j1_lt {j1 : ℝ} (h0 : 0 ≤ j1) (h : j1 < 24049 / 10000) :
    j1 ^ ((2 : ℝ) / 5) < 10 / 7 := by
  have hcast : ((2 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) = (2 : ℝ) / 5 := by norm_num
  have hpow : j1 ^ (2 : ℕ) < (10 / 7 : ℝ) ^ (5 : ℕ) := by nlinarith
  have := rpow_div_lt_of_pow_lt_pow (m := 2) (n := 5) h0 (by norm_num) (by norm_num) hpow
  rwa [hcast] at this

theorem lt_rpow_j2 {j2 : ℝ} (h : 55200 / 10000 < j2) : (49 : ℝ) / 25 < j2 ^ ((2 : ℝ) / 5) := by
  have hcast : ((2 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) = (2 : ℝ) / 5 := by norm_num
  have h0 : (0 : ℝ) ≤ j2 := by linarith
  have hpow : ((49 : ℝ) / 25) ^ (5 : ℕ) < j2 ^ (2 : ℕ) := by nlinarith
  have := lt_rpow_div_of_pow_lt_pow (m := 2) (n := 5) h0 (by norm_num) hpow
  rwa [hcast] at this

/-- `K_2` in closed form: two terms, with the weights `2/3` and `1/3`. -/
theorem K_two (j : ℕ → ℝ) (α x : ℝ) :
    K j 2 α x = 2 / 3 * (j 1) ^ α * J0 (j 1 * x) + 1 / 3 * (j 2) ^ α * J0 (j 2 * x) := by
  have hIcc : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := rfl
  rw [K, hIcc, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2)]
  norm_num

/-- **The write-up's theorem, as a reduction.**  Four numeric facts give the bound. -/
theorem K_two_lt (j : ℕ → ℝ)
    (hA0 : 0 < J0 (j 1 * (99 / 100)))
    (hA : J0 (j 1 * (99 / 100)) < 127 / 10000)
    (hB : J0 (j 2 * (99 / 100)) < -(187 / 10000))
    (hj1 : (j 1) ^ ((2 : ℝ) / 5) < 10 / 7)
    (hj2 : (49 : ℝ) / 25 < (j 2) ^ ((2 : ℝ) / 5)) :
    K j 2 ((2 : ℝ) / 5) (99 / 100) < -(641 / 5250000) := by
  rw [K_two]
  set A := J0 (j 1 * (99 / 100)) with hAdef
  set B := J0 (j 2 * (99 / 100)) with hBdef
  set p := (j 1) ^ ((2 : ℝ) / 5) with hpdef
  set q := (j 2) ^ ((2 : ℝ) / 5) with hqdef
  have hBneg : B ≤ 0 := by linarith
  have h1 : p * A ≤ 10 / 7 * A := mul_le_mul_of_nonneg_right hj1.le hA0.le
  have h2 : q * B ≤ 49 / 25 * B := mul_le_mul_of_nonpos_right hj2.le hBneg
  have hAub : (10 : ℝ) / 7 * A < 10 / 7 * (127 / 10000) :=
    mul_lt_mul_of_pos_left hA (by norm_num)
  have hBub : (49 : ℝ) / 25 * B < 49 / 25 * (-(187 / 10000)) :=
    mul_lt_mul_of_pos_left hB (by norm_num)
  nlinarith [h1, h2, hAub, hBub]

/-- **The refutation.** -/
theorem conjecture_false_of_certificate (j : ℕ → ℝ) (hj : FirstZeros j 2)
    (hA0 : 0 < J0 (j 1 * (99 / 100)))
    (hA : J0 (j 1 * (99 / 100)) < 127 / 10000)
    (hB : J0 (j 2 * (99 / 100)) < -(187 / 10000))
    (hj1 : (j 1) ^ ((2 : ℝ) / 5) < 10 / 7)
    (hj2 : (49 : ℝ) / 25 < (j 2) ^ ((2 : ℝ) / 5)) :
    ¬ Conjecture := by
  intro h
  have hnn := h 2 (by norm_num) j hj ((2 : ℝ) / 5) (99 / 100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlt := K_two_lt j hA0 hA hB hj1 hj2
  linarith

/-! ### The witness, and the refutation

`j 1` and `j 2` are the LEAST zeros of `J₀` in their enclosing intervals.  Taking the infimum is
what makes "nothing below `j 1`" and "nothing strictly between `j 1` and `j 2`" hold BY
CONSTRUCTION on the two sides where no estimate is available.  Exactly one side still needs an
estimate — `(j 1, U₁]`, where a second zero would otherwise be possible — and that is what
`J0_lt_J0_of_lt` supplies. -/

/-- The zero set of `J₀` inside a closed subinterval of `[0,6]` is closed. -/
theorem isClosed_zeroSet {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 6) :
    IsClosed (Set.Icc a b ∩ J0 ⁻¹' {0}) :=
  (continuousOn_J0.mono (Set.Icc_subset_Icc ha hb)).preimage_isClosed_of_isClosed
    isClosed_Icc isClosed_singleton

/-- The least zero of `J₀` in `[L₁, U₁]`. -/
noncomputable def z1 : ℝ := sInf (Set.Icc (24048 / 10000 : ℝ) (24049 / 10000) ∩ J0 ⁻¹' {0})

/-- The least zero of `J₀` in `[L₂, U₂]`. -/
noncomputable def z2 : ℝ := sInf (Set.Icc (55200 / 10000 : ℝ) (55201 / 10000) ∩ J0 ⁻¹' {0})

theorem z1_mem : z1 ∈ Set.Icc (24048 / 10000 : ℝ) (24049 / 10000) ∩ J0 ⁻¹' {0} := by
  refine (isClosed_zeroSet (by norm_num) (by norm_num)).csInf_mem ?_ ?_
  · obtain ⟨z, hz, hfz⟩ := exists_zero_I1
    exact ⟨z, ⟨hz.1.le, hz.2.le⟩, hfz⟩
  · exact BddBelow.mono Set.inter_subset_left bddBelow_Icc

theorem z2_mem : z2 ∈ Set.Icc (55200 / 10000 : ℝ) (55201 / 10000) ∩ J0 ⁻¹' {0} := by
  refine (isClosed_zeroSet (by norm_num) (by norm_num)).csInf_mem ?_ ?_
  · obtain ⟨z, hz, hfz⟩ := exists_zero_I2
    exact ⟨z, ⟨hz.1.le, hz.2.le⟩, hfz⟩
  · exact BddBelow.mono Set.inter_subset_left bddBelow_Icc

theorem z1_least {z : ℝ} (hz : z ∈ Set.Icc (24048 / 10000 : ℝ) (24049 / 10000))
    (h0 : J0 z = 0) : z1 ≤ z :=
  csInf_le (BddBelow.mono Set.inter_subset_left bddBelow_Icc) ⟨hz, h0⟩

theorem z2_least {z : ℝ} (hz : z ∈ Set.Icc (55200 / 10000 : ℝ) (55201 / 10000))
    (h0 : J0 z = 0) : z2 ≤ z :=
  csInf_le (BddBelow.mono Set.inter_subset_left bddBelow_Icc) ⟨hz, h0⟩

theorem J0_z1 : J0 z1 = 0 := z1_mem.2
theorem J0_z2 : J0 z2 = 0 := z2_mem.2

/-- Strict, because `J₀(U₁) < 0` so `U₁` is not a zero. -/
theorem z1_lt : z1 < 24049 / 10000 := by
  rcases lt_or_eq_of_le z1_mem.1.2 with h | h
  · exact h
  · exact absurd (h ▸ J0_z1) (ne_of_lt J0_neg_U1)

/-- Strict, because `J₀(L₂) < 0` so `L₂` is not a zero. -/
theorem z2_gt : 55200 / 10000 < z2 := by
  rcases lt_or_eq_of_le z2_mem.1.1 with h | h
  · exact h
  · exfalso
    have hz : J0 (55200 / 10000 : ℝ) = 0 := by rw [h]; exact J0_z2
    linarith [J0_neg_L2, hz]

/-- The witness: the first two positive zeros. -/
noncomputable def jj : ℕ → ℝ := fun m => if m = 1 then z1 else z2

theorem jj_one : jj 1 = z1 := by norm_num [jj]
theorem jj_two : jj 2 = z2 := by norm_num [jj]

theorem firstZeros_jj : FirstZeros jj 2 where
  pos := by
    intro m h1 h2
    interval_cases m
    · rw [jj_one]; linarith [z1_mem.1.1]
    · rw [jj_two]; linarith [z2_mem.1.1]
  isZero := by
    intro m h1 h2
    interval_cases m
    · rw [jj_one]; exact J0_z1
    · rw [jj_two]; exact J0_z2
  step := by
    intro m h1 h2
    have hm : m ≤ 1 := by omega
    interval_cases m
    · rw [jj_one, jj_two]; linarith [z1_mem.1.2, z2_mem.1.1]
  first := by
    intro z hz0 hlt
    rw [jj_one] at hlt
    by_cases hL : z ≤ 24048 / 10000
    · exact ne_of_gt (J0_pos_low hz0.le hL)
    · rw [not_le] at hL
      intro h0
      have : z1 ≤ z := z1_least ⟨hL.le, by linarith [z1_mem.1.2]⟩ h0
      linarith
  between := by
    intro m h1 h2 z hlo hhi
    have hm : m ≤ 1 := by omega
    interval_cases m
    rw [jj_one] at hlo
    rw [jj_two] at hhi
    by_cases hU : z ≤ 24049 / 10000
    · -- (z1, U₁] : strict decrease past the zero
      have hz1pos : 0 < z1 := by linarith [z1_mem.1.1]
      have := J0_lt_J0_of_lt hz1pos hlo (by linarith)
      rw [J0_z1] at this
      exact ne_of_lt this
    · rw [not_le] at hU
      by_cases hL2 : z ≤ 55200 / 10000
      · exact ne_of_lt (J0_neg_mid hU.le hL2)
      · rw [not_le] at hL2
        intro h0
        have : z2 ≤ z := z2_least ⟨hL2.le, by linarith [z2_mem.1.2]⟩ h0
        linarith

/-! ### The four numeric facts, at the witness -/

theorem A_pos : 0 < J0 (jj 1 * (99 / 100)) := by
  rw [jj_one]
  refine J0_pos_low (by nlinarith [z1_mem.1.1]) ?_
  nlinarith [z1_mem.1.2]

theorem A_upper : J0 (jj 1 * (99 / 100)) < 127 / 10000 := by
  rw [jj_one]
  have h1 : (0 : ℝ) ≤ z1 * (99 / 100) := by nlinarith [z1_mem.1.1]
  have h6 : z1 * (99 / 100) ≤ 6 := by nlinarith [z1_mem.1.2]
  refine J0_lt_of_besselP h1 h6 ?_
  rw [besselP_eq_bpoly]
  refine bpoly12_A_bound ?_ ?_
  · nlinarith [z1_mem.1.1]
  · nlinarith [z1_mem.1.2]

theorem B_upper : J0 (jj 2 * (99 / 100)) < -(187 / 10000) := by
  rw [jj_two]
  have h1 : (0 : ℝ) ≤ z2 * (99 / 100) := by nlinarith [z2_mem.1.1]
  have h6 : z2 * (99 / 100) ≤ 6 := by nlinarith [z2_mem.1.2]
  refine J0_lt_of_besselP h1 h6 ?_
  rw [besselP_eq_bpoly]
  have := bpoly12_B_bound (u := (z2 * (99 / 100)) ^ 2 / 4) (by nlinarith [z2_mem.1.1])
    (by nlinarith [z2_mem.1.2])
  linarith

theorem rpow_A : (jj 1) ^ ((2 : ℝ) / 5) < 10 / 7 := by
  rw [jj_one]
  exact rpow_j1_lt (by linarith [z1_mem.1.1]) z1_lt

theorem rpow_B : (49 : ℝ) / 25 < (jj 2) ^ ((2 : ℝ) / 5) := by
  rw [jj_two]
  exact lt_rpow_j2 z2_gt

/-- **The conjecture is false.**  No carried hypotheses. -/
theorem conjecture_false : ¬ Conjecture :=
  conjecture_false_of_certificate jj firstZeros_jj A_pos A_upper B_upper rpow_A rpow_B

end Principia.MathDB.P365454
