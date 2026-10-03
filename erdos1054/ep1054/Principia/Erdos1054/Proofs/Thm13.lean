/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Spine
import Principia.Erdos1054.Density
import Principia.Erdos1054.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

/-!
# Erdős 1054 (EP1054.tex) — the proof of Theorem 1.3 (`thm:almost-log-tail`), lines 2064–2107

Discharges the `Thm13` package of `Principia.Erdos1054.Spine`. Nothing here uses the finite
representability computation or Helfgott: the only paper inputs are the hypotheses of the links.

Leaves (from the definitions and Mathlib alone):
* `leaf_UpperTails_Claim_AlmostLogTail_momentArith` (lines 2075–2079) — with
  `y = T^{b_j} (log T)^{3/(j-1)} ≤ E` and `1 - j < 0`, `E^{1-j} ≤ y^{1-j} = T^{-(j+1)} (log T)^{-3}`
  (`b_j (1 - j) = -(j+1)`); valid for every `T ≥ 3`.
* `leaf_UpperTails_Claim_RoughNonsquarefree` (lines 2080–2084, 2130–2133) — a `y`-rough
  nonsquarefree `N ≤ X` has `p² ∣ N` for a prime `⌊y⌋ < p ≤ X`; union bound over all
  `n ∈ (⌊y⌋, ⌊X⌋]`, `#{N ≤ X : n² ∣ N} ≤ X/n²`, and Mathlib's `sum_Ioo_inv_sq_le`
  (`∑_{k<n} 1/n² ≤ 2/(k+1) ≤ 2/y`). Constant `C = 2`.
* `leaf_UpperTails_Claim_LscaleRatio` (lines 2093–2096) — `log E / log T → b_j` (squeeze:
  `log E = b_j log T + (3/(j-1)) log log T + O(1)`), then twice the general fact
  `g → ∞, f/g → L > 0 ⟹ log f / log g → 1` (`tendsto_log_div_log`) gives
  `log₂E/log₂T → 1` and `log₃E/log₃T → 1`; finally `L(E) = L(T) · r₃/(r₁ r₂)`.

Links (from exactly the dependencies the spine names):
* `link_UpperTails_Claim_AlmostLogTail_main` (lines 2073–2092) — every `N ∈ V_E` is in the
  target set, or in `G_E ∩ V_E` (density zero, `Prop_FmEnvelope`), or has a representation with
  cofactor `> E` and `e d = f(N) ≤ T N` (`Lem_Moment`'s `eq:large-count` at `k = j`, `A = T`, and
  `momentArith`), or is `E`-rough nonsquarefree (`Claim_VA_rough` + `Claim_RoughNonsquarefree`),
  or is odd (`2 ∈ 𝒦_E`) and unrepresented (`Lem_AnalyticOddRepresentability`, density zero).
  `V_E` has density `d(V_E)` (`Claim_VA_density`). Constants: `C` of `RoughNonsquarefree`,
  `C_j` of `lem:moment`, `T₀ = max(T₀(momentArith), e)` (so `E ≥ T ≥ e ≥ 2`).
* `link_UpperTails_Claim_AlmostLogTail_fixedJ` (lines 2093–2104) — `cor:fm-envelope-tail` at
  `A = E` with `ε₁ = min(ε/4, e^{-γ}/2)`, `L(E) ≥ (1/b_j − ε/4) L(T)`, and both error terms
  `≤ (ε/4)/(log T)² ≤ (ε/4) L(T)` (`L(T) ≥ 1/(log T)²` once `log₃ T ≥ 1`).
* `link_Eq_AlmostLogTail` (lines 2103–2105, `j → ∞`) — `j = max(3, ⌈2/ε⌉)` gives
  `e^{-γ}/2 − e^{-γ}/(2b_j) = e^{-γ}/(j+1) ≤ ε/2`.
* `link_Thm_AlmostLogTail_posLowerDens` (lines 184–185) — apply `eq:almost-log-tail` at
  `T' = max(T, T₀, e^{e^e})` with `ε = e^{-γ}/4`; `L(T') > 0`; monotonicity of `lowerDens`.
* `link_Thm_AlmostLogTail_limsup` (lines 185–188) — a set of positive lower density is infinite.

`Thm_AlmostLogTail` itself is the conjunction of `Eq_AlmostLogTail`,
`Thm_AlmostLogTail_posLowerDens` and `Thm_AlmostLogTail_limsup`, assembled by `And.intro` in the
spine; it gets no declaration here.
-/

namespace Principia.Erdos1054.Proofs.Thm13

open Principia.Erdos1054 Principia.Erdos1054.UpperTails Filter
open scoped Topology

/-! ## Counting helpers -/

/-- `cnt` only sees `1 ≤ N ≤ ⌊X⌋`: a pointwise inclusion there suffices for monotonicity. -/
lemma cnt_le_of_forall {S T : Set ℕ} {X : ℝ}
    (h : ∀ N : ℕ, 1 ≤ N → N ≤ ⌊X⌋₊ → N ∈ S → N ∈ T) : cnt S X ≤ cnt T X := by
  unfold cnt
  apply Finset.card_le_card
  intro N hN
  rw [mem_cntFinset] at hN ⊢
  exact ⟨hN.1, h N hN.1.1 hN.1.2 hN.2⟩

/-- Union bound for `cnt` over a finite index set. -/
lemma cnt_biUnion_le {ι : Type*} (s : Finset ι) (A : ι → Set ℕ) (X : ℝ) :
    cnt (⋃ i ∈ s, A i) X ≤ ∑ i ∈ s, cnt (A i) X := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cnt_empty]
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (cnt_union_le _ _ X).trans (Nat.add_le_add_left ih _)

/-- The odd unrepresented integers have density zero (the `o(X / log₃ X)` clause of
`lem:analytic-odd-representability`, with `log₃ X ≥ 1` for `X ≥ e^{e^e}`). -/
lemma densZero_oddUnrep (h : Lem_AnalyticOddRepresentability_LittleO) : DensZero oddUnrep := by
  rw [densZero_iff_exists_real]
  intro ε hε
  obtain ⟨X₀, hX₀⟩ := h ε hε
  refine ⟨max X₀ (Real.exp (Real.exp (Real.exp 1))), fun X hX => ?_⟩
  have hX' : Real.exp (Real.exp (Real.exp 1)) ≤ X := le_trans (le_max_right _ _) hX
  have h1 := hX₀ X (le_trans (le_max_left _ _) hX)
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX'
  have l1 : Real.exp (Real.exp 1) ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).2 hX'
  have l1pos : 0 < Real.log X := lt_of_lt_of_le (Real.exp_pos _) l1
  have l2 : Real.exp 1 ≤ Real.log (Real.log X) := (Real.le_log_iff_exp_le l1pos).2 l1
  have l2pos : 0 < Real.log (Real.log X) := lt_of_lt_of_le (Real.exp_pos _) l2
  have l3 : 1 ≤ logIt 3 X := (Real.le_log_iff_exp_le l2pos).2 l2
  calc (cnt oddUnrep X : ℝ) ≤ ε * (X / logIt 3 X) := h1
    _ ≤ ε * X := mul_le_mul_of_nonneg_left (div_le_self hXpos.le l3) hε.le

/-! ## Elementary facts about `L`, `b_j`, `E`, `e^{-γ}` -/

lemma Lscale_eq (x : ℝ) :
    Lscale x = Real.log (Real.log (Real.log x)) / (Real.log x * Real.log (Real.log x)) := rfl

lemma Lscale_nonneg {T : ℝ} (hT : Real.exp (Real.exp 1) ≤ T) : 0 ≤ Lscale T := by
  have hTpos : 0 < T := lt_of_lt_of_le (Real.exp_pos _) hT
  have h1 : Real.exp 1 ≤ Real.log T := (Real.le_log_iff_exp_le hTpos).2 hT
  have h1pos : 0 < Real.log T := lt_of_lt_of_le (Real.exp_pos 1) h1
  have h2 : 1 ≤ Real.log (Real.log T) := (Real.le_log_iff_exp_le h1pos).2 h1
  have h3 : 0 ≤ Real.log (Real.log (Real.log T)) := Real.log_nonneg h2
  rw [Lscale_eq]
  exact div_nonneg h3 (mul_nonneg h1pos.le (by linarith))

lemma log_pos_of_ge {T : ℝ} (hT : Real.exp (Real.exp (Real.exp 1)) ≤ T) : 0 < Real.log T := by
  have hTpos : 0 < T := lt_of_lt_of_le (Real.exp_pos _) hT
  have h1 : Real.exp (Real.exp 1) ≤ Real.log T := (Real.le_log_iff_exp_le hTpos).2 hT
  exact lt_of_lt_of_le (Real.exp_pos _) h1

/-- `L(T) ≥ 1/(log T)²` once `log₃ T ≥ 1`. -/
lemma inv_sq_log_le_Lscale {T : ℝ} (hT : Real.exp (Real.exp (Real.exp 1)) ≤ T) :
    1 / (Real.log T) ^ 2 ≤ Lscale T := by
  have hTpos : 0 < T := lt_of_lt_of_le (Real.exp_pos _) hT
  have h1 : Real.exp (Real.exp 1) ≤ Real.log T := (Real.le_log_iff_exp_le hTpos).2 hT
  have h1pos : 0 < Real.log T := lt_of_lt_of_le (Real.exp_pos _) h1
  have h2 : Real.exp 1 ≤ Real.log (Real.log T) := (Real.le_log_iff_exp_le h1pos).2 h1
  have h2pos : 0 < Real.log (Real.log T) := lt_of_lt_of_le (Real.exp_pos _) h2
  have h3 : 1 ≤ Real.log (Real.log (Real.log T)) := (Real.le_log_iff_exp_le h2pos).2 h2
  have h21 : Real.log (Real.log T) ≤ Real.log T := by
    have := Real.log_le_sub_one_of_pos h1pos
    linarith
  rw [Lscale_eq]
  have hprod : 0 < Real.log T * Real.log (Real.log T) := mul_pos h1pos h2pos
  calc 1 / Real.log T ^ 2 ≤ 1 / (Real.log T * Real.log (Real.log T)) := by
        apply one_div_le_one_div_of_le hprod
        rw [pow_two]
        exact mul_le_mul_of_nonneg_left h21 h1pos.le
    _ ≤ _ := div_le_div_of_nonneg_right h3 hprod.le

lemma Lscale_pos {T : ℝ} (hT : Real.exp (Real.exp (Real.exp 1)) ≤ T) : 0 < Lscale T :=
  lt_of_lt_of_le (by have := log_pos_of_ge hT; positivity) (inv_sq_log_le_Lscale hT)

lemma expNegGamma_le_one : Real.exp (-eulerGamma) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  have : (1 : ℝ) / 2 < eulerGamma := Real.one_half_lt_eulerMascheroniConstant
  linarith

lemma one_le_bj {j : ℕ} (hj : 3 ≤ j) : 1 ≤ bj j := by
  have hj3 : (3 : ℝ) ≤ j := by exact_mod_cast hj
  unfold bj
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- `E = ⌈T^{b_j} (log T)^{3/(j-1)}⌉ ≥ T` for `T ≥ e`. -/
lemma le_Ej {j : ℕ} (hj : 3 ≤ j) {T : ℝ} (hT : Real.exp 1 ≤ T) : T ≤ (Ej j T : ℝ) := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hT1 : 1 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hlog : 1 ≤ Real.log T := (Real.le_log_iff_exp_le hTpos).2 hT
  have hj3 : (3 : ℝ) ≤ j := by exact_mod_cast hj
  have hc : 0 ≤ (3 : ℝ) / ((j : ℝ) - 1) := div_nonneg (by norm_num) (by linarith)
  have h1 : T ≤ T ^ bj j := by
    calc T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
      _ ≤ T ^ bj j := Real.rpow_le_rpow_of_exponent_le hT1 (one_le_bj hj)
  have h2 : 1 ≤ Real.log T ^ ((3 : ℝ) / ((j : ℝ) - 1)) := Real.one_le_rpow hlog hc
  have h3 : T ^ bj j ≤ T ^ bj j * Real.log T ^ ((3 : ℝ) / ((j : ℝ) - 1)) :=
    le_mul_of_one_le_right (by positivity) h2
  exact le_trans (h1.trans h3) (Nat.le_ceil _)

/-! ## Asymptotics of `L(E)` -/

/-- If `g → ∞` and `f/g → L > 0`, then `log f / log g → 1`. -/
lemma tendsto_log_div_log {f g : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hg : Tendsto g atTop atTop)
    (hfg : Tendsto (fun T => f T / g T) atTop (𝓝 L)) :
    Tendsto (fun T => Real.log (f T) / Real.log (g T)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun T => Real.log (f T / g T)) atTop (𝓝 (Real.log L)) := hfg.log hL.ne'
  have h2 : Tendsto (fun T => Real.log (g T)) atTop atTop := Real.tendsto_log_atTop.comp hg
  have h3 : Tendsto (fun T => Real.log (f T / g T) / Real.log (g T) + 1) atTop (𝓝 (0 + 1)) :=
    (h1.div_atTop h2).add tendsto_const_nhds
  rw [zero_add] at h3
  refine h3.congr' ?_
  filter_upwards [hg.eventually_gt_atTop 1, hfg.eventually (lt_mem_nhds hL)] with T hg1 hq
  have hgT : 0 < g T := by linarith
  have hfT : 0 < f T := by
    have := mul_pos hq hgT
    rwa [div_mul_cancel₀ _ hgT.ne'] at this
  have hlg : 0 < Real.log (g T) := Real.log_pos hg1
  rw [Real.log_div hfT.ne' hgT.ne', sub_div, div_self hlg.ne', sub_add_cancel]

/-- `log log T / log T → 0`. -/
lemma tendsto_loglog_div_log :
    Tendsto (fun T : ℝ => Real.log (Real.log T) / Real.log T) atTop (𝓝 0) :=
  (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp Real.tendsto_log_atTop

/-- `log E / log T → b_j` for `E = ⌈T^{b_j} (log T)^{3/(j-1)}⌉`. -/
lemma tendsto_logEj_div {j : ℕ} (hj : 3 ≤ j) :
    Tendsto (fun T => Real.log (Ej j T : ℝ) / Real.log T) atTop (𝓝 (bj j)) := by
  have hj3 : (3 : ℝ) ≤ j := by exact_mod_cast hj
  set b := bj j with hb
  set c : ℝ := 3 / ((j : ℝ) - 1) with hc
  have hc0 : 0 ≤ c := div_nonneg (by norm_num) (by linarith)
  have hb1 : 1 ≤ b := one_le_bj hj
  have hlow : Tendsto (fun T => b + c * (Real.log (Real.log T) / Real.log T)) atTop (𝓝 b) := by
    have h := tendsto_const_nhds (x := b) |>.add (tendsto_loglog_div_log.const_mul c)
    simpa using h
  have hup : Tendsto (fun T => b + c * (Real.log (Real.log T) / Real.log T) +
      Real.log 2 / Real.log T) atTop (𝓝 b) := by
    have h := hlow.add ((tendsto_const_nhds (x := Real.log 2)).div_atTop Real.tendsto_log_atTop)
    simpa using h
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have key : ∀ T : ℝ, Real.exp 1 ≤ T →
      0 < Real.log T ∧
      Real.log (T ^ b * Real.log T ^ c) = b * Real.log T + c * Real.log (Real.log T) ∧
      1 ≤ T ^ b * Real.log T ^ c := by
    intro T hT
    have hTpos : 0 < T := by linarith
    have hlog : 1 ≤ Real.log T := (Real.le_log_iff_exp_le hTpos).2 hT
    have hlpos : 0 < Real.log T := by linarith
    refine ⟨hlpos, ?_, ?_⟩
    · rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hTpos,
        Real.log_rpow hlpos]
    · exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by linarith) (by linarith))
        (Real.one_le_rpow hlog hc0)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with T hT
    obtain ⟨hlpos, hly, hy1⟩ := key T hT
    have hEy : T ^ b * Real.log T ^ c ≤ (Ej j T : ℝ) := Nat.le_ceil _
    have h1 : Real.log (T ^ b * Real.log T ^ c) ≤ Real.log (Ej j T : ℝ) :=
      Real.log_le_log (by linarith) hEy
    rw [hly] at h1
    rw [le_div_iff₀ hlpos]
    have e : (b + c * (Real.log (Real.log T) / Real.log T)) * Real.log T =
        b * Real.log T + c * Real.log (Real.log T) := by
      field_simp
    linarith
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with T hT
    obtain ⟨hlpos, hly, hy1⟩ := key T hT
    have hEy : T ^ b * Real.log T ^ c ≤ (Ej j T : ℝ) := Nat.le_ceil _
    have hEy' : (Ej j T : ℝ) < T ^ b * Real.log T ^ c + 1 := Nat.ceil_lt_add_one (by linarith)
    have hEpos : 0 < (Ej j T : ℝ) := by linarith
    have h1 : Real.log (Ej j T : ℝ) ≤ Real.log (2 * (T ^ b * Real.log T ^ c)) :=
      Real.log_le_log hEpos (by linarith)
    rw [Real.log_mul two_ne_zero (by linarith), hly] at h1
    rw [div_le_iff₀ hlpos]
    have e : (b + c * (Real.log (Real.log T) / Real.log T) + Real.log 2 / Real.log T) *
        Real.log T = b * Real.log T + c * Real.log (Real.log T) + Real.log 2 := by
      field_simp
    linarith

end Principia.Erdos1054.Proofs.Thm13

namespace Principia.Erdos1054.Proofs

open Principia.Erdos1054 Principia.Erdos1054.UpperTails Principia.Erdos1054.Proofs.Thm13 Filter
open scoped Topology

/-! ## Leaves -/

/-- EP1054.tex lines 2075–2079: `T^{j+1} E^{1-j} ≤ (log T)^{-3}` (for every `T ≥ 3`). -/
theorem leaf_UpperTails_Claim_AlmostLogTail_momentArith :
    Principia.Erdos1054.UpperTails.Claim_AlmostLogTail_momentArith := by
  intro j hj
  refine ⟨3, fun T hT => ?_⟩
  have hT1 : (1 : ℝ) < T := by linarith
  have hTpos : (0 : ℝ) < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos hT1
  have hj3 : (3 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hj1 : (0 : ℝ) < (j : ℝ) - 1 := by linarith
  set y : ℝ := T ^ bj j * Real.log T ^ ((3 : ℝ) / ((j : ℝ) - 1)) with hy
  have hypos : 0 < y := by positivity
  have hEy : y ≤ (Ej j T : ℝ) := Nat.le_ceil y
  have h1 : (Ej j T : ℝ) ^ (1 - (j : ℝ)) ≤ y ^ (1 - (j : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hypos hEy (by linarith)
  have hexp1 : bj j * (1 - (j : ℝ)) = -(((j + 1 : ℕ) : ℝ)) := by
    unfold bj
    push_cast
    field_simp
    ring
  have hexp2 : (3 : ℝ) / ((j : ℝ) - 1) * (1 - (j : ℝ)) = -((3 : ℕ) : ℝ) := by
    field_simp
    push_cast
    ring
  have h2 : y ^ (1 - (j : ℝ)) = (T ^ (j + 1))⁻¹ * ((Real.log T) ^ 3)⁻¹ := by
    rw [hy, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hTpos.le,
      ← Real.rpow_mul hlog.le, hexp1, hexp2, Real.rpow_neg hTpos.le, Real.rpow_neg hlog.le,
      Real.rpow_natCast, Real.rpow_natCast]
  have hTj : (0 : ℝ) < T ^ (j + 1) := by positivity
  calc T ^ (j + 1) * (Ej j T : ℝ) ^ (1 - (j : ℝ)) ≤ T ^ (j + 1) * y ^ (1 - (j : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 hTj.le
    _ = 1 / (Real.log T) ^ 3 := by
        rw [h2, ← mul_assoc, mul_inv_cancel₀ hTj.ne', one_mul, one_div]

/-- EP1054.tex lines 2080–2084, 2130–2133: `#{N ≤ X : N y-rough, not squarefree} ≤ 2X/y`. -/
theorem leaf_UpperTails_Claim_RoughNonsquarefree :
    Principia.Erdos1054.UpperTails.Claim_RoughNonsquarefree := by
  refine ⟨2, fun y hy X hX => ?_⟩
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hX0 : (0 : ℝ) ≤ X := by linarith
  set K := ⌊y⌋₊ with hK
  set M := ⌊X⌋₊ with hM
  have hsub : cnt {N : ℕ | IsRough y N ∧ ¬ Squarefree N} X ≤
      cnt (⋃ n ∈ Finset.Ioo K (M + 1), {N : ℕ | n ^ 2 ∣ N}) X := by
    apply cnt_le_of_forall
    rintro N hN1 hNM ⟨hR, hsq⟩
    have hex : ∃ p : ℕ, p.Prime ∧ p * p ∣ N := by
      by_contra hcon
      apply hsq
      rw [Nat.squarefree_iff_prime_squarefree]
      intro x hx hxx
      exact hcon ⟨x, hx, hxx⟩
    obtain ⟨p, hp', hpp⟩ := hex
    have hN0 : N ≠ 0 := by omega
    have hpN : p ∣ N := (Dvd.intro p rfl).trans hpp
    have hpf : p ∈ N.primeFactors := Nat.mem_primeFactors.2 ⟨hp', hpN, hN0⟩
    have hyp : y < (p : ℝ) := hR p hpf
    have hKp : K < p := (Nat.floor_lt hy0).2 hyp
    have hpN' : p * p ≤ N := Nat.le_of_dvd (by omega) hpp
    have hp1 : 1 ≤ p := hp'.one_lt.le
    have hpM : p < M + 1 := by nlinarith
    refine Set.mem_iUnion₂.2 ⟨p, Finset.mem_Ioo.2 ⟨hKp, hpM⟩, ?_⟩
    show p ^ 2 ∣ N
    rw [pow_two]
    exact hpp
  have hsum := cnt_biUnion_le (Finset.Ioo K (M + 1)) (fun n : ℕ => {N : ℕ | n ^ 2 ∣ N}) X
  have h1 : (cnt {N : ℕ | IsRough y N ∧ ¬ Squarefree N} X : ℝ) ≤
      ∑ n ∈ Finset.Ioo K (M + 1), (cnt {N : ℕ | n ^ 2 ∣ N} X : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast hsub.trans hsum
  have h2 : ∑ n ∈ Finset.Ioo K (M + 1), (cnt {N : ℕ | n ^ 2 ∣ N} X : ℝ) ≤
      ∑ n ∈ Finset.Ioo K (M + 1), X * ((n : ℝ) ^ 2)⁻¹ := by
    apply Finset.sum_le_sum
    intro n _
    have := cnt_dvd_le (n ^ 2) hX0
    rw [div_eq_mul_inv] at this
    push_cast at this
    exact this
  have h3 : ∑ n ∈ Finset.Ioo K (M + 1), X * ((n : ℝ) ^ 2)⁻¹ ≤ X * (2 / ((K : ℝ) + 1)) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le K (M + 1)) hX0
  have hKy : y < (K : ℝ) + 1 := Nat.lt_floor_add_one y
  have hypos : (0 : ℝ) < y := by linarith
  have h4 : 2 / ((K : ℝ) + 1) ≤ 2 / y :=
    div_le_div_of_nonneg_left (by norm_num) hypos hKy.le
  have h5 : X * (2 / ((K : ℝ) + 1)) ≤ X * (2 / y) := mul_le_mul_of_nonneg_left h4 hX0
  calc (cnt {N : ℕ | IsRough y N ∧ ¬ Squarefree N} X : ℝ) ≤ X * (2 / y) :=
        h1.trans (h2.trans (h3.trans h5))
    _ = 2 * X / y := by ring

/-- EP1054.tex lines 2093–2096: `L(E) = (1/b_j + o(1)) L(T)`. -/
theorem leaf_UpperTails_Claim_LscaleRatio :
    Principia.Erdos1054.UpperTails.Claim_LscaleRatio := by
  intro j hj ε hε
  have hb1 : 1 ≤ bj j := one_le_bj hj
  have hb0 : 0 < bj j := by linarith
  have hlogT : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have r1 := tendsto_logEj_div hj
  have r2 : Tendsto (fun T => Real.log (Real.log (Ej j T : ℝ)) / Real.log (Real.log T)) atTop
      (𝓝 1) := tendsto_log_div_log hb0 hlogT r1
  have hlog2T : Tendsto (fun T => Real.log (Real.log T)) atTop atTop := hlogT.comp hlogT
  have r3 : Tendsto (fun T => Real.log (Real.log (Real.log (Ej j T : ℝ))) /
      Real.log (Real.log (Real.log T))) atTop (𝓝 1) := tendsto_log_div_log one_pos hlog2T r2
  have hq := r3.div (r1.mul r2) (by rw [mul_one]; exact hb0.ne')
  rw [mul_one] at hq
  have hev : ∀ᶠ T in atTop, |Real.log (Real.log (Real.log (Ej j T : ℝ))) /
      Real.log (Real.log (Real.log T)) / (Real.log (Ej j T : ℝ) / Real.log T *
        (Real.log (Real.log (Ej j T : ℝ)) / Real.log (Real.log T))) - 1 / bj j| < ε := by
    have := (Metric.tendsto_nhds.1 hq) ε hε
    filter_upwards [this] with T hT
    rwa [Real.dist_eq] at hT
  have hbig : ∀ᶠ T in atTop, Real.exp (Real.exp (Real.exp 1)) ≤ T := eventually_ge_atTop _
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 (hev.and hbig)
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨hq', hT'⟩ := hT₀ T hT
  have hTpos : 0 < T := lt_of_lt_of_le (Real.exp_pos _) hT'
  have h1 : Real.exp (Real.exp 1) ≤ Real.log T := (Real.le_log_iff_exp_le hTpos).2 hT'
  have h1pos : 0 < Real.log T := lt_of_lt_of_le (Real.exp_pos _) h1
  have h2 : Real.exp 1 ≤ Real.log (Real.log T) := (Real.le_log_iff_exp_le h1pos).2 h1
  have h2pos : 0 < Real.log (Real.log T) := lt_of_lt_of_le (Real.exp_pos _) h2
  have h3 : 1 ≤ Real.log (Real.log (Real.log T)) := (Real.le_log_iff_exp_le h2pos).2 h2
  have h3pos : 0 < Real.log (Real.log (Real.log T)) := by linarith
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hee : Real.exp 1 ≤ Real.exp (Real.exp (Real.exp 1)) := by
    rw [Real.exp_le_exp]
    have := Real.add_one_le_exp (Real.exp 1)
    linarith
  have hET : T ≤ (Ej j T : ℝ) := le_Ej hj (le_trans hee hT')
  have hE1 : Real.log T ≤ Real.log (Ej j T : ℝ) := Real.log_le_log hTpos hET
  have hE1pos : 0 < Real.log (Ej j T : ℝ) := by linarith
  have hE2 : Real.log (Real.log T) ≤ Real.log (Real.log (Ej j T : ℝ)) :=
    Real.log_le_log h1pos hE1
  have hE2pos : 0 < Real.log (Real.log (Ej j T : ℝ)) := by linarith
  have hLT : 0 ≤ Lscale T := by
    rw [Lscale_eq]
    positivity
  have hid : Lscale (Ej j T : ℝ) = Lscale T *
      (Real.log (Real.log (Real.log (Ej j T : ℝ))) / Real.log (Real.log (Real.log T)) /
        (Real.log (Ej j T : ℝ) / Real.log T *
          (Real.log (Real.log (Ej j T : ℝ)) / Real.log (Real.log T)))) := by
    rw [Lscale_eq, Lscale_eq]
    field_simp
  rw [hid]
  set q := Real.log (Real.log (Real.log (Ej j T : ℝ))) / Real.log (Real.log (Real.log T)) /
    (Real.log (Ej j T : ℝ) / Real.log T *
      (Real.log (Real.log (Ej j T : ℝ)) / Real.log (Real.log T))) with hqdef
  have e : Lscale T * q - Lscale T / bj j = Lscale T * (q - 1 / bj j) := by ring
  rw [e, abs_mul, abs_of_nonneg hLT, mul_comm ε]
  exact mul_le_mul_of_nonneg_left hq'.le hLT

/-! ## Links -/

/-- EP1054.tex lines 2073–2092: `d(V_E) − C_j/(log T)³ − O(1/E) ≤ lowerdens{…}`. -/
theorem link_UpperTails_Claim_AlmostLogTail_main :
    Principia.Erdos1054.Spine.Link_UpperTails_Claim_AlmostLogTail_main := by
  intro hFE hMom hArith hVAr hNSQ hOdd hVAd
  obtain ⟨C, hC⟩ := hNSQ
  refine ⟨C, fun j hj => ?_⟩
  obtain ⟨Ck, ⟨hCk0, _⟩, _, hLC⟩ := hMom j (by omega)
  obtain ⟨T₁, hT₁⟩ := hArith j hj
  refine ⟨Ck, max T₁ (Real.exp 1), fun T hT => ?_⟩
  have hTe : Real.exp 1 ≤ T := le_trans (le_max_right _ _) hT
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hT2 : 2 ≤ T := by linarith
  have hET : T ≤ (Ej j T : ℝ) := le_Ej hj hTe
  have harith := hT₁ T (le_trans (le_max_left _ _) hT)
  set E : ℕ := Ej j T with hE
  have hE2 : (2 : ℝ) ≤ (E : ℝ) := by linarith
  have hEpos : (0 : ℝ) < (E : ℝ) := by linarith
  set S := {N : ℕ | N ∈ R ∧ Squarefree N ∧ T * (N : ℝ) < (f N : ℝ)} with hS
  set V := VA (E : ℝ) with hV
  set G := Gcov ⌊(E : ℝ)⌋₊ ∩ VA (E : ℝ) with hG
  set Lc := largeCofactorSet T (E : ℝ) with hLc
  set Q := {N : ℕ | IsRough (E : ℝ) N ∧ ¬ Squarefree N} with hQ
  have hcover : V ⊆ S ∪ (G ∪ (Lc ∪ (Q ∪ oddUnrep))) := by
    intro N hN
    by_cases hR : N ∈ R
    · by_cases hsq : Squarefree N
      · by_cases hbig : T * (N : ℝ) < (f N : ℝ)
        · exact Or.inl ⟨hR, hsq, hbig⟩
        · right
          obtain ⟨e, d, he1, hd1, hfed, hNF⟩ := f_mem_Fform N hR
          by_cases heE : e ≤ E
          · left
            refine ⟨⟨e, d, he1, ?_, hd1, hNF⟩, hN⟩
            rw [Nat.floor_natCast]
            exact heE
          · right
            left
            refine ⟨e, d, he1, hd1, hNF, ?_, ?_⟩
            · exact_mod_cast (lt_of_not_ge heE)
            · have hfc : (f N : ℝ) = (e : ℝ) * (d : ℝ) := by
                rw [hfed, Nat.cast_mul]
              rw [← hfc]
              exact not_lt.1 hbig
      · right
        right
        right
        left
        exact ⟨(hVAr (E : ℝ) hE2).2 N hN, hsq⟩
    · right
      right
      right
      right
      refine ⟨?_, hR⟩
      have h2K : 2 ∈ KA (E : ℝ) := (hVAr (E : ℝ) hE2).1 2 Nat.prime_two (by exact_mod_cast hE2)
      have hn2 : ¬ 2 ∣ N := hN 2 h2K
      exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hn2)
  have hcnt : ∀ X : ℝ, (cnt V X : ℝ) ≤
      cnt S X + cnt G X + cnt Lc X + cnt Q X + cnt oddUnrep X := by
    intro X
    have h1 := cnt_mono hcover X
    have h2 := cnt_union_le S (G ∪ (Lc ∪ (Q ∪ oddUnrep))) X
    have h3 := cnt_union_le G (Lc ∪ (Q ∪ oddUnrep)) X
    have h4 := cnt_union_le Lc (Q ∪ oddUnrep) X
    have h5 := cnt_union_le Q oddUnrep X
    have : cnt V X ≤ cnt S X + cnt G X + cnt Lc X + cnt Q X + cnt oddUnrep X := by omega
    exact_mod_cast this
  have hVd : HasDens V (dV (E : ℝ)) := (hVAd (E : ℝ) hE2).1
  have hGz : DensZero G := (hFE (E : ℝ) hE2).1
  have hOz : DensZero oddUnrep := densZero_oddUnrep hOdd.2
  have hA : Ck * T ^ (j + 1) * (E : ℝ) ^ (1 - (j : ℝ)) ≤ Ck / Real.log T ^ 3 := by
    rw [mul_assoc]
    calc Ck * (T ^ (j + 1) * (E : ℝ) ^ (1 - (j : ℝ))) ≤ Ck * (1 / Real.log T ^ 3) :=
          mul_le_mul_of_nonneg_left harith hCk0.le
      _ = Ck / Real.log T ^ 3 := by ring
  apply le_of_forall_sub_le
  intro δ hδ
  apply le_lowerDens_of_eventually
  have ev1 : ∀ᶠ n : ℕ in atTop, dV (E : ℝ) - δ / 3 < (cnt V n : ℝ) / n :=
    hVd.eventually (lt_mem_nhds (by linarith))
  filter_upwards [ev1, densZero_iff_eventually_le.1 hGz (δ / 3) (by linarith),
    densZero_iff_eventually_le.1 hOz (δ / 3) (by linarith), eventually_ge_atTop 1]
    with n h1 h2 h3 hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  rw [lt_div_iff₀ hnpos] at h1
  have hL := hLC T n (E : ℝ) (by linarith) hn' (by linarith)
  have hL' : Ck * T ^ (j + 1) * (E : ℝ) ^ (1 - (j : ℝ)) * n ≤ Ck / Real.log T ^ 3 * n :=
    mul_le_mul_of_nonneg_right hA hnpos.le
  have hQn := hC (E : ℝ) hE2 n hn'
  have eQ : C * (n : ℝ) / (E : ℝ) = C / (E : ℝ) * n := by ring
  have hcn := hcnt n
  have eG : (dV (E : ℝ) - Ck / Real.log T ^ 3 - C / (E : ℝ) - δ) * n =
      (dV (E : ℝ) - δ / 3) * n - δ / 3 * n - Ck / Real.log T ^ 3 * n - C / (E : ℝ) * n -
        δ / 3 * n := by ring
  rw [eG]
  linarith

/-- EP1054.tex lines 2093–2104: the fixed-`j` form of `eq:almost-log-tail`. -/
theorem link_UpperTails_Claim_AlmostLogTail_fixedJ :
    Principia.Erdos1054.Spine.Link_UpperTails_Claim_AlmostLogTail_fixedJ := by
  intro hmain hcor hLR j hj ε hε
  obtain ⟨C, hC⟩ := hmain
  obtain ⟨Cj, T₁, hT₁⟩ := hC j hj
  have hg0 : 0 < Real.exp (-eulerGamma) := Real.exp_pos _
  have hg1 : Real.exp (-eulerGamma) ≤ 1 := expNegGamma_le_one
  set g := Real.exp (-eulerGamma) with hg
  set ε₁ := min (ε / 4) (g / 2) with hε₁
  have hε₁pos : 0 < ε₁ := lt_min (by linarith) (by linarith)
  have hε₁le : ε₁ ≤ ε / 4 := min_le_left _ _
  have hε₁g : ε₁ ≤ g / 2 := min_le_right _ _
  obtain ⟨A₀, hA₀⟩ := hcor.1 ε₁ hε₁pos
  obtain ⟨T₂, hT₂⟩ := hLR j hj (ε / 4) (by linarith)
  have hlogT := Real.tendsto_log_atTop
  have ev5 : ∀ᶠ T in atTop, Cj / Real.log T ^ 3 ≤ ε / 4 * (1 / Real.log T ^ 2) := by
    filter_upwards [hlogT.eventually_ge_atTop (max 1 (4 * Cj / ε))] with T hT
    have hl1 : 1 ≤ Real.log T := le_trans (le_max_left _ _) hT
    have hl2 : 4 * Cj / ε ≤ Real.log T := le_trans (le_max_right _ _) hT
    have hlpos : 0 < Real.log T := by linarith
    have hCj : Cj ≤ ε / 4 * Real.log T := by
      rw [div_le_iff₀ hε] at hl2
      linarith
    calc Cj / Real.log T ^ 3 ≤ (ε / 4 * Real.log T) / Real.log T ^ 3 :=
          div_le_div_of_nonneg_right hCj (by positivity)
      _ = ε / 4 * (1 / Real.log T ^ 2) := by
          field_simp
  have ev6 : ∀ᶠ T in atTop, |C| / T ≤ ε / 4 * (1 / Real.log T ^ 2) := by
    have ht : Tendsto (fun T : ℝ => |C| * (Real.log T ^ 2 / (1 * T + 0))) atTop
        (𝓝 (|C| * 0)) :=
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).const_mul |C|
    rw [mul_zero] at ht
    filter_upwards [ht.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 4)),
      eventually_gt_atTop 1] with T hT hT1
    have hTpos : 0 < T := by linarith
    have hlpos : 0 < Real.log T := Real.log_pos hT1
    simp only [one_mul, add_zero] at hT
    have e : |C| / T = |C| * (Real.log T ^ 2 / T) * (1 / Real.log T ^ 2) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right hT.le (by positivity)
  have ev4 : ∀ᶠ T in atTop, Real.exp (Real.exp (Real.exp 1)) ≤ T := eventually_ge_atTop _
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 (ev4.and (ev5.and ev6))
  refine ⟨max T₀ (max T₁ (max T₂ (max A₀ (Real.exp 1)))), fun T hT => ?_⟩
  have hTT₀ : T₀ ≤ T := le_trans (le_max_left _ _) hT
  have hTT₁ : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hTT₂ : T₂ ≤ T :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hT
  have hTA : A₀ ≤ T := le_trans (le_trans (le_trans (le_trans (le_max_left _ _)
    (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) hT
  have hTe : Real.exp 1 ≤ T := le_trans (le_trans (le_trans (le_trans (le_max_right _ _)
    (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) hT
  obtain ⟨hbig, h5, h6⟩ := hT₀ T hTT₀
  have hTpos : 0 < T := lt_of_lt_of_le (Real.exp_pos _) hTe
  have hET : T ≤ (Ej j T : ℝ) := le_Ej hj hTe
  have hEpos : 0 < (Ej j T : ℝ) := by linarith
  have hmainT := hT₁ T hTT₁
  have hcorE := hA₀ (Ej j T : ℝ) (le_trans hTA hET)
  have hLRT := hT₂ T hTT₂
  have hLT : 1 / Real.log T ^ 2 ≤ Lscale T := inv_sq_log_le_Lscale hbig
  have hL0 : 0 ≤ Lscale T := le_trans (by positivity) hLT
  have hCE : C / (Ej j T : ℝ) ≤ ε / 4 * Lscale T := by
    calc C / (Ej j T : ℝ) ≤ |C| / (Ej j T : ℝ) :=
          div_le_div_of_nonneg_right (le_abs_self C) hEpos.le
      _ ≤ |C| / T := div_le_div_of_nonneg_left (abs_nonneg C) hTpos hET
      _ ≤ ε / 4 * (1 / Real.log T ^ 2) := h6
      _ ≤ ε / 4 * Lscale T := mul_le_mul_of_nonneg_left hLT (by linarith)
  have hCj : Cj / Real.log T ^ 3 ≤ ε / 4 * Lscale T :=
    h5.trans (mul_le_mul_of_nonneg_left hLT (by linarith))
  have hb1 : 1 ≤ bj j := one_le_bj hj
  have hb0 : 0 < bj j := by linarith
  set ib := 1 / bj j with hib
  have hib0 : 0 < ib := by positivity
  have hib1 : ib ≤ 1 := by
    rw [hib, div_le_one hb0]
    exact hb1
  have hLE : ib * Lscale T - ε / 4 * Lscale T ≤ Lscale (Ej j T : ℝ) := by
    have := (abs_le.1 hLRT).1
    have e : Lscale T / bj j = ib * Lscale T := by
      rw [hib]
      ring
    linarith
  have hgb : g / (2 * bj j) = g / 2 * ib := by
    rw [hib]
    ring
  have key : g / 2 * ib - ε ≤ (g / 2 - ε₁) * (ib - ε / 4) - ε / 2 := by
    have e2 : g * ε ≤ ε := mul_le_of_le_one_left hε.le hg1
    have e3 : ε₁ * ib ≤ ε₁ := mul_le_of_le_one_right hε₁pos.le hib1
    have e4 : 0 ≤ ε₁ * ε := by positivity
    nlinarith
  have s1 : (g / 2 - ε₁) * (ib * Lscale T - ε / 4 * Lscale T) ≤
      (g / 2 - ε₁) * Lscale (Ej j T : ℝ) :=
    mul_le_mul_of_nonneg_left hLE (by linarith)
  calc (g / (2 * bj j) - ε) * Lscale T = (g / 2 * ib - ε) * Lscale T := by rw [hgb]
    _ ≤ ((g / 2 - ε₁) * (ib - ε / 4) - ε / 2) * Lscale T :=
        mul_le_mul_of_nonneg_right key hL0
    _ = (g / 2 - ε₁) * (ib * Lscale T - ε / 4 * Lscale T) - ε / 4 * Lscale T -
        ε / 4 * Lscale T := by ring
    _ ≤ dV (Ej j T : ℝ) - Cj / Real.log T ^ 3 - C / (Ej j T : ℝ) := by linarith
    _ ≤ _ := hmainT

/-- EP1054.tex lines 176–183 (proof 2103–2105): `j → ∞` in the fixed-`j` form. -/
theorem link_Eq_AlmostLogTail : Principia.Erdos1054.Spine.Link_Eq_AlmostLogTail := by
  intro h ε hε
  have hg0 : 0 < Real.exp (-eulerGamma) := Real.exp_pos _
  have hg1 : Real.exp (-eulerGamma) ≤ 1 := expNegGamma_le_one
  set g := Real.exp (-eulerGamma) with hg
  set j := max 3 ⌈2 / ε⌉₊ with hj
  have hj3 : 3 ≤ j := le_max_left _ _
  have hjε : 2 / ε ≤ (j : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 3 ⌈2 / ε⌉₊)
  obtain ⟨T₀, hT₀⟩ := h j hj3 (ε / 2) (by linarith)
  refine ⟨max T₀ (Real.exp (Real.exp 1)), fun T hT => ?_⟩
  have hL := Lscale_nonneg (le_trans (le_max_right _ _) hT)
  have h1 := hT₀ T (le_trans (le_max_left _ _) hT)
  have hjr : (3 : ℝ) ≤ j := by exact_mod_cast hj3
  have hjm : (j : ℝ) - 1 ≠ 0 := by linarith
  have hjp : (j : ℝ) + 1 ≠ 0 := by linarith
  have hkey : g / 2 - ε ≤ g / (2 * bj j) - ε / 2 := by
    have e1 : g / (2 * bj j) = g / 2 - g / ((j : ℝ) + 1) := by
      unfold bj
      field_simp
      ring
    have e2 : g / ((j : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) :=
      div_le_div_of_nonneg_right hg1 (by linarith)
    have e3 : 1 / ((j : ℝ) + 1) ≤ ε / 2 := by
      rw [div_le_iff₀ (by linarith)]
      have : 2 ≤ (j : ℝ) * ε := (div_le_iff₀ hε).1 hjε
      nlinarith
    linarith
  calc (g / 2 - ε) * Lscale T ≤ (g / (2 * bj j) - ε / 2) * Lscale T :=
        mul_le_mul_of_nonneg_right hkey hL
    _ ≤ _ := h1

/-- EP1054.tex lines 184–185: `{N ∈ 𝓡 : f(N) > TN}` has positive lower density. -/
theorem link_Thm_AlmostLogTail_posLowerDens :
    Principia.Erdos1054.Spine.Link_Thm_AlmostLogTail_posLowerDens := by
  intro h T _
  obtain ⟨T₀, hT₀⟩ := h (Real.exp (-eulerGamma) / 4) (by positivity)
  set T' := max (max T T₀) (Real.exp (Real.exp (Real.exp 1))) with hT'
  have hT'1 : T₀ ≤ T' := le_trans (le_max_right _ _) (le_max_left _ _)
  have hT'2 : T ≤ T' := le_trans (le_max_left _ _) (le_max_left _ _)
  have hT'3 : Real.exp (Real.exp (Real.exp 1)) ≤ T' := le_max_right _ _
  have hLpos : 0 < Lscale T' := Lscale_pos hT'3
  have h1 := hT₀ T' hT'1
  have hsub : {N : ℕ | N ∈ R ∧ Squarefree N ∧ T' * (N : ℝ) < (f N : ℝ)} ⊆
      largeRatioSet T := by
    rintro N ⟨hR, _, hlt⟩
    exact ⟨hR, lt_of_le_of_lt (mul_le_mul_of_nonneg_right hT'2 (Nat.cast_nonneg N)) hlt⟩
  have h2 : 0 < (Real.exp (-eulerGamma) / 2 - Real.exp (-eulerGamma) / 4) * Lscale T' := by
    apply mul_pos _ hLpos
    linarith [Real.exp_pos (-eulerGamma)]
  exact lt_of_lt_of_le h2 (h1.trans (lowerDens_mono hsub))

/-- EP1054.tex lines 185–188: `limsup_{N ∈ 𝓡} f(N)/N = ∞`. -/
theorem link_Thm_AlmostLogTail_limsup :
    Principia.Erdos1054.Spine.Link_Thm_AlmostLogTail_limsup := by
  intro h B N₀
  have hT : (0 : ℝ) < max B 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hpos := h (max B 1) hT
  by_contra hcon
  have hfin : (largeRatioSet (max B 1)).Finite := by
    refine (Set.finite_lt_nat (max N₀ 1)).subset ?_
    intro N hN
    obtain ⟨hR, hlt⟩ := hN
    show N < max N₀ 1
    by_contra hge
    have hge' : max N₀ 1 ≤ N := not_lt.1 hge
    apply hcon
    refine ⟨N, le_trans (le_max_left _ _) hge', hR, ?_⟩
    have hN1 : (0 : ℝ) < N := by
      have : 1 ≤ N := le_trans (le_max_right _ _) hge'
      exact_mod_cast this
    rw [lt_div_iff₀ hN1]
    calc B * N ≤ max B 1 * N := mul_le_mul_of_nonneg_right (le_max_left _ _) hN1.le
      _ < f N := hlt
  have h0 := HasDens.lowerDens_eq (densZero_of_finite hfin)
  rw [h0] at hpos
  exact lt_irrefl 0 hpos

end Principia.Erdos1054.Proofs
