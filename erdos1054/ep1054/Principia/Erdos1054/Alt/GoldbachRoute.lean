/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Proofs.OddRepr
import Principia.Erdos1054.Proofs.Thm13
import Principia.Erdos1054.Proofs.FmModulus
import Principia.Erdos1054.Proofs.Normality
import Principia.Erdos1054.Proofs.Moment
import Principia.Erdos1054.Proofs.KernelTails
import Principia.Erdos1054.Proofs.Envelope
import Principia.Erdos1054.Proofs.InputsStd
import Principia.Erdos1054.Proofs.Intro
import Principia.Erdos1054.Proofs.CoverageEta

set_option autoImplicit false

/-!
# EP1054 Theorem 1.3 from density zero of the binary Goldbach exceptional set

The spine (`Principia.Erdos1054.Spine.spine_Thm_AlmostLogTail`) routes Theorem 1.3
(`thm:almost-log-tail`) through `lem:analytic-odd-representability`, which is stated with the
Montgomery–Vaughan rate and so takes the trusted input `Cite_MV_exceptional`. The proof of
Theorem 1.3 (EP1054.tex lines 2066–2107) uses that lemma only to discard the unrepresented odd
targets of `V_E` ("discards only `o(X/log log log X)` unrepresented targets", line 2085), and all
it needs there is that they have **density zero**: the conclusion is a lower density at fixed
`j, T, E`. In Lean the same is true: `Proofs.link_UpperTails_Claim_AlmostLogTail_main` consumes
its `Lem_AnalyticOddRepresentability` hypothesis only through `Thm13.densZero_oddUnrep hOdd.2`.

This module replaces the MV rate by the qualitative Goldbach statement that the comparator-certified
master `GoldbachChainMaster.lean` proves, `almost_all_binary_goldbach_proven :
DensityZero notSumOfTwoPrimes` (namespace `GoldbachChain.GoldbachReduction`).

* `Std_GoldbachDensZero` — the even integers that are not a sum of two primes have density zero,
  stated with `Defs.DensZero` over the master's own predicate `notSumOfTwoPrimes` (copied
  verbatim below, together with the master's `countUpTo` and `DensityZero`).
* `std_GoldbachDensZero_of_densityZero` — the master's `DensityZero notSumOfTwoPrimes` (rational
  `ε`, count over `0 ≤ n ≤ X`) implies `Std_GoldbachDensZero`. With the verbatim copies, a bridge in
  the PNT workspace is `std_GoldbachDensZero_of_densityZero almost_all_binary_goldbach_proven`.
* `oddRepr_densZero_of_goldbach` — `Std_GoldbachDensZero → DensZero {n | Odd n ∧ n ∉ R}`: for odd
  `n ∉ 𝓡`, `n - 1` is a Goldbach exception or `2p` (`OddRepr.cnt_oddUnrep_le`, since
  `1 + p + q = F p q ∈ 𝓡` for distinct primes), and `π(X) ≤ 8X / log X`
  (`OddRepr.primeCounting_le`).
* `claim_AlmostLogTail_main_of_densZero` — `link_UpperTails_Claim_AlmostLogTail_main` re-run with
  `DensZero oddUnrep` in place of `Lem_AnalyticOddRepresentability` (the proof is the same, line for
  line; only the source of `hOz` changes).
* `thm_AlmostLogTail_of_goldbachDensZero` — **Theorem 1.3 from `Std_GoldbachDensZero` alone**,
  composing the proved links and leaves of the `Thm13` package and its prerequisites exactly as
  `spine_Thm_AlmostLogTail` does (with `Std_recipPrimesAP_diverges` supplied by the hypothesis-free
  `InputsStd.recipPrimesAP_diverges`, LEAN-PROGRESS F7, and `Std_Mertens2`/`Std_Mertens3` by the
  discharged `input_Std_Mertens2`/`input_Std_Mertens3`).
* `cor_FixedCofactorDefect_of_goldbachDensZero` — the fixed-cofactor corollary, which the spine
  derives from `Eq_AlmostLogTail` alone, from the same single hypothesis.

What this does **not** give: Theorem 1.4 (`thm:subexp-growth`) uses the odd-representability
bound with its rate, `cnt oddUnrep X ≤ η (X / log₃ X)` at `X`-dependent scales (`Proofs.Thm14`),
which density zero does not supply.
-/

namespace Principia.Erdos1054.Alt

open Finset Filter Principia.Erdos1054 Principia.Erdos1054.UpperTails
  Principia.Erdos1054.Proofs.Thm13
open scoped Topology

/-! ## 1. The Goldbach exceptional set, in the master's own words -/

/-- Verbatim copy of `GoldbachChain.GoldbachReduction.countUpTo` (`GoldbachChainMaster.lean`):
the number of `0 ≤ n ≤ X` satisfying `P`. -/
noncomputable def countUpTo (P : ℕ → Prop) (X : ℕ) : ℕ := by
  classical
  exact ((Finset.range (X + 1)).filter P).card

/-- Verbatim copy of `GoldbachChain.GoldbachReduction.DensityZero` (`GoldbachChainMaster.lean`):
density zero with rational `ε` and an integer threshold. -/
def DensityZero (P : ℕ → Prop) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X ≥ X₀ → (countUpTo P X : ℚ) ≤ ε * X

/-- Verbatim copy of `GoldbachChain.GoldbachReduction.notSumOfTwoPrimes`
(`GoldbachChainMaster.lean`): `n` is even and not a sum of two (not necessarily distinct) primes.
The set `{n | notSumOfTwoPrimes n}` is, by definition, `Proofs.OddRepr.mvSet` and the set counted
by `Cite_MV_exceptional`. -/
def notSumOfTwoPrimes (n : ℕ) : Prop :=
  Even n ∧ ¬ ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

/-- **Almost all even integers are sums of two primes** (the exceptional set has density zero),
transcribed into this library's density notion `Defs.DensZero`.

Proved, with no hypotheses, by the comparator-certified master
`GoldbachChain.GoldbachReduction.almost_all_binary_goldbach_proven : DensityZero notSumOfTwoPrimes`
in `C:/Users/Christian/pnt/GoldbachChainMaster.lean`. That master sits in the PNT+ workspace and
pins another Mathlib commit. Since 2026-09-26 its circle method is ported into this library
(`Principia.Common.Goldbach`), and `Alt.std_GoldbachDensZero_unconditional` proves this Prop inside
one kernel environment; `CircleMethod.densityZero_notSumOfTwoPrimes_eq` bridges the definitions by
`rfl`. `std_GoldbachDensZero_of_densityZero` converts the master's form into this one. It is the qualitative (Chudakov–Estermann–van der Corput) statement, strictly weaker than
`Cite_MV_exceptional`, which gives the count `O(X^{1-c})`. -/
def Std_GoldbachDensZero : Prop := DensZero {n : ℕ | notSumOfTwoPrimes n}

/-- The Goldbach exceptional set of this module is `OddRepr.mvSet`, definitionally. -/
theorem setOf_notSumOfTwoPrimes_eq_mvSet :
    {n : ℕ | notSumOfTwoPrimes n} = Proofs.OddRepr.mvSet := rfl

/-- `cnt` over `[1, n]` is at most the master's `countUpTo` over `[0, n]`. -/
theorem cnt_le_countUpTo (P : ℕ → Prop) (n : ℕ) :
    cnt {m : ℕ | P m} (n : ℝ) ≤ countUpTo P n := by
  classical
  rw [cnt_natCast]
  unfold countUpTo
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter, Finset.mem_Icc] at hx
  obtain ⟨⟨_, hxn⟩, hxP⟩ := hx
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hxP⟩

/-- **The bridge from the master's statement.** `DensityZero P` (rational `ε`, count over
`0 ≤ n ≤ X`) implies `DensZero {n | P n}`. -/
theorem densZero_of_densityZero (P : ℕ → Prop) (h : DensityZero P) : DensZero {n : ℕ | P n} := by
  rw [densZero_iff_eventually_le]
  intro ε hε
  obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn hε
  have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
  obtain ⟨X₀, hX₀⟩ := h q hq0'
  filter_upwards [eventually_ge_atTop X₀] with n hn
  have h1 : (countUpTo P n : ℚ) ≤ q * n := hX₀ n hn
  have h2 : (countUpTo P n : ℝ) ≤ (q : ℝ) * n := by exact_mod_cast h1
  have h3 : (cnt {m : ℕ | P m} (n : ℝ) : ℝ) ≤ countUpTo P n := by
    exact_mod_cast cnt_le_countUpTo P n
  have h4 : (q : ℝ) * n ≤ ε * n := mul_le_mul_of_nonneg_right hqε.le (Nat.cast_nonneg n)
  linarith

/-- The master's conclusion gives `Std_GoldbachDensZero`. -/
theorem std_GoldbachDensZero_of_densityZero (h : DensityZero notSumOfTwoPrimes) :
    Std_GoldbachDensZero :=
  densZero_of_densityZero notSumOfTwoPrimes h

/-! ## 2. Odd unrepresented integers have density zero -/

/-- **The odd integers outside `𝓡` have density zero**, from Goldbach density zero alone. For odd
`n ∉ 𝓡`, `n - 1` is either a Goldbach exception or `2p` (a representation `n - 1 = p + q` with
`p ≠ q` gives `n = F p q ∈ 𝓡`), so `cnt oddUnrep X ≤ cnt mvSet X + π(X)`
(`OddRepr.cnt_oddUnrep_le`); both terms are `o(X)`, the second by `π(X) ≤ 8X / log X`
(`OddRepr.primeCounting_le`, Mathlib's Chebyshev bound). -/
theorem oddRepr_densZero_of_goldbach (hG : Std_GoldbachDensZero) :
    DensZero {n : ℕ | Odd n ∧ n ∉ R} := by
  have hMV : DensZero Proofs.OddRepr.mvSet := hG
  rw [densZero_iff_exists_real]
  intro ε hε
  obtain ⟨X₁, hX₁⟩ := hMV.exists_le_mul (half_pos hε)
  refine ⟨max X₁ (max 3 (Real.exp (16 / ε))), fun X hX => ?_⟩
  have hX1 : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have hX3 : (3 : ℝ) ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXe : Real.exp (16 / ε) ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hXpos : 0 < X := by linarith
  have h16 : 0 < 16 / ε := div_pos (by norm_num) hε
  have hlog : 16 / ε ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).2 hXe
  have hpi : (Nat.primeCounting ⌊X⌋₊ : ℝ) ≤ 8 * (X / Real.log X) :=
    Proofs.OddRepr.primeCounting_le X hX3
  have hdiv : X / Real.log X ≤ X / (16 / ε) := div_le_div_of_nonneg_left hXpos.le h16 hlog
  have heq : X / (16 / ε) = ε / 16 * X := by
    rw [div_div_eq_mul_div]
    ring
  have hmv : (cnt Proofs.OddRepr.mvSet X : ℝ) ≤ ε / 2 * X := hX₁ X hX1
  have hcnt : (cnt oddUnrep X : ℝ) ≤
      cnt Proofs.OddRepr.mvSet X + Nat.primeCounting ⌊X⌋₊ := by
    exact_mod_cast Proofs.OddRepr.cnt_oddUnrep_le X
  change (cnt oddUnrep X : ℝ) ≤ ε * X
  linarith

/-! ## 3. The main counting claim of Theorem 1.3, from density zero -/

/-- EP1054.tex lines 2073–2092 with the odd-representability input weakened to density zero:
`d(V_E) − C_j/(log T)³ − O(1/E) ≤ lowerdens{N ∈ 𝓡 : N squarefree, f(N) > TN}`.

Identical to `Proofs.link_UpperTails_Claim_AlmostLogTail_main` except that the hypothesis
`Lem_AnalyticOddRepresentability` (used there only through `Thm13.densZero_oddUnrep`) is replaced by
`DensZero oddUnrep` itself. -/
theorem claim_AlmostLogTail_main_of_densZero
    (hFE : Prop_FmEnvelope) (hMom : Lem_Moment)
    (hArith : UpperTails.Claim_AlmostLogTail_momentArith) (hVAr : UpperTails.Claim_VA_rough)
    (hNSQ : UpperTails.Claim_RoughNonsquarefree) (hOz : DensZero oddUnrep)
    (hVAd : UpperTails.Claim_VA_density) : UpperTails.Claim_AlmostLogTail_main := by
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

/-! ## 4. Theorem 1.3 and the fixed-cofactor corollary from `Std_GoldbachDensZero` -/

/-- `eq:almost-log-tail` (Theorem 1.3, main display) from Goldbach density zero alone. The
composition is `spine_Thm_AlmostLogTail`'s, with every link, leaf and discharged input supplied by
its proof, `InputsStd.recipPrimesAP_diverges` for `Std_recipPrimesAP_diverges` (F7), and
`claim_AlmostLogTail_main_of_densZero` in place of the MV-rate link. -/
theorem eq_AlmostLogTail_of_goldbachDensZero (hG : Std_GoldbachDensZero) : Eq_AlmostLogTail :=
  have v_Lem_FmModulus : Lem_FmModulus :=
    Proofs.link_Lem_FmModulus Proofs.leaf_Fact_KmodGeTwo
  have v_Lem_FixedModulusNormality : Lem_FixedModulusNormality :=
    Proofs.link_Lem_FixedModulusNormality Proofs.InputsStd.recipPrimesAP_diverges
  have v_Lem_SigmaRangeZero : Lem_SigmaRangeZero :=
    Proofs.link_Lem_SigmaRangeZero v_Lem_FixedModulusNormality
  have v_Lem_Moment : Lem_Moment := Proofs.link_Lem_Moment Proofs.leaf_Eq_Reflection
  have v_Eq_SharpPrimeSum : Eq_SharpPrimeSum :=
    Proofs.link_Eq_SharpPrimeSum Proofs.input_Std_Mertens2
  have v_Eq_FixedKernelTail : Eq_FixedKernelTail :=
    Proofs.link_Eq_FixedKernelTail Proofs.leaf_Eq_RankinKernel v_Eq_SharpPrimeSum
      Proofs.leaf_UpperTails_Claim_EulerHigherTerms
  have v_KA_finite : UpperTails.Claim_KA_finite :=
    Proofs.link_UpperTails_Claim_KA_finite v_Lem_FmModulus Proofs.leaf_Fact_KmodGeTwo
  have v_VA_periodic : UpperTails.Claim_VA_periodic :=
    Proofs.link_UpperTails_Claim_VA_periodic v_KA_finite
  have v_VA_density : UpperTails.Claim_VA_density :=
    Proofs.link_UpperTails_Claim_VA_density v_KA_finite v_VA_periodic Proofs.leaf_Fact_KmodGeTwo
  have v_Prop_FmEnvelope : Prop_FmEnvelope :=
    Proofs.link_Prop_FmEnvelope v_Lem_SigmaRangeZero v_Lem_FmModulus
      v_Lem_FixedModulusNormality v_KA_finite v_VA_density
  have v_DeltaPfix : UpperTails.Claim_DeltaPfix :=
    Proofs.link_UpperTails_Claim_DeltaPfix Proofs.input_Std_Mertens3
  have v_RoughNotVA : UpperTails.Claim_RoughNotVA :=
    Proofs.link_UpperTails_Claim_RoughNotVA v_Lem_FmModulus Proofs.leaf_Fact_KmodGeTwo
      v_KA_finite Proofs.leaf_Notation_Delta_density
  have v_Cor_FmEnvelopeTail : Cor_FmEnvelopeTail :=
    Proofs.link_Cor_FmEnvelopeTail Proofs.leaf_UpperTails_Claim_VA_rough v_VA_density
      Proofs.leaf_Notation_Delta_density v_DeltaPfix v_RoughNotVA v_Eq_FixedKernelTail
  have v_main : UpperTails.Claim_AlmostLogTail_main :=
    claim_AlmostLogTail_main_of_densZero v_Prop_FmEnvelope v_Lem_Moment
      Proofs.leaf_UpperTails_Claim_AlmostLogTail_momentArith Proofs.leaf_UpperTails_Claim_VA_rough
      Proofs.leaf_UpperTails_Claim_RoughNonsquarefree (oddRepr_densZero_of_goldbach hG)
      v_VA_density
  have v_fixedJ : UpperTails.Claim_AlmostLogTail_fixedJ :=
    Proofs.link_UpperTails_Claim_AlmostLogTail_fixedJ v_main v_Cor_FmEnvelopeTail
      Proofs.leaf_UpperTails_Claim_LscaleRatio
  Proofs.link_Eq_AlmostLogTail v_fixedJ

/-- **Theorem 1.3 (`thm:almost-log-tail`) from Goldbach density zero alone** — the main display
and both consequences (`{N ∈ 𝓡 : f(N) > TN}` has positive lower density for every `T > 0`;
`limsup_{N ∈ 𝓡} f(N)/N = ∞`). No other hypothesis: `Cite_MV_exceptional` and `Std_PNT_AP` are not
used. -/
theorem thm_AlmostLogTail_of_goldbachDensZero (hG : Std_GoldbachDensZero) : Thm_AlmostLogTail :=
  have v_Eq : Eq_AlmostLogTail := eq_AlmostLogTail_of_goldbachDensZero hG
  have v_pos : Thm_AlmostLogTail_posLowerDens := Proofs.link_Thm_AlmostLogTail_posLowerDens v_Eq
  ⟨v_Eq, v_pos, Proofs.link_Thm_AlmostLogTail_limsup v_pos⟩

/-- The fixed-cofactor corollary (EP1054.tex lines 2488–2499: `lowerdens(ℕ ∖ G_A) > 0` for every
`A ≥ 1`, and `eq:fixed-cofactor-defect`) from Goldbach density zero alone; the spine derives both
parts from `Eq_AlmostLogTail`. -/
theorem cor_FixedCofactorDefect_of_goldbachDensZero (hG : Std_GoldbachDensZero) :
    Cor_FixedCofactorDefect :=
  have v_Eq : Eq_AlmostLogTail := eq_AlmostLogTail_of_goldbachDensZero hG
  ⟨Proofs.link_Cor_FixedCofactorDefect_pos v_Eq, Proofs.link_Eq_FixedCofactorDefect v_Eq⟩

/-- Theorem 1.3 from the master's own statement, `DensityZero notSumOfTwoPrimes` (the conclusion of
`GoldbachChain.GoldbachReduction.almost_all_binary_goldbach_proven`). -/
theorem thm_AlmostLogTail_of_densityZero (h : DensityZero notSumOfTwoPrimes) : Thm_AlmostLogTail :=
  thm_AlmostLogTail_of_goldbachDensZero (std_GoldbachDensZero_of_densityZero h)

/-- The fixed-cofactor corollary from the master's own statement. -/
theorem cor_FixedCofactorDefect_of_densityZero (h : DensityZero notSumOfTwoPrimes) :
    Cor_FixedCofactorDefect :=
  cor_FixedCofactorDefect_of_goldbachDensZero (std_GoldbachDensZero_of_densityZero h)

end Principia.Erdos1054.Alt
