import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr

set_option autoImplicit false

/-!
# An explicit Halberstam--Richert mean-value bound

## Provenance and licence

Ported (backported from Lean v4.33.0 to our v4.31.0 / Mathlib v4.31.0) from the GitHub
repository `plby/lean-proofs`, commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`
(2026-09-15), project `src/latest/`, files

* `ErdosProblems/Erdos448/HalberstamLean.lean`          (namespace `HalberstamScratch`)
* `ErdosProblems/Erdos448/PrimePowerConvolution448.lean` (namespace `PrimePowerConvolution448`)
* `ErdosProblems/Erdos448/PrimePowerMassLinear448.lean`  (namespace `PrimePowerMassLinear448`)
* `ErdosProblems/Erdos448/HalberstamComplete448.lean`    (namespace `HalberstamComplete448`)
* `ErdosProblems/Erdos67/MRShiuGlobalMean.lean`          (namespace `Erdos67.MRShiu`)

That is the full dependency closure of `HalberstamComplete448.halberstam_richert_explicit`
and `Erdos67.MRShiu.partialSum_le_exp` (every file in it imports only `Mathlib`).

**Licence (recorded verbatim, 2026-09-25).** The repository has no top-level `LICENSE`;
`gh api repos/plby/lean-proofs` reports `license: null`. The file `src/latest/LICENSE` reads, in
full: *"Some files in this repository are from external sources and are licensed under the Apache
License, Version 2.0. You may obtain a copy of the License at
https://www.apache.org/licenses/LICENSE-2.0"*. It does not say which files, so the licence of
these particular files is **not stated explicitly** by the upstream repository; the only licence
named anywhere in it is Apache 2.0. Anyone redistributing this module outside PrincipiaAI should
confirm the terms with the upstream author first.

## Port changes

* All five upstream namespaces are merged into `Principia.Common.HalberstamRichert`.
  Declaration names are otherwise unchanged, except that exact duplicates are merged:
  `PrimePowerConvolution448.logPartialSum` = `HalberstamScratch.logPartialSum` (`logPartialSum`),
  `PrimePowerConvolution448.primePowerMass` = `PrimePowerMassLinear448.primePowerMass`
  (`primePowerMass`), and `PrimePowerMassLinear448.massConstant` =
  `HalberstamScratch.explicitMassConstant` (`explicitMassConstant`) -- all three pairs had
  identical bodies upstream.
* `private` declarations are made public, so that the acceptance gate can name them.
* `PrimePowerMassLinear448.primePowerPairs` / `pairPrimePowerMass` and their two `_zero`
  lemmas are not ported: nothing in the closure uses them.
* Proofs are the upstream proofs, adjusted only where v4.31 needs it.

## Principia additions (not upstream)

The final section derives the form used by the Erdős-1054 paper (Pollack 2014, Lemma 2.4):
for multiplicative `f` with `0 ≤ f (p^k) ≤ 1`,
`∑_{n ≤ x} f n ≤ C x exp (∑_{p ≤ x} (f p - 1)/p)`,
here **conditional** on the upper half of Mertens' second theorem, carried as the named
hypothesis `MertensUpper B` (`∑_{p ≤ N} 1/p ≤ log log N + B` for `N ≥ 2`). It is discharged
unconditionally in `Principia.Common.HalberstamRichertPollack` from the Mertens port.

## Headline results

* `halberstam_richert_explicit`: for multiplicative `h ≥ 0` with
  `h (p^(j+1)) ≤ λ₁ λ₂^j`, `0 ≤ λ₂ < 2`, and `N ≥ 2`,
  `∑_{n ≤ N} h n ≤ (K(λ₁,λ₂) + 1) · N / log N · ∏_{p ≤ N} ∑_j h(p^j)/p^j`,
  `K(λ₁,λ₂) = λ₁ (log 4 + 8 λ₂ log 2 / (1 - λ₂/2)²)`.
* `partialSum_le_exp` (λ₁ = λ₂ = 1):
  `∑_{n ≤ N} h n ≤ (K(1,1) + 1) · N / log N · exp (∑_{p ≤ N} (h p / p + 1/(p(p-1))))`.
* `sum_le_mul_exp_of_mertensUpper` / `_real`: the Pollack form, conditional on `MertensUpper`.
-/

open Finset

namespace Principia.Common.HalberstamRichert

/-! ## Local Euler factors (upstream `HalberstamLean.lean`) -/

/-- Divide an arithmetic weight by its argument.  The value at zero is `0`. -/
noncomputable def recipWeight (h : ℕ → ℝ) (n : ℕ) : ℝ :=
  h n / (n : ℝ)

/-- Exact local Euler-factor estimate implied by the prime-power hypothesis. -/
theorem prime_power_local_mass
    (h : ℕ → ℝ) (p : ℕ) (lambda1 lambda2 : ℝ)
    (hp : Nat.Prime p)
    (hh_nonneg : ∀ n, 0 ≤ h n)
    (hh_one : h 1 = 1)
    (hlambda1 : 0 ≤ lambda1)
    (hlambda2 : 0 ≤ lambda2)
    (hlambda2_lt : lambda2 < 2)
    (hpow : ∀ j : ℕ,
      h (p ^ (j + 1)) ≤ lambda1 * lambda2 ^ j) :
    Summable (fun j : ℕ => ‖recipWeight h (p ^ j)‖) ∧
      (∑' j : ℕ, ‖recipWeight h (p ^ j)‖) ≤
        1 + lambda1 / ((p : ℝ) - lambda2) := by
  let r : ℝ := lambda2 / (p : ℝ)
  let c : ℝ := lambda1 / (p : ℝ)
  have hpReal : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpTwo : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hr_nonneg : 0 ≤ r := div_nonneg hlambda2 hpReal.le
  have hr_lt : r < 1 := by
    dsimp [r]
    exact (div_lt_one hpReal).2 (hlambda2_lt.trans_le hpTwo)
  have hc_nonneg : 0 ≤ c := div_nonneg hlambda1 hpReal.le
  have hbound : ∀ j : ℕ,
      ‖recipWeight h (p ^ (j + 1))‖ ≤ c * r ^ j := by
    intro j
    have hdenom_nonneg : 0 ≤ (((p ^ (j + 1) : ℕ) : ℝ)) := by positivity
    calc
      ‖recipWeight h (p ^ (j + 1))‖
          = h (p ^ (j + 1)) / ((p ^ (j + 1) : ℕ) : ℝ) := by
              rw [recipWeight, Real.norm_eq_abs, abs_of_nonneg]
              exact div_nonneg (hh_nonneg _) hdenom_nonneg
      _ ≤ (lambda1 * lambda2 ^ j) /
            ((p ^ (j + 1) : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right (hpow j) hdenom_nonneg
      _ = c * r ^ j := by
          rw [Nat.cast_pow, pow_succ]
          dsimp [c, r]
          have hpNe : (p : ℝ) ≠ 0 := ne_of_gt hpReal
          rw [div_pow]
          field_simp [hpNe]
  have hgeom : Summable (fun j : ℕ => r ^ j) :=
    summable_geometric_of_lt_one hr_nonneg hr_lt
  have hmajor : Summable (fun j : ℕ => c * r ^ j) := hgeom.mul_left c
  have htail : Summable (fun j : ℕ => ‖recipWeight h (p ^ (j + 1))‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hbound hmajor
  have hseries : Summable (fun j : ℕ => ‖recipWeight h (p ^ j)‖) := by
    apply (summable_nat_add_iff 1).mp
    simpa [Nat.add_comm] using htail
  refine ⟨hseries, ?_⟩
  rw [hseries.tsum_eq_zero_add]
  have hzero : ‖recipWeight h (p ^ 0)‖ = 1 := by
    simp [recipWeight, hh_one]
  rw [hzero]
  have htail_le :
      (∑' j : ℕ, ‖recipWeight h (p ^ (j + 1))‖) ≤
        ∑' j : ℕ, c * r ^ j :=
    htail.tsum_le_tsum hbound hmajor
  have hmajor_sum : (∑' j : ℕ, c * r ^ j) = c * (1 - r)⁻¹ :=
    ((hasSum_geometric_of_lt_one hr_nonneg hr_lt).mul_left c).tsum_eq
  calc
    1 + ∑' j : ℕ, ‖recipWeight h (p ^ (j + 1))‖
        ≤ 1 + ∑' j : ℕ, c * r ^ j := by linarith
    _ = 1 + c * (1 - r)⁻¹ := by rw [hmajor_sum]
    _ = 1 + lambda1 / ((p : ℝ) - lambda2) := by
      dsimp [c, r]
      have hpNe : (p : ℝ) ≠ 0 := ne_of_gt hpReal
      have hdiffPos : 0 < (p : ℝ) - lambda2 :=
        sub_pos.mpr (hlambda2_lt.trans_le hpTwo)
      field_simp [hpNe, ne_of_gt hdiffPos]

/-- Explicit constant in the linear prime-power mass estimate, using the
indexing `h(p^(j+1)) ≤ lambda1 * lambda2^j`. -/
noncomputable def explicitMassConstant (lambda1 lambda2 : ℝ) : ℝ :=
  lambda1 *
    (Real.log 4 +
      8 * lambda2 * Real.log 2 / (1 - lambda2 / 2) ^ 2)

lemma explicitMassConstant_nonneg {lambda1 lambda2 : ℝ}
    (h1 : 0 ≤ lambda1) (h2 : 0 ≤ lambda2) :
    0 ≤ explicitMassConstant lambda1 lambda2 := by
  unfold explicitMassConstant
  positivity

lemma recipWeight_one {h : ℕ → ℝ} (h1 : h 1 = 1) :
    recipWeight h 1 = 1 := by
  simp [recipWeight, h1]

lemma recipWeight_mul {h : ℕ → ℝ} (h0 : h 0 = 0)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → h (m * n) = h m * h n)
    {m n : ℕ} (hmn : m.Coprime n) :
    recipWeight h (m * n) = recipWeight h m * recipWeight h n := by
  by_cases hm : m = 0
  · subst m
    have hn : n = 1 := by simpa using hmn
    subst n
    simp [recipWeight, h0]
  by_cases hn : n = 0
  · subst n
    have hm1 : m = 1 := by simpa [Nat.coprime_comm] using hmn
    subst m
    simp [recipWeight, h0]
  simp only [recipWeight, hmul hmn, Nat.cast_mul]
  field_simp [hm, hn]

lemma nat_Icc_mem_smoothNumbers {x n : ℕ}
    (hn : n ∈ Finset.Icc 1 x) : n ∈ (x + 1).smoothNumbers := by
  rcases Finset.mem_Icc.mp hn with ⟨hn1, hnx⟩
  rw [Nat.mem_smoothNumbers]
  refine ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn1), ?_⟩
  intro p hp
  exact (Nat.le_of_mem_primeFactorsList hp).trans_lt (Nat.lt_succ_of_le hnx)

/--
Exact finite Euler-product majorant.  This is the part of the classical
Halberstam--Richert lemma obtained from positivity, multiplicativity, and
unique factorization alone:

`sum_{n ≤ x} h(n) ≤ x * product_{p ≤ x} sum_j h(p^j)/p^j`.

The classical lemma strengthens `x` to `C * x / log x`; that strengthening
does not follow from the Euler-product expansion and requires an upper-bound
sieve/mean-value argument.
-/
theorem euler_rankin_mean_bound
    (h : ℕ → ℝ)
    (h0 : h 0 = 0)
    (h1 : h 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → h (m * n) = h m * h n)
    (hnonneg : ∀ n, 0 ≤ h n)
    (hloc : ∀ {p : ℕ}, p.Prime →
      Summable (fun j : ℕ => ‖recipWeight h (p ^ j)‖))
    (x : ℕ) :
    (∑ n ∈ Finset.Icc 1 x, h n) ≤
      (x : ℝ) *
        ∏ p ∈ (x + 1).primesBelow,
          ∑' j : ℕ, h (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
  let f : ℕ → ℝ := recipWeight h
  have hf1 : f 1 = 1 := recipWeight_one h1
  have hfmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n := by
    intro m n hmn
    exact recipWeight_mul h0 hmul hmn
  have hEuler :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      hf1 hfmul hloc (x + 1)
  let e : {n // n ∈ Finset.Icc 1 x} ↪ (x + 1).smoothNumbers :=
    { toFun := fun n => ⟨n, nat_Icc_mem_smoothNumbers n.property⟩
      inj' := by
        intro a b hab
        apply Subtype.ext
        exact congrArg (fun z : (x + 1).smoothNumbers => (z : ℕ)) hab }
  let s : Finset ((x + 1).smoothNumbers) := (Finset.Icc 1 x).attach.map e
  have hs_sum :
      (∑ n ∈ Finset.Icc 1 x, f n) = ∑ n ∈ s, f n := by
    calc
      (∑ n ∈ Finset.Icc 1 x, f n) =
          ∑ n ∈ (Finset.Icc 1 x).attach, f n :=
        (Finset.sum_attach (Finset.Icc 1 x) f).symm
      _ = ∑ n ∈ s, f n := by
        change (∑ n ∈ (Finset.Icc 1 x).attach, f n) =
          ∑ n ∈ (Finset.Icc 1 x).attach.map e, f n
        rw [Finset.sum_map]
        rfl
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    exact div_nonneg (hnonneg n) (Nat.cast_nonneg n)
  have hs_le :
      (∑ n ∈ Finset.Icc 1 x, f n) ≤
        ∑' n : (x + 1).smoothNumbers, f n := by
    rw [hs_sum]
    exact hEuler.1.of_norm.sum_le_tsum s
      (fun n _ => hf_nonneg n)
  calc
    (∑ n ∈ Finset.Icc 1 x, h n)
        ≤ ∑ n ∈ Finset.Icc 1 x, (x : ℝ) * f n := by
          refine Finset.sum_le_sum ?_
          intro n hn
          have hnpos : 0 < (n : ℝ) := by
            exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1)
          have hnx : (n : ℝ) ≤ (x : ℝ) := by
            exact_mod_cast (Finset.mem_Icc.mp hn).2
          change h n ≤ (x : ℝ) * (h n / (n : ℝ))
          rw [← mul_div_assoc, le_div_iff₀ hnpos]
          nlinarith [hnonneg n]
    _ = (x : ℝ) * ∑ n ∈ Finset.Icc 1 x, f n := by
          rw [Finset.mul_sum]
    _ ≤ (x : ℝ) * ∑' n : (x + 1).smoothNumbers, f n := by
          exact mul_le_mul_of_nonneg_left hs_le (Nat.cast_nonneg x)
    _ = (x : ℝ) *
        ∏ p ∈ (x + 1).primesBelow,
          ∑' j : ℕ, h (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
          rw [hEuler.2.tsum_eq]
          rfl

/-- The reciprocal partial sum is bounded by its finite Euler product. -/
theorem reciprocal_sum_le_euler_product
    (h : ℕ → ℝ)
    (h0 : h 0 = 0)
    (h1 : h 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → h (m * n) = h m * h n)
    (hnonneg : ∀ n, 0 ≤ h n)
    (hloc : ∀ {p : ℕ}, p.Prime →
      Summable (fun j : ℕ => ‖recipWeight h (p ^ j)‖))
    (x : ℕ) :
    (∑ n ∈ Finset.Icc 1 x, h n / (n : ℝ)) ≤
      ∏ p ∈ (x + 1).primesBelow,
        ∑' j : ℕ, h (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
  let f : ℕ → ℝ := recipWeight h
  have hf1 : f 1 = 1 := recipWeight_one h1
  have hfmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n := by
    intro m n hmn
    exact recipWeight_mul h0 hmul hmn
  have hEuler :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      hf1 hfmul hloc (x + 1)
  let e : {n // n ∈ Finset.Icc 1 x} ↪ (x + 1).smoothNumbers :=
    { toFun := fun n => ⟨n, nat_Icc_mem_smoothNumbers n.property⟩
      inj' := by
        intro a b hab
        apply Subtype.ext
        exact congrArg (fun z : (x + 1).smoothNumbers => (z : ℕ)) hab }
  let s : Finset ((x + 1).smoothNumbers) := (Finset.Icc 1 x).attach.map e
  have hs_sum :
      (∑ n ∈ Finset.Icc 1 x, f n) = ∑ n ∈ s, f n := by
    calc
      (∑ n ∈ Finset.Icc 1 x, f n) =
          ∑ n ∈ (Finset.Icc 1 x).attach, f n :=
        (Finset.sum_attach (Finset.Icc 1 x) f).symm
      _ = ∑ n ∈ s, f n := by
        change (∑ n ∈ (Finset.Icc 1 x).attach, f n) =
          ∑ n ∈ (Finset.Icc 1 x).attach.map e, f n
        rw [Finset.sum_map]
        rfl
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    exact div_nonneg (hnonneg n) (Nat.cast_nonneg n)
  calc
    (∑ n ∈ Finset.Icc 1 x, h n / (n : ℝ))
        = ∑ n ∈ Finset.Icc 1 x, f n := by rfl
    _ = ∑ n ∈ s, f n := hs_sum
    _ ≤ ∑' n : (x + 1).smoothNumbers, f n :=
      hEuler.1.of_norm.sum_le_tsum s (fun n _ => hf_nonneg n)
    _ = ∏ p ∈ (x + 1).primesBelow,
        ∑' j : ℕ, h (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
      rw [hEuler.2.tsum_eq]
      rfl

/-! ## Partial sums and the `N / log N` saving (upstream `HalberstamLean.lean`) -/

/-- The ordinary partial sum of a nonnegative arithmetic weight. -/
def partialSum (h : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, h n

/-- The reciprocal-weighted partial sum. -/
noncomputable def reciprocalPartialSum (h : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, h n / (n : ℝ)

/-- The logarithmically weighted partial sum. -/
noncomputable def logPartialSum (h : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, h n * Real.log (n : ℝ)

/--
The exact final summation step in the Halberstam--Richert proof.  A uniform
bound

`sum h(n) log n ≤ K N sum h(n)/n`

implies the crucial `N / log N` saving, with completely explicit constant
`K + 1`.  The extra `1` comes from bounding `log (N/n)` by `N/n`.
-/
theorem mean_le_of_log_moment
    (h : ℕ → ℝ) (hnonneg : ∀ n, 0 ≤ h n) (K : ℝ) (N : ℕ)
    (hN : 2 ≤ N)
    (hlog : logPartialSum h N ≤
      K * (N : ℝ) * reciprocalPartialSum h N) :
    partialSum h N ≤
      (K + 1) * (N : ℝ) / Real.log (N : ℝ) *
        reciprocalPartialSum h N := by
  have hNpos : 0 < (N : ℝ) := by positivity
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hcomplement :
      (∑ n ∈ Finset.Icc 1 N,
          h n * (Real.log (N : ℝ) - Real.log (n : ℝ))) ≤
        (N : ℝ) * reciprocalPartialSum h N := by
    unfold reciprocalPartialSum
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro n hn
    have hnpos_nat : 0 < n :=
      lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
    have hratio_nonneg : 0 ≤ (N : ℝ) / (n : ℝ) :=
      div_nonneg hNpos.le hnpos.le
    have hlog_div :
        Real.log (N : ℝ) - Real.log (n : ℝ) =
          Real.log ((N : ℝ) / (n : ℝ)) := by
      rw [Real.log_div hNpos.ne' hnpos.ne']
    calc
      h n * (Real.log (N : ℝ) - Real.log (n : ℝ))
          = h n * Real.log ((N : ℝ) / (n : ℝ)) := by rw [hlog_div]
      _ ≤ h n * ((N : ℝ) / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.log_le_self hratio_nonneg) (hnonneg n)
      _ = (N : ℝ) * (h n / (n : ℝ)) := by ring
  have hidentity :
      partialSum h N * Real.log (N : ℝ) =
        (∑ n ∈ Finset.Icc 1 N,
          h n * (Real.log (N : ℝ) - Real.log (n : ℝ))) +
          logPartialSum h N := by
    unfold partialSum logPartialSum
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hweighted :
      partialSum h N * Real.log (N : ℝ) ≤
        (K + 1) * (N : ℝ) * reciprocalPartialSum h N := by
    rw [hidentity]
    calc
      (∑ n ∈ Finset.Icc 1 N,
          h n * (Real.log (N : ℝ) - Real.log (n : ℝ))) +
          logPartialSum h N
          ≤ (N : ℝ) * reciprocalPartialSum h N +
              K * (N : ℝ) * reciprocalPartialSum h N :=
        add_le_add hcomplement hlog
      _ = (K + 1) * (N : ℝ) * reciprocalPartialSum h N := by ring
  rw [show
    (K + 1) * (N : ℝ) / Real.log (N : ℝ) * reciprocalPartialSum h N =
      ((K + 1) * (N : ℝ) * reciprocalPartialSum h N) /
        Real.log (N : ℝ) by ring]
  exact (le_div_iff₀ hlogNpos).2 hweighted

/--
The prime-power-mass-to-log-moment step, stated independently of the concrete
encoding of prime powers.  In the Halberstam--Richert proof, `W Q` is
`sum_{p^ν ≤ Q} h(p^ν) log(p^ν)`.  Unique factorization gives `hconv`, and the
Chebyshev/geometric calculation gives `hW`.  This lemma performs the remaining
finite summation with exact constant `K`.
-/
theorem log_moment_of_mass_convolution
    (h : ℕ → ℝ) (hnonneg : ∀ n, 0 ≤ h n)
    (W : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K) (N : ℕ)
    (hconv : logPartialSum h N ≤
      ∑ m ∈ Finset.Icc 1 N, h m * W (N / m))
    (hW : ∀ Q : ℕ, W Q ≤ K * (Q : ℝ)) :
    logPartialSum h N ≤
      K * (N : ℝ) * reciprocalPartialSum h N := by
  calc
    logPartialSum h N
        ≤ ∑ m ∈ Finset.Icc 1 N, h m * W (N / m) := hconv
    _ ≤ ∑ m ∈ Finset.Icc 1 N, h m * (K * ((N / m : ℕ) : ℝ)) := by
      refine Finset.sum_le_sum ?_
      intro m hm
      exact mul_le_mul_of_nonneg_left (hW (N / m)) (hnonneg m)
    _ ≤ ∑ m ∈ Finset.Icc 1 N,
        K * (N : ℝ) * (h m / (m : ℝ)) := by
      refine Finset.sum_le_sum ?_
      intro m hm
      have hcastdiv : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / (m : ℝ) :=
        Nat.cast_div_le
      calc
        h m * (K * ((N / m : ℕ) : ℝ))
            ≤ h m * (K * ((N : ℝ) / (m : ℝ))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hcastdiv hK) (hnonneg m)
        _ = K * (N : ℝ) * (h m / (m : ℝ)) := by ring
    _ = K * (N : ℝ) * reciprocalPartialSum h N := by
      unfold reciprocalPartialSum
      rw [Finset.mul_sum]

/--
Consumer-shaped explicit Halberstam--Richert theorem, reduced to the
logarithmic-moment estimate.  Once the standard prime-power mass calculation
provides `hlog`, the constant is exactly `K + 1` and the Euler product is the
one used in Erdős--Tenenbaum Lemma 1.
-/
theorem halberstam_richert_of_log_moment
    (h : ℕ → ℝ)
    (h0 : h 0 = 0)
    (h1 : h 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → h (m * n) = h m * h n)
    (hnonneg : ∀ n, 0 ≤ h n)
    (hloc : ∀ {p : ℕ}, p.Prime →
      Summable (fun j : ℕ => ‖recipWeight h (p ^ j)‖))
    (K : ℝ) (hK : 0 ≤ K) (N : ℕ) (hN : 2 ≤ N)
    (hlog : logPartialSum h N ≤
      K * (N : ℝ) * reciprocalPartialSum h N) :
    partialSum h N ≤
      (K + 1) * (N : ℝ) / Real.log (N : ℝ) *
        ∏ p ∈ (N + 1).primesBelow,
          ∑' j : ℕ, h (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
  have hmean := mean_le_of_log_moment h hnonneg K N hN hlog
  have heuler : reciprocalPartialSum h N ≤
      ∏ p ∈ (N + 1).primesBelow,
        ∑' j : ℕ, h (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
    simpa [reciprocalPartialSum] using
      reciprocal_sum_le_euler_product h h0 h1 hmul hnonneg hloc N
  have hfactor_nonneg :
      0 ≤ (K + 1) * (N : ℝ) / Real.log (N : ℝ) := by
    exact div_nonneg
      (mul_nonneg (by linarith) (Nat.cast_nonneg N))
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))
  exact hmean.trans (mul_le_mul_of_nonneg_left heuler hfactor_nonneg)

/--
Fully assembled explicit mean-value bound from the two concrete obligations
that remain in a prime-power implementation: the convolution inequality and
the linear prime-power mass bound.
-/
theorem halberstam_richert_of_mass_convolution
    (h : ℕ → ℝ)
    (h0 : h 0 = 0)
    (h1 : h 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → h (m * n) = h m * h n)
    (hnonneg : ∀ n, 0 ≤ h n)
    (hloc : ∀ {p : ℕ}, p.Prime →
      Summable (fun j : ℕ => ‖recipWeight h (p ^ j)‖))
    (W : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K) (N : ℕ) (hN : 2 ≤ N)
    (hconv : logPartialSum h N ≤
      ∑ m ∈ Finset.Icc 1 N, h m * W (N / m))
    (hW : ∀ Q : ℕ, W Q ≤ K * (Q : ℝ)) :
    partialSum h N ≤
      (K + 1) * (N : ℝ) / Real.log (N : ℝ) *
        ∏ p ∈ (N + 1).primesBelow,
          ∑' j : ℕ, h (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
  apply halberstam_richert_of_log_moment h h0 h1 hmul hnonneg hloc K hK N hN
  exact log_moment_of_mass_convolution h hnonneg W K hK N hconv hW

/-! ## The prime-power convolution (upstream `PrimePowerConvolution448.lean`) -/

/-- The prime-power logarithmic mass `∑_{p^ν ≤ Q, ν ≥ 1} h(p^ν) log(p^ν)`. -/
noncomputable def primePowerMass (h : ℕ → ℝ) (Q : ℕ) : ℝ :=
  ∑ p ∈ (Q + 1).primesBelow,
    ∑ nu ∈ Finset.Icc 1 (Nat.log p Q),
      h (p ^ nu) * Real.log ((p ^ nu : ℕ) : ℝ)

lemma log_eq_sum_primeFactors (n : ℕ) :
    Real.log (n : ℝ) =
      ∑ p ∈ n.primeFactors,
        Real.log ((p ^ n.factorization p : ℕ) : ℝ) := by
  rw [Real.log_nat_eq_sum_factorization]
  simp only [Finsupp.sum, Nat.support_factorization]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Nat.cast_pow, Real.log_pow]

lemma weighted_log_eq_sum_primeFactors
    (h : ℕ → ℝ)
    (hmul : ∀ {a b : ℕ}, a.Coprime b → h (a * b) = h a * h b)
    {n : ℕ} (hn : n ≠ 0) :
    h n * Real.log (n : ℝ) =
      ∑ p ∈ n.primeFactors,
        h (ordCompl[p] n) *
          (h (ordProj[p] n) * Real.log ((ordProj[p] n : ℕ) : ℝ)) := by
  rw [log_eq_sum_primeFactors, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp_mem
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hcop : (ordProj[p] n).Coprime (ordCompl[p] n) :=
    (Nat.coprime_ordCompl hp hn).pow_left _
  have hdecomp : ordProj[p] n * ordCompl[p] n = n :=
    Nat.ordProj_mul_ordCompl_eq_self n p
  calc
    h n * Real.log ((ordProj[p] n : ℕ) : ℝ) =
        h (ordProj[p] n * ordCompl[p] n) *
          Real.log ((ordProj[p] n : ℕ) : ℝ) := by rw [hdecomp]
    _ = (h (ordProj[p] n) * h (ordCompl[p] n)) *
          Real.log ((ordProj[p] n : ℕ) : ℝ) := by rw [hmul hcop]
    _ = h (ordCompl[p] n) *
          (h (ordProj[p] n) * Real.log ((ordProj[p] n : ℕ) : ℝ)) := by ring

/-- Index type `(n, p)` of the source sum. -/
abbrev SourceIndex := Sigma fun _ : ℕ => ℕ

/-- Index type `(m, p, ν)` of the target sum. -/
abbrev TargetIndex := Sigma fun _ : ℕ => Sigma fun _ : ℕ => ℕ

/-- Source index set: `n ≤ N` and `p ∣ n` prime. -/
def sourceSet (N : ℕ) : Finset SourceIndex :=
  (Finset.Icc 1 N).sigma fun n => n.primeFactors

/-- Target index set: `m ≤ N`, `p ≤ N / m` prime, `1 ≤ ν ≤ log_p (N / m)`. -/
def targetSet (N : ℕ) : Finset TargetIndex :=
  (Finset.Icc 1 N).sigma fun m =>
    ((N / m + 1).primesBelow).sigma fun p =>
      Finset.Icc 1 (Nat.log p (N / m))

/-- Source weight `h(n / p^{v_p(n)}) h(p^{v_p(n)}) log p^{v_p(n)}`. -/
noncomputable def sourceWeight (h : ℕ → ℝ) (a : SourceIndex) : ℝ :=
  h (ordCompl[a.2] a.1) *
    (h (ordProj[a.2] a.1) * Real.log ((ordProj[a.2] a.1 : ℕ) : ℝ))

/-- Target weight `h(m) h(p^ν) log p^ν`. -/
noncomputable def targetWeight (h : ℕ → ℝ) (a : TargetIndex) : ℝ :=
  h a.1 * (h (a.2.1 ^ a.2.2) * Real.log ((a.2.1 ^ a.2.2 : ℕ) : ℝ))

/-- `(n, p) ↦ (n / p^{v_p(n)}, p, v_p(n))`. -/
def sourceToTarget (a : SourceIndex) : TargetIndex :=
  ⟨ordCompl[a.2] a.1, ⟨a.2, a.1.factorization a.2⟩⟩

lemma sourceToTarget_injective_on (N : ℕ) :
    Set.InjOn sourceToTarget ↑(sourceSet N) := by
  intro a ha b hb hab
  rcases a with ⟨n, p⟩
  rcases b with ⟨n', p'⟩
  have hn : n = n' := by
    calc
      n = (sourceToTarget ⟨n, p⟩).2.1 ^ (sourceToTarget ⟨n, p⟩).2.2 *
          (sourceToTarget ⟨n, p⟩).1 :=
        (Nat.ordProj_mul_ordCompl_eq_self n p).symm
      _ = (sourceToTarget ⟨n', p'⟩).2.1 ^ (sourceToTarget ⟨n', p'⟩).2.2 *
          (sourceToTarget ⟨n', p'⟩).1 := congrArg
            (fun z : TargetIndex => z.2.1 ^ z.2.2 * z.1) hab
      _ = n' := Nat.ordProj_mul_ordCompl_eq_self n' p'
  have hp : p = p' := congrArg (fun z : TargetIndex => z.2.1) hab
  subst n'
  subst p'
  rfl

lemma sourceToTarget_mem_targetSet {N : ℕ} {a : SourceIndex}
    (ha : a ∈ sourceSet N) : sourceToTarget a ∈ targetSet N := by
  rcases a with ⟨n, p⟩
  simp only [sourceSet, Finset.mem_sigma] at ha
  rcases ha with ⟨hnIcc, hp_mem⟩
  rcases Finset.mem_Icc.mp hnIcc with ⟨hn_one, hnN⟩
  have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn_one)
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hp_dvd : p ∣ n := (Nat.mem_primeFactors.mp hp_mem).2.1
  have hnu : 0 < n.factorization p :=
    hp.factorization_pos_of_dvd hn0 hp_dvd
  have hmpos : 0 < ordCompl[p] n := Nat.ordCompl_pos p hn0
  have hmN : ordCompl[p] n ≤ N :=
    (Nat.div_le_self n (ordProj[p] n)).trans hnN
  have hpow_mul : p ^ n.factorization p * ordCompl[p] n ≤ N := by
    rw [Nat.ordProj_mul_ordCompl_eq_self]
    exact hnN
  have hpowQ : p ^ n.factorization p ≤ N / ordCompl[p] n := by
    rw [Nat.le_div_iff_mul_le hmpos]
    simpa [Nat.mul_comm] using hpow_mul
  have hpQ : p < N / ordCompl[p] n + 1 :=
    Nat.lt_succ_of_le ((Nat.le_self_pow hnu.ne' p).trans hpowQ)
  have hp_below : p ∈ (N / ordCompl[p] n + 1).primesBelow := by
    simpa [Nat.mem_primesBelow] using ⟨Nat.le_of_lt_succ hpQ, hp⟩
  have hnu_log : n.factorization p ≤ Nat.log p (N / ordCompl[p] n) :=
    Nat.le_log_of_pow_le hp.one_lt hpowQ
  simp only [sourceToTarget, targetSet, Finset.mem_sigma]
  exact ⟨Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hmpos.ne', hmN⟩,
    hp_below, Finset.mem_Icc.mpr ⟨hnu, hnu_log⟩⟩

lemma sourceWeight_eq_targetWeight_sourceToTarget
    (h : ℕ → ℝ) (a : SourceIndex) :
    sourceWeight h a = targetWeight h (sourceToTarget a) := by
  rfl

lemma targetWeight_nonneg
    (h : ℕ → ℝ) (hnonneg : ∀ n, 0 ≤ h n)
    {N : ℕ} {a : TargetIndex} (ha : a ∈ targetSet N) :
    0 ≤ targetWeight h a := by
  rcases a with ⟨m, ⟨p, nu⟩⟩
  simp only [targetSet, Finset.mem_sigma] at ha
  rcases ha with ⟨hm, hp, hnu⟩
  have hp_prime : p.Prime := Nat.prime_of_mem_primesBelow hp
  have hpow_one : 1 ≤ p ^ nu := by
    exact one_le_pow₀ hp_prime.one_lt.le
  unfold targetWeight
  exact mul_nonneg (hnonneg m)
    (mul_nonneg (hnonneg (p ^ nu)) (Real.log_nonneg (by exact_mod_cast hpow_one)))

/-- Unique factorisation: the log-weighted partial sum is dominated by the
convolution of `h` with the prime-power mass. -/
theorem logPartialSum_le_primePowerMass_convolution
    (h : ℕ → ℝ)
    (hnonneg : ∀ n, 0 ≤ h n)
    (hmul : ∀ {a b : ℕ}, a.Coprime b → h (a * b) = h a * h b)
    (N : ℕ) :
    logPartialSum h N ≤
      ∑ m ∈ Finset.Icc 1 N, h m * primePowerMass h (N / m) := by
  let e : {a // a ∈ sourceSet N} ↪ TargetIndex :=
    ⟨fun a => sourceToTarget a.1,
      fun a b hab => Subtype.ext (sourceToTarget_injective_on N a.2 b.2 hab)⟩
  let U : Finset TargetIndex := (sourceSet N).attach.map e
  have hsource : logPartialSum h N = ∑ a ∈ sourceSet N, sourceWeight h a := by
    unfold logPartialSum sourceSet
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro n hn
    exact weighted_log_eq_sum_primeFactors h hmul
      (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1))
  have himage :
      (∑ a ∈ sourceSet N, sourceWeight h a) =
        ∑ b ∈ U, targetWeight h b := by
    rw [← Finset.sum_attach]
    change (∑ a ∈ (sourceSet N).attach, sourceWeight h a.1) =
      ∑ b ∈ (sourceSet N).attach.map e, targetWeight h b
    rw [Finset.sum_map]
    exact Finset.sum_congr rfl fun a ha =>
      sourceWeight_eq_targetWeight_sourceToTarget h a.1
  have hUT : U ⊆ targetSet N := by
    intro b hb
    rw [Finset.mem_map] at hb
    rcases hb with ⟨a, ha, rfl⟩
    exact sourceToTarget_mem_targetSet a.2
  have hsubsum :
      (∑ b ∈ U, targetWeight h b) ≤
        ∑ b ∈ targetSet N, targetWeight h b := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hUT fun b hbT hbU =>
      targetWeight_nonneg h hnonneg hbT
  have htarget :
      (∑ b ∈ targetSet N, targetWeight h b) =
        ∑ m ∈ Finset.Icc 1 N, h m * primePowerMass h (N / m) := by
    unfold targetSet primePowerMass targetWeight
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.sum_sigma, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    simp only
    rw [Finset.mul_sum]
  rw [hsource, himage]
  exact hsubsum.trans_eq htarget

/-! ## The linear prime-power mass bound (upstream `PrimePowerMassLinear448.lean`) -/

/-- A deliberately generous but completely explicit dyadic estimate. -/
lemma dyadic_weight_sum_eq (n : ℕ) :
    (∑ k ∈ Finset.range n, (((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ k)) =
      4 - (((2 * n + 4 : ℕ) : ℝ) / (2 : ℝ) ^ n) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      push_cast
      have hpow : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp [hpow]
      ring

lemma dyadic_weight_sum_le_four (n : ℕ) :
    (∑ k ∈ Finset.range n, (((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ k)) ≤ 4 := by
  rw [dyadic_weight_sum_eq]
  exact sub_le_self _ (div_nonneg (by positivity) (by positivity))

lemma prime_log_div_sq_dyadic_block_le (k : ℕ) :
    (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
        Real.log (p : ℝ) / (p : ℝ) ^ 2) ≤
      (((k + 1 : ℕ) : ℝ) * Real.log 2) / (2 : ℝ) ^ k := by
  classical
  let B : Finset ℕ := (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hcard : B.card ≤ 2 ^ k := by
    calc
      B.card ≤ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).card :=
        Finset.card_filter_le _ _
      _ = 2 ^ k := by
        rw [Nat.card_Ico, pow_succ]
        omega
  have hpoint : ∀ p ∈ B,
      Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤
        (((k + 1 : ℕ) : ℝ) * Real.log 2) / (2 : ℝ) ^ (2 * k) := by
    intro p hp
    have hpB := Finset.mem_filter.mp hp
    have hpIco := Finset.mem_Ico.mp hpB.1
    have hpPos : 0 < (p : ℝ) := by exact_mod_cast hpB.2.pos
    have hlow : ((2 ^ k : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpIco.1
    have hupp : (p : ℝ) ≤ (((2 ^ (k + 1) : ℕ) : ℝ)) := by
      exact_mod_cast hpIco.2.le
    have hlog : Real.log (p : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
      calc
        Real.log (p : ℝ) ≤ Real.log (((2 ^ (k + 1) : ℕ) : ℝ)) :=
          Real.log_le_log hpPos hupp
        _ = ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
          rw [show (((2 ^ (k + 1) : ℕ) : ℝ)) = (2 : ℝ) ^ (k + 1) by norm_num,
            Real.log_pow]
    have hlowSq : (((2 ^ k : ℕ) : ℝ)) ^ 2 ≤ (p : ℝ) ^ 2 := by gcongr
    have hnumNonneg : 0 ≤ ((k + 1 : ℕ) : ℝ) * Real.log 2 :=
      mul_nonneg (by positivity) hlog2
    calc
      Real.log (p : ℝ) / (p : ℝ) ^ 2
          ≤ (((k + 1 : ℕ) : ℝ) * Real.log 2) / (p : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right hlog (sq_nonneg _)
      _ ≤ (((k + 1 : ℕ) : ℝ) * Real.log 2) /
            (((2 ^ k : ℕ) : ℝ)) ^ 2 :=
          div_le_div_of_nonneg_left hnumNonneg (by positivity) hlowSq
      _ = (((k + 1 : ℕ) : ℝ) * Real.log 2) / (2 : ℝ) ^ (2 * k) := by
          rw [show (((2 ^ k : ℕ) : ℝ)) = (2 : ℝ) ^ k by norm_num, ← pow_mul]
          simp [Nat.mul_comm]
  calc
    (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
        Real.log (p : ℝ) / (p : ℝ) ^ 2)
        = ∑ p ∈ B, Real.log (p : ℝ) / (p : ℝ) ^ 2 := rfl
    _ ≤ ∑ p ∈ B,
          (((k + 1 : ℕ) : ℝ) * Real.log 2) / (2 : ℝ) ^ (2 * k) :=
      Finset.sum_le_sum hpoint
    _ = (B.card : ℝ) *
          ((((k + 1 : ℕ) : ℝ) * Real.log 2) / (2 : ℝ) ^ (2 * k)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 ^ k : ℕ) : ℝ) *
          ((((k + 1 : ℕ) : ℝ) * Real.log 2) / (2 : ℝ) ^ (2 * k)) := by
      gcongr
    _ = (((k + 1 : ℕ) : ℝ) * Real.log 2) / (2 : ℝ) ^ k := by
      rw [show (((2 ^ k : ℕ) : ℝ)) = (2 : ℝ) ^ k by norm_num]
      have hpow : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
      rw [show (2 : ℝ) ^ (2 * k) = (2 : ℝ) ^ k * (2 : ℝ) ^ k by
        rw [two_mul, pow_add]]
      field_simp [hpow]

theorem sum_primesLE_log_div_sq_le (Y : ℕ) :
    (∑ p ∈ Nat.primesLE Y, Real.log (p : ℝ) / (p : ℝ) ^ 2) ≤
      4 * Real.log 2 := by
  classical
  let S : Finset ℕ := Nat.primesLE Y
  let T : Finset ℕ := Finset.range (Nat.log 2 Y + 1)
  have hmaps : ∀ p ∈ S, Nat.log 2 p ∈ T := by
    intro p hp
    have hpS := Nat.mem_primesLE.mp hp
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Nat.log_mono_right hpS.1))
  have hdecomp :
      (∑ k ∈ T, ∑ p ∈ S.filter (fun p => Nat.log 2 p = k),
          Real.log (p : ℝ) / (p : ℝ) ^ 2) =
        ∑ p ∈ S, Real.log (p : ℝ) / (p : ℝ) ^ 2 :=
    Finset.sum_fiberwise_of_maps_to hmaps
      (fun p : ℕ => Real.log (p : ℝ) / (p : ℝ) ^ 2)
  have hfiber : ∀ k ∈ T,
      (∑ p ∈ S.filter (fun p => Nat.log 2 p = k),
          Real.log (p : ℝ) / (p : ℝ) ^ 2) ≤
        ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
          Real.log (p : ℝ) / (p : ℝ) ^ 2 := by
    intro k hk
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro p hp
      have hpFilter := Finset.mem_filter.mp hp
      have hpS := Nat.mem_primesLE.mp hpFilter.1
      have hpPrime : Nat.Prime p := hpS.2
      have hpNe : p ≠ 0 := hpPrime.ne_zero
      have hlog : Nat.log 2 p = k := hpFilter.2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr
          ⟨by simpa [hlog] using Nat.pow_log_le_self 2 hpNe,
            by simpa [hlog, Nat.succ_eq_add_one] using
              Nat.lt_pow_succ_log_self Nat.one_lt_two p⟩,
          hpPrime⟩
    · intro p hp _hnot
      have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpPrime.one_le))
        (sq_nonneg _)
  calc
    (∑ p ∈ Nat.primesLE Y, Real.log (p : ℝ) / (p : ℝ) ^ 2)
        = ∑ p ∈ S, Real.log (p : ℝ) / (p : ℝ) ^ 2 := rfl
    _ = ∑ k ∈ T, ∑ p ∈ S.filter (fun p => Nat.log 2 p = k),
          Real.log (p : ℝ) / (p : ℝ) ^ 2 := hdecomp.symm
    _ ≤ ∑ k ∈ T,
          ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
            Real.log (p : ℝ) / (p : ℝ) ^ 2 :=
      Finset.sum_le_sum hfiber
    _ ≤ ∑ k ∈ T,
          (((k + 1 : ℕ) : ℝ) * Real.log 2) / (2 : ℝ) ^ k := by
      exact Finset.sum_le_sum (fun k hk => prime_log_div_sq_dyadic_block_le k)
    _ = Real.log 2 *
          ∑ k ∈ T, (((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ Real.log 2 * 4 := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [T] using dyadic_weight_sum_le_four (Nat.log 2 Y + 1))
        (Real.log_nonneg (by norm_num))
    _ = 4 * Real.log 2 := by ring

lemma sum_Icc_one_eq_sum_range_succ (f : ℕ → ℝ) (L : ℕ) :
    (∑ nu ∈ Finset.Icc 1 L, f nu) =
      ∑ j ∈ Finset.range L, f (j + 1) := by
  have hIcc : Finset.Icc 1 L = Finset.Ico 1 (L + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  have hlen : L + 1 - 1 = L := by omega
  rw [hlen]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.add_comm]

lemma primesBelow_succ_eq_primesLE (Q : ℕ) :
    (Q + 1).primesBelow = Nat.primesLE Q := by
  ext p
  simp [Nat.mem_primesBelow, Nat.mem_primesLE]

lemma weighted_geometric_tail_le
    (lambda2 : ℝ) (hlambda2 : 0 ≤ lambda2) (hlambda2_lt : lambda2 < 2)
    (N : ℕ) :
    (∑ k ∈ Finset.range N,
        lambda2 * (((k + 2 : ℕ) : ℝ) * (lambda2 / 2) ^ k)) ≤
      2 * lambda2 / (1 - lambda2 / 2) ^ 2 := by
  let r : ℝ := lambda2 / 2
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hrnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hnat := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hrnorm
  have hgeom := hasSum_geometric_of_lt_one hr0 hr1
  have hsum : HasSum (fun k : ℕ => ((k + 2 : ℕ) : ℝ) * r ^ k)
      (r / (1 - r) ^ 2 + 2 * (1 - r)⁻¹) := by
    -- v4.31 port: upstream closed this with `convert … using 1 <;> ext k <;> …`, which here
    -- leaves an instance goal; rewrite the summand instead.
    have hfun : (fun k : ℕ => ((k + 2 : ℕ) : ℝ) * r ^ k) =
        fun k : ℕ => (k : ℝ) * r ^ k + 2 * r ^ k := by
      ext k
      push_cast
      ring
    rw [hfun]
    exact hnat.add (hgeom.mul_left 2)
  have hnonneg : ∀ k : ℕ, 0 ≤ ((k + 2 : ℕ) : ℝ) * r ^ k := by
    intro k
    positivity
  have hfinite :
      (∑ k ∈ Finset.range N, ((k + 2 : ℕ) : ℝ) * r ^ k) ≤
        r / (1 - r) ^ 2 + 2 * (1 - r)⁻¹ := by
    rw [← hsum.tsum_eq]
    exact hsum.summable.sum_le_tsum (Finset.range N) (fun k _hk => hnonneg k)
  have hone : 0 < 1 - r := sub_pos.mpr hr1
  have hcoarse : r / (1 - r) ^ 2 + 2 * (1 - r)⁻¹ ≤
      2 / (1 - r) ^ 2 := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (sq_pos_of_pos hone)).2
    field_simp [ne_of_gt hone]
    nlinarith
  calc
    (∑ k ∈ Finset.range N,
        lambda2 * (((k + 2 : ℕ) : ℝ) * (lambda2 / 2) ^ k)) =
        lambda2 * ∑ k ∈ Finset.range N,
          (((k + 2 : ℕ) : ℝ) * r ^ k) := by
      simp only [r, Finset.mul_sum]
    _ ≤ lambda2 * (2 / (1 - r) ^ 2) :=
      mul_le_mul_of_nonneg_left (hfinite.trans hcoarse) hlambda2
    _ = 2 * lambda2 / (1 - lambda2 / 2) ^ 2 := by
      dsimp [r]
      ring

lemma tail_prime_power_term_le
    (h : ℕ → ℝ) (lambda1 lambda2 : ℝ)
    (hlambda1 : 0 ≤ lambda1) (hlambda2 : 0 ≤ lambda2)
    (hpow : ∀ (p j : ℕ), p.Prime →
      h (p ^ (j + 1)) ≤ lambda1 * lambda2 ^ j)
    {Q p k : ℕ} (hp : p.Prime) :
    (if p ^ (k + 2) ≤ Q then
        h (p ^ (k + 2)) * Real.log ((p ^ (k + 2) : ℕ) : ℝ)
      else 0) ≤
      lambda1 * (Q : ℝ) * (Real.log (p : ℝ) / (p : ℝ) ^ 2) *
        (lambda2 * (((k + 2 : ℕ) : ℝ) * (lambda2 / 2) ^ k)) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpTwo : 2 ≤ p := hp.two_le
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hright : 0 ≤
      lambda1 * (Q : ℝ) * (Real.log (p : ℝ) / (p : ℝ) ^ 2) *
        (lambda2 * (((k + 2 : ℕ) : ℝ) * (lambda2 / 2) ^ k)) := by
    positivity
  split_ifs with hpQ
  · have hpowLowerNat : p ^ 2 * 2 ^ k ≤ p ^ (k + 2) := by
      rw [show k + 2 = 2 + k by omega, pow_add]
      exact Nat.mul_le_mul_left (p ^ 2) (Nat.pow_le_pow_left hpTwo k)
    have hbaseQNat : p ^ 2 * 2 ^ k ≤ Q := hpowLowerNat.trans hpQ
    have hbasePos : 0 < (p : ℝ) ^ 2 * (2 : ℝ) ^ k := by positivity
    have hbaseQ : (p : ℝ) ^ 2 * (2 : ℝ) ^ k ≤ (Q : ℝ) := by
      exact_mod_cast hbaseQNat
    have hratio : 1 ≤ (Q : ℝ) / ((p : ℝ) ^ 2 * (2 : ℝ) ^ k) :=
      (le_div_iff₀ hbasePos).2 (by simpa using hbaseQ)
    have hA : 0 ≤ lambda1 * lambda2 ^ (k + 1) *
        (((k + 2 : ℕ) : ℝ) * Real.log (p : ℝ)) := by positivity
    calc
      h (p ^ (k + 2)) * Real.log ((p ^ (k + 2) : ℕ) : ℝ)
          ≤ (lambda1 * lambda2 ^ (k + 1)) *
              Real.log ((p ^ (k + 2) : ℕ) : ℝ) := by
            exact mul_le_mul_of_nonneg_right
              (by simpa [Nat.add_assoc] using hpow p (k + 1) hp)
              (Real.log_nonneg (by
                exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
                  (pow_ne_zero _ hp.ne_zero))))
      _ = lambda1 * lambda2 ^ (k + 1) *
            (((k + 2 : ℕ) : ℝ) * Real.log (p : ℝ)) := by
          rw [Nat.cast_pow, Real.log_pow]
      _ ≤ (lambda1 * lambda2 ^ (k + 1) *
            (((k + 2 : ℕ) : ℝ) * Real.log (p : ℝ))) *
            ((Q : ℝ) / ((p : ℝ) ^ 2 * (2 : ℝ) ^ k)) := by
          nlinarith
      _ = lambda1 * (Q : ℝ) * (Real.log (p : ℝ) / (p : ℝ) ^ 2) *
            (lambda2 * (((k + 2 : ℕ) : ℝ) * (lambda2 / 2) ^ k)) := by
          rw [div_pow, pow_succ]
          have hpne : (p : ℝ) ≠ 0 := ne_of_gt hpR
          have htwone : (2 : ℝ) ≠ 0 := by norm_num
          field_simp [hpne, htwone]
  · exact hright

lemma prime_inner_mass_le
    (h : ℕ → ℝ) (lambda1 lambda2 : ℝ)
    (hlambda1 : 0 ≤ lambda1) (hlambda2 : 0 ≤ lambda2)
    (hlambda2_lt : lambda2 < 2)
    (hpow : ∀ (p j : ℕ), p.Prime →
      h (p ^ (j + 1)) ≤ lambda1 * lambda2 ^ j)
    {Q p : ℕ} (hp : p.Prime) (hpQ : p ≤ Q) :
    (∑ nu ∈ Finset.Icc 1 (Nat.log p Q),
        h (p ^ nu) * Real.log ((p ^ nu : ℕ) : ℝ)) ≤
      lambda1 * Real.log (p : ℝ) +
        (lambda1 * (Q : ℝ) * (Real.log (p : ℝ) / (p : ℝ) ^ 2)) *
          (2 * lambda2 / (1 - lambda2 / 2) ^ 2) := by
  let L := Nat.log p Q
  let A : ℝ := lambda1 * (Q : ℝ) * (Real.log (p : ℝ) / (p : ℝ) ^ 2)
  have hLpos : 0 < L := Nat.log_pos hp.one_lt hpQ
  have hpowlog : p ^ L ≤ Q := by
    exact Nat.pow_log_le_self p (Nat.ne_of_gt (hp.pos.trans_le hpQ))
  have hlogp : 0 ≤ Real.log (p : ℝ) := hp.log_pos.le
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  rw [sum_Icc_one_eq_sum_range_succ]
  have hL : L = (L - 1) + 1 := by omega
  rw [show Nat.log p Q = L by rfl, hL, Finset.sum_range_succ']
  have htail :
      (∑ k ∈ Finset.range (L - 1),
          h (p ^ (k + 1 + 1)) *
            Real.log ((p ^ (k + 1 + 1) : ℕ) : ℝ)) ≤
        A * (2 * lambda2 / (1 - lambda2 / 2) ^ 2) := by
    calc
      (∑ k ∈ Finset.range (L - 1),
          h (p ^ (k + 1 + 1)) *
            Real.log ((p ^ (k + 1 + 1) : ℕ) : ℝ))
          ≤ ∑ k ∈ Finset.range (L - 1),
              A * (lambda2 *
                (((k + 2 : ℕ) : ℝ) * (lambda2 / 2) ^ k)) := by
            refine Finset.sum_le_sum ?_
            intro k hk
            have hkL : k + 2 ≤ L := by
              have := Finset.mem_range.mp hk
              omega
            have hpkQ : p ^ (k + 2) ≤ Q :=
              (Nat.pow_le_pow_right hp.pos hkL).trans hpowlog
            simpa [A, Nat.add_assoc, hpkQ] using
              tail_prime_power_term_le h lambda1 lambda2
                hlambda1 hlambda2 hpow (Q := Q) (p := p) (k := k) hp
      _ = A * ∑ k ∈ Finset.range (L - 1),
            lambda2 * (((k + 2 : ℕ) : ℝ) * (lambda2 / 2) ^ k) := by
          rw [Finset.mul_sum]
      _ ≤ A * (2 * lambda2 / (1 - lambda2 / 2) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (weighted_geometric_tail_le lambda2 hlambda2 hlambda2_lt (L - 1)) hA
  have hfirst :
      h (p ^ (0 + 1)) * Real.log ((p ^ (0 + 1) : ℕ) : ℝ) ≤
        lambda1 * Real.log (p : ℝ) := by
    simpa using mul_le_mul_of_nonneg_right (hpow p 0 hp) hlogp
  simpa [add_comm] using add_le_add htail hfirst

/-- The explicit linear prime-power mass estimate in exactly the indexing and
finite encoding used by `primePowerMass`. -/
theorem primePowerMass_le_linear
    (h : ℕ → ℝ) (lambda1 lambda2 : ℝ)
    (hlambda1 : 0 ≤ lambda1) (hlambda2 : 0 ≤ lambda2)
    (hlambda2_lt : lambda2 < 2)
    (hpow : ∀ (p j : ℕ), p.Prime →
      h (p ^ (j + 1)) ≤ lambda1 * lambda2 ^ j) :
    ∀ Q : ℕ,
      primePowerMass h Q ≤ explicitMassConstant lambda1 lambda2 * (Q : ℝ) := by
  intro Q
  let C : ℝ := 2 * lambda2 / (1 - lambda2 / 2) ^ 2
  have hden : 0 < 1 - lambda2 / 2 := by linarith
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hinner : ∀ p ∈ Nat.primesLE Q,
      (∑ nu ∈ Finset.Icc 1 (Nat.log p Q),
          h (p ^ nu) * Real.log ((p ^ nu : ℕ) : ℝ)) ≤
        lambda1 * Real.log (p : ℝ) +
          (lambda1 * (Q : ℝ) * (Real.log (p : ℝ) / (p : ℝ) ^ 2)) * C := by
    intro p hpMem
    have hpData := Nat.mem_primesLE.mp hpMem
    exact prime_inner_mass_le h lambda1 lambda2 hlambda1 hlambda2
      hlambda2_lt hpow hpData.2 hpData.1
  have htheta :
      lambda1 * (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ)) ≤
        lambda1 * (Real.log 4 * (Q : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ hlambda1
    rw [← Chebyshev.theta_eq_sum_primesLE_log]
    exact Chebyshev.theta_le_log4_mul_x (by positivity)
  have htailCoeff : 0 ≤ lambda1 * (Q : ℝ) * C := by positivity
  have hprimeSq :
      (lambda1 * (Q : ℝ) * C) *
          (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / (p : ℝ) ^ 2) ≤
        (lambda1 * (Q : ℝ) * C) * (4 * Real.log 2) :=
    mul_le_mul_of_nonneg_left (sum_primesLE_log_div_sq_le Q) htailCoeff
  calc
    primePowerMass h Q =
        ∑ p ∈ Nat.primesLE Q,
          ∑ nu ∈ Finset.Icc 1 (Nat.log p Q),
            h (p ^ nu) * Real.log ((p ^ nu : ℕ) : ℝ) := by
      rw [primePowerMass, primesBelow_succ_eq_primesLE]
    _ ≤ ∑ p ∈ Nat.primesLE Q,
          (lambda1 * Real.log (p : ℝ) +
            (lambda1 * (Q : ℝ) * (Real.log (p : ℝ) / (p : ℝ) ^ 2)) * C) :=
      Finset.sum_le_sum hinner
    _ = lambda1 * (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ)) +
          (lambda1 * (Q : ℝ) * C) *
            (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / (p : ℝ) ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ lambda1 * (Real.log 4 * (Q : ℝ)) +
          (lambda1 * (Q : ℝ) * C) * (4 * Real.log 2) :=
      add_le_add htheta hprimeSq
    _ = explicitMassConstant lambda1 lambda2 * (Q : ℝ) := by
      dsimp [C, explicitMassConstant]
      ring

/-! ## The assembled theorem (upstream `HalberstamComplete448.lean`) -/

/-- An explicit Halberstam--Richert mean-value theorem, with the prime-power
hypothesis indexed from the first nontrivial power. -/
theorem halberstam_richert_explicit
    (h : ℕ → ℝ)
    (h0 : h 0 = 0)
    (h1 : h 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → h (m * n) = h m * h n)
    (hnonneg : ∀ n, 0 ≤ h n)
    (lambda1 lambda2 : ℝ)
    (hlambda1 : 0 ≤ lambda1)
    (hlambda2 : 0 ≤ lambda2)
    (hlambda2_lt : lambda2 < 2)
    (hpow : ∀ (p : ℕ), p.Prime → ∀ j : ℕ,
      h (p ^ (j + 1)) ≤ lambda1 * lambda2 ^ j)
    (N : ℕ) (hN : 2 ≤ N) :
    partialSum h N ≤
      (explicitMassConstant lambda1 lambda2 + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          ∏ p ∈ (N + 1).primesBelow,
            ∑' j : ℕ, h (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
  apply halberstam_richert_of_mass_convolution
      h h0 h1 hmul hnonneg
      (W := primePowerMass h)
      (K := explicitMassConstant lambda1 lambda2)
      (N := N)
  · intro p hp
    exact (prime_power_local_mass h p lambda1 lambda2 hp
      hnonneg h1 hlambda1 hlambda2 hlambda2_lt (hpow p hp)).1
  · exact explicitMassConstant_nonneg hlambda1 hlambda2
  · exact hN
  · exact logPartialSum_le_primePowerMass_convolution h hnonneg hmul N
  · exact primePowerMass_le_linear h lambda1 lambda2
      hlambda1 hlambda2 hlambda2_lt (fun p j hp => hpow p hp j)

/-- The same theorem with the prime-power hypothesis in the source-paper
indexing `h (p^nu) ≤ A * B^nu`. -/
theorem halberstam_richert_explicit_source_indexing
    (h : ℕ → ℝ)
    (h0 : h 0 = 0)
    (h1 : h 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → h (m * n) = h m * h n)
    (hnonneg : ∀ n, 0 ≤ h n)
    (A B : ℝ)
    (hA : 0 ≤ A)
    (hB : 0 ≤ B)
    (hB_lt : B < 2)
    (hpow : ∀ (p : ℕ), p.Prime → ∀ nu : ℕ,
      h (p ^ nu) ≤ A * B ^ nu)
    (N : ℕ) (hN : 2 ≤ N) :
    partialSum h N ≤
      (explicitMassConstant (A * B) B + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          ∏ p ∈ (N + 1).primesBelow,
            ∑' j : ℕ, h (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
  apply halberstam_richert_explicit h h0 h1 hmul hnonneg (A * B) B
      (mul_nonneg hA hB) hB hB_lt _ N hN
  intro p hp j
  calc
    h (p ^ (j + 1)) ≤ A * B ^ (j + 1) := hpow p hp (j + 1)
    _ = (A * B) * B ^ j := by rw [pow_succ]; ring

/-! ## The exponential (Shiu, `q = 1`) form (upstream `Erdos67/MRShiuGlobalMean.lean`) -/

/-- The Euler exponent in the global (`q = 1`) Shiu estimate. -/
noncomputable def globalEulerExponent (h : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ (N + 1).primesBelow,
    (h p / (p : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)))

theorem globalEulerExponent_nonneg
    {h : ℕ → ℝ} (hnonneg : ∀ n, 0 ≤ h n) (N : ℕ) :
    0 ≤ globalEulerExponent h N := by
  unfold globalEulerExponent
  refine Finset.sum_nonneg fun p hp ↦ add_nonneg
    (div_nonneg (hnonneg p) (Nat.cast_nonneg p)) ?_
  have hpPrime := Nat.prime_of_mem_primesBelow hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
  have hp1' : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  positivity

/-- Keeping the prime term separate turns the remaining local Euler factor
into a genuinely quadratic tail. -/
theorem localFactor_le
    {h : ℕ → ℝ}
    (h1 : h 1 = 1)
    (hnonneg : ∀ n, 0 ≤ h n)
    (hpow : ∀ (p : ℕ), p.Prime → ∀ j : ℕ, h (p ^ (j + 1)) ≤ 1)
    {p : ℕ} (hp : p.Prime) :
    (∑' j : ℕ, h (p ^ j) / ((p ^ j : ℕ) : ℝ)) ≤
      1 + h p / (p : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  let term : ℕ → ℝ := fun j ↦ h (p ^ j) / ((p ^ j : ℕ) : ℝ)
  let r : ℝ := (p : ℝ)⁻¹
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hr0 : 0 ≤ r := inv_nonneg.mpr hpR.le
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ (lt_of_lt_of_le one_lt_two hpTwo)
  have htailBound (j : ℕ) : term (j + 2) ≤ r ^ (j + 2) := by
    have hden : (0 : ℝ) < ((p ^ (j + 2) : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_pos hp.pos
    have hnum : h (p ^ (j + 2)) ≤ 1 := by
      simpa only [show j + 2 = (j + 1) + 1 by omega] using hpow p hp (j + 1)
    calc
      term (j + 2) = h (p ^ (j + 2)) /
          ((p ^ (j + 2) : ℕ) : ℝ) := rfl
      _ ≤ 1 / ((p ^ (j + 2) : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hnum hden.le
      _ = r ^ (j + 2) := by
        rw [Nat.cast_pow]
        simp only [r, one_div, inv_pow]
  have hmajorSummable : Summable (fun j : ℕ ↦ r ^ (j + 2)) := by
    have hs := (summable_geometric_of_lt_one hr0 hr1).mul_left (r ^ 2)
    simpa only [pow_add, mul_comm, mul_left_comm, mul_assoc] using hs
  have htailNonneg (j : ℕ) : 0 ≤ term (j + 2) :=
    div_nonneg (hnonneg _) (Nat.cast_nonneg _)
  have htailSummable : Summable (fun j : ℕ ↦ term (j + 2)) :=
    Summable.of_nonneg_of_le htailNonneg htailBound hmajorSummable
  have htermSummable : Summable term := (summable_nat_add_iff 2).1 htailSummable
  have hshiftSummable : Summable (fun j : ℕ ↦ term (j + 1)) :=
    (summable_nat_add_iff 1).2 htermSummable
  have htailTsum :
      (∑' j : ℕ, term (j + 2)) ≤ ∑' j : ℕ, r ^ (j + 2) :=
    htailSummable.tsum_le_tsum htailBound hmajorSummable
  have hmajorTsum :
      (∑' j : ℕ, r ^ (j + 2)) = r ^ 2 / (1 - r) := by
    have hs := ((hasSum_geometric_of_lt_one hr0 hr1).mul_left (r ^ 2)).tsum_eq
    simpa only [pow_add, mul_comm, mul_left_comm, mul_assoc,
      div_eq_mul_inv] using hs
  have hzero : term 0 = 1 := by simp [term, h1]
  have honeTerm : term 1 = h p / (p : ℝ) := by simp [term]
  rw [show (∑' j : ℕ, h (p ^ j) / ((p ^ j : ℕ) : ℝ)) =
      ∑' j : ℕ, term j by rfl]
  rw [htermSummable.tsum_eq_zero_add, hzero,
    hshiftSummable.tsum_eq_zero_add, honeTerm]
  have htailFinal :
      (∑' j : ℕ, term (j + 2)) ≤
        1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    calc
      (∑' j : ℕ, term (j + 2)) ≤
          ∑' j : ℕ, r ^ (j + 2) := htailTsum
      _ = r ^ 2 / (1 - r) := hmajorTsum
      _ = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
        dsimp [r]
        have hp0 : (p : ℝ) ≠ 0 := ne_of_gt hpR
        have hp1 : (p : ℝ) - 1 ≠ 0 :=
          ne_of_gt (sub_pos.mpr (lt_of_lt_of_le one_lt_two hpTwo))
        field_simp [hp0, hp1]
  linarith

/-- The finite HR Euler product is bounded by the exponential of the exact
prime mass plus a quadratic tail. -/
theorem eulerProduct_le_exp
    {h : ℕ → ℝ}
    (h1 : h 1 = 1)
    (hnonneg : ∀ n, 0 ≤ h n)
    (hpow : ∀ (p : ℕ), p.Prime → ∀ j : ℕ, h (p ^ (j + 1)) ≤ 1)
    (N : ℕ) :
    (∏ p ∈ (N + 1).primesBelow,
        ∑' j : ℕ, h (p ^ j) / ((p ^ j : ℕ) : ℝ)) ≤
      Real.exp (globalEulerExponent h N) := by
  let E : ℕ → ℝ := fun p ↦
    h p / (p : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1))
  calc
    (∏ p ∈ (N + 1).primesBelow,
        ∑' j : ℕ, h (p ^ j) / ((p ^ j : ℕ) : ℝ)) ≤
        ∏ p ∈ (N + 1).primesBelow, (1 + E p) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact tsum_nonneg fun j ↦
          div_nonneg (hnonneg _) (Nat.cast_nonneg _)
      · intro p hp
        have hlocal := localFactor_le h1 hnonneg hpow
          (Nat.prime_of_mem_primesBelow hp)
        simpa [E, add_assoc] using hlocal
    _ ≤ Real.exp (∑ p ∈ (N + 1).primesBelow, E p) := by
      apply Real.prod_one_add_le_exp_sum
      intro p
      dsimp [E]
      by_cases hp0 : p = 0
      · subst p
        simp
      by_cases hp1 : p = 1
      · subst p
        simpa using hnonneg 1
      have hp2 : 2 ≤ p := by omega
      have hp1R : (1 : ℝ) < p := by exact_mod_cast
        (lt_of_lt_of_le Nat.one_lt_two hp2)
      have hp1R' : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      exact add_nonneg (div_nonneg (hnonneg p) (Nat.cast_nonneg p)) (by positivity)
    _ = Real.exp (globalEulerExponent h N) := by rfl

/-- Fully explicit, axiom-free `q = 1` Shiu estimate.  Unlike the crude
prime-power HR bound, its exponent retains the shifted first-prime mass. -/
theorem partialSum_le_exp
    {h : ℕ → ℝ}
    (h0 : h 0 = 0)
    (h1 : h 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → h (m * n) = h m * h n)
    (hnonneg : ∀ n, 0 ≤ h n)
    (hpow : ∀ (p : ℕ), p.Prime → ∀ j : ℕ, h (p ^ (j + 1)) ≤ 1)
    (N : ℕ) (hN : 2 ≤ N) :
    partialSum h N ≤
      (explicitMassConstant 1 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          Real.exp (globalEulerExponent h N) := by
  have hbase := halberstam_richert_explicit
    h h0 h1 hmul hnonneg 1 1 (by norm_num) (by norm_num) (by norm_num)
    (by simpa using hpow) N hN
  have heuler := eulerProduct_le_exp h1 hnonneg hpow N
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hfactor : 0 ≤
      (explicitMassConstant 1 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) := by
    exact div_nonneg
      (mul_nonneg
        (add_nonneg
          (explicitMassConstant_nonneg
            (by norm_num) (by norm_num)) zero_le_one)
        (Nat.cast_nonneg _)) hlog.le
  exact hbase.trans (mul_le_mul_of_nonneg_left heuler hfactor)

/-! ## Principia addition: the Pollack (2014, Lemma 2.4) form

The ported theorems need `h 0 = 0` and `0 ≤ h n` for **all** `n`.  A consumer's
multiplicative `f` is usually only controlled at prime powers and its value at `0` is junk,
so we pass through `zeroExt f` (which agrees with `f` on every `n ≥ 1`) and recover
nonnegativity from the prime-power hypothesis by multiplicative induction.

The only analytic input beyond the port is the **upper half of Mertens' second theorem**,
carried as the named hypothesis `MertensUpper B`. -/

/-- `f` with its junk value at `0` replaced by `0`. -/
noncomputable def zeroExt (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else f n

lemma zeroExt_zero (f : ℕ → ℝ) : zeroExt f 0 = 0 := by
  simp [zeroExt]

lemma zeroExt_of_ne_zero (f : ℕ → ℝ) {n : ℕ} (hn : n ≠ 0) : zeroExt f n = f n := by
  simp [zeroExt, hn]

lemma zeroExt_mul (f : ℕ → ℝ)
    (hmul : ∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n)
    {m n : ℕ} (hmn : m.Coprime n) :
    zeroExt f (m * n) = zeroExt f m * zeroExt f n := by
  by_cases hm : m = 0
  · subst m
    have hn : n = 1 := by simpa using hmn
    subst n
    simp [zeroExt]
  by_cases hn : n = 0
  · subst n
    have hm1 : m = 1 := by simpa [Nat.coprime_comm] using hmn
    subst m
    simp [zeroExt]
  rw [zeroExt_of_ne_zero f (Nat.mul_ne_zero hm hn), zeroExt_of_ne_zero f hm,
    zeroExt_of_ne_zero f hn, hmul m n hmn]

/-- A multiplicative function that is nonnegative on prime powers is nonnegative on every
positive integer (stated for `zeroExt f`, which covers `n = 0` too). -/
lemma zeroExt_nonneg (f : ℕ → ℝ) (hf1 : f 1 = 1)
    (hmul : ∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n)
    (hpp : ∀ p k : ℕ, p.Prime → 1 ≤ k → 0 ≤ f (p ^ k))
    (n : ℕ) : 0 ≤ zeroExt f n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
      rw [zeroExt_of_ne_zero f (pow_ne_zero _ hp.ne_zero)]
      exact hpp p k hp hk
  | zero => simp [zeroExt]
  | one => rw [zeroExt_of_ne_zero f one_ne_zero, hf1]; exact zero_le_one
  | coprime a b _ _ hab ha hb =>
      rw [zeroExt_mul f hmul hab]
      exact mul_nonneg ha hb

/-- `∑_{n ∈ [2, N]} 1/(n(n-1)) = 1 - 1/N` (telescoping), for `N ≥ 1`. -/
lemma sum_Icc_two_inv_mul_pred (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) = 1 - 1 / (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      have hN0 : (N : ℝ) ≠ 0 := by
        have : (1 : ℝ) ≤ N := by exact_mod_cast hN
        linarith
      push_cast
      rw [show (N : ℝ) + 1 - 1 = N by ring]
      have hN1' : (N : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring

/-- The quadratic prime tail `∑_{p ≤ N} 1/(p(p-1))` is at most `1`. -/
lemma sum_primesLE_inv_mul_pred_le_one (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : Nat.primesLE 0 = ∅ := by
      ext p
      simp only [Nat.mem_primesLE, Finset.notMem_empty, iff_false, not_and]
      intro hp0 hp
      exact hp.ne_zero (Nat.le_zero.mp hp0)
    rw [this, Finset.sum_empty]
    exact zero_le_one
  have hsub : Nat.primesLE N ⊆ Finset.Icc 2 N := by
    intro p hp
    have hpd := Nat.mem_primesLE.mp hp
    exact Finset.mem_Icc.mpr ⟨hpd.2.two_le, hpd.1⟩
  have hnonneg : ∀ n ∈ Finset.Icc 2 N, n ∉ Nat.primesLE N →
      0 ≤ (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    intro n hn _
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have h1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have h0 : (0 : ℝ) < (n : ℝ) := by linarith
    positivity
  calc
    ∑ p ∈ Nat.primesLE N, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
        ≤ ∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
    _ = 1 - 1 / (N : ℝ) := sum_Icc_two_inv_mul_pred N hN
    _ ≤ 1 := by
      have : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
      linarith

/-- **Named hypothesis: the upper half of Mertens' second theorem**, with constant `B`:
`∑_{p ≤ N} 1/p ≤ log log N + B` for every integer `N ≥ 2`.
(True for suitable `B` -- it is discharged in `Principia.Common.HalberstamRichertPollack`.) -/
def MertensUpper (B : ℝ) : Prop :=
  ∀ N : ℕ, 2 ≤ N →
    ∑ p ∈ Nat.primesLE N, (1 : ℝ) / (p : ℝ) ≤ Real.log (Real.log (N : ℝ)) + B

/-- A `MertensUpper` constant is automatically nonnegative (test at `N = 2`). -/
lemma MertensUpper.nonneg {B : ℝ} (hB : MertensUpper B) : 0 ≤ B := by
  have h2 := hB 2 le_rfl
  have hsum : 0 ≤ ∑ p ∈ Nat.primesLE 2, (1 : ℝ) / (p : ℝ) :=
    Finset.sum_nonneg fun p _ => by positivity
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hloglog : Real.log (Real.log ((2 : ℕ) : ℝ)) ≤ 0 := by
    have hpos : 0 ≤ Real.log ((2 : ℕ) : ℝ) :=
      Real.log_nonneg (by norm_num)
    exact Real.log_nonpos hpos (by simpa using hlog2)
  calc
    (0 : ℝ) ≤ Real.log (Real.log ((2 : ℕ) : ℝ)) + B := hsum.trans h2
    _ ≤ 0 + B := add_le_add hloglog le_rfl
    _ = B := zero_add B

/-- **Pollack's form of the Halberstam--Richert bound (integer cut-off), conditional on
`MertensUpper B`.**  For `f` multiplicative with `0 ≤ f (p^k) ≤ 1` at every prime power and
every integer `N ≥ 1`,
`∑_{1 ≤ n ≤ N} f n ≤ (K + 1) e^{B+1} · N · exp (∑_{p ≤ N} (f p - 1)/p)`,
with `K = explicitMassConstant 1 1 = log 4 + 32 log 2`. -/
theorem sum_le_mul_exp_of_mertensUpper {B : ℝ} (hB : MertensUpper B)
    (f : ℕ → ℝ) (hf1 : f 1 = 1)
    (hmul : ∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n)
    (hpp : ∀ p k : ℕ, p.Prime → 1 ≤ k → 0 ≤ f (p ^ k) ∧ f (p ^ k) ≤ 1)
    (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, f n ≤
      (explicitMassConstant 1 1 + 1) * Real.exp (B + 1) * (N : ℝ) *
        Real.exp (∑ p ∈ Nat.primesLE N, (f p - 1) / (p : ℝ)) := by
  set h : ℕ → ℝ := zeroExt f with hh
  set S : ℝ := ∑ p ∈ Nat.primesLE N, (f p - 1) / (p : ℝ) with hS
  have hK : 0 ≤ explicitMassConstant 1 1 :=
    explicitMassConstant_nonneg (by norm_num) (by norm_num)
  have hB0 : 0 ≤ B := hB.nonneg
  -- the partial sum of `f` is the partial sum of `h`
  have hsum_eq : ∑ n ∈ Finset.Icc 1 N, f n = partialSum h N := by
    unfold partialSum
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    rw [hh, zeroExt_of_ne_zero f hn0]
  rw [hsum_eq]
  rcases Nat.lt_or_ge N 2 with hN2 | hN2
  · -- `N = 1`: the sum is `f 1 = 1` and the constant is `≥ 1`
    have hN1 : N = 1 := by omega
    subst hN1
    have hP : Nat.primesLE 1 = ∅ := by
      ext p
      simp only [Nat.mem_primesLE, Finset.notMem_empty, iff_false, not_and]
      intro hp1 hp
      exact absurd hp.two_le (by omega)
    have hS0 : S = 0 := by rw [hS, hP, Finset.sum_empty]
    have hps : partialSum h 1 = 1 := by
      unfold partialSum
      rw [Finset.Icc_self, Finset.sum_singleton, hh, zeroExt_of_ne_zero f one_ne_zero, hf1]
    rw [hps, hS0, Real.exp_zero, mul_one, Nat.cast_one, mul_one]
    have he : 1 ≤ Real.exp (B + 1) := Real.one_le_exp (by linarith)
    nlinarith
  · have hnonneg : ∀ n, 0 ≤ h n := fun n =>
      zeroExt_nonneg f hf1 hmul (fun p k hp hk => (hpp p k hp hk).1) n
    have hpow : ∀ (p : ℕ), p.Prime → ∀ j : ℕ, h (p ^ (j + 1)) ≤ 1 := by
      intro p hp j
      rw [hh, zeroExt_of_ne_zero f (pow_ne_zero _ hp.ne_zero)]
      exact (hpp p (j + 1) hp (by omega)).2
    have hmain := partialSum_le_exp (h := h) (zeroExt_zero f)
      (by rw [hh, zeroExt_of_ne_zero f one_ne_zero, hf1])
      (fun hmn => zeroExt_mul f hmul hmn) hnonneg hpow N hN2
    have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
    -- split the Euler exponent
    have hsplit : globalEulerExponent h N =
        S + ∑ p ∈ Nat.primesLE N, (1 : ℝ) / (p : ℝ) +
          ∑ p ∈ Nat.primesLE N, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
      unfold globalEulerExponent
      rw [primesBelow_succ_eq_primesLE, hS, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp0 : p ≠ 0 := (Nat.mem_primesLE.mp hp).2.ne_zero
      rw [hh, zeroExt_of_ne_zero f hp0]
      ring
    have hexp : globalEulerExponent h N ≤
        S + Real.log (Real.log (N : ℝ)) + (B + 1) := by
      rw [hsplit]
      have h1 := hB N hN2
      have h2 := sum_primesLE_inv_mul_pred_le_one N
      linarith
    have hexp' : Real.exp (globalEulerExponent h N) ≤
        Real.exp S * Real.log (N : ℝ) * Real.exp (B + 1) := by
      calc
        Real.exp (globalEulerExponent h N)
            ≤ Real.exp (S + Real.log (Real.log (N : ℝ)) + (B + 1)) :=
          Real.exp_le_exp.mpr hexp
        _ = Real.exp S * Real.log (N : ℝ) * Real.exp (B + 1) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_log hlogpos]
    have hfactor : 0 ≤ (explicitMassConstant 1 1 + 1) * (N : ℝ) / Real.log (N : ℝ) := by
      positivity
    calc
      partialSum h N
          ≤ (explicitMassConstant 1 1 + 1) * (N : ℝ) / Real.log (N : ℝ) *
              Real.exp (globalEulerExponent h N) := hmain
      _ ≤ (explicitMassConstant 1 1 + 1) * (N : ℝ) / Real.log (N : ℝ) *
              (Real.exp S * Real.log (N : ℝ) * Real.exp (B + 1)) :=
          mul_le_mul_of_nonneg_left hexp' hfactor
      _ = (explicitMassConstant 1 1 + 1) * Real.exp (B + 1) * (N : ℝ) * Real.exp S := by
          field_simp

/-- **Pollack's form, real cut-off, conditional on `MertensUpper B`.**  For every real
`x ≥ 1`: `∑_{1 ≤ n ≤ x} f n ≤ (K + 1) e^{B+1} · x · exp (∑_{p ≤ x} (f p - 1)/p)`. -/
theorem sum_le_mul_exp_of_mertensUpper_real {B : ℝ} (hB : MertensUpper B)
    (f : ℕ → ℝ) (hf1 : f 1 = 1)
    (hmul : ∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n)
    (hpp : ∀ p k : ℕ, p.Prime → 1 ≤ k → 0 ≤ f (p ^ k) ∧ f (p ^ k) ≤ 1)
    (x : ℝ) (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n ≤
      (explicitMassConstant 1 1 + 1) * Real.exp (B + 1) * x *
        Real.exp (∑ p ∈ Nat.primesLE ⌊x⌋₊, (f p - 1) / (p : ℝ)) := by
  have hN : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hmain := sum_le_mul_exp_of_mertensUpper hB f hf1 hmul hpp ⌊x⌋₊ hN
  have hK : 0 ≤ explicitMassConstant 1 1 :=
    explicitMassConstant_nonneg (by norm_num) (by norm_num)
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  refine hmain.trans ?_
  have hc : 0 ≤ (explicitMassConstant 1 1 + 1) * Real.exp (B + 1) := by positivity
  have he : 0 ≤ Real.exp (∑ p ∈ Nat.primesLE ⌊x⌋₊, (f p - 1) / (p : ℝ)) :=
    (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfl hc) he

end Principia.Common.HalberstamRichert
