/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfgottWrap
import Principia.Erdos1054.Proofs.SmallRatio

set_option autoImplicit false

/-!
# `HC.EspagnRed`, the analytic reduction of `prop:espagn`: spine, links, and what stays owed

`HC.EspagnRed` (`HelfgottCited.lean`) is the whole analytic argument of `prop:espagn`
(`ternvin.tex` 2891-3272) as ONE named implication. Here it is split into its links, the links
are composed by application (`espagn_of_links`, `espagnRed_of_links`), and every link but three
is PROVED. Source lines are `ternvin.tex` (arXiv:1312.7748v2).

## The spine (a real `R = Q₀/sq` is sorted into one of five cases)

```
 eq:elsyn → eq:karka   ratio ≤ B  ⇐  karka at ω(0.6)          ratio_le, karka_alg     PROVED
                       B = (log Q₀+1.36)/(log Q+c_E) ≤ ω(0.6)   ratio_le_omega          PROVED
 (i)  lem:trivo        G_q(A)/G_q(AB) ≤ e^γ(log(A+log q)+0.65771)/(log B+1.312)
                       from eq:bete, eq:hosmo, lem:suspiro, eq:charpy        trivo      PROVED
      lem:suspiro      = SuspiroSmallCited (cited) + SuspiroBig          suspiro_of  NAMED part
      lem:paniz region R + log q ≤ c(1.36)Q₀^τ ⇒ ratio ≤ B             paniz_alg   PROVED
 (ii) eq:miasmar       err bounds from eq:cante / eq:charpy + eq:hosmo   errE_le, errE_ge PROVED
 (iii) R > ϖ(q)        ¬(i) ∧ ¬(ii) ⇒ R > ϖ(q): eq:koklo, eq:joho iterated  varpiE_lt  PROVED
      R ≥ λ(q)         eq:agammen / eq:sosor from eq:malito               luce_big    PROVED
      ⌊R⌋ ≥ ϖ, R < λ   the cited check at the integer ⌊R⌋               luce_check  PROVED
      ⌊R⌋ < ϖ < R < λ  THE HOLE: nothing covers it                        EspagnEdge  NAMED
      q out of range   ϖ(q) ≥ λ(q) (eq:victo, eq:drolo, eq:mutuso)        EspagnLargeQ NAMED
 eq:luce → eq:karka                                                     karka_of_luce PROVED
```

The "check at `ρ = 0.6` covers every `ρ ≤ 0.6`" step needs no separate argument: every case works
at `ω(0.6)` and `τ(0.6)` directly, `ρ` entering only through `B ≤ ω(0.6)` and `paniz_alg`.

## What stays NAMED (exact statements below)

* **`SuspiroBig`** — `lem:suspiro` for `m + log q > 8.53`: Rosser–Schoenfeld 1975 (5.1)
  (`θ(m) ≤ 1.001102m`) and 1962 (3.42) (= `GS.RS62Thm15`), cited PROOFS — an owner question.
  Its small range is Helfgott's cited run (`HC.SuspiroSmallCited`).
* **`EspagnLargeQ`** — `ϖ(q) ≥ λ(q)` for `q ≥ 3.3·10⁹` outside the checked range (`210 ∤ q`, or
  `q ≥ 2.2·10¹⁰`). Its inputs are the cited `EspagnSmallCited` pieces and RS62 (3.16), (3.24),
  (3.30), (3.32): analysis over a few hundred lines of source-level estimates, not attempted here.
* **`EspagnEdge`** — the citation verifier's hole, and the one input no printed argument or run
  covers. "It is enough to check integer values of `R`" (3282-3286) is true on `[⌈ϖ⌉, λ)` but not
  on `(ϖ, ⌈ϖ⌉)`, where `err_{q,R} = G_q(⌊ϖ⌋) − (φ/q)(log R + …)` and `⌊ϖ⌋ < ϖ` lies below the
  checked range. The supremum over that partial step is the value at the real point `R = ϖ(q)`
  (`G_q` constant on the step, `log R` and `R^{−1/3}` monotone), so the missing fact is EXACTLY
  the cited check's inequality at one extra real point per `q`. **No margin argument exists from
  the cited statement as printed**: it is `≤` with no slack, and closing the step from the check
  at `⌈ϖ⌉` would need slack `(φ(q)/q)·log(⌈ϖ⌉/ϖ)` plus a `R^{−1/3}` term, where `log(⌈ϖ⌉/ϖ)` is
  not small when `ϖ(q)` is (`q = 30030`: `ϖ = 1.79`, `log(2/1.79) = 0.11`). It is a computation
  nobody ran: one value `G_q(⌊ϖ(q)⌋)` per `q`, which any cumulative evaluation of Helfgott's first
  checked value `G_q(⌈ϖ(q)⌉)` passes through. Float64: true on all `297 419` tested moduli
  (`q ≤ 3·10⁵`, multiples of `210` to `4.2·10⁶`, primorials to `223092870`), worst margin `0.0234`
  at `q = 1` (`scratchpad/hcite/edge_num.py`).

## A second finding: `lem:paniz` as stated does not give `prop:espagn`'s bound

`eq:joho` is justified by "all smaller `R` are covered by that Lemma", but `lem:paniz`'s conclusion
(2818) has denominator `log Q + 1.312`, while `prop:espagn` needs `log Q + c_E`, a strictly smaller
ratio (`c_E = 1.33258 > 1.312`). The REGION is nevertheless covered: re-deriving from `lem:trivo`
with the correct denominator (`paniz_alg`) needs
`(K + 0.4 log Q₀)(log Q + c_E) ≤ (log Q₀ + 1.36)(log Q − log Q₀ + 1.312)`, `K = 1.36 − 1.36²/5.248`,
which holds for `log Q₀ ≤ 0.6 log Q` with cross-multiplied margin `≥ 0.00637 log Q₀ + 0.4417`
(before cross-multiplying: `0.0038` in the numerator as `Q → ∞` at `ρ = 0.6`). So the printed
`ϖ(q)` and check range stand; only the citation of `lem:paniz` is inexact.
-/

namespace Principia.Common.TernaryGoldbach.HX

open Principia.Common.PSieve (gQ)
open Principia.Common.TernaryGoldbach.HC (omegaE cDeltaE kappaE betaE lambdaE tauE cSig cRho2
  varpi0 varpiE errE sumLogP)

/-! ## (0) Constants -/

/-- `e^γ ≤ 1.7810727` (`SmallRatio.exp_gamma_le`). -/
theorem expG_le : Real.exp Real.eulerMascheroniConstant ≤ 1.7810727 :=
  Principia.Erdos1054.Proofs.SmallRatio.exp_gamma_le

/-- `log 10⁵ > 1`. -/
theorem logQ0_gt : 1 < Real.log 100000 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-- `ω(0.6)` with `1/0.6` written `5/3` (`linarith` does not clear a decimal denominator). -/
theorem omegaE_eq : omegaE = (Real.log 100000 + 1.36) / (5 / 3 * Real.log 100000 + CY.cE) := by
  unfold omegaE
  rw [show (0.6 : ℝ) = 3 / 5 by norm_num]
  ring

/-- `ω(0.6) > 0`. -/
theorem omegaE_pos (cer : CY.CERange) : 0 < omegaE := by
  rw [omegaE_eq]
  have := logQ0_gt
  have := cer.1
  apply div_pos <;> linarith

/-- `ω(0.6) < 1`. -/
theorem omegaE_lt_one (cer : CY.CERange) : omegaE < 1 := by
  rw [omegaE_eq]
  have := logQ0_gt
  have := cer.1
  have := cer.2
  rw [div_lt_one (by linarith)]
  linarith

/-- `c_Δ = 1.36 − c_E > 0` (needs the UPPER half of `CY.CERange`). -/
theorem cDeltaE_pos (cer : CY.CERange) : 0 < cDeltaE := by
  unfold cDeltaE
  linarith [cer.2]

/-- `τ(0.6) = 0.4e^{−γ} > 0`. -/
theorem tauE_pos : 0 < tauE := by
  unfold tauE
  exact mul_pos (by norm_num) (Real.exp_pos _)

/-- `τ(0.6) < 1`. -/
theorem tauE_lt_one : tauE < 1 := by
  unfold tauE
  have h : Real.exp (-Real.eulerMascheroniConstant) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  nlinarith [Real.exp_pos (-Real.eulerMascheroniConstant)]

/-- `∑_{p ∣ q} log p/p ≥ 0`. -/
theorem sumLogP_nonneg (q : ℕ) : 0 ≤ sumLogP q := by
  unfold sumLogP
  refine Finset.sum_nonneg fun p hp => div_nonneg (Real.log_nonneg ?_) (Nat.cast_nonneg p)
  exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le

/-- `∑_{p ∣ q} log p/p ≤ log q` (`∏_{p ∣ q} p ≤ q`). -/
theorem sumLogP_le (q : ℕ) (hq : 1 ≤ q) : sumLogP q ≤ Real.log q := by
  unfold sumLogP
  have h1 : ∑ p ∈ q.primeFactors, Real.log p / p ≤ ∑ p ∈ q.primeFactors, Real.log p := by
    refine Finset.sum_le_sum fun p hp => ?_
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
    exact div_le_self (Real.log_nonneg hp1) hp1
  have h2 : Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) = ∑ p ∈ q.primeFactors, Real.log p :=
    Real.log_prod fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  have h3 : (∏ p ∈ q.primeFactors, (p : ℝ)) ≤ q := by
    have h := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q)
    have h' : ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ≤ q := by exact_mod_cast h
    rwa [Nat.cast_prod] at h'
  have h4 : 0 < ∏ p ∈ q.primeFactors, (p : ℝ) := Finset.prod_pos fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  have h5 := Real.log_le_log h4 h3
  linarith

/-- `f₁(q) ≥ 0`. -/
theorem f1_nonneg (q : ℕ) : 0 ≤ CY.f1 q := by
  unfold CY.f1
  refine Finset.prod_nonneg fun p hp => ?_
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have h1 : 0 ≤ (p : ℝ) ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg (by linarith) _
  have h2 : 0 ≤ ((p : ℝ) ^ ((1 : ℝ) / 3) + (p : ℝ) ^ ((2 : ℝ) / 3)) /
      ((p : ℝ) * ((p : ℝ) - 1)) := by
    apply div_nonneg
    · exact add_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
    · exact mul_nonneg (by linarith) (by linarith)
  exact div_nonneg (by linarith) (by linarith)

/-- `κ(q) > 0`. -/
theorem kappaE_pos (cer : CY.CERange) (q : ℕ) (hq : 1 ≤ q) : 0 < kappaE q := by
  unfold kappaE
  have h1 := omegaE_lt_one cer
  have h2 := sumLogP_le q hq
  have h3 := cDeltaE_pos cer
  have h4 : 0 ≤ (1 - omegaE) * (Real.log q - sumLogP q) := mul_nonneg (by linarith) (by linarith)
  linarith

/-! ## (1) `lem:suspiro` and `lem:trivo` -/

/-- **`lem:suspiro`** (`ternvin.tex` 2733-2761): `∏_{p ∣ q ∨ p ≤ m} p/(p−1) ≤
e^γ(log(m + log q) + 0.65771)` for integers `m, q ≥ 1`. -/
def Suspiro : Prop :=
  ∀ m q : ℕ, 1 ≤ m → 1 ≤ q →
    HC.suspProd m q ≤
      Real.exp Real.eulerMascheroniConstant * (Real.log ((m : ℝ) + Real.log q) + 0.65771)

/-- **NAMED — `lem:suspiro` beyond the computed range** (`ternvin.tex` 2738-2757): for
`m + log q > 8.53`, from Rosser–Schoenfeld 1975 (5.1) `θ(m) ≤ (1 + 0.001102)m` and Rosser–Schoenfeld
1962 (3.42) (`GS.RS62Thm15`), via `𝒫 ≤ q·e^{θ(m)}` and the monotonicity of `a + b/t`. Cited
PROOFS of the literature (an owner question) plus arithmetic; `0.001102 + 1.40723/log 8.53 =
0.65759 ≤ 0.65771`. (The printed argument also needs `𝒫 ≥ 27`, which fails e.g. at `m = 1`,
`q = 5000`, `𝒫 = 10`; there `𝒫/φ(𝒫) ≤ 3 < 4.99 ≤` the right side, so the statement is unharmed.) -/
def SuspiroBig : Prop :=
  ∀ m q : ℕ, 1 ≤ m → 1 ≤ q → 8.53 < (m : ℝ) + Real.log q →
    HC.suspProd m q ≤
      Real.exp Real.eulerMascheroniConstant * (Real.log ((m : ℝ) + Real.log q) + 0.65771)

/-- **`lem:suspiro` from the cited small range and the named large range.** -/
theorem suspiro_of (sm : HC.SuspiroSmallCited) (sb : SuspiroBig) : Suspiro := by
  intro m q hm hq
  rcases le_or_gt ((m : ℝ) + Real.log q) 8.53 with h | h
  · exact sm m q hm hq h
  · exact sb m q hm hq h

/-- **`𝒫/φ(𝒫) = ∏_{p ∈ S} p/(p−1)`** for `𝒫 = ∏_{p ∈ S} p`, `S` a finite set of primes
(`PSieve.wq_eq`, `PSieve.prod_inv_eq`, `Nat.primeFactors_prod`). -/
theorem wq_prod (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    PSieve.wq (∏ p ∈ S, p) = ∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1) := by
  have hP1 : 1 ≤ ∏ p ∈ S, p :=
    Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun p hp => (hS p hp).ne_zero)
  rw [PSieve.wq_eq, ← PSieve.prod_inv_eq _ hP1, Nat.primeFactors_prod hS,
    Finset.filter_true_of_mem hS]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (hS p hp).one_lt
  have h0 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h1 : (p : ℝ) ≠ 0 := by linarith
  rw [show (1 : ℝ) - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / p by field_simp, inv_div]

/-- **`lem:trivo`, first form, PROVED** (`ternvin.tex` 2764-2799): for `A ≥ 1`, `B ≥ 182`,
`G_q(A) ≤ e^γ(log(A + log q) + 0.65771)/(log B + 1.312) · G_q(AB)`. `eq:bete` and `eq:hosmo` are
`PSieve.trivo_mogan` at `𝒫 = ∏_{p ∣ q ∨ p ≤ ⌊A⌋} p`, `𝒫/φ(𝒫)` is `lem:suspiro` at `m = ⌊A⌋`, and
`G(B) ≥ log B + 1.312` is `eq:charpy`. -/
theorem trivo (su : Suspiro) (cl : HC.CharpyLo) (q : ℕ) (hq : 1 ≤ q) (A B : ℝ) (hA : 1 ≤ A)
    (hB : 182 ≤ B) :
    gQ q A ≤ Real.exp Real.eulerMascheroniConstant * (Real.log (A + Real.log q) + 0.65771) /
      (Real.log B + 1.312) * gQ q (A * B) := by
  obtain ⟨S, hSdef⟩ : ∃ S : Finset ℕ,
      S = (Finset.range (⌊A⌋₊ + q + 1)).filter (fun p => p.Prime ∧ (p ∣ q ∨ p ≤ ⌊A⌋₊)) :=
    ⟨_, rfl⟩
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => by
    rw [hSdef] at hp
    exact (Finset.mem_filter.mp hp).2.1
  have hmem : ∀ p : ℕ, p.Prime → (p ∣ q ∨ p ≤ ⌊A⌋₊) → p ∈ S := by
    intro p hp h
    rw [hSdef, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, hp, h⟩
    rcases h with h | h
    · have := Nat.le_of_dvd (by omega) h
      omega
    · omega
  have hP1 : 1 ≤ ∏ p ∈ S, p :=
    Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun p hp => (hSp p hp).ne_zero)
  have hmo := PSieve.trivo_mogan q (∏ p ∈ S, p) hP1 A B (by linarith)
    (fun p hp hpA => Finset.dvd_prod_of_mem _ (hmem p hp (Or.inr (Nat.le_floor hpA))))
    (fun p hp hpq => Finset.dvd_prod_of_mem _ (hmem p hp (Or.inl hpq)))
  have hw : PSieve.wq (∏ p ∈ S, p) = HC.suspProd ⌊A⌋₊ q := by
    rw [wq_prod S hSp]
    unfold HC.suspProd
    rw [hSdef]
  have hm1 : 1 ≤ ⌊A⌋₊ := Nat.le_floor (by exact_mod_cast hA)
  have hsu := su ⌊A⌋₊ q hm1 hq
  have hfl : (⌊A⌋₊ : ℝ) ≤ A := Nat.floor_le (by linarith)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hm1' : (1 : ℝ) ≤ ⌊A⌋₊ := by exact_mod_cast hm1
  have hlog : Real.log ((⌊A⌋₊ : ℝ) + Real.log q) ≤ Real.log (A + Real.log q) :=
    Real.log_le_log (by linarith) (by linarith)
  have hEg0 := Real.exp_pos Real.eulerMascheroniConstant
  have hbound : PSieve.wq (∏ p ∈ S, p) ≤
      Real.exp Real.eulerMascheroniConstant * (Real.log (A + Real.log q) + 0.65771) := by
    rw [hw]
    exact le_trans hsu (mul_le_mul_of_nonneg_left (by linarith) hEg0.le)
  have hG := cl B hB
  have hlB : 0 < Real.log B := Real.log_pos (by linarith)
  have hwn : 0 ≤ PSieve.wq (∏ p ∈ S, p) := Finset.sum_nonneg fun d _ => PSieve.gt_nonneg d
  have hdiv : PSieve.wq (∏ p ∈ S, p) / gQ 1 B ≤
      Real.exp Real.eulerMascheroniConstant * (Real.log (A + Real.log q) + 0.65771) /
        (Real.log B + 1.312) :=
    div_le_div₀ (le_trans hwn hbound) hbound (by linarith) hG
  exact le_trans hmo (mul_le_mul_of_nonneg_right hdiv (PSieve.gQ_nonneg q _))

/-- **The `lem:paniz` region, re-derived with `prop:espagn`'s denominator, PROVED**: if
`R + log q ≤ c(1.36)·Q₀^τ` (`τ = τ(0.6)`) and `log Q₀ ≤ 0.6 log Q`, the `lem:trivo` bound is at
most `(log Q₀ + 1.36)/(log Q + c_E)`. `e^γ log(c(1.36)Q₀^τ) = 1.36 − 1.36²/5.248 − 1.172 +
0.4 log Q₀` exactly, `0.65771e^γ ≤ 1.172`, and the cross-multiplied polynomial inequality has
margin `0.00637 log Q₀ + 0.4417` (module docstring). -/
theorem paniz_alg (cer : CY.CERange) (Q0 Q R lq : ℝ) (hQ0 : 1 ≤ Q0)
    (hρ : Real.log Q0 ≤ 0.6 * Real.log Q) (hpos : 0 < R + lq)
    (hreg : R + lq ≤ cSig 1.36 * Q0 ^ tauE) :
    Real.exp Real.eulerMascheroniConstant * (Real.log (R + lq) + 0.65771) /
        (Real.log Q - Real.log Q0 + 1.312) ≤
      (Real.log Q0 + 1.36) / (Real.log Q + CY.cE) := by
  have hQ00 : 0 < Q0 := by linarith
  have hl : 0 ≤ Real.log Q0 := Real.log_nonneg hQ0
  have hL : 5 / 3 * Real.log Q0 ≤ Real.log Q := by linarith
  have hc : 0 < cSig 1.36 := Real.exp_pos _
  have hQτ : 0 < Q0 ^ tauE := Real.rpow_pos_of_pos hQ00 _
  have hlog : Real.log (R + lq) ≤ Real.exp (-Real.eulerMascheroniConstant) *
      (1.36 - 1.36 ^ 2 / 5.248 - 1.172) + tauE * Real.log Q0 := by
    have h := Real.log_le_log hpos hreg
    rw [Real.log_mul hc.ne' hQτ.ne', Real.log_rpow hQ00, HC.cSig, Real.log_exp] at h
    exact h
  have heγ : Real.exp Real.eulerMascheroniConstant * Real.exp (-Real.eulerMascheroniConstant) =
      1 := by
    rw [← Real.exp_add]
    simp
  have hEg := expG_le
  have hEg0 := Real.exp_pos Real.eulerMascheroniConstant
  have h1 : Real.exp Real.eulerMascheroniConstant * Real.log (R + lq) ≤
      (1.36 - 1.36 ^ 2 / 5.248 - 1.172) + 0.4 * Real.log Q0 := by
    calc Real.exp Real.eulerMascheroniConstant * Real.log (R + lq)
        ≤ Real.exp Real.eulerMascheroniConstant * (Real.exp (-Real.eulerMascheroniConstant) *
            (1.36 - 1.36 ^ 2 / 5.248 - 1.172) + tauE * Real.log Q0) :=
          mul_le_mul_of_nonneg_left hlog hEg0.le
      _ = (Real.exp Real.eulerMascheroniConstant * Real.exp (-Real.eulerMascheroniConstant)) *
            (1.36 - 1.36 ^ 2 / 5.248 - 1.172) + (Real.exp Real.eulerMascheroniConstant *
              Real.exp (-Real.eulerMascheroniConstant)) * 0.4 * Real.log Q0 := by
          unfold tauE
          ring
      _ = (1.36 - 1.36 ^ 2 / 5.248 - 1.172) + 0.4 * Real.log Q0 := by
          rw [heγ]
          ring
  have hnum : Real.exp Real.eulerMascheroniConstant * (Real.log (R + lq) + 0.65771) ≤
      (1.36 - 1.36 ^ 2 / 5.248) + 0.4 * Real.log Q0 := by
    nlinarith
  have hden : 0 < Real.log Q - Real.log Q0 + 1.312 := by linarith
  have hden2 : 0 < Real.log Q + CY.cE := by linarith [cer.1]
  calc Real.exp Real.eulerMascheroniConstant * (Real.log (R + lq) + 0.65771) /
        (Real.log Q - Real.log Q0 + 1.312)
      ≤ ((1.36 - 1.36 ^ 2 / 5.248) + 0.4 * Real.log Q0) /
          (Real.log Q - Real.log Q0 + 1.312) := div_le_div_of_nonneg_right hnum hden.le
    _ ≤ (Real.log Q0 + 1.36) / (Real.log Q + CY.cE) := by
      rw [div_le_div_iff₀ hden hden2]
      have hA : 0 ≤ Real.log Q0 * (Real.log Q - 5 / 3 * Real.log Q0) :=
        mul_nonneg hl (by linarith)
      have hB : 0 ≤ Real.log Q0 * (1.3325823 - CY.cE) := mul_nonneg hl (by linarith [cer.2])
      nlinarith [cer.2]

/-! ## (2) The error terms: `eq:cante`, `eq:charpy` through `eq:hosmo`; `eq:malito` -/

/-- **Upper bound on `err_{q,R}`** (`ternvin.tex` 2930-2933): `eq:cante` and `eq:hosmo`'s right
half give `err_{q,R} ≤ (φ(q)/q)(log q − ∑_{p∣q} log p/p + (1.4709 − c_E))` for `R ≥ 1`. -/
theorem errE_le (hc : CY.Cante) (q : ℕ) (hq : 1 ≤ q) (R : ℝ) (hR : 1 ≤ R) :
    errE q R ≤ (q.totient : ℝ) / q * (Real.log q - sumLogP q + (1.4709 - CY.cE)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have h1 := PSieve.wq_mul_le q R
  rw [PSieve.wq_eq] at h1
  have h2 := hc ((q : ℝ) * R) (by nlinarith)
  have hlog : Real.log ((q : ℝ) * R) = Real.log q + Real.log R :=
    Real.log_mul hq0.ne' (by linarith)
  have h4 : (q : ℝ) / q.totient * gQ q R ≤ Real.log q + Real.log R + 1.4709 := by
    rw [← hlog]
    linarith
  have e : gQ q R = (q.totient : ℝ) / q * ((q : ℝ) / q.totient * gQ q R) := by
    field_simp
  have h3 : gQ q R ≤ (q.totient : ℝ) / q * (Real.log q + Real.log R + 1.4709) := by
    rw [e]
    exact mul_le_mul_of_nonneg_left h4 (div_nonneg hφ.le hq0.le)
  unfold errE
  linarith

/-- **Lower bound on `err_{q,T}`** (`ternvin.tex` 2934-2936): `eq:charpy` and `eq:hosmo`'s left
half give `err_{q,T} ≥ −(φ(q)/q)(∑_{p∣q} log p/p + (c_E − 1.312))` for `T ≥ 182`. -/
theorem errE_ge (cl : HC.CharpyLo) (q : ℕ) (hq : 1 ≤ q) (T : ℝ) (hT : 182 ≤ T) :
    -((q.totient : ℝ) / q * (sumLogP q + (CY.cE - 1.312))) ≤ errE q T := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have h1 := PSieve.gQ_one_le_wq q hq T
  rw [PSieve.wq_eq] at h1
  have h2 := cl T hT
  have e : gQ q T = (q.totient : ℝ) / q * ((q : ℝ) / q.totient * gQ q T) := by
    field_simp
  have h3 : (q.totient : ℝ) / q * (Real.log T + 1.312) ≤ gQ q T := by
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hφ.le hq0.le)
  unfold errE
  linarith

/-- **`eq:agammen`** (`ternvin.tex` 3003-3005): `|err_{q,R}| ≤ 7.284R^{−1/3}f₁(q)`, `eq:malito`. -/
theorem errE_abs (hm : CY.Malito) (q : ℕ) (hq : 1 ≤ q) (R : ℝ) (hR : 1 ≤ R) :
    |errE q R| ≤ 7.284 * R ^ (-(1 : ℝ) / 3) * CY.f1 q :=
  hm q hq R hR

/-- **The `tR` term** (`ternvin.tex` 3006-3009, 3279-3280): for `X ≥ 1` and `T ≥ 20000X`,
`max(0, −err_{q,T}) ≤ 7.284(20000X)^{−1/3}f₁(q)`. -/
theorem max_errE_le (hm : CY.Malito) (q : ℕ) (hq : 1 ≤ q) (X T : ℝ) (hX : 1 ≤ X)
    (hXT : 20000 * X ≤ T) :
    max 0 (-errE q T) ≤ 7.284 * (20000 * X) ^ (-(1 : ℝ) / 3) * CY.f1 q := by
  have hT1 : 1 ≤ T := by linarith
  have hmal := errE_abs hm q hq T hT1
  have hf := f1_nonneg q
  have h0 : 0 ≤ 7.284 * T ^ (-(1 : ℝ) / 3) * CY.f1 q :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _)) hf
  have h1 : max 0 (-errE q T) ≤ 7.284 * T ^ (-(1 : ℝ) / 3) * CY.f1 q :=
    max_le h0 (le_trans (neg_le_abs _) hmal)
  have h2 : T ^ (-(1 : ℝ) / 3) ≤ (20000 * X) ^ (-(1 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hXT (by norm_num)
  exact le_trans h1 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by norm_num)) hf)

/-! ## (3) `eq:elsyn` → `eq:karka`, and `eq:luce` → `eq:karka` -/

/-- **The algebra of `eq:elsyn` → `eq:karka`** (`ternvin.tex` 2899-2926), with the actual ratio
`B = (l + 1.36)/(L + c)` and `ω = W ≥ B`: from `eq:karka` at `W`, `G_R ≤ B·G_T`. Here
`G_R = u(l − a + c + S) + e₁`, `G_T = u(L − a + c + S) + e₂`, `a = log sq`, `S = ∑ log p/p`. -/
theorem karka_alg (u l L a S c B W e1 e2 GR GT : ℝ) (hu : 0 < u)
    (hGR : GR = u * (l - a + c + S) + e1) (hGT : GT = u * (L - a + c + S) + e2)
    (hB : B * (L + c) = l + 1.36) (hB0 : 0 ≤ B) (hBW : B ≤ W) (haS : 0 ≤ a - S)
    (hk : e1 + W * max 0 (-e2) ≤ u * ((1 - W) * (a - S) + (1.36 - c))) : GR ≤ B * GT := by
  have hm0 : 0 ≤ max 0 (-e2) := le_max_left _ _
  have hm1 : -e2 ≤ max 0 (-e2) := le_max_right _ _
  have h1 : 0 ≤ u * (W - B) * (a - S) := mul_nonneg (mul_nonneg hu.le (by linarith)) haS
  have h2 : 0 ≤ B * (e2 + max 0 (-e2)) := mul_nonneg hB0 (by linarith)
  have h3 : 0 ≤ (W - B) * max 0 (-e2) := mul_nonneg (by linarith) hm0
  have hB' : u * (B * (L + c)) = u * (l + 1.36) := by rw [hB]
  subst hGR hGT
  nlinarith

/-- **`eq:martinos` from `eq:karka` at `ω(0.6)`, PROVED**: the ratio bound follows once
`err_R + ω max(0, −err_T) ≤ (φ/q)((1 − ω)(log sq − ∑ log p/p) + c_Δ)`, given `B ≤ ω(0.6)`. -/
theorem ratio_le (q : ℕ) (hq : 1 ≤ q) (Q0 Q s : ℝ) (hQ0 : 0 < Q0) (hQ : 0 < Q) (hs : 1 ≤ s)
    (hG : 0 < gQ q (Q / (s * q))) (hL : 0 < Real.log Q + CY.cE)
    (hB0 : 0 ≤ (Real.log Q0 + 1.36) / (Real.log Q + CY.cE))
    (hBW : (Real.log Q0 + 1.36) / (Real.log Q + CY.cE) ≤ omegaE)
    (hS : sumLogP q ≤ Real.log q)
    (hk : errE q (Q0 / (s * q)) + omegaE * max 0 (-errE q (Q / (s * q))) ≤
      (q.totient : ℝ) / q * ((1 - omegaE) * (Real.log (s * q) - sumLogP q) + cDeltaE)) :
    gQ q (Q0 / (s * q)) / gQ q (Q / (s * q)) ≤ (Real.log Q0 + 1.36) / (Real.log Q + CY.cE) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hsq : 0 < s * q := by positivity
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  rw [div_le_iff₀ hG]
  have hlR : Real.log (Q0 / (s * q)) = Real.log Q0 - Real.log (s * q) :=
    Real.log_div hQ0.ne' hsq.ne'
  have hlT : Real.log (Q / (s * q)) = Real.log Q - Real.log (s * q) :=
    Real.log_div hQ.ne' hsq.ne'
  have haS : 0 ≤ Real.log (s * q) - sumLogP q := by
    have : Real.log q ≤ Real.log (s * q) := Real.log_le_log hq0 (by nlinarith)
    linarith
  have hB : (Real.log Q0 + 1.36) / (Real.log Q + CY.cE) * (Real.log Q + CY.cE) =
      Real.log Q0 + 1.36 := div_mul_cancel₀ _ hL.ne'
  refine karka_alg ((q.totient : ℝ) / q) (Real.log Q0) (Real.log Q) (Real.log (s * q))
    (sumLogP q) CY.cE _ omegaE (errE q (Q0 / (s * q))) (errE q (Q / (s * q))) _ _
    (div_pos hφ hq0) ?_ ?_ hB hB0 hBW haS ?_
  · unfold errE
    rw [hlR]
    ring
  · unfold errE
    rw [hlT]
    ring
  · unfold cDeltaE at hk
    exact hk

/-- **`B ≤ ω(0.6)`** (`ternvin.tex` 2914-2919): `(log Q₀ + 1.36)/(log Q + c_E)` is at most
`ω(0.6) = (log 10⁵ + 1.36)/(log 10⁵/0.6 + c_E)` when `Q₀ ≥ 10⁵`, `log Q₀ ≤ 0.6 log Q`. -/
theorem ratio_le_omega (cer : CY.CERange) (Q0 Q : ℝ) (hQ0 : 100000 ≤ Q0) (hQ : 1 < Q)
    (hρ : Real.log Q0 ≤ 0.6 * Real.log Q) :
    (Real.log Q0 + 1.36) / (Real.log Q + CY.cE) ≤ omegaE := by
  have hl0 : Real.log 100000 ≤ Real.log Q0 := Real.log_le_log (by norm_num) hQ0
  have h1 := logQ0_gt
  have hLQ := Real.log_pos hQ
  have hc1 := cer.1
  have hc2 := cer.2
  rw [omegaE_eq, div_le_div_iff₀ (by linarith) (by linarith)]
  have ha : 0 ≤ (Real.log 100000 + 1.36) * (Real.log Q - 5 / 3 * Real.log Q0) :=
    mul_nonneg (by linarith) (by linarith)
  have hb : 0 ≤ (Real.log Q0 - Real.log 100000) * (1.36 * (5 / 3) - CY.cE) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- **`eq:luce`** at `(q, R, T)`: `err_{q,R} + ω(0.6)·max(0, −err_{q,T}) ≤ (φ(q)/q)κ(q)`. -/
def Luce (q : ℕ) (R T : ℝ) : Prop :=
  errE q R + omegaE * max 0 (-errE q T) ≤ (q.totient : ℝ) / q * kappaE q

/-- **`eq:luce` → `eq:karka`** (`ternvin.tex` 2989-2997): `κ(q)` drops `(1 − ω) log s ≥ 0`. -/
theorem karka_of_luce (cer : CY.CERange) (q : ℕ) (hq : 1 ≤ q) (s R T : ℝ) (hs : 1 ≤ s)
    (h : Luce q R T) :
    errE q R + omegaE * max 0 (-errE q T) ≤
      (q.totient : ℝ) / q * ((1 - omegaE) * (Real.log (s * q) - sumLogP q) + cDeltaE) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have h1 : Real.log q ≤ Real.log (s * q) := Real.log_le_log hq0 (by nlinarith)
  have hW := omegaE_lt_one cer
  have hle : kappaE q ≤ (1 - omegaE) * (Real.log (s * q) - sumLogP q) + cDeltaE := by
    unfold kappaE
    have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 - omegaE)
    nlinarith
  exact le_trans h (mul_le_mul_of_nonneg_left hle (div_nonneg hφ.le hq0.le))

/-! ## (4) `R > ϖ(q)`: `eq:koklo`, `eq:joho` iterated -/

/-- **The iteration behind `ϖ₀`** (`ternvin.tex` 2963-2984): if `A R^τ < R + ℓ`, `R ≥ 1`,
`ℓ ≥ 0`, `0 < τ < 1` and `A > ℓ + 1`, then `R > (A − ℓ/(A − ℓ)^{τ/(1−τ)})^{1/(1−τ)}`. -/
theorem iter_lt (A lq τ R : ℝ) (hlq : 0 ≤ lq) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hR : 1 ≤ R)
    (hA : lq + 1 < A) (hj : A * R ^ τ < R + lq) :
    (A - lq / (A - lq) ^ (τ / (1 - τ))) ^ (1 / (1 - τ)) < R := by
  have hR0 : 0 < R := by linarith
  have hRτ : 1 ≤ R ^ τ := Real.one_le_rpow hR hτ0.le
  have hRτ0 : 0 < R ^ τ := by linarith
  have h1τ : 0 < 1 - τ := by linarith
  have hsplit : R ^ (1 - τ) = R / R ^ τ := by rw [Real.rpow_sub hR0, Real.rpow_one]
  have hback : ∀ z : ℝ, 0 ≤ z → z < R ^ (1 - τ) → z ^ (1 / (1 - τ)) < R := by
    intro z hz hzR
    have h := Real.rpow_lt_rpow hz hzR (by positivity : (0 : ℝ) < 1 / (1 - τ))
    rwa [← Real.rpow_mul hR0.le, mul_one_div_cancel h1τ.ne', Real.rpow_one] at h
  have hA' : A < R / R ^ τ + lq / R ^ τ := by
    rw [← add_div, lt_div_iff₀ hRτ0]
    linarith
  have hstep : ∀ D : ℝ, 0 < D → D ≤ R ^ τ → A - lq / D < R ^ (1 - τ) := by
    intro D hD hDR
    have := div_le_div_of_nonneg_left hlq hD hDR
    rw [hsplit]
    linarith
  -- first pass: `R > R₁ = (A − ℓ)^{1/(1−τ)}`
  have hR1 : (A - lq) ^ (1 / (1 - τ)) < R := by
    refine hback _ (by linarith) ?_
    have := hstep 1 one_pos hRτ
    rwa [div_one] at this
  -- second pass
  have hD1 : 1 ≤ (A - lq) ^ (τ / (1 - τ)) :=
    Real.one_le_rpow (by linarith) (div_nonneg hτ0.le h1τ.le)
  have hDR : (A - lq) ^ (τ / (1 - τ)) ≤ R ^ τ := by
    have e : (A - lq) ^ (τ / (1 - τ)) = ((A - lq) ^ (1 / (1 - τ))) ^ τ := by
      rw [← Real.rpow_mul (by linarith)]
      congr 1
      field_simp
    rw [e]
    exact Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hR1.le hτ0.le
  have hz : 0 ≤ A - lq / (A - lq) ^ (τ / (1 - τ)) := by
    have := div_le_self hlq hD1
    linarith
  exact hback _ hz (hstep _ (by linarith) hDR)

/-- **`R > ϖ₀(q)` from `eq:joho`** (`ternvin.tex` 2957-2984), `ρ = 0.6`. -/
theorem varpi0_lt (q : ℕ) (hq : 1 ≤ q) (R : ℝ) (hR : 1 ≤ R)
    (hj : cSig 1.36 * (q : ℝ) ^ tauE * R ^ tauE < R + Real.log q) : varpi0 q < R := by
  unfold varpi0
  split_ifs with h
  · exact iter_lt _ _ _ R (Real.log_nonneg (by exact_mod_cast hq)) tauE_pos tauE_lt_one hR h hj
  · linarith

/-- **`R > ϖ(q)`, PROVED** (`eq:armor`, `ternvin.tex` 2946-2984): outside the `lem:paniz` region
(`R + log q > c(1.36)Q₀^τ`) and outside `eq:miasmar`, `R = Q₀/sq` exceeds all three terms of
`ϖ(q)`: `ϖ₀(q)` by the iteration (`Q₀ ≥ qR`), `c(1.36)·10^{5τ} − log q` since `Q₀ ≥ 10⁵`, and
`10⁵/(c_{ρ,2}q)^{1/(1−ω)}` by `eq:koklo`. -/
theorem varpiE_lt (cer : CY.CERange) (q : ℕ) (hq : 1 ≤ q) (Q0 s : ℝ) (hQ0 : 100000 ≤ Q0)
    (hs : 1 ≤ s) (hR1 : 1 ≤ Q0 / (s * q))
    (hnp : cSig 1.36 * Q0 ^ tauE < Q0 / (s * q) + Real.log q)
    (hnm : (1 - omegaE) * Real.log (s * q) <
      Real.log q + (1.4709 - CY.cE) + omegaE * (CY.cE - 1.312) - cDeltaE) :
    varpiE q < Q0 / (s * q) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hsq : 0 < s * q := by positivity
  have hτ0 := tauE_pos
  have hc0 : 0 < cSig 1.36 := Real.exp_pos _
  unfold varpiE
  refine max_lt ?_ (max_lt ?_ ?_)
  · apply varpi0_lt q hq _ hR1
    have hqR : (q : ℝ) * (Q0 / (s * q)) ≤ Q0 := by
      rw [show (q : ℝ) * (Q0 / (s * q)) = Q0 / s by field_simp]
      exact div_le_self (by linarith) hs
    have hmono : ((q : ℝ) * (Q0 / (s * q))) ^ tauE ≤ Q0 ^ tauE :=
      Real.rpow_le_rpow (by positivity) hqR hτ0.le
    rw [Real.mul_rpow hq0.le (by linarith)] at hmono
    calc cSig 1.36 * (q : ℝ) ^ tauE * (Q0 / (s * q)) ^ tauE
        = cSig 1.36 * ((q : ℝ) ^ tauE * (Q0 / (s * q)) ^ tauE) := by ring
      _ ≤ cSig 1.36 * Q0 ^ tauE := mul_le_mul_of_nonneg_left hmono hc0.le
      _ < Q0 / (s * q) + Real.log q := hnp
  · have h1 : (100000 : ℝ) ^ tauE ≤ Q0 ^ tauE := Real.rpow_le_rpow (by norm_num) hQ0 hτ0.le
    have h2 := mul_le_mul_of_nonneg_left h1 hc0.le
    linarith
  · have hW1 := omegaE_lt_one cer
    have h1W : 0 < 1 - omegaE := by linarith
    have hc2 : 0 < cRho2 := Real.exp_pos _
    have hc2q : 0 < cRho2 * q := by positivity
    have hlog : Real.log (s * q) < Real.log (cRho2 * q) / (1 - omegaE) := by
      rw [lt_div_iff₀ h1W, Real.log_mul hc2.ne' hq0.ne']
      unfold cRho2
      rw [Real.log_exp]
      linarith
    have hsq_lt : s * q < (cRho2 * q) ^ (1 / (1 - omegaE)) := by
      rw [Real.rpow_def_of_pos hc2q]
      calc s * q = Real.exp (Real.log (s * q)) := (Real.exp_log hsq).symm
        _ < Real.exp (Real.log (cRho2 * q) * (1 / (1 - omegaE))) := by
          apply Real.exp_lt_exp.mpr
          rw [mul_one_div]
          exact hlog
    have hpos : 0 < (cRho2 * q) ^ (1 / (1 - omegaE)) := Real.rpow_pos_of_pos hc2q _
    calc 100000 / (cRho2 * q) ^ (1 / (1 - omegaE))
        ≤ Q0 / (cRho2 * q) ^ (1 / (1 - omegaE)) := div_le_div_of_nonneg_right hQ0 hpos.le
      _ < Q0 / (s * q) := div_lt_div_of_pos_left (by linarith) hsq hsq_lt

/-! ## (5) `eq:luce` on `R > ϖ(q)`: three ranges -/

/-- **`eq:luce` for `R ≥ λ(q)`, PROVED** (`eq:agammen`, `eq:sosor`, `ternvin.tex` 3003-3015):
`err_R + ω max(0, −err_T) ≤ 7.284(1 + β)f₁R^{−1/3} ≤ (φ/q)κ` once
`R^{1/3} ≥ (q/φ)·7.284(1+β)f₁/κ`. -/
theorem luce_big (hm : CY.Malito) (cer : CY.CERange) (q : ℕ) (hq : 1 ≤ q) (R T : ℝ)
    (hR : 1 ≤ R) (hT : 20000 * R ≤ T) (hlam : lambdaE q ≤ R) : Luce q R T := by
  unfold Luce
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hu : (0 : ℝ) < (q.totient : ℝ) / q := div_pos hφ hq0
  have hκ := kappaE_pos cer q hq
  have hW0 := (omegaE_pos cer).le
  have hf := f1_nonneg q
  have hR0 : 0 < R := by linarith
  have hy0 : 0 < R ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hR0 _
  have hy3 : (R ^ ((1 : ℝ) / 3)) ^ 3 = R := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR0.le]
    norm_num
  have hRm : R ^ (-(1 : ℝ) / 3) = (R ^ ((1 : ℝ) / 3))⁻¹ := by
    rw [show (-(1 : ℝ) / 3) = -((1 : ℝ) / 3) by ring, Real.rpow_neg hR0.le]
  have h20 : (20000 : ℝ) ^ (-(1 : ℝ) / 3) = ((20000 : ℝ) ^ ((1 : ℝ) / 3))⁻¹ := by
    rw [show (-(1 : ℝ) / 3) = -((1 : ℝ) / 3) by ring, Real.rpow_neg (by norm_num)]
  have hβ0 : 0 ≤ betaE := div_nonneg hW0 (Real.rpow_nonneg (by norm_num) _)
  have hC0 : 0 ≤ (q : ℝ) / q.totient * (7.284 * (1 + betaE) * CY.f1 q / kappaE q) := by
    have : 0 ≤ 7.284 * (1 + betaE) * CY.f1 q := by positivity
    positivity
  have hCy : (q : ℝ) / q.totient * (7.284 * (1 + betaE) * CY.f1 q / kappaE q) ≤
      R ^ ((1 : ℝ) / 3) := by
    refine (pow_le_pow_iff_left₀ hC0 hy0.le (by norm_num : (3 : ℕ) ≠ 0)).mp ?_
    rw [hy3]
    exact hlam
  have hD : 7.284 * (1 + betaE) * CY.f1 q ≤
      R ^ ((1 : ℝ) / 3) * ((q.totient : ℝ) / q * kappaE q) := by
    have e : (q : ℝ) / q.totient * (7.284 * (1 + betaE) * CY.f1 q / kappaE q) =
        7.284 * (1 + betaE) * CY.f1 q / ((q.totient : ℝ) / q * kappaE q) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)] at hCy
    linarith
  have h1 : errE q R ≤ 7.284 * (R ^ ((1 : ℝ) / 3))⁻¹ * CY.f1 q := by
    have := (abs_le.mp (errE_abs hm q hq R hR)).2
    rwa [hRm] at this
  have h2 := max_errE_le hm q hq R T hR hT
  rw [Real.mul_rpow (by norm_num) hR0.le, h20, hRm] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 hW0
  have hLHS : errE q R + omegaE * max 0 (-errE q T) ≤
      7.284 * (1 + betaE) * CY.f1 q * (R ^ ((1 : ℝ) / 3))⁻¹ := by
    unfold betaE
    have e : 7.284 * (1 + omegaE / (20000 : ℝ) ^ ((1 : ℝ) / 3)) * CY.f1 q *
        (R ^ ((1 : ℝ) / 3))⁻¹ = 7.284 * (R ^ ((1 : ℝ) / 3))⁻¹ * CY.f1 q + omegaE *
          (7.284 * (((20000 : ℝ) ^ ((1 : ℝ) / 3))⁻¹ * (R ^ ((1 : ℝ) / 3))⁻¹) * CY.f1 q) := by
      ring
    rw [e]
    linarith
  calc errE q R + omegaE * max 0 (-errE q T)
      ≤ 7.284 * (1 + betaE) * CY.f1 q * (R ^ ((1 : ℝ) / 3))⁻¹ := hLHS
    _ ≤ (q.totient : ℝ) / q * kappaE q := by
      rw [← div_eq_mul_inv, div_le_iff₀ hy0]
      linarith

/-- **`eq:luce` for `ϖ(q) ≤ ⌊R⌋ < λ(q)`, PROVED from the cited check** (`ternvin.tex` 3273-3287):
`G_q(R) = G_q(⌊R⌋)` and `log R ≥ log ⌊R⌋` give `err_{q,R} ≤ err_{q,⌊R⌋}`; the `tR` term is
bounded by `eq:agammen` at `20000⌊R⌋ ≤ T`. -/
theorem luce_check (hm : CY.Malito) (cer : CY.CERange) (chk : HC.EspagnCheckCited) (q : ℕ)
    (hq : 1 ≤ q) (hr : (q : ℝ) < 3.3e9 ∨ ((q : ℝ) < 2.2e10 ∧ 210 ∣ q)) (R T : ℝ) (hR : 1 ≤ R)
    (hT : 20000 * R ≤ T) (hv : varpiE q ≤ ⌊R⌋₊) (hlam : R < lambdaE q) : Luce q R T := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hn1 : 1 ≤ ⌊R⌋₊ := Nat.le_floor (by exact_mod_cast hR)
  have hn1' : (1 : ℝ) ≤ ⌊R⌋₊ := by exact_mod_cast hn1
  have hnR : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le (by linarith)
  have hc := chk q hq hr ⌊R⌋₊ hv (lt_of_le_of_lt hnR hlam)
  have hG : gQ q R = gQ q (⌊R⌋₊ : ℝ) := by
    unfold PSieve.gQ
    rw [Nat.floor_natCast]
  have hlog : Real.log (⌊R⌋₊ : ℝ) ≤ Real.log R := Real.log_le_log (by linarith) hnR
  have he : errE q R ≤ errE q (⌊R⌋₊ : ℝ) := by
    unfold errE
    rw [hG]
    have := mul_le_mul_of_nonneg_left hlog (div_nonneg hφ.le hq0.le)
    nlinarith
  have hmx := max_errE_le hm q hq (⌊R⌋₊ : ℝ) T hn1' (by linarith)
  have hW0 := (omegaE_pos cer).le
  have h3 := mul_le_mul_of_nonneg_left hmx hW0
  unfold Luce
  linarith

/-- **NAMED — THE HOLE: the cited check at the real point `R = ϖ(q)`** (`ternvin.tex` 3282-3286;
module docstring). For every checked `q` with `ϖ(q)` NOT an integer and `1 < ϖ(q) < λ(q)`:
`err_{q,ϖ(q)} + ω·7.284(20000ϖ(q))^{−1/3}f₁(q) ≤ (φ(q)/q)κ(q)`, where
`err_{q,ϖ} = G_q(⌊ϖ⌋) − (φ/q)(log ϖ + c_E + ∑ log p/p)`. It is `HC.EspagnCheckCited`'s inequality
at one extra, non-integer `R` per `q` — the supremum of `eq:luce` over the partial step
`(ϖ, ⌈ϖ⌉)` that "it is enough to check integer values of `R`" misses. (An integer `ϖ` is inside
the cited range, and `ϖ ≤ 1` is never needed since `R ≥ 1` (`ϖ(q) = 0.405` at `q = 1.2·10⁵`);
both are excluded, so nothing is asked beyond the hole.) A computation nobody ran; float64-true
with margin `≥ 0.0234` on `297 419` moduli (`scratchpad/hcite/edge_num.py`). -/
def EspagnEdge : Prop :=
  ∀ q : ℕ, 1 ≤ q → ((q : ℝ) < 3.3e9 ∨ ((q : ℝ) < 2.2e10 ∧ 210 ∣ q)) →
    (⌊varpiE q⌋₊ : ℝ) < varpiE q → 1 < varpiE q → varpiE q < lambdaE q →
      errE q (varpiE q) + omegaE * (7.284 * (20000 * varpiE q) ^ (-(1 : ℝ) / 3) * CY.f1 q) ≤
        (q.totient : ℝ) / q * kappaE q

/-- **`eq:luce` on the partial step `ϖ(q) < R < ⌈ϖ(q)⌉`, PROVED from `EspagnEdge`**: `⌊R⌋ = ⌊ϖ⌋`,
so `G_q(R) = G_q(ϖ)`, and `log R ≥ log ϖ`, `(20000R)^{−1/3} ≤ (20000ϖ)^{−1/3}`. -/
theorem luce_edge (hm : CY.Malito) (cer : CY.CERange) (ed : EspagnEdge) (q : ℕ) (hq : 1 ≤ q)
    (hr : (q : ℝ) < 3.3e9 ∨ ((q : ℝ) < 2.2e10 ∧ 210 ∣ q)) (R T : ℝ) (hR : 1 ≤ R)
    (hT : 20000 * R ≤ T) (hvR : varpiE q < R) (hv : ¬varpiE q ≤ ⌊R⌋₊) (hlam : R < lambdaE q) :
    Luce q R T := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hfl1 : (⌊R⌋₊ : ℝ) < varpiE q := lt_of_not_ge hv
  have hn1 : 1 ≤ ⌊R⌋₊ := Nat.le_floor (by exact_mod_cast hR)
  have hn1' : (1 : ℝ) ≤ ⌊R⌋₊ := by exact_mod_cast hn1
  have hv1 : 1 < varpiE q := by linarith
  have hfl : ⌊varpiE q⌋₊ = ⌊R⌋₊ := le_antisymm (Nat.floor_le_floor hvR.le) (Nat.le_floor hfl1.le)
  have hG : gQ q R = gQ q (varpiE q) := by
    unfold PSieve.gQ
    rw [hfl]
  have hni : (⌊varpiE q⌋₊ : ℝ) < varpiE q := by
    rw [hfl]
    exact hfl1
  have hc := ed q hq hr hni hv1 (lt_trans hvR hlam)
  have hlog : Real.log (varpiE q) ≤ Real.log R := Real.log_le_log (by linarith) hvR.le
  have he : errE q R ≤ errE q (varpiE q) := by
    unfold errE
    rw [hG]
    have := mul_le_mul_of_nonneg_left hlog (div_nonneg hφ.le hq0.le)
    nlinarith
  have hmx := max_errE_le hm q hq (varpiE q) T hv1.le (by linarith)
  have hW0 := (omegaE_pos cer).le
  have h3 := mul_le_mul_of_nonneg_left hmx hW0
  unfold Luce
  linarith

/-- **NAMED — `ϖ(q) ≥ λ(q)` outside the checked range** (`ternvin.tex` 3025-3211: `eq:modo`,
`eq:hipo`, `eq:victo`, `eq:drolo`, `eq:mutuso`, and the `210 ∤ q` variant `eq:modowo`,
`eq:hipowo`): for `q ≥ 3.3·10⁹` with `210 ∤ q`, and for `q ≥ 2.2·10¹⁰`. From `CY.CERange`, the cited
`HC.EspagnSmallCited` pieces (`ProdSmallCited`, `LogSumCited`, `LogSumTenKCited`, `F1ProdCited`,
`ThetaSmallCited`, `EspagnEvalCited`) and Rosser–Schoenfeld 1962 (3.16), (3.24), (3.30), (3.32),
cited PROOFS (an owner question). Helfgott proves strict `>`; `≥` is what is consumed. Two
harmless slips inside, recorded in `HC.EspagnRed`'s docstring. -/
def EspagnLargeQ : Prop :=
  CY.CERange → HC.EspagnSmallCited → ∀ q : ℕ, 1 ≤ q →
    ¬((q : ℝ) < 3.3e9 ∨ ((q : ℝ) < 2.2e10 ∧ 210 ∣ q)) → lambdaE q ≤ varpiE q

/-! ## (6) The composition -/

/-- **`prop:espagn` from its links, PROVED by case analysis** — the five cases of the module
docstring, each closed by a proved link or by a named one (`Suspiro`, `EspagnEdge`, the large-`q`
fact). -/
theorem espagn_of_links (cer : CY.CERange) (hm : CY.Malito) (hc : CY.Cante) (cl : HC.CharpyLo)
    (su : Suspiro) (chk : HC.EspagnCheckCited) (ed : EspagnEdge)
    (lq : ∀ q : ℕ, 1 ≤ q → ¬((q : ℝ) < 3.3e9 ∨ ((q : ℝ) < 2.2e10 ∧ 210 ∣ q)) →
      lambdaE q ≤ varpiE q) :
    CY.Espagn := by
  intro Q0 Q h0 h1 h2 q hq1 hq2 s hs1 hs2
  have hQ0 : (0 : ℝ) < Q0 := by linarith
  have hQ : 1 < Q := by nlinarith
  have hLQ : 0 < Real.log Q := Real.log_pos hQ
  have hρ : Real.log Q0 ≤ 0.6 * Real.log Q := by rwa [div_le_iff₀ hLQ] at h2
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hsq : 0 < s * q := by positivity
  have hsqQ0 : s * q ≤ Q0 := by
    rw [le_div_iff₀ hq0] at hs2
    exact hs2
  have hR1 : 1 ≤ Q0 / (s * q) := by
    rw [le_div_iff₀ hsq]
    linarith
  have hT : Q / (s * q) = Q0 / (s * q) * (Q / Q0) := by
    field_simp
  have hTR : 20000 * (Q0 / (s * q)) ≤ Q / (s * q) := by
    have := div_le_div_of_nonneg_right h1 hsq.le
    rwa [mul_div_assoc] at this
  have hT1 : 1 ≤ Q / (s * q) := by linarith
  have hGT : 0 < gQ q (Q / (s * q)) := lt_of_lt_of_le one_pos (PSieve.one_le_gQ q _ hT1)
  have hL : 0 < Real.log Q + CY.cE := by linarith [cer.1]
  have hl0 : 0 ≤ Real.log Q0 := Real.log_nonneg (by linarith)
  have hB0 : 0 ≤ (Real.log Q0 + 1.36) / (Real.log Q + CY.cE) :=
    div_nonneg (by linarith) hL.le
  have hBW := ratio_le_omega cer Q0 Q h0 hQ hρ
  have hS := sumLogP_le q hq1
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq1)
  have hkar := fun hk => ratio_le q hq1 Q0 Q s hQ0 (by linarith) hs1 hGT hL hB0 hBW hS hk
  by_cases hpan : Q0 / (s * q) + Real.log q ≤ cSig 1.36 * Q0 ^ tauE
  · -- (i) the `lem:paniz` region: `lem:trivo` and `paniz_alg`
    have hQQ0 : 182 ≤ Q / Q0 := by
      rw [le_div_iff₀ hQ0]
      linarith
    have htr := trivo su cl q hq1 (Q0 / (s * q)) (Q / Q0) hR1 hQQ0
    rw [← hT, Real.log_div (by linarith) hQ0.ne'] at htr
    have hpa := paniz_alg cer Q0 Q (Q0 / (s * q)) (Real.log q) (by linarith) hρ (by linarith) hpan
    rw [div_le_iff₀ hGT]
    exact le_trans htr (mul_le_mul_of_nonneg_right hpa hGT.le)
  · replace hpan := not_le.mp hpan
    by_cases hmia : Real.log q + (1.4709 - CY.cE) + omegaE * (CY.cE - 1.312) - cDeltaE ≤
        (1 - omegaE) * Real.log (s * q)
    · -- (ii) `eq:miasmar`: the easy error bounds
      apply hkar
      have e1 := errE_le hc q hq1 _ hR1
      have e2 := errE_ge cl q hq1 _ (by linarith : (182 : ℝ) ≤ Q / (s * q))
      have hW0 := (omegaE_pos cer).le
      have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
      have hu : (0 : ℝ) ≤ (q.totient : ℝ) / q := div_nonneg hφ.le hq0.le
      have hSn := sumLogP_nonneg q
      have hmx : max 0 (-errE q (Q / (s * q))) ≤
          (q.totient : ℝ) / q * (sumLogP q + (CY.cE - 1.312)) :=
        max_le (mul_nonneg hu (by linarith [cer.1])) (by linarith)
      have h3 := mul_le_mul_of_nonneg_left hmx hW0
      have h4 := mul_le_mul_of_nonneg_left hmia hu
      nlinarith
    · -- (iii) `R > ϖ(q)`
      replace hmia := not_le.mp hmia
      have hv := varpiE_lt cer q hq1 Q0 s h0 hs1 hR1 hpan hmia
      apply hkar
      apply karka_of_luce cer q hq1 s _ _ hs1
      by_cases hlam : lambdaE q ≤ Q0 / (s * q)
      · exact luce_big hm cer q hq1 _ _ hR1 hTR hlam
      · replace hlam := not_le.mp hlam
        by_cases hr : (q : ℝ) < 3.3e9 ∨ ((q : ℝ) < 2.2e10 ∧ 210 ∣ q)
        · by_cases hvf : varpiE q ≤ ⌊Q0 / (s * q)⌋₊
          · exact luce_check hm cer chk q hq1 hr _ _ hR1 hTR hvf hlam
          · exact luce_edge hm cer ed q hq1 hr _ _ hR1 hTR hv hvf hlam
        · exact absurd (lt_of_le_of_lt (lq q hq1 hr) hv) (not_lt.mpr hlam.le)

/-- **`HC.EspagnRed` from its three named links, PROVED** (application only): `lem:suspiro` from
the cited small range and `SuspiroBig`, the large-`q` fact from `EspagnLargeQ`. -/
theorem espagnRed_of_links (sb : SuspiroBig) (ed : EspagnEdge) (lq : EspagnLargeQ) :
    HC.EspagnRed := fun cer hm hc cl sm chk =>
  espagn_of_links cer hm hc cl (suspiro_of sm.1 sb) chk ed (lq cer sm)

/-- **`CY.EspagnWin 1.36` with `EspagnRed` and `CharpyGap` gone**: the cited checks, `eq:charpas`
(cited), the literature and the three named links. -/
theorem espagnWin_of_wrap (sb : SuspiroBig) (ed : EspagnEdge) (lq : EspagnLargeQ)
    (cer : CY.CERange) (hm : CY.Malito) (hc : CY.Cante) (ch : HC.CharpyCited)
    (cp : CharpasCited) (sm : HC.EspagnSmallCited) (chk : HC.EspagnCheckCited) :
    CY.EspagnWin 1.36 :=
  HC.espagnWin_of_cited (espagnRed_of_links sb ed lq) cer hm hc ch (charpyGap_of_charpas cp) sm chk

end Principia.Common.TernaryGoldbach.HX
