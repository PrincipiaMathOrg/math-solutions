/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.DrujalSum
import Principia.Common.TernaryGoldbach.MinorW
import Principia.Common.TernaryGoldbach.MajorB27W
import Principia.Common.TernaryGoldbach.BandSharp

set_option autoImplicit false

/-!
# THE SPINE OF `lem:drujal`: both halves split into links that COMPOSE

`EN.DrujalE` (upper half, `A ≤ 10`) and `MinW.DrujalLowE` (lower half, `J/x ≥ 8.613`) were two
monolithic links. Per the SPINE RULE this file writes Helfgott's proof of `lem:drujal`
(`ternvin.tex` 1222–1410, statement 1412–1453) as named steps, and composes them — by application
and exact arithmetic only — into `DrujalE100` (cap `100`) and `DrujalLowD` (`J/x ≥ 8.36`).

## The spine

```
 PerArc (1233–1270): per q, per δ,
     |Σ_a |S(a/q+δ/x)|² − μ²(q)/φ(q)·x²|η̂(−δ)|²|
       ≤ μ²/φ·x²·ET(2|η|₁+ET) + E²x² + φ(q)·B_q·(2Σ_n Λ(n)|η(n/x)| + B_q)
 ArcInt (1272–1315) ─► juto : |A_η(x) − L_{r,δ₀}| ≤ etAgg + eAgg + kAgg      (eq:juto/bfpink)
     etAgg = δ₀r·nagS·ET(2|η|₁+ET),  eAgg = δ₀r·harmS·E²,  KSmall ─► kAgg ≤ 10⁻⁶
 lRD_eq (1359–1365, PROVED): L_{r,δ₀} = 2Σ_{q≤r odd} μ²(q)/φ(q)·I_q,
     I_q = ∫_{−δ₀r/2q}^{δ₀r/2q} |η̂|²
 UPPER  MardiQ (1316–1332): I_q ≤ |η|₂²          ⇒ L ≤ 2|η|₂²·S                  (eq:mardi)
 LOWER  BandQ  (1335–1358): I_q(η) ≥ I_q(η∘) − (2|η∘|₂|η−η∘|₂ + |η−η∘|₂²)
        TailQ  (1366–1374): I_q(η∘) ≥ |η∘|₂² − |η∘'''|₁²/(160π⁶w⁵)
            ⇒ L ≥ 2S·(|η∘|₂² − band − |η∘'''|₁²/(163840π⁶))
 ARITHMETIC (DrujalSum, PROVED): 6.5942 ≤ S ≤ 48.44, nagS ≤ 3.125, harmS ≤ 25.84
```

**Links (OPEN) and what each transcribes.** `PerArc` is `eq:beatit` + orthogonality + the Gauss sums
(generic, TRUE for every weight whose `Σ Λ(n)|η(n/x)|` converges). `ArcInt` is the integration over
the disjoint arcs (generic measure theory). `MardiQ`, `BandQ`, `TailQ` are Plancherel (+ Cauchy–
Schwarz, + `eq:madge`), stated as facts about the given weights. `KSmall` bounds the aggregate of
the non-coprime prime powers. Each link is met by something real — `PerArc`, `MardiQ`, `TailQ`,
`KSmall` by the zero weight (`spine_zero`), `ArcInt` too (`arcInt_zero`), `BandQ η η` by EVERY
weight (`bandQ_self`) — and together the links REJECT a junk weight (`spine_rejects_junk`).

## Deviations from the printed argument, each checked against the source

1. **The `K` term is transcribed from 1241, not 1243.** Line 1243 replaces `max_α |S_η(α,x)|` by
   `|S_η(0,x)|`, which needs `η ≥ 0`; `η₊ = h₂₀₀(t)te^{−t²/2}` is not known to be nonnegative. And
   `K_{q,1} = (1+√q)(log x)²|η|_∞` bounds `eq:beatit`'s error `2Σ_{p|q}log p Σ_α|η(p^α/x)|` only for
   weights supported in `[0,1]` (the commented-out 916–917 assume `p^α ≤ x`). So `PerArc` carries
   the error EXACTLY (`bQ`, with `|η|`), the cross term through `Σ_n Λ(n)|η(n/x)|` (`sAbs`), and a
   factor `φ(q)` for the sum over `a` — which 1240 drops. The whole term is `≈ 10⁻¹³` either way;
   `KSmall` asks for `≤ 10⁻⁶`.
2. **`E` weighted by `√q*`** (MajSp correction 1): `PerArc`'s `E²x²` is
   `(1/φ(q))Σ_{χ≠χ₀}μ²(q/q*)q*|err_{χ*}|²x² ≤ E²x²` for `EBound`'s conductor-weighted `E`.
3. **1407 is false** (`DrujalSum`): `harmS = 19.09 > log 2e²r = 14.61`. The spine uses `harmS`.
4. **The lower half never uses `eq:marmo` or `eq:gatosbuenos`.** Helfgott bounds `Σ μ²/φ` ABOVE by
   `½ log r + 0.85` to price the band and tail terms; since both are subtracted inside the same
   `Σ_q μ²(q)/φ(q)·(…)`, a LOWER bound on `S` prices all three at once, provided
   `|η∘|₂² − band − tail ≥ 0` (it is `0.6397`). `(q/r)⁵ ≤ 1` for the tail costs `1.3·10⁻⁴`.

## Numbers (`scratchpad/dspine/nums.py`, `minor_floor.py`; exact rationals in the theorems)

* upper: `A ≤ 2·48.44·0.81² + 1.2·10⁶·3.125·ET(2·1.2 + ET) + … = 63.67 ≤ 100` (`aArith`);
* lower: `J/x ≥ 2·6.5942·0.6397018 − 0.0740045 − 1.8·10⁻⁸ − 10⁻⁶ = 8.36264 ≥ 8.36` (`jArith`),
  with `|η₊|₁ ≤ 0.8673` (`l1_etaPlus_sharp`: `|η∘|₁ ≤ 0.86674704`, band `2.7·10⁻⁴`);
* at `J/x ≥ 8.36` the `p` floor is `8.3599` (`(√8.36 − √8.4031·10⁻¹²)² = 8.3599832`), where
  `MinW.LamberNumW`'s `3.6·10⁻⁴` is FALSE (true sup `3.607510·10⁻⁴`), so `LamberNumD` carries
  `3.7·10⁻⁴` (`+2.56 %`); `MNumD` keeps `0.785` (true sup `0.7532984`, `+4.21 %`); the closing
  `(√(1.2533143·(0.785 + 3.7·10⁻⁴)) + √1.0532·10⁻¹¹)² = 0.9843219 ≤ 0.9845`;
* major arithmetic at `A ≤ 100`: net `1.0485191 ≥ 1.0485` (margin `1.9·10⁻⁵`).
-/

namespace Principia.Common.TernaryGoldbach.DS

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach
open scoped ArithmeticFunction
open Principia.Erdos1054 (helfgottX)
open Principia.Erdos1054.Proofs.BalancedK (HelfgottAt)

/-! ## The quantities of the proof -/

/-- **`I_q(w) = ∫_{−w}^{w} |η̂(−β)|² dβ`**, the per-modulus integral of `eq:juto` after `β = αx`
(`w = δ₀r/2q = 600000/q` for odd `q`, `δ₀r/q` for even `q`). -/
noncomputable def iQ (η : ℝ → ℝ) (w : ℝ) : ℝ := ∫ β in (-w)..w, ‖MajSp.mainFT η β‖ ^ 2

/-- **`L_{r,δ₀}` as the proof defines it** (the main term of `eq:juto`, divided by `x`):
`∑_{q ≤ r odd} μ²/φ·I_q(δ₀r/2q) + ∑_{q ≤ 2r even} μ²/φ·I_q(δ₀r/q)`. -/
noncomputable def lRD (η : ℝ → ℝ) : ℝ :=
  ∑ q ∈ oddQ, cQ q * iQ η (600000 / q) + ∑ q ∈ evenQ, cQ q * iQ η (1200000 / q)

/-- **`∑_{a mod q, (a,q)=1} |S_η(a/q + δ/x, x)|²`**, the left side of 1255. -/
noncomputable def arcSq (η : ℝ → ℝ) (x : ℝ) (q : ℕ) (δ : ℝ) : ℝ :=
  ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
    ‖Smooth.smSum η x ((a : ℝ) / q + δ / x)‖ ^ 2

/-- **`∑_n Λ(n)|η(n/x)|`**, which bounds `max_α |S_η(α,x)|` (1241). -/
noncomputable def sAbs (η : ℝ → ℝ) (x : ℝ) : ℝ := ∑' n : ℕ, Λ n * |η ((n : ℝ) / x)|

/-- **`eq:beatit`'s error, with `|η|`**: `2∑_{p|q} log p ∑_{α ≥ 1} |η(p^α/x)|`. -/
noncomputable def bQ (η : ℝ → ℝ) (x : ℝ) (q : ℕ) : ℝ :=
  2 * ∑ p ∈ q.primeFactors, Real.log p * ∑' k : ℕ, |η ((p : ℝ) ^ (k + 1) / x)|

/-- **The per-arc `K` term** (1240–1243, corrected): `φ(q)·B_q·(2∑Λ|η| + B_q)`. -/
noncomputable def kArc (η : ℝ → ℝ) (x : ℝ) (q : ℕ) : ℝ :=
  (Nat.totient q : ℝ) * bQ η x q * (2 * sAbs η x + bQ η x q)

/-- **The `K` aggregate of `eq:juto`**, divided by `x²`: `∑_q (arc length)·kArc`. -/
noncomputable def kAgg (η : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∑ q ∈ oddQ, 1200000 / (q : ℝ) * kArc η x q +
    ∑ q ∈ evenQ, 2400000 / (q : ℝ) * kArc η x q) / x ^ 2

/-- **The `ET` aggregate of `eq:bfpink`**: `δ₀r·nagS·ET(2|η|₁ + ET)` (Helfgott, via `eq:nagasa`:
`5.19δ₀r·ET(|η|₁ + ET/2)`). -/
noncomputable def etAgg (η : ℝ → ℝ) (T : ℝ) : ℝ := 1200000 * nagS * (T * (2 * MajSp.l1 η + T))

/-- **The `E` aggregate of `eq:bfpink`**: `δ₀r·harmS·E²` (Helfgott: `δ₀r log(2e²r)·E²`, whose
constant is false — `DrujalSum`). -/
noncomputable def eAgg (E : ℝ) : ℝ := 1200000 * harmS * E ^ 2

/-! ## The links -/

/-- **Link [PerArc] — 1233–1270** (`eq:beatit`, orthogonality of characters, `|τ(χ)|² =
μ²(q/q*)q*`), per modulus `q ≤ r·gcd(q,2)` and `|δ| ≤ gcd(q,2)δ₀r/2q`, at the `ET`/`E` bounds of
`eq:sreda` (`E` conductor-weighted: MajSp correction 1). The `K` part is the source's with its
two slips repaired (module docstring, deviation 1). OPEN; generic in the weight, under the
convergence of `∑ Λ(n)|η(n/x)|`. -/
def PerArc (η : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → Summable (fun n : ℕ => Λ n * |η ((n : ℝ) / x)|) →
    ∀ T E : ℝ, MajSp.ETBound η 600000 x T → MajSp.EBound η x E →
      ∀ q : ℕ, 1 ≤ q → q ≤ 150000 * Nat.gcd q 2 → ∀ δ : ℝ,
        |δ| ≤ (Nat.gcd q 2 : ℝ) * 600000 / q →
          |arcSq η x q δ - cQ q * x ^ 2 * ‖MajSp.mainFT η δ‖ ^ 2| ≤
            cQ q * x ^ 2 * (T * (2 * MajSp.l1 η + T)) + E ^ 2 * x ^ 2 + kArc η x q

/-- **Link [ArcInt] — 1272–1315**: integrating per-arc bounds over the arcs of `𝔐_{8,r}` (disjoint
at `x ≥ 4.9·10²⁶`; the arc about `a/q` has length `gcd(q,2)δ₀r/qx`) gives `eq:juto`. Stated for
ANY per-modulus error budget `errq`. OPEN; generic measure theory. -/
def ArcInt (η : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → Summable (fun n : ℕ => Λ n * |η ((n : ℝ) / x)|) →
    ∀ errq : ℕ → ℝ,
      (∀ q : ℕ, 1 ≤ q → q ≤ 150000 * Nat.gcd q 2 → ∀ δ : ℝ,
          |δ| ≤ (Nat.gcd q 2 : ℝ) * 600000 / q →
            |arcSq η x q δ - cQ q * x ^ 2 * ‖MajSp.mainFT η δ‖ ^ 2| ≤ errq q) →
        |MajSp.amaj η x - lRD η| ≤
          (∑ q ∈ oddQ, 1200000 / (q : ℝ) * errq q + ∑ q ∈ evenQ, 2400000 / (q : ℝ) * errq q) /
            x ^ 2

/-- **Link [MardiQ] — 1316–1332** (Plancherel, `eq:mardi` per modulus): `I_q(w) ≤ |η|₂²`.
OPEN; a fact about the weight (TRUE for `η ∈ L¹ ∩ L²` on `(0,∞)`). -/
def MardiQ (η : ℝ → ℝ) : Prop := ∀ w : ℝ, 0 ≤ w → iQ η w ≤ MajSp.l2 η ^ 2

/-- **Link [BandQ] — 1335–1358**, per modulus (before `eq:marmo` is applied):
`I_q(η) ≥ I_q(η∘) − (2|η∘|₂|η − η∘|₂ + |η − η∘|₂²)` (Cauchy–Schwarz and isometry). OPEN; a fact
about the pair (TRUE for `η, η∘ ∈ L¹ ∩ L²`). -/
def BandQ (η ηo : ℝ → ℝ) : Prop :=
  ∀ w : ℝ, 0 ≤ w → iQ ηo w - (2 * MajSp.l2 ηo * MajSp.l2 (fun t => η t - ηo t) +
    MajSp.l2 (fun t => η t - ηo t) ^ 2) ≤ iQ η w

/-- **Link [TailQ] — 1366–1374** (`eq:madge` and Plancherel):
`I_q(η∘) ≥ |η∘|₂² − 2∫_w^∞ |η∘'''|₁²/(2πα)⁶ = |η∘|₂² − |η∘'''|₁²/(160π⁶w⁵)`. OPEN; a fact about
`η∘` (it needs `η∘, η∘', η∘''` to vanish at the ends of the support, which the lemma's printed
hypotheses do not say; Helfgott's `η∘` is `C²` and supported on `[0,2]`). -/
def TailQ (ηo : ℝ → ℝ) : Prop :=
  ∀ w : ℝ, 0 < w → MajSp.l2 ηo ^ 2 - MajSp.l1 (iteratedDeriv 3 ηo) ^ 2 /
    (160 * Real.pi ^ 6 * w ^ 5) ≤ iQ ηo w

/-- **Link [KSmall]**: at every `x ≥ 4.9·10²⁶`, `∑ Λ(n)|η(n/x)|` converges and the `K` aggregate
is `≤ 10⁻⁶` (it is `≈ 5·10⁻¹⁴` for `η₊`). OPEN; weight-specific numerics. -/
def KSmall (η : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → Summable (fun n : ℕ => Λ n * |η ((n : ℝ) / x)|) ∧
    kAgg η x ≤ 1e-6

/-! ## The composition: `eq:juto`/`eq:bfpink` -/

/-- **The aggregates of `eq:juto`**: summing `(arc length)·(cQ x²a + bx² + k)` over the moduli gives
`δ₀r·nagS·a + δ₀r·harmS·b + (the k-aggregate)`. Exact. -/
theorem agg_eq (x a b : ℝ) (k : ℕ → ℝ) (hx : x ≠ 0) :
    (∑ q ∈ oddQ, 1200000 / (q : ℝ) * (cQ q * x ^ 2 * a + b * x ^ 2 + k q) +
        ∑ q ∈ evenQ, 2400000 / (q : ℝ) * (cQ q * x ^ 2 * a + b * x ^ 2 + k q)) / x ^ 2 =
      1200000 * nagS * a + 1200000 * harmS * b +
        (∑ q ∈ oddQ, 1200000 / (q : ℝ) * k q + ∑ q ∈ evenQ, 2400000 / (q : ℝ) * k q) /
          x ^ 2 := by
  have h1 : ∀ q ∈ oddQ, 1200000 / (q : ℝ) * (cQ q * x ^ 2 * a + b * x ^ 2 + k q) =
      x ^ 2 * (1200000 * a) * (cQ q / q) + x ^ 2 * (1200000 * b) * (1 / q) +
        1200000 / (q : ℝ) * k q := fun q _ => by ring
  have h2 : ∀ q ∈ evenQ, 2400000 / (q : ℝ) * (cQ q * x ^ 2 * a + b * x ^ 2 + k q) =
      x ^ 2 * (1200000 * a) * (2 * cQ q / q) + x ^ 2 * (1200000 * b) * (2 / q) +
        2400000 / (q : ℝ) * k q := fun q _ => by ring
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold nagS harmS
  generalize ∑ q ∈ oddQ, cQ q / (q : ℝ) = A1
  generalize ∑ q ∈ oddQ, (1 : ℝ) / q = A2
  generalize ∑ q ∈ oddQ, 1200000 / (q : ℝ) * k q = A3
  generalize ∑ q ∈ evenQ, 2 * cQ q / (q : ℝ) = B1
  generalize ∑ q ∈ evenQ, (2 : ℝ) / q = B2
  generalize ∑ q ∈ evenQ, 2400000 / (q : ℝ) * k q = B3
  field_simp
  ring

/-- **`eq:juto` in aggregate form**: `PerArc` fed into `ArcInt`. -/
theorem juto (η : ℝ → ℝ) (pa : PerArc η) (ai : ArcInt η) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x)
    (hs : Summable (fun n : ℕ => Λ n * |η ((n : ℝ) / x)|)) (T E : ℝ)
    (hT : MajSp.ETBound η 600000 x T) (hE : MajSp.EBound η x E) :
    |MajSp.amaj η x - lRD η| ≤ etAgg η T + eAgg E + kAgg η x := by
  have h : |MajSp.amaj η x - lRD η| ≤
      (∑ q ∈ oddQ, 1200000 / (q : ℝ) *
          (cQ q * x ^ 2 * (T * (2 * MajSp.l1 η + T)) + E ^ 2 * x ^ 2 + kArc η x q) +
        ∑ q ∈ evenQ, 2400000 / (q : ℝ) *
          (cQ q * x ^ 2 * (T * (2 * MajSp.l1 η + T)) + E ^ 2 * x ^ 2 + kArc η x q)) / x ^ 2 :=
    ai x hx hs _ (pa x hx hs T E hT hE)
  have hx0 : x ≠ 0 := (lt_of_lt_of_le (by norm_num) hx).ne'
  rw [agg_eq x (T * (2 * MajSp.l1 η + T)) (E ^ 2) (kArc η x) hx0] at h
  exact h

/-- **The even moduli fold onto the odd ones (1359–1365), PROVED**:
`L_{r,δ₀} = 2∑_{q ≤ r odd} μ²(q)/φ(q)·I_q(δ₀r/2q)`. -/
theorem lRD_eq (η : ℝ → ℝ) : lRD η = 2 * ∑ q ∈ oddQ, cQ q * iQ η (600000 / q) := by
  unfold lRD
  rw [evenOdd (fun q => iQ η (1200000 / q))]
  have e : ∑ q ∈ oddQ, cQ q * iQ η (1200000 / ((2 * q : ℕ) : ℝ)) =
      ∑ q ∈ oddQ, cQ q * iQ η (600000 / q) := by
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [show (1200000 : ℝ) / ((2 * q : ℕ) : ℝ) = 600000 / q by push_cast; ring]
  rw [e]
  ring

/-- **`eq:mardi`**: `L_{r,δ₀} ≤ 2|η|₂²·S`, from `MardiQ`. -/
theorem lRD_le (η : ℝ → ℝ) (mq : MardiQ η) : lRD η ≤ 2 * sR * MajSp.l2 η ^ 2 := by
  rw [lRD_eq]
  unfold sR
  have h : ∑ q ∈ oddQ, cQ q * iQ η (600000 / q) ≤ ∑ q ∈ oddQ, cQ q * MajSp.l2 η ^ 2 :=
    Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (mq _ (by positivity)) (cQ_nonneg q)
  rw [← Finset.sum_mul] at h
  generalize ∑ q ∈ oddQ, cQ q * iQ η (600000 / q) = A at h ⊢
  generalize ∑ q ∈ oddQ, cQ q = B at h ⊢
  linarith

/-- **The lower half of `lem:drujal` before `eq:marmo`**: `L_{r,δ₀} ≥ 2S·(|η∘|₂² − band −
|η∘'''|₁²/(163840π⁶))`, from `BandQ` and `TailQ` at `w = 600000/q ≥ 4`. -/
theorem lRD_ge (η ηo : ℝ → ℝ) (bq : BandQ η ηo) (tq : TailQ ηo) :
    2 * sR * (MajSp.l2 ηo ^ 2 - (2 * MajSp.l2 ηo * MajSp.l2 (fun t => η t - ηo t) +
      MajSp.l2 (fun t => η t - ηo t) ^ 2) -
        MajSp.l1 (iteratedDeriv 3 ηo) ^ 2 / (163840 * Real.pi ^ 6)) ≤ lRD η := by
  rw [lRD_eq]
  unfold sR
  set G := MajSp.l2 ηo ^ 2 - (2 * MajSp.l2 ηo * MajSp.l2 (fun t => η t - ηo t) +
      MajSp.l2 (fun t => η t - ηo t) ^ 2) -
        MajSp.l1 (iteratedDeriv 3 ηo) ^ 2 / (163840 * Real.pi ^ 6) with hG
  have hq : ∀ q ∈ oddQ, cQ q * G ≤ cQ q * iQ η (600000 / q) := by
    intro q hq
    refine mul_le_mul_of_nonneg_left ?_ (cQ_nonneg q)
    have hq' : 1 ≤ q ∧ q ≤ 150000 := by
      simp only [oddQ, Finset.mem_filter, Finset.mem_Icc] at hq
      exact hq.1
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq'.1
    have hq2 : (q : ℝ) ≤ 150000 := by exact_mod_cast hq'.2
    have hw : 4 ≤ (600000 : ℝ) / q := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    have hw0 : 0 < (600000 : ℝ) / q := by positivity
    have h1 := bq _ hw0.le
    have h2 := tq _ hw0
    have h45 : (4 : ℝ) ^ 5 ≤ ((600000 : ℝ) / q) ^ 5 := pow_le_pow_left₀ (by norm_num) hw 5
    have hden : 163840 * Real.pi ^ 6 ≤ 160 * Real.pi ^ 6 * ((600000 : ℝ) / q) ^ 5 :=
      calc 163840 * Real.pi ^ 6 = 160 * Real.pi ^ 6 * 4 ^ 5 := by ring
        _ ≤ 160 * Real.pi ^ 6 * ((600000 : ℝ) / q) ^ 5 :=
            mul_le_mul_of_nonneg_left h45 (by positivity)
    have h3 : MajSp.l1 (iteratedDeriv 3 ηo) ^ 2 / (160 * Real.pi ^ 6 * ((600000 : ℝ) / q) ^ 5) ≤
        MajSp.l1 (iteratedDeriv 3 ηo) ^ 2 / (163840 * Real.pi ^ 6) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
    rw [hG]
    linarith
  have hs := Finset.sum_le_sum hq
  rw [← Finset.sum_mul] at hs
  generalize ∑ q ∈ oddQ, cQ q * iQ η (600000 / q) = A at hs ⊢
  generalize ∑ q ∈ oddQ, cQ q = B at hs ⊢
  linarith

/-! ## The arithmetic sums, numerically -/

/-- `S ≥ 6.5942` (truth `6.7987792`): `S ≥ ∑_{n ≤ r odd} 1/n ≥ 6.5942`. -/
theorem sR_ge : 6.5942 ≤ sR := le_trans hOdd_ge hOdd_le_sR

/-- `S ≥ 0`. -/
theorem sR_nonneg : 0 ≤ sR := le_trans (by norm_num) sR_ge

/-- `S ≤ 48.44` (truth `6.7987792`): `S ≤ (1 + ½ log 149999)² ≤ 6.95929²`. -/
theorem sR_le : sR ≤ 48.44 := by
  have h1 := sR_le_sq
  have h2 := hOdd_le
  have h3 : Real.log 149999 ≤ Real.log 150000 := Real.log_le_log (by norm_num) (by norm_num)
  have h4 := MajSp.log_r_le
  have h5 : hOdd ≤ 6.95929 := by linarith
  have h6 : 0 ≤ hOdd := le_trans (by norm_num) hOdd_ge
  have h7 : hOdd ^ 2 ≤ 6.95929 ^ 2 := pow_le_pow_left₀ h6 h5 2
  linarith

/-- `nagS ≥ 0`. -/
theorem nagS_nonneg : 0 ≤ nagS :=
  add_nonneg (Finset.sum_nonneg fun q _ => div_nonneg (cQ_nonneg q) (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun q _ =>
      div_nonneg (mul_nonneg (by norm_num) (cQ_nonneg q)) (Nat.cast_nonneg _))

/-- `harmS ≥ 0`. -/
theorem harmS_nonneg : 0 ≤ harmS :=
  add_nonneg (Finset.sum_nonneg fun q _ => div_nonneg (by norm_num) (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun q _ => div_nonneg (by norm_num) (Nat.cast_nonneg _))

/-- `harmS ≤ 25.84` (`2(1 + 11.91858)`; truth `19.09`). -/
theorem harmS_le' : harmS ≤ 25.84 := by
  have h1 := harmS_le
  have h2 := MajSp.log_r_le
  linarith

/-! ## The upper half: `DrujalE100` -/

/-- **Link [A] at cap `100`** — `EN.DrujalE` with `A_η(x) ≤ 100` in place of `10` (every
hypothesis unchanged). IMPLIED by `EN.DrujalE` (`drujalE100_of_drujalE`); PRODUCED by the spine
(`drujalE100_of_spine`). -/
def DrujalE100 (η : ℝ → ℝ) : Prop :=
  MemLp η 1 (volume.restrict (Set.Ioi 0)) → (∀ t : ℝ, 0 ≤ t → |η t| ≤ 1.079955) →
    MajSp.l1 η ≤ 1.2 → MajSp.l2 η ≤ 0.81 →
      ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → MajSp.ETBound η 600000 x 1.1377e-8 →
        MajSp.EBound η x 2.3921e-8 → MajSp.amaj η x ≤ 100

/-- **The upper arithmetic**: `2S|η|₂² + etAgg + eAgg + K ≤ 100` at `S ≤ 48.44`, `|η|₂ ≤ 0.81`,
`|η|₁ ≤ 1.2`, `nagS ≤ 3.125`, `harmS ≤ 25.84`, `K ≤ 10⁻⁶` (it is `63.67`). -/
theorem aArith (S l2 l1 nag harm K : ℝ) (hS : S ≤ 48.44) (hl20 : 0 ≤ l2)
    (hl2 : l2 ≤ 0.81) (hl10 : 0 ≤ l1) (hl1 : l1 ≤ 1.2) (hn : nag ≤ 3.125) (hh : harm ≤ 25.84)
    (hK : K ≤ 1e-6) :
    2 * S * l2 ^ 2 + (1200000 * nag * (1.1377e-8 * (2 * l1 + 1.1377e-8)) +
      1200000 * harm * (2.3921e-8) ^ 2 + K) ≤ 100 := by
  have hl2s : l2 ^ 2 ≤ 0.81 ^ 2 := pow_le_pow_left₀ hl20 hl2 2
  have h1 : S * l2 ^ 2 ≤ 48.44 * 0.81 ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hS) (sq_nonneg l2)]
  have hT : 1.1377e-8 * (2 * l1 + 1.1377e-8) ≤ 1.1377e-8 * (2 * 1.2 + 1.1377e-8) := by linarith
  have hT0 : 0 ≤ 1.1377e-8 * (2 * l1 + 1.1377e-8) := by positivity
  have h2 : nag * (1.1377e-8 * (2 * l1 + 1.1377e-8)) ≤
      3.125 * (1.1377e-8 * (2 * 1.2 + 1.1377e-8)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) hT0]
  have h3 : harm * (2.3921e-8) ^ 2 ≤ 25.84 * (2.3921e-8) ^ 2 :=
    mul_le_mul_of_nonneg_right hh (by norm_num)
  linarith

/-- The closing step of the upper half: `|A − L| ≤ R`, `L ≤ U`, `U + R ≤ 100` give `A ≤ 100`. -/
theorem upper_close (A L U R : ℝ) (hj : |A - L| ≤ R) (hL : L ≤ U) (ha : U + R ≤ 100) :
    A ≤ 100 := by
  have h := (abs_le.mp hj).2
  linarith

/-- **`DrujalE100` FROM THE SPINE**: `eq:juto` (`PerArc`, `ArcInt`), `eq:mardi` (`MardiQ`), the `K`
aggregate (`KSmall`), and the proved arithmetic (`aArith`). Application only. -/
theorem drujalE100_of_spine (η : ℝ → ℝ) (pa : PerArc η) (ai : ArcInt η) (mq : MardiQ η)
    (ks : KSmall η) : DrujalE100 η := fun _ _ hl1 hl2 x hx hT hE =>
  upper_close _ _ _ _ (juto η pa ai x hx (ks x hx).1 _ _ hT hE) (lRD_le η mq)
    (aArith sR (MajSp.l2 η) (MajSp.l1 η) nagS harmS (kAgg η x) sR_le (MajSp.l2_nonneg _) hl2
      (MajSp.l1_nonneg _) hl1 nagS_le harmS_le' (ks x hx).2)

/-- **`EN.DrujalE → DrujalE100`**: the cap only rises. -/
theorem drujalE100_of_drujalE (η : ℝ → ℝ) (h : EN.DrujalE η) : DrujalE100 η :=
  fun h1 h2 h3 h4 x hx hT hE => le_trans (h h1 h2 h3 h4 x hx hT hE) (by norm_num)

/-! ## The lower half: `DrujalLowD` -/

/-- **Link [J] at `|η|₁ ≤ 0.8673`, floor `8.36`** — `MinW.DrujalLowE` with `|η|₁ ≤ 0.8673` for
`1.2` and `J/x ≥ 8.36` for `8.613` (every other hypothesis unchanged). IMPLIED by
`MinW.DrujalLowE` (`drujalLowD_of_lowE`); PRODUCED by the spine (`drujalLowD_of_spine`), which
uses only `|η|₁`, `|η∘|₂ ≥ 0.8`, `|η − η∘|₂`, `|η∘'''|₁` and the two `err` bounds. -/
def DrujalLowD (η ηo : ℝ → ℝ) : Prop :=
  MemLp η 1 (volume.restrict (Set.Ioi 0)) → (∀ t : ℝ, 0 ≤ t → |η t| ≤ 1.079955) →
    MajSp.l1 η ≤ 0.8673 →
    (∃ S : Finset ℝ, ∀ t : ℝ, 0 ≤ t → t ∉ S → ContDiffAt ℝ 3 ηo t) →
    Integrable (iteratedDeriv 3 ηo) (volume.restrict (Set.Ioi 0)) →
    MemLp ηo 2 (volume.restrict (Set.Ioi 0)) →
    0.8 ≤ MajSp.l2 ηo → MajSp.l2 ηo ≤ 0.8002 →
    MajSp.l2 (fun t => η t - ηo t) ≤ 1.7999e-4 → MajSp.l1 (iteratedDeriv 3 ηo) ≤ 40 →
    ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → MajSp.ETBound η 600000 x 1.1377e-8 →
      MajSp.EBound η x 2.3921e-8 → 8.36 ≤ MajSp.amaj η x

/-- **The lower arithmetic — THE NEW `J` CONSTANT**: at `S ≥ 6.5942`, `|η∘|₂ ≥ 0.8`,
`|η − η∘|₂ ≤ 1.7999·10⁻⁴`, `|η∘'''|₁ ≤ 40`, `|η|₁ ≤ 0.8673`, `nagS ≤ 3.125`, `harmS ≤ 25.84`,
`K ≤ 10⁻⁶`: `2S(|η∘|₂² − band − tail) − aggregates ≥ 2·6.5942·0.6397018 − 0.0740045 − … =
8.3626377 ≥ 8.36`. -/
theorem jArith (S lo d l3 l1 nag harm K : ℝ) (hS : 6.5942 ≤ S) (hlo : 0.8 ≤ lo) (hd0 : 0 ≤ d)
    (hd : d ≤ 1.7999e-4) (hl30 : 0 ≤ l3) (hl3 : l3 ≤ 40) (hl10 : 0 ≤ l1) (hl1 : l1 ≤ 0.8673)
    (hn : nag ≤ 3.125) (hh : harm ≤ 25.84) (hK : K ≤ 1e-6) :
    8.36 ≤ 2 * S * (lo ^ 2 - (2 * lo * d + d ^ 2) - l3 ^ 2 / (163840 * Real.pi ^ 6)) -
      (1200000 * nag * (1.1377e-8 * (2 * l1 + 1.1377e-8)) +
        1200000 * harm * (2.3921e-8) ^ 2 + K) := by
  have hpi : (3.141592 : ℝ) ^ 6 ≤ Real.pi ^ 6 :=
    pow_le_pow_left₀ (by norm_num) Real.pi_gt_d6.le 6
  have hc3 : l3 ^ 2 / (163840 * Real.pi ^ 6) ≤ 40 ^ 2 / (163840 * (3.141592 : ℝ) ^ 6) :=
    div_le_div₀ (by norm_num) (pow_le_pow_left₀ hl30 hl3 2) (by norm_num) (by linarith)
  have n3 : 40 ^ 2 / (163840 * (3.141592 : ℝ) ^ 6) ≤ 1.01579e-5 := by norm_num
  have hband : 0.64 - 1.6 * d - d ^ 2 ≤ lo ^ 2 - (2 * lo * d + d ^ 2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (by linarith : (0 : ℝ) ≤ lo + 0.8 - 2 * d)]
  have hdd : d ^ 2 ≤ (1.7999e-4) ^ 2 := pow_le_pow_left₀ hd0 hd 2
  have hg : 0.6397018 ≤ lo ^ 2 - (2 * lo * d + d ^ 2) - l3 ^ 2 / (163840 * Real.pi ^ 6) := by
    linarith
  have hmain : 2 * 6.5942 * 0.6397018 ≤
      2 * S * (lo ^ 2 - (2 * lo * d + d ^ 2) - l3 ^ 2 / (163840 * Real.pi ^ 6)) :=
    mul_le_mul (by linarith) hg (by norm_num) (by linarith)
  have hT : 1.1377e-8 * (2 * l1 + 1.1377e-8) ≤ 1.1377e-8 * (2 * 0.8673 + 1.1377e-8) := by
    linarith
  have hT0 : 0 ≤ 1.1377e-8 * (2 * l1 + 1.1377e-8) := by positivity
  have h2 : nag * (1.1377e-8 * (2 * l1 + 1.1377e-8)) ≤
      3.125 * (1.1377e-8 * (2 * 0.8673 + 1.1377e-8)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) hT0]
  have h3 : harm * (2.3921e-8) ^ 2 ≤ 25.84 * (2.3921e-8) ^ 2 :=
    mul_le_mul_of_nonneg_right hh (by norm_num)
  linarith

/-- The closing step of the lower half: `|A − L| ≤ R`, `U ≤ L`, `8.36 ≤ U − R` give `8.36 ≤ A`. -/
theorem lower_close (A L U R : ℝ) (hj : |A - L| ≤ R) (hL : U ≤ L) (ha : 8.36 ≤ U - R) :
    8.36 ≤ A := by
  have h := (abs_le.mp hj).1
  linarith

/-- **`DrujalLowD` FROM THE SPINE**: `eq:juto` (`PerArc`, `ArcInt`), the lower half before
`eq:marmo` (`BandQ`, `TailQ`), the `K` aggregate (`KSmall`), the proved arithmetic
(`S ≥ 6.5942`, `nagS ≤ 3.125`, `harmS ≤ 25.84`; `jArith`). Application only. -/
theorem drujalLowD_of_spine (η ηo : ℝ → ℝ) (pa : PerArc η) (ai : ArcInt η) (bq : BandQ η ηo)
    (tq : TailQ ηo) (ks : KSmall η) : DrujalLowD η ηo :=
  fun _ _ hl1 _ _ _ hlo1 _ hdiff hl3 x hx hT hE =>
    lower_close _ _ _ _ (juto η pa ai x hx (ks x hx).1 _ _ hT hE) (lRD_ge η ηo bq tq)
      (jArith sR (MajSp.l2 ηo) (MajSp.l2 (fun t => η t - ηo t)) (MajSp.l1 (iteratedDeriv 3 ηo))
        (MajSp.l1 η) nagS harmS (kAgg η x) sR_ge hlo1 (MajSp.l2_nonneg _) hdiff
        (MajSp.l1_nonneg _) hl3 (MajSp.l1_nonneg _) hl1 nagS_le harmS_le' (ks x hx).2)

/-- **`MinW.DrujalLowE → DrujalLowD`**: stronger `|η|₁` hypothesis, weaker conclusion. -/
theorem drujalLowD_of_lowE (η ηo : ℝ → ℝ) (h : MinW.DrujalLowE η ηo) : DrujalLowD η ηo :=
  fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 x hx hT hE =>
    le_trans (by norm_num) (h h1 h2 (le_trans h3 (by norm_num)) h4 h5 h6 h7 h8 h9 h10 x hx hT hE)

/-! ## `|η₊|₁ ≤ 0.8673` on Helfgott's weights -/

/-- `∫₋₁¹ (1−u²)³(T₄(u²/2) + (u²/2)⁵/100) = 49779341/57432375 = 0.86674704`. -/
theorem int_C3T : ∫ u in (-1 : ℝ)..1,
    (1 - u ^ 2) ^ 3 * (EN.T4 (u ^ 2 / 2) + (u ^ 2 / 2) ^ 5 / 100) = 49779341 / 57432375 := by
  have h : Set.EqOn (fun u : ℝ => (1 - u ^ 2) ^ 3 * (EN.T4 (u ^ 2 / 2) + (u ^ 2 / 2) ^ 5 / 100))
      (fun u => ∑ k : Fin 17, (![1, 0, -7/2, 0, 37/8, 0, -139/48, 0, 361/384, 0, -39/200, 0,
        133/4800, 0, -1/600, 0, -1/3200] : Fin 17 → ℝ) k * u ^ (k : ℕ)) (Set.uIcc (-1) 1) := by
    intro u _
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.val_zero, Fin.val_succ, EN.T4]
    ring
  rw [intervalIntegral.integral_congr h, EN.int_poly]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.val_zero, Fin.val_succ]
  norm_num

/-- **`|η∘|₁ ≤ 0.86674704`** (truth `0.86674556`), from `e^{−v} ≤ T₄(v) + v⁵/100` at
`v = (t−1)²/2 ≤ 1/2` (`EN.exp_neg_taylor`); `EN.l1_circ_le` has `32/35`. -/
theorem l1_circ_sharp : ∫ t in Set.Ioi (0 : ℝ), |HW.etaCirc t| ≤ 49779341 / 57432375 := by
  rw [EN.setInt_Ioi_02 _ fun t ht => by rw [EN.etaCirc_of_two_lt ht, abs_zero]]
  have hA : IntervalIntegrable (fun t => |HW.etaCirc t|) volume 0 2 :=
    EN.continuous_etaCirc.abs.intervalIntegrable _ _
  have hc : Continuous fun t : ℝ =>
      (1 - (t - 1) ^ 2) ^ 3 * (EN.T4 ((t - 1) ^ 2 / 2) + ((t - 1) ^ 2 / 2) ^ 5 / 100) := by
    unfold EN.T4
    fun_prop
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 2, |HW.etaCirc t| ≤
      (1 - (t - 1) ^ 2) ^ 3 * (EN.T4 ((t - 1) ^ 2 / 2) + ((t - 1) ^ 2 / 2) ^ 5 / 100) := by
    intro t ht
    rw [HW.etaCirc_eq ht.1 ht.2]
    have h20 : 0 ≤ 2 - t := by linarith [ht.2]
    have hp0 : 0 ≤ t ^ 3 * (2 - t) ^ 3 := mul_nonneg (pow_nonneg ht.1 3) (pow_nonneg h20 3)
    have hv0 : 0 ≤ (t - 1) ^ 2 / 2 := by positivity
    have hv1 : (t - 1) ^ 2 / 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    have he := (EN.exp_neg_taylor hv0 hv1).2
    have hee : -(t - 1) ^ 2 / 2 = -((t - 1) ^ 2 / 2) := neg_div _ _
    rw [abs_of_nonneg (mul_nonneg hp0 (Real.exp_pos _).le), hee]
    calc t ^ 3 * (2 - t) ^ 3 * Real.exp (-((t - 1) ^ 2 / 2))
        ≤ t ^ 3 * (2 - t) ^ 3 * (EN.T4 ((t - 1) ^ 2 / 2) + ((t - 1) ^ 2 / 2) ^ 5 / 100) :=
          mul_le_mul_of_nonneg_left he hp0
      _ = (1 - (t - 1) ^ 2) ^ 3 * (EN.T4 ((t - 1) ^ 2 / 2) + ((t - 1) ^ 2 / 2) ^ 5 / 100) := by
          ring
  have h := intervalIntegral.integral_mono_on (by norm_num) hA (hc.intervalIntegrable _ _) hpt
  have hsub : ∫ t in (0 : ℝ)..2,
      (1 - (t - 1) ^ 2) ^ 3 * (EN.T4 ((t - 1) ^ 2 / 2) + ((t - 1) ^ 2 / 2) ^ 5 / 100) =
        49779341 / 57432375 :=
    calc ∫ t in (0 : ℝ)..2,
          (1 - (t - 1) ^ 2) ^ 3 * (EN.T4 ((t - 1) ^ 2 / 2) + ((t - 1) ^ 2 / 2) ^ 5 / 100)
        = ∫ u in (0 - 1 : ℝ)..(2 - 1),
            (1 - u ^ 2) ^ 3 * (EN.T4 (u ^ 2 / 2) + (u ^ 2 / 2) ^ 5 / 100) :=
          intervalIntegral.integral_comp_sub_right
            (fun u => (1 - u ^ 2) ^ 3 * (EN.T4 (u ^ 2 / 2) + (u ^ 2 / 2) ^ 5 / 100)) 1
      _ = ∫ u in (-1 : ℝ)..1,
            (1 - u ^ 2) ^ 3 * (EN.T4 (u ^ 2 / 2) + (u ^ 2 / 2) ^ 5 / 100) := by norm_num
      _ = 49779341 / 57432375 := int_C3T
  linarith

/-- **`|η₊|₁ ≤ 0.8673`**, from `BS.band_sharp`: `|η₊| ≤ |η∘| + 2.7·10⁻⁴·te^{−t²/2}`, so
`|η₊|₁ ≤ 0.86674704 + 2.7·10⁻⁴ = 0.86701704`. -/
theorem l1_etaPlus_sharp : MajSp.l1 HW.etaPlus ≤ 0.8673 := by
  have hA : Integrable (fun t => |HW.etaCirc t|) (volume.restrict (Set.Ioi 0)) :=
    EN.integrableOn_of_cont _ EN.continuous_etaCirc.abs fun t ht => by
      rw [EN.etaCirc_of_two_lt ht, abs_zero]
  have hg : Integrable (fun t => |HW.etaCirc t| + 2.7e-4 * (t * Real.exp (-t ^ 2 / 2)))
      (volume.restrict (Set.Ioi 0)) := hA.add (EN.integrable_t_exp.const_mul 2.7e-4)
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ),
      |HW.etaPlus t| ≤ |HW.etaCirc t| + 2.7e-4 * (t * Real.exp (-t ^ 2 / 2)) := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t * Real.exp (-t ^ 2 / 2) := mul_nonneg (le_of_lt ht) (Real.exp_pos _).le
    have hsplit : HW.etaPlus t =
        HW.etaCirc t + (HW.hH 200 t - HW.hFun t) * (t * Real.exp (-t ^ 2 / 2)) := by
      rw [HW.etaPlus, HW.etaCirc]
      ring
    have hb := BS.band_sharp t ht
    rw [hsplit]
    calc |HW.etaCirc t + (HW.hH 200 t - HW.hFun t) * (t * Real.exp (-t ^ 2 / 2))|
        ≤ |HW.etaCirc t| + |HW.hH 200 t - HW.hFun t| * (t * Real.exp (-t ^ 2 / 2)) := by
          rw [← abs_of_nonneg ht0, ← abs_mul, abs_of_nonneg ht0]
          exact abs_add_le _ _
      _ ≤ |HW.etaCirc t| + 2.7e-4 * (t * Real.exp (-t ^ 2 / 2)) :=
          add_le_add_right (mul_le_mul_of_nonneg_right hb ht0) _
  have h := integral_mono_of_nonneg (ae_of_all _ fun t => abs_nonneg (HW.etaPlus t)) hg
    (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
  rw [integral_add hA (EN.integrable_t_exp.const_mul 2.7e-4), integral_const_mul,
    EN.int_t_exp] at h
  have hc := l1_circ_sharp
  unfold MajSp.l1
  linarith

/-! ## The major arcs at `A ≤ 100` (GENERATED; `gen_dspine.py`) -/

section Major

open Principia.Common.TernaryGoldbach.EN

/-- **Line 2 of `eq:opus111` at `A ≤ 100`** (generated from `EN.line2_le_easy`: `√100 = 10` for
`3.1623`). -/
theorem line2_le_d100 (A lp ls : ℝ) (hA : A ≤ 100) (hlp : lp ≤ 0.81) (hls0 : 0 ≤ ls)
    (hls : ls ^ 2 ≤ 2 / 49) :
    1.3353e-7 / 49 * A + 2.3921e-8 * 1.6812 * (Real.sqrt A + 1.6812 * lp) * ls ≤
      1.3353e-7 / 49 * 100 + 2.3921e-8 * 1.6812 * ((10 + 1.6812 * 0.81) * 0.20204) := by
  have hsA : Real.sqrt A ≤ 10 := by
    refine le_trans (Real.sqrt_le_sqrt hA) ?_
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hls' : ls ≤ 0.20204 := by nlinarith
  have hB' : Real.sqrt A + 1.6812 * lp ≤ 10 + 1.6812 * 0.81 := by linarith
  have hBl : (Real.sqrt A + 1.6812 * lp) * ls ≤ (10 + 1.6812 * 0.81) * 0.20204 :=
    mul_le_mul hB' hls' hls0 (by norm_num)
  linarith

/-- **The major arithmetic at `A ≤ 100`** (generated from `EN.arith_close_b27`): net
`1.0495810 − 1.0440·10⁻³ − 1.7877·10⁻⁵ − 2.2·10⁻⁹ = 1.0485191 ≥ 1.0485` (units `x²/49`;
the cap costs `1.474·10⁻⁵` of the `3.39·10⁻⁵` margin). -/
theorem arith_close_d100 (x s C0 Cc lo l3 lp ls A Zp Zs : ℝ) (I : ℂ)
    (hx : 49 * 10 ^ 25 ≤ x) (hs1 : 1.2533139 ≤ s) (hs2 : s ≤ 1.2533143)
    (hC0 : 1.31 ≤ C0) (hCc : (s * lo ^ 2 - 0.000914) / 49 ≤ Cc)
    (hlo1 : 0.8 ≤ lo) (hlo2 : lo ≤ 0.8002) (hl3 : 0 ≤ l3) (hl3' : l3 ≤ 40)
    (hlp : lp ≤ 0.81) (hls0 : 0 ≤ ls) (hls : ls ^ 2 ≤ 2 / 49)
    (hA : A ≤ 100) (hZp : Zp ≤ 0.640209 * Real.log x)
    (hZs0 : 0 ≤ Zs) (hZs : Zs ≤ 0.0362 * Real.log x)
    (hI : ‖I - ((C0 * Cc * x ^ 2 : ℝ) : ℂ)‖ ≤
      (2.82643 * lo ^ 2 * (2 + 2.25e-4) * 2.25e-4 +
          (4.31004 * lo ^ 2 + 0.0012 * l3 ^ 2 / 8 ^ 5) / 150000) * (s / 49) * x ^ 2 +
        (1.3353e-7 / 49 * A + 2.3921e-8 * 1.6812 * (Real.sqrt A + 1.6812 * lp) * ls) * x ^ 2 +
        (2 * Zp * (24.32 * Real.log x + 0.57) +
          4 * Real.sqrt (Zp * Zs) * (18.57 * Real.log x + 28.39)) * x) :
    1.0485 * x ^ 2 / 49 ≤ I.re := by
  have hX : 0 ≤ x ^ 2 := sq_nonneg x
  have hm := mul_le_mul_of_nonneg_right (main_ge_easy s C0 Cc lo hs1 hC0 hCc hlo1) hX
  have h1 := mul_le_mul_of_nonneg_right (line1_le_b27 s lo l3 hs1 hs2 hlo1 hlo2 hl3 hl3') hX
  have h2 := mul_le_mul_of_nonneg_right (line2_le_d100 A lp ls hA hlp hls0 hls) hX
  have h3 := MajSp.line3_le x Zp Zs hx hZp hZs0 hZs
  have habs := Complex.abs_re_le_norm (I - ((C0 * Cc * x ^ 2 : ℝ) : ℂ))
  rw [Complex.sub_re, Complex.ofReal_re] at habs
  have hlow := (abs_le.mp (le_trans habs hI)).1
  linarith only [hlow, hm, h1, h2, h3, hX]

/-- **(7.25) at `1.0485` with `DrujalE100`** (generated from `EN.majorAt_b27w`;
application only). -/
theorem majorAt_d100 (ηp ηs ηo ηc : ℝ → ℝ) (hm : RT.HelfMajFull ηp ηc)
    (sc : MajSp.StarScale ηs ηc) (rg : RW.RegW ηp ηs ηo) (nf : RW.NefumoW ηp ηs ηo)
    (dj : DrujalE100 ηp) (cl : CLowerE ηo ηs) (nm : NormsB27 ηp ηs ηo)
    (sn : MajSp.SupN ηp ηs) (pf : RT.PlattFull) : RT.MajorLowerAt 1.0485 ηp ηs := by
  intro N hodd hN
  obtain ⟨mp, cp, mh⟩ := hm pf
  obtain ⟨hlo1, hlo2, hdiff, hl3, hld, hl1s, hls, hl1p, hl2p⟩ := nm
  have hx := MajSp.helfX_big N hN
  have hEp := MajSp.eb_plus ηp mp (helfgottX N) hx
  have hEs := MajSp.eb_star ηs ηc sc cp (helfgottX N) hx
  have hET := MajSp.et_plus ηp mp (helfgottX N) hx
  have hT0 := MajSp.et0_star ηs ηc sc cp (helfgottX N) hx
  have hZp := MajSp.zplus ηp (helfgottX N) hx (mh (helfgottX N) (MajSp.x12_le _ hx))
  have hZs := MajSp.zstar_holds ηs sn.2.2.1 sn.2.2.2.2 hl1s (helfgottX N) hx hT0
  have hA := dj rg.1 sn.1 hl1p hl2p (helfgottX N) hx hET hEp
  obtain ⟨hLp, hLs⟩ := MajSp.ls_link ηp ηs sn (helfgottX N) hx
  have hlt := eps_lt_b27 _ _ hdiff hlo1
  have hnef := nf rg 2.25e-4 eps_nonneg_b27 hlt N (MajSp.N_one N hN) (helfgottX N) hx
    2.3921e-8 (1.3353e-7 / 49) hEp hEs (18.57 * Real.log (helfgottX N) + 28.39)
    (24.32 * Real.log (helfgottX N) + 0.57) hLp hLs
  rw [hl1s] at hnef
  have hC := cl hld N hodd hN
  obtain ⟨hs1, hs2⟩ := MajSp.sqrt_pi_half
  exact arith_close_d100 (helfgottX N) (Real.sqrt (Real.pi / 2)) (SingularSeries.sing3 N)
    (MajSp.ccon ηo ηs ((N : ℝ) / helfgottX N)) (MajSp.l2 ηo) (MajSp.l1 (iteratedDeriv 3 ηo))
    (MajSp.l2 ηp) (MajSp.l2 ηs) (MajSp.amaj ηp (helfgottX N))
    (MajSp.zk (fun t => ηp t ^ 2) 2 (helfgottX N)) (MajSp.zk (fun t => ηs t ^ 2) 2 (helfgottX N))
    _ hx hs1 hs2 (RT.c0_131 N hodd) hC hlo1 hlo2 (MajSp.l1_nonneg _) hl3 hl2p (MajSp.l2_nonneg _)
    hls hA hZp (MajSp.zk_sq_nonneg _ _ (MajSp.x_nonneg _ hx)) hZs hnef

/-- **`HelfgottAt 0.00032` with `DrujalE100`** (generated from `EN.helfgottAt_b27w`). -/
theorem helfgottAt_d100 (pf : RT.PlattFull)
    (hm : RT.HelfMajFull HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (rg : RW.RegW HW.etaPlus HW.etaStar HW.etaCirc)
    (nf : RW.NefumoW HW.etaPlus HW.etaStar HW.etaCirc) (dj : DrujalE100 HW.etaPlus)
    (cl : CLowerE HW.etaCirc HW.etaStar) (hb : BandSharp27)
    (mn : RT.MinorUpperAt 0.9845 HW.etaPlus HW.etaStar) : HelfgottAt 0.00032 :=
  helfAt_smooth_b27 HW.etaPlus HW.etaStar BL.supBounds_helf
    (majorAt_d100 HW.etaPlus HW.etaStar HW.etaCirc (HW.mconv HW.eta2 HW.phi) hm RT.starScale_helf
      rg nf dj cl (normsB27_helf hb) supN_helf pf) mn

end Major

/-! ## The minor spine at the `DrujalLowD` floor (GENERATED; `gen_dspine.py`) -/

section Minor

open Principia.Common.TernaryGoldbach.MinSp

/-- **Link [T] at the `DrujalLowD` floor — `eq:lamber`**: `C_{φ,3}(½ log(x/κ))·(s − p) ≤ 3.7·10⁻⁴`
at every `s ≤ felipa`, `p ≥ 8.3599` (generated from `MinW.LamberNumW`: `p ≥ 8.6129`, `3.6·10⁻⁴`).
On Helfgott's `φ` the exact supremum is `3.607510·10⁻⁴` (at the threshold; margin `+2.56 %`); his
`0.2779/K³` gives `3.608844·10⁻⁴`. `3.6·10⁻⁴` is FALSE at this floor. OPEN;
`φ`-specific numerics. -/
def LamberNumD (φ : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ s p : ℝ, s ≤ 0.640209 * Real.log x - 0.021095 → 8.3599 ≤ p →
    cPhi3 φ (kK (x / 49)) * (s - p) ≤ 3.7e-4

/-- **Link [M] at the `DrujalLowD` floor — `eq:bustier`, jointly in `x`**: `MinW.MNumW` with
`p ≥ 8.3599` (was `8.6129`). With `g` exact (`eq:basia`) its supremum over `x ≥ 4.9·10²⁶`,
`0 ≤ s ≤ felipa`, `p ≥ 8.3599` is `0.7532984` (at the threshold), so `MNumD φ 0.785` holds
with a `+4.21 %` margin. STRONGER than `MinW.MNumW` (`mnumW_of_D`). OPEN; numerics about
`eq:basia`. -/
def MNumD (φ : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ s p : ℝ, 0 ≤ s → s ≤ 0.640209 * Real.log x - 0.021095 →
    8.3599 ≤ p →
      gB φ (x / 49) 150000 * (hR0 x * s - p) +
          (2 / (Real.log x + 2 * 0.6294) * intG φ (x / 49) +
            coefC x * gB φ (x / 49) (r1y (x / 49))) * s ≤ c

/-- **`eq:je` at the new floor**: `J ≥ 8.36x`, `E ≤ 8.4031·10⁻¹²x` give `(√J − √E)² ≥ 8.3599x`
(`(√8.36 − √8.4031·10⁻¹²)² = 8.3599832`). Generated from `MinW.je_le_w`. -/
theorem je_le_d (J E x : ℝ) (hx : 0 ≤ x) (hJ : 8.36 * x ≤ J) (hE : E ≤ 8.4031e-12 * x) :
    8.3599 * x ≤ (Real.sqrt J - Real.sqrt E) ^ 2 := by
  have ha := Real.sqrt_le_sqrt hJ
  have he := Real.sqrt_le_sqrt hE
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8.36)] at ha
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8.4031e-12)] at he
  have hu0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hux : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have ha2 : Real.sqrt 8.36 ^ 2 = 8.36 := Real.sq_sqrt (by norm_num)
  have hc2 : Real.sqrt 8.4031e-12 ^ 2 = 8.4031e-12 := Real.sq_sqrt (by norm_num)
  have ha0 : 0 ≤ Real.sqrt 8.36 := Real.sqrt_nonneg _
  have hc0 : 0 ≤ Real.sqrt 8.4031e-12 := Real.sqrt_nonneg _
  have ha3 : Real.sqrt 8.36 ≤ 3 := by nlinarith
  have ha1 : 2 ≤ Real.sqrt 8.36 := by nlinarith
  have hc3 : Real.sqrt 8.4031e-12 ≤ 3e-6 := by nlinarith
  have hd : (Real.sqrt 8.36 - Real.sqrt 8.4031e-12) * Real.sqrt x ≤
      Real.sqrt J - Real.sqrt E := by nlinarith
  have hd0 : 0 ≤ (Real.sqrt 8.36 - Real.sqrt 8.4031e-12) * Real.sqrt x :=
    mul_nonneg (by linarith) hu0
  have hsq := pow_le_pow_left₀ hd0 hd 2
  have hk : 8.3599 ≤ (Real.sqrt 8.36 - Real.sqrt 8.4031e-12) ^ 2 := by nlinarith
  have hm : 8.3599 * x ≤ ((Real.sqrt 8.36 - Real.sqrt 8.4031e-12) * Real.sqrt x) ^ 2 := by
    rw [mul_pow, hux]
    exact mul_le_mul_of_nonneg_right hk hx
  linarith

/-- `je_le_d` on the defined quantities: `J = x·A_{η₊}`, `A_{η₊} ≥ 8.36`. -/
theorem pje_le_d (η b : ℝ → ℝ) (x : ℝ) (hx : 0 ≤ x) (hA : 8.36 ≤ MajSp.amaj η x)
    (hE : eBig b x ≤ 8.4031e-12 * x) : 8.3599 * x ≤ pJE η b x := by
  unfold pJE
  refine je_le_d _ _ x hx ?_ hE
  rw [mul_comm x]
  exact mul_le_mul_of_nonneg_right hA hx

/-- **`M ≤ cM·x`** from `MNumD`, `S ∈ [0, felipa]` and `(√J − √E)² ≥ 8.3599x`. -/
theorem m_le_d (φ η b : ℝ → ℝ) (cM x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (hmn : MNumD φ cM)
    (hS0 : 0 ≤ sPr η x) (hS : sPr η x ≤ (0.640209 * Real.log x - 0.021095) * x)
    (hP : 8.3599 * x ≤ pJE η b x) : mM φ η b x ≤ cM * x := by
  have hx0 := x_pos x hx
  unfold mM
  refine m_scale _ _ _ _ _ _ _ _ x cM hx0 (hmn x hx _ _ (div_nonneg hS0 hx0.le) ?_ ?_)
  · rw [div_le_iff₀ hx0]
    exact hS
  · rw [le_div_iff₀ hx0]
    exact hP

/-- **`T ≤ 3.7·10⁻⁴ x`** from `LamberNumD`. -/
theorem t_le_d (φ η b : ℝ → ℝ) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (hla : LamberNumD φ)
    (hS : sPr η x ≤ (0.640209 * Real.log x - 0.021095) * x)
    (hP : 8.3599 * x ≤ pJE η b x) : tT φ η b x ≤ 3.7e-4 * x := by
  have hx0 := x_pos x hx
  unfold tT
  refine t_scale _ _ _ x _ hx0 (hla x hx _ _ ?_ ?_)
  · rw [div_le_iff₀ hx0]
    exact hS
  · rw [le_div_iff₀ hx0]
    exact hP

/-- **`eq:rozoj` at `T ≤ 3.7·10⁻⁴x`** (generated from `MinW.z_close_w`). -/
theorem z_close_d (Z a M T SE x c cM : ℝ)
    (hZ : Z ≤ (Real.sqrt (a * x / 49 * (M + T)) + Real.sqrt SE) ^ 2)
    (ha0 : 0 ≤ a) (ha : a ≤ 1.2533143) (hx : 0 ≤ x) (hMT : M + T ≤ (cM + 3.7e-4) * x)
    (hcM : 0 ≤ cM + 3.7e-4) (hSE : SE ≤ 1.0532e-11 * x ^ 2 / 49)
    (hc : (Real.sqrt (1.2533143 * (cM + 3.7e-4)) + Real.sqrt 1.0532e-11) ^ 2 ≤ c) :
    Z ≤ c * x ^ 2 / 49 := by
  have hx7 : 0 ≤ x / 7 := div_nonneg hx (by norm_num)
  have h1 : a * x / 49 * (M + T) ≤ 1.2533143 * (cM + 3.7e-4) * (x / 7) ^ 2 := by
    have hx49 : 0 ≤ a * x / 49 := div_nonneg (mul_nonneg ha0 hx) (by norm_num)
    calc a * x / 49 * (M + T) ≤ a * x / 49 * ((cM + 3.7e-4) * x) :=
          mul_le_mul_of_nonneg_left hMT hx49
      _ = a * ((cM + 3.7e-4) * (x / 7) ^ 2) := by ring
      _ ≤ 1.2533143 * ((cM + 3.7e-4) * (x / 7) ^ 2) :=
          mul_le_mul_of_nonneg_right ha (mul_nonneg hcM (sq_nonneg _))
      _ = 1.2533143 * (cM + 3.7e-4) * (x / 7) ^ 2 := by ring
  have h2 : SE ≤ 1.0532e-11 * (x / 7) ^ 2 := le_of_le_of_eq hSE (by ring)
  have hs1 : Real.sqrt (a * x / 49 * (M + T)) ≤
      Real.sqrt (1.2533143 * (cM + 3.7e-4)) * (x / 7) := by
    calc Real.sqrt (a * x / 49 * (M + T))
        ≤ Real.sqrt (1.2533143 * (cM + 3.7e-4) * (x / 7) ^ 2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt (1.2533143 * (cM + 3.7e-4)) * (x / 7) := by
          rw [Real.sqrt_mul (mul_nonneg (by norm_num) hcM), Real.sqrt_sq hx7]
  have hs2 : Real.sqrt SE ≤ Real.sqrt 1.0532e-11 * (x / 7) := by
    calc Real.sqrt SE ≤ Real.sqrt (1.0532e-11 * (x / 7) ^ 2) := Real.sqrt_le_sqrt h2
      _ = Real.sqrt 1.0532e-11 * (x / 7) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hx7]
  have hsum0 : 0 ≤ Real.sqrt (a * x / 49 * (M + T)) + Real.sqrt SE :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsum : Real.sqrt (a * x / 49 * (M + T)) + Real.sqrt SE ≤
      (Real.sqrt (1.2533143 * (cM + 3.7e-4)) + Real.sqrt 1.0532e-11) * (x / 7) := by
    linarith
  have hsq := pow_le_pow_left₀ hsum0 hsum 2
  calc Z ≤ (Real.sqrt (a * x / 49 * (M + T)) + Real.sqrt SE) ^ 2 := hZ
    _ ≤ ((Real.sqrt (1.2533143 * (cM + 3.7e-4)) + Real.sqrt 1.0532e-11) * (x / 7)) ^ 2 := hsq
    _ = (Real.sqrt (1.2533143 * (cM + 3.7e-4)) + Real.sqrt 1.0532e-11) ^ 2 * (x ^ 2 / 49) := by
        ring
    _ ≤ c * (x ^ 2 / 49) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = c * x ^ 2 / 49 := by ring

/-- `M + T ≤ (cM + 3.7·10⁻⁴)x`. -/
theorem mt_le_d (M T cM x : ℝ) (hM : M ≤ cM * x) (hT : T ≤ 3.7e-4 * x) :
    M + T ≤ (cM + 3.7e-4) * x :=
  le_of_le_of_eq (add_le_add hM hT) (by ring)

/-- **THE SPINE of (7.48) at the `DrujalLowD` floor**, generic in the constant:
`MinW.minor_of_mnum_w` with `DrujalLowD` (fed `|η₊|₁ ≤ 0.8673` by the new binder `hl1`),
`LamberNumD`, `MNumD`. Application only. -/
theorem minor_of_mnum_d (c cM : ℝ)
    (hc : (Real.sqrt (1.2533143 * (cM + 3.7e-4)) + Real.sqrt 1.0532e-11) ^ 2 ≤ c)
    (hcM : 0 ≤ cM + 3.7e-4) (ηp ηs ηo ηc φ : ℝ → ℝ) (hm : RT.HelfMajFull ηp ηc)
    (hpf : RT.PlattFull) (hsc : MajSp.StarScale ηs ηc) (hrg : RW.RegW ηp ηs ηo)
    (hnm : EN.NormsB27 ηp ηs ηo) (hsn : MajSp.SupN ηp ηs) (hoh : OstopHyp ηp ηs φ)
    (hos : Ostop ηp ηs φ) (hdl : DrujalLowD ηp ηo) (hl1 : MajSp.l1 ηp ≤ 0.8673)
    (hdu : Dubistdie ηp) (hpl : PhiL1 φ)
    (hla : LamberNumD φ) (hmn : MNumD φ cM) : RT.MinorUpperAt c ηp ηs := by
  intro N _ hN
  obtain ⟨mp, cp, mh⟩ := hm hpf
  obtain ⟨hlo1, hlo2, hdiff, hl3, -, hl1s, -, -, -⟩ := hnm
  have hx := MajSp.helfX_big N hN
  have hx0 := x_pos (helfgottX N) hx
  obtain ⟨b, hb⟩ := exists_supFn ηp hoh.2.2.2.2.1
  have hZ := hos hoh b hb (helfgottX N) hx
  have hS := felipa ηp (helfgottX N) hx (mh (helfgottX N) (MajSp.x12_le _ hx))
  have hS0 := sPr_nonneg ηp (helfgottX N)
  have hE := hdu hsn.1 hsn.2.1 b hb (helfgottX N) hx
  have hA := hdl hrg.1 hsn.1 hl1 hrg.2.2.2.2.1 hrg.2.2.2.2.2.1 hrg.2.2.2.2.2.2
    hlo1 hlo2 hdiff hl3 (helfgottX N) hx (MajSp.et_plus ηp mp _ hx) (MajSp.eb_plus ηp mp _ hx)
  have hP := pje_le_d ηp b (helfgottX N) hx0.le hA hE
  have hM := m_le_d φ ηp b cM (helfgottX N) hx hmn hS0 hS hP
  have hT := t_le_d φ ηp b (helfgottX N) hx hla hS hP
  have hSt := sstar_le ηs ηc hsc cp hsn.2.2.1 hl1s (helfgottX N) hx
  have hSE := hex_le _ _ (helfgottX N) hx0.le (sStar_nonneg ηs hsn.2.2.1 _ hx0) hSt hE
  exact z_close_d _ _ _ _ _ _ c cM hZ (MajSp.l1_nonneg φ) (phi_l1_le φ hpl) hx0.le
    (mt_le_d _ _ cM _ hM hT) hcM hSE hc

/-- The joint route closes at `T ≤ 3.7·10⁻⁴`: `(√(1.2533143·0.78537) + √1.0532·10⁻¹¹)² = 0.9843219`
`≤ 0.9845`. -/
theorem close_mnum_d : (Real.sqrt (1.2533143 * (0.785 + 3.7e-4)) + Real.sqrt 1.0532e-11) ^ 2 ≤
    0.9845 :=
  close_num _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `cM + 3.7·10⁻⁴ ≥ 0` at the joint constant. -/
theorem cM_mnum_d : (0 : ℝ) ≤ 0.785 + 3.7e-4 := by norm_num

/-- **`RT.MinorUpperAt 0.9845` at the `DrujalLowD` floor, joint `MNumD φ 0.785`**. Application
only. -/
theorem minorAt_mnum_d (ηp ηs ηo ηc φ : ℝ → ℝ) (hm : RT.HelfMajFull ηp ηc)
    (hpf : RT.PlattFull) (hsc : MajSp.StarScale ηs ηc) (hrg : RW.RegW ηp ηs ηo)
    (hnm : EN.NormsB27 ηp ηs ηo) (hsn : MajSp.SupN ηp ηs) (hoh : OstopHyp ηp ηs φ)
    (hos : Ostop ηp ηs φ) (hdl : DrujalLowD ηp ηo) (hl1 : MajSp.l1 ηp ≤ 0.8673)
    (hdu : Dubistdie ηp) (hpl : PhiL1 φ)
    (hla : LamberNumD φ) (hmn : MNumD φ 0.785) : RT.MinorUpperAt 0.9845 ηp ηs :=
  minor_of_mnum_d 0.9845 0.785 close_mnum_d cM_mnum_d ηp ηs ηo ηc φ hm hpf hsc hrg hnm hsn hoh hos
    hdl hl1 hdu hpl hla hmn

/-- `amaj` of a junk weight is `0`, so `DrujalLowD`'s conclusion is FALSE for it. -/
theorem amaj_junk_d (η : ℝ → ℝ) (x : ℝ) (h : ∀ α, Smooth.smSum η x α = 0) :
    ¬ 8.36 ≤ MajSp.amaj η x := by
  have h0 : MajSp.amaj η x = 0 := by simp [MajSp.amaj, h]
  rw [h0]
  norm_num

/-- **`MNumD` forces `g(r₀) ≥ 0`** (generated from `MinW.mnumW_nonneg`). -/
theorem mnumD_nonneg (φ : ℝ → ℝ) (c : ℝ) (h : MNumD φ c) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) :
    0 ≤ gB φ (x / 49) 150000 := by
  by_contra hneg
  have hlt : gB φ (x / 49) 150000 < 0 := not_le.mp hneg
  set g0 := gB φ (x / 49) 150000
  have hg : g0 ≠ 0 := hlt.ne
  have hL := MajSp.log_ge_one x hx
  have hs0 : (0 : ℝ) ≤ 0.640209 * Real.log x - 0.021095 := by linarith
  have hq : 0 ≤ (|c| + 1) / (-g0) := div_nonneg (by positivity) (by linarith)
  have h1 := h x hx 0 (8.3599 + (|c| + 1) / (-g0)) le_rfl hs0 (by linarith)
  have e : g0 * (hR0 x * 0 - (8.3599 + (|c| + 1) / (-g0))) +
      (2 / (Real.log x + 2 * 0.6294) * intG φ (x / 49) +
        coefC x * gB φ (x / 49) (r1y (x / 49))) * 0 = -(8.3599 * g0) + (|c| + 1) := by
    field_simp
    ring
  rw [e] at h1
  have h2 := le_abs_self c
  linarith

/-- **`LamberNumD` forces `C_{φ,3}(½ log(x/κ)) ≥ 0`** (generated from
`MinW.lamberW_nonneg`). -/
theorem lamberD_nonneg (φ : ℝ → ℝ) (h : LamberNumD φ) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) :
    0 ≤ cPhi3 φ (kK (x / 49)) := by
  by_contra hneg
  have hlt : cPhi3 φ (kK (x / 49)) < 0 := not_le.mp hneg
  set C := cPhi3 φ (kK (x / 49))
  have hC : C ≠ 0 := hlt.ne
  have hL := MajSp.log_ge_one x hx
  have hs0 : (0 : ℝ) ≤ 0.640209 * Real.log x - 0.021095 := by linarith
  have hq : 0 ≤ 1 / (-C) := div_nonneg (by norm_num) (by linarith)
  have h1 := h x hx 0 (8.3599 + 1 / (-C)) hs0 (by linarith)
  have e : C * (0 - (8.3599 + 1 / (-C))) = -(8.3599 * C) + 1 := by
    field_simp
    ring
  rw [e] at h1
  linarith

/-- **`MNumD → MinW.MNumW`**: the same bound on the narrower range `p ≥ 8.6129 ⊆ p ≥ 8.3599`. -/
theorem mnumW_of_D (φ : ℝ → ℝ) (c : ℝ) (h : MNumD φ c) : MinW.MNumW φ c :=
  fun x hx s p hs0 hs hp => h x hx s p hs0 hs (le_trans (by norm_num) hp)

end Minor

/-! ## The adversarial pass -/

/-- `iQ` of the zero weight is `0`. -/
theorem iQ_zero (w : ℝ) : iQ 0 w = 0 := by
  simp [iQ, MajSp.mainFT]

/-- **`BandQ η η` holds for EVERY weight** (the band term is `≥ 0`): the link is satisfiable by
anything on the diagonal, and constrains only a genuine approximation `η∘ ≠ η`. -/
theorem bandQ_self (η : ℝ → ℝ) : BandQ η η := by
  intro w _
  have h1 := MajSp.l2_nonneg η
  have h2 := MajSp.l2_nonneg (fun t => η t - η t)
  nlinarith [mul_nonneg h1 h2, sq_nonneg (MajSp.l2 (fun t => η t - η t))]

/-- **`PerArc`, `MardiQ`, `TailQ`, `KSmall` hold for the zero weight** (so none is contradictory;
nondegeneracy lives in the norm hypotheses of the composed links, as in `MajSp`). -/
theorem spine_zero : PerArc 0 ∧ MardiQ 0 ∧ TailQ 0 ∧ KSmall 0 := by
  refine ⟨fun x _ _ T E _ _ q _ _ δ _ => ?_, fun w _ => ?_, fun w hw => ?_,
    fun x _ => ⟨?_, ?_⟩⟩
  · have ha : arcSq 0 x q δ = 0 := by simp [arcSq, Smooth.smSum_zero]
    have hm : MajSp.mainFT 0 δ = 0 := by simp [MajSp.mainFT]
    have hk : kArc 0 x q = 0 := by simp [kArc, bQ, sAbs]
    have hl : MajSp.l1 (0 : ℝ → ℝ) = 0 := by simp [MajSp.l1]
    rw [ha, hm, hk, hl]
    have h1 : 0 ≤ cQ q * x ^ 2 * (T * (2 * 0 + T)) := by
      have := cQ_nonneg q
      have : 0 ≤ T * (2 * 0 + T) := by nlinarith [sq_nonneg T]
      positivity
    have h2 : 0 ≤ E ^ 2 * x ^ 2 := by positivity
    have hz : |(0 : ℝ) - cQ q * x ^ 2 * ‖(0 : ℂ)‖ ^ 2| = 0 := by simp
    rw [hz]
    linarith
  · rw [iQ_zero, MajSp.l2_zero]
    norm_num
  · rw [iQ_zero, MajSp.l2_zero]
    have : 0 ≤ MajSp.l1 (iteratedDeriv 3 (0 : ℝ → ℝ)) ^ 2 / (160 * Real.pi ^ 6 * w ^ 5) :=
      div_nonneg (sq_nonneg _) (mul_pos (by positivity) (pow_pos hw 5)).le
    linarith
  · simp
  · norm_num [kAgg, kArc, bQ, sAbs]

/-- **`ArcInt` holds for the zero weight**: both sides vanish, and every admissible modulus gets a
nonnegative budget from the per-arc hypothesis at `δ = 0`. -/
theorem arcInt_zero : ArcInt 0 := by
  intro x _ _ errq herr
  have hA : MajSp.amaj 0 x = 0 := by simp [MajSp.amaj, Smooth.smSum_zero]
  have hL : lRD 0 = 0 := by simp [lRD, iQ_zero]
  rw [hA, hL, sub_zero, abs_zero]
  have hq : ∀ q : ℕ, 1 ≤ q → q ≤ 150000 * Nat.gcd q 2 → 0 ≤ errq q := fun q h1 h2 =>
    le_trans (abs_nonneg _) (herr q h1 h2 0 (by rw [abs_zero]; positivity))
  have ho : ∀ q ∈ oddQ, 0 ≤ 1200000 / (q : ℝ) * errq q := by
    intro q hq'
    simp only [oddQ, Finset.mem_filter, Finset.mem_Icc] at hq'
    have hg : 0 < Nat.gcd q 2 := Nat.gcd_pos_of_pos_right q (by norm_num)
    exact mul_nonneg (by positivity)
      (hq q hq'.1.1 (le_trans hq'.1.2 (Nat.le_mul_of_pos_right 150000 hg)))
  have he : ∀ q ∈ evenQ, 0 ≤ 2400000 / (q : ℝ) * errq q := by
    intro q hq'
    simp only [evenQ, Finset.mem_filter, Finset.mem_Icc] at hq'
    have hg : Nat.gcd q 2 = 2 := Nat.gcd_eq_right (even_iff_two_dvd.mp hq'.2)
    exact mul_nonneg (by positivity) (hq q hq'.1.1 (by rw [hg]; omega))
  exact div_nonneg (add_nonneg (Finset.sum_nonneg ho) (Finset.sum_nonneg he)) (sq_nonneg x)

/-- **The spine REJECTS a junk weight**: if `S_η(α,x) ≡ 0` at some `x ≥ 4.9·10²⁶` (Mathlib's value
for a non-summable `tsum`), the lower-half links cannot all hold alongside the norm hypotheses —
`drujalLowD_of_spine` would force `A_η(x) ≥ 8.36` while `A_η(x) = 0`. -/
theorem spine_rejects_junk (η ηo : ℝ → ℝ) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x)
    (hj : ∀ α, Smooth.smSum η x α = 0) (pa : PerArc η) (ai : ArcInt η) (bq : BandQ η ηo)
    (tq : TailQ ηo) (ks : KSmall η) (h1 : MemLp η 1 (volume.restrict (Set.Ioi 0)))
    (h2 : ∀ t : ℝ, 0 ≤ t → |η t| ≤ 1.079955) (h3 : MajSp.l1 η ≤ 0.8673)
    (h4 : ∃ S : Finset ℝ, ∀ t : ℝ, 0 ≤ t → t ∉ S → ContDiffAt ℝ 3 ηo t)
    (h5 : Integrable (iteratedDeriv 3 ηo) (volume.restrict (Set.Ioi 0)))
    (h6 : MemLp ηo 2 (volume.restrict (Set.Ioi 0))) (h7 : 0.8 ≤ MajSp.l2 ηo)
    (h8 : MajSp.l2 ηo ≤ 0.8002) (h9 : MajSp.l2 (fun t => η t - ηo t) ≤ 1.7999e-4)
    (h10 : MajSp.l1 (iteratedDeriv 3 ηo) ≤ 40) (hT : MajSp.ETBound η 600000 x 1.1377e-8)
    (hE : MajSp.EBound η x 2.3921e-8) : False :=
  amaj_junk_d η x hj
    (drujalLowD_of_spine η ηo pa ai bq tq ks h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 x hx hT hE)

end Principia.Common.TernaryGoldbach.DS
