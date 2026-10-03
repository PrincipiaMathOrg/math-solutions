/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MinMainP
import Principia.Common.TernaryGoldbach.GorshSpine
import Mathlib.NumberTheory.DiophantineApproximation.Basic

set_option autoImplicit false

/-!
# The four pieces of `OP.MinMainP 0.811 45.7575`, spined one level down

`MMP.minMainP_of_piecesW` reduces the corrected minarcs Main Theorem for `η₂` to four pieces:
`MMP.TypeI1W`, `MT.TypeI2`, `MT.TypeII` and `MT.MinMain2L`. This file spines each piece along
Helfgott's book (arXiv:1501.05438, `minarctotals.tex`, `typeI.tex`), every gap a NAMED `Prop`,
every composition PROVED (application plus elementary algebra), and ends in
`minMainP_of_links`, which reaches `OP.MinMainP 0.811 45.7575` from the links alone.

## The spine

```
 TypeI1W  ← Bostb1At       lem:bostb1 at the first choice, main term CORRECTED (x/2q, −δ/2)
          ← Grara, Ronsard, Meproz   the three cited μ-sum bounds (minarcs 650-670)
          ← I1Arith         NUMERIC: eq:cupcake2+kuche2 at D = U  ≤  MMP.bI1W
          typeI1W_of : PROVED (incl. the split muL = log(z/N)·muS + muL(N), `muL_split`)
 TypeI2   ← I2Split         eq:jotoco, S_{I,2} = Σ_v Λ(v)f(v)·gorio2(x/v, vα, U)     PROVED
          ← Bosta2Eta2      lem:bosta2 for η₂, GENERIC (quantified over x, α, D, q, δ, Q₀)
          ← Grara, Ronsard
          ← I2Arith         NUMERIC: Σ_v Λ(v)f(v)·(per-v bosta2 bound) ≤ MT.bI2
          per-v approximation 2(vα) = (va/g)/(q/g) + δ/(x/v), g = (v,q)             PROVED
          typeI2_of : PROVED
 TypeII   ← Vinland1At      eq:vinland1 at the first choice (every δ, q ≤ V/2θ)
          ← EriksagaAt      eq:eriksaga at the first choice (|δ| ≥ 8)
          ← IIArith         NUMERIC: vinland1 (|δ| < 8) / eriksaga (|δ| ≥ 8) ≤ MT.bII,
                            given lem:merkel's q/φ(q) ≤ ϝ(x^{1/3}/6)
          typeII_of : PROVED (lem:merkel from `GS.merkel_of_rs62`)
 MinMain2L← SecI1At, SecI2At, SecIIAt   the book's second choice (eq:elpozer), S_{I,1}, S_{I,2},
                            S_{II} at U = 500√6·x^{1/3}, V = x^{1/3}/3
          ← MinMain1At 0.811 45.7575    (the first case, from the three pieces above)
          ← CoexistArith    NUMERIC: the first-case bound at a COEXISTING approximation
          minMain2L_of : PROVED — Dirichlet (Mathlib), the case split, the vaughan split at the
                            second choice, AND the coexistence argument (below)
 minMainP_of_links : PROVED, application only
```

The three NUMERIC links `CoexistArith`, `I1Arith` and `IIArith` are PROVED downstream
(`MPA.coexistArith` in `MinPiecesArith.lean`, `MPI1.i1Arith` in `MinPiecesI1.lean`,
`MPII.iiArith` in `MinPiecesII.lean`); `MPII.minMainP_of_open` is the Main Theorem from the links
still open.

## Finding — the book's second case has a gap, and it is closed here (`minMain2L_of`)

`minarctotals.tex` 1840-1843 takes a fresh Dirichlet approximation `a'/q'` at `Q' = x^{2/3}/500√6`
and asserts `q' > y` or `|δ'|q' > 8y`, "since otherwise `a'/q'` would already be a valid
approximation under the first choice". That is true but does not exclude it: the Main Theorem's
second case is hypothesised on an approximation `a/q` with `q > y`, and a first-choice-valid
`a'/q'` with `q' ≤ y` can COEXIST with it. `minMain2L_of` handles that branch: `a/q ≠ a'/q'`
(`q ∤ q'`), so `|a/q − a'/q'| ≥ 1/(qq')`, whence `|δ'|q' ≥ (4/3)x^{1/3} − 8/27`, and the FIRST
case at `a'/q'` applies. `CoexistArith` is the resulting numeric obligation: `krawAt 0.811 45.7575`
at `δ₀'q' ≈ x^{1/3}/3` against the second-case bound; scoped at max ratio `0.487`
(`scratchpad/minpieces/coexist.py`).

## Finding — `lem:bostb1`'s printed main term (T6)

Its proof (`typeI.tex` 1247-1260) produces `(x/2)·η̂(−δ/2)·Σ_{m odd, q|m} μ(m)/m·log(x/m)`, i.e.
`x/(2q)` and `−δ/2` with the μ-sums over `(m, 2q) = 1`; the statement prints `x/q` and `−δ` with
`(m, q) = 1`. `Bostb1At` carries the CORRECTED form. With `(m, 2q) = 1` the sums carry
`2q/φ(2q) = 2q/φ(q)` for odd `q`, so the printed `x/q` would DOUBLE the main term; `x/2q` is what
makes `(x/2q)·(2q/φ(q)) = x/φ(q)` match `MMP.bI1W`.

## Cited inputs consumed

`Grara` (Granville–Ramaré 1996 Lem 10.2), `Ronsard` and `Meproz` (Ramaré, Math. Comp. 2015):
literature proofs, NOT computer checks, so none of the `HC.*` definitions applies to them. The
`HC.*` computations that feed the pieces' deeper proofs (`HC.LambdaSmallCited`, `HC.KastCited`,
`HC.NotungCited`, `HC.CortoSmallCited`, `HC.MV8SmallCited`, `HC.YuttoSmallCited`,
`HC.RamareCited`, `HC.OdmalickaCited`, `HC.CameloGridCited`, `HC.WollustCited`) sit BELOW this
layer (inside `Bosta2Eta2`, `Vinland1At`, …) and are consumed when those links are split.
-/

namespace Principia.Common.TernaryGoldbach.MPc

open ArithmeticFunction Principia.Common.Goldbach
open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Principia.Common.TernaryGoldbach.MT

/-! ## (0) Constants and the μ-sums -/

/-- `c₀ = 31.521 ≥ |η̂₂''|_∞` (`lem:octet`; book `normfour.tex`). -/
noncomputable def c0 : ℝ := 31.521

/-- `c₂ = 6π/(5√c₀)` (`lem:bosta2`, `lem:bostb1`). -/
noncomputable def c2 : ℝ := 6 * Real.pi / (5 * Real.sqrt c0)

/-- `|η₂'|₁ = 8 log 2` (`eq:muggle`). -/
noncomputable def eta1 : ℝ := 8 * Real.log 2

/-- `c₁ = 1 + |η'|₁/(x/D)` (`lem:bosta2`, `lem:bostb1`). -/
noncomputable def c1 (x D : ℝ) : ℝ := 1 + eta1 * D / x

/-- `log⁺ t = max(log t, 0)`. -/
noncomputable def logp (t : ℝ) : ℝ := max (Real.log t) 0

/-- `∑_{n ≤ N, (n, k) = 1} μ(n)/n`. -/
noncomputable def muS (k : ℕ) (N : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 ⌊N⌋₊).filter (fun n => Nat.Coprime n k), ((μ n : ℤ) : ℝ) / n

/-- `∑_{n ≤ N, (n, k) = 1} (μ(n)/n)·log(z/n)`. -/
noncomputable def muL (k : ℕ) (N z : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 ⌊N⌋₊).filter (fun n => Nat.Coprime n k),
    ((μ n : ℤ) : ℝ) / n * Real.log (z / n)

/-- **CITED (literature) — `eq:grara`** (`minarcs.tex` 650; Granville–Ramaré, Mathematika 43
(1996), Lemma 10.2): `|∑_{n ≤ x, (n,q)=1} μ(n)/n| ≤ 1` for all `x` and `q ≥ 1`. -/
def Grara : Prop := ∀ (k : ℕ) (N : ℝ), 1 ≤ k → |muS k N| ≤ 1

/-- **CITED (literature) — `eq:ronsard`** (`minarcs.tex` 659; Ramaré, Math. Comp. 2015):
`|∑_{n ≤ x, (n,q)=1} μ(n)/n| ≤ (4/5)(q/φ(q))/log(x/q)` for `q ≤ x` (stated for `q < x`, where
the right side is finite). -/
def Ronsard : Prop :=
  ∀ (k : ℕ) (N : ℝ), 1 ≤ k → (k : ℝ) < N →
    |muS k N| ≤ 4 / 5 * ((k : ℝ) / Nat.totient k) / Real.log (N / k)

/-- **CITED (literature) — `eq:meproz`** (`minarcs.tex` 670; Ramaré, Math. Comp. 2015):
`|∑_{n ≤ x, (n,q)=1} (μ(n)/n) log(x/n)| ≤ 1.00303 q/φ(q)` for all `x` and `q ≥ 1`. -/
def Meproz : Prop :=
  ∀ (k : ℕ) (N : ℝ), 1 ≤ k → |muL k N N| ≤ 1.00303 * ((k : ℝ) / Nat.totient k)

/-- **`muL` splits**: `∑ (μ(n)/n) log(z/n) = log(z/N)·∑ μ(n)/n + ∑ (μ(n)/n) log(N/n)`. -/
theorem muL_split (k : ℕ) (N z : ℝ) (hN : 0 < N) (hz : 0 < z) :
    muL k N z = Real.log (z / N) * muS k N + muL k N N := by
  unfold muL muS
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have e : z / n = z / N * (N / n) := by field_simp
  rw [e, Real.log_mul (div_pos hz hN).ne' (div_pos hN hn0).ne']
  ring

/-! ## (1) `TypeI1W` — `lem:bostb1` at the first choice -/

/-- **The CORRECTED main term of `lem:bostb1`** (`typeI.tex` 1247-1260 with `x/2q`, `−δ/2`,
`(m, 2q) = 1`): `(x/2q)·min(1, c₀/(πδ)²)·|∑ μ(m)/m·log(x/mq)| + (x/2q)·min(2 − log 4,
96 log 2/(π²δ²))·|∑ μ(m)/m|`, sums over `m ≤ U/q`, `(m, 2q) = 1`. The factor
`min(2 − log 4, …)` is `|\widehat{log·η₂}(−δ/2)|`'s bound (`eq:madge` with `k = 2`, `eq:koasl`,
`lem:marengo`: `≤ min(2 − log 4, 24 log 2/(π²t²))` at `t = δ/2`). -/
noncomputable def mainI1 (x δ : ℝ) (q : ℕ) (U : ℝ) : ℝ :=
  x / (2 * q) * capM (c0 / Real.pi ^ 2) δ * |muL (2 * q) (U / q) (x / q)| +
    x / (2 * q) * ((2 - Real.log 4) * capM (96 * Real.log 2 / Real.pi ^ 2 / (2 - Real.log 4)) δ) *
      |muS (2 * q) (U / q)|

/-- The `O*` term of `eq:cupcake2`: `c₀(1/2 − 2/π²)(D²/(4qx)·log(√e·x/D) + 1/e)`. -/
noncomputable def errI1 (x : ℝ) (q : ℕ) (D : ℝ) : ℝ :=
  c0 * (1 / 2 - 2 / Real.pi ^ 2) *
    (D ^ 2 / (4 * q * x) * Real.log (Real.sqrt (Real.exp 1) * x / D) + 1 / Real.exp 1)

/-- **`eq:kuche2`** of `lem:bostb1` (book `typeI.tex` 1191-1202), `η = η₂`. -/
noncomputable def kuche2 (x : ℝ) (q : ℕ) (D : ℝ) : ℝ :=
  2 * Real.sqrt (c0 * c1 x D) / Real.pi * D * Real.log (Real.exp 1 * x / D) +
    3 * c1 x D / 2 * (x / q) * logp (D / (c2 * x / q)) * Real.log (q / c2) +
    (2 * eta1 / Real.pi *
          max 1 (Real.log (c0 * Real.exp 3 * (q : ℝ) ^ 2 / (4 * Real.pi * eta1 * x))) *
          Real.log x +
        2 * Real.sqrt (c0 * c1 x D) / Real.pi * (Real.sqrt 3 + logp (D / (q / 2)) / 2) *
          Real.log (q / c2)) * q +
    3 * c1 x D / 2 * Real.sqrt (2 * x / c2) * Real.log (2 * x / c2) +
    20 * c0 * c2 ^ ((3 : ℝ) / 2) / (3 * Real.pi ^ 2) * Real.sqrt (2 * x) *
      Real.log (2 * Real.sqrt (Real.exp 1) * x / c2)

/-- **Link [Bostb1At] — `lem:bostb1` for `η₂` at the first choice** (`ρ₀ = 4`, `D = U`,
`Q₀ = (3/4)x^{2/3}`, so `M = U` and, as `U ≤ Q₀/2`, the `eq:kuche2` branch holds for every `δ`),
with the CORRECTED main term (`mainI1`). OPEN: generic `lem:bostb1` (`typeI.tex` 1153-1478: T1
`lem:gotog`, T2 `lem:couscous`, T3 `lem:thina`, Poisson, `eq:ra`, `lem:areval`) plus
`eq:puella` for `η₂` (`eq:cloclo`) and `c₀ = 31.521` (`lem:octet`). -/
def Bostb1At : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ α δ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 →
    2 * α = a / q + δ / Y → (q : ℝ) ≤ 3 / 4 * Y ^ ((2 : ℝ) / 3) →
    |δ / Y| ≤ 1 / (q * (3 / 4 * Y ^ ((2 : ℝ) / 3))) → (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6 →
      ‖sI1 Y α (uA Y δ q)‖ ≤
        mainI1 Y δ q (uA Y δ q) + errI1 Y q (uA Y δ q) + kuche2 Y q (uA Y δ q)

/-- **Link [I1Arith] — NUMERIC: the Totals algebra for `S_{I,1}`** (`minarctotals.tex` 94-145,
1370-1446: `eq:cosI1 → eq:lavapie → eq:dikaiopolis → eq:therwald`): at every admissible
`(Y, δ, q)` and for any `s₀, s₁` obeying the three cited μ-bounds (at modulus `2q`, `N = U/q`),
the `Bostb1At` bound is at most `MMP.bI1W`. -/
def I1Arith : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ δ : ℝ, ∀ q : ℕ, 1 ≤ q → |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3) →
    (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6 → ∀ s0 s1 : ℝ, |s0| ≤ 1 →
    (((2 * q : ℕ) : ℝ) < uA Y δ q / q →
      |s0| ≤ 4 / 5 * (((2 * q : ℕ) : ℝ) / Nat.totient (2 * q)) /
        Real.log (uA Y δ q / q / ((2 * q : ℕ) : ℝ))) →
    |s1 - Real.log (Y / uA Y δ q) * s0| ≤ 1.00303 * (((2 * q : ℕ) : ℝ) / Nat.totient (2 * q)) →
      Y / (2 * q) * capM (c0 / Real.pi ^ 2) δ * |s1| +
          Y / (2 * q) *
              ((2 - Real.log 4) * capM (96 * Real.log 2 / Real.pi ^ 2 / (2 - Real.log 4)) δ) *
            |s0| +
          errI1 Y q (uA Y δ q) + kuche2 Y q (uA Y δ q) ≤
        MMP.bI1W Y δ q

/-- `U = x^{2/3}/(9√(qδ₀)) > 0`. -/
theorem uA_pos (Y δ : ℝ) (q : ℕ) (hY : 0 < Y) (hq : 1 ≤ q) : 0 < uA Y δ q := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd := dz_ge δ
  unfold uA
  exact div_pos (Real.rpow_pos_of_pos hY _)
    (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by nlinarith)))

/-- **`TypeI1W` from its links, PROVED.** -/
theorem typeI1W_of (hb : Bostb1At) (hg : Grara) (hr : Ronsard) (hm : Meproz) (ha : I1Arith) :
    MMP.TypeI1W := by
  intro Y hY α δ a q hq hg' h2 hQ hδ hy
  have hY0 : (0 : ℝ) < Y := by linarith
  have hdq := adm_dq Y δ q hY0 hq hδ
  have hU := uA_pos Y δ q hY0 hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have h2q : 1 ≤ 2 * q := by omega
  refine (hb Y hY α δ a q hq hg' h2 hQ hδ hy).trans ?_
  unfold mainI1
  refine ha Y hY δ q hq hdq hy (muS (2 * q) (uA Y δ q / q)) (muL (2 * q) (uA Y δ q / q) (Y / q))
    (hg _ _ h2q) (fun hlt => hr _ _ h2q hlt) ?_
  have hs := muL_split (2 * q) (uA Y δ q / q) (Y / q) (div_pos hU hqR) (div_pos hY0 hqR)
  have e : Y / q / (uA Y δ q / q) = Y / uA Y δ q := div_div_div_cancel_right₀ hqR.ne' Y _
  rw [e] at hs
  rw [hs, add_sub_cancel_left]
  exact hm _ _ h2q

/-! ## (2) `TypeI2` — `eq:jotoco` + `lem:bosta2` per `v` -/

/-- **The Type I sum of `lem:bosta2` for `η₂`** (`eq:gorio2`): `∑_{m ≤ D odd} μ(m)
∑_{n odd} e(βmn)η₂(mn/x)`, as the convolution piece `sP (f·μ_{≤D} ∗ f·1)` (`MT.sP_mul_eq` unfolds
it to the double sum). -/
noncomputable def gorio2 (x β D : ℝ) : ℂ :=
  sP (tw (aU D) * tw (ζ : ArithmeticFunction ℝ)) x β

/-- **`eq:asparto`** with the μ-sum `|∑_{m ≤ M/q, (m,2q)=1} μ(m)/m|` as the parameter `s`. -/
noncomputable def asparto (x δ : ℝ) (q : ℕ) (D s : ℝ) : ℝ :=
  x / (2 * q) * capM (c0 / Real.pi ^ 2) δ * |s| +
    c0 * q / x * (1 / 8 - 1 / (2 * Real.pi ^ 2)) * (D / q + 1) ^ 2

/-- **`eq:keks`** (book `typeI.tex` 1024-1032), `η = η₂`, `c₁ = 1 + |η'|₁/(x/D)`. -/
noncomputable def keks (x : ℝ) (q : ℕ) (D : ℝ) : ℝ :=
  2 * Real.sqrt (c0 * c1 x D) / Real.pi * D +
    3 * c1 x D / 2 * (x / q) * logp (D / (c2 * x / q)) +
    Real.sqrt (c0 * c1 x D) / Real.pi * q * logp (D / (q / 2)) +
    2 * eta1 / Real.pi * q *
      max 1 (Real.log (c0 * Real.exp 3 * (q : ℝ) ^ 2 / (4 * Real.pi * eta1 * x))) +
    (2 * Real.sqrt (3 * c0 * c1 x D) / Real.pi + 3 * c1 x D / (2 * c2) +
        55 * c0 * c2 / (6 * Real.pi ^ 2)) * q

/-- **`eq:kallervo2`** (book `typeI.tex` 1039-1048), `η = η₂`, for `ε ∈ (0, 1]`. -/
noncomputable def kallervo2 (x δ : ℝ) (q : ℕ) (D Q0 ε : ℝ) : ℝ :=
  2 * Real.sqrt (c0 * c1 x D) / Real.pi *
      (D + (1 + ε) * min ((⌊x / (|δ| * q)⌋₊ : ℝ) + 1) (2 * D) *
        (Real.sqrt (3 + 2 * ε) + logp (2 * D / (x / (|δ| * q))) / 2)) +
    3 / 2 * c1 x D * (2 + (1 + ε) / ε * logp (2 * D / (x / (|δ| * q)))) * (x / Q0) +
    35 * c0 * c2 / (3 * Real.pi ^ 2) * q

/-- **Link [Bosta2Eta2] — `lem:bosta2` for `η₂`, GENERIC** (book `typeI.tex` 1002-1050; minarcs
1724-1866): for `2β = a/q + δ/x`, `(a,q) = 1`, `|δ/x| ≤ 1/(qQ₀)`, `q ≤ Q₀`, `Q₀ ≥ 16`,
`1 ≤ D ≤ x`, there is `M ∈ [min(Q₀/2, D), D]` such that `|gorio2| ≤ eq:asparto + eq:keks` when
`|δ| ≤ 1/2c₂` or `D ≤ Q₀/2`, and `≤ eq:asparto + eq:kallervo2(ε)` for every `ε ∈ (0,1]` when
`|δ| ≥ 1/2c₂`. The μ-sum of `eq:asparto` is `muS (2q) (M/q)`. OPEN (T1, T2, T3, Poisson,
`eq:ra`, `lem:areval`, `c₀ = 31.521`). -/
def Bosta2Eta2 : Prop :=
  ∀ x β δ Q0 D : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 → 2 * β = a / q + δ / x →
    |δ / x| ≤ 1 / (q * Q0) → (q : ℝ) ≤ Q0 → 16 ≤ Q0 → 1 ≤ D → D ≤ x →
    ∃ M : ℝ, min (Q0 / 2) D ≤ M ∧ M ≤ D ∧
      ((|δ| ≤ 1 / (2 * c2) ∨ D ≤ Q0 / 2) →
        ‖gorio2 x β D‖ ≤ asparto x δ q D (muS (2 * q) (M / q)) + keks x q D) ∧
      (1 / (2 * c2) ≤ |δ| → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ‖gorio2 x β D‖ ≤ asparto x δ q D (muS (2 * q) (M / q)) + kallervo2 x δ q D Q0 ε)

/-- `q_v = q/(q, v)`. -/
def qv (q v : ℕ) : ℕ := q / Nat.gcd v q

/-- **The per-`v` bound fed to `I2Arith`**: `eq:asparto` at `(x/v, δ, q_v, U)` plus `eq:keks`
(`|δ| ≤ 1/2c₂`) or `eq:kallervo2` at `ε = 0.07` and `Q₀ = Q/v` (`|δ| > 1/2c₂`). -/
noncomputable def b2v (Y δ : ℝ) (q v : ℕ) (s : ℝ) : ℝ :=
  asparto (Y / v) δ (qv q v) (uA Y δ q) s +
    if |δ| ≤ 1 / (2 * c2) then keks (Y / v) (qv q v) (uA Y δ q)
    else kallervo2 (Y / v) δ (qv q v) (uA Y δ q) (3 / 4 * Y ^ ((2 : ℝ) / 3) / v) 0.07

/-- **Link [I2Arith] — NUMERIC: the Totals algebra for `S_{I,2}`** (`minarctotals.tex` 150-455,
1448-1550: `eq:putbarat + eq:douze | eq:cheaslu → eq:chusan + eq:fausto | eq:magus → eq:clums
→ eq:cleson`, at `ε = 0.07`): for any per-`v` bounds `T v` of the `lem:bosta2` shape (with the μ-sum
obeying `eq:grara` and `eq:ronsard` at modulus `2q_v`), `∑_{v ≤ V} Λ(v)f(v)T(v) ≤ MT.bI2`. Its
proof uses the cited Λ-bounds `eq:rala`, `eq:ralobio`, `eq:trado1`, `eq:trado2`, `eq:nicro`, and
the INTENDED `eq:charol` (`∑_{n≤y} Λ(n)/√n < 2·1.0004√y`; printed misstated). -/
def I2Arith : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ δ : ℝ, ∀ q : ℕ, 1 ≤ q → |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3) →
    (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6 → ∀ T : ℕ → ℝ,
    (∀ v : ℕ, 1 ≤ v → v ≤ ⌊vA Y⌋₊ → ∃ M s : ℝ,
      min (3 / 4 * Y ^ ((2 : ℝ) / 3) / v / 2) (uA Y δ q) ≤ M ∧ M ≤ uA Y δ q ∧ |s| ≤ 1 ∧
      (((2 * qv q v : ℕ) : ℝ) < M / (qv q v : ℕ) →
        |s| ≤ 4 / 5 * (((2 * qv q v : ℕ) : ℝ) / Nat.totient (2 * qv q v)) /
          Real.log (M / (qv q v : ℕ) / ((2 * qv q v : ℕ) : ℝ))) ∧
      T v ≤ b2v Y δ q v s) →
    ∑ v ∈ Finset.Ioc 0 ⌊vA Y⌋₊, Λ v * fOdd v * T v ≤ bI2 Y δ q

/-- **`eq:jotoco`, PROVED**: `S_{I,2} = ∑_{v ≤ x} (Λ_{≤V}f)(v)·gorio2(x/v, vα, U)`. -/
theorem sI2_split (x α U V : ℝ) :
    sI2 x α U V = ∑ v ∈ Finset.Ioc 0 ⌊x⌋₊,
      ((tw (bV V) v : ℝ) : ℂ) * gorio2 (x / v) (v * α) U := by
  have hc : tw (aU U) * tw (bV V) * tw (ζ : ArithmeticFunction ℝ) =
      tw (bV V) * (tw (aU U) * tw (ζ : ArithmeticFunction ℝ)) := by ring
  unfold sI2
  rw [hc]
  unfold sP
  rw [MinSum.sum_Ioc_mul_weight_eq_sum_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hv1 : 1 ≤ v := (Finset.mem_Ioc.mp hv).1
  have hv0 : (v : ℝ) ≠ 0 := by exact_mod_cast (by omega : v ≠ 0)
  congr 1
  unfold gorio2 sP
  rw [Nat.floor_div_natCast]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  unfold wt
  have e1 : ((v * m : ℕ) : ℝ) / x = (m : ℝ) / (x / v) := by
    push_cast
    field_simp
  have e2 : ((v * m : ℕ) : ℝ) * α = (m : ℝ) * (v * α) := by
    push_cast
    ring
  rw [e1, e2]

/-- `|(Λ_{≤V}f)(v)| ≤ Λ(v)f(v)`, and it vanishes for `v > V`. -/
theorem twbV_abs (V : ℝ) (v : ℕ) :
    |tw (bV V) v| = if v ≤ ⌊V⌋₊ then Λ v * fOdd v else 0 := by
  rw [tw_apply]
  unfold bV
  rw [MinSum.truncate_apply]
  split_ifs
  · exact abs_of_nonneg (mul_nonneg vonMangoldt_nonneg (fOdd_nonneg v))
  · simp

/-- **The per-`v` approximation, PROVED**: from `2α = a/q + δ/x` with `(a, q) = 1`,
`2(vα) = a_v/q_v + δ/(x/v)` with `q_v = q/(v,q)`, `a_v = (v/(v,q))·a`, `(a_v, q_v) = 1`. -/
theorem approx_v (x α δ : ℝ) (a : ℤ) (q v : ℕ) (hq : 1 ≤ q) (hv : 1 ≤ v)
    (hg : Int.gcd a q = 1) (h2 : 2 * α = a / q + δ / x) (hx : x ≠ 0) :
    1 ≤ qv q v ∧ qv q v ≤ q ∧ Int.gcd (((v / Nat.gcd v q : ℕ) : ℤ) * a) (qv q v) = 1 ∧
      2 * (v * α) = (((v / Nat.gcd v q : ℕ) : ℤ) * a : ℤ) / (qv q v : ℕ) + δ / (x / v) := by
  have hg0 : 0 < Nat.gcd v q := Nat.gcd_pos_of_pos_left q hv
  have hgq : Nat.gcd v q ∣ q := Nat.gcd_dvd_right v q
  have hgv : Nat.gcd v q ∣ v := Nat.gcd_dvd_left v q
  have hqv1 : 1 ≤ qv q v := by
    unfold qv
    exact Nat.div_pos (Nat.le_of_dvd (by omega) hgq) hg0
  have hqvq : qv q v ≤ q := Nat.div_le_self q _
  refine ⟨hqv1, hqvq, ?_, ?_⟩
  · have hc1 : Nat.Coprime (v / Nat.gcd v q) (q / Nat.gcd v q) :=
      Nat.coprime_div_gcd_div_gcd hg0
    have hc2 : Nat.Coprime a.natAbs (q / Nat.gcd v q) :=
      Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hgq) (by simpa [Int.gcd] using hg)
    rw [Int.gcd, Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.coprime_mul_iff_left.mpr ⟨hc1, hc2⟩
  · have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast (by omega : v ≠ 0)
    have hgR : ((Nat.gcd v q : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hg0.ne'
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    have ev : ((v / Nat.gcd v q : ℕ) : ℝ) = v / (Nat.gcd v q : ℕ) := Nat.cast_div hgv hgR
    have eq : ((qv q v : ℕ) : ℝ) = q / (Nat.gcd v q : ℕ) := Nat.cast_div hgq hgR
    rw [Int.cast_mul, Int.cast_natCast, ev, eq]
    have h2' : 2 * (v * α) = v * (2 * α) := by ring
    rw [h2', h2]
    field_simp

/-- `‖S_{I,2}‖ ≤ ∑_{v ≤ V} Λ(v)f(v)‖gorio2(x/v, vα, U)‖`, from `eq:jotoco`. -/
theorem sI2_norm_le (Y α U : ℝ) (hVY : ⌊vA Y⌋₊ ≤ ⌊Y⌋₊) :
    ‖sI2 Y α U (vA Y)‖ ≤ ∑ v ∈ Finset.Ioc 0 ⌊vA Y⌋₊,
      Λ v * fOdd v * ‖gorio2 (Y / v) (v * α) U‖ := by
  rw [sI2_split]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  have hf : (Finset.Ioc 0 ⌊Y⌋₊).filter (fun v => v ≤ ⌊vA Y⌋₊) = Finset.Ioc 0 ⌊vA Y⌋₊ := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    omega
  rw [← hf, Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, twbV_abs]
  split_ifs <;> simp

/-- `q·v ≤ Q = (3/4)x^{2/3}` for `q ≤ x^{1/3}/6`, `v ≤ V = (9/2)x^{1/3}` (`Q/V = y`). -/
theorem qv_mul_le (Y : ℝ) (hY0 : 0 < Y) (q v : ℝ) (hv : 0 ≤ v)
    (hy : q ≤ Y ^ ((1 : ℝ) / 3) / 6) (hvV : v ≤ vA Y) : q * v ≤ 3 / 4 * Y ^ ((2 : ℝ) / 3) := by
  obtain ⟨e23, -, e13, -, -⟩ := rpow_facts Y hY0
  unfold vA at hvV
  rw [e13] at hy hvV
  rw [e23]
  have h1 := mul_le_mul hy hvV hv (by positivity)
  nlinarith

/-- `Q/v ≥ Q/V = x^{1/3}/6 ≥ 16`. -/
theorem q16 (Y : ℝ) (hY : 3.4e23 ≤ Y) (v : ℝ) (hv : 0 < v) (hvV : v ≤ vA Y) :
    16 ≤ 3 / 4 * Y ^ ((2 : ℝ) / 3) / v := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨e23, -, e13, -, -⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  unfold vA at hvV
  rw [e13] at hvV
  rw [e23, le_div_iff₀ hv]
  have h2 : (8000 : ℝ) ^ 2 ≤ (Y ^ ((1 : ℝ) / 6)) ^ 2 := pow_le_pow_left₀ (by norm_num) hu 2
  nlinarith

/-- `|δ/(x/v)| ≤ 1/(q_v·(Q/v))` from `|δ/x| ≤ 1/(qQ)` and `q_v ≤ q`. -/
theorem delta_v (Y δ Q : ℝ) (hY0 : 0 < Y) (hQ : 0 < Q) (q qv' v : ℝ) (hqv : 0 < qv')
    (hqvq : qv' ≤ q) (hv : 0 < v) (hδ : |δ / Y| ≤ 1 / (q * Q)) :
    |δ / (Y / v)| ≤ 1 / (qv' * (Q / v)) := by
  have e1 : |δ / (Y / v)| = v * |δ / Y| := by
    rw [div_div_eq_mul_div, abs_div, abs_mul, abs_div, abs_of_pos hY0, abs_of_pos hv]
    ring
  have e2 : 1 / (qv' * (Q / v)) = v * (1 / (qv' * Q)) := by
    field_simp
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left (hδ.trans (one_div_le_one_div_of_le (by positivity)
    (mul_le_mul_of_nonneg_right hqvq hQ.le))) hv.le

/-- `U = u⁴/(9√(qδ₀))`, `u = x^{1/6}`. -/
theorem uA_eq (Y δ : ℝ) (q : ℕ) (hY0 : 0 < Y) :
    uA Y δ q = (Y ^ ((1 : ℝ) / 6)) ^ 4 / (9 * Real.sqrt (OC.dz δ * q)) := by
  obtain ⟨e23, -, -, -, -⟩ := rpow_facts Y hY0
  unfold uA
  rw [e23]

/-- `1 ≤ √(qδ₀) ≤ u` in the first case. -/
theorem sqrt_dq (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6) :
    1 ≤ Real.sqrt (OC.dz δ * q) ∧ Real.sqrt (OC.dz δ * q) ≤ Y ^ ((1 : ℝ) / 6) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, e13, -, -⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd2 := dz_ge δ
  have htx : OC.dz δ * q ≤ Y ^ ((1 : ℝ) / 3) / 3 := dz_q_le δ _ q hdq hy
  rw [e13] at htx
  constructor
  · exact Real.one_le_sqrt.mpr (by nlinarith)
  · rw [Real.sqrt_le_left (by linarith)]
    nlinarith

/-- `U ≥ 1` in the first case. -/
theorem uA_ge_one (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6) :
    1 ≤ uA Y δ q := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨h1, h2⟩ := sqrt_dq Y δ q hY hq hdq hy
  have hu := u_ge Y hY
  rw [uA_eq Y δ q hY0, le_div_iff₀ (by positivity)]
  have h3 : (8000 : ℝ) ^ 3 ≤ (Y ^ ((1 : ℝ) / 6)) ^ 3 := pow_le_pow_left₀ (by norm_num) hu 3
  nlinarith

/-- `U·V ≤ x` in the first case (`UV = x/(2√(qδ₀))`). -/
theorem uA_mul_vA (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6) :
    uA Y δ q * vA Y ≤ Y := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, e13, eY, -⟩ := rpow_facts Y hY0
  obtain ⟨h1, -⟩ := sqrt_dq Y δ q hY hq hdq hy
  have hu := u_ge Y hY
  rw [uA_eq Y δ q hY0]
  unfold vA
  rw [e13, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nth_rw 3 [eY]
  have h6 : 0 < (Y ^ ((1 : ℝ) / 6)) ^ 6 := by positivity
  nlinarith

/-- **`TypeI2` from its links, PROVED**: `eq:jotoco`, the triangle inequality, `lem:bosta2` at
every `v ≤ V` (scale `x/v`, angle `vα`, `Q₀ = Q/v`, `D = U`), `eq:grara`, `eq:ronsard`, and
`I2Arith`. -/
theorem typeI2_of (hb : Bosta2Eta2) (hg : Grara) (hr : Ronsard) (ha : I2Arith) : TypeI2 := by
  intro Y hY α δ a q hq hg' h2 hQ hδ hy
  have hY0 : (0 : ℝ) < Y := by linarith
  have hdq := adm_dq Y δ q hY0 hq hδ
  have hU := uA_pos Y δ q hY0 hq
  have hVY : ⌊vA Y⌋₊ ≤ ⌊Y⌋₊ := Nat.floor_le_floor (by linarith [vA_lt Y hY])
  refine (sI2_norm_le Y α (uA Y δ q) hVY).trans
    (ha Y hY δ q hq hdq hy _ fun v hv1 hvV => ?_)
  have hv0 : (0 : ℝ) < v := by exact_mod_cast hv1
  have hvV' : (v : ℝ) ≤ vA Y := le_trans (by exact_mod_cast hvV) (Nat.floor_le (by
    unfold vA; positivity))
  obtain ⟨hqv1, hqvq, hgv, h2v⟩ := approx_v Y α δ a q v hq hv1 hg' h2 hY0.ne'
  have hqv0 : (0 : ℝ) < (qv q v : ℕ) := by exact_mod_cast hqv1
  have hqvqR : ((qv q v : ℕ) : ℝ) ≤ q := by exact_mod_cast hqvq
  have hQ0 : (0 : ℝ) < 3 / 4 * Y ^ ((2 : ℝ) / 3) := by positivity
  have hdv := delta_v Y δ _ hY0 hQ0 q _ v hqv0 hqvqR hv0 hδ
  have hqvQ : ((qv q v : ℕ) : ℝ) ≤ 3 / 4 * Y ^ ((2 : ℝ) / 3) / v := by
    rw [le_div_iff₀ hv0]
    exact (mul_le_mul_of_nonneg_right hqvqR hv0.le).trans
      (qv_mul_le Y hY0 q v hv0.le hy hvV')
  have hUv : uA Y δ q ≤ Y / v := by
    rw [le_div_iff₀ hv0]
    exact (mul_le_mul_of_nonneg_left hvV' hU.le).trans (uA_mul_vA Y δ q hY hq hdq hy)
  obtain ⟨M, hM1, hM2, hsmall, hlarge⟩ :=
    hb (Y / v) (v * α) δ (3 / 4 * Y ^ ((2 : ℝ) / 3) / v) (uA Y δ q) _ (qv q v) hqv1 hgv h2v
      hdv hqvQ (q16 Y hY v hv0 hvV') (uA_ge_one Y δ q hY hq hdq hy) hUv
  refine ⟨M, muS (2 * qv q v) (M / (qv q v : ℕ)), hM1, hM2, hg _ _ (by omega),
    fun hlt => hr _ _ (by omega) hlt, ?_⟩
  unfold b2v
  split_ifs with hd
  · exact hsmall (Or.inl hd)
  · exact hlarge (le_of_lt (not_le.mp hd)) 0.07 (by norm_num) (by norm_num)

/-! ## (3) `TypeII` — `eq:vinland1` / `eq:eriksaga` at the first choice -/

/-- `κ₂ = 4√κ₁ ≤ 1.93768` (`minarctotals.tex` 579). -/
noncomputable def kap2 : ℝ := 1.93768

/-- `κ₆ = 0.60428` (`minarctotals.tex` 686, from `eq:velib`). -/
noncomputable def kap6 : ℝ := 0.60428

/-- `κ₇ = √2·κ₄/1000 ≤ 0.1281` (`minarctotals.tex` 704). -/
noncomputable def kap7 : ℝ := 0.1281

/-- `κ₉ = 8√(1.0172κ₁) ≤ 3.9086` (`minarctotals.tex` 522). -/
noncomputable def kap9 : ℝ := 3.9086

/-- **`eq:vinland1`** (`minarctotals.tex` 951-960). -/
noncomputable def vin1 (x U V : ℝ) (q : ℕ) : ℝ :=
  x / Real.sqrt (2 * Nat.totient q) *
      Real.sqrt ((Real.log (x / (U * V)) + Real.log (2 * q) *
          Real.log (1 + Real.log (x / (U * V)) / Real.log (V / (2 * q)))) *
        (kap6 * Real.log (x / (U * V)) + 2 * kap7)) +
    Real.sqrt 2 * kap2 * Real.sqrt ((q : ℝ) / Nat.totient q) *
      (1 + 1.15 * Real.sqrt (Real.log (2 * q) / Real.log (x / (2 * U * q)))) * (x / Real.sqrt U) +
    kap9 * (x / Real.sqrt V)

/-- **`eq:eriksaga`** (`minarctotals.tex` 993-1013), `ε₁ = x/(2UQ)`. -/
noncomputable def erik (x U V Q δ : ℝ) (q : ℕ) : ℝ :=
  2 * x / Real.sqrt (|δ| * Nat.totient q) *
      Real.sqrt (Real.log (x / (U * V)) + Real.log (|δ| * q * (1 + x / (2 * U * Q)) / 4) *
        Real.log (1 + Real.log (x / (U * V)) /
          Real.log (4 * V / (|δ| * (1 + x / (2 * U * Q)) * q)))) *
      Real.sqrt (kap6 * Real.log (x / (U * V)) + 2 * kap7) +
    kap2 * Real.sqrt (2 * q / Nat.totient q) *
      Real.sqrt (Real.log V / Real.log (2 * V / (|δ| * q))) * (x / Real.sqrt U) +
    kap9 * (x / Real.sqrt V)

/-- **Link [Vinland1At] — `eq:vinland1` at the first choice** (every `δ`; `q ≤ V/2θ` holds by
`eq:werto` with `θ = 27/8`). OPEN: the Type II chapter (`typeII.tex`: `lem:monro`, `lem:yutto`,
`eq:corto`, `eq:velib`, `prop:kraken`, the large sieve `LS`/`WLS`/`MI`, MV Lem 8) and
`subs:absur`. -/
def Vinland1At : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ α δ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 →
    2 * α = a / q + δ / Y → (q : ℝ) ≤ 3 / 4 * Y ^ ((2 : ℝ) / 3) →
    |δ / Y| ≤ 1 / (q * (3 / 4 * Y ^ ((2 : ℝ) / 3))) → (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6 →
      ‖sII Y α (uA Y δ q) (vA Y)‖ ≤ vin1 Y (uA Y δ q) (vA Y) q

/-- **Link [EriksagaAt] — `eq:eriksaga` at the first choice** (`|δ| ≥ 8`; `|δq| ≤ V/θ` holds by
`eq:werto`). OPEN, as `Vinland1At`. -/
def EriksagaAt : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ α δ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 →
    2 * α = a / q + δ / Y → (q : ℝ) ≤ 3 / 4 * Y ^ ((2 : ℝ) / 3) →
    |δ / Y| ≤ 1 / (q * (3 / 4 * Y ^ ((2 : ℝ) / 3))) → (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6 →
    8 ≤ |δ| →
      ‖sII Y α (uA Y δ q) (vA Y)‖ ≤ erik Y (uA Y δ q) (vA Y) (3 / 4 * Y ^ ((2 : ℝ) / 3)) δ q

/-- **Link [IIArith] — NUMERIC: the Totals algebra for `S_{II}`** (`minarctotals.tex` 1626-1717:
`eq:pell`, `eq:meli` → `eq:senorburns`), given `lem:merkel`'s `q/φ(q) ≤ ϝ(x^{1/3}/6)`. -/
def IIArith : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ δ : ℝ, ∀ q : ℕ, 1 ≤ q → |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3) →
    (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6 →
    (q : ℝ) / Nat.totient q ≤ MinSp.bigF (Y ^ ((1 : ℝ) / 3) / 6) →
      (|δ| < 8 → vin1 Y (uA Y δ q) (vA Y) q ≤ bII Y δ q) ∧
      (8 ≤ |δ| → erik Y (uA Y δ q) (vA Y) (3 / 4 * Y ^ ((2 : ℝ) / 3)) δ q ≤ bII Y δ q)

/-- `y = x^{1/3}/6 ≥ 3` for `x ≥ 3.4·10²³`. -/
theorem y_ge (Y : ℝ) (hY : 3.4e23 ≤ Y) : 3 ≤ Y ^ ((1 : ℝ) / 3) / 6 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, e13, -, -⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  rw [e13]
  nlinarith

/-- **`TypeII` from its links, PROVED** (`lem:merkel` from `GS.merkel_of_rs62`). -/
theorem typeII_of (hv : Vinland1At) (he : EriksagaAt) (ha : IIArith) (h15 : GS.RS62Thm15) :
    TypeII := by
  intro Y hY α δ a q hq hg h2 hQ hδ hy
  have hY0 : (0 : ℝ) < Y := by linarith
  have hdq := adm_dq Y δ q hY0 hq hδ
  have hF : (q : ℝ) / Nat.totient q ≤ MinSp.bigF (Y ^ ((1 : ℝ) / 3) / 6) :=
    (GS.merkel_of_rs62 h15 q hq _ (y_ge Y hY) hy).le
  obtain ⟨hs, hl⟩ := ha Y hY δ q hq hdq hy hF
  rcases lt_or_ge |δ| 8 with h8 | h8
  · exact (hv Y hY α δ a q hq hg h2 hQ hδ hy).trans (hs h8)
  · exact (he Y hY α δ a q hq hg h2 hQ hδ hy h8).trans (hl h8)

/-! ## (4) `MinMain2L` — the second choice and the coexisting approximation -/

/-- **`U` of the second choice** (`eq:elpozer`): `U = 500√6·x^{1/3}`. -/
noncomputable def u2 (Y : ℝ) : ℝ := 500 * Real.sqrt 6 * Y ^ ((1 : ℝ) / 3)

/-- **`V` of the second choice** (`eq:elpozer`): `V = x^{1/3}/3`. -/
noncomputable def v2 (Y : ℝ) : ℝ := Y ^ ((1 : ℝ) / 3) / 3

/-- **`Q` of the second choice** (`eq:elpozer`): `Q = x/U`. -/
noncomputable def q2 (Y : ℝ) : ℝ := Y / u2 Y

/-- **The second-choice hypotheses** (`minarctotals.tex` 1840-1846): `2α = a/q + δ/x`,
`(a,q) = 1`, `q ≤ Q'`, `|δ/x| ≤ 1/(qQ')`, and `q > y` or `|δ|q > 8y`. -/
def Adm2 (Y α δ : ℝ) (a : ℤ) (q : ℕ) : Prop :=
  1 ≤ q ∧ Int.gcd a q = 1 ∧ 2 * α = a / q + δ / Y ∧ (q : ℝ) ≤ q2 Y ∧
    |δ / Y| ≤ 1 / (q * q2 Y) ∧
      (Y ^ ((1 : ℝ) / 3) / 6 < q ∨ 4 / 3 * Y ^ ((1 : ℝ) / 3) < |δ| * q)

/-- **Link [SecI1At] — `|S_{I,1}|` at the second choice** (`minarctotals.tex` 1857-1901, from
`eq:lavapie` = `lem:bostb1`): `≤ 2.4719x^{2/3}log x + 0.00289x^{2/3}(log x)²`. OPEN. -/
def SecI1At : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ α δ : ℝ, ∀ a : ℤ, ∀ q : ℕ, Adm2 Y α δ a q →
    ‖sI1 Y α (u2 Y)‖ ≤
      2.4719 * Y ^ ((2 : ℝ) / 3) * Real.log Y + 0.00289 * Y ^ ((2 : ℝ) / 3) * Real.log Y ^ 2

/-- **Link [SecI2At] — `|S_{I,2}|` at the second choice** (`minarctotals.tex` 1905-1975,
`lem:bogus`): `≤ 1230.9x^{2/3}log x + 0.0006406x^{2/3}(log x)²`. OPEN. -/
def SecI2At : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ α δ : ℝ, ∀ a : ℤ, ∀ q : ℕ, Adm2 Y α δ a q →
    ‖sI2 Y α (u2 Y) (v2 Y)‖ ≤
      1230.9 * Y ^ ((2 : ℝ) / 3) * Real.log Y + 0.0006406 * Y ^ ((2 : ℝ) / 3) * Real.log Y ^ 2

/-- **Link [SecIIAt] — `|S_{II}|` at the second choice** (`minarctotals.tex` 1977-2235,
`eq:vinland2`, `eq:vinland3`, `eq:vinlandsaga`), LOOSENED: `≤ 0.34x^{5/6}(log x)^{3/2}`. The book
claims `0.275964` (`eq:hostoma`, from an unpublished interval run on a 15-term expression that the
planning fork could not reproduce at its arXiv value `0.272652`); `0.34` is what the composition
needs, and the book's claim implies it. OPEN. -/
def SecIIAt : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ α δ : ℝ, ∀ a : ℤ, ∀ q : ℕ, Adm2 Y α δ a q →
    ‖sII Y α (u2 Y) (v2 Y)‖ ≤ 0.34 * Y ^ ((5 : ℝ) / 6) * Real.log Y ^ ((3 : ℝ) / 2)

/-- **Link [CoexistArith] — NUMERIC: the first-case bound at a coexisting approximation**
(`minMain2L_of`, case B): if `q ≤ x^{1/3}/6` and `(4/3)x^{1/3} − 1 ≤ |δ|q ≤ (4/3)x^{1/3}`, then
`krawAt 0.811 45.7575` is at most the second-case bound (given `lem:merkel`). Scoped max ratio
`0.487` over `x ∈ [3.4·10²³, 10⁵⁰⁰⁰]` (`scratchpad/minpieces/coexist.py`). -/
def CoexistArith : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ δ : ℝ, ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6 →
    |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3) → 4 / 3 * Y ^ ((1 : ℝ) / 3) - 1 ≤ |δ| * q →
    (q : ℝ) / Nat.totient q ≤ MinSp.bigF (Y ^ ((1 : ℝ) / 3) / 6) →
      krawAt 0.811 45.7575 Y δ q ≤
        0.3409 * Y ^ ((5 : ℝ) / 6) * Real.log Y ^ ((3 : ℝ) / 2) +
          1522.5 * Y ^ ((2 : ℝ) / 3) * Real.log Y

/-- `V' = x^{1/3}/3 < x/4`. -/
theorem v2_lt (Y : ℝ) (hY : 3.4e23 ≤ Y) : v2 Y < Y / 4 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, e13, eY, -⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  unfold v2
  rw [e13]
  nth_rw 2 [eY]
  have h4 : (8000 : ℝ) ^ 4 ≤ (Y ^ ((1 : ℝ) / 6)) ^ 4 := pow_le_pow_left₀ (by norm_num) hu 4
  nlinarith [pow_pos (show (0 : ℝ) < Y ^ ((1 : ℝ) / 6) by linarith) 2]

/-- `(log x)^{3/2} = log x · √(log x)`. -/
theorem log_pow_three_halves (L : ℝ) (hL : 0 ≤ L) : L ^ ((3 : ℝ) / 2) = L * Real.sqrt L := by
  rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
    Real.rpow_add' hL (by norm_num), Real.rpow_one]

/-- **The second-case arithmetic, PROVED**: the three second-choice piece bounds plus
`|S_{0,2}| ≤ 3(log x + 1)` sum to at most the second-case bound of `MT.MinMain2L`. -/
theorem sec_sum_le (Y : ℝ) (hY : 3.4e23 ≤ Y) (a1 a2 a3 a4 : ℝ)
    (h1 : a1 ≤ 2.4719 * Y ^ ((2 : ℝ) / 3) * Real.log Y + 0.00289 * Y ^ ((2 : ℝ) / 3) *
      Real.log Y ^ 2)
    (h2 : a2 ≤ 1230.9 * Y ^ ((2 : ℝ) / 3) * Real.log Y + 0.0006406 * Y ^ ((2 : ℝ) / 3) *
      Real.log Y ^ 2)
    (h3 : a3 ≤ 0.34 * Y ^ ((5 : ℝ) / 6) * Real.log Y ^ ((3 : ℝ) / 2))
    (h4 : a4 ≤ 3 * (Real.log Y + 1)) :
    a1 + a2 + a3 + a4 ≤ 0.3409 * Y ^ ((5 : ℝ) / 6) * Real.log Y ^ ((3 : ℝ) / 2) +
      1522.5 * Y ^ ((2 : ℝ) / 3) * Real.log Y := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨e23, e56, -, -, eL⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  set L := Real.log Y with hL_def
  have hL2 := log_ge_two Y hY
  have hL0 : 0 ≤ L := by linarith
  rw [log_pow_three_halves L hL0] at h3 ⊢
  rw [e23] at h1 h2 ⊢
  rw [e56] at h3 ⊢
  -- `L = 6 log u ≤ 6u`, so `√L ≤ u/4`
  have hlu : Real.log u ≤ u := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hLu : L ≤ 6 * u := by rw [eL]; linarith
  have hsL : Real.sqrt L ≤ u / 4 := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hsL1 : 1 ≤ Real.sqrt L := Real.one_le_sqrt.mpr (by linarith)
  have hu4 : 0 < u ^ 4 := by positivity
  -- `L²u⁴ ≤ (L√L)u⁵/4`
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0
  have hLL : L ^ 2 * u ^ 4 ≤ L * Real.sqrt L * u ^ 5 / 4 := by
    have : L ^ 2 = L * Real.sqrt L * Real.sqrt L := by rw [mul_assoc, hsq]; ring
    rw [this]
    have h := mul_le_mul_of_nonneg_left hsL (by positivity : (0 : ℝ) ≤ L * Real.sqrt L * u ^ 4)
    nlinarith
  have h1u : (1 : ℝ) ≤ u ^ 4 := one_le_pow₀ (by linarith)
  have hlow : 3 * (L + 1) ≤ 100 * u ^ 4 * L := by nlinarith
  have hA : 0.0035306 * (L ^ 2 * u ^ 4) ≤ 0.0035306 * (L * Real.sqrt L * u ^ 5 / 4) :=
    mul_le_mul_of_nonneg_left hLL (by norm_num)
  have hP : 0 ≤ L * Real.sqrt L * u ^ 5 :=
    mul_nonneg (mul_nonneg hL0 (Real.sqrt_nonneg L)) (pow_pos (by linarith : (0 : ℝ) < u) 5).le
  have hLu4 : 0 ≤ u ^ 4 * L := mul_nonneg hu4.le hL0
  linarith

/-- **`|δ'/x| ≤ 1/(q'Q)` from `|δ'|q' ≤ (4/3)x^{1/3}`** (the converse of `MT.adm_dq`). -/
theorem adm_of_dq (Y δ : ℝ) (q : ℕ) (hY0 : 0 < Y) (hq : 1 ≤ q)
    (h : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) :
    |δ / Y| ≤ 1 / (q * (3 / 4 * Y ^ ((2 : ℝ) / 3))) := by
  obtain ⟨e23, -, e13, eY, -⟩ := rpow_facts Y hY0
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hu0 : 0 < Y ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hY0 _
  rw [e23, abs_div, abs_of_pos hY0, div_le_div_iff₀ hY0 (by positivity), one_mul]
  rw [e13] at h
  nth_rw 2 [eY]
  nlinarith [pow_pos hu0 4]

/-- **The coexistence bound, PROVED**: if `a/q` (`q > y`, `(a,q) = 1`) and `a'/q'` (`q' ≤ y`) both
approximate `2α` to within `1/(qQ)` and `1/(q'Q)`, `Q = (3/4)x^{2/3}`, then
`|δ'|q' ≥ (4/3)x^{1/3} − 1` for `δ' = x(2α − a'/q')`. -/
theorem coexist_lower (Y α : ℝ) (hY : 3.4e23 ≤ Y) (a a' : ℤ) (q q' : ℕ) (hq : 1 ≤ q)
    (hq' : 1 ≤ q') (hg : Int.gcd a q = 1) (hqQ : (q : ℝ) ≤ 3 / 4 * Y ^ ((2 : ℝ) / 3))
    (hδ : |2 * α - a / q| ≤ 1 / (q * (3 / 4 * Y ^ ((2 : ℝ) / 3))))
    (hy : Y ^ ((1 : ℝ) / 3) / 6 < q) (hy' : (q' : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6) :
    4 / 3 * Y ^ ((1 : ℝ) / 3) - 1 ≤ |Y * (2 * α - a' / q')| * q' := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨e23, -, e13, eY, -⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'R : (0 : ℝ) < q' := by exact_mod_cast hq'
  -- `a/q ≠ a'/q'`: otherwise `q ∣ q'`, but `q' < q`
  have hne : a * q' - a' * q ≠ 0 := by
    intro h0
    have hdvd : (q : ℤ) ∣ a * q' := ⟨a', by linarith⟩
    have hcop : IsCoprime (q : ℤ) a := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
      exact hg
    have hqq' : (q : ℤ) ∣ q' := hcop.dvd_of_dvd_mul_left hdvd
    have hle : (q : ℤ) ≤ q' := Int.le_of_dvd (by exact_mod_cast (by omega : 0 < q')) hqq'
    have hle' : (q : ℝ) ≤ q' := by exact_mod_cast hle
    linarith
  have h1 : (1 : ℝ) ≤ |((a * q' - a' * q : ℤ) : ℝ)| := by
    have : (1 : ℤ) ≤ |a * q' - a' * q| := Int.one_le_abs hne
    exact_mod_cast this
  have hsep : 1 / (q * q') ≤ |(a : ℝ) / q - a' / q'| := by
    have e : (a : ℝ) / q - a' / q' = ((a * q' - a' * q : ℤ) : ℝ) / (q * q') := by
      push_cast
      field_simp
    rw [e, abs_div, abs_of_pos (mul_pos hqR hq'R)]
    exact div_le_div_of_nonneg_right h1 (mul_pos hqR hq'R).le
  have htri : |(a : ℝ) / q - a' / q'| ≤ |2 * α - a / q| + |2 * α - a' / q'| := by
    have := abs_sub_le ((a : ℝ) / q) (2 * α) (a' / q')
    rw [abs_sub_comm ((a : ℝ) / q) (2 * α)] at this
    exact this
  have hQ0 : 0 < 3 / 4 * Y ^ ((2 : ℝ) / 3) := by positivity
  -- `|2α − a'/q'| ≥ 1/(qq') − 1/(qQ)`
  have hlow : 1 / (q * q') - 1 / (q * (3 / 4 * Y ^ ((2 : ℝ) / 3))) ≤ |2 * α - a' / q'| := by
    linarith
  -- multiply by `Yq'`
  have hmul : Y * q' * (1 / (q * q') - 1 / (q * (3 / 4 * Y ^ ((2 : ℝ) / 3)))) ≤
      |Y * (2 * α - a' / q')| * q' := by
    rw [abs_mul, abs_of_pos hY0]
    have := mul_le_mul_of_nonneg_left hlow (by positivity : (0 : ℝ) ≤ Y * q')
    linarith
  refine le_trans ?_ hmul
  -- `Y q'(1/(qq') − 1/(qQ)) = (Y/q)(1 − q'/Q) ≥ (Y/Q)(1 − y/Q)`
  rw [e23] at hqQ hmul ⊢
  rw [e13] at hy hy' ⊢
  have hQ4 : 0 < 3 / 4 * u ^ 4 := by positivity
  have e : Y * q' * (1 / (q * q') - 1 / (q * (3 / 4 * u ^ 4))) =
      Y / q * (1 - q' / (3 / 4 * u ^ 4)) := by
    field_simp
  rw [e]
  have hfac : 0 ≤ 1 - q' / (3 / 4 * u ^ 4) := by
    rw [sub_nonneg, div_le_one hQ4]
    nlinarith
  have hYq : Y / (3 / 4 * u ^ 4) ≤ Y / q := div_le_div_of_nonneg_left hY0.le hqR hqQ
  have hstep : Y / (3 / 4 * u ^ 4) * (1 - q' / (3 / 4 * u ^ 4)) ≤
      Y / q * (1 - q' / (3 / 4 * u ^ 4)) := mul_le_mul_of_nonneg_right hYq hfac
  refine le_trans ?_ hstep
  rw [eY]
  have e2 : u ^ 6 / (3 / 4 * u ^ 4) * (1 - q' / (3 / 4 * u ^ 4)) =
      4 / 3 * u ^ 2 - 16 / 9 * q' / u ^ 2 := by
    field_simp
    ring
  rw [e2]
  have hq'u : 16 / 9 * (q' : ℝ) / u ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  linarith

/-- **`MinMain2L` from its links, PROVED.** Dirichlet at `Q' = x^{2/3}/(500√6)`
(`Real.exists_rat_abs_sub_le_and_den_le`) gives `a'/q'`. **Case A** (`q' > y` or `|δ'|q' > 8y`):
the vaughan split at the second choice and `sec_sum_le`. **Case B** (the gap): `a'/q'` is a
first-choice approximation coexisting with `a/q`, the first case applies at it, and
`coexist_lower` + `CoexistArith` close. -/
theorem minMain2L_of (h1 : SecI1At) (h2 : SecI2At) (h3 : SecIIAt)
    (hm : MinMain1At 0.811 45.7575) (h15 : GS.RS62Thm15) (hc : CoexistArith) : MinMain2L := by
  intro Y hY α δ a q hq hg h2α hQ hδ hy
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨e23, -, e13, eY, -⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  have hs6 : Real.sqrt 6 ≤ 2.5 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs60 : 0 < Real.sqrt 6 := by positivity
  -- `Q' = x^{2/3}/(500√6) ≥ 1`
  have hU2 : 0 < u2 Y := by unfold u2; positivity
  have hq2 : q2 Y = (Y ^ ((1 : ℝ) / 6)) ^ 4 / (500 * Real.sqrt 6) := by
    unfold q2 u2
    rw [e13]
    nth_rw 1 [eY]
    field_simp
  have hq2ge : 1 ≤ q2 Y := by
    rw [hq2, le_div_iff₀ (by positivity)]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8000) hu 4]
  set n := ⌊q2 Y⌋₊ with hn_def
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hq2ge)
  obtain ⟨r, hr, hrden⟩ := Real.exists_rat_abs_sub_le_and_den_le (2 * α) (n_pos := hn1)
  set q' := r.den with hq'_def
  set a' := r.num with ha'_def
  have hq'1 : 1 ≤ q' := r.pos
  have hq'R : (0 : ℝ) < q' := by exact_mod_cast hq'1
  have hr_eq : (r : ℝ) = a' / q' := by
    rw [Rat.cast_def]
  have hg' : Int.gcd a' q' = 1 := r.reduced
  set δ' := Y * (2 * α - a' / q') with hδ'_def
  have h2' : 2 * α = a' / q' + δ' / Y := by
    rw [hδ'_def]
    field_simp
    ring
  have hnQ : (n : ℝ) ≤ q2 Y := Nat.floor_le (by linarith)
  have hQn : q2 Y < n + 1 := Nat.lt_floor_add_one _
  have hq'Q : (q' : ℝ) ≤ q2 Y := le_trans (by exact_mod_cast hrden) hnQ
  have hδ'Y : |δ' / Y| ≤ 1 / (q' * q2 Y) := by
    have e : δ' / Y = 2 * α - a' / q' := by rw [hδ'_def]; field_simp
    rw [e, ← hr_eq]
    refine hr.trans (one_div_le_one_div_of_le (by positivity) ?_)
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hQn.le (by positivity)
  by_cases hA : Y ^ ((1 : ℝ) / 3) / 6 < q' ∨ 4 / 3 * Y ^ ((1 : ℝ) / 3) < |δ'| * q'
  · -- Case A: the second choice
    have hadm : Adm2 Y α δ' a' q' := ⟨hq'1, hg', h2', hq'Q, hδ'Y, hA⟩
    have hsplit := vaughan_split Y α (u2 Y) (v2 Y) hY0
    rw [s0i_eq_zero Y α (v2 Y) hY0 (v2_lt Y hY), add_zero] at hsplit
    rw [hsplit]
    have n1 := norm_add_le (sI1 Y α (u2 Y) - sI2 Y α (u2 Y) (v2 Y) + sII Y α (u2 Y) (v2 Y))
      (s02 Y α)
    have n2 := norm_add_le (sI1 Y α (u2 Y) - sI2 Y α (u2 Y) (v2 Y)) (sII Y α (u2 Y) (v2 Y))
    have n3 := norm_sub_le (sI1 Y α (u2 Y)) (sI2 Y α (u2 Y) (v2 Y))
    have hsum := sec_sum_le Y hY _ _ _ _ (h1 Y hY α δ' a' q' hadm) (h2 Y hY α δ' a' q' hadm)
      (h3 Y hY α δ' a' q' hadm) (s02_norm_le Y α (by linarith))
    linarith
  · -- Case B: a first-choice approximation coexisting with `a/q`
    simp only [not_or, not_lt] at hA
    obtain ⟨hy', hdq'⟩ := hA
    have hqQ' : (q' : ℝ) ≤ 3 / 4 * Y ^ ((2 : ℝ) / 3) := by
      refine hy'.trans ?_
      rw [e13, e23]
      nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8000) hu 2]
    have hadm1 := adm_of_dq Y δ' q' hY0 hq'1 hdq'
    have hk := hm Y hY α δ' a' q' hq'1 hg' h2' hqQ' hadm1 hy'
    have hδq : |2 * α - a / q| ≤ 1 / (q * (3 / 4 * Y ^ ((2 : ℝ) / 3))) := by
      have e : 2 * α - a / q = δ / Y := by rw [h2α]; ring
      rw [e]
      exact hδ
    have hlow := coexist_lower Y α hY a a' q q' hq hq'1 hg hQ hδq hy hy'
    have hF : (q' : ℝ) / Nat.totient q' ≤ MinSp.bigF (Y ^ ((1 : ℝ) / 3) / 6) :=
      (GS.merkel_of_rs62 h15 q' hq'1 _ (y_ge Y hY) hy').le
    exact hk.trans (hc Y hY δ' q' hq'1 hy' hdq' hlow hF)

/-! ## (5) The top: `OP.MinMainP 0.811 45.7575` from the links -/

/-- **THE SPINE OF THE CORRECTED MAIN THEOREM, PROVED (application only).** -/
theorem minMainP_of_links (hb1 : Bostb1At) (hgr : Grara) (hro : Ronsard) (hme : Meproz)
    (hA1 : I1Arith) (hb2 : Bosta2Eta2) (hA2 : I2Arith) (hv1 : Vinland1At) (her : EriksagaAt)
    (hA3 : IIArith) (hs1 : SecI1At) (hs2 : SecI2At) (hs3 : SecIIAt) (hco : CoexistArith)
    (h15 : GS.RS62Thm15) : OP.MinMainP 0.811 45.7575 := by
  have t1 := typeI1W_of hb1 hgr hro hme hA1
  have t2 := typeI2_of hb2 hgr hro hA2
  have t3 := typeII_of hv1 her hA3 h15
  have m1 : MinMain1At 0.811 45.7575 :=
    MMP.minMain1_of_arithW 0.811 45.7575 MMP.arith_811W t1 t2 t3
  exact MMP.minMainP_of_piecesW t1 t2 t3 (minMain2L_of hs1 hs2 hs3 m1 h15 hco)

end Principia.Common.TernaryGoldbach.MPc
