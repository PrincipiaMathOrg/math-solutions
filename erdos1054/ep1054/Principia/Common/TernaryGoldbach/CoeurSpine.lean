/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.OstopSpine
import Principia.Common.PSieveBasic

set_option autoImplicit false

/-!
# The spine of `OC.CoeurY` (Helfgott `cor:coeur` at `δ₀ = 392`): C0 → C13, every gap named

Target: `OC.CoeurY η` (`OstopC.lean` 687) — for `x ≥ 4.9·10²⁶`, `150000 ≤ r < r₁(x/49)`,
`∫_{(0,1] ∩ 𝔐_{8,r+1}(x/49)} |S₁(α)|² ≤ (log(r+1) + 2.05315)/(log √x − 1.306476) · S`,
`S₁ = ∑_{p > √x} (log p)η(p/x)e(pα)`, `S = MinSp.sPr η x`. Source: `ternvin.tex` `cor:coeur`
(3418-3459, second form) from `prop:bellen` (2491-2603) and `prop:espagn` (2870-3301).

## The chain (plan `spines/minmain_spine.md` §3)

```
 C0   𝔐_{8,r+1}(x/49) = 𝔐_{392,r+1}(x)                         OC.arcs_y           PROVED
      𝔐_{δ₀,n}(x) = oeArcs(δ₀n/x, n);  392n/x = Q₀/(2Q²), Q = √(x/784)   arcs_eq_oe   PROVED
 C1   window: Q₀' = 2(r+1) ≥ 3·10⁵, 2Q ≥ 4.5·10⁵·Q₀', log Q₀' ≤ 0.54 log 2Q, Q₀ ≤ Q,
      2Q ≤ √x                                    win_t, win_rho, q0_le_q, twoQ_le  PROVED
 C2   Parseval ∫_{(0,1]}|S|² = ∑|aₙ|² for ∑|aₙ| < ∞               OS.parseval_Ioc     PROVED
 C3–C6 prop:bellen (arc disjointness, Bombieri's character identity, Selberg's identity,
      the G-swap), scale-free                                   PS.BellenG          NAMED here
 C8   eq:malito / eq:cante / c_E ∈ [1.3325822, 1.3325823]   Malito, Cante, CERange  NAMED
 C10–C12 prop:espagn on the CoeurY window, even q only        EspagnWin            NAMED
      (the published statement: Espagn;  Espagn → EspagnWin: espagnWin_of_espagn  PROVED)
 C13  B = (log 2Q₀ + c₊)/(log 2Q + c_E) ≤ H(r)  (cplus_ge, cminus_le)   b_le_h     PROVED
 coeurYc_of_links : BellenG → EspagnWin c₊ → c_E ≥ 1.3325822 → CoeurYc (log 2 + c₊ ≤ c⁺)
 coeurY_of_links  : BellenG → EspagnWin 1.36 → c_E ≥ 1.3325822 → OC.CoeurY η   (every η)
```

`BellenG` is the campaign-agnostic large sieve for primes over arcs; it is PROVED (or not) in
`Principia/Common/PSieve*.lean`, which this file does not import, so that the chain composes
by application before any of it is discharged. The junk case (`∑|aₙ| = ∞`, where `S₁ ≡ 0`) is
handled here, so the conclusion is for EVERY weight `η`, `HW.etaPlus` included.

## The window of `EspagnWin` (why it is not `prop:espagn`'s)

`prop:espagn` (2870) is stated for `Q₀ ≥ 10⁵`, `Q ≥ 20000Q₀`, `ρ = log Q₀/log Q ≤ 0.6`, every
`q ≤ Q₀`; its proof ends in a machine check over `q < 2.2·10¹⁰` (3273-3301: two weeks, one
core, unpublished C). `cor:coeur` at `δ₀ = 392` consumes it at `(Q₀', Q') = (2(r+1), 2√(x/784))`
only, and `prop:bellen` only at EVEN `q`. `EspagnWin` is exactly that: `Q₀ ≥ 3·10⁵`,
`Q ≥ 4.5·10⁵·Q₀`, `log Q₀ ≤ 0.54 log Q`, `q` even — the window facts are PROVED here (`win_t`,
`win_rho`; the true sup of `ρ` is `0.53625` at the threshold, `0.54` is used for margin). It is a
consequence of the published statement (`espagnWin_of_espagn`), and needs far less computation:
see the pricing in the file `scratchpad/coeur/price_cplus.py` quoted in the gate header.

## Not cited: the explicit `G_q(R)` error terms of Ramaré 2019 (Thm 3.1) and Akhilesh–Ramaré 2017

They would shrink the finite check further, but they rest on machine computations and a new
citation is the owner's call. They are NOT used or stated here.
-/

namespace Principia.Common.TernaryGoldbach.CY

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach
open Principia.Common.PSieve (gQ oeArcs BellenG eS)

/-! ## (1) The named inputs -/

/-- **`c_E = γ + ∑_p log p/(p(p−1))`** (`ternvin.tex` `eq:garno` 2669-2671). -/
noncomputable def cE : ℝ :=
  Real.eulerMascheroniConstant + ∑' p : Nat.Primes, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))

/-- **`f₁(d) = ∏_{p∣d}(1 + p^{−2/3})(1 + (p^{1/3} + p^{2/3})/(p(p−1)))^{−1}`** (`eq:assur`
2665-2667). -/
noncomputable def f1 (d : ℕ) : ℝ :=
  ∏ p ∈ d.primeFactors, (1 + (p : ℝ) ^ (-(2 : ℝ) / 3)) /
    (1 + ((p : ℝ) ^ ((1 : ℝ) / 3) + (p : ℝ) ^ ((2 : ℝ) / 3)) / ((p : ℝ) * ((p : ℝ) - 1)))

/-- **[C8] `eq:malito`** (Ramaré, Ann. SNS Pisa 22 (1995), Lem. 3.4; `ternvin.tex` 2658-2663):
`G_d(R) = (φ(d)/d)(log R + c_E + ∑_{p∣d} log p/p) + O*(7.284 R^{−1/3} f₁(d))` for all `d ≥ 1`,
`R ≥ 1`. NAMED (a proof, elementary; not formalized). Not on this file's composition path: it
feeds `EspagnWin` through the reduction `eq:elsyn → eq:karka → eq:luce` (2892-3015). -/
def Malito : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ R : ℝ, 1 ≤ R →
    |gQ d R - (d.totient : ℝ) / d * (Real.log R + cE + ∑ p ∈ d.primeFactors, Real.log p / p)| ≤
      7.284 * R ^ (-(1 : ℝ) / 3) * f1 d

/-- **[C8] `eq:cante`** (Ramaré 1995, Lem. 3.4; `ternvin.tex` 2633-2636): `G(R) ≤ log R + 1.4709`
for `R ≥ 1`. NAMED. -/
def Cante : Prop := ∀ R : ℝ, 1 ≤ R → gQ 1 R ≤ Real.log R + 1.4709

/-- **[C8] `c_E ∈ [1.3325822, 1.3325823]`** (Rosser–Schoenfeld 1962 (2.11); `ternvin.tex`
2670). NAMED (a numeric enclosure). `OC.cminus_le` is proved against the printed `1.3325822`. -/
def CERange : Prop := 1.3325822 ≤ cE ∧ cE ≤ 1.3325823

/-- **[C10–C12] `prop:espagn` as PUBLISHED** (`ternvin.tex` 2870-2877): for `Q ≥ 20000Q₀`,
`Q₀ ≥ 10⁵`, `ρ = log Q₀/log Q ≤ 0.6`, every `1 ≤ q ≤ Q₀`, `s ∈ [1, Q₀/q]`:
`G_q(Q₀/sq)/G_q(Q/sq) ≤ (log Q₀ + 1.36)/(log Q + c_E)`. Its proof ends in a machine check
(3273-3301, unpublished). NAMED; only its window `EspagnWin` is consumed. -/
def Espagn : Prop :=
  ∀ Q₀ Q : ℝ, 100000 ≤ Q₀ → 20000 * Q₀ ≤ Q → Real.log Q₀ / Real.log Q ≤ 0.6 →
    ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Q₀ → ∀ s : ℝ, 1 ≤ s → s ≤ Q₀ / q →
      gQ q (Q₀ / (s * q)) / gQ q (Q / (s * q)) ≤ (Real.log Q₀ + 1.36) / (Real.log Q + cE)

/-- **[C10–C12] `prop:espagn` on the `CoeurY` window, at a parametric `c₊`**: `Q₀ ≥ 3·10⁵`,
`Q ≥ 4.5·10⁵·Q₀`, `log Q₀ ≤ 0.54 log Q`, EVEN `q ≤ Q₀` (all `prop:bellen` consumes),
`s ∈ [1, Q₀/q]`: `G_q(Q₀/sq)/G_q(Q/sq) ≤ (log Q₀ + c₊)/(log Q + c_E)`. NAMED. At `c₊ = 1.36`
it follows from `Espagn` (`espagnWin_of_espagn`). -/
def EspagnWin (cp : ℝ) : Prop :=
  ∀ Q₀ Q : ℝ, 300000 ≤ Q₀ → 450000 * Q₀ ≤ Q → Real.log Q₀ ≤ 0.54 * Real.log Q →
    ∀ q : ℕ, Even q → 1 ≤ q → (q : ℝ) ≤ Q₀ → ∀ s : ℝ, 1 ≤ s → s ≤ Q₀ / q →
      gQ q (Q₀ / (s * q)) / gQ q (Q / (s * q)) ≤ (Real.log Q₀ + cp) / (Real.log Q + cE)

/-- **`OC.CoeurY` at a parametric numerator constant `c⁺`** (`OC.CoeurY = CoeurYc 2.05315`,
`coeurY_iff`). -/
def CoeurYc (cplus : ℝ) (ηp : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ r : ℕ, 150000 ≤ r → (r : ℝ) < MinSp.r1y (x / 49) →
    ∫ α in Set.Ioc (0 : ℝ) 1 ∩ Smooth.arcs 8 (r + 1) (x / 49), ‖OC.s1Sum ηp x α‖ ^ 2 ≤
      (Real.log ((r : ℝ) + 1) + cplus) / (Real.log (Real.sqrt x) - 1.306476) * MinSp.sPr ηp x

/-- **`OC.CoeurY` IS `CoeurYc 2.05315`**, by `Iff.rfl`. -/
theorem coeurY_iff (ηp : ℝ → ℝ) : OC.CoeurY ηp ↔ CoeurYc 2.05315 ηp := Iff.rfl

/-- **The published `prop:espagn` gives the window**: `3·10⁵ ≥ 10⁵`, `4.5·10⁵ ≥ 2·10⁴`,
`log Q₀ ≤ 0.54 log Q` with `log Q > 0` gives `ρ ≤ 0.54 ≤ 0.6`, and even `q` is a sub-case. -/
theorem espagnWin_of_espagn (h : Espagn) : EspagnWin 1.36 := by
  intro Q₀ Q h0 h1 h2 q _ hq1 hq2 s hs1 hs2
  have hQ0 : (0 : ℝ) < Q₀ := by linarith
  have hQ : (1 : ℝ) < Q := by nlinarith
  have hlQ : 0 < Real.log Q := Real.log_pos hQ
  refine h Q₀ Q (by linarith) (by nlinarith) ?_ q hq1 hq2 s hs1 hs2
  rw [div_le_iff₀ hlQ]
  linarith

/-! ## (2) C0: the arcs are the odd/even family -/

/-- **`𝔐_{δ₀,n}(x) = oeArcs(δ₀n/x, n)`**: the half-widths `δ₀n/(2qx)`, `δ₀n/(qx)` are
`h/(2q)`, `h/q` at `h = δ₀n/x`. -/
theorem arcs_eq_oe (δ₀ : ℝ) (n : ℕ) (x : ℝ) :
    Smooth.arcs δ₀ n x = oeArcs (δ₀ * n / x) n := by
  have w1 : ∀ q : ℕ, δ₀ * n / (2 * q * x) = δ₀ * n / x / (2 * q) := fun q => by ring
  have w2 : ∀ q : ℕ, δ₀ * n / (q * x) = δ₀ * n / x / q := fun q => by ring
  ext α
  simp only [Smooth.arcs, oeArcs, Set.mem_union, Set.mem_iUnion, Set.mem_Icc, w1, w2,
    exists_prop]
  constructor
  · rintro (⟨q, ⟨h1, h2⟩, ho, rest⟩ | ⟨q, ⟨h1, h2⟩, he, rest⟩)
    · exact Or.inl ⟨q, ⟨h1, by exact_mod_cast h2, ho⟩, rest⟩
    · exact Or.inr ⟨q, ⟨h1, by exact_mod_cast h2, he⟩, rest⟩
  · rintro (⟨q, ⟨h1, h2, ho⟩, rest⟩ | ⟨q, ⟨h1, h2, he⟩, rest⟩)
    · exact Or.inl ⟨q, ⟨h1, by exact_mod_cast h2⟩, ho, rest⟩
    · exact Or.inr ⟨q, ⟨h1, by exact_mod_cast h2⟩, he, rest⟩

/-- **`392n/x = n/(2Q²)`** at `Q = √(x/784)`, `x > 0`. -/
theorem h392 (n x : ℝ) (hx : 0 < x) :
    392 * n / x = n / (2 * Real.sqrt (x / 784) ^ 2) := by
  rw [Real.sq_sqrt (by positivity)]
  field_simp
  ring

/-! ## (3) C1: the window, from `u = y^{1/30}`, `y = x/49 ≥ 10²⁵` -/

/-- `u^30 = y` for `u = y^{1/30}`, `y ≥ 0`. -/
theorem u_pow30 (y : ℝ) (hy : 0 ≤ y) : (y ^ ((1 : ℝ) / 30)) ^ (30 : ℕ) = y := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
  norm_num

/-- `y^{k/30} = (y^{1/30})^k`. -/
theorem rpow_k30 (y : ℝ) (hy : 0 ≤ y) (k : ℕ) :
    y ^ ((k : ℝ) / 30) = (y ^ ((1 : ℝ) / 30)) ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
  congr 1
  ring

/-- **`u ≥ 6.81`** for `u = y^{1/30}`, `y ≥ 10²⁵` (`6.81³⁰ < 10²⁵`). -/
theorem u_ge (y : ℝ) (hy : 10 ^ 25 ≤ y) : 6.81 ≤ y ^ ((1 : ℝ) / 30) := by
  have hy0 : 0 ≤ y := le_trans (by norm_num) hy
  by_contra hlt
  push Not at hlt
  have hu0 : 0 ≤ y ^ ((1 : ℝ) / 30) := Real.rpow_nonneg hy0 _
  have h1 : (y ^ ((1 : ℝ) / 30)) ^ (30 : ℕ) < (6.81 : ℝ) ^ (30 : ℕ) :=
    pow_lt_pow_left₀ hlt hu0 (by norm_num)
  rw [u_pow30 y hy0] at h1
  have h2 : (6.81 : ℝ) ^ (30 : ℕ) < 10 ^ 25 := by norm_num
  linarith

/-- `r₁(y) = (3/8)u⁸`. -/
theorem r1y_eq (y : ℝ) (hy : 0 ≤ y) : MinSp.r1y y = 3 / 8 * (y ^ ((1 : ℝ) / 30)) ^ 8 := by
  unfold MinSp.r1y
  rw [← rpow_k30 y hy 8]
  norm_num

/-- `2√(x/784) = u¹⁵/2` at `y = x/49`. -/
theorem twoQ_eq (x : ℝ) (hx : 0 ≤ x) :
    2 * Real.sqrt (x / 784) = ((x / 49) ^ ((1 : ℝ) / 30)) ^ 15 / 2 := by
  have hy : 0 ≤ x / 49 := by positivity
  have e1 : x / 784 = x / 49 / 4 ^ 2 := by norm_num; ring
  rw [e1, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4 ^ 2), Real.sqrt_sq (by norm_num),
    Real.sqrt_eq_rpow, ← rpow_k30 _ hy 15]
  norm_num
  ring

/-- `u⁸ ≥ 10⁴` and `u⁷ ≥ 679000` from `u ≥ 6.81`. -/
theorem u_pows (u : ℝ) (hu : 6.81 ≤ u) : 10000 ≤ u ^ 8 ∧ 679000 ≤ u ^ 7 := by
  have hu0 : (0 : ℝ) ≤ 6.81 := by norm_num
  have h8 := pow_le_pow_left₀ hu0 hu 8
  have h7 := pow_le_pow_left₀ hu0 hu 7
  constructor
  · exact le_trans (by norm_num) h8
  · exact le_trans (by norm_num) h7

/-- **[C1] `2Q ≥ 4.5·10⁵·Q₀'`**: `4.5·10⁵·2(r+1) ≤ 2√(x/784)` for `r < r₁(x/49)`,
`x ≥ 4.9·10²⁶` (margin `0.9 %` at the threshold, growing like `y^{7/30}`). -/
theorem win_t (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (r : ℕ) (hr : (r : ℝ) < MinSp.r1y (x / 49)) :
    450000 * (2 * ((r : ℝ) + 1)) ≤ 2 * Real.sqrt (x / 784) := by
  have hx0 := MinSp.x_pos x hx
  have hy := MinSp.y_ge x hx
  have hy0 : 0 ≤ x / 49 := by positivity
  set u := (x / 49) ^ ((1 : ℝ) / 30) with hu
  have hu1 : 6.81 ≤ u := u_ge _ hy
  obtain ⟨h8, h7⟩ := u_pows u hu1
  rw [r1y_eq _ hy0] at hr
  rw [twoQ_eq x hx0.le]
  have h15 : u ^ 15 = u ^ 8 * u ^ 7 := by ring
  have h87 : u ^ 8 * 679000 ≤ u ^ 8 * u ^ 7 :=
    mul_le_mul_of_nonneg_left h7 (by positivity)
  linarith

/-- **[C1] `ρ ≤ 0.54`**: `log(2(r+1)) ≤ 0.54·log(2√(x/784))` for `r < r₁(x/49)`,
`x ≥ 4.9·10²⁶` (true sup `0.53625`). -/
theorem win_rho (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (r : ℕ) (hr : (r : ℝ) < MinSp.r1y (x / 49)) :
    Real.log (2 * ((r : ℝ) + 1)) ≤ 0.54 * Real.log (2 * Real.sqrt (x / 784)) := by
  have hx0 := MinSp.x_pos x hx
  have hy := MinSp.y_ge x hx
  have hy0 : 0 ≤ x / 49 := by positivity
  set u := (x / 49) ^ ((1 : ℝ) / 30) with hu
  have hu1 : 6.81 ≤ u := u_ge _ hy
  have hu0 : 0 < u := by linarith
  obtain ⟨h8, -⟩ := u_pows u hu1
  rw [r1y_eq _ hy0] at hr
  rw [twoQ_eq x hx0.le, ← hu]
  have hA : 2 * ((r : ℝ) + 1) ≤ 0.7502 * u ^ 8 := by linarith
  have hr0 : (0 : ℝ) < 2 * ((r : ℝ) + 1) := by positivity
  have hl1 : Real.log (2 * ((r : ℝ) + 1)) ≤ Real.log (0.7502 * u ^ 8) :=
    Real.log_le_log hr0 hA
  have hu8 : u ^ 8 ≠ 0 := by positivity
  have hu15 : u ^ 15 ≠ 0 := by positivity
  rw [Real.log_mul (by norm_num : (0.7502 : ℝ) ≠ 0) hu8, Real.log_pow] at hl1
  rw [Real.log_div hu15 (by norm_num : (2 : ℝ) ≠ 0), Real.log_pow]
  have hc : Real.log 0.7502 ≤ 0.7502 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have hl4 : 2 * Real.log 2 ≤ Real.log u := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num; linarith)
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  push_cast at hl1 ⊢
  nlinarith

/-- **[C1] `Q₀ ≤ Q`**: `r + 1 ≤ √(x/784)` (from `win_t`). -/
theorem q0_le_q (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (r : ℕ) (hr : (r : ℝ) < MinSp.r1y (x / 49)) :
    (r : ℝ) + 1 ≤ Real.sqrt (x / 784) := by
  have h := win_t x hx r hr
  have h0 : (0 : ℝ) ≤ (r : ℝ) + 1 := by positivity
  nlinarith

/-- **[C1] `2Q ≤ √x`**: `2√(x/784) = √x/14`. -/
theorem twoQ_le (x : ℝ) : 2 * Real.sqrt (x / 784) ≤ Real.sqrt x := by
  have e : x / 784 = x / 28 ^ 2 := by norm_num
  rw [e, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 28 ^ 2), Real.sqrt_sq (by norm_num)]
  have := Real.sqrt_nonneg x
  linarith

/-! ## (4) C13: the constants -/

/-- **`log 2Q = log 2 + log √x − log 28`** at `Q = √(x/784)`, `x > 0`. -/
theorem log_twoQ (x : ℝ) (hx : 0 < x) :
    Real.log (2 * Real.sqrt (x / 784)) = Real.log 2 + Real.log (Real.sqrt x) - Real.log 28 := by
  have e : x / 784 = x / 28 ^ 2 := by norm_num
  rw [e, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 28 ^ 2), Real.sqrt_sq (by norm_num),
    Real.log_mul (by norm_num) (by positivity), Real.log_div (by positivity) (by norm_num)]
  ring

/-- **[C13] `B ≤ H(r)`**: `(log 2Q₀ + c₊)/(log 2Q + c_E) ≤ (log Q₀ + c⁺)/(log √x − 1.306476)`
from `log 2 + c₊ ≤ c⁺`, `c_E ≥ 1.3325822` (`OC.cminus_le`), `D = log √x − 1.306476 > 7`
(`OS.dh_pos`), `Q₀ ≥ 1`, `c₊ ≥ 0`. -/
theorem b_le_h (cp cplus : ℝ) (hcp0 : 0 ≤ cp) (hcp : Real.log 2 + cp ≤ cplus)
    (hce : 1.3325822 ≤ cE) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (Q₀ : ℝ) (hQ0 : 1 ≤ Q₀) :
    (Real.log (2 * Q₀) + cp) / (Real.log (2 * Real.sqrt (x / 784)) + cE) ≤
      (Real.log Q₀ + cplus) / (Real.log (Real.sqrt x) - 1.306476) := by
  have hx0 := MinSp.x_pos x hx
  have hD := OS.dh_pos x hx
  have hcm := OC.cminus_le
  have hl2 := Real.log_two_gt_d9
  have hlq : 0 ≤ Real.log Q₀ := Real.log_nonneg hQ0
  rw [log_twoQ x hx0, Real.log_mul (by norm_num) (by linarith)]
  have hden : Real.log (Real.sqrt x) - 1.306476 ≤
      Real.log 2 + Real.log (Real.sqrt x) - Real.log 28 + cE := by linarith
  have hDpos : 0 < Real.log (Real.sqrt x) - 1.306476 := by linarith
  calc (Real.log 2 + Real.log Q₀ + cp) / (Real.log 2 + Real.log (Real.sqrt x) - Real.log 28 + cE)
      ≤ (Real.log 2 + Real.log Q₀ + cp) / (Real.log (Real.sqrt x) - 1.306476) :=
        div_le_div_of_nonneg_left (by linarith) hDpos hden
    _ ≤ (Real.log Q₀ + cplus) / (Real.log (Real.sqrt x) - 1.306476) :=
        div_le_div_of_nonneg_right (by linarith) hDpos.le

/-! ## (5) The composition -/

/-- The coefficients of `S₁` are supported on primes `> √x`, hence coprime to every
`1 ≤ m ≤ √x`. -/
theorem a1_coprime (η : ℝ → ℝ) (x : ℝ) (n : ℕ) (hn : OS.a1 η x n ≠ 0) (m : ℕ) (hm : 1 ≤ m)
    (hmx : (m : ℝ) ≤ Real.sqrt x) : Nat.Coprime n m := by
  classical
  have hp : n.Prime ∧ Real.sqrt x < (n : ℝ) := by
    by_contra h
    exact hn (by simp only [OS.a1, if_neg h])
  have hmn : m < n := by exact_mod_cast lt_of_le_of_lt hmx hp.2
  refine (Nat.Prime.coprime_iff_not_dvd hp.1).mpr fun hd => ?_
  have := Nat.le_of_dvd (by omega) hd
  omega

/-- `c₊ = 1.36 ≥ 0`. -/
theorem cp136_nonneg : (0 : ℝ) ≤ 1.36 := by norm_num

/-- **[C13] `CoeurYc` from the links**: `BellenG` at `Q₀ = r + 1`, `Q = √(x/784)`, fed by
`EspagnWin c₊` at `(2Q₀, 2Q)` (window: `win_t`, `win_rho`), Parseval (`OS.parseval_Ioc`),
and `b_le_h`. The junk case `∑|aₙ| = ∞` gives `S₁ ≡ 0`. -/
theorem coeurYc_of_links (cp cplus : ℝ) (hcp0 : 0 ≤ cp) (hcp : Real.log 2 + cp ≤ cplus)
    (hbel : BellenG) (hesp : EspagnWin cp) (hce : 1.3325822 ≤ cE) (ηp : ℝ → ℝ) :
    CoeurYc cplus ηp := by
  intro x hx r hr0 hr
  have hx0 := MinSp.x_pos x hx
  have hD := OS.dh_pos x hx
  have hl2 := Real.log_two_gt_d9
  set Q₀ : ℝ := (r : ℝ) + 1 with hQ₀
  set Q : ℝ := Real.sqrt (x / 784) with hQ
  have hr0R : (150000 : ℝ) ≤ r := by exact_mod_cast hr0
  have hQ01 : 1 ≤ Q₀ := by rw [hQ₀]; linarith
  have hQ0Q : Q₀ ≤ Q := q0_le_q x hx r hr
  have hH0 : 0 ≤ (Real.log Q₀ + cplus) / (Real.log (Real.sqrt x) - 1.306476) :=
    div_nonneg (by linarith [Real.log_nonneg hQ01]) (by linarith)
  have hS0 := MinSp.sPr_nonneg ηp x
  have harc : Set.Ioc (0 : ℝ) 1 ∩ Smooth.arcs 8 (r + 1) (x / 49) =
      Set.Ioc (0 : ℝ) 1 ∩ oeArcs (Q₀ / (2 * Q ^ 2)) Q₀ := by
    rw [OC.arcs_y, arcs_eq_oe, ← h392 _ x hx0]
    push_cast
    rfl
  rw [harc]
  simp_rw [OS.s1Sum_eq]
  by_cases hs : Summable fun n => ‖OS.a1 ηp x n‖
  · set B := (Real.log (2 * Q₀) + cp) / (Real.log (2 * Q) + cE) with hB
    have hBle : B ≤ (Real.log Q₀ + cplus) / (Real.log (Real.sqrt x) - 1.306476) :=
      b_le_h cp cplus hcp0 hcp hce x hx Q₀ hQ01
    have hsupp : ∀ n : ℕ, OS.a1 ηp x n ≠ 0 → ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ 2 * Q →
        Nat.Coprime n m := fun n hn m hm hmQ =>
      a1_coprime ηp x n hn m hm (le_trans hmQ (twoQ_le x))
    have hrat : ∀ q : ℕ, Even q → 1 ≤ q → (q : ℝ) ≤ 2 * Q₀ → ∀ s : ℝ, 1 ≤ s →
        s ≤ 2 * Q₀ / q → gQ q (2 * Q₀ / (s * q)) ≤ B * gQ q (2 * Q / (s * q)) := by
      intro q hqe hq1 hq2 s hs1 hs2
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
      have hsq : 0 < s * q := by positivity
      have hge : 1 ≤ 2 * Q / (s * q) := by
        rw [le_div_iff₀ hsq]
        have : s * q ≤ 2 * Q₀ := by rwa [le_div_iff₀ hq0] at hs2
        linarith
      have hG := Principia.Common.PSieve.one_le_gQ q _ hge
      have h := hesp (2 * Q₀) (2 * Q) (by linarith) (by rw [hQ₀, hQ]; exact win_t x hx r hr)
        (by rw [hQ₀, hQ]; exact win_rho x hx r hr) q hqe hq1 hq2 s hs1 hs2
      rwa [div_le_iff₀ (by linarith)] at h
    have hmain := hbel (OS.a1 ηp x) Q₀ Q B hs hQ01 hQ0Q hsupp hrat
    have hpar : ∫ α in Set.Ioc (0 : ℝ) 1, ‖eS (OS.a1 ηp x) α‖ ^ 2 = MinSp.sPr ηp x := by
      have h := OS.parseval_Ioc (OS.a1 ηp x) hs
      rw [OS.sq_a1] at h
      exact h
    have hmain' : ∫ α in Set.Ioc (0 : ℝ) 1 ∩ oeArcs (Q₀ / (2 * Q ^ 2)) Q₀,
        ‖OS.eSum (OS.a1 ηp x) α‖ ^ 2 ≤ B * MinSp.sPr ηp x := by
      rw [← hpar]
      exact hmain
    exact le_trans hmain' (mul_le_mul_of_nonneg_right hBle hS0)
  · have h0 : ∀ α, OS.eSum (OS.a1 ηp x) α = 0 := OS.eSum_junk _ hs
    simp_rw [h0, norm_zero]
    refine le_trans (le_of_eq ?_) (mul_nonneg hH0 hS0)
    simp

/-- **`OC.CoeurY η` for EVERY weight `η`, from the named links**: `coeurYc_of_links` at
`c₊ = 1.36`, `c⁺ = 2.05315` (`OC.cplus_ge`). OPEN: `BellenG`, `EspagnWin 1.36`, and the lower
half of `CERange` (the upper half is not consumed). -/
theorem coeurY_of_links (hbel : BellenG) (hesp : EspagnWin 1.36) (hce : 1.3325822 ≤ cE)
    (ηp : ℝ → ℝ) : OC.CoeurY ηp :=
  coeurYc_of_links 1.36 2.05315 cp136_nonneg OC.cplus_ge hbel hesp hce ηp

/-- **`OC.CoeurY HW.etaPlus`** (Helfgott's `η₊`) from the named links. -/
theorem coeurY_helf (hbel : BellenG) (hesp : EspagnWin 1.36) (hce : 1.3325822 ≤ cE) :
    OC.CoeurY HW.etaPlus :=
  coeurY_of_links hbel hesp hce HW.etaPlus

/-- **From the PUBLISHED `prop:espagn`**: `OC.CoeurY η` from `BellenG`, `Espagn`,
`c_E ≥ 1.3325822`. -/
theorem coeurY_of_espagn (hbel : BellenG) (hesp : Espagn) (hce : 1.3325822 ≤ cE)
    (ηp : ℝ → ℝ) :
    OC.CoeurY ηp :=
  coeurY_of_links hbel (espagnWin_of_espagn hesp) hce ηp

end Principia.Common.TernaryGoldbach.CY
