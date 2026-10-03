/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MajorR
import Principia.Common.TernaryGoldbach.PerArcSpine
import Principia.Common.TernaryGoldbach.MNumLEnv
import Principia.Common.TernaryGoldbach.TotientSq
import Principia.Common.TernaryGoldbach.OstopSpine

set_option autoImplicit false

/-!
# `OL.CoprarL η* φ` PROVED from the retyped major arcs (`MR.HelfMajR`)

**Target** (`OstopL.lean`): on the annulus `A₀ = 𝔐^{(y)}_{8,r₀} ∖ 𝔐^{(x)}_{8,r₀}` (`OC.annA0`,
`y = x/49`, `r₀ = 150000`), `|S_{η*}(α,x)| ≤ (g̃_L(y,r₀) + C_{φ,3}(K))·|φ|₁·y`.
`coprarL_of_R : RT.PlattFull → MR.HelfMajR η₊ (η₂ ∗_M φ) → OL.CoprarL η* φ` — every link below
is PROVED; the only input is `MR.CoprarR` for the base `η_c = η₂ ∗_M φ`, read off `HelfMajR`.

## The spine

```
 decode    α ∈ A₀ ⇒ α = a/q + δ/x, (a,q) = 1, q ≤ 3·10⁵, 600000/q ≤ |δ| ≤ 49·(q,2)·600000/q
                                                                   annA0_decode, reduce_num
 expand    |S_η(a/q+δ/x)| ≤ (1+√q)B + xE + x|η̂(δ)|/φ(q)   (eq:beatit, PA's eight links)  sm_le
 E         √q*·|err_{η*,χ*}(δ,x)| ≤ 2.1941·10⁻⁷/49 on the WIDE δ-range (CoprarR at y)  eb_wide
 B         B ≤ 15.84√x   (|η*(t)| ≤ 0.3√x(3/4)^k at t = p^{k+1}/x;  ∑_{p|q} log p ≤ 13.2)  bNon_le
 decay     |η̂₂(ν)| ≤ 2.2/|ν|  (integration by parts on [1/4,1/2], [1/2,1])            eta2Decay
           |η̂_c(ω)| ≤ 2.2/|ω|  (Fubini: η̂_c(ω) = ∫φ(y)η̂₂(ωy)dy, ∫y e^{-y²/2} = 1)     mcDecay_of
           η̂*(δ) = η̂_c(δ/49)/49                                                         ft_star
 q/φ(q)    q ≤ 8.54 φ(q) for q ≤ 3·10⁵  (TotientSq's Euler product, (101/100)⁴·70)     q_le_tot
 level     (g̃_L(y,r₀) + C_{φ,3})|φ|₁ ≥ 0.00572 (g_Y(t) ≥ 2.5/√(2t), GS.gtlInt)       levelFloor
 close     |S_{η*}| ≤ 3.1318·10⁻⁵ x ≤ 0.00572·x/49                                 coprarL_of_links
```

## Constants and margins (units of `y = x/49`; floating point in `scratchpad/coprar/price.py`)

* principal term `y·|η̂_c(ω)|/φ(q)` at `|ω| ≥ 12244.9/q`: certified `≤ 2.2·8.54·49/600000 =
  1.5344·10⁻³`; the numerics give about `6.0·10⁻⁵` (worst sampled `q = 60060`).
* the characters' error `xE`: `2.1941·10⁻⁷`.
* the non-coprime mass `(1+√q)B`: `≤ 548.7226·15.84·7/√y ≤ 1.93·10⁻⁸`.
* **total `≤ 1.5346·10⁻³`** (`close_arith`: `3.1318·10⁻⁵x`).
* **level `≥ 0.00572`** (`2.5/√300000·√(π/2) = 0.0057206`); the coordinator's value is about
  `0.041` at `y = 10^(10⁶)` and `0.0530` at `y = 10²⁵`.

Margin `0.00572/1.5346·10⁻³ = 3.73×`. The losses are deliberate: `q/φ(q) ≤ 8.54` (true max
`5.2135` at `q = 30030`), `|η̂₂(ν)|·|ν| ≤ 2.2` (true sup `0.613`), and the level keeps only the
`2.5/√(2r)` summand of `g_Y`.

## Two points of care

* **The lower edge of `δ` is the SAME arc's `x`-width.** `α ∉ 𝔐^{(x)}` is used only at the
  `(q,a)` that puts `α` in `𝔐^{(y)}`, giving `|δ| ≥ 600000/q` (odd; `1.2·10⁶/q` even). That is
  what makes the principal term small: `|η̂_c(δ/49)| ≤ 2.2·49/|δ| ≤ 2.2·49q/600000`, and `q/φ(q)`
  is bounded, so `|δ|` is never needed to be LARGE, only `≥ 600000/q`.
* **`E` on the wide range.** `MR.eb_starR` bounds `err_{η*}` only for `|δ| ≤ (q,2)·600000/q`;
  here `|δ|` reaches `49×` that. At scale `y` it is `|δ/49| ≤ (q,2)·600000/q ≤ 1.2·10⁶/q*`, inside
  `CoprarR`'s `4·300000/q*`, so the same `star_numR` arithmetic applies (`eb_wide`).
-/

namespace Principia.Common.TernaryGoldbach.CP

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach
open scoped ArithmeticFunction

/-! ## (0) The analytic links, as propositions (each PROVED below) -/

/-- **[Eta2Decay]** `|η̂₂(ν)| ≤ 2.2/|ν|` (`η₂` is `C¹` on `[1/4,1/2]`, `[1/2,1]`, `|η₂'| ≤ 16`,
`η₂(1/4) = η₂(1) = 0`, `η₂(1/2) = 4 log 2`; the constant is `(8 log 2 + 8)/(2π) = 2.1558`).
PROVED (`eta2Decay`). -/
def Eta2Decay : Prop := ∀ ν : ℝ, ν ≠ 0 → ‖MajSp.mainFT HW.eta2 ν‖ ≤ 2.2 / |ν|

/-- **[McDecay]** `|η̂_c(ω)| ≤ 2.2/|ω|` for the base `η_c = η₂ ∗_M φ` of `η*`. PROVED from
`Eta2Decay` (`mcDecay_of`). -/
def McDecay : Prop :=
  ∀ ω : ℝ, ω ≠ 0 → ‖MajSp.mainFT (HW.mconv HW.eta2 HW.phi) ω‖ ≤ 2.2 / |ω|

/-- **[LevelFloor]** the right side of `OL.CoprarL` is at least `0.00572·y`. PROVED
(`levelFloor`). -/
def LevelFloor : Prop :=
  ∀ y : ℝ, 10 ^ 25 ≤ y → 0.00572 * y ≤
    (OL.gTL HW.phi y 150000 + MinSp.cPhi3 HW.phi (MinSp.kK y)) * MajSp.l1 HW.phi * y

/-! ## (1) Exponential sums: integer shifts and junk -/

/-- `e(m) = 1` for every integer `m`. -/
theorem e_intCast (m : ℤ) : e (m : ℝ) = 1 := by
  simp only [e]
  rw [show (2 * Real.pi * Complex.I * ((m : ℝ) : ℂ)) = (m : ℂ) * (2 * Real.pi * Complex.I) by
    push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I m

/-- `S_η(β + k, x) = S_η(β, x)` for `k ∈ ℤ`. -/
theorem smSum_add_int (η : ℝ → ℝ) (x β : ℝ) (k : ℤ) :
    Smooth.smSum η x (β + k) = Smooth.smSum η x β := by
  unfold Smooth.smSum
  refine tsum_congr fun n => ?_
  have h : e ((n : ℝ) * (β + k)) = e ((n : ℝ) * β) := by
    rw [mul_add, ← e_add, show (n : ℝ) * (k : ℝ) = (((n : ℤ) * k : ℤ) : ℝ) by push_cast; ring,
      e_intCast, mul_one]
  rw [h]

/-- **Junk**: if `∑ Λ(n)|η(n/x)|` diverges, `S_η(α, x) = 0`. -/
theorem smSum_junk (η : ℝ → ℝ) (x α : ℝ)
    (h : ¬ Summable fun n : ℕ => Λ n * |η ((n : ℝ) / x)|) : Smooth.smSum η x α = 0 := by
  unfold Smooth.smSum
  refine tsum_eq_zero_of_not_summable fun hs => h ?_
  refine (summable_norm_iff.mpr hs).congr fun n => ?_
  rw [norm_mul, norm_mul, e_norm, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg vonMangoldt_nonneg, Real.norm_eq_abs]

/-! ## (2) Decoding the annulus -/

/-- `|d| < W`, `W·x = c` give `|d·x| ≤ c`. -/
theorem abs_mul_le_of (d W x c : ℝ) (hx : 0 < x) (h1 : -W < d) (h2 : d < W) (hW : W * x = c) :
    |d * x| ≤ c := by
  rw [abs_mul, abs_of_pos hx, ← hW]
  exact mul_le_mul_of_nonneg_right (abs_lt.mpr ⟨h1, h2⟩).le hx.le

/-- `¬(|d| < W)`, `W·x = c` give `c ≤ |d·x|`. -/
theorem le_abs_mul_of (d W x c : ℝ) (hx : 0 < x) (hW : W * x = c)
    (hno : ¬ (-W < d ∧ d < W)) : c ≤ |d * x| := by
  by_contra hlt'
  have hlt := not_le.mp hlt'
  apply hno
  rw [abs_mul, abs_of_pos hx, ← hW] at hlt
  exact abs_lt.mp (lt_of_mul_lt_mul_right hlt hx.le)

/-- **The annulus in coordinates**: `α ∈ A₀` is `a/q + δ/x` with `(a,q) = 1`, `q ≤ 3·10⁵` and
`600000/q ≤ |δ| ≤ 49·(q,2)·600000/q` — the upper edge from the `y`-arc containing `α`, the lower
from `α` missing the `x`-arc of the SAME `(q,a)`. -/
theorem annA0_decode (x α : ℝ) (hx : 0 < x) (h : α ∈ OC.annA0 x) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ 300000 ∧ ∃ a : ℤ, Int.gcd a q = 1 ∧ ∃ δ : ℝ,
      α = a / q + δ / x ∧ 600000 / q ≤ |δ| ∧ |δ| ≤ 49 * (Nat.gcd q 2 : ℝ) * 600000 / q := by
  obtain ⟨-, hin, hout⟩ := h
  simp only [Smooth.arcs, Set.mem_union, Set.mem_iUnion, Set.mem_Ioo] at hin
  have hxe : ∀ a : ℤ, ∀ q : ℕ, α = a / q + (α - a / q) * x / x := fun a q => by
    rw [mul_div_assoc, div_self hx.ne', mul_one]
    ring
  rcases hin with ⟨q, hq, ho, a, ha, h1, h2⟩ | ⟨q, hq, he, a, ha, h1, h2⟩
  · have hq1 : 1 ≤ q := hq.1
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
    have hg : Nat.gcd q 2 = 1 := Nat.coprime_two_right.mpr ho
    refine ⟨q, hq1, le_trans hq.2 (by norm_num), a, ha, (α - a / q) * x, hxe a q, ?_, ?_⟩
    · refine le_abs_mul_of _ (8 * (150000 : ℕ) / (2 * q * x)) x _ hx ?_ fun hk => hout ?_
      · field_simp
        norm_num
      · simp only [Smooth.arcs, Set.mem_union, Set.mem_iUnion, Set.mem_Ioo]
        exact Or.inl ⟨q, hq, ho, a, ha, by linarith [hk.1], by linarith [hk.2]⟩
    · rw [hg]
      refine abs_mul_le_of _ (8 * (150000 : ℕ) / (2 * q * (x / 49))) x _ hx (by linarith)
        (by linarith) ?_
      field_simp
      norm_num
  · have hq1 : 1 ≤ q := hq.1
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
    have hg : Nat.gcd q 2 = 2 := Nat.gcd_eq_right (even_iff_two_dvd.mp he)
    refine ⟨q, hq1, le_trans hq.2 (by norm_num), a, ha, (α - a / q) * x, hxe a q, ?_, ?_⟩
    · have hc : 600000 / (q : ℝ) ≤ 8 * (150000 : ℕ) / q := by
        rw [div_le_div_iff_of_pos_right hq0]
        norm_num
      refine le_trans hc (le_abs_mul_of _ (8 * (150000 : ℕ) / (q * x)) x _ hx ?_ fun hk => hout ?_)
      · field_simp
      · simp only [Smooth.arcs, Set.mem_union, Set.mem_iUnion, Set.mem_Ioo]
        exact Or.inr ⟨q, hq, he, a, ha, by linarith [hk.1], by linarith [hk.2]⟩
    · rw [hg]
      refine abs_mul_le_of _ (8 * (150000 : ℕ) / (q * (x / 49))) x _ hx (by linarith)
        (by linarith) ?_
      field_simp
      norm_num

/-- **The numerator reduced mod `q`**: `a/q = b/q + k` with `b ∈ ℕ`, `(b,q) = 1`, `k ∈ ℤ`. -/
theorem reduce_num (q : ℕ) (hq : 1 ≤ q) (a : ℤ) (ha : Int.gcd a q = 1) :
    ∃ b : ℕ, Nat.Coprime b q ∧ ∃ k : ℤ, (a : ℝ) / q = (b : ℝ) / q + k := by
  have hq0 : (0 : ℤ) < q := by exact_mod_cast hq
  have hnn : 0 ≤ a % q := Int.emod_nonneg a hq0.ne'
  have hb : ((a % q).toNat : ℤ) = a % q := Int.toNat_of_nonneg hnn
  refine ⟨(a % q).toNat, ?_, a / q, ?_⟩
  · have h1 : Int.gcd (a % q) q = 1 := by rw [Int.gcd_emod]; exact ha
    rw [← hb, Int.gcd_natCast_natCast] at h1
    exact h1
  · have hqR : (q : ℝ) ≠ 0 := by positivity
    have h2 : a = a % q + q * (a / q) := (Int.emod_add_mul_ediv a q).symm
    have h3 : (a : ℝ) = ((a % q : ℤ) : ℝ) + (q : ℝ) * ((a / q : ℤ) : ℝ) := by exact_mod_cast h2
    have h4 : (((a % q).toNat : ℕ) : ℝ) = ((a % q : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, hb]
    rw [h4, h3]
    field_simp

/-! ## (3) The character expansion (`eq:beatit`), generic in the weight -/

/-- **`|S_η(a/q + δ/x)| ≤ (1+√q)B + xE + x|η̂(δ)|/φ(q)`** for `(a,q) = 1`, given
`√q*·|err_{η,χ*}(δ,x)| ≤ E` for every `χ` mod `q`. `S = X_a + O*(B)` (`PA.beatIt`),
`|S_χ − S_{χ*}| ≤ B` (`PA.toPrimitive`), `|τ(χ̄)|² ≤ q* ≤ q` (`PA.gauss`), `S_{χ*} = x·err` for
`χ ≠ χ₀` and `x(η̂ + err)` for `χ₀`; `φ(q)` characters. -/
theorem sm_le (η : ℝ → ℝ) (x δ : ℝ) (q : ℕ) [NeZero q] (hx : 0 < x)
    (hs : Summable fun n : ℕ => Λ n * |η ((n : ℝ) / x)|) (a : ℕ) (ha : Nat.Coprime a q) (E : ℝ)
    (hE : ∀ χ : DirichletCharacter ℂ q,
      Real.sqrt (χ.conductor : ℝ) * ‖MajSp.err η χ.primitiveCharacter δ x‖ ≤ E) :
    ‖Smooth.smSum η x ((a : ℝ) / q + δ / x)‖ ≤
      (1 + Real.sqrt q) * PA.bNon η x q + x * E + x * ‖MajSp.mainFT η δ‖ / q.totient := by
  classical
  have hB0 := (PA.massLink η x q (NeZero.ne q) hs).1
  set B := PA.bNon η x q with hBdef
  set F := ‖MajSp.mainFT η δ‖ with hF
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hsq0 := Real.sqrt_nonneg (q : ℝ)
  have hterm : ∀ χ : DirichletCharacter ℂ q,
      ‖gaussSum χ⁻¹ ZMod.stdAddChar * PA.tw η x δ χ / (q.totient : ℂ) * χ (a : ZMod q)‖ ≤
        (x * E + Real.sqrt q * B) / q.totient + (if χ = 1 then x * F / q.totient else 0) := by
    intro χ
    have hχa : ‖χ (a : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hτ : ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ≤ Real.sqrt χ.conductor := by
      rw [← Real.sqrt_sq (norm_nonneg (gaussSum χ⁻¹ ZMod.stdAddChar))]
      exact Real.sqrt_le_sqrt ((PA.gauss q).2.1 χ)
    have hcq : (χ.conductor : ℝ) ≤ q := by
      exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
    have hsq : Real.sqrt χ.conductor ≤ Real.sqrt q := Real.sqrt_le_sqrt hcq
    have hτ0 := norm_nonneg (gaussSum χ⁻¹ ZMod.stdAddChar)
    have htw : ‖PA.tw η x δ χ‖ ≤ ‖PA.twP η x δ χ‖ + B := by
      have h1 := PA.toPrimitive η x δ q hs χ
      have h2 := norm_sub_norm_le (PA.tw η x δ χ) (PA.twP η x δ χ)
      linarith
    have hEχ := hE χ
    have hP : ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ * ‖PA.twP η x δ χ‖ ≤
        x * E + (if χ = 1 then x * F else 0) := by
      by_cases h1 : χ = 1
      · have hc : χ.conductor = 1 := DirichletCharacter.eq_one_iff_conductor_eq_one.mp h1
        have htwP : PA.twP η x δ χ =
            (x : ℂ) * (MajSp.err η χ.primitiveCharacter δ x + MajSp.mainFT η δ) := by
          unfold MajSp.err
          rw [if_pos hc]
          unfold PA.twP
          field_simp
          ring
        have hc1 : Real.sqrt (χ.conductor : ℝ) = 1 := by rw [hc, Nat.cast_one, Real.sqrt_one]
        rw [hc1, one_mul] at hEχ
        rw [hc1] at hτ
        rw [if_pos h1, htwP, norm_mul, Complex.norm_real, Real.norm_of_nonneg hx.le]
        have hn := norm_add_le (MajSp.err η χ.primitiveCharacter δ x) (MajSp.mainFT η δ)
        have hk : ‖MajSp.err η χ.primitiveCharacter δ x + MajSp.mainFT η δ‖ ≤ E + F := by
          rw [hF]
          linarith
        calc ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ *
              (x * ‖MajSp.err η χ.primitiveCharacter δ x + MajSp.mainFT η δ‖)
            ≤ 1 * (x * (E + F)) :=
              mul_le_mul hτ (mul_le_mul_of_nonneg_left hk hx.le) (by positivity) zero_le_one
          _ = x * E + x * F := by ring
      · have hc : χ.conductor ≠ 1 :=
          fun h => h1 (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)
        have htwP : PA.twP η x δ χ = (x : ℂ) * MajSp.err η χ.primitiveCharacter δ x := by
          unfold MajSp.err
          rw [if_neg hc, sub_zero]
          unfold PA.twP
          field_simp
        rw [if_neg h1, add_zero, htwP, norm_mul, Complex.norm_real, Real.norm_of_nonneg hx.le]
        calc ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ * (x * ‖MajSp.err η χ.primitiveCharacter δ x‖)
            = x * (‖gaussSum χ⁻¹ ZMod.stdAddChar‖ * ‖MajSp.err η χ.primitiveCharacter δ x‖) := by
              ring
          _ ≤ x * (Real.sqrt χ.conductor * ‖MajSp.err η χ.primitiveCharacter δ x‖) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hτ (norm_nonneg _)) hx.le
          _ ≤ x * E := mul_le_mul_of_nonneg_left hEχ hx.le
    have hT : ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ * ‖PA.tw η x δ χ‖ ≤
        x * E + Real.sqrt q * B + (if χ = 1 then x * F else 0) := by
      calc ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ * ‖PA.tw η x δ χ‖
          ≤ ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ * (‖PA.twP η x δ χ‖ + B) :=
            mul_le_mul_of_nonneg_left htw hτ0
        _ = ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ * ‖PA.twP η x δ χ‖ +
            ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ * B := by ring
        _ ≤ (x * E + (if χ = 1 then x * F else 0)) + Real.sqrt q * B :=
            add_le_add hP (mul_le_mul_of_nonneg_right (hτ.trans hsq) hB0)
        _ = x * E + Real.sqrt q * B + (if χ = 1 then x * F else 0) := by ring
    rw [norm_mul, norm_div, norm_mul, Complex.norm_natCast]
    have hA0 : 0 ≤ ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ * ‖PA.tw η x δ χ‖ / (q.totient : ℝ) :=
      div_nonneg (mul_nonneg hτ0 (norm_nonneg _)) hφ.le
    calc ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ * ‖PA.tw η x δ χ‖ / (q.totient : ℝ) * ‖χ (a : ZMod q)‖
        ≤ ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ * ‖PA.tw η x δ χ‖ / (q.totient : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hχa hA0
      _ ≤ (x * E + Real.sqrt q * B + (if χ = 1 then x * F else 0)) / (q.totient : ℝ) := by
          rw [mul_one]
          exact div_le_div_of_nonneg_right hT hφ.le
      _ = (x * E + Real.sqrt q * B) / q.totient +
            (if χ = 1 then x * F / q.totient else 0) := by
          split_ifs <;> ring
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hX : ‖PA.xMain η x δ q (a : ZMod q)‖ ≤ (x * E + Real.sqrt q * B) + x * F / q.totient := by
    unfold PA.xMain
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun χ _ => hterm χ).trans (le_of_eq ?_))
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul,
      Finset.sum_ite_eq' Finset.univ (1 : DirichletCharacter ℂ q), if_pos (Finset.mem_univ _)]
    field_simp
  have h1 := PA.beatIt η x δ q hs a ha
  have h2 := norm_le_norm_add_norm_sub' (Smooth.smSum η x ((a : ℝ) / q + δ / x))
    (PA.xMain η x δ q (a : ZMod q))
  have e1 : (1 + Real.sqrt q) * B = B + Real.sqrt q * B := by ring
  rw [e1]
  linarith

/-! ## (4) `E` for `η*` on the WIDE `δ`-range, from `CoprarR` at scale `y = x/49` -/

/-- **`√q*·|err_{η*,χ*}(δ,x)| ≤ 2.1941·10⁻⁷/49`** for every `χ` mod `q ≤ 3·10⁵` and
`|δ| ≤ 49·(q,2)·600000/q` (the `y`-arcs): `err_{η*}(δ,x) = err_{η_c}(δ/49, y)/49`, and
`|δ/49| ≤ 1.2·10⁶/q ≤ 4·300000/q*`, inside `CoprarR`; then `MR.star_numR`. -/
theorem eb_wide (cp : MR.CoprarR (HW.mconv HW.eta2 HW.phi)) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x)
    (q : ℕ) (hq1 : 1 ≤ q) (hq : q ≤ 300000) (δ : ℝ)
    (hδ : |δ| ≤ 49 * (Nat.gcd q 2 : ℝ) * 600000 / q) (χ : DirichletCharacter ℂ q) :
    Real.sqrt (χ.conductor : ℝ) * ‖MajSp.err HW.etaStar χ.primitiveCharacter δ x‖ ≤
      2.1941e-7 / 49 := by
  haveI : NeZero q := ⟨by omega⟩
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hc1 : 1 ≤ χ.conductor := Nat.one_le_iff_ne_zero.mpr χ.conductor_ne_zero
  have hcq : χ.conductor ≤ q := Nat.le_of_dvd (by omega) χ.conductor_dvd_level
  have hg2 : Nat.gcd q 2 ≤ 2 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_right q 2)
  have hδ' : |δ / 49| ≤ 4 * 300000 / (χ.conductor : ℝ) := by
    have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
    have hc0 : (0 : ℝ) < χ.conductor := Nat.cast_pos.mpr (by omega)
    have hgR : (Nat.gcd q 2 : ℝ) ≤ 2 := by exact_mod_cast hg2
    have hcqR : (χ.conductor : ℝ) ≤ q := by exact_mod_cast hcq
    have e1 : |δ / 49| = |δ| / 49 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 49)]
    have e2 : |δ| / 49 ≤ (Nat.gcd q 2 : ℝ) * 600000 / q := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 49)]
      calc |δ| ≤ 49 * (Nat.gcd q 2 : ℝ) * 600000 / q := hδ
        _ = (Nat.gcd q 2 : ℝ) * 600000 / q * 49 := by ring
    have e3 : (Nat.gcd q 2 : ℝ) * 600000 / q ≤ 4 * 300000 / (χ.conductor : ℝ) := by
      rw [div_le_div_iff₀ hq0 hc0]
      nlinarith
    rw [e1]
    linarith
  have hy : 10 ^ 8 ≤ x / 49 := by
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have hc3 : χ.conductor ≤ 300000 := by omega
  have hb := cp (x / 49) hy χ.conductor hc1 hc3 χ.primitiveCharacter
    χ.primitiveCharacter_isPrimitive (δ / 49) hδ'
  rw [MajSp.sqrt_div49 x hx0.le] at hb
  rw [MajSp.err_scale HW.etaStar _ RT.starScale_helf χ.primitiveCharacter δ x hx0.ne', norm_div,
    Complex.norm_ofNat]
  have hs1 : 1 ≤ Real.sqrt (χ.conductor : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity), one_pow]
    exact_mod_cast hc1
  calc Real.sqrt (χ.conductor : ℝ) *
        (‖MajSp.err (HW.mconv HW.eta2 HW.phi) χ.primitiveCharacter (δ / 49) (x / 49)‖ / 49)
      ≤ Real.sqrt (χ.conductor : ℝ) * ((3e-13 / (χ.conductor : ℝ) +
          (650000 / Real.sqrt (χ.conductor : ℝ) + 80) / (Real.sqrt x / 7)) / 49) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hb (by norm_num))
          (Real.sqrt_nonneg _)
    _ ≤ 2.1941e-7 / 49 :=
        MR.star_numR _ _ _ (Real.mul_self_sqrt (Nat.cast_nonneg _)) hs1 (MajSp.sqrt_c_le _ hc3)
          (MajSp.sqrt_x_ge x hx)

/-! ## (5) The non-coprime mass `B` for `η*` -/

/-- `η*(t)²·t ≤ 1.414·6/49` for `t > 0` (`0 ≤ η* ≤ 1.414`, `η*(t)·t ≤ 3√3e^{−3/2}/49 ≤ 6/49`). -/
theorem etaStar_sq_mul_le (t : ℝ) (ht : 0 < t) : HW.etaStar t ^ 2 * t ≤ 1.414 * (6 / 49) := by
  obtain ⟨h0, h1⟩ := EN.etaStar_mem ht.le
  have h2 := EN.etaStar_mul_le ht.le
  have hs3 : Real.sqrt 3 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have he : Real.exp (-3 / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have he0 := Real.exp_pos (-3 / 2)
  have hs0 := Real.sqrt_nonneg 3
  have h3 : 3 * Real.sqrt 3 * Real.exp (-3 / 2) / 49 ≤ 6 / 49 := by
    rw [div_le_div_iff_of_pos_right (by norm_num)]
    have := mul_le_mul hs3 he he0.le (by norm_num)
    nlinarith
  have h4 : HW.etaStar t * t ≤ 6 / 49 := h2.trans h3
  have h5 : 0 ≤ HW.etaStar t * t := mul_nonneg h0 ht.le
  calc HW.etaStar t ^ 2 * t = HW.etaStar t * (HW.etaStar t * t) := by ring
    _ ≤ 1.414 * (6 / 49) := mul_le_mul h1 h4 h5 (by norm_num)

/-- **`|η*(p^{k+1}/x)| ≤ 0.3√x·(3/4)^k`** for a prime power base `p ≥ 2`. -/
theorem etaStar_pk_le (p : ℕ) (hp : 2 ≤ p) (x : ℝ) (hx : 0 < x) (k : ℕ) :
    |HW.etaStar ((p : ℝ) ^ (k + 1) / x)| ≤ 0.3 * Real.sqrt x * (3 / 4) ^ k := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  set P : ℝ := (p : ℝ) ^ (k + 1) with hP
  have hP0 : 0 < P := by positivity
  have ht : 0 < P / x := div_pos hP0 hx
  obtain ⟨h0, -⟩ := EN.etaStar_mem ht.le
  rw [abs_of_nonneg h0]
  have h1 := etaStar_sq_mul_le (P / x) ht
  set s := HW.etaStar (P / x) with hs
  have h1' : s ^ 2 * P ≤ 1.414 * (6 / 49) * x := by
    have e : s ^ 2 * (P / x) * x = s ^ 2 * P := by field_simp
    rw [← e]
    exact mul_le_mul_of_nonneg_right h1 hx.le
  set R : ℝ := (3 / 4 : ℝ) ^ k with hR
  have hR0 : 0 ≤ R := by positivity
  have hQR : 1 ≤ (2 : ℝ) ^ k * R ^ 2 := by
    have e : (2 : ℝ) ^ k * R ^ 2 = (9 / 8 : ℝ) ^ k := by
      rw [hR, ← pow_mul, mul_comm k 2, pow_mul, ← mul_pow]
      norm_num
    rw [e]
    exact one_le_pow₀ (by norm_num)
  have hPQ : 2 * (2 : ℝ) ^ k ≤ P := by
    rw [hP, pow_succ]
    calc 2 * (2 : ℝ) ^ k = (2 : ℝ) ^ k * 2 := by ring
      _ ≤ (p : ℝ) ^ k * p :=
          mul_le_mul (pow_le_pow_left₀ (by norm_num) hp2 k) hp2 (by norm_num) (by positivity)
  have hPR : 2 ≤ P * R ^ 2 := by nlinarith [sq_nonneg R, pow_pos (by norm_num : (0 : ℝ) < 2) k]
  have hs2 : s ^ 2 * 2 ≤ 1.414 * (6 / 49) * x * R ^ 2 := by
    calc s ^ 2 * 2 ≤ s ^ 2 * (P * R ^ 2) := mul_le_mul_of_nonneg_left hPR (sq_nonneg s)
      _ = s ^ 2 * P * R ^ 2 := by ring
      _ ≤ 1.414 * (6 / 49) * x * R ^ 2 := mul_le_mul_of_nonneg_right h1' (sq_nonneg R)
  have hsx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hB : s ^ 2 ≤ (0.3 * Real.sqrt x * R) ^ 2 := by
    have e : (0.3 * Real.sqrt x * R) ^ 2 = 0.09 * x * R ^ 2 := by
      rw [mul_pow, mul_pow, hsx]
      ring
    rw [e]
    nlinarith [mul_nonneg hx.le (sq_nonneg R)]
  have hB0 : 0 ≤ 0.3 * Real.sqrt x * R := by positivity
  exact (pow_le_pow_iff_left₀ h0 hB0 two_ne_zero).mp hB

/-- **`∑_k |η*(p^{k+1}/x)| ≤ 1.2√x`** (geometric, ratio `3/4`). -/
theorem tsum_pk_le (p : ℕ) (hp : 2 ≤ p) (x : ℝ) (hx : 0 < x) :
    ∑' k : ℕ, |HW.etaStar ((p : ℝ) ^ (k + 1) / x)| ≤ 1.2 * Real.sqrt x := by
  have hg : Summable fun k : ℕ => 0.3 * Real.sqrt x * (3 / 4 : ℝ) ^ k :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hb := etaStar_pk_le p hp x hx
  have hs : Summable fun k : ℕ => |HW.etaStar ((p : ℝ) ^ (k + 1) / x)| :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hb hg
  calc ∑' k : ℕ, |HW.etaStar ((p : ℝ) ^ (k + 1) / x)|
      ≤ ∑' k : ℕ, 0.3 * Real.sqrt x * (3 / 4 : ℝ) ^ k := hs.tsum_le_tsum hb hg
    _ = 1.2 * Real.sqrt x := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num
        ring

/-- **`∑_{p | q} log p ≤ 13.2`** for `1 ≤ q ≤ 3·10⁵` (`∏_{p|q} p ≤ q ≤ 2¹⁹`). -/
theorem sum_log_pf_le (q : ℕ) (hq1 : 1 ≤ q) (hq : q ≤ 300000) :
    ∑ p ∈ q.primeFactors, Real.log p ≤ 13.2 := by
  have hne : ∀ p ∈ q.primeFactors, (p : ℝ) ≠ 0 := fun p hp =>
    Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
  rw [← Real.log_prod hne]
  have hpos : 0 < ∏ p ∈ q.primeFactors, (p : ℝ) :=
    Finset.prod_pos fun p hp => Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos
  have hle : ∏ p ∈ q.primeFactors, p ≤ q := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q)
  have hleR : ∏ p ∈ q.primeFactors, (p : ℝ) ≤ (2 : ℝ) ^ 19 := by
    have h1 : ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ≤ (2 : ℝ) ^ 19 := by
      have : ∏ p ∈ q.primeFactors, p ≤ 2 ^ 19 := le_trans hle (le_trans hq (by norm_num))
      exact_mod_cast this
    simpa [Nat.cast_prod] using h1
  calc Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) ≤ Real.log ((2 : ℝ) ^ 19) :=
        Real.log_le_log hpos hleR
    _ = 19 * Real.log 2 := by rw [Real.log_pow]; norm_num
    _ ≤ 13.2 := by linarith [Real.log_two_lt_d9]

/-- **`B = ∑_{(n,q)>1} Λ(n)|η*(n/x)| ≤ 15.84√x`** for `1 ≤ q ≤ 3·10⁵` (`2B ≤ B_q`,
`PA.massLink`; `B_q/2 = ∑_{p|q} log p ∑_k |η*(p^{k+1}/x)| ≤ 13.2·1.2√x`). -/
theorem bNon_le (x : ℝ) (hx : 0 < x) (q : ℕ) (hq1 : 1 ≤ q) (hq : q ≤ 300000)
    (hs : Summable fun n : ℕ => Λ n * |HW.etaStar ((n : ℝ) / x)|) :
    PA.bNon HW.etaStar x q ≤ 15.84 * Real.sqrt x := by
  obtain ⟨-, h2⟩ := PA.massLink HW.etaStar x q (by omega) hs
  have hsx := Real.sqrt_nonneg x
  have hQ : DS.bQ HW.etaStar x q ≤ 2 * (13.2 * (1.2 * Real.sqrt x)) := by
    unfold DS.bQ
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    calc ∑ p ∈ q.primeFactors, Real.log p * ∑' k : ℕ, |HW.etaStar ((p : ℝ) ^ (k + 1) / x)|
        ≤ ∑ p ∈ q.primeFactors, Real.log p * (1.2 * Real.sqrt x) := by
          refine Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left
            (tsum_pk_le p (Nat.prime_of_mem_primeFactors hp).two_le x hx) ?_
          exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)
      _ = (∑ p ∈ q.primeFactors, Real.log p) * (1.2 * Real.sqrt x) := by
          rw [Finset.sum_mul]
      _ ≤ 13.2 * (1.2 * Real.sqrt x) :=
          mul_le_mul_of_nonneg_right (sum_log_pf_le q hq1 hq) (by positivity)
  linarith

/-! ## (6) Decay of the Fourier transforms -/

/-- `d/dt e(νt) = 2πiν·e(νt)`. -/
theorem hasDerivAt_e_mul (ν t : ℝ) :
    HasDerivAt (fun s : ℝ => e (ν * s)) (2 * Real.pi * Complex.I * ν * e (ν * t)) t := by
  have hr : HasDerivAt (fun s : ℝ => ν * s) ν t := by
    simpa using (hasDerivAt_id t).const_mul ν
  have h2 := (hr.ofReal_comp.const_mul (2 * Real.pi * Complex.I : ℂ)).cexp
  have hfe : (fun s : ℝ => e (ν * s)) =
      fun s : ℝ => Complex.exp ((2 * Real.pi * Complex.I : ℂ) * ((ν * s : ℝ) : ℂ)) := by
    funext s
    simp only [e]
  rw [hfe]
  have hv : 2 * Real.pi * Complex.I * ν * e (ν * t) =
      Complex.exp ((2 * Real.pi * Complex.I : ℂ) * ((ν * t : ℝ) : ℂ)) *
        (2 * Real.pi * Complex.I * (ν : ℂ)) := by
    simp only [e]
    push_cast
    ring
  rw [hv]
  exact h2

/-- `‖2πiν‖ = 2π|ν|`. -/
theorem norm_twoPiI (ν : ℝ) : ‖(2 * Real.pi * Complex.I * ν : ℂ)‖ = 2 * Real.pi * |ν| := by
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_ofNat]
  ring

/-- **Integration by parts against `e(νt)`**: for `f ∈ C¹[a,b]` with `|f'| ≤ M`,
`|∫_a^b f(t)e(νt)dt| ≤ (|f(a)| + |f(b)| + M(b − a))/(2π|ν|)`. -/
theorem ibp_le (f f' : ℝ → ℝ) (a b ν M : ℝ) (hab : a ≤ b) (hν : ν ≠ 0)
    (hf : ∀ t ∈ Set.uIcc a b, HasDerivAt f (f' t) t) (hc : ContinuousOn f' (Set.uIcc a b))
    (hM : ∀ t ∈ Set.uIcc a b, |f' t| ≤ M) :
    ‖∫ t in a..b, ((f t : ℝ) : ℂ) * e (ν * t)‖ ≤
      (|f a| + |f b| + M * (b - a)) / (2 * Real.pi * |ν|) := by
  set c : ℂ := 2 * Real.pi * Complex.I * ν with hcdef
  have hν0 : 0 < |ν| := abs_pos.mpr hν
  have hN : ‖c‖ = 2 * Real.pi * |ν| := norm_twoPiI ν
  have hN0 : 0 < ‖c‖ := by rw [hN]; positivity
  have hc0 : c ≠ 0 := norm_pos_iff.mp hN0
  have hv : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun s : ℝ => e (ν * s) / c) (e (ν * t)) t := by
    intro t _
    have h := (hasDerivAt_e_mul ν t).div_const c
    have e1 : 2 * Real.pi * Complex.I * ν * e (ν * t) / c = e (ν * t) := by
      rw [mul_comm (2 * Real.pi * Complex.I * (ν : ℂ)) (e (ν * t)), mul_div_assoc, ← hcdef,
        div_self hc0, mul_one]
    rwa [e1] at h
  have hu : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun s : ℝ => ((f s : ℝ) : ℂ)) ((f' t : ℝ) : ℂ) t :=
    fun t ht => (hf t ht).ofReal_comp
  have hu' : IntervalIntegrable (fun t : ℝ => ((f' t : ℝ) : ℂ)) volume a b :=
    (Complex.continuous_ofReal.comp_continuousOn hc).intervalIntegrable
  have hv' : IntervalIntegrable (fun t : ℝ => e (ν * t)) volume a b := by
    refine Continuous.intervalIntegrable ?_ a b
    unfold e
    fun_prop
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv']
  have hvn : ∀ t : ℝ, ‖e (ν * t) / c‖ = 1 / ‖c‖ := fun t => by rw [norm_div, e_norm]
  have hI : ‖∫ t in a..b, ((f' t : ℝ) : ℂ) * (e (ν * t) / c)‖ ≤ M / ‖c‖ * |b - a| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    have ht' : t ∈ Set.uIcc a b := Set.uIoc_subset_uIcc ht
    rw [norm_mul, hvn, Complex.norm_real, Real.norm_eq_abs, ← div_eq_mul_one_div]
    exact div_le_div_of_nonneg_right (hM t ht') hN0.le
  have hb1 : ‖((f b : ℝ) : ℂ) * (e (ν * b) / c)‖ = |f b| / ‖c‖ := by
    rw [norm_mul, hvn, Complex.norm_real, Real.norm_eq_abs, ← div_eq_mul_one_div]
  have ha1 : ‖((f a : ℝ) : ℂ) * (e (ν * a) / c)‖ = |f a| / ‖c‖ := by
    rw [norm_mul, hvn, Complex.norm_real, Real.norm_eq_abs, ← div_eq_mul_one_div]
  have t1 := norm_sub_le (((f b : ℝ) : ℂ) * (e (ν * b) / c) - ((f a : ℝ) : ℂ) * (e (ν * a) / c))
    (∫ t in a..b, ((f' t : ℝ) : ℂ) * (e (ν * t) / c))
  have t2 := norm_sub_le (((f b : ℝ) : ℂ) * (e (ν * b) / c)) (((f a : ℝ) : ℂ) * (e (ν * a) / c))
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hI
  rw [← hN]
  have e2 : (|f a| + |f b| + M * (b - a)) / ‖c‖ =
      |f b| / ‖c‖ + |f a| / ‖c‖ + M / ‖c‖ * (b - a) := by
    field_simp
    ring
  rw [e2]
  linarith

/-- `mainFT η₂ ν = ∫_{1/4}^{1/2} + ∫_{1/2}^{1}` of `η₂(t)e(νt)` (`η₂ = 0` off `(1/4, 1)`). -/
theorem mainFT_eta2_split (ν : ℝ) :
    MajSp.mainFT HW.eta2 ν = (∫ t in (1 / 4 : ℝ)..(1 / 2), ((HW.eta2 t : ℝ) : ℂ) * e (ν * t)) +
      ∫ t in (1 / 2 : ℝ)..1, ((HW.eta2 t : ℝ) : ℂ) * e (ν * t) := by
  have hce : Continuous fun t : ℝ => e (ν * t) := by
    unfold e
    fun_prop
  have hco : ∀ a b : ℝ, 0 < a → 0 < b →
      IntervalIntegrable (fun t : ℝ => ((HW.eta2 t : ℝ) : ℂ) * e (ν * t)) volume a b := by
    intro a b ha hb
    refine ContinuousOn.intervalIntegrable ?_
    exact (Complex.continuous_ofReal.comp_continuousOn
      (EN.eta2_contOn.mono (HW.uIcc_pos ha hb))).mul hce.continuousOn
  rw [intervalIntegral.integral_add_adjacent_intervals (hco _ _ (by norm_num) (by norm_num))
    (hco _ _ (by norm_num) (by norm_num)), intervalIntegral.integral_of_le (by norm_num)]
  unfold MajSp.mainFT
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun t ht => lt_trans (by norm_num) ht.1) fun t ht => ?_
  obtain ⟨h0, h1⟩ := ht
  have h0' : 0 < t := h0
  have hz : HW.eta2 t = 0 := by
    rcases le_or_gt t (1 / 4) with hq | hq
    · exact HW.eta2_of_le_quarter h0' hq
    · exact HW.eta2_of_one_le (le_of_lt (not_le.mp fun h => h1 ⟨hq, h⟩))
  rw [hz, Complex.ofReal_zero, zero_mul]

/-- **[Eta2Decay] PROVED**: `ibp_le` on `[1/4,1/2]` (`η₂ = 4(2 log 2 + log t)`, `|η₂'| ≤ 16`) and
`[1/2,1]` (`η₂ = −4 log t`, `|η₂'| ≤ 8`): `|η̂₂(ν)| ≤ (8 log 2 + 8)/(2π|ν|) ≤ 2.2/|ν|`. -/
theorem eta2Decay : Eta2Decay := by
  intro ν hν
  have hν0 : 0 < |ν| := abs_pos.mpr hν
  have hl2 := Real.log_two_lt_d9
  have hl20 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpi := Real.pi_gt_d2
  set fL : ℝ → ℝ := fun t => 4 * (2 * Real.log 2 + Real.log t) with hfL
  set fR : ℝ → ℝ := fun t => -4 * Real.log t with hfR
  have hsubL : Set.uIcc (1 / 4 : ℝ) (1 / 2) ⊆ Set.Ioi 0 := HW.uIcc_pos (by norm_num) (by norm_num)
  have hsubR : Set.uIcc (1 / 2 : ℝ) 1 ⊆ Set.Ioi 0 := HW.uIcc_pos (by norm_num) (by norm_num)
  have hmemL : ∀ t ∈ Set.uIcc (1 / 4 : ℝ) (1 / 2), 1 / 4 ≤ t ∧ t ≤ 1 / 2 := fun t ht => by
    rw [Set.uIcc_of_le (by norm_num)] at ht
    exact ht
  have hmemR : ∀ t ∈ Set.uIcc (1 / 2 : ℝ) 1, 1 / 2 ≤ t ∧ t ≤ 1 := fun t ht => by
    rw [Set.uIcc_of_le (by norm_num)] at ht
    exact ht
  have hL : (∫ t in (1 / 4 : ℝ)..(1 / 2), ((HW.eta2 t : ℝ) : ℂ) * e (ν * t)) =
      ∫ t in (1 / 4 : ℝ)..(1 / 2), ((fL t : ℝ) : ℂ) * e (ν * t) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    obtain ⟨h1, h2⟩ := hmemL t ht
    simp only [hfL, EN.eta2_left h1 h2]
  have hR : (∫ t in (1 / 2 : ℝ)..1, ((HW.eta2 t : ℝ) : ℂ) * e (ν * t)) =
      ∫ t in (1 / 2 : ℝ)..1, ((fR t : ℝ) : ℂ) * e (ν * t) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    obtain ⟨h1, h2⟩ := hmemR t ht
    simp only [hfR, EN.eta2_right h1 h2]
  have hbL := ibp_le fL (fun t => 4 * t⁻¹) (1 / 4) (1 / 2) ν 16 (by norm_num) hν
    (fun t ht => by
      have ht0 : 0 < t := hsubL ht
      have h := ((hasDerivAt_const t (2 * Real.log 2)).add
        (Real.hasDerivAt_log ht0.ne')).const_mul 4
      simpa [hfL] using h)
    (continuousOn_const.mul (continuousOn_inv₀.mono fun t ht => (hsubL ht).ne'))
    (fun t ht => by
      obtain ⟨h1, -⟩ := hmemL t ht
      have ht0 : 0 < t := by linarith
      rw [abs_of_pos (by positivity), ← div_eq_mul_inv, div_le_iff₀ ht0]
      linarith)
  have hbR := ibp_le fR (fun t => -4 * t⁻¹) (1 / 2) 1 ν 8 (by norm_num) hν
    (fun t ht => by
      have ht0 : 0 < t := hsubR ht
      have h := (Real.hasDerivAt_log ht0.ne').const_mul (-4)
      simpa [hfR] using h)
    (continuousOn_const.mul (continuousOn_inv₀.mono fun t ht => (hsubR ht).ne'))
    (fun t ht => by
      obtain ⟨h1, -⟩ := hmemR t ht
      have ht0 : 0 < t := by linarith
      rw [abs_mul, abs_of_neg (by norm_num : (-4 : ℝ) < 0), abs_of_pos (inv_pos.mpr ht0),
        ← div_eq_mul_inv, div_le_iff₀ ht0]
      linarith)
  have h14 : Real.log (1 / 4) = -(2 * Real.log 2) := by
    rw [show (1 / 4 : ℝ) = (2 ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
    norm_num
  have fL1 : fL (1 / 4) = 0 := by simp only [hfL, h14]; ring
  have fL2 : fL (1 / 2) = 4 * Real.log 2 := by simp only [hfL, EN.log_half]; ring
  have fR1 : fR (1 / 2) = 4 * Real.log 2 := by simp only [hfR, EN.log_half]; ring
  have fR2 : fR 1 = 0 := by simp only [hfR, Real.log_one]; ring
  rw [fL1, fL2, abs_zero, abs_of_pos (by positivity)] at hbL
  rw [fR1, fR2, abs_zero, abs_of_pos (by positivity)] at hbR
  rw [mainFT_eta2_split, hL, hR]
  refine (norm_add_le _ _).trans ?_
  have hD : 0 < 2 * Real.pi * |ν| := by positivity
  have hsum : (0 + 4 * Real.log 2 + 16 * (1 / 2 - 1 / 4)) / (2 * Real.pi * |ν|) +
      (4 * Real.log 2 + 0 + 8 * (1 - 1 / 2)) / (2 * Real.pi * |ν|) ≤ 2.2 / |ν| := by
    rw [← add_div, div_le_div_iff₀ hD hν0]
    nlinarith
  linarith

/-- `∫₀^∞ y e^{−y²/2} dy = 1` (`integral_mul_cexp_neg_mul_sq` at `b = 1/2`). -/
theorem int_mul_exp_half : ∫ y in Set.Ioi (0 : ℝ), y * Real.exp (-(1 / 2) * y ^ 2) = 1 := by
  have h := integral_mul_cexp_neg_mul_sq (b := (1 / 2 : ℂ)) (by norm_num)
  have h2 : (((∫ y in Set.Ioi (0 : ℝ), y * Real.exp (-(1 / 2) * y ^ 2)) : ℝ) : ℂ) = 1 := by
    rw [← integral_complex_ofReal]
    push_cast
    rw [h]
    norm_num
  exact_mod_cast h2

/-- **[McDecay] from [Eta2Decay]**: Fubini on the Mellin convolution,
`η̂_c(ω) = ∫₀^∞ φ(y) η̂₂(ωy) dy` (`EN.integrable_mconv_prod` twisted by `e(ωs)`, then
`s = yu`), so `|η̂_c(ω)| ≤ ∫ φ(y)·2.2/(|ω|y) dy = 2.2/|ω|·∫ y e^{−y²/2} = 2.2/|ω|`. -/
theorem mcDecay_of (h2 : Eta2Decay) : McDecay := by
  intro ω hω
  have hω0 : 0 < |ω| := abs_pos.mpr hω
  set G : ℝ → ℝ → ℝ := fun s y => HW.eta2 (s / y) * HW.phi y / y with hG
  set F : ℝ → ℝ → ℂ := fun s y => ((G s y : ℝ) : ℂ) * e (ω * s) with hF
  have hce : Continuous fun s : ℝ => e (ω * s) := by
    unfold e
    fun_prop
  have hFi : Integrable (Function.uncurry F)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
    have hG' : Integrable (fun p : ℝ × ℝ => ((Function.uncurry G p : ℝ) : ℂ))
        ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) :=
      EN.integrable_mconv_prod.ofReal
    have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => e (ω * p.1))
        ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) :=
      (hce.comp continuous_fst).aestronglyMeasurable
    exact hG'.mul_bdd hm (Filter.Eventually.of_forall fun p => le_of_eq (e_norm _))
  -- the transform as an iterated integral
  have hstep : MajSp.mainFT (HW.mconv HW.eta2 HW.phi) ω =
      ∫ s in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ), F s y := by
    unfold MajSp.mainFT
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    simp only [hF, hG]
    rw [integral_mul_const, integral_complex_ofReal]
    rfl
  rw [hstep, integral_integral_swap hFi]
  -- the inner integral
  have hinner : ∀ y : ℝ, 0 < y →
      ∫ s in Set.Ioi (0 : ℝ), F s y = ((HW.phi y : ℝ) : ℂ) * MajSp.mainFT HW.eta2 (ω * y) := by
    intro y hy
    have hc := integral_comp_mul_left_Ioi
      (fun u : ℝ => ((HW.eta2 u : ℝ) : ℂ) * e (ω * y * u)) 0 (inv_pos.mpr hy)
    rw [mul_zero, inv_inv] at hc
    have e1 : ∀ s : ℝ, F s y = ((HW.phi y / y : ℝ) : ℂ) *
        (((HW.eta2 (y⁻¹ * s) : ℝ) : ℂ) * e (ω * y * (y⁻¹ * s))) := by
      intro s
      simp only [hF, hG]
      rw [show ω * y * (y⁻¹ * s) = ω * s by field_simp, div_eq_inv_mul s y]
      push_cast
      ring
    have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    simp_rw [e1]
    rw [integral_const_mul, hc]
    unfold MajSp.mainFT
    rw [Complex.real_smul]
    push_cast
    field_simp
  have hint : Integrable (fun y : ℝ => 2.2 / |ω| * (y * Real.exp (-(1 / 2) * y ^ 2)))
      (volume.restrict (Set.Ioi 0)) :=
    ((integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).integrableOn).const_mul _
  have hbound : ∀ᵐ y ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ‖∫ s in Set.Ioi (0 : ℝ), F s y‖ ≤ 2.2 / |ω| * (y * Real.exp (-(1 / 2) * y ^ 2)) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_
    have hy0 : 0 < y := hy
    have hωy : ω * y ≠ 0 := mul_ne_zero hω hy0.ne'
    rw [hinner y hy0, norm_mul, Complex.norm_real, Real.norm_of_nonneg (HW.phi_nonneg y)]
    have hd := h2 (ω * y) hωy
    rw [abs_mul, abs_of_pos hy0] at hd
    have hp : HW.phi y = y ^ 2 * Real.exp (-(1 / 2) * y ^ 2) := by
      unfold HW.phi
      ring_nf
    rw [hp]
    have hex := Real.exp_pos (-(1 / 2) * y ^ 2)
    calc y ^ 2 * Real.exp (-(1 / 2) * y ^ 2) * ‖MajSp.mainFT HW.eta2 (ω * y)‖
        ≤ y ^ 2 * Real.exp (-(1 / 2) * y ^ 2) * (2.2 / (|ω| * y)) :=
          mul_le_mul_of_nonneg_left hd (by positivity)
      _ = 2.2 / |ω| * (y * Real.exp (-(1 / 2) * y ^ 2)) := by
          field_simp
  refine (norm_integral_le_of_norm_le hint hbound).trans (le_of_eq ?_)
  rw [integral_const_mul, int_mul_exp_half, mul_one]

/-- **`η̂*(δ) = η̂_c(δ/49)/49`** (`η*(t) = η_c(49t)`, `t ↦ t/49`). -/
theorem mainFT_star (δ : ℝ) : MajSp.mainFT HW.etaStar δ =
    (49 : ℝ)⁻¹ • MajSp.mainFT (HW.mconv HW.eta2 HW.phi) (δ / 49) := by
  have hc := integral_comp_mul_left_Ioi
    (fun u : ℝ => ((HW.mconv HW.eta2 HW.phi u : ℝ) : ℂ) * e (δ / 49 * u)) 0
    (by norm_num : (0 : ℝ) < 49)
  rw [mul_zero] at hc
  unfold MajSp.mainFT
  rw [← hc]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [HW.etaStar]
  rw [show δ / 49 * (49 * t) = δ * t by ring]

/-- **`|η̂*(δ)| ≤ 2.2/|δ|`** (`mcDecay_of eta2Decay`, `mainFT_star`). -/
theorem ft_star_le (hdec : McDecay) (δ : ℝ) (hδ : δ ≠ 0) :
    ‖MajSp.mainFT HW.etaStar δ‖ ≤ 2.2 / |δ| := by
  have hδ0 : 0 < |δ| := abs_pos.mpr hδ
  rw [mainFT_star, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 49⁻¹)]
  have h := hdec (δ / 49) (div_ne_zero hδ (by norm_num))
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 49)] at h
  calc (49 : ℝ)⁻¹ * ‖MajSp.mainFT (HW.mconv HW.eta2 HW.phi) (δ / 49)‖
      ≤ (49 : ℝ)⁻¹ * (2.2 / (|δ| / 49)) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 2.2 / |δ| := by field_simp

/-! ## (7) `q/φ(q)` on the major-arc moduli -/

/-- **`q ≤ 8.54·φ(q)` for `1 ≤ q ≤ 3·10⁵`**: `(q/φ(q))² = ∏_{p|q}(1 + gw p)`
(`TotientSq.sq_ratio`) `≤ 70·(101/100)⁴ = 72.84` (`prod_gw_le`, `rough_le`); true max `5.2135`. -/
theorem q_le_tot (q : ℕ) (hq1 : 1 ≤ q) (hq : q ≤ 300000) : (q : ℝ) ≤ 8.54 * q.totient := by
  classical
  have hq0 : q ≠ 0 := by omega
  have h2 : ∀ p ∈ q.primeFactors, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hsq := TotientSq.sq_ratio q hq0
  have hsplit := Finset.prod_inter_mul_prod_sdiff q.primeFactors TotientSq.sps
    (fun p => 1 + TotientSq.gw p)
  have hrough := TotientSq.rough_le q hq0 hq
  have hsm : ∏ p ∈ q.primeFactors ∩ TotientSq.sps, (1 + TotientSq.gw p) ≤ 70 := by
    have hs2 := Finset.prod_inter_mul_prod_sdiff TotientSq.sps q.primeFactors
      (fun p => 1 + TotientSq.gw p)
    have hone : 1 ≤ ∏ p ∈ TotientSq.sps \ q.primeFactors, (1 + TotientSq.gw p) := by
      have h := Finset.prod_le_prod (s := TotientSq.sps \ q.primeFactors) (f := fun _ => (1 : ℝ))
        (g := fun p => 1 + TotientSq.gw p) (fun _ _ => zero_le_one) fun p hp =>
          le_add_of_nonneg_right (TotientSq.gw_nonneg
            (TotientSq.two_le_sps (Finset.mem_sdiff.mp hp).1))
      simpa using h
    have hnn : 0 ≤ ∏ p ∈ TotientSq.sps ∩ q.primeFactors, (1 + TotientSq.gw p) :=
      Finset.prod_nonneg fun p hp => by
        have := TotientSq.gw_nonneg (TotientSq.two_le_sps (Finset.mem_inter.mp hp).1)
        linarith
    have hall := TotientSq.prod_gw_le
    rw [Finset.inter_comm]
    nlinarith
  have hnn2 : 0 ≤ ∏ p ∈ q.primeFactors ∩ TotientSq.sps, (1 + TotientSq.gw p) :=
    Finset.prod_nonneg fun p hp => by
      have := TotientSq.gw_nonneg (h2 p (Finset.mem_inter.mp hp).1)
      linarith
  have hprod : ∏ p ∈ q.primeFactors, (1 + TotientSq.gw p) ≤ 70 * (101 / 100 : ℝ) ^ 4 := by
    rw [← hsplit]
    exact mul_le_mul hsm hrough (Finset.prod_nonneg fun p hp => by
      have := TotientSq.gw_nonneg (h2 p (Finset.mem_sdiff.mp hp).1)
      linarith) (by norm_num)
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hle : (q : ℝ) ^ 2 ≤ 70 * (101 / 100 : ℝ) ^ 4 * (q.totient : ℝ) ^ 2 := by
    have h := hsq.le.trans hprod
    rwa [div_le_iff₀ (by positivity)] at h
  have hq0' : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  nlinarith [sq_nonneg ((q : ℝ) - 8.54 * q.totient), sq_nonneg ((q : ℝ) + 8.54 * q.totient)]

/-! ## (8) The level: `(g̃_L(y, r₀) + C_{φ,3}(K))·|φ|₁ ≥ 0.00572` -/

/-- **`g_Y(t) ≥ 2.5/√(2t)` on the corrected `L`** once `t ≥ 1000` and
`log(9Y^{1/3}/(4.008t)) > 0`: every other summand of `g_Y` is `≥ 0` (`MC.gY_nonneg`'s proof). -/
theorem gYL_ge (Y t : ℝ) (hY : 0 < Y) (ht : 1000 ≤ t)
    (hD : 0 < Real.log (9 * Y ^ ((1 : ℝ) / 3) / (2.004 * (2 * t)))) :
    2.5 / Real.sqrt (2 * t) ≤ OL.gYL Y t := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  rw [ML.gYL_eq]
  have hd := div_nonneg (ML.dL_bounds t (by linarith)).1 ht0.le
  have hR : 0 ≤ MinSp.rR Y (2 * t) := le_trans (by norm_num) (MN.rR_ge _ _ (by linarith) hD)
  have hL : 0 ≤ Real.log (2 * t) := Real.log_nonneg (by linarith)
  have hl1 : 1 < Real.log t := by
    rw [Real.lt_log_iff_exp_lt ht0]
    linarith [Real.exp_one_lt_d9]
  have hll : 0 < Real.log (Real.log t) := Real.log_pos hl1
  have hF : 0 ≤ MinSp.bigF t := by
    unfold MinSp.bigF
    positivity
  have hLL := MC.lL_nonneg t ht0 (by linarith) hF
  have hA : 0 ≤ (MinSp.rR Y (2 * t) * Real.log (2 * t) + 0.5) * Real.sqrt (MinSp.bigF t) := by
    positivity
  have h1 : 2.5 / Real.sqrt (2 * t) ≤
      ((MinSp.rR Y (2 * t) * Real.log (2 * t) + 0.5) * Real.sqrt (MinSp.bigF t) + 2.5) /
        Real.sqrt (2 * t) := div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  have h2 : 0 ≤ MinSp.lL t / t := div_nonneg hLL ht0.le
  have h3 : 0 ≤ 3.2 * Y ^ (-(1 : ℝ) / 6) := mul_nonneg (by norm_num) (Real.rpow_nonneg hY.le _)
  unfold OC.gY
  linarith

/-- `2.5/√300000 ≥ 0.0045641`. -/
theorem c0_ge : (0.0045641 : ℝ) ≤ 2.5 / Real.sqrt 300000 := by
  have hs : Real.sqrt 300000 ≤ 547.75 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hs0 : 0 < Real.sqrt 300000 := Real.sqrt_pos.mpr (by norm_num)
  rw [le_div_iff₀ hs0]
  nlinarith

/-- **[LevelFloor] PROVED**: with `c₀ = 2.5/√300000`, `gYL(wy, w r₀) ≥ c₀` on `[w₁, 1]` (argument
`≤ r₀`) and `gYL(wy, r₀) ≥ c₀` on `(1, ∞)` (`gYL_ge`; the integrands are integrable,
`GS.gtlInt`), and `1.04488 ≥ c₀` on `[0, w₁]`; so the level is `≥ c₀∫₀^∞φ = c₀√(π/2)`. -/
theorem levelFloor : LevelFloor := by
  intro y hy
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy
  have hly : 57.564626 ≤ Real.log y := MN.lya_ge_1.trans (Real.log_le_log (by norm_num) hy)
  have h9 := MN.log9_ge
  have h20 : Real.log 601200 ≤ 20 * 0.6931471808 := by
    have := Real.log_le_log (by norm_num) (show (601200 : ℝ) ≤ 2 ^ 20 by norm_num)
    rw [Real.log_pow] at this
    push_cast at this
    linarith [Real.log_two_lt_d9]
  obtain ⟨hy1, hm0, hm1⟩ := MC.w1_facts y 150000 hy (by norm_num)
  set w1 := max (1 / MinSp.kK y) (1000 / (150000 : ℝ)) with hw1
  have hK : 0 < MinSp.kK y := by
    unfold MinSp.kK
    linarith
  have hK0 : 0 ≤ 1 / MinSp.kK y := by positivity
  have hw11 : w1 ≤ 1 := hm1.trans (by norm_num)
  set c0 := 2.5 / Real.sqrt 300000 with hc0
  have hc00 := c0_ge
  have hc0le : c0 ≤ 1.04488 := by
    have : Real.sqrt 300000 ≥ 3 := by
      rw [ge_iff_le, Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    rw [hc0, div_le_iff₀ (by linarith)]
    linarith
  have hr1 : (150000 : ℝ) ≤ MinSp.r1y y := by
    have h := OS.rpow_ge_4e6 y hy
    unfold MinSp.r1y
    linarith
  obtain ⟨hIlo, hIhi⟩ := GS.gtlInt HW.phi MinSp.phi_integrableOn y hy 150000 le_rfl hr1
  have hφc := HW.continuous_phi
  have hφi : ∀ a b : ℝ, IntervalIntegrable HW.phi volume a b :=
    fun a b => hφc.intervalIntegrable a b
  -- the w ≤ 1 piece
  have hlo : c0 * ∫ w in w1..1, HW.phi w ≤
      ∫ w in w1..1, OL.gYL (w * y) (w * 150000) * HW.phi w := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hw11 ((hφi _ _).const_mul c0)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hw11).mpr hIlo) fun w hw => ?_
    have hw0 : 0 < w := lt_of_lt_of_le (lt_of_lt_of_le (by norm_num) (le_max_right _ _)) hw.1
    have hwr := MC.wr_ge y 150000 w (by norm_num) hw.1
    have hlw : Real.log w ≤ 0 := Real.log_nonpos hw0.le hw.2
    have hD : 0 < Real.log (9 * (w * y) ^ ((1 : ℝ) / 3) / (2.004 * (2 * (w * 150000)))) := by
      rw [MN.logD_eq _ _ (mul_pos hw0 hy0) (by positivity), Real.log_mul hw0.ne' hy0.ne',
        show (2.004 : ℝ) * (2 * (w * 150000)) = w * 601200 by ring,
        Real.log_mul hw0.ne' (by norm_num)]
      linarith
    have hg := gYL_ge (w * y) (w * 150000) (mul_pos hw0 hy0) hwr hD
    have hsq : Real.sqrt (2 * (w * 150000)) ≤ Real.sqrt 300000 :=
      Real.sqrt_le_sqrt (by nlinarith [hw.2])
    have hsq0 : 0 < Real.sqrt (2 * (w * 150000)) := Real.sqrt_pos.mpr (by positivity)
    have hc : c0 ≤ 2.5 / Real.sqrt (2 * (w * 150000)) :=
      div_le_div_of_nonneg_left (by norm_num) hsq0 hsq
    exact mul_le_mul_of_nonneg_right (hc.trans hg) (HW.phi_nonneg w)
  -- the w > 1 piece
  have hhi : c0 * ∫ w in Set.Ioi (1 : ℝ), HW.phi w ≤
      ∫ w in Set.Ioi (1 : ℝ), OL.gYL (w * y) 150000 * HW.phi w := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on
      ((MinSp.phi_integrableOn.mono_set (Set.Ioi_subset_Ioi zero_le_one)).const_mul c0) hIhi
      measurableSet_Ioi fun w hw => ?_
    have hw1' : (1 : ℝ) < w := hw
    have hw0 : 0 < w := by linarith
    have hlw : 0 ≤ Real.log w := Real.log_nonneg hw1'.le
    have hD : 0 < Real.log (9 * (w * y) ^ ((1 : ℝ) / 3) / (2.004 * (2 * (150000 : ℝ)))) := by
      rw [MN.logD_eq _ _ (mul_pos hw0 hy0) (by positivity), Real.log_mul hw0.ne' hy0.ne',
        show (2.004 : ℝ) * (2 * (150000 : ℝ)) = 601200 by norm_num]
      linarith
    have hg := gYL_ge (w * y) 150000 (mul_pos hw0 hy0) (by norm_num) hD
    have hc : c0 = 2.5 / Real.sqrt (2 * 150000) := by norm_num [hc0]
    rw [← hc] at hg
    exact mul_le_mul_of_nonneg_right hg (HW.phi_nonneg w)
  -- the two slivers `[0, 1/K]` and `[1/K, w₁]`
  have habs : ∀ a b : ℝ, ∫ w in a..b, |HW.phi w| = ∫ w in a..b, HW.phi w := fun a b =>
    intervalIntegral.integral_congr fun w _ => abs_of_nonneg (HW.phi_nonneg w)
  have hS1 : 0 ≤ ∫ w in (1 / MinSp.kK y)..w1, HW.phi w :=
    intervalIntegral.integral_nonneg (le_max_left _ _) fun w _ => HW.phi_nonneg w
  have hS0 : 0 ≤ ∫ w in (0 : ℝ)..(1 / MinSp.kK y), HW.phi w :=
    intervalIntegral.integral_nonneg hK0 fun w _ => HW.phi_nonneg w
  -- the total mass
  have htot : (∫ w in (0 : ℝ)..(1 / MinSp.kK y), HW.phi w) +
      (∫ w in (1 / MinSp.kK y)..w1, HW.phi w) + (∫ w in w1..1, HW.phi w) +
      (∫ w in Set.Ioi (1 : ℝ), HW.phi w) = Real.sqrt (Real.pi / 2) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hφi _ _) (hφi _ _),
      intervalIntegral.integral_add_adjacent_intervals (hφi _ _) (hφi _ _),
      intervalIntegral.integral_of_le zero_le_one, ← EN.int_phi,
      ← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
    rw [setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (MinSp.phi_integrableOn.mono_set Set.Ioc_subset_Ioi_self)
      (MinSp.phi_integrableOn.mono_set (Set.Ioi_subset_Ioi zero_le_one))]
  have hl1 : MajSp.l1 HW.phi = Real.sqrt (Real.pi / 2) := RW.phiL1_helf
  obtain ⟨hs1, -⟩ := MajSp.sqrt_pi_half
  have hSq0 : 0 < Real.sqrt (Real.pi / 2) := lt_of_lt_of_le (by norm_num) hs1
  have hlev : c0 * Real.sqrt (Real.pi / 2) ≤
      (OL.gTL HW.phi y 150000 + MinSp.cPhi3 HW.phi (MinSp.kK y)) * MajSp.l1 HW.phi := by
    unfold OL.gTL MinSp.cPhi3
    rw [hl1, habs, habs, ← hw1]
    have key : ∀ A B C D s : ℝ, s ≠ 0 →
        ((A + B + 1.04488 * C) / s + 1.04488 / s * D) * s = A + B + 1.04488 * C + 1.04488 * D :=
      fun A B C D s hs => by field_simp
    rw [key _ _ _ _ _ hSq0.ne', ← htot]
    nlinarith [mul_le_mul_of_nonneg_right hc0le hS1, mul_le_mul_of_nonneg_right hc0le hS0]
  have hfin : 0.00572 ≤ c0 * Real.sqrt (Real.pi / 2) := by nlinarith
  calc 0.00572 * y ≤ c0 * Real.sqrt (Real.pi / 2) * y := mul_le_mul_of_nonneg_right hfin hy0.le
    _ ≤ (OL.gTL HW.phi y 150000 + MinSp.cPhi3 HW.phi (MinSp.kK y)) * MajSp.l1 HW.phi * y :=
        mul_le_mul_of_nonneg_right hlev hy0.le

/-! ## (9) THE COMPOSITION -/

/-- **The closing arithmetic** (units of `x`): `(1+√q)B ≤ 548.7226·15.84√x ≤ 3.927·10⁻¹⁰x`,
`xE = 4.478·10⁻⁹x`, `x|η̂*(δ)|/φ(q) ≤ 2.2·8.54/600000·x = 3.1313·10⁻⁵x`; total
`≤ 3.1318·10⁻⁵x ≤ 0.00572·x/49 = 1.1673·10⁻⁴x`. -/
theorem close_arith (x sq B F φ q d : ℝ) (hx : 49 * 10 ^ 25 ≤ x)
    (hsq : sq ≤ 547.7226) (hB0 : 0 ≤ B) (hB : B ≤ 15.84 * Real.sqrt x)
    (hφ : 0 < φ) (hq0 : 0 < q) (hqφ : q ≤ 8.54 * φ) (hd : 600000 / q ≤ d)
    (hF : F ≤ 2.2 / d) :
    (1 + sq) * B + x * (2.1941e-7 / 49) + x * F / φ ≤ 0.00572 * (x / 49) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hsx := MajSp.sqrt_x_ge x hx
  have hsxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hsx0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  -- `√x ≤ x/2.2135943·10¹³`
  have hsxle : Real.sqrt x * (22135943 * 10 ^ 6) ≤ x := by nlinarith
  have hT1 : (1 + sq) * B ≤ 548.7226 * (15.84 * Real.sqrt x) :=
    mul_le_mul (by linarith) hB hB0 (by norm_num)
  -- `F ≤ 2.2q/600000`
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hd
  have hFq : F ≤ 2.2 * q / 600000 := by
    refine hF.trans ?_
    rw [div_le_div_iff₀ hd0 (by norm_num)]
    rw [div_le_iff₀ hq0] at hd
    nlinarith
  have hT3 : x * F / φ ≤ x * (2.2 * 8.54 / 600000) := by
    rw [div_le_iff₀ hφ]
    have h1 : x * F ≤ x * (2.2 * q / 600000) := mul_le_mul_of_nonneg_left hFq hx0.le
    have h2 : x * (2.2 * q / 600000) ≤ x * (2.2 * 8.54 / 600000) * φ := by
      have : 2.2 * q / 600000 ≤ 2.2 * 8.54 / 600000 * φ := by
        rw [div_le_iff₀ (by norm_num)]
        nlinarith
      nlinarith
    linarith
  nlinarith

/-- **`OL.CoprarL η* φ` from its three analytic inputs** (`McDecay`, `LevelFloor`, `CoprarR` for
the base): decode `α`, reduce `a` mod `q`, expand in characters (`sm_le`), bound `E` (`eb_wide`),
`B` (`bNon_le`), the principal term (`ft_star_le`, `q_le_tot`), close (`close_arith`). Junk: if
`∑Λ(n)|η*(n/x)|` diverges, `S_{η*} = 0`. -/
theorem coprarL_of_links (hdec : McDecay) (hlev : LevelFloor)
    (cp : MR.CoprarR (HW.mconv HW.eta2 HW.phi)) : OL.CoprarL HW.etaStar HW.phi := by
  intro _ _ _ x hx α hα
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hy : 10 ^ 25 ≤ x / 49 := MinSp.y_ge x hx
  have hL := hlev (x / 49) hy
  have hy0 : 0 ≤ 0.00572 * (x / 49) := by positivity
  by_cases hs : Summable fun n : ℕ => Λ n * |HW.etaStar ((n : ℝ) / x)|
  swap
  · rw [smSum_junk _ _ _ hs, norm_zero]
    linarith
  obtain ⟨q, hq1, hq3, a, ha, δ, hαe, hlo, hhi⟩ := annA0_decode x α hx0 hα
  haveI : NeZero q := ⟨by omega⟩
  obtain ⟨b, hb, k, hk⟩ := reduce_num q hq1 a ha
  have hαe' : α = ((b : ℝ) / q + δ / x) + k := by
    rw [hαe, hk]
    ring
  rw [hαe', smSum_add_int]
  have hm := sm_le HW.etaStar x δ q hx0 hs b hb (2.1941e-7 / 49)
    (eb_wide cp x hx q hq1 hq3 δ hhi)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hδ0 : δ ≠ 0 := by
    intro h
    rw [h, abs_zero] at hlo
    have : (0 : ℝ) < 600000 / q := by positivity
    linarith
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hc := close_arith x (Real.sqrt q) (PA.bNon HW.etaStar x q)
    ‖MajSp.mainFT HW.etaStar δ‖ q.totient q |δ| hx
    (MajSp.sqrt_c_le q hq3) (PA.massLink HW.etaStar x q (by omega) hs).1
    (bNon_le x hx0 q hq1 hq3 hs) hφ hq0 (q_le_tot q hq1 hq3) hlo
    (ft_star_le hdec δ hδ0)
  linarith

/-- **`OL.CoprarL η* φ` from the retyped major arcs**: `coprarL_of_links` with `McDecay`
(`mcDecay_of eta2Decay`) and `LevelFloor` (`levelFloor`) PROVED and `CoprarR` read off
`MR.HelfMajR` under `RT.PlattFull`. Application only. -/
theorem coprarL_of_R (pf : RT.PlattFull) (hm : MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi)) :
    OL.CoprarL HW.etaStar HW.phi :=
  coprarL_of_links (mcDecay_of eta2Decay) levelFloor (hm pf).2.1

end Principia.Common.TernaryGoldbach.CP
