/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MinorSpine
import Principia.Common.TernaryGoldbach.EasyBand27
import Principia.Common.TernaryGoldbach.RegW

set_option autoImplicit false

/-!
# The minor-arc spine on the band-`2.7·10⁻⁴` route: `RegW`, `NormsB27`, and a re-derived `J`

`MinSp.minor_of_mnum` (the spine of (7.48)) takes `MajSp.Reg` and `MajSp.Norms`. Both are wrong
for the integrated EP1054 headline:
* `MajSp.Reg` is UNSATISFIABLE on Helfgott's `η₊` (`RegW.lean`); the spine used only four of its
  conjuncts (`η₊ ∈ L¹`, `η∘` piecewise `C³`, `η∘''' ∈ L¹`, `η∘ ∈ L²`), all in `RW.RegW`.
* `MajSp.Norms` carries Helfgott's 7-digit norms (`|η∘|₂ ∈ [0.8001287, 0.8001288]`,
  `|η₊ − η∘|₂ ≤ 2.43·10⁻⁶`, `|η∘'''|₁ ≤ 32.5023`, `|η₊|₁ ≤ 1.062319`). On the band route only
  `EN.NormsB27` holds (`0.8 ≤ |η∘|₂ ≤ 0.8002`, `|η₊ − η∘|₂ ≤ 1.7999·10⁻⁴`, `|η∘'''|₁ ≤ 40`,
  `|η₊|₁ ≤ 1.2`), and they reach the minor arcs only through `MinSp.DrujalLow`'s hypotheses.

So the `J` bound is RE-DERIVED at `NormsB27`'s inputs from `lem:drujal`'s lower half
(`ternvin.tex` 1419–1452; `drujalE_const` certifies the arithmetic in exact rationals), and the
links that consume it are restated at the new floor. Numbers (`scratchpad/integ/integ_numbers.py`,
`g` exact from `eq:basia`, mpmath 40 digits):

| link | `MinorSpine` | here | truth on Helfgott's `φ` | margin |
|---|---|---|---|---|
| `J/x` (`DrujalLowE`) | `≥ 8.6298` | `≥ 8.613` | formula: `8.6134735` | `4.7·10⁻⁴` |
| `(√J − √E)²/x` (`eq:je`) | `≥ 8.6297` | `≥ 8.6129` | `8.6129830` | — |
| `T/x` (`LamberNumW`) | `≤ 3.5776·10⁻⁴` | `≤ 3.6·10⁻⁴` | `3.578034·10⁻⁴` | `+0.61 %` |
| `M/x` (`MNumW`) | `≤ 0.785`, `p ≥ 8.6297` | `≤ 0.785`, `p ≥ 8.6129` | `0.7429222` | `+5.66 %` |
| closing (`eq:rozoj`) | `0.98431 ≤ 0.9845` | `0.984309 ≤ 0.9845` | — | `1.9·10⁻⁴` |

**Why the `J` floor fell.** Of the `0.0164` it lost, `0.0100` is `lem:drujal`'s
`5.19δ₀r·ET·|η₊|₁` at `|η₊|₁ ≤ 1.2` instead of `1.062319`, and `0.0039` the band-limiting
`(log r + 1.7)·2|η∘|₂|η₊ − η∘|₂` at `1.7999·10⁻⁴` instead of `2.43·10⁻⁶`. **`LamberNum`'s old
constant does not survive it**: `3.5776·10⁻⁴` had a `5.6·10⁻⁵` relative margin over Helfgott's own
`0.2779/K³` bound, and the new floor moves `s − p` by `5.3·10⁻⁴`; `3.6·10⁻⁴` is true with `0.6 %`.
The joint `MNum` link keeps its constant `0.785` (true sup rises `0.742233 → 0.742922`).

**GENERATED** (`scratchpad/integ/gen_minorw.py`): every theorem below down to `amaj_junk_w` is a
copy of its `MinorSpine.lean` namesake with the constants and names rewritten by COUNTED
substitutions, every stale constant then asserted absent from the code; the docstrings are new.
The last five declarations are handwritten: `mnum_of_W` (`MNumW → MNum`), `mnumW_nonneg` and
`lamberW_nonneg` (the links force `g(r₀) ≥ 0` and `C_{φ,3} ≥ 0`, so an arbitrary function does not
meet them), `drujalE_const` and `drujalE_inst` (its hypotheses discharged once, by the endpoint
values).

`DrujalLowE`, `LamberNumW`, `MNumW` are OPEN. `DrujalLowE` and `DrujalLow` are incomparable
(weaker hypotheses, weaker conclusion); `DrujalLowE` rests on the same lemma, re-evaluated.
-/

namespace Principia.Common.TernaryGoldbach.MinW

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach
open scoped ArithmeticFunction
open Principia.Erdos1054 (helfgottX)
open Principia.Common.TernaryGoldbach.MinSp

/-- **Link [J] at the band-`2.7·10⁻⁴` norms — the LOWER half of `lem:drujal`** (`eq:bfpink`
with `eq:chetvyorg`, `ternvin.tex` 1419–1452, 4549–4564) at the inputs `EN.NormsB27` supplies:
`0.8 ≤ |η∘|₂ ≤ 0.8002`, `|η − η∘|₂ ≤ 1.7999·10⁻⁴`, `|η∘'''|₁ ≤ 40`, `|η|₁ ≤ 1.2` (Helfgott's
`DrujalLow` needs his 7-digit `eq:lopez`, `eq:sanchez`, `eq:halr`, `eq:sazar`, which the band
route does not have). The conclusion is RE-DERIVED from the lemma's lower half
(`drujalE_const` certifies the arithmetic): `L ≥ 2·6.798779·0.8² − (log r + 1.7)(2·0.8002·d + d²)
− (2·40²/(5π⁶8⁵))(0.64787 + …) = 8.6985007`, minus `5.19δ₀r·ET(1.2 + ET/2) = 0.0850271` and
`δ₀r log(2e²r)(E² + K/x) = 1.0·10⁻⁸`: `J/x ≥ 8.6134735 ≥ 8.613`. (At Helfgott's inputs the same
formula gives `8.6299`, his `8.6298`.) The `|η|₁` term is the cost: `1.2` for his `1.062319`.
OPEN; generic in the weights. -/
def DrujalLowE (η ηo : ℝ → ℝ) : Prop :=
  MemLp η 1 (volume.restrict (Set.Ioi 0)) → (∀ t : ℝ, 0 ≤ t → |η t| ≤ 1.079955) →
    MajSp.l1 η ≤ 1.2 →
    (∃ S : Finset ℝ, ∀ t : ℝ, 0 ≤ t → t ∉ S → ContDiffAt ℝ 3 ηo t) →
    Integrable (iteratedDeriv 3 ηo) (volume.restrict (Set.Ioi 0)) →
    MemLp ηo 2 (volume.restrict (Set.Ioi 0)) →
    0.8 ≤ MajSp.l2 ηo → MajSp.l2 ηo ≤ 0.8002 →
    MajSp.l2 (fun t => η t - ηo t) ≤ 1.7999e-4 → MajSp.l1 (iteratedDeriv 3 ηo) ≤ 40 →
    ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → MajSp.ETBound η 600000 x 1.1377e-8 →
      MajSp.EBound η x 2.3921e-8 → 8.613 ≤ MajSp.amaj η x

/-- **Link [T] at the new `J` floor — `eq:lamber`**: `C_{φ,3}(½ log(x/κ))·(s − p) ≤ 3.6·10⁻⁴` at
every `s ≤ felipa`, `p ≥ 8.6129` (`MinSp.LamberNum` has `p ≥ 8.6297`, `3.5776·10⁻⁴`). On
Helfgott's `φ` the exact supremum is `3.578034·10⁻⁴` (at the threshold; margin `+0.61 %`), and his
`C_{φ,3}(K) ≤ 0.2779/K³` gives `3.579357·10⁻⁴` (`+0.58 %`). At `p ≥ 8.6129` the old constant is
FALSE for his own bound (`3.5794·10⁻⁴ > 3.5776·10⁻⁴`): it had a `5.6·10⁻⁵` relative margin, and
the `J` floor moved `s − p` by `5.3·10⁻⁴`. OPEN; `φ`-specific numerics. -/
def LamberNumW (φ : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ s p : ℝ, s ≤ 0.640209 * Real.log x - 0.021095 → 8.6129 ≤ p →
    cPhi3 φ (kK (x / 49)) * (s - p) ≤ 3.6e-4

/-- **Link [M] at the new `J` floor — `eq:bustier`, jointly in `x`**: `MinSp.MNum` with `p ≥ 8.6129`
(was `8.6297`). With `g` exact (`eq:basia`), its supremum over `x ≥ 4.9·10²⁶`, `0 ≤ s ≤ felipa`,
`p ≥ 8.6129` is `0.7429222` (at the threshold; `0.742233` at `8.6297`), so `MNumW φ 0.785` holds
with a `+5.66 %` margin. STRONGER than `MNum` (`mnum_of_W`). OPEN; numerics about `eq:basia`. -/
def MNumW (φ : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ s p : ℝ, 0 ≤ s → s ≤ 0.640209 * Real.log x - 0.021095 →
    8.6129 ≤ p →
      gB φ (x / 49) 150000 * (hR0 x * s - p) +
          (2 / (Real.log x + 2 * 0.6294) * intG φ (x / 49) +
            coefC x * gB φ (x / 49) (r1y (x / 49))) * s ≤ c

/-- **`eq:je` at the new floor**: `J ≥ 8.613x`, `E ≤ 8.4031·10⁻¹²x` give
`(√J − √E)² ≥ 8.6129x` (`(√8.613 − √8.4031·10⁻¹²)² = 8.6129830`). -/
theorem je_le_w (J E x : ℝ) (hx : 0 ≤ x) (hJ : 8.613 * x ≤ J) (hE : E ≤ 8.4031e-12 * x) :
    8.6129 * x ≤ (Real.sqrt J - Real.sqrt E) ^ 2 := by
  have ha := Real.sqrt_le_sqrt hJ
  have he := Real.sqrt_le_sqrt hE
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8.613)] at ha
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8.4031e-12)] at he
  have hu0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hux : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have ha2 : Real.sqrt 8.613 ^ 2 = 8.613 := Real.sq_sqrt (by norm_num)
  have hc2 : Real.sqrt 8.4031e-12 ^ 2 = 8.4031e-12 := Real.sq_sqrt (by norm_num)
  have ha0 : 0 ≤ Real.sqrt 8.613 := Real.sqrt_nonneg _
  have hc0 : 0 ≤ Real.sqrt 8.4031e-12 := Real.sqrt_nonneg _
  have ha3 : Real.sqrt 8.613 ≤ 3 := by nlinarith
  have ha1 : 2 ≤ Real.sqrt 8.613 := by nlinarith
  have hc3 : Real.sqrt 8.4031e-12 ≤ 3e-6 := by nlinarith
  have hd : (Real.sqrt 8.613 - Real.sqrt 8.4031e-12) * Real.sqrt x ≤
      Real.sqrt J - Real.sqrt E := by nlinarith
  have hd0 : 0 ≤ (Real.sqrt 8.613 - Real.sqrt 8.4031e-12) * Real.sqrt x :=
    mul_nonneg (by linarith) hu0
  have hsq := pow_le_pow_left₀ hd0 hd 2
  have hk : 8.6129 ≤ (Real.sqrt 8.613 - Real.sqrt 8.4031e-12) ^ 2 := by nlinarith
  have hm : 8.6129 * x ≤ ((Real.sqrt 8.613 - Real.sqrt 8.4031e-12) * Real.sqrt x) ^ 2 := by
    rw [mul_pow, hux]
    exact mul_le_mul_of_nonneg_right hk hx
  linarith

/-- `je_le_w` on the defined quantities: `J = x·A_{η₊}`, `A_{η₊} ≥ 8.613`. -/
theorem pje_le_w (η b : ℝ → ℝ) (x : ℝ) (hx : 0 ≤ x) (hA : 8.613 ≤ MajSp.amaj η x)
    (hE : eBig b x ≤ 8.4031e-12 * x) : 8.6129 * x ≤ pJE η b x := by
  unfold pJE
  refine je_le_w _ _ x hx ?_ hE
  rw [mul_comm x]
  exact mul_le_mul_of_nonneg_right hA hx

/-- **`M ≤ cM·x`** from `MNumW`, `S ∈ [0, felipa]` and `(√J − √E)² ≥ 8.6129x`. -/
theorem m_le_w (φ η b : ℝ → ℝ) (cM x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (hmn : MNumW φ cM)
    (hS0 : 0 ≤ sPr η x) (hS : sPr η x ≤ (0.640209 * Real.log x - 0.021095) * x)
    (hP : 8.6129 * x ≤ pJE η b x) : mM φ η b x ≤ cM * x := by
  have hx0 := x_pos x hx
  unfold mM
  refine m_scale _ _ _ _ _ _ _ _ x cM hx0 (hmn x hx _ _ (div_nonneg hS0 hx0.le) ?_ ?_)
  · rw [div_le_iff₀ hx0]
    exact hS
  · rw [le_div_iff₀ hx0]
    exact hP

/-- **`T ≤ 3.6·10⁻⁴ x`** from `LamberNumW`. -/
theorem t_le_w (φ η b : ℝ → ℝ) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (hla : LamberNumW φ)
    (hS : sPr η x ≤ (0.640209 * Real.log x - 0.021095) * x)
    (hP : 8.6129 * x ≤ pJE η b x) : tT φ η b x ≤ 3.6e-4 * x := by
  have hx0 := x_pos x hx
  unfold tT
  refine t_scale _ _ _ x _ hx0 (hla x hx _ _ ?_ ?_)
  · rw [div_le_iff₀ hx0]
    exact hS
  · rw [le_div_iff₀ hx0]
    exact hP

/-- **`eq:rozoj`, the last step, at `T ≤ 3.6·10⁻⁴x`**: `Z ≤ (√(|φ|₁ x/49 (M+T)) + √(S*E))²` with
`|φ|₁ ≤ 1.2533143`, `M + T ≤ (cM + 3.6·10⁻⁴)x`, `S*E ≤ 1.0532·10⁻¹¹x²/49` gives `Z ≤ c·x²/49`
whenever `(√(1.2533143(cM + 3.6·10⁻⁴)) + √(1.0532·10⁻¹¹))² ≤ c`. -/
theorem z_close_w (Z a M T SE x c cM : ℝ)
    (hZ : Z ≤ (Real.sqrt (a * x / 49 * (M + T)) + Real.sqrt SE) ^ 2)
    (ha0 : 0 ≤ a) (ha : a ≤ 1.2533143) (hx : 0 ≤ x) (hMT : M + T ≤ (cM + 3.6e-4) * x)
    (hcM : 0 ≤ cM + 3.6e-4) (hSE : SE ≤ 1.0532e-11 * x ^ 2 / 49)
    (hc : (Real.sqrt (1.2533143 * (cM + 3.6e-4)) + Real.sqrt 1.0532e-11) ^ 2 ≤ c) :
    Z ≤ c * x ^ 2 / 49 := by
  have hx7 : 0 ≤ x / 7 := div_nonneg hx (by norm_num)
  have h1 : a * x / 49 * (M + T) ≤ 1.2533143 * (cM + 3.6e-4) * (x / 7) ^ 2 := by
    have hx49 : 0 ≤ a * x / 49 := div_nonneg (mul_nonneg ha0 hx) (by norm_num)
    calc a * x / 49 * (M + T) ≤ a * x / 49 * ((cM + 3.6e-4) * x) :=
          mul_le_mul_of_nonneg_left hMT hx49
      _ = a * ((cM + 3.6e-4) * (x / 7) ^ 2) := by ring
      _ ≤ 1.2533143 * ((cM + 3.6e-4) * (x / 7) ^ 2) :=
          mul_le_mul_of_nonneg_right ha (mul_nonneg hcM (sq_nonneg _))
      _ = 1.2533143 * (cM + 3.6e-4) * (x / 7) ^ 2 := by ring
  have h2 : SE ≤ 1.0532e-11 * (x / 7) ^ 2 := le_of_le_of_eq hSE (by ring)
  have hs1 : Real.sqrt (a * x / 49 * (M + T)) ≤
      Real.sqrt (1.2533143 * (cM + 3.6e-4)) * (x / 7) := by
    calc Real.sqrt (a * x / 49 * (M + T))
        ≤ Real.sqrt (1.2533143 * (cM + 3.6e-4) * (x / 7) ^ 2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt (1.2533143 * (cM + 3.6e-4)) * (x / 7) := by
          rw [Real.sqrt_mul (mul_nonneg (by norm_num) hcM), Real.sqrt_sq hx7]
  have hs2 : Real.sqrt SE ≤ Real.sqrt 1.0532e-11 * (x / 7) := by
    calc Real.sqrt SE ≤ Real.sqrt (1.0532e-11 * (x / 7) ^ 2) := Real.sqrt_le_sqrt h2
      _ = Real.sqrt 1.0532e-11 * (x / 7) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hx7]
  have hsum0 : 0 ≤ Real.sqrt (a * x / 49 * (M + T)) + Real.sqrt SE :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsum : Real.sqrt (a * x / 49 * (M + T)) + Real.sqrt SE ≤
      (Real.sqrt (1.2533143 * (cM + 3.6e-4)) + Real.sqrt 1.0532e-11) * (x / 7) := by
    linarith
  have hsq := pow_le_pow_left₀ hsum0 hsum 2
  calc Z ≤ (Real.sqrt (a * x / 49 * (M + T)) + Real.sqrt SE) ^ 2 := hZ
    _ ≤ ((Real.sqrt (1.2533143 * (cM + 3.6e-4)) + Real.sqrt 1.0532e-11) * (x / 7)) ^ 2 := hsq
    _ = (Real.sqrt (1.2533143 * (cM + 3.6e-4)) + Real.sqrt 1.0532e-11) ^ 2 * (x ^ 2 / 49) := by
        ring
    _ ≤ c * (x ^ 2 / 49) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = c * x ^ 2 / 49 := by ring

/-- `M + T ≤ (cM + 3.6·10⁻⁴)x`. -/
theorem mt_le_w (M T cM x : ℝ) (hM : M ≤ cM * x) (hT : T ≤ 3.6e-4 * x) :
    M + T ≤ (cM + 3.6e-4) * x :=
  le_of_le_of_eq (add_le_add hM hT) (by ring)

/-- **THE SPINE of (7.48) on the band-`2.7·10⁻⁴` route**, generic in the constant:
`MinSp.minor_of_mnum` with `RW.RegW` for `MajSp.Reg` (it used only `η₊ ∈ L¹`, `η∘`'s piecewise
`C³`, `η∘''' ∈ L¹`, `η∘ ∈ L²` — all in `RegW`), `EN.NormsB27` for `MajSp.Norms`, and the
`J`-consuming links at the constants those norms support (`DrujalLowE`, `LamberNumW`, `MNumW`).
Application only. -/
theorem minor_of_mnum_w (c cM : ℝ)
    (hc : (Real.sqrt (1.2533143 * (cM + 3.6e-4)) + Real.sqrt 1.0532e-11) ^ 2 ≤ c)
    (hcM : 0 ≤ cM + 3.6e-4) (ηp ηs ηo ηc φ : ℝ → ℝ) (hm : RT.HelfMajFull ηp ηc)
    (hpf : RT.PlattFull) (hsc : MajSp.StarScale ηs ηc) (hrg : RW.RegW ηp ηs ηo)
    (hnm : EN.NormsB27 ηp ηs ηo) (hsn : MajSp.SupN ηp ηs) (hoh : OstopHyp ηp ηs φ)
    (hos : Ostop ηp ηs φ) (hdl : DrujalLowE ηp ηo) (hdu : Dubistdie ηp) (hpl : PhiL1 φ)
    (hla : LamberNumW φ) (hmn : MNumW φ cM) : RT.MinorUpperAt c ηp ηs := by
  intro N _ hN
  obtain ⟨mp, cp, mh⟩ := hm hpf
  obtain ⟨hlo1, hlo2, hdiff, hl3, -, hl1s, -, hl1p, -⟩ := hnm
  have hx := MajSp.helfX_big N hN
  have hx0 := x_pos (helfgottX N) hx
  obtain ⟨b, hb⟩ := exists_supFn ηp hoh.2.2.2.2.1
  have hZ := hos hoh b hb (helfgottX N) hx
  have hS := felipa ηp (helfgottX N) hx (mh (helfgottX N) (MajSp.x12_le _ hx))
  have hS0 := sPr_nonneg ηp (helfgottX N)
  have hE := hdu hsn.1 hsn.2.1 b hb (helfgottX N) hx
  have hA := hdl hrg.1 hsn.1 hl1p hrg.2.2.2.2.1 hrg.2.2.2.2.2.1 hrg.2.2.2.2.2.2
    hlo1 hlo2 hdiff hl3 (helfgottX N) hx (MajSp.et_plus ηp mp _ hx) (MajSp.eb_plus ηp mp _ hx)
  have hP := pje_le_w ηp b (helfgottX N) hx0.le hA hE
  have hM := m_le_w φ ηp b cM (helfgottX N) hx hmn hS0 hS hP
  have hT := t_le_w φ ηp b (helfgottX N) hx hla hS hP
  have hSt := sstar_le ηs ηc hsc cp hsn.2.2.1 hl1s (helfgottX N) hx
  have hSE := hex_le _ _ (helfgottX N) hx0.le (sStar_nonneg ηs hsn.2.2.1 _ hx0) hSt hE
  exact z_close_w _ _ _ _ _ _ c cM hZ (MajSp.l1_nonneg φ) (phi_l1_le φ hpl) hx0.le
    (mt_le_w _ _ cM _ hM hT) hcM hSE hc

/-- The joint route closes at `T ≤ 3.6·10⁻⁴`: `(√(1.2533143·0.78536) + √1.0532·10⁻¹¹)² = 0.984309 ≤
0.9845`. -/
theorem close_mnum_w : (Real.sqrt (1.2533143 * (0.785 + 3.6e-4)) + Real.sqrt 1.0532e-11) ^ 2 ≤
    0.9845 :=
  close_num _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `cM + 3.6·10⁻⁴ ≥ 0` at the joint constant. -/
theorem cM_mnum_w : (0 : ℝ) ≤ 0.785 + 3.6e-4 := by norm_num

/-- **`RT.MinorUpperAt 0.9845` on the band-`2.7·10⁻⁴` route, joint `MNumW φ 0.785`**. Application
only. -/
theorem minorAt_mnum_w (ηp ηs ηo ηc φ : ℝ → ℝ) (hm : RT.HelfMajFull ηp ηc)
    (hpf : RT.PlattFull) (hsc : MajSp.StarScale ηs ηc) (hrg : RW.RegW ηp ηs ηo)
    (hnm : EN.NormsB27 ηp ηs ηo) (hsn : MajSp.SupN ηp ηs) (hoh : OstopHyp ηp ηs φ)
    (hos : Ostop ηp ηs φ) (hdl : DrujalLowE ηp ηo) (hdu : Dubistdie ηp) (hpl : PhiL1 φ)
    (hla : LamberNumW φ) (hmn : MNumW φ 0.785) : RT.MinorUpperAt 0.9845 ηp ηs :=
  minor_of_mnum_w 0.9845 0.785 close_mnum_w cM_mnum_w ηp ηs ηo ηc φ hm hpf hsc hrg hnm hsn hoh hos
    hdl hdu hpl hla hmn

/-- `amaj` of a junk weight is `0`: then `DrujalLowE`'s conclusion is FALSE, so the link is never
met by junk. -/
theorem amaj_junk_w (η : ℝ → ℝ) (x : ℝ) (h : ∀ α, Smooth.smSum η x α = 0) :
    ¬ 8.613 ≤ MajSp.amaj η x := by
  have h0 : MajSp.amaj η x = 0 := by simp [MajSp.amaj, h]
  rw [h0]
  norm_num

/-- **`MNumW → MNum`**: the same bound on the wider range `p ≥ 8.6129 ⊇ p ≥ 8.6297`. -/
theorem mnum_of_W (φ : ℝ → ℝ) (c : ℝ) (h : MNumW φ c) : MNum φ c :=
  fun x hx s p hs0 hs hp => h x hx s p hs0 hs (le_trans (by norm_num) hp)

/-- **`MNumW` forces `g(r₀) ≥ 0`** (a true property of `eq:basia`): at `s = 0`, a negative `g(r₀)`
would make `−g(r₀)·p` unbounded as `p → ∞`. So the link is not met by an arbitrary function in
place of `g`. -/
theorem mnumW_nonneg (φ : ℝ → ℝ) (c : ℝ) (h : MNumW φ c) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) :
    0 ≤ gB φ (x / 49) 150000 := by
  by_contra hneg
  have hlt : gB φ (x / 49) 150000 < 0 := not_le.mp hneg
  set g0 := gB φ (x / 49) 150000
  have hg : g0 ≠ 0 := hlt.ne
  have hL := MajSp.log_ge_one x hx
  have hs0 : (0 : ℝ) ≤ 0.640209 * Real.log x - 0.021095 := by linarith
  have hq : 0 ≤ (|c| + 1) / (-g0) := div_nonneg (by positivity) (by linarith)
  have h1 := h x hx 0 (8.6129 + (|c| + 1) / (-g0)) le_rfl hs0 (by linarith)
  have e : g0 * (hR0 x * 0 - (8.6129 + (|c| + 1) / (-g0))) +
      (2 / (Real.log x + 2 * 0.6294) * intG φ (x / 49) +
        coefC x * gB φ (x / 49) (r1y (x / 49))) * 0 = -(8.6129 * g0) + (|c| + 1) := by
    field_simp
    ring
  rw [e] at h1
  have h2 := le_abs_self c
  linarith

/-- **`LamberNumW` forces `C_{φ,3}(½ log(x/κ)) ≥ 0`** (true: it is `1.04488/|φ|₁` times an integral
of `|φ|`): at `s = 0`, a negative `C_{φ,3}` would make `−C_{φ,3}·p` exceed `3.6·10⁻⁴` for large
`p`. -/
theorem lamberW_nonneg (φ : ℝ → ℝ) (h : LamberNumW φ) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) :
    0 ≤ cPhi3 φ (kK (x / 49)) := by
  by_contra hneg
  have hlt : cPhi3 φ (kK (x / 49)) < 0 := not_le.mp hneg
  set C := cPhi3 φ (kK (x / 49))
  have hC : C ≠ 0 := hlt.ne
  have hL := MajSp.log_ge_one x hx
  have hs0 : (0 : ℝ) ≤ 0.640209 * Real.log x - 0.021095 := by linarith
  have hq : 0 ≤ 1 / (-C) := div_nonneg (by norm_num) (by linarith)
  have h1 := h x hx 0 (8.6129 + 1 / (-C)) hs0 (by linarith)
  have e : C * (0 - (8.6129 + 1 / (-C))) = -(8.6129 * C) + 1 := by
    field_simp
    ring
  rw [e] at h1
  linarith

/-- **The constant of `DrujalLowE`, certified**: `lem:drujal`'s lower half — `eq:bfpink` with
`eq:chetvyorg`, at `δ₀ = 8`, `r = 150000` —
`A ≥ 2S|η∘|₂² − (log r + 1.7)(2|η∘|₂d + d²) − (2|η∘'''|₁²/(5π⁶δ₀⁵))(0.64787 + log r/4r + 0.425/r)
− 5.19δ₀r·ET(|η|₁ + ET/2) − δ₀r log(2e²r)(E² + K)`, `d = |η − η∘|₂`, `K = K_{r,2}/x`, evaluated at
`S ≥ 6.798779` (Helfgott's `∑_{q ≤ r odd} μ²/φ`), `EN.NormsB27`'s inputs, HelfMaj's
`ET ≤ 1.1377·10⁻⁸`, `E ≤ 2.3921·10⁻⁸`, and `K ≤ 10⁻¹⁹` (it is `1.1·10⁻²⁰` at `x ≥ 4.9·10²⁶`), is
`≥ 8.613`. Terms:
`8.70243712 − 0.0039234 − 0.0000132 − 0.0850271 − 1.0·10⁻⁸ = 8.6134732`. -/
theorem drujalE_const (S lo d l3 l1 ET E K : ℝ) (hS : 6.798779 ≤ S) (hlo1 : 0.8 ≤ lo)
    (hlo2 : lo ≤ 0.8002) (hd0 : 0 ≤ d) (hd : d ≤ 1.7999e-4) (hl30 : 0 ≤ l3) (hl3 : l3 ≤ 40)
    (hl10 : 0 ≤ l1) (hl1 : l1 ≤ 1.2) (hET0 : 0 ≤ ET) (hET : ET ≤ 1.1377e-8) (hE0 : 0 ≤ E)
    (hE : E ≤ 2.3921e-8) (hK0 : 0 ≤ K) (hK : K ≤ 1e-19) :
    8.613 ≤ 2 * S * lo ^ 2 - (Real.log 150000 + 1.7) * (2 * lo * d + d ^ 2) -
      2 * l3 ^ 2 / (5 * Real.pi ^ 6 * 8 ^ 5) *
        (0.64787 + Real.log 150000 / (4 * 150000) + 0.425 / 150000) -
      5.19 * 8 * 150000 * (ET * (l1 + ET / 2)) -
      8 * 150000 * Real.log (2 * Real.exp 2 * 150000) * (E ^ 2 + K) := by
  have hlr := MajSp.log_r_le
  have hlr0 : 0 ≤ Real.log 150000 := Real.log_nonneg (by norm_num)
  have hlo0 : 0 ≤ lo := le_trans (by norm_num) hlo1
  -- the main term
  have hsq : 0.64 ≤ lo ^ 2 := by nlinarith
  have h1 : 6.798779 * 0.64 ≤ S * lo ^ 2 :=
    mul_le_mul hS hsq (by norm_num) (le_trans (by norm_num) hS)
  -- the band-limiting term
  have hq : 2 * lo * d + d ^ 2 ≤ 2 * 0.8002 * 1.7999e-4 + (1.7999e-4) ^ 2 := by
    have hld : lo * d ≤ 0.8002 * 1.7999e-4 := mul_le_mul hlo2 hd hd0 (by norm_num)
    have hdd : d ^ 2 ≤ (1.7999e-4) ^ 2 := pow_le_pow_left₀ hd0 hd 2
    linarith
  have hq0 : 0 ≤ 2 * lo * d + d ^ 2 := by positivity
  have h2 : (Real.log 150000 + 1.7) * (2 * lo * d + d ^ 2) ≤
      (11.91858 + 1.7) * (2 * 0.8002 * 1.7999e-4 + (1.7999e-4) ^ 2) :=
    mul_le_mul (by linarith) hq hq0 (by norm_num)
  have n2 : (11.91858 + 1.7) * (2 * 0.8002 * 1.7999e-4 + (1.7999e-4) ^ 2) ≤ (3.9235e-3 : ℝ) := by
    norm_num
  -- the `η∘'''` term
  have hpi6 : (3.141592 : ℝ) ^ 6 ≤ Real.pi ^ 6 := pow_le_pow_left₀ (by norm_num) Real.pi_gt_d6.le 6
  have hden : 5 * (3.141592 : ℝ) ^ 6 * 8 ^ 5 ≤ 5 * Real.pi ^ 6 * 8 ^ 5 := by linarith
  have hl3sq : l3 ^ 2 ≤ 40 ^ 2 := pow_le_pow_left₀ hl30 hl3 2
  have hc3 : 2 * l3 ^ 2 / (5 * Real.pi ^ 6 * 8 ^ 5) ≤
      2 * 40 ^ 2 / (5 * (3.141592 : ℝ) ^ 6 * 8 ^ 5) :=
    div_le_div₀ (by norm_num) (by linarith) (by norm_num) hden
  have hf : 0.64787 + Real.log 150000 / (4 * 150000) + 0.425 / 150000 ≤
      0.64787 + 11.91858 / (4 * 150000) + (0.425 : ℝ) / 150000 := by
    have := div_le_div_of_nonneg_right hlr (by norm_num : (0 : ℝ) ≤ 4 * 150000)
    linarith
  have hf0 : 0 ≤ 0.64787 + Real.log 150000 / (4 * 150000) + (0.425 : ℝ) / 150000 := by positivity
  have h3 : 2 * l3 ^ 2 / (5 * Real.pi ^ 6 * 8 ^ 5) *
      (0.64787 + Real.log 150000 / (4 * 150000) + 0.425 / 150000) ≤
      2 * 40 ^ 2 / (5 * (3.141592 : ℝ) ^ 6 * 8 ^ 5) *
        (0.64787 + 11.91858 / (4 * 150000) + 0.425 / 150000) :=
    mul_le_mul hc3 hf hf0 (by norm_num)
  have n3 : 2 * 40 ^ 2 / (5 * (3.141592 : ℝ) ^ 6 * 8 ^ 5) *
      (0.64787 + 11.91858 / (4 * 150000) + 0.425 / 150000) ≤ (1.317e-5 : ℝ) := by
    norm_num
  -- the `ET` term
  have het : ET * (l1 + ET / 2) ≤ 1.1377e-8 * (1.2 + 1.1377e-8 / 2) :=
    mul_le_mul hET (by linarith) (by positivity) (by norm_num)
  have n4 : 5.19 * 8 * 150000 * (1.1377e-8 * (1.2 + 1.1377e-8 / 2)) ≤ (0.0850272 : ℝ) := by
    norm_num
  -- the `E` term
  have hlog : Real.log (2 * Real.exp 2 * 150000) = Real.log 2 + 2 + Real.log 150000 := by
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_mul (by norm_num) (by positivity),
      Real.log_exp]
  have hl2 := Real.log_two_lt_d9
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hL5 : Real.log (2 * Real.exp 2 * 150000) ≤ 0.6931471808 + 2 + 11.91858 := by
    rw [hlog]
    linarith
  have hEsq : E ^ 2 ≤ (2.3921e-8) ^ 2 := pow_le_pow_left₀ hE0 hE 2
  have hEK : E ^ 2 + K ≤ (2.3921e-8) ^ 2 + 1e-19 := by linarith
  have h5 : Real.log (2 * Real.exp 2 * 150000) * (E ^ 2 + K) ≤
      (0.6931471808 + 2 + 11.91858) * ((2.3921e-8) ^ 2 + 1e-19) :=
    mul_le_mul hL5 hEK (by positivity) (by norm_num)
  have n5 : 8 * 150000 * ((0.6931471808 + 2 + 11.91858) * ((2.3921e-8) ^ 2 + 1e-19)) ≤
      (1.1e-8 : ℝ) := by
    norm_num
  linarith [h1, h2, n2, h3, n3, het, n4, h5, n5]

/-- **`drujalE_const`'s hypotheses discharged once, by real values**: every input at the end of
its range (`S = 6.798779`, `|η∘|₂ = 0.8`, `d = 1.7999·10⁻⁴`, `|η∘'''|₁ = 40`, `|η|₁ = 1.2`,
`ET`, `E` at HelfMaj's bounds, `K = 10⁻¹⁹`). -/
theorem drujalE_inst : (8.613 : ℝ) ≤ 2 * 6.798779 * 0.8 ^ 2 -
    (Real.log 150000 + 1.7) * (2 * 0.8 * 1.7999e-4 + (1.7999e-4) ^ 2) -
    2 * 40 ^ 2 / (5 * Real.pi ^ 6 * 8 ^ 5) *
      (0.64787 + Real.log 150000 / (4 * 150000) + 0.425 / 150000) -
    5.19 * 8 * 150000 * (1.1377e-8 * (1.2 + 1.1377e-8 / 2)) -
    8 * 150000 * Real.log (2 * Real.exp 2 * 150000) * ((2.3921e-8) ^ 2 + 1e-19) :=
  drujalE_const 6.798779 0.8 1.7999e-4 40 1.2 1.1377e-8 2.3921e-8 1e-19 le_rfl le_rfl
    (by norm_num) (by norm_num) le_rfl (by norm_num) le_rfl (by norm_num) le_rfl (by norm_num)
    le_rfl (by norm_num) le_rfl (by norm_num) le_rfl

end Principia.Common.TernaryGoldbach.MinW
