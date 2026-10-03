/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.Retarget
import Principia.Common.TernaryGoldbach.BandLimit

set_option autoImplicit false

/-!
# The retargeted major arcs with EASY constants: `Norms`, `CLower`, `Drujal` loosened

**EVERY LINK NAMED BELOW IS OPEN except where a theorem says otherwise. This file proves the
COMPOSITION and the arithmetic.** Nothing here proves Helfgott's major-arc analysis.

## Why

At `K = 0.00032` (`Retarget.lean`) the major arcs need `1.049·x²/49`, and with `C₀ ≥ 1.31` and
Helfgott's seven-digit constants they reach `1.0499854`. That room is spent here on the numerical
links: every constant Helfgott certified by interval arithmetic is loosened until each is either
elementary or follows from one sharp band-limiting bound, and the major side STILL reaches
`1.049` (`arith_close_easy`).

| input | Helfgott (`MajSp`) | here |
|---|---|---|
| `|η∘|₂` | `[0.8001287, 0.8001288]` | `[0.8, 0.8002]` |
| `|η₊ − η∘|₂` | `≤ 2.43e-6` | `≤ 3e-5` |
| `|η∘'''|₁` | `≤ 32.5023` | `≤ 40` |
| `|η∘'|₂²` | `≤ 2.7375293` | `≤ 3` |
| `|η*|₁` | `= √(π/2)/49` | `= √(π/2)/49` (unchanged, exact) |
| `|η*|₂²` | `≤ 1.77082/49` | `≤ 2/49` |
| `|η₊|₁`, `|η₊|₂` | `≤ 1.062319`, `≤ 0.800132` | `≤ 1.2`, `≤ 0.81` |
| `A₊` (`Drujal`'s output) | `≤ 8.7806` | `≤ 10` |
| `CLower`'s constant | `0.000834` | `0.000914` |

## The three relaxed links, each re-derived at the looser numbers

* `NormsE` — `MajSp.Norms` with the column above. Implied by `Norms` (`normsE_of_norms`).
* `CLowerE` — `eq:barbar` re-derived from `eq:karlmarx`/`eq:sasa` at `|η∘'|₂² ≤ D = 3`: the second
  integral of `eq:karlmarx` costs `2.71·D·(49/48·√(π/2) − (9/4)²/(2√(2π)))/κ² =
  2.71·3·0.2696017/49² = 0.00091290` (at `D = 2.7375293` the same line is `0.00083303`, Helfgott's
  `0.000834`); the `e^{−2κ²}` term is `< 10⁻²⁰⁰⁰`. So `0.000914`.
* `DrujalE` — `lem:drujal` (`eq:bfpink`, `eq:mardi`) at `|η|₁ ≤ 1.2`, `|η|₂ ≤ 0.81`:
  `L ≤ 2·6.798779·0.81² = 8.92136`, the `ET` term `5.19·8·150000·1.1377e-8·(1.2 + ET/2) =
  0.085027`, the `E²` term `1.0e-8`, total `9.00638 ≤ 10`.

**`CLowerE` and `DrujalE` are NOT implied by `CLower`/`Drujal` alone**, and this is said rather
than hidden: each is the same generic lemma at looser inputs, so it asks MORE of its input range
and LESS of its output. What holds is that the ORIGINAL TUPLE implies the relaxed tuple:
`clowerE_of : CLower → Norms → CLowerE` and `drujalE_of : Drujal → Norms → DrujalE` (`Norms`
supplies the tighter inputs outright). Hence `easy_of_orig`, and every discharge of the old links
discharges the new ones.

## Arithmetic (`arith_close_easy`; exact rationals, `scratchpad/easy_numbers.py`)

`ε₀ = 3.751e-5` (`3e-5 < 3.751e-5·0.8 = 3.0008e-5`). Units `x²/49`:
* main `1.31·(1.2533139·0.8² − 0.000914) = 1.0495810`;
* line 1 `≤ 1.5418e-4·1.2533143 = 1.9323e-4` (the bracket is `1.5417432e-4`);
* line 2 `≤ 1.3353e-6 + 49·2.3921e-8·1.6812·(3.1623 + 1.6812·0.81)·0.20204 = 3.1364e-6`;
* line 3 `≤ 49·976/(22135943·10⁶) = 2.2e-9`.
Net `1.0493847 ≥ 1.049`, margin `3.8·10⁻⁴`.

## The adversarial pass

* `normsE_zero_o`: `NormsE` still rejects `η∘ = 0` (`|η∘|₂ ≥ 0.8`).
* `easy_zero`: the zero weights satisfy `CLowerE` and `DrujalE`, so neither is contradictory;
  nondegeneracy lives in `NormsE`, exactly as in `MajSp`.
-/

namespace Principia.Common.TernaryGoldbach.EN

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach
open Principia.Erdos1054 (helfgottX)
open Principia.Erdos1054.Proofs.BalancedK (HelfgottAt)

/-! ## The relaxed links -/

/-- **Link [N], loosened**: `MajSp.Norms` with `|η∘|₂ ∈ [0.8, 0.8002]`, `|η₊ − η∘|₂ ≤ 3·10⁻⁵`,
`|η∘'''|₁ ≤ 40`, `|η∘'|₂² ≤ 3`, `|η*|₁ = √(π/2)/49` (exact, unchanged), `|η*|₂² ≤ 2/49`,
`|η₊|₁ ≤ 1.2`, `|η₊|₂ ≤ 0.81`. OPEN here; weight-specific. -/
def NormsE (ηp ηs ηo : ℝ → ℝ) : Prop :=
  0.8 ≤ MajSp.l2 ηo ∧ MajSp.l2 ηo ≤ 0.8002 ∧ MajSp.l2 (fun t => ηp t - ηo t) ≤ 3e-5 ∧
    MajSp.l1 (iteratedDeriv 3 ηo) ≤ 40 ∧ MajSp.l2 (deriv ηo) ^ 2 ≤ 3 ∧
    MajSp.l1 ηs = Real.sqrt (Real.pi / 2) / 49 ∧ MajSp.l2 ηs ^ 2 ≤ 2 / 49 ∧
    MajSp.l1 ηp ≤ 1.2 ∧ MajSp.l2 ηp ≤ 0.81

/-- **Link [C], loosened** — `eq:barbar` at `|η∘'|₂² ≤ 3`: `C_{η∘,η*}(N/x) ≥ (√(π/2)|η∘|₂² −
0.000914)/49` at `x = helfgottX N`. OPEN; weight-specific. -/
def CLowerE (ηo ηs : ℝ → ℝ) : Prop :=
  MajSp.l2 (deriv ηo) ^ 2 ≤ 3 → ∀ N : ℕ, Odd N → 10 ^ 27 ≤ N →
    (Real.sqrt (Real.pi / 2) * MajSp.l2 ηo ^ 2 - 0.000914) / 49 ≤
      MajSp.ccon ηo ηs ((N : ℝ) / helfgottX N)

/-- **Link [A], loosened** — `lem:drujal` (`eq:bfpink` with `eq:mardi`) at `|η|₁ ≤ 1.2`,
`|η|₂ ≤ 0.81`: `A_η(x) ≤ 10`. The sup norm and the two `err`-bounds are `MajSp.Drujal`'s. OPEN;
generic in the weight. -/
def DrujalE (η : ℝ → ℝ) : Prop :=
  MemLp η 1 (volume.restrict (Set.Ioi 0)) → (∀ t : ℝ, 0 ≤ t → |η t| ≤ 1.079955) →
    MajSp.l1 η ≤ 1.2 → MajSp.l2 η ≤ 0.81 →
      ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → MajSp.ETBound η 600000 x 1.1377e-8 →
        MajSp.EBound η x 2.3921e-8 → MajSp.amaj η x ≤ 10

/-! ## The relaxation is a weakening of the original TUPLE -/

/-- **`Norms → NormsE`**: every constant of `NormsE` is implied by Helfgott's. -/
theorem normsE_of_norms (ηp ηs ηo : ℝ → ℝ) (nm : MajSp.Norms ηp ηs ηo) : NormsE ηp ηs ηo := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := nm
  refine ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num), le_trans h3 (by norm_num),
    le_trans h4 (by norm_num), le_trans h5 (by norm_num), h6, le_trans h7 (by norm_num),
    le_trans h8 (by norm_num), le_trans h9 (by norm_num)⟩

/-- **`CLower → Norms → CLowerE`**: `Norms` supplies `|η∘'|₂² ≤ 2.7375293`, `CLower` then gives the
`0.000834` bound, which implies the `0.000914` one. (`CLower` alone does NOT imply `CLowerE`:
`CLowerE` accepts `|η∘'|₂²` up to `3`.) -/
theorem clowerE_of (ηp ηs ηo : ℝ → ℝ) (cl : MajSp.CLower ηo ηs) (nm : MajSp.Norms ηp ηs ηo) :
    CLowerE ηo ηs := by
  intro _ N hodd hN
  have h := cl nm.2.2.2.2.1 N hodd hN
  have hle : (Real.sqrt (Real.pi / 2) * MajSp.l2 ηo ^ 2 - 0.000914) / 49 ≤
      (Real.sqrt (Real.pi / 2) * MajSp.l2 ηo ^ 2 - 0.000834) / 49 :=
    div_le_div_of_nonneg_right (by linarith) (by norm_num)
  exact le_trans hle h

/-- **`Drujal → Norms → DrujalE`**: `Norms` supplies `|η₊|₁ ≤ 1.062319` and `|η₊|₂ ≤ 0.800132`,
`Drujal` then gives `A ≤ 8.7806 ≤ 10`. (`Drujal` alone does NOT imply `DrujalE`: `DrujalE`
accepts `|η|₁ ≤ 1.2`, `|η|₂ ≤ 0.81`.) -/
theorem drujalE_of (ηp ηs ηo : ℝ → ℝ) (dj : MajSp.Drujal ηp) (nm : MajSp.Norms ηp ηs ηo) :
    DrujalE ηp := by
  intro hm hsup _ _ x hx hET hE
  exact le_trans (dj hm hsup nm.2.2.2.2.2.2.2.1 nm.2.2.2.2.2.2.2.2 x hx hET hE) (by norm_num)

/-- **The original tuple implies the relaxed tuple**, so every discharge of Helfgott's
`Drujal`, `CLower`, `Norms` discharges `DrujalE`, `CLowerE`, `NormsE`. -/
theorem easy_of_orig (ηp ηs ηo : ℝ → ℝ) (dj : MajSp.Drujal ηp) (cl : MajSp.CLower ηo ηs)
    (nm : MajSp.Norms ηp ηs ηo) : DrujalE ηp ∧ CLowerE ηo ηs ∧ NormsE ηp ηs ηo :=
  ⟨drujalE_of ηp ηs ηo dj nm, clowerE_of ηp ηs ηo cl nm, normsE_of_norms ηp ηs ηo nm⟩

/-! ## The closing arithmetic at the easy constants -/

/-- **The main term**: `C₀·C ≥ 1.31·(1.2533139·0.8² − 0.000914)/49`. -/
theorem main_ge_easy (s C0 Cc lo : ℝ) (hs1 : 1.2533139 ≤ s) (hC0 : 1.31 ≤ C0)
    (hCc : (s * lo ^ 2 - 0.000914) / 49 ≤ Cc) (hlo1 : 0.8 ≤ lo) :
    1.31 * ((1.2533139 * 0.8 ^ 2 - 0.000914) / 49) ≤ C0 * Cc := by
  have hlo2' : 0.8 ^ 2 ≤ lo ^ 2 := pow_le_pow_left₀ (by norm_num) hlo1 2
  have hslo : 1.2533139 * 0.8 ^ 2 ≤ s * lo ^ 2 :=
    mul_le_mul hs1 hlo2' (by norm_num) (by linarith)
  have hCc' : (1.2533139 * 0.8 ^ 2 - 0.000914) / 49 ≤ Cc :=
    le_trans (div_le_div_of_nonneg_right (by linarith) (by norm_num)) hCc
  exact mul_le_mul hC0 hCc' (by norm_num) (by linarith)

/-- **Line 1 of `eq:opus111`** at `ε₀ = 3.751e-5`, `|η∘|₂ ≤ 0.8002`, `|η∘'''|₁ ≤ 40`: at most
`1.5418e-4·|η*|₁` (the bracket is `1.5417432e-4`). -/
theorem line1_le_easy (s lo l3 : ℝ) (hs1 : 1.2533139 ≤ s) (hs2 : s ≤ 1.2533143)
    (hlo1 : 0.8 ≤ lo) (hlo2 : lo ≤ 0.8002) (hl3 : 0 ≤ l3) (hl3' : l3 ≤ 40) :
    (2.82643 * lo ^ 2 * (2 + 3.751e-5) * 3.751e-5 +
        (4.31004 * lo ^ 2 + 0.0012 * l3 ^ 2 / 8 ^ 5) / 150000) * (s / 49) ≤
      1.5418e-4 * (1.2533143 / 49) := by
  have hlo2sq : lo ^ 2 ≤ 0.8002 ^ 2 := pow_le_pow_left₀ (by linarith) hlo2 2
  have hl3sq : l3 ^ 2 ≤ 40 ^ 2 := pow_le_pow_left₀ hl3 hl3' 2
  have hK : 2.82643 * lo ^ 2 * (2 + 3.751e-5) * 3.751e-5 +
      (4.31004 * lo ^ 2 + 0.0012 * l3 ^ 2 / 8 ^ 5) / 150000 ≤ 1.5418e-4 := by
    linarith
  exact mul_le_mul hK (div_le_div_of_nonneg_right hs2 (by norm_num))
    (div_nonneg (by linarith) (by norm_num)) (by norm_num)

/-- **Line 2 of `eq:opus111`** (corrected `E*`) at `A ≤ 10`, `|η₊|₂ ≤ 0.81`, `|η*|₂² ≤ 2/49`. -/
theorem line2_le_easy (A lp ls : ℝ) (hA : A ≤ 10) (hlp : lp ≤ 0.81) (hls0 : 0 ≤ ls)
    (hls : ls ^ 2 ≤ 2 / 49) :
    1.3353e-7 / 49 * A + 2.3921e-8 * 1.6812 * (Real.sqrt A + 1.6812 * lp) * ls ≤
      1.3353e-7 / 49 * 10 + 2.3921e-8 * 1.6812 * ((3.1623 + 1.6812 * 0.81) * 0.20204) := by
  have hsA : Real.sqrt A ≤ 3.1623 := by
    refine le_trans (Real.sqrt_le_sqrt hA) ?_
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hls' : ls ≤ 0.20204 := by nlinarith
  have hB' : Real.sqrt A + 1.6812 * lp ≤ 3.1623 + 1.6812 * 0.81 := by linarith
  have hBl : (Real.sqrt A + 1.6812 * lp) * ls ≤ (3.1623 + 1.6812 * 0.81) * 0.20204 :=
    mul_le_mul hB' hls' hls0 (by norm_num)
  linarith

/-- **The arithmetic of `ternvin.tex` 4772–4865 at the EASY constants and `C₀ ≥ 1.31`**: the
`prop:nefumo` bound at `ε₀ = 3.751e-5` forces `Re ∫_𝔐 ≥ 1.049 x²/49`. Net `1.0493847`, margin
`3.8·10⁻⁴`. -/
theorem arith_close_easy (x s C0 Cc lo l3 lp ls A Zp Zs : ℝ) (I : ℂ)
    (hx : 49 * 10 ^ 25 ≤ x) (hs1 : 1.2533139 ≤ s) (hs2 : s ≤ 1.2533143)
    (hC0 : 1.31 ≤ C0) (hCc : (s * lo ^ 2 - 0.000914) / 49 ≤ Cc)
    (hlo1 : 0.8 ≤ lo) (hlo2 : lo ≤ 0.8002) (hl3 : 0 ≤ l3) (hl3' : l3 ≤ 40)
    (hlp : lp ≤ 0.81) (hls0 : 0 ≤ ls) (hls : ls ^ 2 ≤ 2 / 49)
    (hA : A ≤ 10) (hZp : Zp ≤ 0.640209 * Real.log x)
    (hZs0 : 0 ≤ Zs) (hZs : Zs ≤ 0.0362 * Real.log x)
    (hI : ‖I - ((C0 * Cc * x ^ 2 : ℝ) : ℂ)‖ ≤
      (2.82643 * lo ^ 2 * (2 + 3.751e-5) * 3.751e-5 +
          (4.31004 * lo ^ 2 + 0.0012 * l3 ^ 2 / 8 ^ 5) / 150000) * (s / 49) * x ^ 2 +
        (1.3353e-7 / 49 * A + 2.3921e-8 * 1.6812 * (Real.sqrt A + 1.6812 * lp) * ls) * x ^ 2 +
        (2 * Zp * (24.32 * Real.log x + 0.57) +
          4 * Real.sqrt (Zp * Zs) * (18.57 * Real.log x + 28.39)) * x) :
    1.049 * x ^ 2 / 49 ≤ I.re := by
  have hX : 0 ≤ x ^ 2 := sq_nonneg x
  have hm := mul_le_mul_of_nonneg_right (main_ge_easy s C0 Cc lo hs1 hC0 hCc hlo1) hX
  have h1 := mul_le_mul_of_nonneg_right (line1_le_easy s lo l3 hs1 hs2 hlo1 hlo2 hl3 hl3') hX
  have h2 := mul_le_mul_of_nonneg_right (line2_le_easy A lp ls hA hlp hls0 hls) hX
  have h3 := MajSp.line3_le x Zp Zs hx hZp hZs0 hZs
  have habs := Complex.abs_re_le_norm (I - ((C0 * Cc * x ^ 2 : ℝ) : ℂ))
  rw [Complex.sub_re, Complex.ofReal_re] at habs
  have hlow := (abs_le.mp (le_trans habs hI)).1
  linarith only [hlow, hm, h1, h2, h3, hX]

/-! ## THE COMPOSITION -/

/-- `ε₀ = 3.751e-5 ≥ 0`. -/
theorem eps_nonneg_easy : (0 : ℝ) ≤ 3.751e-5 := by norm_num

/-- `|η₊ − η∘|₂ ≤ 3e-5` and `|η∘|₂ ≥ 0.8` give `|η₊ − η∘|₂ < ε₀|η∘|₂` at `ε₀ = 3.751e-5`
(`3.751e-5·0.8 = 3.0008e-5`). -/
theorem eps_lt_easy (a b : ℝ) (ha : a ≤ 3e-5) (hb : 0.8 ≤ b) : a < 3.751e-5 * b := by
  linarith

/-- **THE SPINE of (7.25) at `1.049` with the EASY links**: `RT.majorAt_of_links` with `Drujal`,
`CLower`, `Norms` replaced by `DrujalE`, `CLowerE`, `NormsE`, and `prop:nefumo` applied at
`ε₀ = 3.751e-5`. Application only; the arithmetic is `arith_close_easy`. -/
theorem majorAt_easy (ηp ηs ηo ηc : ℝ → ℝ) (hm : RT.HelfMajFull ηp ηc)
    (sc : MajSp.StarScale ηs ηc) (rg : MajSp.Reg ηp ηs ηo) (nf : MajSp.Nefumo ηp ηs ηo)
    (dj : DrujalE ηp) (cl : CLowerE ηo ηs) (nm : NormsE ηp ηs ηo)
    (sn : MajSp.SupN ηp ηs) (pf : RT.PlattFull) : RT.MajorLowerAt 1.049 ηp ηs := by
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
  have hA := dj rg.2.2.1 sn.1 hl1p hl2p (helfgottX N) hx hET hEp
  obtain ⟨hLp, hLs⟩ := MajSp.ls_link ηp ηs sn (helfgottX N) hx
  have hlt := eps_lt_easy _ _ hdiff hlo1
  have hnef := nf rg 3.751e-5 eps_nonneg_easy hlt N (MajSp.N_one N hN) (helfgottX N) hx
    2.3921e-8 (1.3353e-7 / 49) hEp hEs (18.57 * Real.log (helfgottX N) + 28.39)
    (24.32 * Real.log (helfgottX N) + 0.57) hLp hLs
  rw [hl1s] at hnef
  have hC := cl hld N hodd hN
  obtain ⟨hs1, hs2⟩ := MajSp.sqrt_pi_half
  exact arith_close_easy (helfgottX N) (Real.sqrt (Real.pi / 2)) (SingularSeries.sing3 N)
    (MajSp.ccon ηo ηs ((N : ℝ) / helfgottX N)) (MajSp.l2 ηo) (MajSp.l1 (iteratedDeriv 3 ηo))
    (MajSp.l2 ηp) (MajSp.l2 ηs) (MajSp.amaj ηp (helfgottX N))
    (MajSp.zk (fun t => ηp t ^ 2) 2 (helfgottX N)) (MajSp.zk (fun t => ηs t ^ 2) 2 (helfgottX N))
    _ hx hs1 hs2 (RT.c0_131 N hodd) hC hlo1 hlo2 (MajSp.l1_nonneg _) hl3 hl2p (MajSp.l2_nonneg _)
    hls hA hZp (MajSp.zk_sq_nonneg _ _ (MajSp.x_nonneg _ hx)) hZs hnef

/-- **`HelfgottAt 0.00032` on Helfgott's own weights from the EASY links**: `RT.helfgottAt_of_links`
with `DrujalE`, `CLowerE`, `NormsE` in place of `Drujal`, `CLower`, `Norms`, and link 0
(`SupBounds`) supplied by the theorem `BL.supBounds_helf`. -/
theorem helfgottAt_easy (pf : RT.PlattFull)
    (hm : RT.HelfMajFull HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (rg : MajSp.Reg HW.etaPlus HW.etaStar HW.etaCirc)
    (nf : MajSp.Nefumo HW.etaPlus HW.etaStar HW.etaCirc) (dj : DrujalE HW.etaPlus)
    (cl : CLowerE HW.etaCirc HW.etaStar) (nm : NormsE HW.etaPlus HW.etaStar HW.etaCirc)
    (sn : MajSp.SupN HW.etaPlus HW.etaStar)
    (mn : RT.MinorUpperAt 0.9845 HW.etaPlus HW.etaStar) : HelfgottAt 0.00032 :=
  RT.helfgottAt_of_smooth HW.etaPlus HW.etaStar BL.supBounds_helf
    (majorAt_easy HW.etaPlus HW.etaStar HW.etaCirc (HW.mconv HW.eta2 HW.phi) hm RT.starScale_helf
      rg nf dj cl nm sn pf) mn

/-! ## THE ADVERSARIAL PASS -/

/-- **`NormsE` still rejects `η∘ = 0`** (`|η∘|₂ ≥ 0.8`). -/
theorem normsE_zero_o (ηp ηs : ℝ → ℝ) : ¬ NormsE ηp ηs 0 := by
  intro h
  have h1 := h.1
  rw [MajSp.l2_zero] at h1
  norm_num at h1

/-- **The zero weights satisfy `CLowerE` and `DrujalE`**: neither relaxed link is contradictory,
and neither forces nondegeneracy (that lives in `NormsE` and `HelfMajFull`). -/
theorem easy_zero : CLowerE 0 0 ∧ DrujalE 0 := by
  refine ⟨?_, ?_⟩
  · intro _ N _ _
    have h : MajSp.ccon 0 0 ((N : ℝ) / helfgottX N) = 0 := by simp [MajSp.ccon]
    rw [h, MajSp.l2_zero]
    norm_num
  · intro _ _ _ _ x _ _ _
    have h : MajSp.amaj 0 x = 0 := by simp [MajSp.amaj, Smooth.smSum_zero]
    rw [h]
    norm_num

end Principia.Common.TernaryGoldbach.EN
