/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.OstopL
import Principia.Common.Chebyshev.Upper

set_option autoImplicit false

/-!
# The spine of the corrected `prop:gorsh` (`OL.GorshL`) from `OL.MinMainL`

**`OL.GorshL` is COMPOSED here; five named inputs remain, all published or numeric.** Target:
`OL.GorshL η* φ` (`OstopL.lean`): for `x ≥ 4.9·10²⁶`, `r ∈ [150000, r₁(x/49)]`, `α` off the
arcs `𝔐_{8,r}(y)`, `y = x/49`: `|S_{η*}(α,x)| ≤ (g̃(r) + C_{φ,3}(K))|φ|₁y`, `η* = (η₂ ∗_M φ)(49·)`
(`ternvin.tex` 2086-2196 redone per scale, F7; plan `scratchpad/spines/minmain_spine.md` §2.5-2.6).

## The spine

```
 G1 mellinLe_all  |S_{η*}(α,x)| ≤ ∫₀^∞ |S_{η₂}(α,wy)| φ(w) dw/w, every φ ≥ 0 in L¹   PROVED
 G2 off_arc       α ∉ 𝔐_{8,r}(y), q ≤ r, (a,q) = 1  ⟹  |2α − a/q| ≥ 8r/(qy)          PROVED
 G3 dirichlet_at  ∀Y ∃ reduced a/q, q ≤ Q(Y) = (3/4)Y^{2/3}, |2α − a/q| ≤ 1/(qQ(Y))   PROVED
 G4 arg_lower     min(w,1)·r ≤ max(1,|δ|/8)·q,  δ = wy(2α − a/q)                       PROVED
    arg_upper     q ≤ Y^{1/3}/6  ⟹  max(1,|δ|/8)·q ≤ Y^{1/3}/6                          PROVED
 M2 kraw_le_gYL   krawL(Y,δ,q) ≤ gYL(Y, max(1,|δ|/8)q)·Y  (δ₀^a q^b ≤ 2^a r^b)         PROVED
 M1 merkel_of_rs62  lem:merkel from RS62 Thm 15 (small q by `decide`)                 PROVED
 G5/G6 scale_bound |S_{η₂}(α,wy)| ≤ gYL(wy, min(w,1)r)·wy  for w ≥ 1/K                  PROVED
      from  MinMainL (published, L repaired), GYMono, HLeG                              NAMED
 G7 norm_smSum_eta2_le  |S_{η₂}(α,Y)| ≤ 1.04488·Y, all Y > 0, from Austeria            PROVED
      Austeria = cor:austeria: Σ Λ(n)η₂(n/Y) ≤ 1.04488Y (Y ≥ 1)                        NAMED
 G8 gorsh_core    integrate against φ(w)dw/w over (0,w₁] ∪ (w₁,1] ∪ (1,∞)              PROVED
      gtlInt: the g-weighted pieces of gTL are integrable (gYL ≤ gCap)                 PROVED
 gorshL_of_links : MinMainL → Merkel → GYMono → HLeG → Austeria → MellinLe → GTLInt → GorshL
 gorshL_of_open  : MinMainL → RS62Thm15 → GYMono → HLeG → Austeria → OL.GorshL η* φ
```

## G7 priced (`scratchpad/gorsh/g7_price.py`)

Proved here: `Σ Λ(n)η₂(n/Y) ≤ 4 log 2·ψ(Y)` (`sEta2_le_psi`), hence `≤ 3.0776Y` for
`Y ≥ 3·10⁹` (`austeriaAt_cheb`, Principia's `ψ ≤ 1.11t`) and `≤ 15Y` for all `Y > 0`
(`sEta2_le_lin`, Mathlib's `ψ ≤ (log 4 + 4)t`). In place of `1.04488` inside `C_{φ,3}` these
give `T/x = 1.063·10⁻³` resp. `5.18·10⁻³` at `x = 4.9·10²⁶`, against `LamberNumL`'s `3.7·10⁻⁴`
(`3.610·10⁻⁴` at `1.04488`); the closing test `≤ 1.0154` then needs `M̃ ≤ 0.80910` resp.
`0.80498` instead of `0.8095` (the true sup is about `0.7924`). They FIT only as a RESTATEMENT of
`cPhi3`, `gTL`'s sliver and the `T` constant, which `OstopL` types at `1.04488`: not done here.

## The numeric links, checked before stating (`scratchpad/gorsh/gorsh_num.py`, `gymono2.py`)

Independent mpmath (30-60 digits) transcription of `OL.gYL`, `MinSp.rR`, `MinSp.bigF`, `OL.lLc`.
* `HLeG` is stated with the SCALED argument's worst case `(Y, r₁(Y))`: G6 needs
  `hL(Y) ≤ gYL(Y, a)·Y` at `a = min(w,1)r ≤ r₁(wy)` (`arg_le_r1y`), and `GYMono` moves `a` up to
  `r₁(Y)`. Ratio `gYL(Y,r₁(Y))·Y/hL(Y)` on a 1100-point log grid of `Y ∈ [3.4·10²³, 10^{10000}]`:
  **minimum 1.29971 at `Y = 3.4·10²³`** (`1.6247` against the unloosened `h`), increasing after.
  The UNSCALED pairing `(y/K, r₁(y))` at `y = 10²⁵` gives `0.92353` (i.e. `1.154` against `h`,
  matching the OstopL verifier): it is not the pairing the proof uses.
* `GYMono`: `d gYL(Y,r)/d log r < 0` at every point of a 600-point log grid of
  `r ∈ [175, Y^{1/3}/6]`, for 15 scales `Y ∈ [3.4·10²³, 10^{10000}]`; the maximum is always at
  the top end `r = Y^{1/3}/6` (`−0.00268` at `Y = 3.4·10²³`).

Floating-point SCOPING, not certificates: both stay NAMED. `HLeG` is CERTIFIED at one point,
`Y = 10³⁰` (`hLeG_at_1e30`, ratio `≥ 1.046`), which also pins its scaling. `GYMono` is not
discharged at any point: it is monotonicity on a continuum (`lem:vinc`'s derivative argument,
`eq:hut`), which no finite `norm_num` check certifies. `HLeG` for all `Y` needs more than the
bounds this file certifies (`R_{Y,2t} ≥ 0.41415`, `ϝ ≥ 3.75`, `L_t/t` and `3.2Y^{−1/6}` dropped):
those give ratio `0.714` at `Y = 3.4·10²³` and cross `1` only near `Y ≈ 10²⁹`
(`scratchpad/gorsh/hleg_crude.py`); a proof needs the sharp `R_{Y,2r₁(Y)} ≥ 0.63` and
`ϝ(r₁(Y)) ≥ 5.6` of `lem:gosia`'s own argument.

## Why `Y ≥ 3.4·10²³` suffices

Every scale used is `wy` with `w ≥ w₁ ≥ 1/K`, `K = (log y)/2`, and `2y/log y ≥ 3.4·10²³` for
`y ≥ 10²⁵` (`scale_ge`: `log y ≤ 84 log 2 + y/10²⁵ − 1`).
-/

namespace Principia.Common.TernaryGoldbach.GS

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach
open scoped ArithmeticFunction

/-! ## (1) Objects -/

/-- **`h′(Y)·Y`**: the right side of `OL.MinMainL`'s loosened second case,
`0.3409Y^{5/6}(log Y)^{3/2} + 1522.5Y^{2/3} log Y`. -/
noncomputable def hL (Y : ℝ) : ℝ :=
  0.3409 * Y ^ ((5 : ℝ) / 6) * Real.log Y ^ ((3 : ℝ) / 2) +
    1522.5 * Y ^ ((2 : ℝ) / 3) * Real.log Y

/-- **`Σ_n Λ(n) η₂(n/Y)`**, the left side of `cor:austeria` (`ternvin.tex` 5530-5540). -/
noncomputable def sEta2 (Y : ℝ) : ℝ := ∑' n : ℕ, Λ n * HW.eta2 ((n : ℝ) / Y)

/-- **The majorant integrated in G8**: `y·1.04488·φ(w)` on `w ≤ w₁`, `y·gYL(wy,wr)φ(w)` on
`w₁ < w ≤ 1`, `y·gYL(wy,r)φ(w)` on `w > 1`. -/
noncomputable def gPiece (φ : ℝ → ℝ) (y r w₁ w : ℝ) : ℝ :=
  if w ≤ w₁ then y * (1.04488 * φ w) else
    if w ≤ 1 then y * (OL.gYL (w * y) (w * r) * φ w) else y * (OL.gYL (w * y) r * φ w)

/-! ## (2) The named links -/

/-- **Link [G1] — `eq:chemdames` as an inequality**: `|S_{η*}(α,x)| ≤ ∫₀^∞|S_{η₂}(α,wy)|φ(w)dw/w`
for `η* = (η₂ ∗_M φ)(49·)`, `y = x/49`. PROVED for every `φ ≥ 0` in `L¹(0,∞)`
(`mellinLe_all`). -/
def MellinLe (ηs φ : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, ηs t = HW.mconv HW.eta2 φ (49 * t)) → (∀ t : ℝ, 0 ≤ t → 0 ≤ φ t) →
    IntegrableOn φ (Set.Ioi 0) → ∀ x : ℝ, 0 < x → ∀ α : ℝ,
      ‖Smooth.smSum ηs x α‖ ≤
        ∫ w in Set.Ioi (0 : ℝ), ‖Smooth.smSum HW.eta2 (w * (x / 49)) α‖ * φ w / w

/-- **Link [G7, cited] — `cor:austeria`** (`ternvin.tex` 5530-5540): `Σ_n Λ(n)η₂(n/Y) ≤ 1.04488Y`
for `Y ≥ 1`. It rests on Platt's verification of RH to height `3.061·10¹⁰` (a cited machine
computation) plus a computation for `Y < 2000`. Only the `1.04488` branch of its `min` is
transcribed. -/
def Austeria : Prop := ∀ Y : ℝ, 1 ≤ Y → sEta2 Y ≤ 1.04488 * Y

/-- **Link [RS62, cited] — Rosser-Schoenfeld 1962, Theorem 15**: `n/φ(n) < e^γ log log n +
2.50637/log log n` for `n ≥ 3` (no exception with `2.50637`; the exception `223092870` is for
the constant `2.5`). -/
def RS62Thm15 : Prop := ∀ n : ℕ, 3 ≤ n → (n : ℝ) / (Nat.totient n) < MinSp.bigF n

/-- **Link [M1] — `lem:merkel`** (`ternvin.tex` 1925-1939): `q/φ(q) < ϝ(r)` for `q ≥ 1`,
`r ≥ max(3, q)`. Reduced to `RS62Thm15` by `merkel_of_rs62`. -/
def Merkel : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∀ r : ℝ, 3 ≤ r → (q : ℝ) ≤ r → (q : ℝ) / (Nat.totient q) < MinSp.bigF r

/-- **Link [GYMono] — `lem:vinc` at `K = 1` on the corrected `L`**: `gYL(Y,·)` is non-increasing
on `[175, Y^{1/3}/6]` for every `Y ≥ 3.4·10²³`. NUMERIC (module docstring); NAMED. -/
def GYMono : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → AntitoneOn (OL.gYL Y) (Set.Icc 175 (Y ^ ((1 : ℝ) / 3) / 6))

/-- **Link [HLeG] — the second case fits under `g`, at the SCALED argument's worst case**:
`h′(Y) ≤ gYL(Y, r₁(Y))·Y` for `Y ≥ 3.4·10²³`, `r₁(Y) = (3/8)Y^{4/15}`. NUMERIC, minimum ratio
`1.29971` at `Y = 3.4·10²³` (module docstring); NAMED. NOT `lem:gosia` (whose inequality fails
at `3.47·10²³`). -/
def HLeG : Prop := ∀ Y : ℝ, 3.4e23 ≤ Y → hL Y ≤ OL.gYL Y (MinSp.r1y Y) * Y

/-- **Link [GTLInt] — the `g`-weighted pieces of `gTL` are integrable** for every `φ ∈ L¹(0,∞)`:
`w ↦ gYL(wy,wr)φ(w)` on `(w₁,1]` and `w ↦ gYL(wy,r)φ(w)` on `(1,∞)`, `w₁ = max(1/K, 1000/r)`.
Without it `gTL`'s integrals are junk `0`. PROVED (`gtlInt`: `0 < gYL ≤ gCap(r)` on both
pieces, and `gYL` is measurable). -/
def GTLInt : Prop :=
  ∀ φ : ℝ → ℝ, IntegrableOn φ (Set.Ioi 0) → ∀ y : ℝ, 10 ^ 25 ≤ y →
    ∀ r : ℝ, 150000 ≤ r → r ≤ MinSp.r1y y →
      IntegrableOn (fun w => OL.gYL (w * y) (w * r) * φ w)
          (Set.Ioc (max (1 / MinSp.kK y) (1000 / r)) 1) ∧
        IntegrableOn (fun w => OL.gYL (w * y) r * φ w) (Set.Ioi 1)

/-! ## (3) G2-G4: the per-scale Dirichlet data -/

/-- **[G2] The off-arc lemma**: `α ∉ 𝔐_{8,r}(y)` and a reduced `a/q` with `q ≤ r` give
`|2α − a/q| ≥ 8r/(qy)`. (`a` even: `q` is odd and `α` is near `(a/2)/q`, an odd arc of
half-width `4r/(qy)`; `a` odd: `α` is near `a/(2q)`, an even arc, `2q ≤ 2r`.) -/
theorem off_arc (r : ℕ) (y : ℝ) (hy : 0 < y) (α : ℝ) (hα : α ∉ Smooth.arcs 8 r y)
    (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hqr : q ≤ r) (hg : Int.gcd a q = 1) :
    8 * (r : ℝ) / (q * y) ≤ |2 * α - a / q| := by
  by_contra hlt'
  have hlt := lt_of_not_ge hlt'
  apply hα
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq0' : (q : ℝ) ≠ 0 := hq0.ne'
  have hy0' : y ≠ 0 := hy.ne'
  have hcop : IsCoprime a (q : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hg
  have hhalf : |α - a / (2 * q)| < 4 * r / (q * y) := by
    have e1 : α - a / (2 * q) = (2 * α - a / q) / 2 := by
      field_simp
    have e2 : 4 * (r : ℝ) / (q * y) = 8 * r / (q * y) / 2 := by ring
    rw [e1, e2, abs_div, abs_two]
    exact div_lt_div_of_pos_right hlt two_pos
  simp only [Smooth.arcs, Set.mem_union, Set.mem_iUnion, Set.mem_Icc, Set.mem_Ioo]
  rcases Int.even_or_odd a with ⟨b, hb⟩ | hodd
  · have h2b : IsCoprime (2 * b) (q : ℤ) := by rwa [two_mul, ← hb]
    have hqo : Odd q := (Int.odd_coe_nat q).mp (Int.isCoprime_two_left.mp h2b.of_mul_left_left)
    have hbq : Int.gcd b q = 1 := Int.isCoprime_iff_gcd_eq_one.mp h2b.of_mul_left_right
    have hc : (a : ℝ) / (2 * q) = (b : ℝ) / q := by
      rw [hb]
      push_cast
      field_simp
      ring
    have hw : 8 * (r : ℝ) / (2 * q * y) = 4 * r / (q * y) := by
      field_simp
      ring
    rw [hc] at hhalf
    refine Or.inl ⟨q, ⟨hq, hqr⟩, hqo, b, hbq, ?_, ?_⟩ <;> rw [hw] <;>
      linarith [(abs_lt.mp hhalf).1, (abs_lt.mp hhalf).2]
  · have h2 : IsCoprime a 2 := (Int.isCoprime_two_left.mpr hodd).symm
    have hg2 : Int.gcd a ((2 * q : ℕ) : ℤ) = 1 := by
      push_cast
      exact Int.isCoprime_iff_gcd_eq_one.mp (h2.mul_right hcop)
    have hc : (a : ℝ) / ((2 * q : ℕ) : ℝ) = a / (2 * q) := by push_cast; ring
    have hw : 8 * (r : ℝ) / ((2 * q : ℕ) * y) = 4 * r / (q * y) := by
      push_cast
      field_simp
      ring
    refine Or.inr ⟨2 * q, ⟨by omega, by omega⟩, even_two_mul q, a, hg2, ?_, ?_⟩ <;>
      rw [hc, hw] <;> linarith [(abs_lt.mp hhalf).1, (abs_lt.mp hhalf).2]

/-- **[G3] Dirichlet at scale `Y`**: a reduced `a/q` with `1 ≤ q ≤ Q = (3/4)Y^{2/3}` and
`|2α − a/q| ≤ 1/(qQ)`, whenever `Q ≥ 1` (Mathlib `Real.exists_rat_abs_sub_le_and_den_le`
at `n = ⌊Q⌋`). -/
theorem dirichlet_at (α Y : ℝ) (hQ : 1 ≤ 3 / 4 * Y ^ ((2 : ℝ) / 3)) :
    ∃ a : ℤ, ∃ q : ℕ, 1 ≤ q ∧ Int.gcd a q = 1 ∧ (q : ℝ) ≤ 3 / 4 * Y ^ ((2 : ℝ) / 3) ∧
      |2 * α - a / q| ≤ 1 / (q * (3 / 4 * Y ^ ((2 : ℝ) / 3))) := by
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = 3 / 4 * Y ^ ((2 : ℝ) / 3) := ⟨_, rfl⟩
  rw [← hQdef] at hQ ⊢
  have hQ0 : 0 ≤ Q := by linarith
  have hn : 0 < ⌊Q⌋₊ := Nat.floor_pos.mpr hQ
  obtain ⟨ρ, h1, h2⟩ := Real.exists_rat_abs_sub_le_and_den_le (2 * α) hn
  have hd : (0 : ℝ) < ρ.den := by exact_mod_cast ρ.den_pos
  have hfl : (⌊Q⌋₊ : ℝ) ≤ Q := Nat.floor_le hQ0
  have hlt : Q < (⌊Q⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one Q
  refine ⟨ρ.num, ρ.den, ρ.den_pos, ρ.reduced, ?_, ?_⟩
  · have : (ρ.den : ℝ) ≤ ⌊Q⌋₊ := by exact_mod_cast h2
    linarith
  · rw [← Rat.cast_def]
    refine le_trans h1 ?_
    rw [div_le_div_iff₀ (by positivity) (mul_pos hd (by linarith)), one_mul, one_mul]
    nlinarith

/-- **[G4] The argument is at least `min(w,1)·r`**: with `δ = wy(2α − a/q)`,
`max(1,|δ|/8)·q ≥ w·r` if `q ≤ r` (G2), and `≥ q > r` otherwise. -/
theorem arg_lower (r : ℕ) (y w : ℝ) (hy : 0 < y) (hw : 0 < w) (α : ℝ)
    (hα : α ∉ Smooth.arcs 8 r y) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hg : Int.gcd a q = 1) :
    min w 1 * r ≤ max 1 (|w * y * (2 * α - a / q)| / 8) * q := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  rcases le_or_gt q r with hqr | hqr
  · have hoff := off_arc r y hy α hα a q hq hqr hg
    have h1 : w * y * (8 * r / (q * y)) ≤ |w * y * (2 * α - a / q)| := by
      rw [abs_mul, abs_of_pos (mul_pos hw hy)]
      exact mul_le_mul_of_nonneg_left hoff (mul_pos hw hy).le
    have h2 : w * y * (8 * r / (q * y)) = 8 * (w * r) / q := by
      field_simp
    rw [h2, div_le_iff₀ hq0] at h1
    calc min w 1 * r ≤ w * r := mul_le_mul_of_nonneg_right (min_le_left _ _) hr0
      _ ≤ |w * y * (2 * α - a / q)| / 8 * q := by
          rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]
          linarith
      _ ≤ max 1 (|w * y * (2 * α - a / q)| / 8) * q :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hq0.le
  · have hqr' : (r : ℝ) < q := by exact_mod_cast hqr
    calc min w 1 * r ≤ 1 * r := mul_le_mul_of_nonneg_right (min_le_right _ _) hr0
      _ ≤ 1 * q := by linarith
      _ ≤ max 1 (|w * y * (2 * α - a / q)| / 8) * q :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hq0.le

/-- `Y = u³`, `Y^{1/3} = u`, `Y^{2/3} = u²` for `Y > 0`. -/
theorem cube_rep (Y : ℝ) (hY : 0 < Y) : ∃ u : ℝ, 0 < u ∧ Y ^ ((1 : ℝ) / 3) = u ∧
    Y ^ ((2 : ℝ) / 3) = u ^ 2 ∧ Y = u ^ 3 := by
  refine ⟨Y ^ ((1 : ℝ) / 3), Real.rpow_pos_of_pos hY _, rfl, ?_, ?_⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hY.le]
    norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hY.le]
    norm_num

/-- **[G4] The argument stays in `lem:vinc`'s range**: if `q ≤ Y^{1/3}/6` then
`max(1,|δ|/8)·q ≤ Y^{1/3}/6`, since `|δ|q/8 ≤ Y/(8Q(Y)) = Y^{1/3}/6`. -/
theorem arg_upper (Y : ℝ) (hY : 0 < Y) (α : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q)
    (hd : |2 * α - a / q| ≤ 1 / (q * (3 / 4 * Y ^ ((2 : ℝ) / 3))))
    (hsm : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6) :
    max 1 (|Y * (2 * α - a / q)| / 8) * q ≤ Y ^ ((1 : ℝ) / 3) / 6 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq0' : (q : ℝ) ≠ 0 := hq0.ne'
  obtain ⟨u, hu0, hu1, hu2, hu3⟩ := cube_rep Y hY
  have hu0' : u ≠ 0 := hu0.ne'
  rw [hu2] at hd
  rw [hu1] at hsm ⊢
  rcases le_total 1 (|Y * (2 * α - a / q)| / 8) with h | h
  · rw [max_eq_right h, abs_mul, abs_of_pos hY]
    have h2 : Y * (1 / (q * (3 / 4 * u ^ 2))) / 8 * q = u / 6 := by
      rw [hu3]
      field_simp
      norm_num
    calc Y * |2 * α - a / q| / 8 * q ≤ Y * (1 / (q * (3 / 4 * u ^ 2))) / 8 * q := by
          gcongr
      _ = u / 6 := h2
  · rw [max_eq_left h, one_mul]
    exact hsm

/-! ## (4) M2: from `eq:kraw` to `eq:syryza` on the corrected `L` -/

/-- `R_{Y,t} ≥ 0.41415` for `1/4 ≤ t ≤ Y^{1/3}/3` (both logarithms in `R` are then genuine). -/
theorem rR_ge (Y t : ℝ) (hY : 0 < Y) (ht : 1 / 4 ≤ t) (htY : t ≤ Y ^ ((1 : ℝ) / 3) / 3) :
    0.41415 ≤ MinSp.rR Y t := by
  unfold MinSp.rR
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = Y ^ ((1 : ℝ) / 3) := ⟨_, rfl⟩
  rw [← hc] at htY ⊢
  have hc0 : 0 < c := hc ▸ Real.rpow_pos_of_pos hY _
  have h4 : 0 ≤ Real.log (4 * t) := Real.log_nonneg (by linarith)
  have hq : 1 < 9 * c / (2.004 * t) := by
    rw [one_lt_div (by positivity)]
    linarith
  have hl : 0 < Real.log (9 * c / (2.004 * t)) := Real.log_pos hq
  have hfr : 0 ≤ Real.log (4 * t) / (2 * Real.log (9 * c / (2.004 * t))) :=
    div_nonneg h4 (by linarith)
  have hlg : 0 ≤ Real.log (1 + Real.log (4 * t) / (2 * Real.log (9 * c / (2.004 * t)))) :=
    Real.log_nonneg (by linarith)
  linarith

/-- **The `L` comparison of M2**: with `δ₀q = 2r'`, `δ₀ ≥ 2`, `q ≤ r'` and `q/φ(q) ≤ ϝ(r')`,
`L_{δ₀,q} ≤ L_{r'}` (`δ₀^a q^b ≤ 2^a r'^b` for `a < b`, `ternvin.tex` 1967-1969). -/
theorem ltosca_le (d rp : ℝ) (q : ℕ) (hq : 1 ≤ q) (hd : 2 ≤ d) (hdq : d * q = 2 * rp)
    (hqr : (q : ℝ) ≤ rp) (hF : (q : ℝ) / Nat.totient q ≤ MinSp.bigF rp) :
    OL.lToscaL d q ≤ OL.lLc rp := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hd0 : (0 : ℝ) < d := by linarith
  have hrp0 : 0 < rp := by linarith
  have hφ0 : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hlog : Real.log d + Real.log q = Real.log 2 + Real.log rp := by
    rw [← Real.log_mul hd0.ne' hq0.ne', hdq, Real.log_mul two_ne_zero hrp0.ne']
  have hlq : Real.log q ≤ Real.log rp := Real.log_le_log hq0 hqr
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hld : Real.log 2 ≤ Real.log d := Real.log_le_log two_pos hd
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have e1 : Real.log (d ^ ((7 : ℝ) / 4) * (q : ℝ) ^ ((13 : ℝ) / 4)) =
      7 / 4 * Real.log d + 13 / 4 * Real.log q := by
    rw [Real.log_mul (Real.rpow_pos_of_pos hd0 _).ne' (Real.rpow_pos_of_pos hq0 _).ne',
      Real.log_rpow hd0, Real.log_rpow hq0]
  have e2 : Real.log ((q : ℝ) ^ (13.6516 : ℝ) * d ^ (1.7984 : ℝ)) =
      13.6516 * Real.log q + 1.7984 * Real.log d := by
    rw [Real.log_mul (Real.rpow_pos_of_pos hq0 _).ne' (Real.rpow_pos_of_pos hd0 _).ne',
      Real.log_rpow hq0, Real.log_rpow hd0]
  have hqφ : 0 ≤ (q : ℝ) / Nat.totient q := div_nonneg hq0.le hφ0.le
  have hX : 7 / 4 * Real.log d + 13 / 4 * Real.log q + 80 / 9 ≤
      7 / 4 * Real.log 2 + 13 / 4 * Real.log rp + 80 / 9 := by linarith
  have hmain : (7 / 4 * Real.log d + 13 / 4 * Real.log q + 80 / 9) /
      ((Nat.totient q : ℝ) / q) ≤
      MinSp.bigF rp * (7 / 4 * Real.log 2 + 13 / 4 * Real.log rp + 80 / 9) := by
    rw [div_div_eq_mul_div, mul_div_assoc, mul_comm (MinSp.bigF rp)]
    exact mul_le_mul hX hF hqφ (by linarith)
  unfold OL.lToscaL OL.lLc
  rw [e1, e2, OL.log_two_rpow_mul _ _ rp hrp0, OL.log_two_rpow_mul _ _ rp hrp0]
  linarith

/-- **[M2] `eq:kraw` ⟹ `eq:monoro`/`eq:syryza` on the corrected `L`**: at `δ₀ = max(2,|δ|/4)`
and `r' = max(1,|δ|/8)q` (so `δ₀q = 2r'`), `krawL(Y,δ,q) ≤ gYL(Y,r')·Y`, from `lem:merkel`
(`Merkel`) and `r' ≤ Y^{1/3}/6` (which keeps `R_{Y,2r'} ≥ 0.41415`). -/
theorem kraw_le_gYL (hmk : Merkel) (Y δ : ℝ) (q : ℕ) (hq : 1 ≤ q) (hY : 0 < Y)
    (h3 : 3 ≤ max 1 (|δ| / 8) * q) (hup : max 1 (|δ| / 8) * q ≤ Y ^ ((1 : ℝ) / 3) / 6) :
    OL.krawL Y δ q ≤ OL.gYL Y (max 1 (|δ| / 8) * q) * Y := by
  obtain ⟨rp, hrp⟩ : ∃ rp : ℝ, rp = max 1 (|δ| / 8) * q := ⟨_, rfl⟩
  rw [← hrp] at h3 hup ⊢
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hdz : OC.dz δ = 2 * max 1 (|δ| / 8) := by
    unfold OC.dz
    rcases le_total 1 (|δ| / 8) with h | h
    · rw [max_eq_right h, max_eq_right (by linarith)]
      ring
    · rw [max_eq_left h, max_eq_left (by linarith)]
      norm_num
  have hdq : OC.dz δ * q = 2 * rp := by
    rw [hdz, hrp]
    ring
  have hd2 : 2 ≤ OC.dz δ := le_max_left _ _
  have hd0 : 0 < OC.dz δ := by linarith
  have hqr : (q : ℝ) ≤ rp := by
    rw [hrp]
    nlinarith [le_max_left 1 (|δ| / 8)]
  have hrp0 : 0 < rp := by linarith
  have hφ0 : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hF : (q : ℝ) / Nat.totient q ≤ MinSp.bigF rp := (hmk q hq rp h3 hqr).le
  have hFq : (q : ℝ) ≤ MinSp.bigF rp * Nat.totient q := (div_le_iff₀ hφ0).mp hF
  have hF0 : 0 ≤ MinSp.bigF rp := le_trans (div_nonneg hq0.le hφ0.le) hF
  have hR := rR_ge Y (2 * rp) hY (by linarith) (by linarith)
  have hlog2 : 0 ≤ Real.log (2 * rp) := Real.log_nonneg (by linarith)
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = MinSp.rR Y (2 * rp) * Real.log (2 * rp) + 0.5 := ⟨_, rfl⟩
  have hA : 0 ≤ A := by
    rw [hAdef]
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ MinSp.rR Y (2 * rp)) hlog2
    linarith
  have hs2 : 0 < Real.sqrt (2 * rp) := Real.sqrt_pos.mpr (by linarith)
  have hsd : 0 < Real.sqrt (OC.dz δ * Nat.totient q) := Real.sqrt_pos.mpr (by positivity)
  have hkey : 1 / Real.sqrt (OC.dz δ * Nat.totient q) ≤
      Real.sqrt (MinSp.bigF rp) / Real.sqrt (2 * rp) := by
    rw [div_le_div_iff₀ hsd hs2, one_mul, ← Real.sqrt_mul hF0]
    apply Real.sqrt_le_sqrt
    rw [← hdq]
    calc OC.dz δ * q ≤ OC.dz δ * (MinSp.bigF rp * Nat.totient q) :=
          mul_le_mul_of_nonneg_left hFq hd0.le
      _ = MinSp.bigF rp * (OC.dz δ * Nat.totient q) := by ring
  have hT1 : A / Real.sqrt (OC.dz δ * Nat.totient q) * Y ≤
      A * Real.sqrt (MinSp.bigF rp) / Real.sqrt (2 * rp) * Y := by
    apply mul_le_mul_of_nonneg_right _ hY.le
    calc A / Real.sqrt (OC.dz δ * Nat.totient q)
        = A * (1 / Real.sqrt (OC.dz δ * Nat.totient q)) := by ring
      _ ≤ A * (Real.sqrt (MinSp.bigF rp) / Real.sqrt (2 * rp)) :=
          mul_le_mul_of_nonneg_left hkey hA
      _ = A * Real.sqrt (MinSp.bigF rp) / Real.sqrt (2 * rp) := by ring
  have hlt := ltosca_le (OC.dz δ) rp q hq hd2 hdq hqr hF
  have hT3 : 2 * Y / (2 * rp) * OL.lToscaL (OC.dz δ) q ≤ OL.lLc rp / rp * Y := by
    rw [mul_div_mul_left Y rp two_ne_zero]
    calc Y / rp * OL.lToscaL (OC.dz δ) q ≤ Y / rp * OL.lLc rp :=
          mul_le_mul_of_nonneg_left hlt (div_nonneg hY.le hrp0.le)
      _ = OL.lLc rp / rp * Y := by ring
  have hT4 : Y ^ ((5 : ℝ) / 6) = Y ^ (-(1 : ℝ) / 6) * Y := by
    rw [← Real.rpow_add_one hY.ne']
    norm_num
  unfold OL.krawL OL.gYL
  rw [hdq, hT4, ← hAdef]
  calc _ ≤ A * Real.sqrt (MinSp.bigF rp) / Real.sqrt (2 * rp) * Y +
        2.5 * Y / Real.sqrt (2 * rp) + OL.lLc rp / rp * Y +
        3.2 * (Y ^ (-(1 : ℝ) / 6) * Y) := by linarith
    _ = _ := by ring

/-! ## (5) G5 + G6: the bound at one scale `wy` -/

/-- `r₁(Y) ≤ Y^{1/3}/6` for `Y ≥ 3.4·10²³` (`(9/4)^{15} ≤ Y`). -/
theorem r1y_le_third (Y : ℝ) (hY : 3.4e23 ≤ Y) : MinSp.r1y Y ≤ Y ^ ((1 : ℝ) / 3) / 6 := by
  have hY0 : 0 < Y := lt_of_lt_of_le (by norm_num) hY
  unfold MinSp.r1y
  have hsplit : Y ^ ((1 : ℝ) / 3) = Y ^ ((4 : ℝ) / 15) * Y ^ ((1 : ℝ) / 15) := by
    rw [← Real.rpow_add hY0]
    norm_num
  have h15 : (9 / 4 : ℝ) ≤ Y ^ ((1 : ℝ) / 15) := by
    have h1 : (9 / 4 : ℝ) ^ (15 : ℕ) ≤ Y := le_trans (by norm_num) hY
    have h2 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 1 / 15)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h2
    norm_num at h2
    exact h2
  rw [hsplit]
  have h4 : 0 < Y ^ ((4 : ℝ) / 15) := Real.rpow_pos_of_pos hY0 _
  nlinarith [mul_le_mul_of_nonneg_left h15 h4.le]

/-- **The F7 SCALED argument never exceeds `r₁(wy)`**: `min(w,1)·r ≤ (3/8)(wy)^{4/15}` when
`r ≤ (3/8)y^{4/15}` (`w ≤ w^{4/15}` for `w ≤ 1`). -/
theorem arg_le_r1y (y w r : ℝ) (hy : 0 < y) (hw : 0 < w) (hr : r ≤ MinSp.r1y y) :
    min w 1 * r ≤ MinSp.r1y (w * y) := by
  unfold MinSp.r1y at hr ⊢
  have hy' : 0 ≤ y ^ ((4 : ℝ) / 15) := (Real.rpow_pos_of_pos hy _).le
  rcases le_total w 1 with h | h
  · rw [min_eq_left h, Real.mul_rpow hw.le hy.le]
    have hw' : w ≤ w ^ ((4 : ℝ) / 15) := by
      have := Real.rpow_le_rpow_of_exponent_ge hw h (by norm_num : (4 : ℝ) / 15 ≤ 1)
      rwa [Real.rpow_one] at this
    calc w * r ≤ w * (3 / 8 * y ^ ((4 : ℝ) / 15)) := mul_le_mul_of_nonneg_left hr hw.le
      _ = 3 / 8 * (w * y ^ ((4 : ℝ) / 15)) := by ring
      _ ≤ 3 / 8 * (w ^ ((4 : ℝ) / 15) * y ^ ((4 : ℝ) / 15)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw' hy') (by norm_num)
  · rw [min_eq_right h, one_mul]
    calc r ≤ 3 / 8 * y ^ ((4 : ℝ) / 15) := hr
      _ ≤ 3 / 8 * (w * y) ^ ((4 : ℝ) / 15) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow hy.le (by nlinarith) (by norm_num)) (by norm_num)

/-- **[G5 + G6] The Main Theorem at scale `Y = wy`, re-approximated at that scale**:
`|S_{η₂}(α,wy)| ≤ gYL(wy, min(w,1)r)·wy`. G3 gives `a/q` at scale `Y`; if `q ≤ Y^{1/3}/6`,
`MinMainL` (i) + M2 bound it by `gYL(Y,r')Y` with `min(w,1)r ≤ r' ≤ Y^{1/3}/6` (G4), and `GYMono`
moves `r'` down; otherwise `MinMainL` (ii) + `HLeG` + `GYMono` (the argument is `≤ r₁(Y)`). -/
theorem scale_bound (hmm : OL.MinMainL) (hmk : Merkel) (hmo : GYMono) (hhl : HLeG)
    (r : ℕ) (y : ℝ) (hy : 0 < y) (hr1 : (r : ℝ) ≤ MinSp.r1y y) (α : ℝ)
    (hα : α ∉ Smooth.arcs 8 r y) (w : ℝ) (hw : 0 < w) (hY : 3.4e23 ≤ w * y)
    (hlo : 175 ≤ min w 1 * r) :
    ‖Smooth.smSum HW.eta2 (w * y) α‖ ≤ OL.gYL (w * y) (min w 1 * r) * (w * y) := by
  have hY0 : 0 < w * y := mul_pos hw hy
  obtain ⟨u, hu0, -, hu2, hu3⟩ := cube_rep (w * y) hY0
  have hu2' : 2 ≤ u := by
    by_contra h'
    have h := lt_of_not_ge h'
    have h8 : u ^ 3 < 2 ^ 3 := pow_lt_pow_left₀ h hu0.le (by norm_num)
    rw [← hu3] at h8
    norm_num at h8
    linarith
  have hQ : 1 ≤ 3 / 4 * (w * y) ^ ((2 : ℝ) / 3) := by
    rw [hu2]
    nlinarith
  obtain ⟨a, q, hq, hg, hqQ, hd⟩ := dirichlet_at α (w * y) hQ
  have hlow := arg_lower r y w hy hw α hα a q hq hg
  have h2α : 2 * α = a / q + w * y * (2 * α - a / q) / (w * y) := by
    rw [mul_div_cancel_left₀ _ hY0.ne']
    ring
  have hδ : |w * y * (2 * α - a / q) / (w * y)| ≤
      1 / (q * (3 / 4 * (w * y) ^ ((2 : ℝ) / 3))) := by
    rwa [mul_div_cancel_left₀ _ hY0.ne']
  obtain ⟨hsm, hlg⟩ := hmm (w * y) hY α (w * y * (2 * α - a / q)) a q hq hg h2α hqQ hδ
  have hmono := hmo (w * y) hY
  have hr1Y := r1y_le_third (w * y) hY
  by_cases hc : (q : ℝ) ≤ (w * y) ^ ((1 : ℝ) / 3) / 6
  · have hup := arg_upper (w * y) hY0 α a q hq hd hc
    have hk := kraw_le_gYL hmk (w * y) (w * y * (2 * α - a / q)) q hq hY0 (by linarith) hup
    have hmn : OL.gYL (w * y) (max 1 (|w * y * (2 * α - a / q)| / 8) * q) ≤
        OL.gYL (w * y) (min w 1 * r) :=
      hmono ⟨hlo, by linarith⟩ ⟨by linarith, hup⟩ hlow
    calc ‖Smooth.smSum HW.eta2 (w * y) α‖ ≤ OL.krawL (w * y) (w * y * (2 * α - a / q)) q :=
          hsm hc
      _ ≤ _ := hk
      _ ≤ OL.gYL (w * y) (min w 1 * r) * (w * y) := mul_le_mul_of_nonneg_right hmn hY0.le
  · have hbig := hlg (lt_of_not_ge hc)
    have hH := hhl (w * y) hY
    have ht1 : min w 1 * r ≤ MinSp.r1y (w * y) := arg_le_r1y y w r hy hw hr1
    have hmn : OL.gYL (w * y) (MinSp.r1y (w * y)) ≤ OL.gYL (w * y) (min w 1 * r) :=
      hmono ⟨hlo, by linarith⟩ ⟨by linarith, hr1Y⟩ ht1
    calc ‖Smooth.smSum HW.eta2 (w * y) α‖ ≤ hL (w * y) := hbig
      _ ≤ _ := hH
      _ ≤ OL.gYL (w * y) (min w 1 * r) * (w * y) := mul_le_mul_of_nonneg_right hmn hY0.le

/-! ## (6) G7: the trivial bound at every scale, from `Austeria` -/

/-- `η₂(t) = 0` for `t ≥ 1` (its support is `[1/4, 1]`). -/
theorem eta2_eq_zero (t : ℝ) (ht : 1 ≤ t) : HW.eta2 t = 0 := by
  unfold HW.eta2
  rw [if_pos (by linarith)]
  have h2 : Real.log 2 ≤ Real.log (2 * t) := Real.log_le_log two_pos (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [abs_of_nonneg (by linarith), max_eq_right (by linarith), mul_zero]

/-- The terms of `sEta2 Y` vanish for `n ≥ Y`. -/
theorem sEta2_term_zero (Y : ℝ) (hY : 0 < Y) (n : ℕ) (hn : Y ≤ n) :
    Λ n * HW.eta2 ((n : ℝ) / Y) = 0 := by
  rw [eta2_eq_zero _ ((one_le_div hY).mpr hn), mul_zero]

/-- `Σ_n Λ(n)|η₂(n/Y)|` is a finite sum, hence summable. -/
theorem summable_eta2 (Y : ℝ) (hY : 0 < Y) :
    Summable (fun n : ℕ => Λ n * |HW.eta2 ((n : ℝ) / Y)|) := by
  apply summable_of_ne_finset_zero (s := Finset.range (⌊Y⌋₊ + 1))
  intro n hn
  have hYn : Y ≤ n := by
    rw [Finset.mem_range, not_lt] at hn
    have h1 := Nat.lt_floor_add_one Y
    have h' : ((⌊Y⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h'
    linarith
  rw [eta2_eq_zero _ ((one_le_div hY).mpr hYn), abs_zero, mul_zero]

/-- `|S_{η₂}(α,Y)| ≤ Σ_n Λ(n)η₂(n/Y)` (`η₂ ≥ 0`, `|e(·)| = 1`). -/
theorem norm_le_sEta2 (Y : ℝ) (hY : 0 < Y) (α : ℝ) :
    ‖Smooth.smSum HW.eta2 Y α‖ ≤ sEta2 Y := by
  unfold Smooth.smSum sEta2
  have hs' : Summable (fun n : ℕ =>
      ‖((Λ n : ℝ) : ℂ) * ((HW.eta2 ((n : ℝ) / Y) : ℝ) : ℂ) * e ((n : ℝ) * α)‖) :=
    (summable_eta2 Y hY).congr fun n => (Smooth.norm_term HW.eta2 Y α n).symm
  refine le_trans (norm_tsum_le_tsum_norm hs') (le_of_eq (tsum_congr fun n => ?_))
  rw [Smooth.norm_term, abs_of_nonneg (HW.eta2_nonneg _)]

/-- **[G7] `|S_{η₂}(α,Y)| ≤ 1.04488·Y` for EVERY `Y > 0`**: `Austeria` for `Y ≥ 1`; for `Y < 1`
every term vanishes (`n ≥ 1 > Y`, `Λ(0) = 0`). -/
theorem norm_smSum_eta2_le (hau : Austeria) (Y : ℝ) (hY : 0 < Y) (α : ℝ) :
    ‖Smooth.smSum HW.eta2 Y α‖ ≤ 1.04488 * Y := by
  refine le_trans (norm_le_sEta2 Y hY α) ?_
  rcases le_or_gt 1 Y with h1 | h1
  · exact hau Y h1
  · have h0 : sEta2 Y = 0 := by
      unfold sEta2
      refine (tsum_congr fun n => ?_).trans tsum_zero
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp [ArithmeticFunction.map_zero]
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        exact sEta2_term_zero Y hY n (by linarith)
    rw [h0]
    positivity

/-! ## (7) G8: the integration -/

/-- `s ≤ B·wy`, `p ≥ 0` ⟹ `s·p/w ≤ y·(B·p)`: the `dw/w` cancels the scale. -/
theorem div_bound (s B w y p : ℝ) (hw : 0 < w) (hp : 0 ≤ p) (hs : s ≤ B * (w * y)) :
    s * p / w ≤ y * (B * p) := by
  rw [div_le_iff₀ hw]
  calc s * p ≤ B * (w * y) * p := mul_le_mul_of_nonneg_right hs hp
    _ = y * (B * p) * w := by ring

/-- `log y > 17` for `y ≥ 10²⁵`. -/
theorem log_gt (y : ℝ) (hy : 10 ^ 25 ≤ y) : 17 < Real.log y := by
  have h1 : Real.log ((2 : ℝ) ^ 83) ≤ Real.log y :=
    Real.log_le_log (by positivity) (le_trans (by norm_num) hy)
  rw [Real.log_pow] at h1
  have := Real.log_two_gt_d9
  push_cast at h1
  linarith

/-- `log y ≤ 84 log 2 + y/10²⁵ − 1` for `y ≥ 10²⁵` (`log t ≤ t − 1` at `t = y/10²⁵`,
`10²⁵ ≤ 2⁸⁴`). -/
theorem log_le_of_ge (y : ℝ) (hy : 10 ^ 25 ≤ y) :
    Real.log y ≤ 84 * Real.log 2 + y / 10 ^ 25 - 1 := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have h1 := Real.log_le_sub_one_of_pos (show 0 < y / 10 ^ 25 by positivity)
  rw [Real.log_div hy0.ne' (by norm_num)] at h1
  have h2 : Real.log ((10 : ℝ) ^ 25) ≤ 84 * Real.log 2 := by
    calc Real.log ((10 : ℝ) ^ 25) ≤ Real.log ((2 : ℝ) ^ 84) :=
          Real.log_le_log (by norm_num) (by norm_num)
      _ = 84 * Real.log 2 := by
          rw [Real.log_pow]
          norm_num
  generalize Real.log ((10 : ℝ) ^ 25) = L at h1 h2
  generalize y / 10 ^ 25 = t at h1 ⊢
  linarith

/-- **Every scale used is `≥ 3.4·10²³`**: `w ≥ 1/K` and `y ≥ 10²⁵` give `wy ≥ 2y/log y`. -/
theorem scale_ge (y w : ℝ) (hy : 10 ^ 25 ≤ y) (hw : 1 / MinSp.kK y ≤ w) : 3.4e23 ≤ w * y := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hl := log_gt y hy
  have hle := log_le_of_ge y hy
  have hl2 := Real.log_two_lt_d9
  have hl0 : Real.log y ≠ 0 := by positivity
  have hK : 1 / MinSp.kK y * y = 2 * y / Real.log y := by
    unfold MinSp.kK
    field_simp
  have h1 : 3.4e23 ≤ 2 * y / Real.log y := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  calc (3.4e23 : ℝ) ≤ 1 / MinSp.kK y * y := by rw [hK]; exact h1
    _ ≤ w * y := mul_le_mul_of_nonneg_right hw hy0.le

/-- `((A + B + 1.04488C)/L + (1.04488/L)D)·L·Y = Y(1.04488(D + C)) + YA + YB` for `L ≠ 0`. -/
theorem gtl_alg (A B C D L Y : ℝ) (hL : L ≠ 0) :
    ((A + B + 1.04488 * C) / L + 1.04488 / L * D) * L * Y =
      Y * (1.04488 * (D + C)) + Y * A + Y * B := by
  field_simp
  ring

/-- **[G8] The integration**: `∫₀^∞|S_{η₂}(α,wy)|φ(w)dw/w ≤ (g̃(r) + C_{φ,3}(K))|φ|₁y`. The
majorant `gPiece` (G7 on `(0,w₁]`, G5/G6 on `(w₁,∞)`) is integrated piece by piece. -/
theorem gorsh_core (hmm : OL.MinMainL) (hmk : Merkel) (hmo : GYMono) (hhl : HLeG)
    (hau : Austeria) (hint : GTLInt) (φ : ℝ → ℝ) (hφ0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ φ t)
    (hφi : IntegrableOn φ (Set.Ioi 0)) (y : ℝ) (hy : 10 ^ 25 ≤ y) (r : ℕ) (hr : 150000 ≤ r)
    (hr1 : (r : ℝ) ≤ MinSp.r1y y) (α : ℝ) (hα : α ∉ Smooth.arcs 8 r y) :
    ∫ w in Set.Ioi (0 : ℝ), ‖Smooth.smSum HW.eta2 (w * y) α‖ * φ w / w ≤
      (OL.gTL φ y r + MinSp.cPhi3 φ (MinSp.kK y)) * MajSp.l1 φ * y := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hrR : (150000 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  -- the degenerate `|φ|₁ = 0`: `φ = 0` a.e. on `(0,∞)`, both sides vanish
  rcases eq_or_ne (MajSp.l1 φ) 0 with h0 | h0
  · have hab : (fun w => |φ w|) =ᵐ[volume.restrict (Set.Ioi 0)] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun w => abs_nonneg (φ w)) (Integrable.abs hφi)).mp h0
    have hz : ∫ w in Set.Ioi (0 : ℝ), ‖Smooth.smSum HW.eta2 (w * y) α‖ * φ w / w = 0 := by
      rw [integral_congr_ae (g := fun _ => (0 : ℝ)) ?_]
      · simp
      · filter_upwards [hab] with w hw
        have hφw : φ w = 0 := abs_eq_zero.mp hw
        simp [hφw]
    rw [hz, h0]
    simp
  have hl17 := log_gt y hy
  have hK0 : 0 < 1 / MinSp.kK y := by
    unfold MinSp.kK
    have : 0 < Real.log y := by linarith
    positivity
  have hK1 : 1 / MinSp.kK y ≤ 1 := by
    unfold MinSp.kK
    rw [div_le_one (by linarith)]
    linarith
  obtain ⟨w₁, hw₁⟩ : ∃ w₁ : ℝ, w₁ = max (1 / MinSp.kK y) (1000 / (r : ℝ)) := ⟨_, rfl⟩
  have hKw : 1 / MinSp.kK y ≤ w₁ := hw₁ ▸ le_max_left _ _
  have hrw : 1000 / (r : ℝ) ≤ w₁ := hw₁ ▸ le_max_right _ _
  have hw0 : 0 < w₁ := lt_of_lt_of_le hK0 hKw
  have hw1 : w₁ ≤ 1 := by
    rw [hw₁]
    refine max_le hK1 ?_
    rw [div_le_one hr0]
    linarith
  -- integrability of the majorant, piece by piece
  obtain ⟨hI1, hI2⟩ := hint φ hφi y hy r hrR hr1
  rw [← hw₁] at hI1
  have hφw : IntegrableOn φ (Set.Ioc 0 w₁) := hφi.mono_set Set.Ioc_subset_Ioi_self
  have hg1 : IntegrableOn (gPiece φ y r w₁) (Set.Ioc 0 w₁) :=
    IntegrableOn.congr_fun (Integrable.const_mul hφw (y * 1.04488))
      (fun w hw => by simp only [gPiece, if_pos hw.2]; ring) measurableSet_Ioc
  have hg2 : IntegrableOn (gPiece φ y r w₁) (Set.Ioc w₁ 1) :=
    IntegrableOn.congr_fun (Integrable.const_mul hI1 y)
      (fun w hw => by simp only [gPiece, if_neg (not_le.mpr hw.1), if_pos hw.2])
      measurableSet_Ioc
  have hg3 : IntegrableOn (gPiece φ y r w₁) (Set.Ioi 1) :=
    IntegrableOn.congr_fun (Integrable.const_mul hI2 y)
      (fun w hw => by
        have h1 : ¬ w ≤ w₁ := not_le.mpr (lt_of_le_of_lt hw1 hw)
        simp only [gPiece, if_neg h1, if_neg (not_le.mpr (show (1 : ℝ) < w from hw))])
      measurableSet_Ioi
  have hU1 : Set.Ioc w₁ 1 ∪ Set.Ioi 1 = Set.Ioi w₁ := Set.Ioc_union_Ioi_eq_Ioi hw1
  have hU0 : Set.Ioc 0 w₁ ∪ Set.Ioi w₁ = Set.Ioi 0 := Set.Ioc_union_Ioi_eq_Ioi hw0.le
  have hg23 : IntegrableOn (gPiece φ y r w₁) (Set.Ioi w₁) := by
    rw [← hU1]
    exact hg2.union hg3
  have hg : IntegrableOn (gPiece φ y r w₁) (Set.Ioi 0) := by
    rw [← hU0]
    exact hg1.union hg23
  -- the pointwise bound (G7 on `(0,w₁]`, G5/G6 beyond)
  have hpt : ∀ w ∈ Set.Ioi (0 : ℝ),
      ‖Smooth.smSum HW.eta2 (w * y) α‖ * φ w / w ≤ gPiece φ y r w₁ w := by
    intro w hw
    have hw0' : 0 < w := hw
    have hφw0 : 0 ≤ φ w := hφ0 w hw0'.le
    rcases le_or_gt w w₁ with h1 | h1
    · rw [show gPiece φ y r w₁ w = y * (1.04488 * φ w) by simp only [gPiece, if_pos h1]]
      exact div_bound _ _ _ _ _ hw0' hφw0
        (norm_smSum_eta2_le hau (w * y) (mul_pos hw0' hy0) α)
    · have hY : 3.4e23 ≤ w * y := scale_ge y w hy (le_trans hKw h1.le)
      rcases le_or_gt w 1 with h2 | h2
      · rw [show gPiece φ y r w₁ w = y * (OL.gYL (w * y) (w * r) * φ w) by
          simp only [gPiece, if_neg (not_le.mpr h1), if_pos h2]]
        have hlo : 175 ≤ min w 1 * (r : ℝ) := by
          rw [min_eq_left h2]
          have h3 : 1000 / (r : ℝ) * r ≤ w * r :=
            mul_le_mul_of_nonneg_right (le_trans hrw h1.le) hr0.le
          rw [div_mul_cancel₀ _ hr0.ne'] at h3
          linarith
        have hb := scale_bound hmm hmk hmo hhl r y hy0 hr1 α hα w hw0' hY hlo
        rw [min_eq_left h2] at hb
        exact div_bound _ _ _ _ _ hw0' hφw0 hb
      · rw [show gPiece φ y r w₁ w = y * (OL.gYL (w * y) r * φ w) by
          simp only [gPiece, if_neg (not_le.mpr h1), if_neg (not_le.mpr h2)]]
        have hlo : 175 ≤ min w 1 * (r : ℝ) := by
          rw [min_eq_right h2.le, one_mul]
          linarith
        have hb := scale_bound hmm hmk hmo hhl r y hy0 hr1 α hα w hw0' hY hlo
        rw [min_eq_right h2.le, one_mul] at hb
        exact div_bound _ _ _ _ _ hw0' hφw0 hb
  have hmono : ∫ w in Set.Ioi (0 : ℝ), ‖Smooth.smSum HW.eta2 (w * y) α‖ * φ w / w ≤
      ∫ w in Set.Ioi (0 : ℝ), gPiece φ y r w₁ w :=
    integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Ioi fun w hw =>
        div_nonneg (mul_nonneg (norm_nonneg _) (hφ0 w (le_of_lt hw))) (le_of_lt hw))
      hg (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
  -- the integral of the majorant
  have e1 : ∫ w in Set.Ioc 0 w₁, gPiece φ y r w₁ w =
      y * (1.04488 * ∫ w in Set.Ioc 0 w₁, φ w) := by
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun w => y * (1.04488 * φ w))
      (fun w hw => by simp only [gPiece, if_pos hw.2]), integral_const_mul, integral_const_mul]
  have e2 : ∫ w in Set.Ioc w₁ 1, gPiece φ y r w₁ w =
      y * ∫ w in Set.Ioc w₁ 1, OL.gYL (w * y) (w * r) * φ w := by
    rw [setIntegral_congr_fun measurableSet_Ioc
      (g := fun w => y * (OL.gYL (w * y) (w * r) * φ w))
      (fun w hw => by simp only [gPiece, if_neg (not_le.mpr hw.1), if_pos hw.2]),
      integral_const_mul]
  have e3 : ∫ w in Set.Ioi 1, gPiece φ y r w₁ w =
      y * ∫ w in Set.Ioi 1, OL.gYL (w * y) r * φ w := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (g := fun w => y * (OL.gYL (w * y) r * φ w))
      (fun w hw => by
        have h1 : ¬ w ≤ w₁ := not_le.mpr (lt_of_le_of_lt hw1 hw)
        simp only [gPiece, if_neg h1, if_neg (not_le.mpr (show (1 : ℝ) < w from hw))]),
      integral_const_mul]
  have hsplit : ∫ w in Set.Ioi (0 : ℝ), gPiece φ y r w₁ w =
      y * (1.04488 * ∫ w in Set.Ioc 0 w₁, φ w) +
        ((y * ∫ w in Set.Ioc w₁ 1, OL.gYL (w * y) (w * r) * φ w) +
          y * ∫ w in Set.Ioi 1, OL.gYL (w * y) r * φ w) := by
    rw [← hU0, setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hg1 hg23, ← hU1,
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hg2 hg3, e1, e2, e3]
  -- the `φ`-mass of `(0,w₁]` is `J₀ + J₁`
  have hJ : ∫ w in Set.Ioc 0 w₁, φ w =
      (∫ w in (0 : ℝ)..(1 / MinSp.kK y), |φ w|) + ∫ w in (1 / MinSp.kK y)..w₁, |φ w| := by
    rw [intervalIntegral.integral_of_le hK0.le, intervalIntegral.integral_of_le hKw,
      ← Set.Ioc_union_Ioc_eq_Ioc hK0.le hKw,
      setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
        (hφi.mono_set Set.Ioc_subset_Ioi_self)
        (hφi.mono_set (fun w hw => lt_trans hK0 hw.1))]
    congr 1
    · exact setIntegral_congr_fun measurableSet_Ioc
        (fun w hw => (abs_of_nonneg (hφ0 w hw.1.le)).symm)
    · exact setIntegral_congr_fun measurableSet_Ioc
        (fun w hw => (abs_of_nonneg (hφ0 w (lt_trans hK0 hw.1).le)).symm)
  have hI1 : (∫ w in w₁..1, OL.gYL (w * y) (w * r) * φ w) =
      ∫ w in Set.Ioc w₁ 1, OL.gYL (w * y) (w * r) * φ w := intervalIntegral.integral_of_le hw1
  rw [hJ] at hsplit
  unfold OL.gTL MinSp.cPhi3
  rw [← hw₁, gtl_alg _ _ _ _ _ _ h0, hI1]
  linarith

/-! ## (8) THE COMPOSITION -/

/-- **`OL.GorshL` from its links** — application only: G1 (`MellinLe`) then G8 (`gorsh_core`,
which carries G2-G7). OPEN inputs: `OL.MinMainL` (the published Main Theorem, `L` repaired),
`Merkel` (or `RS62Thm15`, `merkel_of_rs62`), `GYMono`, `HLeG`, `Austeria`, `MellinLe η* φ`,
`GTLInt`. -/
theorem gorshL_of_links (ηs φ : ℝ → ℝ) (hmm : OL.MinMainL) (hmk : Merkel) (hmo : GYMono)
    (hhl : HLeG) (hau : Austeria) (hme : MellinLe ηs φ) (hint : GTLInt) :
    OL.GorshL ηs φ := by
  intro hη hφ0 hφi x hx r hr hr1 α hα
  exact le_trans (hme hη hφ0 hφi x (MinSp.x_pos x hx) α)
    (gorsh_core hmm hmk hmo hhl hau hint φ hφ0 hφi (x / 49) (MinSp.y_ge x hx) r hr hr1 α hα)

/-! ## (9) `lem:merkel` from Rosser-Schoenfeld Theorem 15 -/

/-- `4q ≤ 15φ(q)`, i.e. `q/φ(q) ≤ 3.75`, for `q < 50` (the maximum is at `q = 30`). -/
theorem small_totient : ∀ n : ℕ, n < 50 → 4 * n ≤ 15 * Nat.totient n := by decide

/-- `e^γ > 3/2` (`e^γ ≥ 1 + γ`, `γ > 1/2`). -/
theorem exp_gamma_gt : (3 / 2 : ℝ) < Real.exp Real.eulerMascheroniConstant := by
  have h1 := Real.add_one_le_exp Real.eulerMascheroniConstant
  have h2 := Real.one_half_lt_eulerMascheroniConstant
  linarith

/-- `ϝ(r) > 3.75` for `r ≥ 3`: with `u = log log r > 0`, `ϝ(r) > 1.5u + 2.50637/u` and
`1.5u² − 3.75u + 2.50637 = 1.5(u − 1.25)² + 0.16262 > 0`. -/
theorem bigF_gt (r : ℝ) (hr : 3 ≤ r) : 3.75 < MinSp.bigF r := by
  have hr0 : 0 < r := by linarith
  have hlr : 1 < Real.log r := by
    rw [Real.lt_log_iff_exp_lt hr0]
    linarith [Real.exp_one_lt_d9]
  have hu0 : 0 < Real.log (Real.log r) := Real.log_pos hlr
  have hg := exp_gamma_gt
  unfold MinSp.bigF
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = Real.log (Real.log r) := ⟨_, rfl⟩
  rw [← hu] at hu0 ⊢
  have hv : 2.50637 / u * u = 2.50637 := div_mul_cancel₀ _ hu0.ne'
  have h1 : 3 / 2 * u < Real.exp Real.eulerMascheroniConstant * u :=
    mul_lt_mul_of_pos_right hg hu0
  have key : 3.75 < 3 / 2 * u + 2.50637 / u := by
    nlinarith [sq_nonneg (u - 1.25)]
  linarith

/-- `ϝ` is non-decreasing on `[50, ∞)`: `u₁ = log log a ≥ 1.3` (`log 50 ≥ 5.6 log 2 ≥ 3.88 ≥
e^{1.3}`), and `ϝ(b) − ϝ(a) = (u₂ − u₁)(e^γ − 2.50637/(u₁u₂)) ≥ 0` since `1.5·1.3² > 2.50637`. -/
theorem bigF_mono (a b : ℝ) (ha : 50 ≤ a) (hab : a ≤ b) : MinSp.bigF a ≤ MinSp.bigF b := by
  have ha0 : 0 < a := by linarith
  have hla : 3.88 ≤ Real.log a := by
    have h1 : Real.log ((2 : ℝ) ^ 56) ≤ Real.log ((50 : ℝ) ^ 10) :=
      Real.log_le_log (by positivity) (by norm_num)
    rw [Real.log_pow, Real.log_pow] at h1
    have h2 : Real.log 50 ≤ Real.log a := Real.log_le_log (by norm_num) ha
    have := Real.log_two_gt_d9
    push_cast at h1
    linarith
  have he : Real.exp 1.3 ≤ 3.88 := by
    have h1 : Real.exp 1.3 = Real.exp 1 * Real.exp 0.3 := by
      rw [← Real.exp_add]
      norm_num
    have h2 := Real.abs_exp_sub_one_sub_id_le (show |(0.3 : ℝ)| ≤ 1 by norm_num)
    rw [abs_le] at h2
    have h3 : Real.exp 0.3 ≤ 1.39 := by nlinarith [h2.2]
    have h4 := mul_le_mul Real.exp_one_lt_d9.le h3 (Real.exp_pos _).le (by norm_num)
    rw [h1]
    linarith
  have hu1 : 1.3 ≤ Real.log (Real.log a) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith
  have hu12 : Real.log (Real.log a) ≤ Real.log (Real.log b) :=
    Real.log_le_log (by linarith) (Real.log_le_log ha0 hab)
  have hg := exp_gamma_gt
  unfold MinSp.bigF
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = Real.log (Real.log a) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = Real.log (Real.log b) := ⟨_, rfl⟩
  rw [← hu, ← hv]
  rw [← hu] at hu1 hu12
  rw [← hv] at hu12
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have huv : 0 < u * v := mul_pos hu0 hv0
  have key : 2.50637 / u - 2.50637 / v = 2.50637 * (v - u) / (u * v) := by
    field_simp
  have k1 : 0 ≤ 1.5 * (u * v) - 2.50637 := by nlinarith
  have k2 : 2.50637 * (v - u) / (u * v) ≤ 1.5 * (v - u) := by
    rw [div_le_iff₀ huv]
    nlinarith [mul_nonneg (sub_nonneg.2 hu12) k1]
  have k3 := mul_le_mul_of_nonneg_right hg.le (sub_nonneg.2 hu12)
  rw [mul_sub] at k3
  linarith

/-- **`lem:merkel` from `RS62Thm15`**: for `q < 50`, `q/φ(q) ≤ 3.75 < ϝ(r)` (`small_totient`,
`bigF_gt`); for `q ≥ 50`, `q/φ(q) < ϝ(q) ≤ ϝ(r)` (RS62 Thm 15, `bigF_mono`). -/
theorem merkel_of_rs62 (h15 : RS62Thm15) : Merkel := by
  intro q hq r hr3 hqr
  have hφ0 : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  rcases lt_or_ge q 50 with hq50 | hq50
  · have h' : (4 : ℝ) * q ≤ 15 * Nat.totient q := by exact_mod_cast small_totient q hq50
    have hle : (q : ℝ) / Nat.totient q ≤ 3.75 := by
      rw [div_le_iff₀ hφ0]
      linarith
    linarith [bigF_gt r hr3]
  · have hq50' : (50 : ℝ) ≤ q := by exact_mod_cast hq50
    exact lt_of_lt_of_le (h15 q (by omega)) (bigF_mono q r hq50' hqr)

/-- **`RS62Thm15` holds for `3 ≤ n < 50`** (`n/φ(n) ≤ 3.75 < ϝ(n)`): the citation is consumed
only from `n = 50` on. A real instance of the cited statement. -/
theorem rs62_small (n : ℕ) (h3 : 3 ≤ n) (h50 : n < 50) :
    (n : ℝ) / Nat.totient n < MinSp.bigF n := by
  have hφ0 : (0 : ℝ) < Nat.totient n := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have h' : (4 : ℝ) * n ≤ 15 * Nat.totient n := by exact_mod_cast small_totient n h50
  have hle : (n : ℝ) / Nat.totient n ≤ 3.75 := by
    rw [div_le_iff₀ hφ0]
    linarith
  have h3' : (3 : ℝ) ≤ n := by exact_mod_cast h3
  linarith [bigF_gt n h3']

/-! ## (10) Pricing `Austeria` (G7) from Chebyshev bounds -/

/-- `cor:austeria`'s shape at a constant `c` from a threshold `Y₀`. -/
def AusteriaAt (c Y₀ : ℝ) : Prop := ∀ Y : ℝ, Y₀ ≤ Y → sEta2 Y ≤ c * Y

/-- `Austeria` IS `AusteriaAt 1.04488 1`, by `Iff.rfl`. -/
theorem austeria_iff : Austeria ↔ AusteriaAt 1.04488 1 := Iff.rfl

/-- `|η₂|_∞ ≤ 4 log 2`. -/
theorem eta2_le (t : ℝ) : HW.eta2 t ≤ 4 * Real.log 2 := by
  unfold HW.eta2
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  split_ifs
  · have : max (Real.log 2 - |Real.log (2 * t)|) 0 ≤ Real.log 2 :=
      max_le (by linarith [abs_nonneg (Real.log (2 * t))]) hl2.le
    linarith
  · linarith

/-- **`Σ_n Λ(n)η₂(n/Y) ≤ 4 log 2 · ψ(Y)`** for `Y > 0`: `|η₂|_∞ = 4 log 2` and only `n < Y`
contribute. -/
theorem sEta2_le_psi (Y : ℝ) (hY : 0 < Y) : sEta2 Y ≤ 4 * Real.log 2 * Chebyshev.psi Y := by
  have hsupp : ∀ n ∉ Finset.Icc 0 ⌊Y⌋₊, Λ n * HW.eta2 ((n : ℝ) / Y) = 0 := by
    intro n hn
    have hlt : ⌊Y⌋₊ < n := by
      rw [Finset.mem_Icc] at hn
      omega
    exact sEta2_term_zero Y hY n ((Nat.floor_lt hY.le).mp hlt).le
  unfold sEta2
  rw [tsum_eq_sum hsupp, Chebyshev.psi_eq_sum_Icc, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  calc Λ n * HW.eta2 ((n : ℝ) / Y) ≤ Λ n * (4 * Real.log 2) :=
        mul_le_mul_of_nonneg_left (eta2_le _) ArithmeticFunction.vonMangoldt_nonneg
    _ = 4 * Real.log 2 * Λ n := by ring

/-- **`AusteriaAt 3.0776 (3·10⁹)`** from Principia's Chebyshev `ψ(t) ≤ 1.11t`
(`4 log 2 · 1.11 = 3.07757`): the shape of `Austeria` met by a real, proved bound, `2.945`
times weaker than `cor:austeria`'s `1.04488`. -/
theorem austeriaAt_cheb : AusteriaAt 3.0776 (3 * 10 ^ 9) := by
  intro Y hY
  have hY0 : 0 < Y := lt_of_lt_of_le (by norm_num) hY
  have h1 := sEta2_le_psi Y hY0
  have h2 := Principia.Common.Chebyshev.psi_le_cheb hY
  have hl2 := Real.log_two_lt_d9
  have hl2' : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * Real.log 2)
  have h4 := mul_le_mul_of_nonneg_right hl2.le hY0.le
  linarith

/-- **`AusteriaAt 15 0`**, uniform in `Y > 0`, from Mathlib's `ψ(x) ≤ (log 4 + 4)x`
(`4 log 2 (log 4 + 4) ≤ 14.94`). Used for the Tonelli step of G1. -/
theorem sEta2_le_lin (Y : ℝ) (hY : 0 < Y) : sEta2 Y ≤ 15 * Y := by
  have h1 := sEta2_le_psi Y hY
  have h2 := Chebyshev.psi_le_const_mul_self hY.le
  have hl2 := Real.log_two_lt_d9
  have hl2' : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hl4] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * Real.log 2)
  have hA : Real.log 2 * Y ≤ 0.6931471808 * Y := mul_le_mul_of_nonneg_right hl2.le hY.le
  have hB : Real.log 2 * (Real.log 2 * Y) ≤ 0.6931471808 * (0.6931471808 * Y) :=
    mul_le_mul hl2.le hA (by positivity) (by norm_num)
  linarith

/-! ## (11) G1 PROVED: `eq:chemdames` as an inequality, for every `φ ≥ 0` in `L¹(0,∞)` -/

/-- `η₂` is measurable. -/
theorem eta2_measurable : Measurable HW.eta2 := by
  unfold HW.eta2
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id) (by fun_prop)
    measurable_const

/-- The `(n, v)` term of `S_{η*}(α,x)` after unfolding the Mellin convolution:
`Λ(n)·η₂(n/(vy))φ(v)/v·e(nα)`. -/
noncomputable def gTerm (φ : ℝ → ℝ) (y α : ℝ) (n : ℕ) (v : ℝ) : ℂ :=
  ((Λ n * (HW.eta2 ((n : ℝ) / (v * y)) * φ v / v) : ℝ) : ℂ) * e ((n : ℝ) * α)

/-- `‖gTerm‖ₑ = Λ(n)η₂(n/(vy))·(φ(v)/v)` for `v > 0`. -/
theorem enorm_gTerm (φ : ℝ → ℝ) (hφ0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ φ t) (y α : ℝ) (n : ℕ) (v : ℝ)
    (hv : 0 < v) : ‖gTerm φ y α n v‖ₑ =
      ENNReal.ofReal (Λ n * HW.eta2 ((n : ℝ) / (v * y)) * (φ v / v)) := by
  have hnn : 0 ≤ Λ n * (HW.eta2 ((n : ℝ) / (v * y)) * φ v / v) :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (div_nonneg (mul_nonneg (HW.eta2_nonneg _) (hφ0 v hv.le)) hv.le)
  rw [← ofReal_norm]
  congr 1
  unfold gTerm
  rw [norm_mul, e_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  ring

/-- **[G1] `MellinLe` holds for every `φ ≥ 0` in `L¹(0,∞)`**: each `η*(n/x)` is the integral
`∫ η₂(n/(vy))φ(v)dv/v` (`HW.mconv`, `49(n/x)/v = n/(vy)`), the sum over `n` and the integral
commute (`integral_tsum`; absolutely, since `Σ_n Λ(n)η₂(n/Y) ≤ 15Y` by `sEta2_le_lin`, so the
double sum-integral is `≤ 15y∫φ`), and `‖∫‖ ≤ ∫‖·‖`. -/
theorem mellinLe_all (ηs φ : ℝ → ℝ) : MellinLe ηs φ := by
  intro hη hφ0 hφi x hx α
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = x / 49 := ⟨_, rfl⟩
  rw [← hy]
  have hy0 : 0 < y := by
    rw [hy]
    positivity
  have hηm := eta2_measurable
  have hφm : AEMeasurable φ (volume.restrict (Set.Ioi 0)) := hφi.aemeasurable
  have hGm : ∀ n : ℕ, AEStronglyMeasurable (gTerm φ y α n) (volume.restrict (Set.Ioi 0)) := by
    intro n
    have h : AEMeasurable (fun v : ℝ => ((Λ n * (HW.eta2 ((n : ℝ) / (v * y)) * φ v / v) : ℝ) : ℂ)
        * e ((n : ℝ) * α)) (volume.restrict (Set.Ioi 0)) := by
      fun_prop
    exact h.aestronglyMeasurable
  -- each term is an integral
  have hterm : ∀ n : ℕ, ∫ v in Set.Ioi (0 : ℝ), gTerm φ y α n v =
      ((Λ n : ℝ) : ℂ) * ((ηs ((n : ℝ) / x) : ℝ) : ℂ) * e ((n : ℝ) * α) := by
    intro n
    have hm : ηs ((n : ℝ) / x) =
        ∫ v in Set.Ioi (0 : ℝ), HW.eta2 ((n : ℝ) / (v * y)) * φ v / v := by
      rw [hη, HW.mconv]
      congr 1
      funext v
      rw [show 49 * ((n : ℝ) / x) / v = (n : ℝ) / (v * y) by rw [hy]; ring]
    unfold gTerm
    rw [integral_mul_const, integral_complex_ofReal, integral_const_mul, hm]
    push_cast
    ring
  -- absolute convergence of the double sum-integral
  have hbd : ∀ᵐ v ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∑' n : ℕ, ‖gTerm φ y α n v‖ₑ ≤ ENNReal.ofReal (15 * y * φ v) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun v hv => ?_
    have hv0 : 0 < v := hv
    have hvy : 0 < v * y := mul_pos hv0 hy0
    have hφv : 0 ≤ φ v / v := div_nonneg (hφ0 v hv0.le) hv0.le
    have hnn : ∀ n : ℕ, 0 ≤ Λ n * HW.eta2 ((n : ℝ) / (v * y)) * (φ v / v) := fun n =>
      mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (HW.eta2_nonneg _)) hφv
    have hs : Summable (fun n : ℕ => Λ n * HW.eta2 ((n : ℝ) / (v * y)) * (φ v / v)) :=
      ((summable_eta2 (v * y) hvy).congr fun n => by
        rw [abs_of_nonneg (HW.eta2_nonneg _)]).mul_right _
    rw [tsum_congr fun n => enorm_gTerm φ hφ0 y α n v hv0, ← ENNReal.ofReal_tsum_of_nonneg hnn hs]
    apply ENNReal.ofReal_le_ofReal
    rw [tsum_mul_right]
    have h1 := sEta2_le_lin (v * y) hvy
    calc (∑' n : ℕ, Λ n * HW.eta2 ((n : ℝ) / (v * y))) * (φ v / v)
        ≤ 15 * (v * y) * (φ v / v) := mul_le_mul_of_nonneg_right h1 hφv
      _ = 15 * y * φ v := by
          field_simp
  have hfin : ∑' n : ℕ, ∫⁻ v in Set.Ioi (0 : ℝ), ‖gTerm φ y α n v‖ₑ ≠ ⊤ := by
    rw [← lintegral_tsum (fun n => (hGm n).enorm)]
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono_ae hbd) ?_)
    calc ∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (15 * y * φ v)
        = ∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (15 * y) * ENNReal.ofReal (φ v) :=
          lintegral_congr fun v => ENNReal.ofReal_mul (by positivity)
      _ = ENNReal.ofReal (15 * y) * ∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (φ v) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Integrable.lintegral_lt_top hφi)
  -- assemble
  have hsum : Smooth.smSum ηs x α = ∑' n : ℕ, ∫ v in Set.Ioi (0 : ℝ), gTerm φ y α n v := by
    unfold Smooth.smSum
    exact tsum_congr fun n => (hterm n).symm
  rw [hsum, ← integral_tsum hGm hfin]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
  have hv0 : 0 < v := hv
  have hsplit : ∑' n : ℕ, gTerm φ y α n v =
      Smooth.smSum HW.eta2 (v * y) α * ((φ v / v : ℝ) : ℂ) := by
    unfold Smooth.smSum
    rw [← tsum_mul_right]
    refine tsum_congr fun n => ?_
    unfold gTerm
    push_cast
    ring
  rw [hsplit, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (hφ0 v hv0.le) hv0.le), mul_div_assoc]

/-! ## (12) `GTLInt` PROVED: `gYL` is bounded on every argument `gTL` integrates -/

/-- `e^γ log log R + 2.50637`, the cap on `ϝ(t)` for `1000 ≤ t ≤ R`. -/
noncomputable def fCap (R : ℝ) : ℝ :=
  Real.exp Real.eulerMascheroniConstant * Real.log (Real.log R) + 2.50637

/-- `0.27125·log(8R)/2 + 0.41415`, the cap on `R_{Y,2t}` for `t ≤ min(R, Y^{1/3}/6)`. -/
noncomputable def aCap (R : ℝ) : ℝ := 0.27125 * (Real.log (8 * R) / 2) + 0.41415

/-- The cap on `L_t` (`lLc`) for `1000 ≤ t ≤ R`. -/
noncomputable def lCap (R : ℝ) : ℝ :=
  fCap R * (7 / 4 * Real.log 2 + 13 / 4 * Real.log R + 80 / 9) + 1.7984 * Real.log 2 +
    13.6516 * Real.log R + 22.7538

/-- The cap on `gYL(Y,t)` for `Y ≥ 1`, `1000 ≤ t ≤ min(R, Y^{1/3}/6)`. -/
noncomputable def gCap (R : ℝ) : ℝ :=
  ((aCap R * Real.log (2 * R) + 0.5) * Real.sqrt (fCap R) + 2.5) / Real.sqrt 2000 +
    lCap R / 1000 + 3.2

/-- **`gYL(Y,t) ≤ gCap(R)`** for `Y ≥ 1`, `1000 ≤ t ≤ R`, `t ≤ Y^{1/3}/6`: every piece of
`g_Y(t)` is capped (`R_{Y,2t} ≤ aCap` since the inner logarithm is `≥ 1`, `ϝ(t) ≤ fCap` since
`log log t ≥ 1`, `√(2t) ≥ √2000`, `Y^{−1/6} ≤ 1`). -/
theorem gYL_le_cap (Y t R : ℝ) (hY : 1 ≤ Y) (ht : 1000 ≤ t) (htY : t ≤ Y ^ ((1 : ℝ) / 3) / 6)
    (htR : t ≤ R) : OL.gYL Y t ≤ gCap R := by
  have hY0 : 0 < Y := by linarith
  have ht0 : 0 < t := by linarith
  have hR0 : 0 < R := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlt : Real.exp 1 ≤ Real.log t := by
    have h1 : Real.log ((2 : ℝ) ^ 9) ≤ Real.log t :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_pow] at h1
    have := Real.log_two_gt_d9
    have := Real.exp_one_lt_d9
    push_cast at h1
    linarith
  have hlt0 : 0 < Real.log t := lt_of_lt_of_le (Real.exp_pos 1) hlt
  have hll : 1 ≤ Real.log (Real.log t) := (Real.le_log_iff_exp_le hlt0).mpr hlt
  have hlR : Real.log t ≤ Real.log R := Real.log_le_log ht0 htR
  have hllR : Real.log (Real.log t) ≤ Real.log (Real.log R) := Real.log_le_log hlt0 hlR
  have hg0 : 0 < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  -- `ϝ`
  have hF0 : 0 ≤ MinSp.bigF t := by
    unfold MinSp.bigF
    have := div_nonneg (by norm_num : (0 : ℝ) ≤ 2.50637) (by linarith : 0 ≤ Real.log (Real.log t))
    have := mul_nonneg hg0.le (by linarith : 0 ≤ Real.log (Real.log t))
    linarith
  have hF1 : MinSp.bigF t ≤ fCap R := by
    unfold MinSp.bigF fCap
    have h1 : 2.50637 / Real.log (Real.log t) ≤ 2.50637 := div_le_self (by norm_num) hll
    have h2 := mul_le_mul_of_nonneg_left hllR hg0.le
    linarith
  have hFc0 : 0 ≤ fCap R := le_trans hF0 hF1
  -- `R_{Y,2t}`
  have hRlo := rR_ge Y (2 * t) hY0 (by linarith) (by linarith)
  have hRhi : MinSp.rR Y (2 * t) ≤ aCap R := by
    unfold MinSp.rR aCap
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = Y ^ ((1 : ℝ) / 3) := ⟨_, rfl⟩
    rw [← hc] at htY ⊢
    have hq : Real.exp 1 ≤ 9 * c / (2.004 * (2 * t)) := by
      rw [le_div_iff₀ (by positivity)]
      have := Real.exp_one_lt_d9
      nlinarith
    have hℓ : 1 ≤ Real.log (9 * c / (2.004 * (2 * t))) :=
      (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) hq)).mpr hq
    have h8 : 0 ≤ Real.log (4 * (2 * t)) := Real.log_nonneg (by linarith)
    have h8R : Real.log (4 * (2 * t)) ≤ Real.log (8 * R) :=
      Real.log_le_log (by positivity) (by linarith)
    have hu0 : 0 ≤ Real.log (4 * (2 * t)) / (2 * Real.log (9 * c / (2.004 * (2 * t)))) :=
      div_nonneg h8 (by linarith)
    have hu : Real.log (4 * (2 * t)) / (2 * Real.log (9 * c / (2.004 * (2 * t)))) ≤
        Real.log (8 * R) / 2 := by
      calc Real.log (4 * (2 * t)) / (2 * Real.log (9 * c / (2.004 * (2 * t))))
          ≤ Real.log (4 * (2 * t)) / 2 := div_le_div_of_nonneg_left h8 (by norm_num) (by linarith)
        _ ≤ Real.log (8 * R) / 2 := by linarith
    have hlog1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 +
      Real.log (4 * (2 * t)) / (2 * Real.log (9 * c / (2.004 * (2 * t)))) by linarith)
    linarith
  -- the first term
  have hl2t : 0 ≤ Real.log (2 * t) := Real.log_nonneg (by linarith)
  have hl2R : Real.log (2 * t) ≤ Real.log (2 * R) := Real.log_le_log (by linarith) (by linarith)
  have ha0 : 0 ≤ aCap R := le_trans (by linarith) hRhi
  have hA : MinSp.rR Y (2 * t) * Real.log (2 * t) + 0.5 ≤ aCap R * Real.log (2 * R) + 0.5 := by
    have := mul_le_mul hRhi hl2R hl2t ha0
    linarith
  have hA0 : 0 ≤ MinSp.rR Y (2 * t) * Real.log (2 * t) + 0.5 := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ MinSp.rR Y (2 * t)) hl2t
    linarith
  have hsF := Real.sqrt_le_sqrt hF1
  have hN : (MinSp.rR Y (2 * t) * Real.log (2 * t) + 0.5) * Real.sqrt (MinSp.bigF t) + 2.5 ≤
      (aCap R * Real.log (2 * R) + 0.5) * Real.sqrt (fCap R) + 2.5 := by
    have := mul_le_mul hA hsF (Real.sqrt_nonneg _) (by linarith)
    linarith
  have hN0 : 0 ≤ (aCap R * Real.log (2 * R) + 0.5) * Real.sqrt (fCap R) + 2.5 := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ aCap R * Real.log (2 * R) + 0.5)
      (Real.sqrt_nonneg (fCap R))
    linarith
  have hs2000 : 0 < Real.sqrt 2000 := Real.sqrt_pos.mpr (by norm_num)
  have hs2t : Real.sqrt 2000 ≤ Real.sqrt (2 * t) := Real.sqrt_le_sqrt (by linarith)
  have hT1 : ((MinSp.rR Y (2 * t) * Real.log (2 * t) + 0.5) * Real.sqrt (MinSp.bigF t) + 2.5) /
      Real.sqrt (2 * t) ≤
      ((aCap R * Real.log (2 * R) + 0.5) * Real.sqrt (fCap R) + 2.5) / Real.sqrt 2000 :=
    calc _ ≤ ((aCap R * Real.log (2 * R) + 0.5) * Real.sqrt (fCap R) + 2.5) /
          Real.sqrt (2 * t) := div_le_div_of_nonneg_right hN (Real.sqrt_nonneg _)
      _ ≤ _ := div_le_div_of_nonneg_left hN0 hs2000 hs2t
  -- the `L` term
  have hL1 : OL.lLc t ≤ lCap R := by
    unfold OL.lLc lCap
    rw [OL.log_two_rpow_mul _ _ t ht0, OL.log_two_rpow_mul _ _ t ht0]
    have h1 := mul_le_mul hF1
      (show 7 / 4 * Real.log 2 + 13 / 4 * Real.log t + 80 / 9 ≤
        7 / 4 * Real.log 2 + 13 / 4 * Real.log R + 80 / 9 by linarith)
      (by linarith) hFc0
    linarith
  have hLc0 : 0 ≤ lCap R := by
    unfold lCap
    have := mul_nonneg hFc0
      (show (0 : ℝ) ≤ 7 / 4 * Real.log 2 + 13 / 4 * Real.log R + 80 / 9 by linarith)
    linarith
  have hT2 : OL.lLc t / t ≤ lCap R / 1000 :=
    calc OL.lLc t / t ≤ lCap R / t := div_le_div_of_nonneg_right hL1 ht0.le
      _ ≤ lCap R / 1000 := div_le_div_of_nonneg_left hLc0 (by norm_num) ht
  have hT3 : 3.2 * Y ^ (-(1 : ℝ) / 6) ≤ 3.2 := by
    have := Real.rpow_le_one_of_one_le_of_nonpos hY (by norm_num : -(1 : ℝ) / 6 ≤ 0)
    linarith
  unfold OL.gYL gCap
  linarith

/-- `|gYL(Y,t)| ≤ gCap(R)` on the arguments `gTL` integrates (`gYL > 0` there, `OL.gYL_pos`). -/
theorem norm_gYL_le (Y t R : ℝ) (hY : 3.4e23 ≤ Y) (ht : 1000 ≤ t)
    (htY : t ≤ Y ^ ((1 : ℝ) / 3) / 6) (htR : t ≤ R) : ‖OL.gYL Y t‖ ≤ gCap R := by
  rw [Real.norm_eq_abs,
    abs_of_pos (OL.gYL_pos Y t (lt_of_lt_of_le (by norm_num) hY) (by linarith) htY)]
  exact gYL_le_cap Y t R (le_trans (by norm_num) hY) ht htY htR

/-- **[GTLInt] PROVED**: on `(w₁,1]` the argument is `(wy, wr)` with `wr ∈ [1000, r]`, on
`(1,∞)` it is `(wy, r)`; in both cases `wy ≥ 3.4·10²³` and the argument is `≤ r₁(wy) ≤
(wy)^{1/3}/6` (`arg_le_r1y`, `r1y_le_third`), so `gYL ≤ gCap(r)`; a bounded measurable function
times `φ ∈ L¹` is integrable. -/
theorem gtlInt : GTLInt := by
  intro φ hφi y hy r hr hr1
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hr0 : 0 < r := by linarith
  have hl17 := log_gt y hy
  have hK0 : 0 < 1 / MinSp.kK y := by
    unfold MinSp.kK
    have : 0 < Real.log y := by linarith
    positivity
  have hw0 : 0 < max (1 / MinSp.kK y) (1000 / r) := lt_of_lt_of_le hK0 (le_max_left _ _)
  have hm1 : Measurable fun w : ℝ => OL.gYL (w * y) (w * r) := by
    unfold OL.gYL MinSp.rR OL.lLc MinSp.bigF
    fun_prop
  have hm2 : Measurable fun w : ℝ => OL.gYL (w * y) r := by
    unfold OL.gYL MinSp.rR OL.lLc MinSp.bigF
    fun_prop
  refine ⟨?_, ?_⟩
  · refine Integrable.bdd_mul (c := gCap r)
      (hφi.mono_set fun w hw => lt_of_lt_of_le hw0 hw.1.le) hm1.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioc fun w hw => ?_)
    have hw0' : 0 < w := lt_trans hw0 hw.1
    have hY : 3.4e23 ≤ w * y := scale_ge y w hy (le_trans (le_max_left _ _) hw.1.le)
    have h1000 : 1000 ≤ w * r := by
      have h := mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) hw.1.le) hr0.le
      rw [div_mul_cancel₀ _ hr0.ne'] at h
      exact h
    have harg := arg_le_r1y y w r hy0 hw0' hr1
    rw [min_eq_left hw.2] at harg
    exact norm_gYL_le (w * y) (w * r) r hY h1000
      (le_trans harg (r1y_le_third (w * y) hY)) (by nlinarith [hw.2])
  · refine Integrable.bdd_mul (c := gCap r)
      (hφi.mono_set fun w (hw : 1 < w) => lt_trans one_pos hw) hm2.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun w hw => ?_)
    have hw1 : 1 < w := hw
    have hY : 3.4e23 ≤ w * y := by nlinarith
    have harg := arg_le_r1y y w r hy0 (lt_trans one_pos hw1) hr1
    rw [min_eq_right hw1.le, one_mul] at harg
    exact norm_gYL_le (w * y) r r hY (by linarith)
      (le_trans harg (r1y_le_third (w * y) hY)) le_rfl

/-! ## (13) THE HEADLINE: `OL.GorshL` with G1 and `GTLInt` discharged -/

/-- **`OL.GorshL η* φ` from the PUBLISHED and NUMERIC inputs only**: `gorshL_of_links` with G1
(`mellinLe_all`), `GTLInt` (`gtlInt`) and `lem:merkel` (`merkel_of_rs62`) discharged. OPEN:
`OL.MinMainL` (minarcs Main Theorem, `L` repaired), `RS62Thm15` (Rosser-Schoenfeld 1962 Thm 15,
needed only from `n = 50`), `GYMono` and `HLeG` (numeric, checked in floating point), `Austeria`
(`cor:austeria`, Platt's zeros). Application only. -/
theorem gorshL_of_open (ηs φ : ℝ → ℝ) (hmm : OL.MinMainL) (h15 : RS62Thm15) (hmo : GYMono)
    (hhl : HLeG) (hau : Austeria) : OL.GorshL ηs φ :=
  gorshL_of_links ηs φ hmm (merkel_of_rs62 h15) hmo hhl hau (mellinLe_all ηs φ) gtlInt

/-! ## (14) `HLeG` at one real point, `Y = 10³⁰` -/

/-- `(10³⁰)^a = 10^b` when `30a = b`. -/
theorem ten30_rpow (a : ℝ) (b : ℕ) (hab : 30 * a = b) : ((10 : ℝ) ^ 30) ^ a = 10 ^ b := by
  rw [← Real.rpow_natCast (10 : ℝ) 30, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10),
    ← Real.rpow_natCast]
  congr 1

/-- `L_t ≥ 0` for `t ≥ 1000`. -/
theorem lLc_nonneg (t : ℝ) (ht : 1000 ≤ t) : 0 ≤ OL.lLc t := by
  have ht0 : 0 < t := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hF := (bigF_gt t (by linarith)).le
  unfold OL.lLc
  rw [OL.log_two_rpow_mul _ _ t ht0, OL.log_two_rpow_mul _ _ t ht0]
  have := mul_nonneg (by linarith : (0 : ℝ) ≤ MinSp.bigF t)
    (by positivity : (0 : ℝ) ≤ 7 / 4 * Real.log 2 + 13 / 4 * Real.log t + 80 / 9)
  linarith

/-- **`HLeG` at `Y = 10³⁰`, certified**: `h′(10³⁰) ≤ 1.978·10²⁷ ≤ 2.069·10²⁷ ≤
gYL(10³⁰, r₁(10³⁰))·10³⁰`, `r₁(10³⁰) = 3.75·10⁷`, from `R ≥ 0.41415`, `ϝ ≥ 3.75`, `2²⁶ ≤ 7.5·10⁷`
and `10³ < 2¹⁰` only (certified ratio `1.046`; the float ratio there is `1.974`). A real instance
of the numeric link, which also pins its scaling (`hL` absolute, `gYL·Y`). -/
theorem hLeG_at_1e30 :
    hL ((10 : ℝ) ^ 30) ≤ OL.gYL ((10 : ℝ) ^ 30) (MinSp.r1y ((10 : ℝ) ^ 30)) * (10 : ℝ) ^ 30 := by
  have hY0 : (0 : ℝ) < 10 ^ 30 := by positivity
  have h415 := ten30_rpow ((4 : ℝ) / 15) 8 (by norm_num)
  have h13 := ten30_rpow ((1 : ℝ) / 3) 10 (by norm_num)
  have h56 := ten30_rpow ((5 : ℝ) / 6) 25 (by norm_num)
  have h23 := ten30_rpow ((2 : ℝ) / 3) 20 (by norm_num)
  have hr1 : MinSp.r1y ((10 : ℝ) ^ 30) = 3.75e7 := by
    unfold MinSp.r1y
    rw [h415]
    norm_num
  -- `log 10³⁰ ≤ 69.3148`, `(log 10³⁰)^{3/2} ≤ 577.1`
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hl10 : 3 * Real.log 10 ≤ 10 * Real.log 2 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 10 ^ 3) (by norm_num : (10 : ℝ) ^ 3 ≤ 2 ^ 10)
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    exact h
  have hLY : Real.log ((10 : ℝ) ^ 30) = 30 * Real.log 10 := by
    rw [Real.log_pow]
    push_cast
    ring
  have hL0 : 0 < Real.log ((10 : ℝ) ^ 30) := Real.log_pos (by norm_num)
  have hLhi : Real.log ((10 : ℝ) ^ 30) ≤ 69.3148 := by
    rw [hLY]
    linarith
  have h32 : Real.log ((10 : ℝ) ^ 30) ^ ((3 : ℝ) / 2) ≤ 577.1 := by
    have e : Real.log ((10 : ℝ) ^ 30) ^ ((3 : ℝ) / 2) =
        Real.log ((10 : ℝ) ^ 30) * Real.sqrt (Real.log ((10 : ℝ) ^ 30)) := by
      rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hL0,
        Real.rpow_one]
    have hs : Real.sqrt (Real.log ((10 : ℝ) ^ 30)) ≤ 8.3256 :=
      calc Real.sqrt (Real.log ((10 : ℝ) ^ 30)) ≤ Real.sqrt (8.3256 ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith)
        _ = 8.3256 := Real.sqrt_sq (by norm_num)
    rw [e]
    have := mul_le_mul hLhi hs (Real.sqrt_nonneg _) (by norm_num)
    linarith
  have hhL : hL ((10 : ℝ) ^ 30) ≤ 1.978e27 := by
    unfold hL
    rw [h56, h23]
    linarith
  -- `gYL(10³⁰, 3.75·10⁷) ≥ 17.919/8660.26`
  rw [hr1]
  have hR := rR_ge ((10 : ℝ) ^ 30) (2 * 3.75e7) hY0 (by norm_num) (by rw [h13]; norm_num)
  have hF := bigF_gt 3.75e7 (by norm_num)
  have hlog : 18.02 ≤ Real.log (2 * 3.75e7) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2 ^ 26)
      (by norm_num : (2 : ℝ) ^ 26 ≤ 2 * 3.75e7)
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hsF : 1.9364 ≤ Real.sqrt (MinSp.bigF 3.75e7) :=
    calc (1.9364 : ℝ) = Real.sqrt (1.9364 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt (MinSp.bigF 3.75e7) := Real.sqrt_le_sqrt (by nlinarith)
  have hs2t : Real.sqrt (2 * 3.75e7) ≤ 8660.26 :=
    calc Real.sqrt (2 * 3.75e7) ≤ Real.sqrt (8660.26 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = 8660.26 := Real.sqrt_sq (by norm_num)
  have hs2t0 : 0 < Real.sqrt (2 * 3.75e7) := Real.sqrt_pos.mpr (by norm_num)
  have hN : 17.919 ≤ (MinSp.rR ((10 : ℝ) ^ 30) (2 * 3.75e7) * Real.log (2 * 3.75e7) + 0.5) *
      Real.sqrt (MinSp.bigF 3.75e7) + 2.5 := by
    have h1 : 0.41415 * 18.02 ≤ MinSp.rR ((10 : ℝ) ^ 30) (2 * 3.75e7) * Real.log (2 * 3.75e7) :=
      mul_le_mul hR hlog (by norm_num) (by linarith)
    have h2 := mul_le_mul
      (show 0.41415 * 18.02 + 0.5 ≤
        MinSp.rR ((10 : ℝ) ^ 30) (2 * 3.75e7) * Real.log (2 * 3.75e7) + 0.5 by linarith)
      hsF (by norm_num) (by linarith)
    linarith
  have hT1 : 17.919 / 8660.26 ≤ ((MinSp.rR ((10 : ℝ) ^ 30) (2 * 3.75e7) *
      Real.log (2 * 3.75e7) + 0.5) * Real.sqrt (MinSp.bigF 3.75e7) + 2.5) /
      Real.sqrt (2 * 3.75e7) :=
    calc (17.919 : ℝ) / 8660.26 ≤ ((MinSp.rR ((10 : ℝ) ^ 30) (2 * 3.75e7) *
          Real.log (2 * 3.75e7) + 0.5) * Real.sqrt (MinSp.bigF 3.75e7) + 2.5) / 8660.26 :=
          div_le_div_of_nonneg_right hN (by norm_num)
      _ ≤ _ := div_le_div_of_nonneg_left (by linarith) hs2t0 hs2t
  have hT2 : 0 ≤ OL.lLc 3.75e7 / 3.75e7 := div_nonneg (lLc_nonneg _ (by norm_num)) (by norm_num)
  have hT3 : 0 ≤ 3.2 * ((10 : ℝ) ^ 30) ^ (-(1 : ℝ) / 6) := by positivity
  have hg : 17.919 / 8660.26 ≤ OL.gYL ((10 : ℝ) ^ 30) 3.75e7 := by
    unfold OL.gYL
    linarith
  calc hL ((10 : ℝ) ^ 30) ≤ 1.978e27 := hhL
    _ ≤ 17.919 / 8660.26 * (10 : ℝ) ^ 30 := by norm_num
    _ ≤ OL.gYL ((10 : ℝ) ^ 30) 3.75e7 * (10 : ℝ) ^ 30 := mul_le_mul_of_nonneg_right hg hY0.le

end Principia.Common.TernaryGoldbach.GS
