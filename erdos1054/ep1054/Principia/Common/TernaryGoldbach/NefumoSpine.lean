/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.PerArcSpine
import Principia.Common.TernaryGoldbach.DrujalPlancherel

set_option autoImplicit false

/-!
# THE SPINE OF `prop:nefumo`: `RW.NefumoW` as a composition of named links

**`nefumoW_of_links` proves `RW.NefumoW ηp ηs ηo` for EVERY triple of weights from eight links:
three generic (`ArcsReal`, `Massacre`, `TailLink`, all OPEN here and all TRUE) and five about the
weights (`OInt`, `Madge` — DISCHARGED for Helfgott's `η∘` — and `HostoW`, `T3W`, `JokoW`, OPEN
here; `HostoW` follows from the generic `Hosto`, `hostoW_of_hosto`). It proves no part of
Helfgott's major-arc estimate beyond what is listed as PROVED below.** `nefumoW_helf` is the
instance at `(η₊, η*, η∘)`. `NefumoLinks.lean` discharges more of it (see there).

The source is `prop:nefumo`'s LIVE proof, `ternvin.tex` §3, 966–1676 (the commented-out blocks
at 1144–1160 and 1179–1195 are not part of it). `RegW`'s docstring records which hypotheses that
proof uses; here every step is a link.

## The spine

```
 kernS = S₊²S* e(−Nα) on the arc about a/q,  α = a/q + δ/x;  S = M + R + D,
   M = μ(q)/φ(q)·x·η̂(−δ)               (eq:massac, 1557–1563; `mT`)
   R = (x/φ)∑_χ χ(a)τ(χ̄)err_{χ*}(δ,x)   (eq:glenkin, eq:brahms, 979–986; `rT`)
   D = S − M − R                          (the non-coprime part, eq:beatit/eq:mouche 795–899)
 S₊²S* − M₊²M* = [S₊²R* + S₊R₊M* + R₊M₊M*] + [S₊²D* + S₊D₊M* + D₊M₊M*]   (telescoping)
      │                      │                              │
  mainI (eq:henki)       rI (eq:huppert, 1482–1610)     ∫_𝔐 kernS − mainI − rI
      │  sum_e_pt (eq:selb): ∑_a e(−Na/q) = c_q(N)          │
      │  arcSum_main_eq: mainI = x²∑_q T₃(q)∫_{−w_q}^{w_q} η̂₊²η̂* e    [JokoW] ≤ line 3
      │  band_le (eq:pommes)      η̂₊ → η̂∘, cost 2.82643|η∘|₂²(2+ε₀)ε₀|η*|₁
      │  [TailLink] (eq:rusko, eq:boussole; [Madge], eq:gat1o/e)  complete ∑_q to 𝔖₃(N)
      │  [Hosto] (eq:hosto)        ∫_ℝ η̂∘²η̂* e(−δN/x) = C_{η∘,η*}(N/x)
      ▼                                   rI_le: E*A + E₊√2.82643·√A|η*|₂ + E₊·t3Sum
 main_close: |mainI − C₀Cx²| ≤ line 1       [T3W] t3Sum ≤ 2.82643|η₊|₂|η*|₂  ⇒ line 2
                          close_nefumo ⇒ RW.NefumoW
```

## The links

| link | statement | source | status |
|---|---|---|---|
| `ArcsReal` | `∫_𝔐 f = ∑_q (∫_{−w_q}^{w_q} ∑_a f(a/q+δ/x))/x` | 1272–1315 | OPEN, generic |
| `Massacre` | `∑_{q∈Qs} μ²/φ² ≤ 2.82643` | `eq:massacre` 5581 | OPEN, numeric |
| `TailLink` | completing `∑_q` costs `(4.31004ℓ² + 0.0012L²/8⁵)|η*|₁/r` | 1099–1142 | OPEN |
| `HostoW` | `∫ η̂∘²η̂* e(−δy) = C_{η∘,η*}(y)` (generic form `Hosto`) | 1166–1178 | OPEN |
| `OInt` | `η∘ ∈ L¹(0,∞)` | implicit | `oInt_helf` |
| `Madge` | `|η̂∘(−δ)| ≤ |η∘'''|₁/(2π|δ|)³` | `eq:madge` 646–654 | `madge_helf` |
| `T3W` | `t3Sum ≤ 2.82643|η₊|₂|η*|₂` | 1585–1588 | OPEN, weight |
| `JokoW` | `|∫_𝔐 kernS − mainI − rI| ≤ (2Z₊LS* + 4√(Z₊Z*)LS₊)x` | 929–933, 1501–1524 | OPEN |

PROVED: `sum_e_pt` (the Ramanujan sum, via `MajorArcMainTerm.ramSum_eq_cRam`), `mainA_eq` and
`arcSum_main_eq` (the principal characters produce `x³T₃(q)`, `T₃ = μ³c_q(N)/φ³ =
SingularSeries.sing3Local`), `rT_norm_le` (`|R| ≤ xE`), `rT_sq_sum_le` (`∑_a|R|² ≤ x²E²`, from
`PA.orth` and `PA.gauss`), `rT_sum_le`, `rA_le`, `rI_le` (the three `err` terms), `band_q`,
`band_le`, `main_close`, `close_nefumo`, `nefumoW_of_links`, `t3_le_c3`.

**Each link is TRUE or measured, and none is vacuous.** `ArcsReal` is PROVED in `NefumoLinks`
(`arcsReal`, from `ArcIntSpine`). `Massacre`: the partial sum is `2.8264114` (`scratchpad/nefumo/
c3.py`; the full series is `2.826419…2.826421`). `TailLink` is PROVED in `NefumoLinks` from the
arithmetic `GatTail` (`eq:gat1o`/`eq:gat1e`, 5713–5726), whose ratio to its bound is `≤ 0.394`
numerically. `Hosto`: `η̂∘²η̂*` is the transform of `η∘ ∗ η∘ ∗ η*`, which is continuous when
`η∘ ∈ L²`, so Fourier inversion applies at every point; `HostoW` is PROVED at Helfgott's pair in
`NefumoLinks` (`hostoW_helf`). `T3W`, `JokoW`: below.

## Findings (each checked against `ternvin.tex`)

1. **[T3] The `R₊M₊M*` term is priced with the wrong `ℓ²` norm (1585–1588).** The source bounds
   the error part of `S_{η₁}` "in the same way, using solely the `ℓ₂` norm in (thaddeus)", i.e.
   with `√B₊ = 1.6812|η₊|₂`. But `eq:thaddeus` is the norm per `(q, δ)`, WITHOUT the sum over `a`
   — right for `S₊R₊M*`, where `M*` is constant in `a` and orthogonality puts `∑_a|R₊|² ≤ x²E₊²`
   against `∑_a|S₊|²`. In `R₊M₊M*` BOTH `M`'s are constant in `a`, the whole `a`-sum falls on
   `|R₊|`, and `∑_a|R₊| ≤ √φ(q)·xE₊` is sharp. The honest weight is `t3Sum ≤ c₃|η₊|₂|η*|₂`,
   `c₃ = ∑_{q ∈ Qs} μ²(q)/φ(q)^{3/2} = 3.8523845 > 2.82643` (`t3_le_c3`, PROVED). `T3W` is FALSE
   for `η₊ = η* = e^{−t}` (`t3Sum = 1.9261 > 2.82643·|η|₂² = 1.4132`) and TRUE for Helfgott's
   `(η∘, η*)` (`0.1001 ≤ 0.3332`, `t3helf.py`), so it is a WEIGHT link. Replacing `2.82643` by
   `c₃` costs `(c₃ − 2.82643)E₊|η₊|₂|η*|₂ ≤ 1.97·10⁻⁷` (units `x²/49`) at `E₊ = 2.3921·10⁻⁸`
   (`MC0` margin `1.07·10⁻⁶`) and `3.52·10⁻⁷` at `MR`'s `4.2813·10⁻⁸` (margin `1.01·10⁻⁶`).
2. **[Joko] is a first-order bound (929–933, 1504–1524).** Every telescoping of
   `S₊²S* − M₊²M*` puts an `M` (not an `S`) beside `D` in two of the three `D`-terms, or else
   produces second-order `D²S` terms, which `eq:joko` omits. The honest route to line 3: `|D| ≤
   ∑_{p|q} (p/(p−1)) log p ∑_k |η(p^{k+1}/x)|` (the exact coefficient of `eq:mouche`, 795–824;
   `max_q ∑_{p|q} (p/(p−1)) log p = 14.84 ≤ 2 log r`, `jokow.py`), `∫_𝔐|S|² ≤ xZ_{η²,2}`
   (Parseval on the circle), and `∫_𝔐|M|² = x·L_{r,δ₀}(η) ≤ xZ_{η²,2}(x)` — the last a fact about
   the weights (`L ≤ 13.6|η|₂²` against `Z ≈ |η|₂² log x`). So `JokoW` is a WEIGHT link;
   `NefumoJoko.jokoW_of_links` proves it from exactly these links.
3. **`η∘ ∈ L¹` is not in `RegW`** (1060, 1616): without it `MajSp.mainFT η∘` is the junk `0`, and
   the band and completion steps have nothing to act on. `OInt`, a weight link; `oInt_helf`.
4. **`eq:madge` needs boundary terms to vanish**: `η∘, η∘', η∘''` at `0` and at the points where
   `η∘` is not `C³`; "thrice differentiable outside finitely many points" does not give it. `Madge`,
   a weight link; `madge_helf` from `DP.decay_circ`.
5. **`0 ≤ ε₀` is redundant** in `NefumoBody`: `0 ≤ |η₊ − η∘|₂ < ε₀|η∘|₂` forces `ε₀ > 0`
   (`band_arith` does not take it).

## Reuse

`PA.orth`, `PA.gauss` (`PerArcSpine`), `DP.mardiQ_of`, `DP.mainFT_eq`, `DP.fourier_zext_add`,
`DP.decay_circ` (`DrujalPlancherel`), `FourierBessel.cs_real`, `FourierBessel.continuous_fourier`,
`SingularSeries.norm_sing3Arith_le_maj`, `MajorArcMainTerm.ramSum_eq_cRam`.
-/

namespace Principia.Common.TernaryGoldbach.NF

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach
open scoped ArithmeticFunction FourierTransform

/-! ## The objects -/

/-- The moduli of `𝔐_{8,150000}`: odd `q ≤ r`, even `q ≤ 2r`. -/
def Qs : Finset ℕ := DS.oddQ ∪ DS.evenQ

/-- The residues of modulus `q`: `0 ≤ a < q`, `(a,q) = 1` (`DS.arcSq`'s index set). -/
def cop (q : ℕ) : Finset ℕ := (Finset.range q).filter (fun a => Nat.Coprime a q)

/-- The `δ`-half-width of the arc of modulus `q`: `gcd(q,2)·δ₀r/2q`. -/
noncomputable def wq (q : ℕ) : ℝ := (Nat.gcd q 2 : ℝ) * 600000 / q

/-- The point `α = a/q + δ/x` of the arc about `a/q`. -/
noncomputable def pt (x : ℝ) (q a : ℕ) (δ : ℝ) : ℝ := (a : ℝ) / q + δ / x

/-- `∑_q (∫_{−w_q}^{w_q} ∑_{(a,q)=1} f(q,a,δ) dδ)/x`. -/
noncomputable def arcSum (x : ℝ) (f : ℕ → ℕ → ℝ → ℂ) : ℂ :=
  ∑ q ∈ Qs, (∫ δ in (-wq q)..(wq q), ∑ a ∈ cop q, f q a δ) / x

/-- `M = μ(q)/φ(q)·x·η̂(−δ)` (`eq:massac`). -/
noncomputable def mT (η : ℝ → ℝ) (x : ℝ) (q : ℕ) (δ : ℝ) : ℂ :=
  (((moebius q : ℝ) / (q.totient : ℝ) * x : ℝ) : ℂ) * MajSp.mainFT η δ

/-- `R = (x/φ(q))∑_χ χ(a)τ(χ̄)err_{η,χ*}(δ,x)`. -/
noncomputable def rT (η : ℝ → ℝ) (x : ℝ) (q a : ℕ) (δ : ℝ) : ℂ :=
  if h : q = 0 then 0 else
    haveI : NeZero q := ⟨h⟩
    ∑ χ : DirichletCharacter ℂ q, (x : ℂ) / (q.totient : ℂ) * gaussSum χ⁻¹ ZMod.stdAddChar *
      MajSp.err η χ.primitiveCharacter δ x * χ (a : ZMod q)

/-- `η̂₁(−δ)²η̂*(−δ)e(−δy)`. -/
noncomputable def gO (η ηs : ℝ → ℝ) (y δ : ℝ) : ℂ :=
  MajSp.mainFT η δ ^ 2 * MajSp.mainFT ηs δ * e (-(δ * y))

theorem mem_Qs {q : ℕ} (hq : q ∈ Qs) : 1 ≤ q ∧ q ≤ 150000 * Nat.gcd q 2 := by
  unfold Qs DS.oddQ DS.evenQ at hq
  rcases Finset.mem_union.mp hq with h | h
  · obtain ⟨h1, h2⟩ := Finset.mem_filter.mp h
    obtain ⟨ha, hb⟩ := Finset.mem_Icc.mp h1
    have hg : Nat.gcd q 2 = 1 := Nat.coprime_two_right.mpr h2
    rw [hg]
    exact ⟨ha, by omega⟩
  · obtain ⟨h1, h2⟩ := Finset.mem_filter.mp h
    obtain ⟨ha, hb⟩ := Finset.mem_Icc.mp h1
    have hg : Nat.gcd q 2 = 2 := Nat.gcd_eq_right (even_iff_two_dvd.mp h2)
    rw [hg]
    exact ⟨ha, by omega⟩

theorem wq_nonneg (q : ℕ) : 0 ≤ wq q := by
  unfold wq
  positivity

theorem card_cop (q : ℕ) : (cop q).card = q.totient := by
  rw [Nat.totient_eq_card_coprime]
  unfold cop
  congr 1
  exact Finset.filter_congr fun a _ => Nat.coprime_comm

theorem norm_mainFT_le (η : ℝ → ℝ) (δ : ℝ) : ‖MajSp.mainFT η δ‖ ≤ MajSp.l1 η := by
  unfold MajSp.mainFT MajSp.l1
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only
  rw [norm_mul, e_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem continuous_mainFT_of (η : ℝ → ℝ) (h : Integrable η (volume.restrict (Set.Ioi 0))) :
    Continuous (MajSp.mainFT η) := by
  have h1 := FourierBessel.continuous_fourier _ (DP.integrable_zext η h)
  have h2 : MajSp.mainFT η = fun β => 𝓕 (DP.zext η) (-β) := funext (DP.mainFT_eq η)
  rw [h2]
  exact h1.comp continuous_neg

theorem mainFT_sub (η ηo : ℝ → ℝ) (h1 : Integrable η (volume.restrict (Set.Ioi 0)))
    (h2 : Integrable ηo (volume.restrict (Set.Ioi 0))) (δ : ℝ) :
    MajSp.mainFT (fun t => η t - ηo t) δ = MajSp.mainFT η δ - MajSp.mainFT ηo δ := by
  rw [DP.mainFT_eq, DP.mainFT_eq, DP.mainFT_eq, DP.fourier_zext_add η ηo h1 h2 (-δ)]
  ring

/-- **The Ramanujan sum** (`eq:selb`): `∑_{(a,q)=1} e(−N(a/q + δ/x)) = c_q(N)·e(−δN/x)`. -/
theorem sum_e_pt (N : ℕ) (x δ : ℝ) (q : ℕ) (hq : 0 < q) :
    ∑ a ∈ cop q, e (-(N : ℝ) * pt x q a δ) =
      (MajorArcMainTerm.cRam q N : ℂ) * e (-(δ * ((N : ℝ) / x))) := by
  have h1 : ∀ a ∈ cop q, e (-(N : ℝ) * pt x q a δ) =
      starRingEnd ℂ (e ((N : ℝ) * a / q)) * e (-(δ * ((N : ℝ) / x))) := by
    intro a _
    rw [e_conj, e_add]
    unfold pt
    congr 1
    ring
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, ← map_sum]
  have h2 : ∑ a ∈ cop q, e ((N : ℝ) * a / q) = MajorArcMainTerm.ramSum q N := by
    unfold MajorArcMainTerm.ramSum cop
    refine Finset.sum_congr ?_ fun _ _ => rfl
    exact Finset.filter_congr fun a _ => Iff.rfl
  rw [h2, MajorArcMainTerm.ramSum_eq_cRam q N hq, map_intCast]

/-- **The principal-character main term, summed over `a`** (`eq:lookatme`–`eq:henki`):
`∑_{(a,q)=1} M₊²M* e(−Nα) = x³·T₃(q)·η̂₊²η̂* e(−δN/x)`, `T₃ = μ³c_q(N)/φ³`. -/
theorem mainA_eq (ηp ηs : ℝ → ℝ) (N : ℕ) (x δ : ℝ) (q : ℕ) (hq : 0 < q) :
    ∑ a ∈ cop q, mT ηp x q δ ^ 2 * mT ηs x q δ * e (-(N : ℝ) * pt x q a δ) =
      ((x ^ 3 * SingularSeries.sing3Local q N : ℝ) : ℂ) * gO ηp ηs ((N : ℝ) / x) δ := by
  rw [← Finset.mul_sum, sum_e_pt N x δ q hq]
  unfold mT gO SingularSeries.sing3Local
  push_cast
  ring

/-- **The main term** of `eq:henki`: `x²∑_q T₃(q)∫_{−w_q}^{w_q} η̂₊²η̂* e(−δN/x) dδ`. -/
theorem arcSum_main_eq (ηp ηs : ℝ → ℝ) (N : ℕ) (x : ℝ) (hx : x ≠ 0) :
    arcSum x (fun q a δ => mT ηp x q δ ^ 2 * mT ηs x q δ * e (-(N : ℝ) * pt x q a δ)) =
      ((x ^ 2 : ℝ) : ℂ) * ∑ q ∈ Qs, ((SingularSeries.sing3Local q N : ℝ) : ℂ) *
        ∫ δ in (-wq q)..(wq q), gO ηp ηs ((N : ℝ) / x) δ := by
  unfold arcSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq0 : 0 < q := (mem_Qs hq).1
  have h1 : (fun δ => ∑ a ∈ cop q, mT ηp x q δ ^ 2 * mT ηs x q δ * e (-(N : ℝ) * pt x q a δ)) =
      fun δ => ((x ^ 3 * SingularSeries.sing3Local q N : ℝ) : ℂ) *
        gO ηp ηs ((N : ℝ) / x) δ := funext fun δ => mainA_eq ηp ηs N x δ q hq0
  rw [h1, intervalIntegral.integral_const_mul]
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  push_cast
  field_simp


/-! ## The error part `R` (`eq:glenkin`, `eq:brahms`): pointwise and `ℓ²` over `a` -/

theorem rT_eq (η : ℝ → ℝ) (x : ℝ) (q a : ℕ) [NeZero q] (δ : ℝ) :
    rT η x q a δ = ∑ χ : DirichletCharacter ℂ q, (x : ℂ) / (q.totient : ℂ) *
      gaussSum χ⁻¹ ZMod.stdAddChar * MajSp.err η χ.primitiveCharacter δ x * χ (a : ZMod q) := by
  unfold rT
  rw [dif_neg (NeZero.ne q)]

theorem norm_gauss_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ≤ Real.sqrt (χ.conductor : ℝ) := by
  rw [← Real.sqrt_sq (norm_nonneg (gaussSum χ⁻¹ ZMod.stdAddChar))]
  exact Real.sqrt_le_sqrt ((PA.gauss q).2.1 χ)

/-- `|τ(χ̄)|·|err_{χ*}| ≤ E` on an arc (`EBound`, conductor-weighted). -/
theorem gauss_err_le (η : ℝ → ℝ) (x E : ℝ) (hE : MajSp.EBound η x E) (q : ℕ) [NeZero q]
    (hq1 : 1 ≤ q) (hq2 : q ≤ 150000 * Nat.gcd q 2) (δ : ℝ)
    (hδ : |δ| ≤ (Nat.gcd q 2 : ℝ) * 600000 / q) (χ : DirichletCharacter ℂ q) :
    ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ * ‖MajSp.err η χ.primitiveCharacter δ x‖ ≤ E :=
  le_trans (mul_le_mul_of_nonneg_right (norm_gauss_le χ) (norm_nonneg _)) (hE q hq1 hq2 χ δ hδ)

/-- **`|R| ≤ xE` pointwise.** -/
theorem rT_norm_le (η : ℝ → ℝ) (x E : ℝ) (hx : 0 ≤ x) (hE : MajSp.EBound η x E) (q : ℕ)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 150000 * Nat.gcd q 2) (a : ℕ) (δ : ℝ)
    (hδ : |δ| ≤ (Nat.gcd q 2 : ℝ) * 600000 / q) : ‖rT η x q a δ‖ ≤ x * E := by
  haveI : NeZero q := ⟨by omega⟩
  rw [rT_eq]
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hcard : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hc : 0 ≤ x / q.totient := div_nonneg hx hφ.le
  have hterm : ∀ χ : DirichletCharacter ℂ q, ‖(x : ℂ) / (q.totient : ℂ) *
      gaussSum χ⁻¹ ZMod.stdAddChar * MajSp.err η χ.primitiveCharacter δ x * χ (a : ZMod q)‖ ≤
        x / q.totient * E := by
    intro χ
    have hA := gauss_err_le η x E hE q hq1 hq2 δ hδ χ
    have hB : 0 ≤ ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ * ‖MajSp.err η χ.primitiveCharacter δ x‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have h3 : ‖χ (a : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    rw [norm_mul, norm_mul, norm_mul, norm_div, Complex.norm_real, Complex.norm_natCast,
      Real.norm_of_nonneg hx]
    calc x / q.totient * ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ *
          ‖MajSp.err η χ.primitiveCharacter δ x‖ * ‖χ (a : ZMod q)‖
        = x / q.totient * (‖gaussSum χ⁻¹ ZMod.stdAddChar‖ *
            ‖MajSp.err η χ.primitiveCharacter δ x‖) * ‖χ (a : ZMod q)‖ := by ring
      _ ≤ x / q.totient * (‖gaussSum χ⁻¹ ZMod.stdAddChar‖ *
            ‖MajSp.err η χ.primitiveCharacter δ x‖) * 1 :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg hc hB)
      _ ≤ x / q.totient * E := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_left hA hc
  calc ‖∑ χ : DirichletCharacter ℂ q, (x : ℂ) / (q.totient : ℂ) *
        gaussSum χ⁻¹ ZMod.stdAddChar * MajSp.err η χ.primitiveCharacter δ x * χ (a : ZMod q)‖
      ≤ ∑ χ : DirichletCharacter ℂ q, ‖(x : ℂ) / (q.totient : ℂ) *
        gaussSum χ⁻¹ ZMod.stdAddChar * MajSp.err η χ.primitiveCharacter δ x *
          χ (a : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _χ : DirichletCharacter ℂ q, x / q.totient * E :=
        Finset.sum_le_sum fun χ _ => hterm χ
    _ = x * E := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
        field_simp

/-- **`∑_a |R|² ≤ x²E²`**: orthogonality (`PA.orth`), `|τ(χ̄)||err_{χ*}| ≤ E`. -/
theorem rT_sq_sum_le (η : ℝ → ℝ) (x E : ℝ) (hx : 0 ≤ x) (hE : MajSp.EBound η x E) (q : ℕ)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 150000 * Nat.gcd q 2) (δ : ℝ)
    (hδ : |δ| ≤ (Nat.gcd q 2 : ℝ) * 600000 / q) :
    ∑ a ∈ cop q, ‖rT η x q a δ‖ ^ 2 ≤ (x * E) ^ 2 := by
  haveI : NeZero q := ⟨by omega⟩
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hcard : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hr : ∀ a ∈ cop q, ‖rT η x q a δ‖ ^ 2 = ‖∑ χ : DirichletCharacter ℂ q,
      (x : ℂ) / (q.totient : ℂ) * gaussSum χ⁻¹ ZMod.stdAddChar *
        MajSp.err η χ.primitiveCharacter δ x * χ (a : ZMod q)‖ ^ 2 := fun a _ => by rw [rT_eq]
  rw [Finset.sum_congr rfl hr]
  have ho := PA.orth q (fun χ => (x : ℂ) / (q.totient : ℂ) * gaussSum χ⁻¹ ZMod.stdAddChar *
    MajSp.err η χ.primitiveCharacter δ x)
  change ∑ a ∈ cop q, _ = _ at ho
  rw [ho]
  have hterm : ∀ χ : DirichletCharacter ℂ q, ‖(x : ℂ) / (q.totient : ℂ) *
      gaussSum χ⁻¹ ZMod.stdAddChar * MajSp.err η χ.primitiveCharacter δ x‖ ^ 2 ≤
        (x / q.totient * E) ^ 2 := by
    intro χ
    have hA := gauss_err_le η x E hE q hq1 hq2 δ hδ χ
    have hB : 0 ≤ ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ * ‖MajSp.err η χ.primitiveCharacter δ x‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hc : 0 ≤ x / q.totient := div_nonneg hx hφ.le
    rw [norm_mul, norm_mul, norm_div, Complex.norm_real, Complex.norm_natCast,
      Real.norm_of_nonneg hx, mul_assoc]
    exact pow_le_pow_left₀ (mul_nonneg hc hB) (mul_le_mul_of_nonneg_left hA hc) 2
  calc (q.totient : ℝ) * ∑ χ : DirichletCharacter ℂ q, ‖(x : ℂ) / (q.totient : ℂ) *
        gaussSum χ⁻¹ ZMod.stdAddChar * MajSp.err η χ.primitiveCharacter δ x‖ ^ 2
      ≤ (q.totient : ℝ) * ∑ _χ : DirichletCharacter ℂ q, (x / q.totient * E) ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun χ _ => hterm χ) hφ.le
    _ = (x * E) ^ 2 := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
        field_simp

/-- **`∑_a |R| ≤ √φ(q)·xE`** (Cauchy–Schwarz over the `φ(q)` residues). -/
theorem rT_sum_le (η : ℝ → ℝ) (x E : ℝ) (hx : 0 ≤ x) (hE : MajSp.EBound η x E) (q : ℕ)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 150000 * Nat.gcd q 2) (δ : ℝ)
    (hδ : |δ| ≤ (Nat.gcd q 2 : ℝ) * 600000 / q) :
    ∑ a ∈ cop q, ‖rT η x q a δ‖ ≤ Real.sqrt (q.totient : ℝ) * (x * E) := by
  have hE0 : 0 ≤ x * E := le_trans (norm_nonneg _) (rT_norm_le η x E hx hE q hq1 hq2 0 δ hδ)
  have h1 := sq_sum_le_card_mul_sum_sq (s := cop q) (f := fun a => ‖rT η x q a δ‖)
  rw [card_cop] at h1
  have h2 := rT_sq_sum_le η x E hx hE q hq1 hq2 δ hδ
  have h3 : (∑ a ∈ cop q, ‖rT η x q a δ‖) ^ 2 ≤ (q.totient : ℝ) * (x * E) ^ 2 :=
    le_trans h1 (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _))
  calc ∑ a ∈ cop q, ‖rT η x q a δ‖ ≤ Real.sqrt ((q.totient : ℝ) * (x * E) ^ 2) :=
        Real.le_sqrt_of_sq_le h3
    _ = Real.sqrt (q.totient : ℝ) * (x * E) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hE0]

/-! ## Continuity -/

theorem e_nat (n : ℕ) : e (n : ℝ) = 1 := (e_eq_one_iff (n : ℝ)).mpr ⟨n, (Int.cast_natCast n).symm⟩

theorem smSum_add_one (η : ℝ → ℝ) (x α : ℝ) :
    Smooth.smSum η x (α + 1) = Smooth.smSum η x α := by
  unfold Smooth.smSum
  refine tsum_congr fun n => ?_
  rw [mul_add, mul_one, ← e_add, e_nat n, mul_one]

/-- `α ↦ S_η(α,x)` is continuous for EVERY `η` (`smSum_junk` when not summable). -/
theorem continuous_sm (η : ℝ → ℝ) (x : ℝ) : Continuous (Smooth.smSum η x) := by
  by_cases hs : Summable (fun n : ℕ => Λ n * |η ((n : ℝ) / x)|)
  · exact Smooth.continuous_smSum η x hs
  · have h0 : Smooth.smSum η x = fun _ => 0 := funext (Smooth.smSum_junk η x hs)
    rw [h0]
    exact continuous_const

theorem continuous_pt (x : ℝ) (q a : ℕ) : Continuous (pt x q a) := by
  unfold pt
  exact continuous_const.add (continuous_id.div_const x)

/-- `δ ↦ ∑_{(a,q)=1} |S_η(a/q+δ/x)|²` is continuous. -/
theorem continuous_arcSq (η : ℝ → ℝ) (x : ℝ) (q : ℕ) :
    Continuous fun δ => ∑ a ∈ cop q, ‖Smooth.smSum η x (pt x q a δ)‖ ^ 2 :=
  continuous_finsetSum _ fun a _ => ((continuous_sm η x).comp (continuous_pt x q a)).norm.pow 2

/-! ## Cauchy–Schwarz over a sum of interval integrals -/

/-- `∑_q ∫_{−w_q}^{w_q} f_q g_q ≤ √(∑_q ∫ f_q²)·√(∑_q ∫ g_q²)` for continuous `f_q, g_q`. -/
theorem cs_sum_int (s : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ q, 0 ≤ w q) (f g : ℕ → ℝ → ℝ)
    (hf : ∀ q, Continuous (f q)) (hg : ∀ q, Continuous (g q)) :
    ∑ q ∈ s, ∫ δ in (-w q)..(w q), f q δ * g q δ ≤
      Real.sqrt (∑ q ∈ s, ∫ δ in (-w q)..(w q), f q δ ^ 2) *
        Real.sqrt (∑ q ∈ s, ∫ δ in (-w q)..(w q), g q δ ^ 2) := by
  have hww : ∀ q, -w q ≤ w q := fun q => by linarith [hw q]
  refine FourierBessel.cs_real _ _ _
    (Finset.sum_nonneg fun q _ => intervalIntegral.integral_nonneg (hww q) fun δ _ => sq_nonneg _)
    (Finset.sum_nonneg fun q _ => intervalIntegral.integral_nonneg (hww q) fun δ _ => sq_nonneg _)
    fun l hl => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun q _ => ?_
  have iF : IntervalIntegrable (fun δ => f q δ ^ 2) volume (-w q) (w q) :=
    ((hf q).pow 2).intervalIntegrable _ _
  have iG : IntervalIntegrable (fun δ => g q δ ^ 2) volume (-w q) (w q) :=
    ((hg q).pow 2).intervalIntegrable _ _
  have iFG : IntervalIntegrable (fun δ => f q δ * g q δ) volume (-w q) (w q) :=
    ((hf q).mul (hg q)).intervalIntegrable _ _
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_div, ← intervalIntegral.integral_add
      (iF.const_mul l) (iG.div_const l)]
  refine intervalIntegral.integral_mono_on (hww q) (iFG.const_mul 2)
    ((iF.const_mul l).add (iG.div_const l)) fun δ _ => ?_
  have e1 : l * f q δ ^ 2 + g q δ ^ 2 / l - 2 * (f q δ * g q δ) =
      (l * f q δ - g q δ) ^ 2 / l := by
    field_simp
    ring
  have : 0 ≤ (l * f q δ - g q δ) ^ 2 / l := by positivity
  linarith

/-- The one-interval Cauchy–Schwarz: `∫_{−w}^{w} fg ≤ √(∫f²)·√(∫g²)`. -/
theorem cs_int (w : ℝ) (hw : 0 ≤ w) (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    ∫ δ in (-w)..w, f δ * g δ ≤
      Real.sqrt (∫ δ in (-w)..w, f δ ^ 2) * Real.sqrt (∫ δ in (-w)..w, g δ ^ 2) := by
  have h := cs_sum_int {0} (fun _ => w) (fun _ => hw) (fun _ => f) (fun _ => g) (fun _ => hf)
    (fun _ => hg)
  simpa only [Finset.sum_singleton] using h


/-! ## The spine's integrals and the links -/

/-- `∑_{(a,q)=1} |S_{η}(a/q + δ/x)|²`. -/
noncomputable def aSq (η : ℝ → ℝ) (x : ℝ) (q : ℕ) (δ : ℝ) : ℝ :=
  ∑ a ∈ cop q, ‖Smooth.smSum η x (pt x q a δ)‖ ^ 2

/-- **The main term** `∫_𝔐 M₊²M* e(−Nα)` (`eq:henki`). -/
noncomputable def mainI (ηp ηs : ℝ → ℝ) (N : ℕ) (x : ℝ) : ℂ :=
  arcSum x fun q a δ => mT ηp x q δ ^ 2 * mT ηs x q δ * e (-(N : ℝ) * pt x q a δ)

/-- **The `err` terms** (`eq:huppert` and 1557–1588): `S₊²R* + S₊R₊M* + R₊M₊M*`. -/
noncomputable def rI (ηp ηs : ℝ → ℝ) (N : ℕ) (x : ℝ) : ℂ :=
  arcSum x fun q a δ =>
    (Smooth.smSum ηp x (pt x q a δ) ^ 2 * rT ηs x q a δ +
      Smooth.smSum ηp x (pt x q a δ) * rT ηp x q a δ * mT ηs x q δ +
        rT ηp x q a δ * mT ηp x q δ * mT ηs x q δ) * e (-(N : ℝ) * pt x q a δ)

/-- **The weight of the `R₊M₊M*` term**: `∑_q μ²(q)/φ(q)^{3/2}·∫_{−w_q}^{w_q}|η̂₊||η̂*|`. -/
noncomputable def t3Sum (ηp ηs : ℝ → ℝ) : ℝ :=
  ∑ q ∈ Qs, DS.cQ q / Real.sqrt (q.totient : ℝ) *
    ∫ δ in (-wq q)..(wq q), ‖MajSp.mainFT ηp δ‖ * ‖MajSp.mainFT ηs δ‖

/-- `c₃ = ∑_{q ∈ Qs} μ²(q)/φ(q)^{3/2}` (`3.8523845`, `scratchpad/nefumo/c3.py`). -/
noncomputable def c3 : ℝ := ∑ q ∈ Qs, DS.cQ q / Real.sqrt (q.totient : ℝ)

/-- **[Arcs]**: `∫_𝔐 f = ∑_q (∫_{−w_q}^{w_q} ∑_{(a,q)=1} f(a/q + δ/x) dδ)/x` for continuous
`1`-periodic real `f`. OPEN here; generic measure theory. -/
def ArcsReal : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ f : ℝ → ℝ, Continuous f → (∀ α, f (α + 1) = f α) →
    ∫ α in Smooth.majorSet x, f α =
      ∑ q ∈ Qs, (∫ δ in (-wq q)..(wq q), ∑ a ∈ cop q, f (pt x q a δ)) / x

/-- **[Massacre]** (`eq:massacre`, 5581): `∑_{q ∈ Qs} μ²(q)/φ(q)² ≤ 2.82643`. OPEN; numeric. -/
def Massacre : Prop := ∑ q ∈ Qs, DS.cQ q / (q.totient : ℝ) ≤ 2.82643

/-- **[Madge]** (`eq:madge` at `k = 3`, 646–654): `|η̂∘(−δ)| ≤ |η∘'''|₁/(2π|δ|)³`. A WEIGHT link. -/
def Madge (ηo : ℝ → ℝ) : Prop :=
  ∀ δ : ℝ, δ ≠ 0 →
    ‖MajSp.mainFT ηo δ‖ ≤ MajSp.l1 (iteratedDeriv 3 ηo) / (2 * Real.pi * |δ|) ^ 3

/-- **[Tail]** (`eq:rusko`, `eq:boussole`, 1099–1142, with `eq:gat1o`/`eq:gat1e`): completing the
`q`-sum costs `(4.31004|η∘|₂² + 0.0012|η∘'''|₁²/δ₀⁵)|η*|₁/r`. OPEN; generic given `Madge`. -/
def TailLink : Prop :=
  ∀ ηo ηs : ℝ → ℝ, Integrable ηo (volume.restrict (Set.Ioi 0)) →
    MemLp ηo 2 (volume.restrict (Set.Ioi 0)) → Integrable ηs (volume.restrict (Set.Ioi 0)) →
      Madge ηo → ∀ N : ℕ, 1 ≤ N → ∀ y : ℝ,
        ‖∑ q ∈ Qs, ((SingularSeries.sing3Local q N : ℝ) : ℂ) *
            (∫ δ in (-wq q)..(wq q), gO ηo ηs y δ) -
          ((SingularSeries.sing3 N : ℝ) : ℂ) * ∫ δ, gO ηo ηs y δ‖ ≤
        (4.31004 * MajSp.l2 ηo ^ 2 + 0.0012 * MajSp.l1 (iteratedDeriv 3 ηo) ^ 2 / 8 ^ 5) /
          150000 * MajSp.l1 ηs

/-- **[Hosto]** (`eq:hosto`, 1166–1178): `∫_ℝ η̂∘(−δ)²η̂*(−δ)e(−δy) dδ = C_{η∘,η*}(y)`. OPEN;
generic Fourier inversion. -/
def Hosto : Prop :=
  ∀ ηo ηs : ℝ → ℝ, Integrable ηo (volume.restrict (Set.Ioi 0)) →
    MemLp ηo 2 (volume.restrict (Set.Ioi 0)) → Integrable ηs (volume.restrict (Set.Ioi 0)) →
      MemLp ηs 2 (volume.restrict (Set.Ioi 0)) → ∀ y : ℝ,
        ∫ δ, gO ηo ηs y δ = ((MajSp.ccon ηo ηs y : ℝ) : ℂ)

/-- **[Hosto] at one pair of weights**, the form the composition consumes: a WEIGHT link, implied
by the generic `Hosto` (`hostoW_of_hosto`). -/
def HostoW (ηo ηs : ℝ → ℝ) : Prop :=
  ∀ y : ℝ, ∫ δ, gO ηo ηs y δ = ((MajSp.ccon ηo ηs y : ℝ) : ℂ)

/-- The generic `Hosto` gives `HostoW` at every pair in `L¹ ∩ L²`. -/
theorem hostoW_of_hosto (ho : Hosto) (ηo ηs : ℝ → ℝ)
    (h1 : Integrable ηo (volume.restrict (Set.Ioi 0)))
    (h2 : MemLp ηo 2 (volume.restrict (Set.Ioi 0)))
    (h3 : Integrable ηs (volume.restrict (Set.Ioi 0)))
    (h4 : MemLp ηs 2 (volume.restrict (Set.Ioi 0))) :
    HostoW ηo ηs :=
  ho ηo ηs h1 h2 h3 h4

/-- **[O1]** `η∘ ∈ L¹(0,∞)`. A WEIGHT link. -/
def OInt (ηo : ℝ → ℝ) : Prop := Integrable ηo (volume.restrict (Set.Ioi 0))

/-- **[T3]** (1585–1588): the `R₊M₊M*` weight is `≤ B₊^{1/2}B*^{1/2} = 2.82643|η₊|₂|η*|₂`.
A WEIGHT link: FALSE generically. -/
def T3W (ηp ηs : ℝ → ℝ) : Prop := t3Sum ηp ηs ≤ 2.82643 * MajSp.l2 ηp * MajSp.l2 ηs

/-- **[Joko]** (`eq:joko`, 929–933, 1501–1524): everything but the main and `err` terms is
`≤ (2Z₊LS* + 4√(Z₊Z*)LS₊)x`. A WEIGHT link. -/
def JokoW (ηp ηs : ℝ → ℝ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ Lp Ls : ℝ,
    MajSp.LSBound ηp x Lp → MajSp.LSBound ηs x Ls →
      ‖(∫ α in Smooth.majorSet x, Smooth.kernS ηp ηs N x α) - mainI ηp ηs N x - rI ηp ηs N x‖ ≤
        (2 * MajSp.zk (fun t => ηp t ^ 2) 2 x * Ls +
          4 * Real.sqrt (MajSp.zk (fun t => ηp t ^ 2) 2 x * MajSp.zk (fun t => ηs t ^ 2) 2 x) *
            Lp) * x

/-! ## The `err` terms -/

theorem norm_mT (η : ℝ → ℝ) (x : ℝ) (q : ℕ) (δ : ℝ) :
    ‖mT η x q δ‖ = |(moebius q : ℝ) / (q.totient : ℝ) * x| * ‖MajSp.mainFT η δ‖ := by
  unfold mT
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]

theorem continuous_mT (η : ℝ → ℝ) (h : Integrable η (volume.restrict (Set.Ioi 0))) (x : ℝ)
    (q : ℕ) : Continuous fun δ => ‖mT η x q δ‖ := by
  unfold mT
  exact (continuous_const.mul (continuous_mainFT_of η h)).norm

theorem aSq_nonneg (η : ℝ → ℝ) (x : ℝ) (q : ℕ) (δ : ℝ) : 0 ≤ aSq η x q δ :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **The pointwise bound on the `err` integrand**, per modulus: `|∑_a (…)| ≤ x(E*·∑|S₊|² +
E₊|M*|√(∑|S₊|²) + E₊√φ|M₊||M*|)` (`eq:frainf`; orthogonality in `a` for the `R₊` terms). -/
theorem rA_le (ηp ηs : ℝ → ℝ) (N : ℕ) (x : ℝ) (hx : 0 ≤ x) (Ep Es : ℝ)
    (hEp : MajSp.EBound ηp x Ep) (hEs : MajSp.EBound ηs x Es) (q : ℕ) (hq : q ∈ Qs) (δ : ℝ)
    (hδ : |δ| ≤ wq q) :
    ‖∑ a ∈ cop q, (Smooth.smSum ηp x (pt x q a δ) ^ 2 * rT ηs x q a δ +
      Smooth.smSum ηp x (pt x q a δ) * rT ηp x q a δ * mT ηs x q δ +
        rT ηp x q a δ * mT ηp x q δ * mT ηs x q δ) * e (-(N : ℝ) * pt x q a δ)‖ ≤
      x * (Es * aSq ηp x q δ + Ep * (‖mT ηs x q δ‖ * Real.sqrt (aSq ηp x q δ)) +
        Ep * (Real.sqrt (q.totient : ℝ) * (‖mT ηp x q δ‖ * ‖mT ηs x q δ‖))) := by
  obtain ⟨hq1, hq2⟩ := mem_Qs hq
  have hRs : ∀ a, ‖rT ηs x q a δ‖ ≤ x * Es := fun a => rT_norm_le ηs x Es hx hEs q hq1 hq2 a δ hδ
  have hEp0 : 0 ≤ x * Ep := le_trans (norm_nonneg _) (rT_norm_le ηp x Ep hx hEp q hq1 hq2 0 δ hδ)
  have h2 := rT_sq_sum_le ηp x Ep hx hEp q hq1 hq2 δ hδ
  have h3 := rT_sum_le ηp x Ep hx hEp q hq1 hq2 δ hδ
  have hpt : ∀ a ∈ cop q, ‖(Smooth.smSum ηp x (pt x q a δ) ^ 2 * rT ηs x q a δ +
      Smooth.smSum ηp x (pt x q a δ) * rT ηp x q a δ * mT ηs x q δ +
        rT ηp x q a δ * mT ηp x q δ * mT ηs x q δ) * e (-(N : ℝ) * pt x q a δ)‖ ≤
      ‖Smooth.smSum ηp x (pt x q a δ)‖ ^ 2 * (x * Es) +
        ‖mT ηs x q δ‖ * (‖Smooth.smSum ηp x (pt x q a δ)‖ * ‖rT ηp x q a δ‖) +
          ‖mT ηp x q δ‖ * ‖mT ηs x q δ‖ * ‖rT ηp x q a δ‖ := by
    intro a _
    rw [norm_mul, e_norm, mul_one]
    refine le_trans norm_add₃_le ?_
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow]
    have h1 : ‖Smooth.smSum ηp x (pt x q a δ)‖ ^ 2 * ‖rT ηs x q a δ‖ ≤
        ‖Smooth.smSum ηp x (pt x q a δ)‖ ^ 2 * (x * Es) :=
      mul_le_mul_of_nonneg_left (hRs a) (sq_nonneg _)
    have e2 : ‖Smooth.smSum ηp x (pt x q a δ)‖ * ‖rT ηp x q a δ‖ * ‖mT ηs x q δ‖ =
        ‖mT ηs x q δ‖ * (‖Smooth.smSum ηp x (pt x q a δ)‖ * ‖rT ηp x q a δ‖) := by ring
    have e3 : ‖rT ηp x q a δ‖ * ‖mT ηp x q δ‖ * ‖mT ηs x q δ‖ =
        ‖mT ηp x q δ‖ * ‖mT ηs x q δ‖ * ‖rT ηp x q a δ‖ := by ring
    rw [e2, e3]
    linarith
  have hcs : ∑ a ∈ cop q, ‖Smooth.smSum ηp x (pt x q a δ)‖ * ‖rT ηp x q a δ‖ ≤
      Real.sqrt (aSq ηp x q δ) * (x * Ep) := by
    refine le_trans (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    calc Real.sqrt (∑ a ∈ cop q, ‖rT ηp x q a δ‖ ^ 2) ≤ Real.sqrt ((x * Ep) ^ 2) :=
          Real.sqrt_le_sqrt h2
      _ = x * Ep := Real.sqrt_sq hEp0
  refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum hpt) ?_)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    ← Finset.mul_sum]
  have hA : ∑ a ∈ cop q, ‖Smooth.smSum ηp x (pt x q a δ)‖ ^ 2 = aSq ηp x q δ := rfl
  rw [hA]
  have hM : 0 ≤ ‖mT ηs x q δ‖ := norm_nonneg _
  have hMM : 0 ≤ ‖mT ηp x q δ‖ * ‖mT ηs x q δ‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have k2 := mul_le_mul_of_nonneg_left hcs hM
  have k3 := mul_le_mul_of_nonneg_left h3 hMM
  nlinarith [k2, k3]


/-- `E ≥ 0` whenever `EBound η x E` (its `q = 1`, `χ = 1`, `δ = 0` instance). -/
theorem ebound_nonneg (η : ℝ → ℝ) (x E : ℝ) (h : MajSp.EBound η x E) : 0 ≤ E :=
  le_trans (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (h 1 le_rfl (by norm_num) (1 : DirichletCharacter ℂ 1) 0 (by norm_num))

/-- **`∑_q ∫ ∑_a |S|² = x²A_η`** ([Arcs] at `f = |S_η|²`, which is continuous and `1`-periodic). -/
theorem sum_int_aSq (ar : ArcsReal) (η : ℝ → ℝ) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) :
    ∑ q ∈ Qs, ∫ δ in (-wq q)..(wq q), aSq η x q δ = x ^ 2 * MajSp.amaj η x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have h : ∫ α in Smooth.majorSet x, ‖Smooth.smSum η x α‖ ^ 2 =
      ∑ q ∈ Qs, (∫ δ in (-wq q)..(wq q), aSq η x q δ) / x :=
    ar x hx (fun α => ‖Smooth.smSum η x α‖ ^ 2) ((continuous_sm η x).norm.pow 2)
      (fun α => congrArg (fun z => ‖z‖ ^ 2) (smSum_add_one η x α))
  unfold MajSp.amaj
  rw [h, ← Finset.sum_div]
  field_simp

/-- **`∑_q ∫ |M*|² ≤ 2.82643·x²|η*|₂²`** (`eq:thaddeus`): Plancherel (`DP.mardiQ_of`) per modulus,
then [Massacre]. -/
theorem mS_sq_le (ms : Massacre) (ηs : ℝ → ℝ)
    (hs1 : Integrable ηs (volume.restrict (Set.Ioi 0)))
    (hs2 : Integrable (fun t => ηs t ^ 2) (volume.restrict (Set.Ioi 0))) (x : ℝ) :
    ∑ q ∈ Qs, ∫ δ in (-wq q)..(wq q), ‖mT ηs x q δ‖ ^ 2 ≤
      x ^ 2 * (2.82643 * MajSp.l2 ηs ^ 2) := by
  have mq := DP.mardiQ_of ηs hs1 hs2
  have h1 : ∀ q ∈ Qs, ∫ δ in (-wq q)..(wq q), ‖mT ηs x q δ‖ ^ 2 ≤
      x ^ 2 * MajSp.l2 ηs ^ 2 * (DS.cQ q / q.totient) := by
    intro q _
    have e1 : (fun δ => ‖mT ηs x q δ‖ ^ 2) =
        fun δ => x ^ 2 * (DS.cQ q / q.totient) * ‖MajSp.mainFT ηs δ‖ ^ 2 := by
      funext δ
      rw [norm_mT, mul_pow, sq_abs]
      unfold DS.cQ
      ring
    rw [e1, intervalIntegral.integral_const_mul]
    have hc : 0 ≤ x ^ 2 * (DS.cQ q / q.totient) :=
      mul_nonneg (sq_nonneg x) (div_nonneg (DS.cQ_nonneg q) (Nat.cast_nonneg _))
    calc x ^ 2 * (DS.cQ q / q.totient) *
          ∫ δ in (-wq q)..(wq q), ‖MajSp.mainFT ηs δ‖ ^ 2
        ≤ x ^ 2 * (DS.cQ q / q.totient) * MajSp.l2 ηs ^ 2 :=
          mul_le_mul_of_nonneg_left (mq (wq q) (wq_nonneg q)) hc
      _ = x ^ 2 * MajSp.l2 ηs ^ 2 * (DS.cQ q / q.totient) := by ring
  calc ∑ q ∈ Qs, ∫ δ in (-wq q)..(wq q), ‖mT ηs x q δ‖ ^ 2
      ≤ ∑ q ∈ Qs, x ^ 2 * MajSp.l2 ηs ^ 2 * (DS.cQ q / q.totient) := Finset.sum_le_sum h1
    _ = x ^ 2 * MajSp.l2 ηs ^ 2 * ∑ q ∈ Qs, DS.cQ q / q.totient := by rw [Finset.mul_sum]
    _ ≤ x ^ 2 * MajSp.l2 ηs ^ 2 * 2.82643 :=
        mul_le_mul_of_nonneg_left ms (mul_nonneg (sq_nonneg x) (sq_nonneg _))
    _ = x ^ 2 * (2.82643 * MajSp.l2 ηs ^ 2) := by ring

/-- `√φ·(μ/φ·x)² = x²·(μ²/φ)/√φ` for `φ > 0`. -/
theorem sqrt_weight (m φ x : ℝ) (hφ : 0 < φ) :
    Real.sqrt φ * (m / φ * x) ^ 2 = x ^ 2 * (m ^ 2 / φ / Real.sqrt φ) := by
  have hs : 0 < Real.sqrt φ := Real.sqrt_pos.mpr hφ
  have hss : Real.sqrt φ * Real.sqrt φ = φ := Real.mul_self_sqrt hφ.le
  field_simp
  linear_combination (m ^ 2 * x ^ 2) * hss

/-- **`∑_q ∫ √φ(q)|M₊||M*| = x²·t3Sum`**. -/
theorem mm_sum (ηp ηs : ℝ → ℝ) (x : ℝ) :
    ∑ q ∈ Qs, ∫ δ in (-wq q)..(wq q),
        Real.sqrt (q.totient : ℝ) * (‖mT ηp x q δ‖ * ‖mT ηs x q δ‖) =
      x ^ 2 * t3Sum ηp ηs := by
  unfold t3Sum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (mem_Qs hq).1
  have e1 : (fun δ => Real.sqrt (q.totient : ℝ) * (‖mT ηp x q δ‖ * ‖mT ηs x q δ‖)) =
      fun δ => x ^ 2 * (DS.cQ q / Real.sqrt (q.totient : ℝ)) *
        (‖MajSp.mainFT ηp δ‖ * ‖MajSp.mainFT ηs δ‖) := by
    funext δ
    rw [norm_mT, norm_mT]
    have key := sqrt_weight (moebius q : ℝ) (q.totient : ℝ) x hφ
    have habs : |(moebius q : ℝ) / (q.totient : ℝ) * x| *
        |(moebius q : ℝ) / (q.totient : ℝ) * x| = ((moebius q : ℝ) / (q.totient : ℝ) * x) ^ 2 := by
      rw [abs_mul_abs_self, sq]
    unfold DS.cQ
    calc Real.sqrt (q.totient : ℝ) *
          (|(moebius q : ℝ) / (q.totient : ℝ) * x| * ‖MajSp.mainFT ηp δ‖ *
            (|(moebius q : ℝ) / (q.totient : ℝ) * x| * ‖MajSp.mainFT ηs δ‖))
        = Real.sqrt (q.totient : ℝ) * (|(moebius q : ℝ) / (q.totient : ℝ) * x| *
            |(moebius q : ℝ) / (q.totient : ℝ) * x|) *
              (‖MajSp.mainFT ηp δ‖ * ‖MajSp.mainFT ηs δ‖) := by ring
      _ = x ^ 2 * ((moebius q : ℝ) ^ 2 / (q.totient : ℝ) / Real.sqrt (q.totient : ℝ)) *
            (‖MajSp.mainFT ηp δ‖ * ‖MajSp.mainFT ηs δ‖) := by rw [habs, key]
  rw [e1, intervalIntegral.integral_const_mul]
  ring


/-- **The `err` terms, integrated** (`eq:teresa`, 1594–1610, with the `R₊M₊M*` weight kept as
`t3Sum`): `|rI| ≤ (E*·A + E₊·√2.82643·√A·|η*|₂ + E₊·t3Sum)·x²`. -/
theorem rI_le (ar : ArcsReal) (ms : Massacre) (ηp ηs : ℝ → ℝ)
    (hp1 : Integrable ηp (volume.restrict (Set.Ioi 0)))
    (hs1 : Integrable ηs (volume.restrict (Set.Ioi 0)))
    (hs2 : Integrable (fun t => ηs t ^ 2) (volume.restrict (Set.Ioi 0)))
    (N : ℕ) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (Ep Es : ℝ) (hEp : MajSp.EBound ηp x Ep)
    (hEs : MajSp.EBound ηs x Es) :
    ‖rI ηp ηs N x‖ ≤ (Es * MajSp.amaj ηp x +
      Ep * (Real.sqrt 2.82643 * Real.sqrt (MajSp.amaj ηp x) * MajSp.l2 ηs) +
        Ep * t3Sum ηp ηs) * x ^ 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hEp0 : 0 ≤ Ep := ebound_nonneg ηp x Ep hEp
  have cA : ∀ q, Continuous fun δ => aSq ηp x q δ := fun q => continuous_arcSq ηp x q
  have cMs : ∀ q, Continuous fun δ => ‖mT ηs x q δ‖ := fun q => continuous_mT ηs hs1 x q
  have cMp : ∀ q, Continuous fun δ => ‖mT ηp x q δ‖ := fun q => continuous_mT ηp hp1 x q
  have cR : ∀ q, Continuous fun δ => Real.sqrt (aSq ηp x q δ) := fun q => (cA q).sqrt
  have i1 : ∀ q, IntervalIntegrable (fun δ => Es * aSq ηp x q δ) volume (-wq q) (wq q) :=
    fun q => ((cA q).intervalIntegrable _ _).const_mul Es
  have i2 : ∀ q, IntervalIntegrable
      (fun δ => Ep * (‖mT ηs x q δ‖ * Real.sqrt (aSq ηp x q δ))) volume (-wq q) (wq q) :=
    fun q => (((cMs q).mul (cR q)).intervalIntegrable _ _).const_mul Ep
  have i3 : ∀ q, IntervalIntegrable (fun δ => Ep * (Real.sqrt (q.totient : ℝ) *
      (‖mT ηp x q δ‖ * ‖mT ηs x q δ‖))) volume (-wq q) (wq q) :=
    fun q => ((continuous_const.mul ((cMp q).mul (cMs q))).intervalIntegrable _ _).const_mul Ep
  have i12 : ∀ q, IntervalIntegrable (fun δ => Es * aSq ηp x q δ +
      Ep * (‖mT ηs x q δ‖ * Real.sqrt (aSq ηp x q δ))) volume (-wq q) (wq q) :=
    fun q => (i1 q).add (i2 q)
  have hq : ∀ q ∈ Qs, ‖(∫ δ in (-wq q)..(wq q), ∑ a ∈ cop q,
      (Smooth.smSum ηp x (pt x q a δ) ^ 2 * rT ηs x q a δ +
        Smooth.smSum ηp x (pt x q a δ) * rT ηp x q a δ * mT ηs x q δ +
          rT ηp x q a δ * mT ηp x q δ * mT ηs x q δ) * e (-(N : ℝ) * pt x q a δ)) / (x : ℂ)‖ ≤
      Es * (∫ δ in (-wq q)..(wq q), aSq ηp x q δ) +
        Ep * (∫ δ in (-wq q)..(wq q), ‖mT ηs x q δ‖ * Real.sqrt (aSq ηp x q δ)) +
          Ep * (∫ δ in (-wq q)..(wq q), Real.sqrt (q.totient : ℝ) *
            (‖mT ηp x q δ‖ * ‖mT ηs x q δ‖)) := by
    intro q hq
    have hww : -wq q ≤ wq q := by linarith [wq_nonneg q]
    have hb := intervalIntegral.norm_integral_le_of_norm_le hww
      (ae_of_all _ fun δ hδ => rA_le ηp ηs N x hx0.le Ep Es hEp hEs q hq δ
        (abs_le.mpr ⟨hδ.1.le, hδ.2⟩))
      (((i12 q).add (i3 q)).const_mul x)
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (i12 q) (i3 q),
      intervalIntegral.integral_add (i1 q) (i2 q), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hb
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hx0.le, div_le_iff₀ hx0]
    linarith
  have hsum : ‖rI ηp ηs N x‖ ≤ Es * (∑ q ∈ Qs, ∫ δ in (-wq q)..(wq q), aSq ηp x q δ) +
      Ep * (∑ q ∈ Qs, ∫ δ in (-wq q)..(wq q), ‖mT ηs x q δ‖ * Real.sqrt (aSq ηp x q δ)) +
        Ep * (∑ q ∈ Qs, ∫ δ in (-wq q)..(wq q), Real.sqrt (q.totient : ℝ) *
          (‖mT ηp x q δ‖ * ‖mT ηs x q δ‖)) := by
    simp only [rI, arcSum]
    refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum hq) (le_of_eq ?_))
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum]
  have hA := sum_int_aSq ar ηp x hx
  have hC := mm_sum ηp ηs x
  have hsq : ∑ q ∈ Qs, ∫ δ in (-wq q)..(wq q), Real.sqrt (aSq ηp x q δ) ^ 2 =
      x ^ 2 * MajSp.amaj ηp x := by
    rw [← hA]
    refine Finset.sum_congr rfl fun q _ => ?_
    refine intervalIntegral.integral_congr fun δ _ => ?_
    exact Real.sq_sqrt (aSq_nonneg ηp x q δ)
  have hcs : ∑ q ∈ Qs, ∫ δ in (-wq q)..(wq q), ‖mT ηs x q δ‖ * Real.sqrt (aSq ηp x q δ) ≤
      Real.sqrt (∑ q ∈ Qs, ∫ δ in (-wq q)..(wq q), ‖mT ηs x q δ‖ ^ 2) *
        Real.sqrt (∑ q ∈ Qs, ∫ δ in (-wq q)..(wq q), Real.sqrt (aSq ηp x q δ) ^ 2) :=
    cs_sum_int Qs wq wq_nonneg (fun q δ => ‖mT ηs x q δ‖) (fun q δ => Real.sqrt (aSq ηp x q δ))
      cMs cR
  have s1 : Real.sqrt (x ^ 2 * (2.82643 * MajSp.l2 ηs ^ 2)) =
      x * (Real.sqrt 2.82643 * MajSp.l2 ηs) := by
    rw [Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq hx0.le, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (MajSp.l2_nonneg ηs)]
  have s2 : Real.sqrt (x ^ 2 * MajSp.amaj ηp x) = x * Real.sqrt (MajSp.amaj ηp x) := by
    rw [Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq hx0.le]
  have hB : ∑ q ∈ Qs, ∫ δ in (-wq q)..(wq q), ‖mT ηs x q δ‖ * Real.sqrt (aSq ηp x q δ) ≤
      x * (Real.sqrt 2.82643 * MajSp.l2 ηs) * (x * Real.sqrt (MajSp.amaj ηp x)) := by
    rw [hsq, s2] at hcs
    rw [← s1]
    have hxA : 0 ≤ x * Real.sqrt (MajSp.amaj ηp x) := mul_nonneg hx0.le (Real.sqrt_nonneg _)
    exact le_trans hcs (mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (mS_sq_le ms ηs hs1 hs2 x)) hxA)
  rw [hA, hC] at hsum
  have hB' := mul_le_mul_of_nonneg_left hB hEp0
  have e1 : (Es * MajSp.amaj ηp x +
      Ep * (Real.sqrt 2.82643 * Real.sqrt (MajSp.amaj ηp x) * MajSp.l2 ηs) +
        Ep * t3Sum ηp ηs) * x ^ 2 =
      Es * (x ^ 2 * MajSp.amaj ηp x) +
        Ep * (x * (Real.sqrt 2.82643 * MajSp.l2 ηs) * (x * Real.sqrt (MajSp.amaj ηp x))) +
          Ep * (x ^ 2 * t3Sum ηp ηs) := by ring
  rw [e1]
  linarith

/-! ## The band term (1078–1098) -/

theorem continuous_gO (η ηs : ℝ → ℝ) (h1 : Integrable η (volume.restrict (Set.Ioi 0)))
    (hs1 : Integrable ηs (volume.restrict (Set.Ioi 0))) (y : ℝ) : Continuous (gO η ηs y) := by
  unfold gO
  exact (((continuous_mainFT_of η h1).pow 2).mul (continuous_mainFT_of ηs hs1)).mul
    (Spine.continuous_e.comp (continuous_mul_const y).neg)

/-- **The band step, per modulus** (`eq:pommes`): `|∫(η̂₊² − η̂∘²)η̂* e| ≤ |η*|₁(2dℓ + d²)`,
`d = |η₊ − η∘|₂`, `ℓ = |η∘|₂` (Cauchy–Schwarz and Plancherel on `[−w, w]`). -/
theorem band_q (ηp ηo ηs : ℝ → ℝ) (hp1 : Integrable ηp (volume.restrict (Set.Ioi 0)))
    (ho1 : Integrable ηo (volume.restrict (Set.Ioi 0)))
    (hs1 : Integrable ηs (volume.restrict (Set.Ioi 0)))
    (ho2 : Integrable (fun t => ηo t ^ 2) (volume.restrict (Set.Ioi 0)))
    (hd2 : Integrable (fun t => (ηp t - ηo t) ^ 2) (volume.restrict (Set.Ioi 0)))
    (y w : ℝ) (hw : 0 ≤ w) :
    ‖(∫ δ in (-w)..w, gO ηp ηs y δ) - ∫ δ in (-w)..w, gO ηo ηs y δ‖ ≤
      MajSp.l1 ηs * (2 * MajSp.l2 (fun t => ηp t - ηo t) * MajSp.l2 ηo +
        MajSp.l2 (fun t => ηp t - ηo t) ^ 2) := by
  have hww : -w ≤ w := by linarith
  have hd1 : Integrable (fun t => ηp t - ηo t) (volume.restrict (Set.Ioi 0)) := hp1.sub ho1
  have cD := (continuous_mainFT_of _ hd1).norm
  have cO := (continuous_mainFT_of _ ho1).norm
  rw [← intervalIntegral.integral_sub ((continuous_gO ηp ηs hp1 hs1 y).intervalIntegrable _ _)
    ((continuous_gO ηo ηs ho1 hs1 y).intervalIntegrable _ _)]
  have hpt : ∀ δ, ‖gO ηp ηs y δ - gO ηo ηs y δ‖ ≤ MajSp.l1 ηs *
      (2 * (‖MajSp.mainFT (fun t => ηp t - ηo t) δ‖ * ‖MajSp.mainFT ηo δ‖) +
        ‖MajSp.mainFT (fun t => ηp t - ηo t) δ‖ ^ 2) := by
    intro δ
    have hF : MajSp.mainFT ηp δ =
        MajSp.mainFT ηo δ + MajSp.mainFT (fun t => ηp t - ηo t) δ := by
      rw [mainFT_sub ηp ηo hp1 ho1 δ]
      ring
    have e1 : gO ηp ηs y δ - gO ηo ηs y δ = MajSp.mainFT (fun t => ηp t - ηo t) δ *
        (2 * MajSp.mainFT ηo δ + MajSp.mainFT (fun t => ηp t - ηo t) δ) *
          (MajSp.mainFT ηs δ * e (-(δ * y))) := by
      unfold gO
      rw [hF]
      ring
    rw [e1, norm_mul, norm_mul, norm_mul, e_norm, mul_one]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    have h1 : ‖2 * MajSp.mainFT ηo δ + MajSp.mainFT (fun t => ηp t - ηo t) δ‖ ≤
        2 * ‖MajSp.mainFT ηo δ‖ + ‖MajSp.mainFT (fun t => ηp t - ηo t) δ‖ := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, h2]
    have h3 := norm_mainFT_le ηs δ
    have ha : 0 ≤ ‖MajSp.mainFT (fun t => ηp t - ηo t) δ‖ := norm_nonneg _
    have hb : 0 ≤ 2 * ‖MajSp.mainFT ηo δ‖ + ‖MajSp.mainFT (fun t => ηp t - ηo t) δ‖ := by
      positivity
    calc ‖MajSp.mainFT (fun t => ηp t - ηo t) δ‖ *
          ‖2 * MajSp.mainFT ηo δ + MajSp.mainFT (fun t => ηp t - ηo t) δ‖ *
            ‖MajSp.mainFT ηs δ‖
        ≤ ‖MajSp.mainFT (fun t => ηp t - ηo t) δ‖ *
            (2 * ‖MajSp.mainFT ηo δ‖ + ‖MajSp.mainFT (fun t => ηp t - ηo t) δ‖) *
              MajSp.l1 ηs :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 ha) h3 (norm_nonneg _) (mul_nonneg ha hb)
      _ = MajSp.l1 ηs * (2 * (‖MajSp.mainFT (fun t => ηp t - ηo t) δ‖ *
            ‖MajSp.mainFT ηo δ‖) + ‖MajSp.mainFT (fun t => ηp t - ηo t) δ‖ ^ 2) := by ring
  have iP : IntervalIntegrable (fun δ => ‖MajSp.mainFT (fun t => ηp t - ηo t) δ‖ *
      ‖MajSp.mainFT ηo δ‖) volume (-w) w := (cD.mul cO).intervalIntegrable _ _
  have iS : IntervalIntegrable (fun δ => ‖MajSp.mainFT (fun t => ηp t - ηo t) δ‖ ^ 2)
      volume (-w) w := (cD.pow 2).intervalIntegrable _ _
  have iPS : IntervalIntegrable (fun δ => 2 * (‖MajSp.mainFT (fun t => ηp t - ηo t) δ‖ *
      ‖MajSp.mainFT ηo δ‖) + ‖MajSp.mainFT (fun t => ηp t - ηo t) δ‖ ^ 2) volume (-w) w :=
    (iP.const_mul 2).add iS
  refine le_trans (intervalIntegral.norm_integral_le_of_norm_le hww
    (ae_of_all _ fun δ _ => hpt δ) (iPS.const_mul _)) ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (iP.const_mul 2) iS,
    intervalIntegral.integral_const_mul]
  have hcs := cs_int w hw (fun δ => ‖MajSp.mainFT (fun t => ηp t - ηo t) δ‖)
    (fun δ => ‖MajSp.mainFT ηo δ‖) cD cO
  have mD := DP.mardiQ_of _ hd1 hd2 w hw
  have mO := DP.mardiQ_of _ ho1 ho2 w hw
  have sD : Real.sqrt (∫ δ in (-w)..w, ‖MajSp.mainFT (fun t => ηp t - ηo t) δ‖ ^ 2) ≤
      MajSp.l2 (fun t => ηp t - ηo t) := by
    rw [← Real.sqrt_sq (MajSp.l2_nonneg (fun t => ηp t - ηo t))]
    exact Real.sqrt_le_sqrt mD
  have sO : Real.sqrt (∫ δ in (-w)..w, ‖MajSp.mainFT ηo δ‖ ^ 2) ≤ MajSp.l2 ηo := by
    rw [← Real.sqrt_sq (MajSp.l2_nonneg ηo)]
    exact Real.sqrt_le_sqrt mO
  have hpr : Real.sqrt (∫ δ in (-w)..w, ‖MajSp.mainFT (fun t => ηp t - ηo t) δ‖ ^ 2) *
      Real.sqrt (∫ δ in (-w)..w, ‖MajSp.mainFT ηo δ‖ ^ 2) ≤
        MajSp.l2 (fun t => ηp t - ηo t) * MajSp.l2 ηo :=
    mul_le_mul sD sO (Real.sqrt_nonneg _) (MajSp.l2_nonneg _)
  have hK : 2 * (∫ δ in (-w)..w, ‖MajSp.mainFT (fun t => ηp t - ηo t) δ‖ *
        ‖MajSp.mainFT ηo δ‖) + ∫ δ in (-w)..w, ‖MajSp.mainFT (fun t => ηp t - ηo t) δ‖ ^ 2 ≤
      2 * MajSp.l2 (fun t => ηp t - ηo t) * MajSp.l2 ηo +
        MajSp.l2 (fun t => ηp t - ηo t) ^ 2 := by
    have : ∫ δ in (-w)..w, ‖MajSp.mainFT (fun t => ηp t - ηo t) δ‖ ^ 2 ≤
        MajSp.l2 (fun t => ηp t - ηo t) ^ 2 := mD
    linarith
  exact mul_le_mul_of_nonneg_left hK (MajSp.l1_nonneg ηs)

/-- `|T₃(q, N)| ≤ μ²(q)/φ(q)²` (uniform in `N`). -/
theorem norm_sing3Local_le (q N : ℕ) :
    ‖SingularSeries.sing3Local q N‖ ≤ DS.cQ q / q.totient := by
  have h := SingularSeries.norm_sing3Arith_le_maj N q
  rw [SingularSeries.sing3Arith_apply] at h
  have e1 : SingularSeries.sing3Maj q = DS.cQ q / q.totient := by
    unfold SingularSeries.sing3Maj DS.cQ
    ring
  rwa [e1] at h

/-- **The band step, summed** (`eq:pommes` with `eq:massacre`). -/
theorem band_le (ms : Massacre) (ηp ηo ηs : ℝ → ℝ)
    (hp1 : Integrable ηp (volume.restrict (Set.Ioi 0)))
    (ho1 : Integrable ηo (volume.restrict (Set.Ioi 0)))
    (hs1 : Integrable ηs (volume.restrict (Set.Ioi 0)))
    (ho2 : Integrable (fun t => ηo t ^ 2) (volume.restrict (Set.Ioi 0)))
    (hd2 : Integrable (fun t => (ηp t - ηo t) ^ 2) (volume.restrict (Set.Ioi 0)))
    (N : ℕ) (y : ℝ) :
    ‖∑ q ∈ Qs, ((SingularSeries.sing3Local q N : ℝ) : ℂ) *
        ((∫ δ in (-wq q)..(wq q), gO ηp ηs y δ) - ∫ δ in (-wq q)..(wq q), gO ηo ηs y δ)‖ ≤
      2.82643 * (MajSp.l1 ηs * (2 * MajSp.l2 (fun t => ηp t - ηo t) * MajSp.l2 ηo +
        MajSp.l2 (fun t => ηp t - ηo t) ^ 2)) := by
  have hK : 0 ≤ MajSp.l1 ηs * (2 * MajSp.l2 (fun t => ηp t - ηo t) * MajSp.l2 ηo +
      MajSp.l2 (fun t => ηp t - ηo t) ^ 2) :=
    mul_nonneg (MajSp.l1_nonneg ηs) (add_nonneg (mul_nonneg (mul_nonneg zero_le_two
      (MajSp.l2_nonneg _)) (MajSp.l2_nonneg _)) (sq_nonneg _))
  have h1 : ∀ q ∈ Qs, ‖((SingularSeries.sing3Local q N : ℝ) : ℂ) *
      ((∫ δ in (-wq q)..(wq q), gO ηp ηs y δ) - ∫ δ in (-wq q)..(wq q), gO ηo ηs y δ)‖ ≤
        DS.cQ q / q.totient * (MajSp.l1 ηs * (2 * MajSp.l2 (fun t => ηp t - ηo t) *
          MajSp.l2 ηo + MajSp.l2 (fun t => ηp t - ηo t) ^ 2)) := by
    intro q _
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul (norm_sing3Local_le q N)
      (band_q ηp ηo ηs hp1 ho1 hs1 ho2 hd2 y (wq q) (wq_nonneg q)) (norm_nonneg _)
      (div_nonneg (DS.cQ_nonneg q) (Nat.cast_nonneg _))
  refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum h1) ?_)
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right ms hK

/-! ## The main term: band, completion, `eq:hosto` -/

/-- `2dℓ + d² ≤ (2 + ε₀)ε₀ℓ²` when `0 ≤ d ≤ ε₀ℓ`. -/
theorem band_arith (d lo ε₀ : ℝ) (hd : 0 ≤ d) (hlo : 0 ≤ lo) (h : d ≤ ε₀ * lo) :
    2 * d * lo + d ^ 2 ≤ lo ^ 2 * (2 + ε₀) * ε₀ := by
  have h1 : 2 * d * lo ≤ 2 * (ε₀ * lo) * lo := by nlinarith
  have h2 : d ^ 2 ≤ (ε₀ * lo) ^ 2 := pow_le_pow_left₀ hd h 2
  nlinarith

/-- **The main term of `prop:nefumo`** (`eq:notspel`, `eq:stev`): `|mainI − C₀C_{η∘,η*}x²| ≤
(2.82643|η∘|₂²(2+ε₀)ε₀ + (4.31004|η∘|₂² + 0.0012|η∘'''|₁²/δ₀⁵)/r)|η*|₁x²`. -/
theorem main_close (ms : Massacre) (tl : TailLink) (ηp ηs ηo : ℝ → ℝ)
    (hp1 : Integrable ηp (volume.restrict (Set.Ioi 0)))
    (hp2 : MemLp ηp 2 (volume.restrict (Set.Ioi 0)))
    (hs1 : Integrable ηs (volume.restrict (Set.Ioi 0)))
    (ho1 : Integrable ηo (volume.restrict (Set.Ioi 0)))
    (ho2 : MemLp ηo 2 (volume.restrict (Set.Ioi 0)))
    (md : Madge ηo) (hw : HostoW ηo ηs) (ε₀ : ℝ)
    (hband : MajSp.l2 (fun t => ηp t - ηo t) < ε₀ * MajSp.l2 ηo) (N : ℕ) (hN : 1 ≤ N)
    (x : ℝ) (hx : x ≠ 0) :
    ‖mainI ηp ηs N x - ((SingularSeries.sing3 N * MajSp.ccon ηo ηs (N / x) * x ^ 2 : ℝ) : ℂ)‖ ≤
      (2.82643 * MajSp.l2 ηo ^ 2 * (2 + ε₀) * ε₀ +
        (4.31004 * MajSp.l2 ηo ^ 2 + 0.0012 * MajSp.l1 (iteratedDeriv 3 ηo) ^ 2 / 8 ^ 5) /
          150000) * MajSp.l1 ηs * x ^ 2 := by
  have hd2 : Integrable (fun t => (ηp t - ηo t) ^ 2) (volume.restrict (Set.Ioi 0)) :=
    DP.sq_integrable_of_memLp _ (hp2.sub ho2)
  have e1 : mainI ηp ηs N x = ((x ^ 2 : ℝ) : ℂ) * ∑ q ∈ Qs,
      ((SingularSeries.sing3Local q N : ℝ) : ℂ) *
        ∫ δ in (-wq q)..(wq q), gO ηp ηs ((N : ℝ) / x) δ := arcSum_main_eq ηp ηs N x hx
  have hh := hw ((N : ℝ) / x)
  have e2 : ((SingularSeries.sing3 N * MajSp.ccon ηo ηs (N / x) * x ^ 2 : ℝ) : ℂ) =
      ((x ^ 2 : ℝ) : ℂ) * (((SingularSeries.sing3 N : ℝ) : ℂ) *
        ∫ δ, gO ηo ηs ((N : ℝ) / x) δ) := by
    rw [hh]
    push_cast
    ring
  have e3 : (∑ q ∈ Qs, ((SingularSeries.sing3Local q N : ℝ) : ℂ) *
        ∫ δ in (-wq q)..(wq q), gO ηp ηs ((N : ℝ) / x) δ) -
      ∑ q ∈ Qs, ((SingularSeries.sing3Local q N : ℝ) : ℂ) *
        ∫ δ in (-wq q)..(wq q), gO ηo ηs ((N : ℝ) / x) δ =
      ∑ q ∈ Qs, ((SingularSeries.sing3Local q N : ℝ) : ℂ) *
        ((∫ δ in (-wq q)..(wq q), gO ηp ηs ((N : ℝ) / x) δ) -
          ∫ δ in (-wq q)..(wq q), gO ηo ηs ((N : ℝ) / x) δ) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q _ => (mul_sub _ _ _).symm
  have hsplit : mainI ηp ηs N x -
      ((SingularSeries.sing3 N * MajSp.ccon ηo ηs (N / x) * x ^ 2 : ℝ) : ℂ) =
      ((x ^ 2 : ℝ) : ℂ) * ((∑ q ∈ Qs, ((SingularSeries.sing3Local q N : ℝ) : ℂ) *
        ((∫ δ in (-wq q)..(wq q), gO ηp ηs ((N : ℝ) / x) δ) -
          ∫ δ in (-wq q)..(wq q), gO ηo ηs ((N : ℝ) / x) δ)) +
      ((∑ q ∈ Qs, ((SingularSeries.sing3Local q N : ℝ) : ℂ) *
        ∫ δ in (-wq q)..(wq q), gO ηo ηs ((N : ℝ) / x) δ) -
          ((SingularSeries.sing3 N : ℝ) : ℂ) * ∫ δ, gO ηo ηs ((N : ℝ) / x) δ)) := by
    rw [e1, e2, ← e3]
    ring
  have hb := band_le ms ηp ηo ηs hp1 ho1 hs1 (DP.sq_integrable_of_memLp _ ho2) hd2 N
    ((N : ℝ) / x)
  have ht := tl ηo ηs ho1 ho2 hs1 md N hN ((N : ℝ) / x)
  have ha := band_arith _ _ ε₀ (MajSp.l2_nonneg _) (MajSp.l2_nonneg _) hband.le
  have hb' : 2.82643 * (MajSp.l1 ηs * (2 * MajSp.l2 (fun t => ηp t - ηo t) * MajSp.l2 ηo +
      MajSp.l2 (fun t => ηp t - ηo t) ^ 2)) ≤
        2.82643 * MajSp.l2 ηo ^ 2 * (2 + ε₀) * ε₀ * MajSp.l1 ηs := by
    have := mul_le_mul_of_nonneg_left ha (MajSp.l1_nonneg ηs)
    nlinarith
  rw [hsplit, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg x)]
  have hsum := norm_add_le (∑ q ∈ Qs, ((SingularSeries.sing3Local q N : ℝ) : ℂ) *
        ((∫ δ in (-wq q)..(wq q), gO ηp ηs ((N : ℝ) / x) δ) -
          ∫ δ in (-wq q)..(wq q), gO ηo ηs ((N : ℝ) / x) δ))
      ((∑ q ∈ Qs, ((SingularSeries.sing3Local q N : ℝ) : ℂ) *
        ∫ δ in (-wq q)..(wq q), gO ηo ηs ((N : ℝ) / x) δ) -
          ((SingularSeries.sing3 N : ℝ) : ℂ) * ∫ δ, gO ηo ηs ((N : ℝ) / x) δ)
  have htot := le_trans hsum (add_le_add (le_trans hb hb') ht)
  have e4 : (2.82643 * MajSp.l2 ηo ^ 2 * (2 + ε₀) * ε₀ +
      (4.31004 * MajSp.l2 ηo ^ 2 + 0.0012 * MajSp.l1 (iteratedDeriv 3 ηo) ^ 2 / 8 ^ 5) /
        150000) * MajSp.l1 ηs * x ^ 2 = x ^ 2 * (2.82643 * MajSp.l2 ηo ^ 2 * (2 + ε₀) * ε₀ *
          MajSp.l1 ηs + (4.31004 * MajSp.l2 ηo ^ 2 +
            0.0012 * MajSp.l1 (iteratedDeriv 3 ηo) ^ 2 / 8 ^ 5) / 150000 * MajSp.l1 ηs) := by
    ring
  rw [e4]
  exact mul_le_mul_of_nonneg_left htot (sq_nonneg x)


/-! ## The composition -/

theorem amaj_nonneg (η : ℝ → ℝ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ MajSp.amaj η x :=
  div_nonneg (integral_nonneg fun _ => sq_nonneg _) hx

/-- `√2.82643 ≤ 1.6812` (`1.6812² = 2.82643344`). -/
theorem sqrt_massacre_le : Real.sqrt 2.82643 ≤ 1.6812 := by
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num

/-- `x ≠ 0` at `x ≥ 4.9·10²⁶`. -/
theorem x_ne (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : x ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hx)

/-- **The closing arithmetic**: the three pieces, with `√2.82643 ≤ 1.6812` and [T3]. -/
theorem close_nefumo (I m r C : ℂ) (x Es Ep A t lp ls b1 L3 : ℝ)
    (h3 : ‖I - m - r‖ ≤ L3 * x)
    (h2 : ‖r‖ ≤ (Es * A + Ep * (Real.sqrt 2.82643 * Real.sqrt A * ls) + Ep * t) * x ^ 2)
    (h1 : ‖m - C‖ ≤ b1) (ht : t ≤ 2.82643 * lp * ls) (hEp : 0 ≤ Ep) (hlp : 0 ≤ lp)
    (hls : 0 ≤ ls) :
    ‖I - C‖ ≤ b1 + (Es * A + Ep * 1.6812 * (Real.sqrt A + 1.6812 * lp) * ls) * x ^ 2 +
      L3 * x := by
  have hsplit : I - C = (I - m - r) + r + (m - C) := by ring
  have htri : ‖I - C‖ ≤ ‖I - m - r‖ + ‖r‖ + ‖m - C‖ := by
    rw [hsplit]
    exact norm_add₃_le
  have hs := sqrt_massacre_le
  have hA : 0 ≤ Real.sqrt A := Real.sqrt_nonneg A
  have k1 : Ep * (Real.sqrt 2.82643 * Real.sqrt A * ls) ≤ Ep * (1.6812 * Real.sqrt A * ls) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hs hA) hls) hEp
  have k2 : Ep * t ≤ Ep * (1.6812 * 1.6812 * lp * ls) := by
    have e : (1.6812 : ℝ) * 1.6812 = 2.82643344 := by norm_num
    have ht' : t ≤ 1.6812 * 1.6812 * lp * ls := by
      rw [e]
      have hpl : 0 ≤ lp * ls := mul_nonneg hlp hls
      nlinarith
    exact mul_le_mul_of_nonneg_left ht' hEp
  have hr : (Es * A + Ep * (Real.sqrt 2.82643 * Real.sqrt A * ls) + Ep * t) * x ^ 2 ≤
      (Es * A + Ep * 1.6812 * (Real.sqrt A + 1.6812 * lp) * ls) * x ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg x)
    nlinarith
  linarith

/-- **THE COMPOSITION: `prop:nefumo`'s live proof, `RW.NefumoW ηp ηs ηo`, from its links.**
Generic links ([Arcs], [Massacre], [Tail]) and weight links ([O1], [Madge], [Hosto], [T3],
[Joko]); the proof is application of `close_nefumo` to [Joko], `rI_le` and `main_close`.
`0 ≤ ε₀` is not used: `0 ≤ |η₊ − η∘|₂ < ε₀|η∘|₂` already forces it. -/
theorem nefumoW_of_links (ar : ArcsReal) (ms : Massacre) (tl : TailLink)
    (ηp ηs ηo : ℝ → ℝ) (oi : OInt ηo) (md : Madge ηo) (hw : HostoW ηo ηs) (t3 : T3W ηp ηs)
    (jk : JokoW ηp ηs) :
    RW.NefumoW ηp ηs ηo := by
  intro rg ε₀ _ hband N hN x hx Ep Es hEp hEs Lp Ls hLp hLs
  obtain ⟨hp1, hp2, hs1, hs2, -, -, ho2⟩ := rg
  exact close_nefumo _ _ _ _ x Es Ep (MajSp.amaj ηp x) (t3Sum ηp ηs) (MajSp.l2 ηp)
    (MajSp.l2 ηs) _ _ (jk N hN x hx Lp Ls hLp hLs)
    (rI_le ar ms ηp ηs (memLp_one_iff_integrable.mp hp1) (memLp_one_iff_integrable.mp hs1)
      (DP.sq_integrable_of_memLp _ hs2) N x hx Ep Es hEp hEs)
    (main_close ms tl ηp ηs ηo (memLp_one_iff_integrable.mp hp1) hp2
      (memLp_one_iff_integrable.mp hs1) oi ho2 md hw ε₀ hband N hN x (x_ne x hx))
    t3 (ebound_nonneg ηp x Ep hEp) (MajSp.l2_nonneg ηp) (MajSp.l2_nonneg ηs)

/-! ## Helfgott's weights -/

/-- **[O1] at Helfgott's `η∘`** (supported on `[0, 2]`, `CT.integrable_circ`). -/
theorem oInt_helf : OInt HW.etaCirc := CT.integrable_circ.integrableOn

/-- **[Madge] at Helfgott's `η∘`**: `DP.decay_circ` (three integrations by parts, `η∘, η∘', η∘''`
vanishing at `0` and `2`) with `DP.l3_le`. -/
theorem madge_helf : Madge HW.etaCirc := by
  intro δ hδ
  rw [DP.mainFT_eq]
  have h1 := DP.decay_circ (-δ) (neg_ne_zero.mpr hδ)
  rw [abs_neg] at h1
  have hpos : 0 < (2 * Real.pi * |δ|) ^ 3 :=
    pow_pos (mul_pos (mul_pos two_pos Real.pi_pos) (abs_pos.mpr hδ)) 3
  exact le_trans h1 (div_le_div_of_nonneg_right DP.l3_le hpos.le)

/-- **`RW.NefumoW` at Helfgott's weights**: the three generic links and the weight links
[Hosto], [T3], [Joko] at `(η₊, η*, η∘)` (`NefumoLinks` discharges [Arcs] and [Hosto]). -/
theorem nefumoW_helf (ar : ArcsReal) (ms : Massacre) (tl : TailLink)
    (hw : HostoW HW.etaCirc HW.etaStar) (t3 : T3W HW.etaPlus HW.etaStar)
    (jk : JokoW HW.etaPlus HW.etaStar) : RW.NefumoW HW.etaPlus HW.etaStar HW.etaCirc :=
  nefumoW_of_links ar ms tl HW.etaPlus HW.etaStar HW.etaCirc oInt_helf madge_helf hw t3 jk

/-! ## What the printed argument actually gives for [T3] -/

/-- **The honest `R₊M₊M*` bound**: `t3Sum ≤ c₃|η₊|₂|η*|₂`, `c₃ = ∑_{q ∈ Qs} μ²(q)/φ(q)^{3/2}`
(`3.8523845`), for EVERY pair in `L¹ ∩ L²` (Cauchy–Schwarz and Plancherel per modulus). The
source's constant is `2.82643 < c₃`. -/
theorem t3_le_c3 (ηp ηs : ℝ → ℝ) (hp1 : Integrable ηp (volume.restrict (Set.Ioi 0)))
    (hp2 : Integrable (fun t => ηp t ^ 2) (volume.restrict (Set.Ioi 0)))
    (hs1 : Integrable ηs (volume.restrict (Set.Ioi 0)))
    (hs2 : Integrable (fun t => ηs t ^ 2) (volume.restrict (Set.Ioi 0))) :
    t3Sum ηp ηs ≤ c3 * MajSp.l2 ηp * MajSp.l2 ηs := by
  have mp := DP.mardiQ_of ηp hp1 hp2
  have mS := DP.mardiQ_of ηs hs1 hs2
  have h1 : ∀ q ∈ Qs, DS.cQ q / Real.sqrt (q.totient : ℝ) *
      (∫ δ in (-wq q)..(wq q), ‖MajSp.mainFT ηp δ‖ * ‖MajSp.mainFT ηs δ‖) ≤
        DS.cQ q / Real.sqrt (q.totient : ℝ) * (MajSp.l2 ηp * MajSp.l2 ηs) := by
    intro q _
    refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (DS.cQ_nonneg q) (Real.sqrt_nonneg _))
    have hcs := cs_int (wq q) (wq_nonneg q) (fun δ => ‖MajSp.mainFT ηp δ‖)
      (fun δ => ‖MajSp.mainFT ηs δ‖) (continuous_mainFT_of ηp hp1).norm
      (continuous_mainFT_of ηs hs1).norm
    have sP : Real.sqrt (∫ δ in (-wq q)..(wq q), ‖MajSp.mainFT ηp δ‖ ^ 2) ≤ MajSp.l2 ηp := by
      rw [← Real.sqrt_sq (MajSp.l2_nonneg ηp)]
      exact Real.sqrt_le_sqrt (mp (wq q) (wq_nonneg q))
    have sS : Real.sqrt (∫ δ in (-wq q)..(wq q), ‖MajSp.mainFT ηs δ‖ ^ 2) ≤ MajSp.l2 ηs := by
      rw [← Real.sqrt_sq (MajSp.l2_nonneg ηs)]
      exact Real.sqrt_le_sqrt (mS (wq q) (wq_nonneg q))
    exact le_trans hcs (mul_le_mul sP sS (Real.sqrt_nonneg _) (MajSp.l2_nonneg _))
  unfold t3Sum c3
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun q hq => ?_
  have := h1 q hq
  linarith

/-- **[T3] is satisfiable**: the zero weights meet it. (It is FALSE for `η₊ = η* = e^{−t}` —
`t3Sum = 1.9261 > 2.82643·|η|₂² = 1.4132`, `scratchpad/nefumo/c3.py` — and TRUE for Helfgott's
`(η∘, η*)` with room `×3.3`, `t3helf.py`; so it is a WEIGHT link.) -/
theorem t3W_zero : T3W 0 0 := by
  have h0 : ∀ δ : ℝ, MajSp.mainFT 0 δ = 0 := fun δ => by simp [MajSp.mainFT]
  unfold T3W t3Sum
  simp [h0, MajSp.l2]

end Principia.Common.TernaryGoldbach.NF
