/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.CoeurSpine
import Principia.Common.TernaryGoldbach.GorshSpine
import Principia.Common.TernaryGoldbach.NefumoLinks
import Principia.Common.TernaryGoldbach.SingularSeries
import Principia.Common.TernaryGoldbach.PlattCite
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

set_option autoImplicit false

/-!
# Helfgott's computer checks, CITED at his exact statements, and the links they feed

**Owner directive (2026-09-30):** *"for anything that is a computer check, don't verify that in
Lean. Instead, in the final project submission, we'll just link Helfgott's verification."* It
extends the 2026-09-29 Platt directive (`PC.PlattThm71`, `PC.PlattTrudgian`). Two limits apply:

* **(a)** a computation is cited only at HIS statement. Where the campaign changed a constant it
  feeds, his run no longer certifies what we consume, and the link is not derived here.
* **(b)** only the COMPUTATION is cited. The analytic argument around it is a proof and stays in
  scope: it is PROVED here or it is a NAMED hypothesis carrying its exact statement.

Every `…Cited` definition below transcribes one computation on Helfgott's own objects, with his
ranges and constants, and its docstring gives the source lines and the link for the final
submission. **Helfgott published no code, data or repository for any of these runs** (web and
arXiv-metadata search, 2026-09-30). What the submission can link is the printed account:
arXiv:1312.7748v2 (`ternvin.tex`), arXiv:1305.2897v4 (`majarcs.tex`), arXiv:1205.5252
(`minarcs.tex`), and the consolidated book draft arXiv:1501.05438.

## The four consumed links and what replaces them

* `NF.Massacre` ← cited `MassacreCited`; no wrapper is left (`massacre_of_cited`, PROVED).
* `NF.GatTail` ← cited `GatProdCited` + named `GatOddWrap` (`gatTail_of_cited`, PROVED).
* `GS.Austeria` ← cited `AusteriaGridCited`, `AusteriaWindowCited` + named `AusteriaLip`, `Crepe`
  + cited `PC.PlattTrudgian` (`austeria_of_cited`, PROVED).
* `CY.EspagnWin 1.36` ← cited `EspagnCheckCited`, `EspagnSmallCited`, `CharpyCited` + named
  `EspagnRed`, `CharpyGap` + the literature `CY.CERange`, `CY.Malito`, `CY.Cante`
  (`espagnWin_of_cited`, PROVED).

`EspagnWin` also needs **`CharpyGap`, a computation NOBODY RAN**: `eq:charpy`'s lower bound is
checked for `R ≤ 4·10⁷` and `eq:malito` only reaches it from `R ≥ 4.4322·10⁷`
(`1.3325822 − 7.284·(4·10⁷)^{−1/3} = 1.31128 < 1.312`). The gap is NOT citable; it is named.

`MR.HelfMajR` and `OL.MinMainL` are NOT derived: the campaign retyped their constants (limit (a)).
Their sub-computations that survive at Helfgott's exact statement are transcribed in §5 and §6
for the submission's citation list; nothing in this library consumes them yet.
-/

namespace Principia.Common.TernaryGoldbach.HC

open MeasureTheory
open Principia.Common.PSieve (gQ)
open Principia.Common.TernaryGoldbach.SingularSeries (sing3Maj sing3Maj_nonneg sing3Maj_summable)

/-! ## (1) `eq:massacre` -/

/-- **CITED computer check — `eq:massacre`** (`ternvin.tex` 5580-5583; method 5584-5586: "an easy
tail bound followed by a computation", footnote 5568: D. Platt's integer arithmetic package; book
arXiv:1501.05438 `sumlaphi.tex` 165): `2.826419 ≤ ∑_{q ≥ 1} μ²(q)/φ(q)² < 2.826421`, on his
object `sing3Maj q = μ(q)²/φ(q)²` (the `q = 0` term is `0`). The junk value `∑' = 0` is excluded by
the lower bound, which is part of what he states: the series converges into this interval.
**Limit (b) bites:** the tail bound (`eq:maloso`) and the finite Euler product are published only
as this one enclosure (the cutoff is unprinted), so the enclosure is cited as one unit.
Link: arXiv:1312.7748v2, eq. (massacre). CITED computer check (owner directive 2026-09-30). -/
def MassacreCited : Prop :=
  2.826419 ≤ ∑' q : ℕ, sing3Maj q ∧ ∑' q : ℕ, sing3Maj q < 2.826421

/-- **The bridge**: the campaign's `DS.cQ q / φ(q)` is Helfgott's `μ(q)²/φ(q)²`. -/
theorem cQ_div_totient (q : ℕ) : DS.cQ q / (q.totient : ℝ) = sing3Maj q := by
  unfold DS.cQ sing3Maj
  ring

/-- **`NF.Massacre` from the cited enclosure, PROVED**: the finite sum over `Qs` of non-negative
terms is at most the full sum, which is `< 2.826421 ≤ 2.82643`. No wrapper remains. -/
theorem massacre_of_cited (h : MassacreCited) : NF.Massacre := by
  unfold NF.Massacre
  rw [Finset.sum_congr rfl fun q _ => cQ_div_totient q]
  have hle : ∑ q ∈ NF.Qs, sing3Maj q ≤ ∑' q : ℕ, sing3Maj q :=
    sing3Maj_summable.sum_le_tsum _ fun q _ => sing3Maj_nonneg q
  linarith [h.2]

/-! ## (2) `eq:gat1o` / `eq:gat1e` -/

/-- The Euler factor `1 + (2p − 1)/((p − 1)²p)` of `∑_{b odd} f₂(b)` (`ternvin.tex` 5645, 5720). -/
noncomputable def gatFac (p : ℕ) : ℝ := 1 + (2 * (p : ℝ) - 1) / (((p : ℝ) - 1) ^ 2 * p)

/-- The partial Euler product over the primes `2 < p ≤ n`. -/
noncomputable def gatPart (n : ℕ) : ℝ := ∏ p ∈ (Finset.Icc 3 n).filter Nat.Prime, gatFac p

/-- **CITED computer check — the Euler product in `eq:gat1o`** (`ternvin.tex` 5720-5721; method
5584-5586, Platt's package): `(12/π²)·∏_{p>2}(1 + (2p−1)/((p−1)²p)) ≤ 2.15502`. Every factor is
`≥ 1`, so the infinite product is the supremum of the partial products and the bound is stated on
every partial product (no `tprod` junk value can make it vacuous). Only this number is computed;
`eq:merleau`, `lem:sidio` and the Euler-product identity are analysis (`GatOddWrap`). **Limit (b)
bites** as for `eq:massacre`: the tail cutoff is unprinted, so the product enclosure is one unit.
Link: arXiv:1312.7748v2, eq. (gat1o). CITED computer check (owner directive 2026-09-30). -/
def GatProdCited : Prop := ∀ n : ℕ, 12 / Real.pi ^ 2 * gatPart n ≤ 2.15502

/-- The product `∏_{p>2}(1 + (2p−1)/((p−1)²p))`, as the supremum of its partial products. -/
noncomputable def gatProd : ℝ := ⨆ n : ℕ, gatPart n

/-- `∑_{q ≥ r, q odd} μ²(q)/φ(q)²`. -/
noncomputable def oddTail (r : ℝ) : ℝ :=
  ∑' q : ℕ, if Odd q ∧ r ≤ (q : ℝ) then sing3Maj q else 0

/-- `∑_{q ≥ r, q even} μ²(q)/φ(q)²`. -/
noncomputable def evenTail (r : ℝ) : ℝ :=
  ∑' q : ℕ, if Even q ∧ r ≤ (q : ℝ) then sing3Maj q else 0

/-- **NAMED analytic wrapper of `eq:gat1o`** (`ternvin.tex` 5713-5722): for every `r > 0`,
`∑_{q ≥ r odd} μ²(q)/φ(q)² ≤ (12/π²)(1/r)∏_{p>2}(1 + (2p−1)/((p−1)²p))`. Its proof is the
convolution identity `eq:merleau` (5640-5646), `lem:sidio` at `j = 2`, `m = 2` (5649-5698),
`ζ(2)/ζ(4) = 15/π²`, and `∑_{b odd} f₂(b) = ∏_{p>2}(1 + f₂(p))`: analysis, no computation. NOT
cited. It does not mention the number `2.15502`. -/
def GatOddWrap : Prop := ∀ r : ℝ, 0 < r → oddTail r ≤ 12 / Real.pi ^ 2 / r * gatProd

/-- The cited product gives `(12/π²)·∏ ≤ 2.15502` for the supremum. -/
theorem gatProd_le (h : GatProdCited) : 12 / Real.pi ^ 2 * gatProd ≤ 2.15502 := by
  have hpos : (0 : ℝ) < 12 / Real.pi ^ 2 := by positivity
  have hb : gatProd ≤ 2.15502 / (12 / Real.pi ^ 2) := by
    unfold gatProd
    refine ciSup_le fun n => ?_
    rw [le_div_iff₀ hpos, mul_comm]
    exact h n
  have hne : (12 / Real.pi ^ 2 : ℝ) ≠ 0 := hpos.ne'
  calc 12 / Real.pi ^ 2 * gatProd ≤ 12 / Real.pi ^ 2 * (2.15502 / (12 / Real.pi ^ 2)) :=
        mul_le_mul_of_nonneg_left hb hpos.le
    _ = 2.15502 := mul_div_cancel₀ _ hne

/-- **`eq:gat1o`, PROVED from the cited product and the named wrapper**:
`∑_{q ≥ r odd} μ²/φ² ≤ 2.15502/r`. -/
theorem oddTail_le (hc : GatProdCited) (hw : GatOddWrap) (r : ℝ) (hr : 0 < r) :
    oddTail r ≤ 2.15502 / r := by
  have h1 := hw r hr
  have h2 := gatProd_le hc
  calc oddTail r ≤ 12 / Real.pi ^ 2 / r * gatProd := h1
    _ = (12 / Real.pi ^ 2 * gatProd) / r := by ring
    _ ≤ 2.15502 / r := div_le_div_of_nonneg_right h2 hr.le

/-- `μ²(2m)/φ(2m)² = μ²(m)/φ(m)²` for odd `m`, and `0` for even `m` (`4 ∣ 2m`). -/
theorem sing3Maj_two_mul (m : ℕ) : sing3Maj (2 * m) = if Odd m then sing3Maj m else 0 := by
  split_ifs with hm
  · have hc : Nat.Coprime 2 m := Nat.coprime_two_left.mpr hm
    have hμ : ArithmeticFunction.moebius (2 * m) = -ArithmeticFunction.moebius m := by
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc,
        ArithmeticFunction.moebius_apply_prime Nat.prime_two]
      ring
    have hφ : Nat.totient (2 * m) = Nat.totient m := by
      rw [Nat.totient_mul hc, Nat.totient_two, one_mul]
    unfold sing3Maj
    rw [hμ, hφ]
    push_cast
    ring
  · obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp hm
    have hsq : ¬Squarefree (2 * m) := by
      intro h
      have h2 := h 2 ⟨k, by rw [hk]; ring⟩
      exact absurd (Nat.isUnit_iff.mp h2) (by norm_num)
    unfold sing3Maj
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    simp

/-- **`eq:gat1e`, PROVED** (the elementary half: even `q = 2q'`, `q'` odd): the even tail from
`2r` is at most the odd tail from `r`. -/
theorem evenTail_two_le (r : ℝ) : evenTail (2 * r) ≤ oddTail r := by
  have ho0 : ∀ q : ℕ, 0 ≤ (if Odd q ∧ r ≤ (q : ℝ) then sing3Maj q else 0) := fun q => by
    split_ifs
    · exact sing3Maj_nonneg q
    · exact le_rfl
  have hos : Summable fun q : ℕ => if Odd q ∧ r ≤ (q : ℝ) then sing3Maj q else 0 :=
    Summable.of_nonneg_of_le ho0 (fun q => by
      split_ifs
      · exact le_rfl
      · exact sing3Maj_nonneg q) sing3Maj_summable
  have hsupp : Function.support (fun q : ℕ => if Even q ∧ 2 * r ≤ (q : ℝ) then sing3Maj q else 0)
      ⊆ Set.range (fun m : ℕ => 2 * m) := by
    intro q hq
    rw [Function.mem_support] at hq
    by_cases h : Even q ∧ 2 * r ≤ (q : ℝ)
    · obtain ⟨k, hk⟩ := h.1
      exact ⟨k, show 2 * k = q by omega⟩
    · exact absurd (if_neg h) hq
  have hinj : Function.Injective (fun m : ℕ => 2 * m) := fun a b hab => by
    have h' : 2 * a = 2 * b := hab
    omega
  have hre : ∑' m : ℕ, (if Even (2 * m) ∧ 2 * r ≤ ((2 * m : ℕ) : ℝ) then sing3Maj (2 * m) else 0)
      = evenTail (2 * r) := hinj.tsum_eq hsupp
  have hpt : ∀ m : ℕ, (if Even (2 * m) ∧ 2 * r ≤ ((2 * m : ℕ) : ℝ) then sing3Maj (2 * m) else 0)
      ≤ (if Odd m ∧ r ≤ (m : ℝ) then sing3Maj m else 0) := by
    intro m
    by_cases h1 : Even (2 * m) ∧ 2 * r ≤ ((2 * m : ℕ) : ℝ)
    · rw [if_pos h1, sing3Maj_two_mul]
      by_cases h2 : Odd m
      · have h1' : 2 * r ≤ 2 * (m : ℝ) := by exact_mod_cast h1.2
        have h3 : Odd m ∧ r ≤ (m : ℝ) := ⟨h2, by linarith⟩
        simp only [if_pos h2, if_pos h3, le_refl]
      · rw [if_neg h2]
        exact ho0 m
    · rw [if_neg h1]
      exact ho0 m
  have hes : Summable fun m : ℕ =>
      (if Even (2 * m) ∧ 2 * r ≤ ((2 * m : ℕ) : ℝ) then sing3Maj (2 * m) else 0) :=
    Summable.of_nonneg_of_le (fun m => by
      split_ifs
      · exact sing3Maj_nonneg _
      · exact le_rfl) hpt hos
  rw [← hre]
  exact hes.tsum_le_tsum hpt hos

/-- Whether the arcs keep the modulus `q` at `δ`: `q ∈ Qs` and `δ ∈ (−w_q, w_q]`. -/
def kept (δ : ℝ) (q : ℕ) : Prop := q ∈ NF.Qs ∧ δ ∈ Set.Ioc (-NF.wq q) (NF.wq q)

open Classical in
/-- The part of `𝔖₃(N)` the arcs keep at `δ`, termwise. -/
noncomputable def keptPart (N : ℕ) (δ : ℝ) (q : ℕ) : ℝ :=
  if kept δ q then SingularSeries.sing3Local q N else 0

/-- An odd modulus the arcs miss at `δ` is `≥ 1/max(1/150000, |δ|/600000)`. -/
theorem odd_missed (δ : ℝ) (q : ℕ) (hq : Odd q) (hmiss : ¬kept δ q) :
    1 ≤ (q : ℝ) * max (1 / 150000) (|δ| / 600000) := by
  have hq1 : 1 ≤ q := hq.pos
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  by_cases hQ : q ∈ NF.Qs
  · have hw : δ ∉ Set.Ioc (-NF.wq q) (NF.wq q) := fun h => hmiss ⟨hQ, h⟩
    have hg : Nat.gcd q 2 = 1 := Nat.coprime_two_right.mpr hq
    have hwq : NF.wq q = 600000 / q := by
      unfold NF.wq
      rw [hg]
      push_cast
      ring
    rw [Set.mem_Ioc, hwq] at hw
    have habs : 600000 / (q : ℝ) ≤ |δ| := by
      by_contra hc0
      have hc := not_le.mp hc0
      exact hw ⟨by linarith [neg_abs_le δ], by linarith [le_abs_self δ]⟩
    have h6 : 600000 ≤ (q : ℝ) * |δ| := by
      rw [div_le_iff₀ hqpos] at habs
      linarith
    have hm : |δ| / 600000 ≤ max (1 / 150000 : ℝ) (|δ| / 600000) := le_max_right _ _
    have h7 : (q : ℝ) * (|δ| / 600000) ≤ (q : ℝ) * max (1 / 150000) (|δ| / 600000) :=
      mul_le_mul_of_nonneg_left hm hqpos.le
    have h8 : (q : ℝ) * (|δ| / 600000) = (q : ℝ) * |δ| / 600000 := by ring
    rw [h8] at h7
    have h9 : 1 ≤ (q : ℝ) * |δ| / 600000 := by
      rw [le_div_iff₀ (by norm_num)]
      linarith
    linarith
  · have h1 : 150000 < q := by
      by_contra hc0
      have hc := not_lt.mp hc0
      exact hQ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq1, hc⟩, hq⟩))
    have hq' : (150000 : ℝ) ≤ q := by exact_mod_cast h1.le
    have hm : 1 / 150000 ≤ max (1 / 150000 : ℝ) (|δ| / 600000) := le_max_left _ _
    calc (1 : ℝ) = 150000 * (1 / 150000) := by norm_num
      _ ≤ (q : ℝ) * max (1 / 150000) (|δ| / 600000) :=
        mul_le_mul hq' hm (by norm_num) hqpos.le

/-- A non-zero even modulus the arcs miss at `δ` is `≥ 2/max(1/150000, |δ|/600000)`. -/
theorem even_missed (δ : ℝ) (q : ℕ) (hq : Even q) (hq0 : q ≠ 0) (hmiss : ¬kept δ q) :
    2 ≤ (q : ℝ) * max (1 / 150000) (|δ| / 600000) := by
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  by_cases hQ : q ∈ NF.Qs
  · have hw : δ ∉ Set.Ioc (-NF.wq q) (NF.wq q) := fun h => hmiss ⟨hQ, h⟩
    have hg : Nat.gcd q 2 = 2 := Nat.gcd_eq_right (even_iff_two_dvd.mp hq)
    have hwq : NF.wq q = 1200000 / q := by
      unfold NF.wq
      rw [hg]
      push_cast
      ring
    rw [Set.mem_Ioc, hwq] at hw
    have habs : 1200000 / (q : ℝ) ≤ |δ| := by
      by_contra hc0
      have hc := not_le.mp hc0
      exact hw ⟨by linarith [neg_abs_le δ], by linarith [le_abs_self δ]⟩
    have h6 : 1200000 ≤ (q : ℝ) * |δ| := by
      rw [div_le_iff₀ hqpos] at habs
      linarith
    have hm : |δ| / 600000 ≤ max (1 / 150000 : ℝ) (|δ| / 600000) := le_max_right _ _
    have h7 : (q : ℝ) * (|δ| / 600000) ≤ (q : ℝ) * max (1 / 150000) (|δ| / 600000) :=
      mul_le_mul_of_nonneg_left hm hqpos.le
    have h8 : (q : ℝ) * (|δ| / 600000) = (q : ℝ) * |δ| / 600000 := by ring
    rw [h8] at h7
    have h9 : 2 ≤ (q : ℝ) * |δ| / 600000 := by
      rw [le_div_iff₀ (by norm_num)]
      linarith
    linarith
  · have h1 : 300000 < q := by
      by_contra hc0
      have hc := not_lt.mp hc0
      exact hQ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq1, hc⟩, hq⟩))
    have hq' : (300000 : ℝ) ≤ q := by exact_mod_cast h1.le
    have hm : 1 / 150000 ≤ max (1 / 150000 : ℝ) (|δ| / 600000) := le_max_left _ _
    calc (2 : ℝ) = 300000 * (1 / 150000) := by norm_num
      _ ≤ (q : ℝ) * max (1 / 150000) (|δ| / 600000) :=
        mul_le_mul hq' hm (by norm_num) hqpos.le

set_option maxHeartbeats 1000000 in
-- The `Summable`/`tsum` API over the `SummationFilter`-parameterised sums elaborates slowly here
-- (the same instance chain `SingularSeries.lean` records); 200000 heartbeats is not enough.
/-- **`NF.GatTail` from the two tails, PROVED** (`ternvin.tex` 1121-1142, `eq:boussole`): what the
arcs miss at `δ` is a sum of `T₃(q, N)` over odd `q ≥ m` and even `q ≥ 2m`,
`m = 1/max(1/150000, |δ|/600000)`, each bounded by `μ²(q)/φ(q)²`; the odd tail is
`≤ 2.15502/m` and the even tail is at most the odd tail (`evenTail_two_le`). -/
theorem gatTail_of_tails (ho : ∀ r : ℝ, 0 < r → oddTail r ≤ 2.15502 / r) : NF.GatTail := by
  intro N hN δ
  have hMpos : (0 : ℝ) < max (1 / 150000) (|δ| / 600000) :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hrpos : (0 : ℝ) < 1 / max (1 / 150000) (|δ| / 600000) := one_div_pos.mpr hMpos
  have hTs : Summable fun q : ℕ => SingularSeries.sing3Local q N :=
    (SingularSeries.sing3_summable N hN).of_norm
  have hKfin : ∀ q ∉ NF.Qs, keptPart N δ q = 0 := fun q hq => if_neg fun h => hq h.1
  have hKs : Summable (keptPart N δ) := summable_of_ne_finset_zero hKfin
  have hwin : NF.win N δ = ∑' q : ℕ, keptPart N δ q := by
    rw [tsum_eq_sum hKfin]
    unfold NF.win
    refine Finset.sum_congr rfl fun q hq => ?_
    unfold keptPart kept
    by_cases h : δ ∈ Set.Ioc (-NF.wq q) (NF.wq q)
    · rw [if_pos h, if_pos ⟨hq, h⟩]
    · rw [if_neg h, if_neg fun h' => h h'.2]
  have hsing : SingularSeries.sing3 N = ∑' q : ℕ, SingularSeries.sing3Local q N := rfl
  have hdiff : SingularSeries.sing3 N - NF.win N δ =
      ∑' q : ℕ, (SingularSeries.sing3Local q N - keptPart N δ q) := by
    rw [hsing, hwin, hTs.tsum_sub hKs]
  -- the missed terms, bounded by the two tails' summands
  have hpt : ∀ q : ℕ, ‖SingularSeries.sing3Local q N - keptPart N δ q‖ ≤
      (if Odd q ∧ 1 / max (1 / 150000) (|δ| / 600000) ≤ (q : ℝ) then sing3Maj q else 0) +
      (if Even q ∧ 2 * (1 / max (1 / 150000) (|δ| / 600000)) ≤ (q : ℝ) then sing3Maj q
        else 0) := by
    intro q
    have hnn : 0 ≤ (if Odd q ∧ 1 / max (1 / 150000) (|δ| / 600000) ≤ (q : ℝ) then sing3Maj q
        else 0) + (if Even q ∧ 2 * (1 / max (1 / 150000) (|δ| / 600000)) ≤ (q : ℝ) then
          sing3Maj q else 0) := by
      apply add_nonneg <;> split_ifs <;> first | exact sing3Maj_nonneg q | exact le_rfl
    by_cases hk : kept δ q
    · have : SingularSeries.sing3Local q N - keptPart N δ q = 0 := by
        unfold keptPart
        rw [if_pos hk, sub_self]
      rw [this, norm_zero]
      exact hnn
    · have e1 : SingularSeries.sing3Local q N - keptPart N δ q =
          SingularSeries.sing3Local q N := by
        unfold keptPart
        rw [if_neg hk, sub_zero]
      rw [e1]
      have hT : ‖SingularSeries.sing3Local q N‖ ≤ sing3Maj q :=
        SingularSeries.norm_sing3Arith_le_maj N q
      rcases Nat.even_or_odd q with he | hod
      · rcases Nat.eq_zero_or_pos q with h0 | hpos
        · subst h0
          have h00 : sing3Maj 0 = 0 := by simp [sing3Maj]
          rw [h00] at hT
          exact hT.trans hnn
        · have h2 := even_missed δ q he hpos.ne' hk
          have hle : 2 * (1 / max (1 / 150000) (|δ| / 600000)) ≤ (q : ℝ) := by
            rw [← mul_div_assoc, mul_one, div_le_iff₀ hMpos]
            linarith
          have hcond : Even q ∧ 2 * (1 / max (1 / 150000) (|δ| / 600000)) ≤ (q : ℝ) :=
            ⟨he, hle⟩
          rw [if_pos hcond]
          have hodd0 : 0 ≤ (if Odd q ∧ 1 / max (1 / 150000) (|δ| / 600000) ≤ (q : ℝ) then
              sing3Maj q else 0) := by
            split_ifs
            · exact sing3Maj_nonneg q
            · exact le_rfl
          linarith
      · have h1 := odd_missed δ q hod hk
        have hle : 1 / max (1 / 150000) (|δ| / 600000) ≤ (q : ℝ) := by
          rw [div_le_iff₀ hMpos]
          linarith
        have hcond : Odd q ∧ 1 / max (1 / 150000) (|δ| / 600000) ≤ (q : ℝ) := ⟨hod, hle⟩
        rw [if_pos hcond]
        have hev0 : 0 ≤ (if Even q ∧ 2 * (1 / max (1 / 150000) (|δ| / 600000)) ≤ (q : ℝ) then
            sing3Maj q else 0) := by
          split_ifs
          · exact sing3Maj_nonneg q
          · exact le_rfl
        linarith
  have hos : Summable fun q : ℕ =>
      (if Odd q ∧ 1 / max (1 / 150000) (|δ| / 600000) ≤ (q : ℝ) then sing3Maj q else 0) :=
    Summable.of_nonneg_of_le (fun q => by
      split_ifs
      · exact sing3Maj_nonneg q
      · exact le_rfl) (fun q => by
      split_ifs
      · exact le_rfl
      · exact sing3Maj_nonneg q) sing3Maj_summable
  have hes : Summable fun q : ℕ =>
      (if Even q ∧ 2 * (1 / max (1 / 150000) (|δ| / 600000)) ≤ (q : ℝ) then sing3Maj q
        else 0) :=
    Summable.of_nonneg_of_le (fun q => by
      split_ifs
      · exact sing3Maj_nonneg q
      · exact le_rfl) (fun q => by
      split_ifs
      · exact le_rfl
      · exact sing3Maj_nonneg q) sing3Maj_summable
  have hns : Summable fun q : ℕ => ‖SingularSeries.sing3Local q N - keptPart N δ q‖ :=
    Summable.of_nonneg_of_le (fun q => norm_nonneg _) hpt (hos.add hes)
  have hsum := norm_tsum_le_tsum_norm hns
  have hsum2 := hns.tsum_le_tsum hpt (hos.add hes)
  rw [hos.tsum_add hes] at hsum2
  have hodd := ho _ hrpos
  have hev := evenTail_two_le (1 / max (1 / 150000) (|δ| / 600000))
  unfold oddTail at hodd hev
  unfold evenTail at hev
  have hfin : 2.15502 / (1 / max (1 / 150000) (|δ| / 600000)) =
      2.15502 * max (1 / 150000) (|δ| / 600000) := by
    rw [div_div_eq_mul_div, div_one]
  rw [hfin] at hodd
  rw [hdiff]
  have key : ‖∑' q : ℕ, (SingularSeries.sing3Local q N - keptPart N δ q)‖ ≤
      4.31004 * max (1 / 150000) (|δ| / 600000) := by
    linarith
  rwa [Real.norm_eq_abs] at key

/-- **`NF.GatTail` from the cited product and the named `eq:gat1o` wrapper.** -/
theorem gatTail_of_cited (hc : GatProdCited) (hw : GatOddWrap) : NF.GatTail :=
  gatTail_of_tails (oddTail_le hc hw)

/-! ## (3) `cor:austeria`, the `1.04488` branch -/

/-- The two windows `(9.5, 10.5) ∪ (13.5, 14.5)` where the grid is too coarse. -/
def austW : Set ℝ := Set.Ioo 9.5 10.5 ∪ Set.Ioo 13.5 14.5

/-- **CITED computer check — `cor:austeria`'s grid for `x < 2000`** (`ternvin.tex` 5543-5550;
book `sumlaphi.tex` 125-141): `S(x) = ∑ Λ(n)η₂(n/x)` computed at `x ∈ (1/1000)ℤ ∩ [0, 2000]`,
where "computing only at grid points results in an inaccuracy of at most `0.00801x`" and "this
resolves the matter at all points outside" the windows. Transcribed as that sentence says: every
`x ∈ [1, 2000)` outside the windows has a grid point `x_k` within `0.0005` with
`S(x_k) + 0.00801x ≤ 1.04488x`. The per-point inequality is not printed; this is its weakest
reading (a float64 sweep of all `2·10⁶` grid points gives margin `≥ 0.054`, at `x = 14.5`,
`scratchpad/hcite/austeria_num.py`). Link: arXiv:1312.7748v2, proof of Cor. (austeria).
CITED computer check (owner directive 2026-09-30). -/
def AusteriaGridCited : Prop :=
  ∀ x : ℝ, 1 ≤ x → x < 2000 → x ∉ austW →
    ∃ k : ℕ, |x - (k : ℝ) / 1000| ≤ 0.0005 ∧
      GS.sEta2 ((k : ℝ) / 1000) + 0.00801 * x ≤ 1.04488 * x

/-- **CITED computer check — `cor:austeria` on the two windows** (`ternvin.tex` 5548-5553): there
"the prime powers involved do not change … and thus we can find the maximum of the sum just by
taking derivatives". The maximum is at `x = 14`, `S(14)/14 = 1.04487679`, a margin of `3.2·10⁻⁶`.
Classified as a computation (a maximisation of an explicit function, evaluated numerically); if
the owner classes it as analysis, it becomes a named wrapper with this same statement.
Link: arXiv:1312.7748v2, proof of Cor. (austeria). CITED computer check (owner directive
2026-09-30). -/
def AusteriaWindowCited : Prop := ∀ x : ℝ, x ∈ austW → GS.sEta2 x ≤ 1.04488 * x

/-- **NAMED analytic wrapper — the grid inaccuracy** (`ternvin.tex` 5543-5547): for `x ≥ 1` and a
grid point `x_k` with `|x − x_k| ≤ 0.0005`, `S(x) ≤ S(x_k) + 0.00801x`, from `|η₂'|_∞ = 16` and
`∑_{x/4 ≤ n ≤ x} Λ(n) ≤ x` (a Chebyshev-type bound). NOT cited: it is a proof. (Sampled float64:
`max (S(x) − S(x_k))/x = 0.0004`, far inside `0.00801`.) -/
def AusteriaLip : Prop :=
  ∀ x : ℝ, 1 ≤ x → ∀ k : ℕ, |x - (k : ℝ) / 1000| ≤ 0.0005 →
    GS.sEta2 x ≤ GS.sEta2 ((k : ℝ) / 1000) + 0.00801 * x

/-- **NAMED analytic wrapper — `lem:crepe`** (`ternvin.tex` 5454-5528), its upper half at
`T₀ = 3.061·10¹⁰`: RH up to `T₀` gives `S(x) ≤ (1 + 2.73·10⁻¹⁰)x + 0.135√x` for `x ≥ 2000`. DEEP:
the explicit formula for `ζ` (`lem:expfor`, Iwaniec–Kowalski §5.5 ex. 5; not in Mathlib), Rosser
1941 Lemma 17 and Ramaré–Saouter 2003 Lemma 2 (cited proofs: an owner question), and the numerics
`9.61114`, `κ₁ = 0.0463`. The RH input is supplied by the cited `PC.PlattTrudgian`. NOT cited. -/
def Crepe : Prop :=
  PC.ZetaRHTo 3.061e10 → ∀ x : ℝ, 2000 ≤ x → GS.sEta2 x ≤ (1 + 2.73e-10) * x + 0.135 * Real.sqrt x

/-- **`GS.Austeria` from the two cited checks, the two named wrappers and Platt–Trudgian,
PROVED.** Below `2000`: the windows directly, elsewhere the grid plus the inaccuracy bound. From
`2000`: `lem:crepe` with RH to `3.061·10¹⁰ ≤ 3·10¹²`, and `0.135√x ≤ 0.0448x` once `√x ≥ 44`. -/
theorem austeria_of_cited (z : PC.PlattTrudgian) (gr : AusteriaGridCited)
    (wi : AusteriaWindowCited) (lp : AusteriaLip) (cr : Crepe) : GS.Austeria := by
  intro Y hY
  rcases lt_or_ge Y 2000 with h | h
  · by_cases hw : Y ∈ austW
    · exact wi Y hw
    · obtain ⟨k, hk, hs⟩ := gr Y hY h hw
      have := lp Y hY k hk
      linarith
  · have hz : PC.ZetaRHTo 3.061e10 := PC.zetaRHTo_mono (T := 3 * 10 ^ 12) (by norm_num) z
    have hc := cr hz Y h
    have hs44 : (44 : ℝ) ≤ Real.sqrt Y := by
      have h1 : Real.sqrt (44 ^ 2) ≤ Real.sqrt Y := Real.sqrt_le_sqrt (by nlinarith)
      rwa [Real.sqrt_sq (by norm_num)] at h1
    have hYY : Real.sqrt Y * Real.sqrt Y = Y := Real.mul_self_sqrt (by linarith)
    have h0 : 0 ≤ Real.sqrt Y := Real.sqrt_nonneg Y
    have h1 : 0.135 * Real.sqrt Y ≤ 0.0448 * Y := by nlinarith
    linarith

/-! ## (4) `prop:espagn` -/

/-- `∑_{p ∣ q} log p / p`. -/
noncomputable def sumLogP (q : ℕ) : ℝ := ∑ p ∈ q.primeFactors, Real.log p / p

/-- `ω(ρ)` at `ρ = 0.6`, `Q₀,min = 10⁵`, `c₊ = 1.36` (`ternvin.tex` 2915-2917). -/
noncomputable def omegaE : ℝ := (Real.log 100000 + 1.36) / (Real.log 100000 / 0.6 + CY.cE)

/-- `c_Δ = c₊ − c_E` (2926). -/
noncomputable def cDeltaE : ℝ := 1.36 - CY.cE

/-- `κ(q) = (1 − ω)(log q − ∑_{p∣q} log p/p) + c_Δ` (2995-2997). -/
noncomputable def kappaE (q : ℕ) : ℝ := (1 - omegaE) * (Real.log q - sumLogP q) + cDeltaE

/-- `β_ρ = ω(ρ)/20000^{1/3}` (3009). -/
noncomputable def betaE : ℝ := omegaE / (20000 : ℝ) ^ ((1 : ℝ) / 3)

/-- `λ(q) = ((q/φ(q))·7.284(1 + β)f₁(q)/κ(q))³` (`eq:sosor`, 3012-3015). -/
noncomputable def lambdaE (q : ℕ) : ℝ :=
  ((q : ℝ) / (q.totient : ℝ) * (7.284 * (1 + betaE) * CY.f1 q / kappaE q)) ^ 3

/-- `τ = (1 − ρ)e^{−γ}` at `ρ = 0.6` (2968). -/
noncomputable def tauE : ℝ := (1 - 0.6) * Real.exp (-Real.eulerMascheroniConstant)

/-- `c(σ) = exp(e^{−γ}(σ − σ²/5.248 − 1.172))` (`lem:paniz`, 2822-2823). -/
noncomputable def cSig (σ : ℝ) : ℝ :=
  Real.exp (Real.exp (-Real.eulerMascheroniConstant) * (σ - σ ^ 2 / 5.248 - 1.172))

/-- `c_{ρ,2} = exp((1.4709 − c_E) + ω(c_E − 1.312) − c_Δ)` (2951). -/
noncomputable def cRho2 : ℝ := Real.exp ((1.4709 - CY.cE) + omegaE * (CY.cE - 1.312) - cDeltaE)

/-- `ϖ₀(q)` (2977-2984) at `ρ = 0.6`. -/
noncomputable def varpi0 (q : ℝ) : ℝ :=
  if Real.log q + 1 < cSig 1.36 * q ^ tauE then
    (cSig 1.36 * q ^ tauE - Real.log q / (cSig 1.36 * q ^ tauE - Real.log q) ^ (tauE / (1 - tauE)))
      ^ (1 / (1 - tauE))
  else 0

/-- `ϖ(q) = max(ϖ₀(q), c(c₊)Q₀,min^τ − log q, Q₀,min/(c_{ρ,2}q)^{1/(1−ω)})` (`eq:armor`,
2972-2975). -/
noncomputable def varpiE (q : ℕ) : ℝ :=
  max (varpi0 q) (max (cSig 1.36 * (100000 : ℝ) ^ tauE - Real.log q)
    (100000 / (cRho2 * q) ^ (1 / (1 - omegaE))))

/-- `err_{q,R} = G_q(R) − (φ(q)/q)(log R + c_E + ∑_{p∣q} log p/p)` (`eq:mero`, 2892-2894). -/
noncomputable def errE (q : ℕ) (R : ℝ) : ℝ :=
  gQ q R - (q.totient : ℝ) / q * (Real.log R + CY.cE + sumLogP q)

/-- **CITED computer check — the finite check of `prop:espagn`** (`ternvin.tex` 3273-3301;
statement 2870-2881; book arXiv:1501.05438 `l2normls.tex` 976-1000): for every `q < 3.3·10⁹`, and
every `3.3·10⁹ ≤ q < 2.2·10¹⁰` with `210 ∣ q`, and every INTEGER `R ∈ [ϖ(q), λ(q))`,
`eq:luce` with `err_{q,tR}` bounded by `eq:agammen` at `t = 20000`:
`err_{q,R} + ω·7.284(20000R)^{−1/3}f₁(q) ≤ (φ(q)/q)κ(q)`. Parameters his: `ρ = 0.6` (the worst
case; the check at `0.6` dominates every `ρ ≤ 0.6`, which is part of `EspagnRed`),
`Q₀,min = 10⁵`, `c₊ = 1.36`, `c_E = CY.cE` exact. Where his text leaves a choice open this is the
WEAKEST reading: exact `ω(0.6)`, `β(0.6)` rather than the rounded-up `0.627312`, `0.023111`, and
the `tR`-term per `R` rather than at `ϖ(q)`. Non-vacuous: at `q = 1` the range is
`[71734, 2.008·10⁷)` (`scratchpad/hcite/espagn_num.py`), and a float64 evaluation of THIS
statement on every `q ≤ 3000` (`2.1·10⁷` pairs `(q, R)`) finds margin `≥ 0.0233`, at `q = 1`,
`R = 71935` (`scratchpad/hcite/espagn_check_num.py`): evidence the transcription is true and has
content, not a replication of his run. Written in C by Helfgott; every
floating-point operation in Platt's interval arithmetic; about two weeks on one 2010 core. No code
or output was published. Link: arXiv:1312.7748v2, proof of Prop. (espagn), "Computation" paragraph
and footnote. CITED computer check (owner directive 2026-09-30). -/
def EspagnCheckCited : Prop :=
  ∀ q : ℕ, 1 ≤ q → ((q : ℝ) < 3.3e9 ∨ ((q : ℝ) < 2.2e10 ∧ 210 ∣ q)) →
    ∀ R : ℕ, varpiE q ≤ R → (R : ℝ) < lambdaE q →
      errE q R + omegaE * (7.284 * (20000 * (R : ℝ)) ^ (-(1 : ℝ) / 3) * CY.f1 q) ≤
        (q.totient : ℝ) / q * kappaE q

/-- `∏_{p ∣ q ∨ p ≤ m} p/(p − 1)`. -/
noncomputable def suspProd (m q : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range (m + q + 1)).filter (fun p => p.Prime ∧ (p ∣ q ∨ p ≤ m)),
    (p : ℝ) / ((p : ℝ) - 1)

/-- **CITED computer check — `lem:suspiro` below `8.53`** (`ternvin.tex` 2758-2760; book
`l2normls.tex` 433-465): "We verify all choices of `m, q ≥ 1` with `m + log q ≤ 8.53`
computationally; the worst case is that of `m = 1`, `q = 6`." Integer `m` (the product depends on
`⌊m⌋`, so real `m` reduces to this, which is `EspagnRed`'s). Margin `6.4·10⁻⁶` at `(1, 6)`.
Link: arXiv:1312.7748v2, proof of Lemma (suspiro). CITED computer check (owner directive
2026-09-30). -/
def SuspiroSmallCited : Prop :=
  ∀ m q : ℕ, 1 ≤ m → 1 ≤ q → (m : ℝ) + Real.log q ≤ 8.53 →
    suspProd m q ≤
      Real.exp Real.eulerMascheroniConstant * (Real.log ((m : ℝ) + Real.log q) + 0.65771)

/-- `∏_{p ≤ x} p/(p − 1)`. -/
noncomputable def mertProd (x : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (p : ℝ) / ((p : ℝ) - 1)

/-- **CITED computer check** (`ternvin.tex` 3072-3077): "By [RS62 (3.30)] and a numerical
computation for `29 ≤ p₁ ≤ 43`, `∏_{p ≤ p₁} p/(p−1) < 1.90516 log p₁`." The computed range, at
the primes `p₁` (the product and the claim change only there). Margin `2.5·10⁻⁵` at `p₁ = 31`.
Link: arXiv:1312.7748v2, proof of Prop. (espagn). CITED computer check (owner directive
2026-09-30). -/
def ProdSmallCited : Prop :=
  ∀ p1 : ℕ, p1.Prime → 29 ≤ p1 → p1 ≤ 43 → mertProd p1 < 1.90516 * Real.log p1

/-- `∑_{p ≤ x} log(1 + p^{−2/3})`. -/
noncomputable def logSum (x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime, Real.log (1 + (p : ℝ) ^ (-(2 : ℝ) / 3))

/-- **CITED computer check** (`ternvin.tex` 3104-3107): "a direct computation for all `x` prime
between `29` and `10⁴` then confirms that `∑_{p ≤ x} log(1 + p^{−2/3}) ≤ 0.74914x^{1/3}`".
Margin `2.4·10⁻⁵` at `x = 31`. Link: arXiv:1312.7748v2, proof of Prop. (espagn). CITED computer
check (owner directive 2026-09-30). -/
def LogSumCited : Prop :=
  ∀ x : ℕ, x.Prime → 29 ≤ x → x ≤ 10000 → logSum x ≤ 0.74914 * (x : ℝ) ^ ((1 : ℝ) / 3)

/-- **CITED computer check, MISPRINTED in the source** (`ternvin.tex` 3100): printed "Since
`∑_{p ≤ 10⁴} log p ≤ 10.09062`", which is false (`θ(10⁴) = 9895.99`); the next line uses
`10.09062` as `∑_{p ≤ 10⁴} log(1 + p^{−2/3})`, whose value is `10.0906127`. Transcribed as the
evidently intended statement, flagged for the coordinator. Link: arXiv:1312.7748v2, proof of Prop.
(espagn). CITED computer check (owner directive 2026-09-30). -/
def LogSumTenKCited : Prop := logSum 10000 ≤ 10.09062

/-- **CITED computer check** (`ternvin.tex` 3108-3111): the denominator `6.62365` of
`∏_{p ≤ x} f₁(p) ≤ e^{0.74914x^{1/3}}/6.62365`, i.e.
`∏_{p ≤ 29}(1 + (p^{1/3} + p^{2/3})/(p(p−1))) ≥ 6.62365` (value `6.6236524`). Link:
arXiv:1312.7748v2, proof of Prop. (espagn). CITED computer check (owner directive 2026-09-30). -/
def F1ProdCited : Prop :=
  6.62365 ≤ ∏ p ∈ (Finset.range 30).filter Nat.Prime,
    (1 + ((p : ℝ) ^ ((1 : ℝ) / 3) + (p : ℝ) ^ ((2 : ℝ) / 3)) / ((p : ℝ) * ((p : ℝ) - 1)))

/-- `θ(x) = ∑_{p ≤ x} log p`. -/
noncomputable def thetaN (x : ℕ) : ℝ := ∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime, Real.log p

/-- **CITED computer check** (`ternvin.tex` 3160-3162): "By [RS62 (3.16)] and a computation for
`31 ≤ q < 200`, we know that `log q ≥ ∏_{p ≤ p₁} log p ≥ 0.8009p₁`" (the `∏` is a misprint for
`∑`). The computed part at the primes `p₁ ∈ [31, 200)`: `θ(p₁) ≥ 0.8009p₁` (at non-primes it is
false, e.g. `t = 36`). Margin `0.002` at `37`. Link: arXiv:1312.7748v2, proof of Prop. (espagn).
CITED computer check (owner directive 2026-09-30). -/
def ThetaSmallCited : Prop :=
  ∀ p1 : ℕ, p1.Prime → 31 ≤ p1 → p1 < 200 → 0.8009 * (p1 : ℝ) ≤ thetaN p1

/-- The FIRST line of `eq:victo` (`ternvin.tex` 3120-3123), the bound on `λ(q)` for
`q < ∏_{p ≤ p₀} p`, `p₁` the prime before `p₀`. -/
noncomputable def victoFirst (p1 q : ℝ) : ℝ :=
  (1.90516 * Real.log p1 * (7.45235 * (Real.exp (0.74914 * p1 ^ ((1 : ℝ) / 3)) / 6.62365)) /
    (0.37268 * (Real.log q - Real.log p1) + 0.02741)) ^ 3

/-- The first line of the `210 ∤ q` variant (`ternvin.tex` 3190-3195). -/
noncomputable def hipowoFirst (p1 q : ℝ) : ℝ :=
  (1.633 * Real.log p1 * (7.45235 * (Real.exp (0.74914 * p1 ^ ((1 : ℝ) / 3)) / 7.44586)) /
    (0.37268 * (Real.log q - Real.log p1 + Real.log 7 / 7) + 0.02741)) ^ 3

/-- **CITED numerical evaluations** (`ternvin.tex` 3145-3148, 3199-3202): `ϖ₀(2.2·10¹⁰) ≥ 846.765`
against `λ ≤ 838.227`; `ϖ₀(3.3·10⁹) ≥ 477.465` against `λ ≤ 475.513`; and at
`q₀ = ∏_{p ≤ 31, p ≠ 7} p = 28651498590`, `ϖ₀(q₀) ≥ 916.322` against `λ ≤ 429.731`. The `λ`
values are those of the FIRST lines of `eq:victo` / its variant: **the second line of `eq:victo`
evaluates to `838.2279 > 838.227` at `2.2·10¹⁰`** (a rounding slip; the first line gives
`838.2246`), so the printed number is certified by the first line only. Link: arXiv:1312.7748v2,
proof of Prop. (espagn). CITED computer check (owner directive 2026-09-30). -/
def EspagnEvalCited : Prop :=
  846.765 ≤ varpi0 2.2e10 ∧ victoFirst 29 2.2e10 ≤ 838.227 ∧
  477.465 ≤ varpi0 3.3e9 ∧ hipowoFirst 29 3.3e9 ≤ 475.513 ∧
  916.322 ≤ varpi0 28651498590 ∧ hipowoFirst 31 28651498590 ≤ 429.731

/-- **The small cited checks inside `prop:espagn`'s reduction, bundled.** -/
def EspagnSmallCited : Prop :=
  SuspiroSmallCited ∧ ProdSmallCited ∧ LogSumCited ∧ LogSumTenKCited ∧ F1ProdCited ∧
    ThetaSmallCited ∧ EspagnEvalCited

/-- **CITED computer check — `eq:charpy` on the computed range** (`ternvin.tex` 2674-2681, footnote
2680-2681: Platt's interval arithmetic; book `l2normls.tex` 375-380): for `120 ≤ R ≤ 4·10⁷`,
`G(R) ≤ log R + 1.354`, and for `182 ≤ R ≤ 4·10⁷` also `log R + 1.312 ≤ G(R)`, with
`G = G₁ = PSieve.gQ 1`. Stated for real `R`, as printed. Link: arXiv:1312.7748v2, eq. (charpy)
and its footnote. CITED computer check (owner directive 2026-09-30). -/
def CharpyCited : Prop :=
  ∀ R : ℝ, 120 ≤ R → R ≤ 40000000 →
    gQ 1 R ≤ Real.log R + 1.354 ∧ (182 ≤ R → Real.log R + 1.312 ≤ gQ 1 R)

/-- **NAMED, NOT CITABLE — the gap in `eq:charpy`'s lower bound.** Helfgott: "This is true by
`eq:malito` for `R ≥ 4·10⁷`; we check it for `120 ≤ R ≤ 4·10⁷`." But `eq:malito` at `R = 4·10⁷`
gives only `log R + c_E − 7.284R^{−1/3} = log R + 1.31128`, below `1.312`; it reaches `1.312` from
`R ≥ 4.4322·10⁷`. So `(4·10⁷, 355³)` is covered by no printed argument and by no run (the book
arXiv:1501.05438 has the same text). It is a finite computation nobody ran: `~4.7·10⁶` values of
`G`. TRUE by a float64 sieve (margin `0.02058`, `scratchpad/hcite/charpy_gap.py`), which is
evidence, not a certificate. The owner may want it run rigorously; until then it is named. -/
def CharpyGap : Prop := ∀ R : ℝ, 40000000 < R → R < 44738875 → Real.log R + 1.312 ≤ gQ 1 R

/-- `eq:charpy`'s lower bound for all `R ≥ 182`, the form `prop:espagn`'s reduction consumes
(2934-2936, and `lem:trivo` 2792-2799). -/
def CharpyLo : Prop := ∀ R : ℝ, 182 ≤ R → Real.log R + 1.312 ≤ gQ 1 R

/-- `(355³)^{−1/3} = 1/355`. -/
theorem rpow_355 : (44738875 : ℝ) ^ (-(1 : ℝ) / 3) = 1 / 355 := by
  have h1 : (44738875 : ℝ) = (355 : ℝ) ^ ((3 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    norm_num
  rw [h1, ← Real.rpow_mul (by norm_num)]
  have h2 : ((3 : ℕ) : ℝ) * (-(1 : ℝ) / 3) = -1 := by norm_num
  rw [h2, Real.rpow_neg_one]
  norm_num

/-- **`CharpyLo`, PROVED** from the cited range `[182, 4·10⁷]`, the named gap `(4·10⁷, 355³)`, and
`eq:malito` at `d = 1` with `c_E ≥ 1.3325822` beyond: `1.3325822 − 7.284/355 = 1.3120639`. -/
theorem charpyLo_of (ch : CharpyCited) (gap : CharpyGap) (hm : CY.Malito)
    (hce : 1.3325822 ≤ CY.cE) : CharpyLo := by
  intro R hR
  rcases le_or_gt R 40000000 with h1 | h1
  · exact (ch R (by linarith) h1).2 hR
  rcases lt_or_ge R 44738875 with h2 | h2
  · exact gap R h1 h2
  · have hmal := hm 1 le_rfl R (by linarith)
    have hf1 : CY.f1 1 = 1 := by simp [CY.f1]
    simp only [Nat.totient_one, Nat.cast_one, div_one, Nat.primeFactors_one, Finset.sum_empty,
      add_zero, one_mul, hf1, mul_one] at hmal
    have hr : R ^ (-(1 : ℝ) / 3) ≤ 1 / 355 := by
      rw [← rpow_355]
      exact Real.rpow_le_rpow_of_nonpos (by norm_num) h2 (by norm_num)
    have hlo := (abs_le.mp hmal).1
    linarith

/-- **NAMED analytic wrapper — the reduction of `prop:espagn` to its finite checks**
(`ternvin.tex` 2891-3272): from `eq:mero` through `eq:elsyn`, `eq:karka` (the `ω(ρ)` trick),
`eq:miasmar`/`eq:koklo` (bounds on `s`), `lem:paniz` (via `lem:trivo`, `lem:suspiro`) for
`R ≤ ϖ(q)`, `eq:agammen`/`eq:sosor` for `R ≥ λ(q)`, the reduction of real `R` to integers, the
monotonicity in `ρ` that lets the check at `ρ = 0.6` cover every `ρ ≤ 0.6`, and the large-`q`
proof that `ϖ(q) > λ(q)` (`eq:victo`, `eq:drolo`, `eq:mutuso`, and the `210 ∤ q` variant).
Its inputs are the cited checks and the cited literature it names as hypotheses: `CY.CERange`
(RS62 (2.11), both bounds: `c_Δ ≥ 0.02741` needs the upper one), `CY.Malito`, `CY.Cante`
(Ramaré 1995 Lem. 3.4), `CharpyLo`. Its proof also uses RS62 (3.16), (3.24), (3.30), (3.32),
(3.42) and RS75 (5.1), cited PROOFS (an owner question), plus arithmetic. NOT cited.
**Two slips inside, both harmless to the implication:** "`q > 112000` is sufficient for
`ϖ(q) = ϖ₀(q)`" (3139-3141) is false at `ρ = 0.6` below `q ≈ 125887` (only `q ≥ 3.3·10⁹` uses
it), and the second line of `eq:victo` (see `EspagnEvalCited`). -/
def EspagnRed : Prop :=
  CY.CERange → CY.Malito → CY.Cante → CharpyLo → EspagnSmallCited → EspagnCheckCited → CY.Espagn

/-- **`CY.EspagnWin 1.36` from the cited checks, the named gap and the named reduction, PROVED**:
`CharpyLo` from `charpyLo_of`, `prop:espagn` from `EspagnRed`, and its window from
`CY.espagnWin_of_espagn`. -/
theorem espagnWin_of_cited (red : EspagnRed) (cer : CY.CERange) (hm : CY.Malito)
    (hc : CY.Cante) (ch : CharpyCited) (gap : CharpyGap) (sm : EspagnSmallCited)
    (chk : EspagnCheckCited) : CY.EspagnWin 1.36 :=
  CY.espagnWin_of_espagn (red cer hm hc (charpyLo_of ch gap hm cer.1) sm chk)

/-! ## (5) `MR.HelfMajR`: computations cited at Helfgott's statement, consumed by nothing yet

`MR.HelfMajR` itself is NOT derived (limit (a): flags F1, F2, F4 and N1 retyped Thm 1.4, Cor 1.3
and Prop 1.5). NOT transcribed, and why: the VNODE-LP integral `√226.844` (majarcs 3140-3158;
flag F6 changes the integrand, so his run does not certify the corrected one); `C₄ = 2013.18…`
(5791-5819; the printed interior integral `1152.70` is wrong, the true one is `1035.54`, so the
run's output is not a certificate even though the direction `C₄ ≤ 2013.18` is safe);
`|Mh|₁ ≤ 16.1939176` and `|(t+i)Mh|₁ ≤ 27.8622803` (closed-form arithmetic from `C₀ … C₄`, not a
run); Appendix A's extrema (flag F3: unverified that the repaired proof consumes the same ones). -/

/-- **CITED computer check — the VNODE-LP integral of Cor. 1.3** (`majarcs.tex` 4163-4168,
footnote 4164-4165: "rigorous integration from `1/4` to `1/2` and from `1/2` to `1`", VNODE-LP):
`∫_{1/4}^{1} exp(−0.1065(4π)²(w⁻² − 1)) η₂(w) dw ≤ 0.002866` (value `0.0028654`). Link:
arXiv:1305.2897v4, proof of Cor. (kolona), footnote. CITED computer check (owner directive
2026-09-30). -/
def CoprarIntCited : Prop :=
  ∫ w in (1 / 4 : ℝ)..1, Real.exp (-(0.1065 * (4 * Real.pi) ^ 2 * (1 / w ^ 2 - 1))) * HW.eta2 w ≤
    0.002866

/-- **CITED computer check — the VNODE-LP main-term integrals of Prop. 1.5** (`majarcs.tex`
4970-4976, 4986-4987): `∫₀^∞ η∘² = 0.64020599736635 + O(10⁻¹⁴)`,
`∫₀^∞ η∘² log t = −0.021094778698867 + O(10⁻¹⁵)`, and `|η∘ · log|₂ ≤ 0.214` ("evaluated
rigorously as above"). His `O(·)` is read as an explicit bound `|·| ≤`, the enclosure width of a
VNODE-LP run; a reader who takes `O` as an unspecified constant should read the first two
conjuncts as stronger than printed. (mpmath: `0.6402059973663522`, `−0.0210947786988672`,
`0.21387`.) Link: arXiv:1305.2897v4, proof of Prop. (malheur). CITED computer check (owner
directive 2026-09-30). -/
def MalMainCited : Prop :=
  |(∫ t in Set.Ioi (0 : ℝ), HW.etaCirc t ^ 2) - 0.64020599736635| ≤ 1e-14 ∧
    |(∫ t in Set.Ioi (0 : ℝ), HW.etaCirc t ^ 2 * Real.log t) - -0.021094778698867| ≤ 1e-15 ∧
      Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (HW.etaCirc t * Real.log t) ^ 2) ≤ 0.214

/-- `C_k = ∫₀^∞ |h^{(k)}(x)| x^{k−1} dx` (`majarcs.tex` 5693), for `k = 2, 3` where no
distributional term enters. -/
noncomputable def cK (k : ℕ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), |iteratedDeriv k HW.hFun x| * x ^ (k - 1)

/-- **CITED computer check — Appendix B, root isolation and the constants `C₂`, `C₃`, `|h'|_∞`**
(`majarcs.tex` 5745-5790, 6197-6202): roots of `H₂`, `H₃` found with SAGE `find_root` and
verified by sign changes in interval arithmetic; then `C₂ = 10.79195821037…`,
`C₃ = 75.1295251672…` (read as the printed digits truncated) and
`|h'|_∞ = |h'(α_{2,2})| ≤ 2.805820379671` (mpmath: `10.791958210373`, `75.129525167221`,
`2.8058203796708`). Link: arXiv:1305.2897v4, App. B (eq:nessu2, eq:nessu3, eq:morno). CITED
computer check (owner directive 2026-09-30). -/
def AppBCited : Prop :=
  (10.79195821037 ≤ cK 2 ∧ cK 2 ≤ 10.79195821038) ∧
    (75.1295251672 ≤ cK 3 ∧ cK 3 ≤ 75.1295251673) ∧ ∀ t : ℝ, |deriv HW.hFun t| ≤ 2.805820379671

/-- **CITED computer check — Appendix B's bisection maxima** (`majarcs.tex` 5914-5922: 40
iterations; 6236-6245: 30 and 32 iterations; Tucker's method on Platt's interval arithmetic):
`max_{t ∈ (0,5]} e^{−t²}t³|log t| = 0.14882234545…` (the bisection covers `[0,1]` and `[1,5]`),
`|η∘ log|_∞ ≤ 0.279491`, `|η◇ t log|_∞ ≤ 0.3811561` with `η◇(t) = te^{−t²/2}` (6027),
`|η∘/t|_∞ ≤ 1.08754396`, `|η∘ t|_∞ ≤ 1.06473476`. For `η◇ t log t` the bisection interval is not
printed, so the tail beyond it is bundled here (limit (b)). The wrapper that turned these into
sup norms of `η₊` (`eq:havana`) is broken (HELFGOTT-PROOF-MAP §2.4); the campaign proves its own
(`BL.supBounds_helf`). Link: arXiv:1305.2897v4, App. B. CITED computer check (owner directive
2026-09-30). -/
def AppBBisectCited : Prop :=
  (∀ t : ℝ, 0 < t → t ≤ 5 → Real.exp (-t ^ 2) * t ^ 3 * |Real.log t| ≤ 0.14882234546) ∧
    (∃ t : ℝ, 0 < t ∧ t ≤ 5 ∧ 0.14882234545 ≤ Real.exp (-t ^ 2) * t ^ 3 * |Real.log t|) ∧
      (∀ t : ℝ, 0 < t → |HW.etaCirc t * Real.log t| ≤ 0.279491) ∧
        (∀ t : ℝ, 0 < t → |t * Real.exp (-t ^ 2 / 2) * t * Real.log t| ≤ 0.3811561) ∧
          (∀ t : ℝ, 0 < t → |HW.etaCirc t / t| ≤ 1.08754396) ∧
            ∀ t : ℝ, 0 < t → |HW.etaCirc t * t| ≤ 1.06473476

/-- `υ(ρ) = √((1 + √(1 + ρ²))/2)` (`majarcs.tex` 709). -/
noncomputable def upsE (ρ : ℝ) : ℝ := Real.sqrt ((1 + Real.sqrt (1 + ρ ^ 2)) / 2)

/-- `E(ρ) = ½(arccos(1/υ(ρ)) − 2(υ(ρ) − 1)/ρ)` (`eq:cormo`, `majarcs.tex` 698-702). -/
noncomputable def eRho (ρ : ℝ) : ℝ := (Real.arccos (1 / upsE ρ) - 2 * (upsE ρ - 1) / ρ) / 2

/-- **CITED computer check — `cor:amanita1`'s bisection** (`majarcs.tex` 2540-2548): "`E(ρ) ≥
0.1065ρ` … for `ρ ∈ [1.19, 1.5]` by the bisection method (with 20 iterations)", and the single
evaluation `0.1598 ≤ E(1.5)` (margins `5.2·10⁻⁵`, `2.8·10⁻⁵`). Link: arXiv:1305.2897v4, proof of
Cor. (amanita1). CITED computer check (owner directive 2026-09-30). -/
def AmanitaBisectCited : Prop :=
  (∀ ρ : ℝ, 1.19 ≤ ρ → ρ ≤ 1.5 → 0.1065 * ρ ≤ eRho ρ) ∧ 0.1598 ≤ eRho 1.5

/-! ## (6) `OL.MinMainL`: computations cited at Helfgott's statement, consumed by nothing yet

`OL.MinMainL` is NOT derived (limit (a): the corrected `L` constant and the AM-GM `0.5 ↦ 0.811`;
`MinMainTotals` proves the typed pair unreachable along the book's route). NOT transcribed, and
why: `lem:octet` (the run stops at `2252.21`, its tail starts at `2252.51`); `lem:lujur` (printed
`< 0.7` is false, true `0.8548`; off the Main Theorem's path); `eq:charol` (misprinted, false as
printed); the book's `C_{x,t}/log t ≤ 0.08659` (false as printed; bypassed by `cXT_bounds`);
`eq:rala` (RS62 (3.23) with a "quick calculation": not a separable computation); `eq:passi`,
`eq:velib` and the `S < 16` part of `eq:corto` (they need `G_v = K_{v,1}(⌊S⌋) + K_{v,2}(⌊S⌋)/S`
of `eq:greco`, not transcribed this round); the second-case ratios `0.275964`, `0.23511` of the
book's `minarctotals.tex` 2095-2232 (15-term expressions, and fork C could not reproduce
`0.272652`; the campaign's loosened second case does not consume them). -/

/-- `g(t) = 4e(−t/4) − 4e(−t/2) + e(−t)` (`eq:ellib`, `minarcs.tex` 5716-5717). -/
noncomputable def wollG (t : ℝ) : ℂ :=
  4 * Principia.Common.Goldbach.e (-t / 4) - 4 * Principia.Common.Goldbach.e (-t / 2) +
    Principia.Common.Goldbach.e (-t)

/-- **CITED computer check — `lem:wollust`** (`minarcs.tex` 5697-5747; book `normfour.tex`
8-58): `|4e(−t/4) − 4e(−t/2) + e(−t)| ≤ 7.87052` for every real `t` (true max `7.8705102`). The
grid (spacing `√(8ε/9π²)`, `ε = 10⁻⁶`) is not printed, so the interpolation step `eq:elek1` is
bundled with the run (limit (b)). Link: arXiv:1205.5252, Lemma (wollust). CITED computer check
(owner directive 2026-09-30). -/
def WollustCited : Prop := ∀ t : ℝ, ‖wollG t‖ ≤ 7.87052

open Classical in
/-- `f = η₂'' − 4(4δ_{1/4} − 4δ_{1/2} + δ₁)` (`minarcs.tex` 5770-5775). -/
noncomputable def cameloF (x : ℝ) : ℝ :=
  if 1 / 4 ≤ x ∧ x < 1 / 2 then -4 / x ^ 2 else if 1 / 2 ≤ x ∧ x < 1 then 4 / x ^ 2 else 0

/-- `f̂(t) = ∫ f(x)e(−xt) dx`, Helfgott's normalisation. -/
noncomputable def cameloFHat (t : ℝ) : ℂ :=
  ∫ x in (1 / 4 : ℝ)..1, (cameloF x : ℂ) * Principia.Common.Goldbach.e (-(x * t))

/-- **CITED computer check — `lem:camelo`'s grid** (`minarcs.tex` 5786-5806, footnote 5798-5801:
Platt's interval arithmetic; book `normfour.tex` 60-110): `|4g + f̂|` at the endpoints of
`[0, 655)` cut into intervals of length `δ₁ = 0.001`, with `f̂` by Simpson's rule; "the largest
value … is `31.52065…`, with an error term of at most `4.5·10⁻⁵`". So at every grid point
`t = j/1000 ≤ 655`: `|4g(t) + f̂(t)| ≤ 31.52066 + 4.5·10⁻⁵`. The interpolation (`≤ 0.000237`) and
the tail `|t| ≥ 655` are analysis. Link: arXiv:1205.5252, Lemma (camelo). CITED computer check
(owner directive 2026-09-30). -/
def CameloGridCited : Prop :=
  ∀ j : ℕ, j ≤ 655000 →
    ‖4 * wollG ((j : ℝ) / 1000) + cameloFHat ((j : ℝ) / 1000)‖ ≤ 31.52066 + 4.5e-5

/-- `g_v(x) = ∑_{r₁, r₂ ≤ x, (r₁, r₂) = 1, (r₁r₂, v) = 1} μ(r₁)μ(r₂)/(σ(r₁)σ(r₂))`
(`lem:yutto`, `minarcs.tex` 2856-2860). -/
noncomputable def gYutto (v : ℕ) (x : ℝ) : ℝ :=
  ∑ r1 ∈ Finset.Icc 1 ⌊x⌋₊, ∑ r2 ∈ Finset.Icc 1 ⌊x⌋₊,
    if Nat.Coprime r1 r2 ∧ Nat.Coprime (r1 * r2) v then
      ((ArithmeticFunction.moebius r1 : ℤ) : ℝ) * ((ArithmeticFunction.moebius r2 : ℤ) : ℝ) /
        ((ArithmeticFunction.sigma 1 r1 : ℝ) * (ArithmeticFunction.sigma 1 r2 : ℝ))
    else 0

/-- **CITED computer check — `lem:yutto` for `x ≤ 10⁶`** (`minarcs.tex` 2878-2882: "The
statements for `x ≤ 10⁶` are proven by direct computation", Platt's interval arithmetic):
`|g₁(x)| ≤ 1/x` and `|g₂(x)| ≤ 2.1/x` for `33 ≤ x ≤ 10⁶`. Link: arXiv:1205.5252, Lemma (yutto).
CITED computer check (owner directive 2026-09-30). -/
def YuttoSmallCited : Prop :=
  ∀ x : ℝ, 33 ≤ x → x ≤ 1000000 → |gYutto 1 x| ≤ 1 / x ∧ |gYutto 2 x| ≤ 2.1 / x

/-- `∑_{n ≤ x} μ(n)/n`. -/
noncomputable def mertF (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.moebius n : ℤ) : ℝ) / n

/-- **CITED computer check — `eq:ramare`** (`minarcs.tex` 678-697, Platt's interval arithmetic):
`|∑_{n ≤ x} μ(n)/n| ≤ √(2/x)` for all real `0 < x ≤ 10¹²`; the recorded check datum
`5.42625·10⁻⁸ ≤ ∑_{n ≤ 10¹²} μ(n)/n ≤ 5.42898·10⁻⁸`; and `≤ 1/(2√x)` for
`3 ≤ x ≤ 7727068587`. Link: arXiv:1205.5252, eq. (ramare). CITED computer check (owner directive
2026-09-30). -/
def RamareCited : Prop :=
  (∀ x : ℝ, 0 < x → x ≤ 1e12 → |mertF x| ≤ Real.sqrt (2 / x)) ∧
    (5.42625e-8 ≤ mertF 1e12 ∧ mertF 1e12 ≤ 5.42898e-8) ∧
      ∀ x : ℝ, 3 ≤ x → x ≤ 7727068587 → |mertF x| ≤ 1 / (2 * Real.sqrt x)

/-- **CITED computer check — the two-variable inequalities behind `eq:odmalicka`**
(`minarcs.tex` 2983-3001, footnote 2997-3001: QEPCAD). The case reduction to boundary cases is
analysis, but the reduced inequalities are not printed, so the printed inequality is cited as the
unit (limit (b)): for `0 < x ≤ y₁, y₂ < 1` with `y₁², y₂² ≤ x`,
`1 + y₁y₂/((1 − y₁ + x)(1 − y₂ + x)) ≤ (1 − x³)²(1 − x⁴)/((1 − y₁y₂)(1 − y₁y₂²)(1 − y₁²y₂))`.
Link: arXiv:1205.5252, eq. (odmalicka). CITED computer check (owner directive 2026-09-30). -/
def OdmalickaCited : Prop :=
  ∀ x y1 y2 : ℝ, 0 < x → x ≤ y1 → x ≤ y2 → y1 < 1 → y2 < 1 → y1 ^ 2 ≤ x → y2 ^ 2 ≤ x →
    1 + y1 * y2 / ((1 - y1 + x) * (1 - y2 + x)) ≤
      (1 - x ^ 3) ^ 2 * (1 - x ^ 4) / ((1 - y1 * y2) * (1 - y1 * y2 ^ 2) * (1 - y1 ^ 2 * y2))

/-- `(φ(v)/v)·½·∑_{m ≤ 10⁴} g_v(m) log(1 + 1/m)`. -/
noncomputable def cortoMain (v : ℕ) : ℝ :=
  (v.totient : ℝ) / v * (1 / 2) *
    ∑ m ∈ Finset.Icc (1 : ℕ) 10000, gYutto v (m : ℝ) * Real.log (1 + 1 / (m : ℝ))

/-- `c·∑_{m ≤ 10⁴} |g_v(m)|(5m² + 2m + 1)`. -/
noncomputable def cortoErr (v : ℕ) (c : ℝ) : ℝ :=
  c * ∑ m ∈ Finset.Icc (1 : ℕ) 10000, |gYutto v (m : ℝ)| * (5 * (m : ℝ) ^ 2 + 2 * (m : ℝ) + 1)

/-- **CITED computer check — the `C₀ = 10000` sums of `eq:corto`** (`minarcs.tex` 3251-3266):
`0.362482…` (`v = 1`), `0.360576…` (`v = 2`), and with `c_{1,0} = 1/6`, `c_{2,0} = 1/3`
(3232-3233) the error sums `≤ 6204066.5…`, `≤ 15911340.1…`. Link: arXiv:1205.5252, proof of
eq. (corto). CITED computer check (owner directive 2026-09-30). -/
def CortoC0Cited : Prop :=
  (0.362482 ≤ cortoMain 1 ∧ cortoMain 1 ≤ 0.362483) ∧
    (0.360576 ≤ cortoMain 2 ∧ cortoMain 2 ≤ 0.360577) ∧
      cortoErr 1 (1 / 6) ≤ 6204066.6 ∧ cortoErr 2 (1 / 3) ≤ 15911340.2

/-- `∑_{s ≤ S, (s,v) = 1} (1/s)∫_{1/2}^{1} g_v(uS/s) du`, the left side of `eq:corto`. -/
noncomputable def cortoLHS (v : ℕ) (S : ℝ) : ℝ :=
  ∑ s ∈ (Finset.Icc 1 ⌊S⌋₊).filter (fun s => Nat.Coprime s v),
    1 / (s : ℝ) * ∫ u in (1 / 2 : ℝ)..1, gYutto v (u * S / s)

/-- **CITED computer check — `eq:corto` below `10⁵`** (`minarcs.tex` 3283-3289): "It is easy to
check numerically that this implies that (corto) holds … also for `40 ≤ S < 100000` (if `v = 1`)
or `16 ≤ S < 100000` (if `v = 2`)." The computed object `G_v` is not transcribed, so the printed
consequence is cited (limit (b)). Link: arXiv:1205.5252, proof of eq. (corto). CITED computer
check (owner directive 2026-09-30). -/
def CortoSmallCited : Prop :=
  (∀ S : ℝ, 40 ≤ S → S < 100000 → cortoLHS 1 S ≤ 0.36393) ∧
    ∀ S : ℝ, 16 ≤ S → S < 100000 → cortoLHS 2 S ≤ 0.37273

/-- **CITED computer check — Montgomery–Vaughan Lemma 8 below `100`** (`minarcs.tex` 3524-3530):
"easily verifiable numerically for `2 ≤ R < 100`. (It suffices to verify this for `R` integer
with `r < R` instead of `r ≤ R`, as that is the worst case.)" So: integer `R ∈ [3, 100]`,
`∑_{r < R} (1 + r/R)⁻¹μ²(r)/φ(r) > log R + 0.25068` (`R = 2` covers no real `R ≥ 2`; margin
`1.1·10⁻⁶` at `R = 5`). Link: arXiv:1205.5252, proof of Lemma (kastor1)'s small range. CITED
computer check (owner directive 2026-09-30). -/
def MV8SmallCited : Prop :=
  ∀ R : ℕ, 3 ≤ R → R ≤ 100 →
    Real.log R + 0.25068 < ∑ r ∈ Finset.Ico 1 R,
      (1 + (r : ℝ) / R)⁻¹ * (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / (r.totient : ℝ))

/-- **CITED computer check — `eq:notung`** (`minarcs.tex` 4307-4312): "by numerical work for
`e ≤ T ≤ T₀`", `T₀ = e^{(1−2/2.3)^{−1}} = 2135.94…`:
`∫_e^T dt/√(t log t) ≤ 2.3√(T/log T)`. Link: arXiv:1205.5252, eq. (notung). CITED computer check
(owner directive 2026-09-30). -/
def NotungCited : Prop :=
  ∀ T : ℝ, Real.exp 1 ≤ T → T ≤ 2135.94 →
    ∫ t in (Real.exp 1)..T, 1 / Real.sqrt (t * Real.log t) ≤ 2.3 * Real.sqrt (T / Real.log T)

/-- **CITED computer check — `eq:kast`** (`minarcs.tex` 745-751): "for `117 ≤ y < 2·758699` by
direct computation", `∑_{y/2 < p ≤ y} (log p)² ≤ ½ y log y`. Link: arXiv:1205.5252, eq. (kast).
CITED computer check (owner directive 2026-09-30). -/
def KastCited : Prop :=
  ∀ y : ℝ, 117 ≤ y → y < 2 * 758699 →
    ∑ p ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun p : ℕ => p.Prime ∧ y / 2 < (p : ℝ)),
        Real.log p ^ 2 ≤
      1 / 2 * y * Real.log y

/-- `∑_{n ≤ y} Λ(n) w(n)`. -/
noncomputable def lamSum (y : ℝ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n * w n

/-- **CITED computer checks — the `Λ` inputs of `minarcs.tex` 700-743, their computed ranges**:
`eq:ralobio` "a numerical verification for `x ≤ 1000`" (`∑ Λ(n)/n ≥ log x − log(3/√2)`, tight as
`x → 3⁻`); `eq:trado1` "supplemented by a computation for `2·10⁶ ≤ V ≤ 4·10⁶`" (`ψ(V) ≤ 1.0004V`);
`eq:chronop` "a computation for `663 < y ≤ 200000`" (`∑ Λ(n)n < 1.03884y²/2`); `eq:nicro`
"computations for small `y < 10⁷`", read on `(1.6·10⁶, 10⁷)` (`∑ Λ(n)n < 1.0008y²/2`). The
analytic halves (RS62 (3.21), Ramaré–Rumely's table, partial summation) are not cited here.
Link: arXiv:1205.5252, §(Λ bounds). CITED computer checks (owner directive 2026-09-30). -/
def LambdaSmallCited : Prop :=
  (∀ x : ℝ, 1 ≤ x → x ≤ 1000 →
      Real.log x - Real.log (3 / Real.sqrt 2) ≤ lamSum x fun n => 1 / (n : ℝ)) ∧
    (∀ V : ℝ, 2e6 ≤ V → V ≤ 4e6 → lamSum V (fun _ => 1) ≤ 1.0004 * V) ∧
      (∀ y : ℝ, 663 < y → y ≤ 200000 → lamSum y (fun n => (n : ℝ)) < 1.03884 * y ^ 2 / 2) ∧
        ∀ y : ℝ, 1.6e6 < y → y < 1e7 → lamSum y (fun n => (n : ℝ)) < 1.0008 * y ^ 2 / 2

end Principia.Common.TernaryGoldbach.HC
