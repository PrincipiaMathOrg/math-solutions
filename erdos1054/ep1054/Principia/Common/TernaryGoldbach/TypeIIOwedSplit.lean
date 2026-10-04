/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIIErikCalcC
import Principia.Common.TernaryGoldbach.TypeIIKastLarge
import Principia.Common.TernaryGoldbach.TypeIIMenson2C

set_option autoImplicit false

/-!
# The owed Type II links, split: `T2S.Kraken` into its five bounds, `T2SC.SecIICalcC` into its
three cases, and the Type II triple assembled from what is left

```
 Kraken      ← Garn1b, Garn1a, Gargamel, Procida2, Procida3        (prop:kraken, one link each)
 SecIICalcC  ← SecIICaseA1 (y < q ≤ x/8U; book 0.2760 + erratum + garn1a fix, scoped ≤ 0.302)
               SecIICaseA2 (q > x/8U; book 0.10327)
               SecIICaseB  (q ≤ y, |δ|q > 8y; book 0.23511)          (minarctotals 1977-2235)
 KastLarge   PROVED from KLR.RS75Cor2 (TypeIIKastLarge)
 Menson2C    ← M2H.MonroFleming, M2H.GrottoTab, M2H.CortoLarge + HC.CortoSmallCited
               (its HOkC half PROVED, TypeIIMenson2C)
 typeII_of_owed : Vinland1AtC ∧ EriksagaAtC ∧ SecIIAt                                 PROVED
```

Each `Kraken` piece is the matching conjunct of `T2S.KrakenAt` (at `P = ∑(log p)²`,
`S = S₂`) under `Kraken`'s hypotheses, so the five statements are the book's five displays as
`KrakenAt` transcribes them, and recombine by construction. The `SecIICalcC` cases are the
book's case split at `θ = 4`, `y = x^{1/3}/6`: `q > y` with `q ≤ x/8U` (`eq:vinland2` → `eq:hust` → `eq:quan`), `q > x/8U`
(`eq:vinland3`), and `q ≤ y`, `|δ|q > 8y = (4/3)x^{1/3}` (`eq:vinlandsaga` → `eq:bilal` →
`eq:jadwi`; `|δ| > 8` follows). All three keep the conclusion `0.34x^{5/6}(log x)^{3/2}`.
-/

namespace Principia.Common.TernaryGoldbach.T2X

open MeasureTheory
open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc
open Principia.Common.TernaryGoldbach.T2S Principia.Common.TernaryGoldbach.T2SC

/-! ## (1) `prop:kraken`, one link per bound -/

/-- **Link [Garn1b] — `eq:garn1b`** (`typeII.tex` 1196-1200; `lem:ogor` with the sharp large
sieve): for `q ≤ ρQ`, `S₂ ≤ (max(1, 2ρ)(x/8q + x/2W) + W/2 + 2q)·∑(log p)²`. DEEP; OPEN. -/
def Garn1b : Prop :=
  ∀ x W W' U' Q α δ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 117 ≤ W → W ≤ x → W / 2 ≤ W' → x / (2 * W) ≤ U' →
    1 ≤ q → Int.gcd a q = 1 → 2 * α = a / q + δ / x → |δ / x| ≤ 1 / (q * Q) → (q : ℝ) ≤ Q →
      ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → (q : ℝ) ≤ ρ * Q →
        s2 x α U' W' W ≤ (max 1 (2 * ρ) * (x / (8 * q) + x / (2 * W)) + W / 2 + 2 * q) * pSq W' W

/-- **Link [Garn1a] — `eq:garn1a`** (`typeII.tex` 1201-1206; `lem:kastor1` via Montgomery's
inequality and MV Lemma 8, `HC.MV8SmallCited`), under `q < W/2` and `3.5W ≤ Q` (the
`TypeIISpine` finding). DEEP; OPEN. -/
def Garn1a : Prop :=
  ∀ x W W' U' Q α δ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 117 ≤ W → W ≤ x → W / 2 ≤ W' → x / (2 * W) ≤ U' →
    1 ≤ q → Int.gcd a q = 1 → 2 * α = a / q + δ / x → |δ / x| ≤ 1 / (q * Q) → (q : ℝ) ≤ Q →
      (q : ℝ) < W / 2 → 3.5 * W ≤ Q →
        s2 x α U' W' W ≤ (x / (4 * Nat.totient q) / Real.log (W / (2 * q)) +
          (q : ℝ) / Nat.totient q * W / Real.log (W / (2 * q))) * pSq W' W

/-- **Link [Gargamel] — `eq:gargamel`** (`typeII.tex` 1207-1211), for `W > x/4q`. DEEP;
OPEN. -/
def Gargamel : Prop :=
  ∀ x W W' U' Q α δ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 117 ≤ W → W ≤ x → W / 2 ≤ W' → x / (2 * W) ≤ U' →
    1 ≤ q → Int.gcd a q = 1 → 2 * α = a / q + δ / x → |δ / x| ≤ 1 / (q * Q) → (q : ℝ) ≤ Q →
      x / (4 * q) < W →
        s2 x α U' W' W ≤ (W / 2 + q / (1 - x / (4 * W * q))) * pSq W' W

/-- **Link [Procida2] — `eq:procida2`** (`typeII.tex` 1213-1226; `lem:kastor2`, the weighted
large sieve), for `δ ≠ 0` and the strict `x/4W + q < x/|δq|`. DEEP; OPEN. -/
def Procida2 : Prop :=
  ∀ x W W' U' Q α δ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 117 ≤ W → W ≤ x → W / 2 ≤ W' → x / (2 * W) ≤ U' →
    1 ≤ q → Int.gcd a q = 1 → 2 * α = a / q + δ / x → |δ / x| ≤ 1 / (q * Q) → (q : ℝ) ≤ Q →
      δ ≠ 0 → x / (4 * W) + q < x / (|δ| * q) →
        s2 x α U' W' W ≤ min 1 (2 * ((q : ℝ) / Nat.totient q) /
          Real.log (x / (|δ| * q) / (q + x / (4 * W)))) * (x / (|δ| * q) + W / 2) * pSq W' W

/-- **Link [Procida3] — `eq:procida3`** (`typeII.tex` 1227-1240), for `δ ≠ 0`, `q ≤ ρQ`,
`ρ < 1`. DEEP; OPEN. -/
def Procida3 : Prop :=
  ∀ x W W' U' Q α δ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 117 ≤ W → W ≤ x → W / 2 ≤ W' → x / (2 * W) ≤ U' →
    1 ≤ q → Int.gcd a q = 1 → 2 * α = a / q + δ / x → |δ / x| ≤ 1 / (q * Q) → (q : ℝ) ≤ Q →
      δ ≠ 0 → ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 → (q : ℝ) ≤ ρ * Q →
        s2 x α U' W' W ≤ (x / (|δ| * q) + W / 2 + x / (8 * (1 - ρ) * Q) +
          x / (4 * (1 - ρ) * W)) * pSq W' W

/-- **`T2S.Kraken` from its five bounds, PROVED.** -/
theorem kraken_of (h1 : Garn1b) (h2 : Garn1a) (h3 : Gargamel) (h4 : Procida2) (h5 : Procida3) :
    Kraken := by
  intro x W W' U' Q α δ a q hW hWx hW' hU' hq hg h2a hδ hqQ
  unfold KrakenAt
  exact ⟨h1 x W W' U' Q α δ a q hW hWx hW' hU' hq hg h2a hδ hqQ,
    h2 x W W' U' Q α δ a q hW hWx hW' hU' hq hg h2a hδ hqQ,
    h3 x W W' U' Q α δ a q hW hWx hW' hU' hq hg h2a hδ hqQ,
    h4 x W W' U' Q α δ a q hW hWx hW' hU' hq hg h2a hδ hqQ,
    h5 x W W' U' Q α δ a q hW hWx hW' hU' hq hg h2a hδ hqQ⟩

/-! ## (2) `SecIICalcC`, one link per case -/

/-- **Link [SecIICaseA1] — case (a), `y < q ≤ x/8U`** (`minarctotals.tex` 1977-2119:
`eq:vinland2` at `θ = 4` → `eq:hust` → `eq:quan`; book `0.275964`, `≤ 0.2779` after the
`eq:passi` erratum, plus `≈ 0.024` for `eq:garn1b` on `(Q/3.5, Q]`, scoped). OPEN. -/
def SecIICaseA1 : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ δ : ℝ, ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ q2 Y →
    |δ / Y| ≤ 1 / (q * q2 Y) → Y ^ ((1 : ℝ) / 3) / 6 < q → (q : ℝ) ≤ Y / (8 * u2 Y) →
      ∀ H s1f s2f s3f : ℝ → ℝ, HOkC H → PtBds Y (u2 Y) (v2 Y) (q2 Y) δ q H s1f s2f s3f →
        4 * ∫ W in (v2 Y)..(Y / u2 Y), secI s1f s2f s3f W ≤
          0.34 * Y ^ ((5 : ℝ) / 6) * Real.log Y ^ ((3 : ℝ) / 2)

/-- **Link [SecIICaseA2] — `q > x/8U`** (`minarctotals.tex` 2120-2150: `eq:vinland3`, maximal
at `q = Q`; book `0.10327`). OPEN. -/
def SecIICaseA2 : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ δ : ℝ, ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ q2 Y →
    |δ / Y| ≤ 1 / (q * q2 Y) → Y / (8 * u2 Y) < q →
      ∀ H s1f s2f s3f : ℝ → ℝ, HOkC H → PtBds Y (u2 Y) (v2 Y) (q2 Y) δ q H s1f s2f s3f →
        4 * ∫ W in (v2 Y)..(Y / u2 Y), secI s1f s2f s3f W ≤
          0.34 * Y ^ ((5 : ℝ) / 6) * Real.log Y ^ ((3 : ℝ) / 2)

/-- **Link [SecIICaseB] — case (b), `q ≤ y`, `|δ|q > 8y`** (`minarctotals.tex` 2152-2235:
`eq:vinlandsaga` → `eq:bilal` → `eq:jadwi`/`eq:asex`; book `0.23511`). OPEN. -/
def SecIICaseB : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ δ : ℝ, ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ q2 Y →
    |δ / Y| ≤ 1 / (q * q2 Y) → (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6 →
    4 / 3 * Y ^ ((1 : ℝ) / 3) < |δ| * q →
      ∀ H s1f s2f s3f : ℝ → ℝ, HOkC H → PtBds Y (u2 Y) (v2 Y) (q2 Y) δ q H s1f s2f s3f →
        4 * ∫ W in (v2 Y)..(Y / u2 Y), secI s1f s2f s3f W ≤
          0.34 * Y ^ ((5 : ℝ) / 6) * Real.log Y ^ ((3 : ℝ) / 2)

/-- **`T2SC.SecIICalcC` from its three cases, PROVED** (the split is exhaustive). -/
theorem secIICalcC_of (ha1 : SecIICaseA1) (ha2 : SecIICaseA2) (hb : SecIICaseB) :
    SecIICalcC := by
  intro Y hY δ q hq hqQ hδ hcase H s1f s2f s3f hH hpt
  rcases le_or_gt (q : ℝ) (Y ^ ((1 : ℝ) / 3) / 6) with hy | hy
  · have hb' : 4 / 3 * Y ^ ((1 : ℝ) / 3) < |δ| * q := by
      rcases hcase with h | h
      · exact absurd hy (not_le.mpr h)
      · exact h
    exact hb Y hY δ q hq hqQ hδ hy hb' H s1f s2f s3f hH hpt
  · rcases le_or_gt (q : ℝ) (Y / (8 * u2 Y)) with h8 | h8
    · exact ha1 Y hY δ q hq hqQ hδ hy h8 H s1f s2f s3f hH hpt
    · exact ha2 Y hY δ q hq hqQ hδ h8 H s1f s2f s3f hH hpt

/-! ## (3) The Type II triple from the owed links -/

/-- **`Vinland1AtC`, `EriksagaAtC`, `SecIIAt` from the owed links, PROVED**: `SecInt`,
`Vin1CalcC`, `ErikCalcC`, `KastLarge` and `HOkC H₂` are discharged; what remains is the five
`prop:kraken` bounds, the three `S₁` links of `M2H`, the three `SecIICalcC` cases, RS75 Cor. 2,
and the cited computations. -/
theorem typeII_of_owed (g1 : Garn1b) (g2 : Garn1a) (g3 : Gargamel) (g4 : Procida2)
    (g5 : Procida3) (mf : M2H.MonroFleming) (gt : M2H.GrottoTab) (cl : M2H.CortoLarge)
    (ha1 : SecIICaseA1) (ha2 : SecIICaseA2) (hb : SecIICaseB) (rs : KLR.RS75Cor2)
    (cs : HC.CortoSmallCited) (hc : HC.KastCited) (h13 : EB.RS62Thm13) (hn : HC.NotungCited) :
    Vinland1AtC ∧ EriksagaAtC ∧ SecIIAt := by
  have hm := M2H.menson2C_of_links mf gt cl cs
  have hk := kraken_of g1 g2 g3 g4 g5
  have hl := KLR.kastLarge_of_rs75 rs
  exact ⟨vinland1AtC_of_deep hm hk hc hl h13 hn, eriksagaAtC_of_deep hm hk hc hl h13,
    secIIAtC_of secInt_holds hm hk hc hl h13 (secIICalcC_of ha1 ha2 hb)⟩

end Principia.Common.TernaryGoldbach.T2X
