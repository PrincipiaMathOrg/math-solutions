/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.BogusEta2C
import Principia.Common.TernaryGoldbach.EsthelEta2K

set_option autoImplicit false

/-!
# `lem:bogus` CORRECTED (`eq:etoile`, `c₁`, `eq:esthel3`), spined to three links

Three defects of the printed `lem:bogus` (book `typeI.tex` 1496-1880) and its links
`MPBG.MainBogusEta2`, `MPBC.EsthelBogusEta2C`:

* **`eq:etoile` is false.** It bounds `∑_{p odd, p ∣ q, p^α ≤ V} (log p)p^α` by `V log q`; at
  `q = 3`, `V = 9` the left side is `3 log 3 + 9 log 3 = 12 log 3 > 9 log 3`. The geometric sum
  gives `(3/2)V log q` (`∑_{α ≤ a} p^α ≤ p^a·p/(p - 1) ≤ (3/2)V` for odd `p`). Hence
  `eq:cupcake3`'s last term `(U + 1)²V/(2x)·log q` becomes `(3/4)(U + 1)²V/x·log q`
  (`cupcake3C`), and `MainBogusEta2C` is `MPBG.MainBogusEta2` with it.
* **`c₁`.** `eq:esthel3` charges `T(m) ≤ x/2m + |η'|₁/2` (`MPB2.TromB`, the bound `eq:trompais`
  that `MPT.TrompaisEta2` delivers), i.e. `T(m) ≤ (x/2m)(1 + |η'|₁m/x)`: the factor is
  `MPc.c1 = 1 + |η'|₁D/x`, not the printed `c₁ = 1 + |η'|₁D/(2x)` (`MPG.c1b`).
* **`eq:gator1`/`eq:gator2`** weight each `lem:gotog` window `(jq + R, (j + 1)q + R]` by
  `log(jq + R)`, its BOTTOM end; `log m` increases, so that is not an upper bound. The
  `R = q/2` case is left to "it is easy to check".

**The corrected route.** `eq:esthel3` is split into its two branches:

* `EsthelBogusKD` (`|δ| ≤ 1/2c₂` or `UV ≤ Q₀/2`): `≤ log(UV)·eq:keks(UV)` -- `log m ≤ log UV`
  and `MPE2.esthelEta2K_holds`. **PROVED here** (`esthelBogusKD_holds`).
* `EsthelBogusED` (`|δ| ≥ 1/2c₂`): `≤ tvorogD`, the `eq:tvorog` shape re-derived from the
  `lem:bosta2` pieces with the windows weighted at their TOP end and telescoped against
  `G(t) = t log(t/e)` (`BogusEsthelE.lean`).

Both bounds still close `SecI2At` (`SecI2ArithD.lean`); the cost of the crude `eq:keks` branch is
`(2√(c₀c₁)/π)·UV/2 ≈ 730u⁴` of a `≈ 3000u⁴` margin.

```
 BogusEta2D ← TrompaisEta2, MainBogusEta2C, EsthelBogusKD (PROVED), EsthelBogusED
            (bogusEta2D_of)
```
All four links carry `Q₀ ≥ 16` (the hypothesis of `MPB2.EsthelEta2`; at the second choice
`Q₀ = x^{2/3}/(500√6)`).
-/

namespace Principia.Common.TernaryGoldbach.MPBD

open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc
  Principia.Common.TernaryGoldbach.MPG Principia.Common.TernaryGoldbach.MPB2
  Principia.Common.TernaryGoldbach.MPT Principia.Common.TernaryGoldbach.MPBG
  Principia.Common.TernaryGoldbach.MPBC

/-! ## (1) The corrected bounds -/

/-- **`eq:cupcake3` with `eq:etoile` CORRECTED**, `D = UV`: last term `(3/4)(U + 1)²V/x·log q`
(the printed `(U + 1)²V/(2x)·log q` rests on the false `eq:etoile`). -/
noncomputable def cupcake3C (x δ : ℝ) (q : ℕ) (U V : ℝ) : ℝ :=
  x / (2 * q) * capM (c0 / Real.pi ^ 2) δ * Real.log (V * q) +
    (1 / 4 - 1 / Real.pi ^ 2) * c0 *
      ((U * V) ^ 2 * Real.log V / (2 * q * x) + 3 * c4 / 2 * (U * V ^ 2 / x) +
        3 / 4 * ((U + 1) ^ 2 * V / x) * Real.log q)

/-- **The `|δ| ≥ 1/2c₂` branch of `eq:esthel3`, corrected**, `D = UV`, `K = x/(|δ|q)`,
`ε ∈ (0, 1]`: `(2√(c₀c₁)/π)(D log(D/e) + K/2 + (1 + ε)K(√(3 + 2ε)·log min(D, (3 + 2ε)K/2)
+ 2 log⁺(2D/K) + (log D/2)·log⁺(2D/K))) + 3c₁|δ|q·log D·(1 + ((1 + ε)/2ε)·log⁺(2D/K))
+ (35c₀c₂/3π²)·q·log D`, with `c₁ = MPc.c1 x D`. -/
noncomputable def tvorogD (x δ : ℝ) (q : ℕ) (U V ε : ℝ) : ℝ :=
  2 * Real.sqrt (c0 * c1 x (U * V)) / Real.pi *
      (U * V * Real.log (U * V / Real.exp 1) + x / (|δ| * q) / 2 +
        (1 + ε) * (x / (|δ| * q)) *
          (Real.sqrt (3 + 2 * ε) *
              Real.log (min (U * V) ((3 + 2 * ε) * (x / (|δ| * q)) / 2)) +
            2 * logp (2 * (U * V) / (x / (|δ| * q))) +
            Real.log (U * V) / 2 * logp (2 * (U * V) / (x / (|δ| * q))))) +
    3 * c1 x (U * V) * (|δ| * q) * Real.log (U * V) *
      (1 + (1 + ε) / (2 * ε) * logp (2 * (U * V) / (x / (|δ| * q)))) +
    35 * c0 * c2 / (3 * Real.pi ^ 2) * q * Real.log (U * V)

/-! ## (2) The links -/

/-- **Link [MainBogusEta2C] — the main term of `lem:bogus`, `eq:etoile` CORRECTED**: as
`MPBG.MainBogusEta2` (with `Q₀ ≥ 16`), bounded by `cupcake3C`. OPEN. -/
def MainBogusEta2C : Prop :=
  ∀ x α δ Q0 U V : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 → 2 * α = a / q + δ / x →
    |δ / x| ≤ 1 / (q * Q0) → (q : ℝ) ≤ Q0 → 16 ≤ Q0 → 2 * Real.sqrt x ≤ Q0 →
    Real.exp 1 ^ 2 * c2 / 2 ≤ x → 1 ≤ U → 1 ≤ V → U * V + 19 / 18 * Q0 ≤ x / 5.6 →
      ‖∑ d ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun d => q ∣ d ∧ (d : ℝ) ≤ mR x δ q (U * V)),
          ((cUV U V d * fOdd d : ℝ) : ℂ) * tmo x α d‖ ≤ cupcake3C x δ q U V

/-- **Link [EsthelBogusKD] — `eq:esthel3`, the `|δ| ≤ 1/2c₂` (or `UV ≤ Q₀/2`) branch**: for
every `T` obeying `eq:trompais`, `∑ (log d)T(d)` over the `d ≤ UV` other than (`q ∣ d` and
`d ≤ M`) is at most `log(UV)·eq:keks(UV)`. PROVED (`esthelBogusKD_holds`). -/
def EsthelBogusKD : Prop :=
  ∀ x α δ Q0 U V : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 → 2 * α = a / q + δ / x →
    |δ / x| ≤ 1 / (q * Q0) → (q : ℝ) ≤ Q0 → 16 ≤ Q0 → 1 ≤ U → 1 ≤ V → U * V ≤ x →
    ∀ T : ℕ → ℝ, TromB x α T → (|δ| ≤ 1 / (2 * c2) ∨ U * V ≤ Q0 / 2) →
      ∑ d ∈ (Finset.Ioc 0 ⌊U * V⌋₊).filter
          (fun d => ¬ (q ∣ d ∧ (d : ℝ) ≤ mR x δ q (U * V))), Real.log d * T d ≤
        Real.log (U * V) * keks x q (U * V)

/-- **Link [EsthelBogusED] — `eq:esthel3`, the `|δ| ≥ 1/2c₂` branch, corrected**: for every `T`
obeying `eq:trompais` and `ε ∈ (0, 1]`, the same weighted sum is at most `tvorogD`. -/
def EsthelBogusED : Prop :=
  ∀ x α δ Q0 U V : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 → 2 * α = a / q + δ / x →
    |δ / x| ≤ 1 / (q * Q0) → (q : ℝ) ≤ Q0 → 16 ≤ Q0 → 1 ≤ U → 1 ≤ V → U * V ≤ x →
    ∀ T : ℕ → ℝ, TromB x α T → 1 / (2 * c2) ≤ |δ| → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∑ d ∈ (Finset.Ioc 0 ⌊U * V⌋₊).filter
          (fun d => ¬ (q ∣ d ∧ (d : ℝ) ≤ mR x δ q (U * V))), Real.log d * T d ≤
        tvorogD x δ q U V ε

/-- **Link [BogusEta2D] — `lem:bogus` for `η₂`, CORRECTED**: under `lem:bogus`'s hypotheses
(with `Q₀ ≥ 16`), `|S_{I,2}| ≤ cupcake3C + log(UV)·eq:keks(UV)` if `|δ| ≤ 1/2c₂` or
`UV ≤ Q₀/2`, and `≤ cupcake3C + tvorogD(ε)` for `ε ∈ (0, 1]` if `|δ| ≥ 1/2c₂`. -/
def BogusEta2D : Prop :=
  ∀ x α δ Q0 U V : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 → 2 * α = a / q + δ / x →
    |δ / x| ≤ 1 / (q * Q0) → (q : ℝ) ≤ Q0 → 16 ≤ Q0 → 2 * Real.sqrt x ≤ Q0 →
    Real.exp 1 ^ 2 * c2 / 2 ≤ x → 1 ≤ U → 1 ≤ V → U * V + 19 / 18 * Q0 ≤ x / 5.6 →
      ((|δ| ≤ 1 / (2 * c2) ∨ U * V ≤ Q0 / 2) →
        ‖sI2 x α U V‖ ≤ cupcake3C x δ q U V + Real.log (U * V) * keks x q (U * V)) ∧
      (1 / (2 * c2) ≤ |δ| → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ‖sI2 x α U V‖ ≤ cupcake3C x δ q U V + tvorogD x δ q U V ε)

/-! ## (3) The composition, PROVED -/

/-- **`BogusEta2D` from its links, PROVED** (application, `M = mR`). -/
theorem bogusEta2D_of (h1 : TrompaisEta2) (h2 : MainBogusEta2C) (hk : EsthelBogusKD)
    (he : EsthelBogusED) : BogusEta2D := by
  intro x α δ Q0 U V a q hq hg h2α hδ hqQ h16 hsq hx hU hV hUV
  have hx0 := x_pos_of x hx
  have hT : TromB x α (fun d => ‖tmo x α d‖) := fun d hd => ⟨norm_nonneg _, h1 x α hx0 d hd⟩
  have hmain := h2 x α δ Q0 U V a q hq hg h2α hδ hqQ h16 hsq hx hU hV hUV
  have hQ0 : 0 ≤ Q0 := by linarith
  have h56 : x / 5.6 ≤ x := by rw [div_le_iff₀ (by norm_num)]; nlinarith
  have hDx : U * V ≤ x := by linarith
  have hle := sI2_le x α U V (by linarith) (by linarith)
    (fun d => q ∣ d ∧ (d : ℝ) ≤ mR x δ q (U * V)) hDx
  exact ⟨fun hc => hle.trans (add_le_add hmain
      (hk x α δ Q0 U V a q hq hg h2α hδ hqQ h16 hU hV hDx _ hT hc)),
    fun hc ε hε hε1 => hle.trans (add_le_add hmain
      (he x α δ Q0 U V a q hq hg h2α hδ hqQ h16 hU hV hDx _ hT hc ε hε hε1))⟩

/-- **`BogusEta2D` on `TrompaisC`, `MainBogusEta2C`, `EsthelBogusKD`, `EsthelBogusED`.** -/
theorem bogusEta2D_of_C (h1 : TrompaisC) (h2 : MainBogusEta2C) (hk : EsthelBogusKD)
    (he : EsthelBogusED) : BogusEta2D :=
  bogusEta2D_of (trompaisEta2_of h1) h2 hk he

/-! ## (4) The `eq:keks` branch, PROVED -/

/-- **A weighted sum under a bounded weight**: `∑_S (log d)T(d) ≤ log D·∑_S T(d)` when every
`d ∈ S` has `1 ≤ d ≤ D` and `T ≥ 0` there. -/
theorem wsum_le (S : Finset ℕ) (T : ℕ → ℝ) (D : ℝ) (hS : ∀ d ∈ S, 1 ≤ d ∧ (d : ℝ) ≤ D)
    (hT : ∀ d ∈ S, 0 ≤ T d) :
    ∑ d ∈ S, Real.log d * T d ≤ Real.log D * ∑ d ∈ S, T d := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun d hd => ?_
  obtain ⟨h1, h2⟩ := hS d hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast h1
  exact mul_le_mul_of_nonneg_right (Real.log_le_log hd0 h2) (hT d hd)

/-- **`EsthelBogusKD`, PROVED** (`log d ≤ log UV`, then `MPE2.esthelEta2K_holds`). -/
theorem esthelBogusKD_holds : EsthelBogusKD := by
  intro x α δ Q0 U V a q hq hg h2 hδ hqQ h16 hU hV hDx T hT hbr
  have hD1 : 1 ≤ U * V := by nlinarith
  have hk := MPE2.esthelEta2K_holds x α δ Q0 (U * V) a q hq hg h2 hδ hqQ h16 hD1 hDx T hT hbr
  set S := (Finset.Ioc 0 ⌊U * V⌋₊).filter (fun d => ¬ (q ∣ d ∧ (d : ℝ) ≤ mR x δ q (U * V)))
    with hS_def
  have hmem : ∀ d ∈ S, 1 ≤ d ∧ (d : ℝ) ≤ U * V := by
    intro d hd
    have h := Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1
    refine ⟨by omega, ?_⟩
    have : (d : ℝ) ≤ ⌊U * V⌋₊ := by exact_mod_cast h.2
    linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ U * V)]
  have hw := wsum_le S T (U * V) hmem (fun d hd => (hT d (hmem d hd).1).1)
  exact hw.trans (mul_le_mul_of_nonneg_left hk (Real.log_nonneg hD1))

end Principia.Common.TernaryGoldbach.MPBD
