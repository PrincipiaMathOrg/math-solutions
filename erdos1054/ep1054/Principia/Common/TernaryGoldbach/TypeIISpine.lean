/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MinPieces
import Principia.Common.TernaryGoldbach.EBoundRS
import Principia.Common.TernaryGoldbach.HelfgottCited

set_option autoImplicit false

/-!
# The three Type II links `MPc.Vinland1At`, `MPc.EriksagaAt`, `MPc.SecIIAt`, spined

All three bound `|S_{II}|` (`MT.sII`) and all three are proved, in the book, by ONE argument
(`typeII.tex` 1-146, 813-837, 1193-1323; `minarctotals.tex` 464-1040), run at three parameter
choices. This file names its pieces on CONCRETE Lean objects and proves the three links from them.

```
 Vinland1At ┐            SecInt     eq:bycaus + Cauchy-Schwarz: |S_II| ≤ 4∫_V^{x/U} (√(S₁S₂) +
 EriksagaAt ├─ ← ────── √(S₁S₃)) dW/W, for the objects s1, s2, s3 below          (ELEMENTARY)
 SecIIAt    ┘            Menson2    eq:menson2 + eq:velib + eq:demimond (lem:monro, lem:yutto,
                                    eq:corto)                                            (DEEP)
                         Kraken     prop:kraken, all five bounds (lem:ogor, lem:kastor2: large
                                    sieve, Montgomery's inequality, MV weighted LS, MV Lem 8) (DEEP)
                         immer      eq:immer ← HC.KastCited + KastLarge                  PROVED
                         s3_le      eq:negli ← EB.RS62Thm13                              PROVED
                         Vin1Calc / ErikCalc / SecIICalc  the integral calculus of
                                    minarctotals 525-1040 (+ 1977-2235 for SecII), over ABSTRACT
                                    functions obeying the pointwise bounds              (ANALYSIS)
 vinland1At_of, eriksagaAt_of, secIIAt_of : PROVED (application + side conditions)
```

The `…Calc` links quantify over arbitrary `s1f s2f s3f : ℝ → ℝ` (and the `H` of `Menson2`), so
they are pure real analysis and attach by construction: the composition hands them exactly the
pointwise bounds the concrete objects are proved (or assumed) to satisfy. `eq:senorburns` has ZERO
main-term slack against `eq:eriksaga` (`MPII.iiArith`), so `Vin1Calc` and `ErikCalc` conclude the
book's displays `vin1` / `erik` exactly.

## Finding — the second choice uses `eq:garn1a` outside its hypothesis

`prop:kraken` is stated under `Q ≥ 3.5W`; of its five bounds only `eq:garn1a` uses it (through
`eq:pokor2b`, i.e. `lem:kastor1`'s `1/Q ≤ σ/(3.5qR²)`, which makes `3σ/(1 − σ/3.5) < 1`; with
`Q ≥ W` only, `3σ/(1 − σ) = 1.30 > 1` and the MV-Lemma-8 constant is lost). `Kraken` below states
`3.5W ≤ Q` on `eq:garn1a` ALONE, which is what the book's proof supports. At the FIRST choice
`Q = (3/4)x^{2/3} ≥ 3.5·x/U` for `x^{1/6} ≥ 24.3`, so `Vinland1At`/`EriksagaAt` are unaffected. At
the SECOND choice (`eq:elpozer`) `Q = x/U` while `W` runs up to `x/U`, so `Q ≥ 3.5W` FAILS on
`W ∈ (Q/3.5, Q]`, yet case (a) (`eq:vinland2`, `eq:hust`) applies `eq:garn1a` on all of
`[W₀, x/U]`. `SecIICalc` therefore only receives `eq:garn1a` for `3.5W ≤ Q`. Replacing it by
`eq:garn1b` (`ρ = q/Q ≤ 1/8`) on `(Q/3.5, Q]` costs, by a scoping estimate, about
`0.024·x^{5/6}(log x)^{3/2}` at `x = 3.4·10²³` (dominant term `√κ₁·x·√(log Q)·log 3.5/√q`,
`q > x^{1/3}/6`), inside the `0.34 − 0.275964` that `SecIIAt` was already loosened by; so the
LINK is believed true, but the book's derivation of it is not valid as printed.

## Other choices, recorded

* `Kraken` requires `W ≥ 117` (the book: `W ≥ 1`). Every use has `W ≥ V ≥ 2·10⁷`; the
  `R = 2` branch of `lem:kastor1` needs `R ≤ W'` (Montgomery's inequality for `r ≤ R` against
  `p > W'`), i.e. `W' ≥ 2`, which `W ≥ 1, W' ≥ W/2` does not give.
* `eq:procida2` is stated under the STRICT `x/4W + q < x/|δq|`: at equality the book's `min(1, ·/0)`
  reads `1`, Lean's `·/0 = 0` would read `0` and make the bound false.
* `Menson2` carries `22.6418 ≥ 1.27ζ(3/2)³ = 22.64177…` (implied by the book's form).
* `S₃` uses `ψ(W) − θ(W)` (Mathlib's `Chebyshev`), which bounds the non-prime part of the inner
  sum termwise; `eq:negli`'s `≤ 1.0171x + 2.0341W` is PROVED here (`s3_le`) from
  `EB.RS62Thm13` (the book drops the oddness of `m`; we keep it and land inside).
-/

namespace Principia.Common.TernaryGoldbach.T2S

open ArithmeticFunction Principia.Common.Goldbach MeasureTheory
open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc

/-! ## (1) The objects of `eq:costo`, `eq:honi`, `eq:negli` (at `v = 2`) -/

/-- **`c_m = ∑_{d ∣ m, d > U} μ(d)`** (`eq:adoucit`). -/
noncomputable def cU (U : ℝ) (m : ℕ) : ℝ :=
  ∑ d ∈ m.divisors.filter (fun d : ℕ => U < (d : ℝ)), ((μ d : ℤ) : ℝ)

/-- **The `m`-range** `{m odd : max(x/2W, A) < m ≤ x/W}` (`eq:costo`, `eq:honi`). -/
noncomputable def mSet (x A W : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊x / W⌋₊).filter (fun m => m % 2 = 1 ∧ max (x / (2 * W)) A < (m : ℝ))

/-- **`S₁(U, W) = ∑_{max(x/2W, U) < m ≤ x/W, m odd} c_m²`** (`eq:costo`, `eq:mahalobi`). -/
noncomputable def s1 (x U W : ℝ) : ℝ :=
  ∑ m ∈ mSet x U W, cU U m ^ 2

/-- **`∑_{W' < p ≤ W} (log p) e(αmp)`** (`eq:honi`). -/
noncomputable def pS (α W' W : ℝ) (m : ℕ) : ℂ :=
  ∑ p ∈ (Finset.Icc 1 ⌊W⌋₊).filter (fun p : ℕ => p.Prime ∧ W' < (p : ℝ)),
    ((Real.log p : ℝ) : ℂ) * e (((m * p : ℕ) : ℝ) * α)

/-- **`S₂(U', W', W) = ∑_{U' < m ≤ x/W, m odd} |∑_{W' < p ≤ W} (log p) e(αmp)|²`**
(`eq:honi`; for `U' ≥ x/2W` the range is exactly `U' < m ≤ x/W`). -/
noncomputable def s2 (x α U' W' W : ℝ) : ℝ :=
  ∑ m ∈ mSet x U' W, ‖pS α W' W m‖ ^ 2

/-- **`∑_{W' < p ≤ W} (log p)²`**. -/
noncomputable def pSq (W' W : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 ⌊W⌋₊).filter (fun p : ℕ => p.Prime ∧ W' < (p : ℝ)), Real.log p ^ 2

/-- **`S₃(W) = ∑_{x/2W < m ≤ x/W, m odd} (ψ(W) − θ(W))²`** (`eq:negli`): `ψ − θ` is the sum of
`Λ(n)` over the non-prime `n ≤ W`. -/
noncomputable def s3 (x W : ℝ) : ℝ :=
  ∑ _m ∈ mSet x 0 W, (Chebyshev.psi W - Chebyshev.theta W) ^ 2

theorem s1_nonneg (x U W : ℝ) : 0 ≤ s1 x U W :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem s2_nonneg (x α U' W' W : ℝ) : 0 ≤ s2 x α U' W' W :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem s3_nonneg (x W : ℝ) : 0 ≤ s3 x W :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **The integrand of `eq:secint`**, for abstract `S₁, S₂, S₃`. -/
noncomputable def secI (s1f s2f s3f : ℝ → ℝ) (W : ℝ) : ℝ :=
  (Real.sqrt (s1f W * s2f W) + Real.sqrt (s1f W * s3f W)) / W

/-! ## (2) The links -/

/-- **Link [SecInt] — `eq:bycaus` + Cauchy–Schwarz** (`typeII.tex` 59-146): with
`η₂ = η₁ ∗_M η₁`, `η₁ = 2·1_{[1/2,1]}`, the substitution `t = (m/x)W` gives
`S_{II} = 4∫_V^{x/U} ∑_m c_m ∑_{max(V,W/2) < n ≤ W, n odd} Λ(n)e(αmn) dW/W`; Cauchy–Schwarz over
`m`, splitting `n` into primes (`p > W' ≥ V ≥ 3` are odd) and non-primes (`|∑| ≤ ψ(W) − θ(W)`),
gives the integrand `√(S₁S₂) + √(S₁S₃)` at `U' = max(U, x/2W)`, `W' = max(V, W/2)`. ELEMENTARY
(Fubini over finite sums and Cauchy–Schwarz); OPEN. -/
def SecInt : Prop :=
  ∀ x α U V : ℝ, 0 < x → 0 < U → 3 ≤ V → V * U ≤ x →
    ‖sII x α U V‖ ≤ 4 * ∫ W in V..(x / U),
      secI (fun W => s1 x U W) (fun W => s2 x α (max U (x / (2 * W))) (max V (W / 2)) W)
        (fun W => s3 x W) W

/-- **`H₂` is admissible**: `0 ≤ H₂ ≤ 2/π²` (`eq:demimond`), integrable, and
`∫_1^T H₂(S) dS/S ≤ 0.15107 log T` (`eq:velib`, `v = 2`). -/
def HOk (H : ℝ → ℝ) : Prop :=
  (∀ s : ℝ, 1 ≤ s → 0 ≤ H s ∧ H s ≤ 2 / Real.pi ^ 2) ∧
    (∀ T : ℝ, 1 ≤ T → IntervalIntegrable H volume 1 T) ∧
      ∀ T : ℝ, 1 ≤ T → ∫ s in (1 : ℝ)..T, H s / s ≤ 0.15107 * Real.log T

/-- **The bound of `eq:menson2`**: `S ≤ (x/W)H(x/WU) + 22.6418·(x/W)^{3/2}/U`. -/
def S1Bd (H : ℝ → ℝ) (x U W S : ℝ) : Prop :=
  S ≤ x / W * H (x / (W * U)) + 22.6418 * (x / W) ^ ((3 : ℝ) / 2) / U

/-- **Link [Menson2] — `eq:menson2` with `eq:velib`, `eq:demimond`** (`typeII.tex` 147-837:
`eq:crusto`, `lem:monro`, `lem:yutto`, `eq:corto`, `eq:passi`; `1.27ζ(3/2)³ ≤ 22.6418`). One
`H₂` (Helfgott's `(4/π²)G₂` below `16`, `0.15107` above) serves every `x, U, W`. DEEP; OPEN. Its
computations are `HC.YuttoSmallCited`, `HC.RamareCited`, `HC.OdmalickaCited`, `HC.CortoC0Cited`,
`HC.CortoSmallCited`. -/
def Menson2 : Prop :=
  ∃ H : ℝ → ℝ, HOk H ∧
    ∀ x U W : ℝ, 1 ≤ U → 1 ≤ W → U * W ≤ x → S1Bd H x U W (s1 x U W)

/-- **The five bounds of `prop:kraken`** (`typeII.tex` 1193-1240) on a value `S`, with the prime
sum `∑_{W' < p ≤ W} (log p)²` replaced by a parameter `P`: `eq:garn1b`, `eq:garn1a` (under
`3.5W ≤ Q`, see the module note), `eq:gargamel`, `eq:procida2` (strict hypothesis),
`eq:procida3`. -/
def KrakenAt (x Q δ : ℝ) (q : ℕ) (W P S : ℝ) : Prop :=
  (∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → (q : ℝ) ≤ ρ * Q →
      S ≤ (max 1 (2 * ρ) * (x / (8 * q) + x / (2 * W)) + W / 2 + 2 * q) * P) ∧
    ((q : ℝ) < W / 2 → 3.5 * W ≤ Q →
      S ≤ (x / (4 * Nat.totient q) / Real.log (W / (2 * q)) +
        (q : ℝ) / Nat.totient q * W / Real.log (W / (2 * q))) * P) ∧
    (x / (4 * q) < W → S ≤ (W / 2 + q / (1 - x / (4 * W * q))) * P) ∧
    (δ ≠ 0 → x / (4 * W) + q < x / (|δ| * q) →
      S ≤ min 1 (2 * ((q : ℝ) / Nat.totient q) /
          Real.log (x / (|δ| * q) / (q + x / (4 * W)))) * (x / (|δ| * q) + W / 2) * P) ∧
    (δ ≠ 0 → ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 → (q : ℝ) ≤ ρ * Q →
      S ≤ (x / (|δ| * q) + W / 2 + x / (8 * (1 - ρ) * Q) + x / (4 * (1 - ρ) * W)) * P)

/-- **Link [Kraken] — `prop:kraken`** at `v = 2` (`typeII.tex` 1193-1323, from `lem:ogor`
858-950 and `lem:kastor2` 1143-1185, i.e. the sharp large sieve (Selberg; Montgomery–Vaughan
1973), Montgomery's inequality (IK Lem 7.15), Montgomery–Vaughan's weighted large sieve (1974,
(1.6)), MV Lemma 8 with `HC.MV8SmallCited`). Hypotheses as the book's, except `W ≥ 117` and
`3.5W ≤ Q` moved onto `eq:garn1a` (module note). DEEP; OPEN. -/
def Kraken : Prop :=
  ∀ x W W' U' Q α δ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 117 ≤ W → W ≤ x → W / 2 ≤ W' → x / (2 * W) ≤ U' →
    1 ≤ q → Int.gcd a q = 1 → 2 * α = a / q + δ / x → |δ / x| ≤ 1 / (q * Q) → (q : ℝ) ≤ Q →
      KrakenAt x Q δ q W (pSq W' W) (s2 x α U' W' W)

/-- **NAMED analytic link — `eq:kast` above the computed range** (`minarcs.tex` 745-751):
`∑_{y/2 < p ≤ y} (log p)² ≤ ½y log y` for `y ≥ 2·758699`, "by [Rosser–Schoenfeld 1975,
Cor. 2] applied to `x = y`, `y/2`, `2y/3`" (partial summation). OPEN. -/
def KastLarge : Prop :=
  ∀ y : ℝ, 2 * 758699 ≤ y →
    ∑ p ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun p : ℕ => p.Prime ∧ y / 2 < (p : ℝ)),
        Real.log p ^ 2 ≤ 1 / 2 * y * Real.log y

/-- **`eq:immer`, PROVED** from the cited `eq:kast` computation and `KastLarge`: for `W ≥ 117`,
`W' ≥ W/2`, `∑_{W' < p ≤ W} (log p)² ≤ ½W log W`. -/
theorem immer (hc : HC.KastCited) (hl : KastLarge) (W W' : ℝ) (hW : 117 ≤ W)
    (hW' : W / 2 ≤ W') : pSq W' W ≤ 1 / 2 * W * Real.log W := by
  have hsub : pSq W' W ≤
      ∑ p ∈ (Finset.Icc 1 ⌊W⌋₊).filter (fun p : ℕ => p.Prime ∧ W / 2 < (p : ℝ)),
        Real.log p ^ 2 := by
    unfold pSq
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1, lt_of_le_of_lt hW' hp.2.2⟩
  refine hsub.trans ?_
  rcases lt_or_ge W (2 * 758699) with h | h
  · exact hc W hW h
  · exact hl W h

/-- **At most `(b − a)/2 + 1` odd integers lie in `(a, b]`.** -/
theorem card_odd_le (a b : ℝ) (hab : a ≤ b) (s : Finset ℕ)
    (hs : ∀ m ∈ s, m % 2 = 1 ∧ a < (m : ℝ) ∧ (m : ℝ) ≤ b) :
    (s.card : ℝ) ≤ (b - a) / 2 + 1 := by
  rcases s.eq_empty_or_nonempty with h | hne
  · subst h
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith
  have hinj : Set.InjOn (fun m : ℕ => m / 2) (s : Set ℕ) := by
    intro m hm n hn h
    have h1 := (hs m hm).1
    have h2 := (hs n hn).1
    simp only at h
    omega
  have hcard : (s.image fun m : ℕ => m / 2).card = s.card := Finset.card_image_of_injOn hinj
  set t := s.image fun m : ℕ => m / 2 with ht
  have htne : t.Nonempty := hne.image _
  have hsub : t ⊆ Finset.Icc (t.min' htne) (t.max' htne) := fun j hj =>
    Finset.mem_Icc.mpr ⟨t.min'_le j hj, t.le_max' j hj⟩
  have hc : t.card ≤ t.max' htne + 1 - t.min' htne := by
    simpa using Finset.card_le_card hsub
  have hkK : t.min' htne ≤ t.max' htne := t.min'_le _ (t.max'_mem htne)
  obtain ⟨m, hm, hmk⟩ := Finset.mem_image.mp (t.min'_mem htne)
  obtain ⟨n, hn, hnK⟩ := Finset.mem_image.mp (t.max'_mem htne)
  have em : (m : ℝ) = 2 * (t.min' htne : ℝ) + 1 := by
    have h1 := (hs m hm).1
    have : m = 2 * t.min' htne + 1 := by omega
    exact_mod_cast this
  have en : (n : ℝ) = 2 * (t.max' htne : ℝ) + 1 := by
    have h1 := (hs n hn).1
    have : n = 2 * t.max' htne + 1 := by omega
    exact_mod_cast this
  have hma := (hs m hm).2.1
  have hnb := (hs n hn).2.2
  rw [← hcard]
  have hc' : (t.card : ℝ) ≤ (t.max' htne : ℝ) + 1 - (t.min' htne : ℝ) := by
    have : ((t.max' htne + 1 - t.min' htne : ℕ) : ℝ) =
        (t.max' htne : ℝ) + 1 - (t.min' htne : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [← this]
    exact_mod_cast hc
  linarith

/-- **`eq:negli`, PROVED** from `EB.RS62Thm13` (`ψ − θ < 1.42620√W`): for `x, W > 0`,
`S₃(W) ≤ 1.0171x + 2.0341W` (`#{m odd ∈ (x/2W, x/W]} ≤ x/4W + 1`, `1.4262² ≤ 2.03405`). -/
theorem s3_le (h13 : EB.RS62Thm13) (x W : ℝ) (hx : 0 < x) (hW : 0 < W) :
    s3 x W ≤ 1.0171 * x + 2.0341 * W := by
  have hcard : ((mSet x 0 W).card : ℝ) ≤ x / (4 * W) + 1 := by
    have h := card_odd_le (x / (2 * W)) (x / W)
      (div_le_div_of_nonneg_left hx.le hW (by linarith)) (mSet x 0 W) (by
        intro m hm
        rw [mSet, Finset.mem_filter, Finset.mem_Icc] at hm
        obtain ⟨⟨-, hmW⟩, hodd, hlt⟩ := hm
        refine ⟨hodd, lt_of_le_of_lt (le_max_left _ _) hlt, ?_⟩
        exact (Nat.cast_le.mpr hmW).trans (Nat.floor_le (div_pos hx hW).le))
    have e : (x / W - x / (2 * W)) / 2 = x / (4 * W) := by
      field_simp
      ring
    linarith
  have hpt := h13 W hW
  have hge : 0 ≤ Chebyshev.psi W - Chebyshev.theta W := sub_nonneg.mpr (Chebyshev.theta_le_psi W)
  have hsq : (Chebyshev.psi W - Chebyshev.theta W) ^ 2 ≤ 2.0340465 * W := by
    have h1 : (Chebyshev.psi W - Chebyshev.theta W) ^ 2 ≤ (1.42620 * Real.sqrt W) ^ 2 :=
      pow_le_pow_left₀ hge hpt.le 2
    rw [mul_pow, Real.sq_sqrt hW.le] at h1
    linarith
  unfold s3
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc0 : (0 : ℝ) ≤ (mSet x 0 W).card := Nat.cast_nonneg _
  calc ((mSet x 0 W).card : ℝ) * (Chebyshev.psi W - Chebyshev.theta W) ^ 2
      ≤ (x / (4 * W) + 1) * (2.0340465 * W) :=
        mul_le_mul hcard hsq (sq_nonneg _) (by positivity)
    _ = 0.508511625 * x + 2.0340465 * W := by
        field_simp
        ring
    _ ≤ 1.0171 * x + 2.0341 * W := by nlinarith

/-- **The pointwise inputs of the integral calculus on `[V, x/U]`**: `S₁ ≥ 0, S₂ ≥ 0, S₃ ≥ 0`,
`eq:menson2` for `S₁`, `prop:kraken` for `S₂` with `P = ½W log W` (`eq:immer`), `eq:negli`. -/
def PtBds (x U V Q δ : ℝ) (q : ℕ) (H s1f s2f s3f : ℝ → ℝ) : Prop :=
  ∀ W ∈ Set.Icc V (x / U), 0 ≤ s1f W ∧ 0 ≤ s2f W ∧ 0 ≤ s3f W ∧ S1Bd H x U W (s1f W) ∧
    KrakenAt x Q δ q W (1 / 2 * W * Real.log W) (s2f W) ∧ s3f W ≤ 1.0171 * x + 2.0341 * W

/-- **Link [Vin1Calc] — the integral calculus giving `eq:vinland1`** (`minarctotals.tex`
525-830, case `q ≤ V/2θ`, `θ = 27/8`, `W₀ = V`): `eq:crudo` + `eq:negli` → `κ₉x/√V`;
`eq:garn1a` split by `√(a+b) ≤ √a + √b`: `eq:vivaldi` with `eq:notung` (cited `HC.NotungCited` on
`[e, 2135.94]`, the derivative argument above) → the `x/√U` term, and `eq:soledad` with
`eq:menson2`, AM-GM in `β`, `eq:velib`, `eq:curious`, `eq:wofov` → the main term (`eq:valmont`).
Pure real analysis over abstract `s1f s2f s3f`; OPEN. -/
def Vin1Calc : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ δ : ℝ, ∀ q : ℕ, 1 ≤ q → |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3) →
    (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6 → ∀ H s1f s2f s3f : ℝ → ℝ, HOk H →
      PtBds Y (uA Y δ q) (vA Y) (3 / 4 * Y ^ ((2 : ℝ) / 3)) δ q H s1f s2f s3f →
        4 * ∫ W in (vA Y)..(Y / uA Y δ q), secI s1f s2f s3f W ≤ vin1 Y (uA Y δ q) (vA Y) q

/-- **Link [ErikCalc] — the integral calculus giving `eq:eriksaga`** (`minarctotals.tex`
843-1013, case `|δq| ≤ V/θ`, `W₀ = V`): `eq:procida2` → `eq:thislife` (`1 + x/2UQ ≤ 3/2`),
`eq:tort`; the `Wx/|δq|` part as in `eq:soledad`-`eq:valmont` (`eq:regxo1`), the `W²/2` part by
`eq:crudo` and `eq:filmot`, and `κ₉x/√V`. Pure real analysis; OPEN. -/
def ErikCalc : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ δ : ℝ, ∀ q : ℕ, 1 ≤ q → |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3) →
    (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6 → 8 ≤ |δ| → ∀ H s1f s2f s3f : ℝ → ℝ, HOk H →
      PtBds Y (uA Y δ q) (vA Y) (3 / 4 * Y ^ ((2 : ℝ) / 3)) δ q H s1f s2f s3f →
        4 * ∫ W in (vA Y)..(Y / uA Y δ q), secI s1f s2f s3f W ≤
          erik Y (uA Y δ q) (vA Y) (3 / 4 * Y ^ ((2 : ℝ) / 3)) δ q

/-- **Link [SecIICalc] — the integral calculus at the second choice** (`minarctotals.tex`
1977-2235: `eq:vinland2`/`eq:hust`/`eq:quan` in case (a) `q ≤ x/8U`, `eq:vinland3` for
`q > x/8U`, `eq:vinlandsaga`/`eq:bilal`/`eq:jadwi` in case (b), `θ = 4`), LOOSENED to `0.34`
as `MPc.SecIIAt`. `eq:garn1a` is available only where `3.5W ≤ Q = x/U` (module finding). Pure real
analysis plus the `0.275964` numeric; OPEN. -/
def SecIICalc : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ δ : ℝ, ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ q2 Y →
    |δ / Y| ≤ 1 / (q * q2 Y) →
    (Y ^ ((1 : ℝ) / 3) / 6 < q ∨ 4 / 3 * Y ^ ((1 : ℝ) / 3) < |δ| * q) →
      ∀ H s1f s2f s3f : ℝ → ℝ, HOk H → PtBds Y (u2 Y) (v2 Y) (q2 Y) δ q H s1f s2f s3f →
        4 * ∫ W in (v2 Y)..(Y / u2 Y), secI s1f s2f s3f W ≤
          0.34 * Y ^ ((5 : ℝ) / 6) * Real.log Y ^ ((3 : ℝ) / 2)

/-! ## (3) The compositions -/

/-- `P ≤ P'` lifts every `prop:kraken` bound (all five factors are `≥ 0` under their
hypotheses). -/
theorem krakenAt_mono (x Q δ : ℝ) (q : ℕ) (W P P' S : ℝ) (hx : 0 < x) (hW : 0 < W) (hq : 1 ≤ q)
    (hQ : 0 < Q) (hPP : P ≤ P') (hk : KrakenAt x Q δ q W P S) : KrakenAt x Q δ q W P' S := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hφ : (1 : ℝ) ≤ Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  obtain ⟨k1, k2, k3, k4, k5⟩ := hk
  refine ⟨fun ρ h0 h1 hρ => ?_, fun hqW h35 => ?_, fun hxW => ?_, fun hδ hc => ?_,
    fun hδ ρ h0 h1 hρ => ?_⟩
  · refine (k1 ρ h0 h1 hρ).trans (mul_le_mul_of_nonneg_left hPP ?_)
    have : (1 : ℝ) ≤ max 1 (2 * ρ) := le_max_left _ _
    positivity
  · refine (k2 hqW h35).trans (mul_le_mul_of_nonneg_left hPP ?_)
    have hl : 0 < Real.log (W / (2 * q)) :=
      Real.log_pos (by rw [lt_div_iff₀ (by positivity)]; linarith)
    positivity
  · refine (k3 hxW).trans (mul_le_mul_of_nonneg_left hPP ?_)
    have h1 : x / (4 * W * q) < 1 := by
      rw [div_lt_one (by positivity)]
      rw [div_lt_iff₀ (by positivity)] at hxW
      linarith
    have : 0 < 1 - x / (4 * W * q) := by linarith
    positivity
  · refine (k4 hδ hc).trans (mul_le_mul_of_nonneg_left hPP ?_)
    have hd : 0 < |δ| := abs_pos.mpr hδ
    have hr : 1 < x / (|δ| * q) / (q + x / (4 * W)) := by
      rw [one_lt_div (by positivity)]
      linarith
    have hl : 0 < Real.log (x / (|δ| * q) / (q + x / (4 * W))) := Real.log_pos hr
    have hm : 0 ≤ min 1 (2 * ((q : ℝ) / Nat.totient q) /
        Real.log (x / (|δ| * q) / (q + x / (4 * W)))) := le_min zero_le_one (by positivity)
    have : 0 ≤ x / (|δ| * q) + W / 2 := by positivity
    exact mul_nonneg hm this
  · refine (k5 hδ ρ h0 h1 hρ).trans (mul_le_mul_of_nonneg_left hPP ?_)
    have hd : 0 < |δ| := abs_pos.mpr hδ
    have h1' : 0 < 1 - ρ := by linarith
    positivity

/-- **The concrete objects obey `PtBds`**, PROVED from `Menson2`'s bound, `Kraken`, `eq:immer`
and `eq:negli`, for any `U ≥ 1`, `V ≥ 117` and a Diophantine approximation `2α = a/q + δ/x`
with `|δ/x| ≤ 1/(qQ)`, `q ≤ Q`. -/
theorem ptBds_of (H : ℝ → ℝ)
    (hm : ∀ x U W : ℝ, 1 ≤ U → 1 ≤ W → U * W ≤ x → S1Bd H x U W (s1 x U W))
    (hk : Kraken) (hc : HC.KastCited) (hl : KastLarge) (h13 : EB.RS62Thm13)
    (x α U V Q δ : ℝ) (a : ℤ) (q : ℕ) (hx : 0 < x) (hU : 1 ≤ U) (hV : 117 ≤ V) (hq : 1 ≤ q)
    (hg : Int.gcd a q = 1) (h2 : 2 * α = a / q + δ / x) (hδ : |δ / x| ≤ 1 / (q * Q))
    (hqQ : (q : ℝ) ≤ Q) :
    PtBds x U V Q δ q H (fun W => s1 x U W)
      (fun W => s2 x α (max U (x / (2 * W))) (max V (W / 2)) W) (fun W => s3 x W) := by
  intro W hW
  obtain ⟨hVW, hWU⟩ := hW
  have hW117 : 117 ≤ W := le_trans hV hVW
  have hW0 : 0 < W := by linarith
  have hUW : U * W ≤ x := by
    rw [le_div_iff₀ (by linarith)] at hWU
    linarith
  have hWx : W ≤ x := by nlinarith
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hQ : 0 < Q := by linarith
  refine ⟨s1_nonneg _ _ _, s2_nonneg _ _ _ _ _, s3_nonneg _ _, hm x U W hU (by linarith) hUW,
    ?_, s3_le h13 x W hx hW0⟩
  refine krakenAt_mono x Q δ q W _ _ _ hx hW0 hq hQ
    (immer hc hl W (max V (W / 2)) hW117 (le_max_right _ _)) ?_
  exact hk x W (max V (W / 2)) (max U (x / (2 * W))) Q α δ a q hW117 hWx (le_max_right _ _)
    (le_max_right _ _) hq hg h2 hδ hqQ

/-- `V = (9/2)x^{1/3} ≥ 117`. -/
theorem vA_ge (Y : ℝ) (hY : 3.4e23 ≤ Y) : 117 ≤ vA Y := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, e13, -, -⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  unfold vA
  rw [e13]
  nlinarith

/-- **`Vinland1At` from its links, PROVED** (application and the first choice's side
conditions). -/
theorem vinland1At_of (hs : SecInt) (hm : Menson2) (hk : Kraken) (hc : HC.KastCited)
    (hl : KastLarge) (h13 : EB.RS62Thm13) (hv : Vin1Calc) : Vinland1At := by
  intro Y hY α δ a q hq hg h2 hQ hδ hy
  obtain ⟨H, hH, hm⟩ := hm
  have hY0 : (0 : ℝ) < Y := by linarith
  have hdq := adm_dq Y δ q hY0 hq hδ
  have hU := uA_ge_one Y δ q hY hq hdq hy
  have hUV := uA_mul_vA Y δ q hY hq hdq hy
  have hV := vA_ge Y hY
  refine (hs Y α (uA Y δ q) (vA Y) hY0 (by linarith) (by linarith) (by linarith)).trans ?_
  exact hv Y hY δ q hq hdq hy H _ _ _ hH
    (ptBds_of H hm hk hc hl h13 Y α _ _ _ δ a q hY0 hU hV hq hg h2 hδ hQ)

/-- **`EriksagaAt` from its links, PROVED.** -/
theorem eriksagaAt_of (hs : SecInt) (hm : Menson2) (hk : Kraken) (hc : HC.KastCited)
    (hl : KastLarge) (h13 : EB.RS62Thm13) (he : ErikCalc) : EriksagaAt := by
  intro Y hY α δ a q hq hg h2 hQ hδ hy h8
  obtain ⟨H, hH, hm⟩ := hm
  have hY0 : (0 : ℝ) < Y := by linarith
  have hdq := adm_dq Y δ q hY0 hq hδ
  have hU := uA_ge_one Y δ q hY hq hdq hy
  have hUV := uA_mul_vA Y δ q hY hq hdq hy
  have hV := vA_ge Y hY
  refine (hs Y α (uA Y δ q) (vA Y) hY0 (by linarith) (by linarith) (by linarith)).trans ?_
  exact he Y hY δ q hq hdq hy h8 H _ _ _ hH
    (ptBds_of H hm hk hc hl h13 Y α _ _ _ δ a q hY0 hU hV hq hg h2 hδ hQ)

/-- The second choice: `U' ≥ 1`, `V' ≥ 117`, `V'U' ≤ x`, `Q' > 0`. -/
theorem second_facts (Y : ℝ) (hY : 3.4e23 ≤ Y) :
    1 ≤ u2 Y ∧ 117 ≤ v2 Y ∧ v2 Y * u2 Y ≤ Y ∧ 0 < q2 Y := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, e13, eY, -⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  have hs2 : (2 : ℝ) ≤ Real.sqrt 6 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hs3 : Real.sqrt 6 ≤ 3 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hu2 : 0 < u2 Y := by
    unfold u2
    positivity
  refine ⟨?_, ?_, ?_, div_pos hY0 hu2⟩
  · unfold u2
    rw [e13]
    nlinarith
  · unfold v2
    rw [e13]
    nlinarith
  · unfold u2 v2
    rw [e13]
    nth_rw 3 [eY]
    have h2 : (8000 : ℝ) ^ 2 ≤ (Y ^ ((1 : ℝ) / 6)) ^ 2 := pow_le_pow_left₀ (by norm_num) hu 2
    have h4 : 0 ≤ (Y ^ ((1 : ℝ) / 6)) ^ 4 := by positivity
    nlinarith

/-- **`SecIIAt` from its links, PROVED.** -/
theorem secIIAt_of (hs : SecInt) (hm : Menson2) (hk : Kraken) (hc : HC.KastCited)
    (hl : KastLarge) (h13 : EB.RS62Thm13) (h2c : SecIICalc) : SecIIAt := by
  intro Y hY α δ a q hadm
  obtain ⟨hq, hg, h2, hqQ, hδ, hcase⟩ := hadm
  obtain ⟨H, hH, hm⟩ := hm
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨hU, hV, hVU, -⟩ := second_facts Y hY
  refine (hs Y α (u2 Y) (v2 Y) hY0 (by linarith) (by linarith) hVU).trans ?_
  exact h2c Y hY δ q hq hqQ hδ hcase H _ _ _ hH
    (ptBds_of H hm hk hc hl h13 Y α _ _ _ δ a q hY0 hU hV hq hg h2 hδ hqQ)

end Principia.Common.TernaryGoldbach.T2S
