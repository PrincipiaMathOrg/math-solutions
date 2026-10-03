/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.SuspiroWrap
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

set_option autoImplicit false

/-!
# The edge hole `HX.EspagnEdge`, cut down by two ANALYTIC covers

`HX.EspagnEdge` asks for Helfgott's cited check (`HC.EspagnCheckCited`) at the one real point
`R = ϖ(q)`, for every checked `q` with non-integer `ϖ(q)`: a computation nobody ran. Here the
partial step `ϖ(q) < R < N(q) = ⌊ϖ(q)⌋ + 1` is covered ANALYTICALLY for every `q` satisfying one
of two explicit conditions, and what is left is the SMALLER named residue `EspagnEdgeRes` —
`EspagnEdge`'s own statement with the two covers' failures added as hypotheses
(`edgeRes_of_edge` shows it is implied by `EspagnEdge`).

## The two covers

* **`CoverB q` — `lem:paniz` reaches past `ϖ(q)`.** `ϖ(q)` is a LOWER bound for the edge of
  region (i) (`R + log q ≤ c(1.36)Q₀^τ`), got by iterating twice. If
  `R + log q ≤ c(1.36)(qR)^τ` holds at both `R = ϖ(q)` and `R = N(q)`, it holds on the whole
  step (`R ↦ c(qR)^τ − R` is concave: `Real.concaveOn_rpow`), and since `Q₀ = Rsq ≥ Rq` the step
  lies inside region (i) — the edge configuration cannot occur (`false_of_coverB`).
* **`CoverA q` — the slack `κ(q)` throws away.** `eq:luce → eq:karka` drops `(1 − ω)log s ≥ 0`
  (`HX.karka_of_luce`). On the step, `G_q(R) = G_q(N − 1) ≤ G_q(N)`, so the cited check at the
  INTEGER `N(q)` (or `eq:malito` if `N(q) ≥ λ(q)`) gives `eq:karka` at `R` as soon as
  `log(N/ϖ) + (q/φ)ω·7.284f₁((20000ϖ)^{−1/3} − (20000N)^{−1/3}) ≤ (1 − ω)·max(0, log(10⁵/(Nq)))`,
  because `s = Q₀/(Rq) ≥ 10⁵/(Nq)` (`karka_of_coverA`).

`espagn_of_links2` is `HX.espagn_of_links` with the edge branch discharged by the two covers and
`EspagnEdgeRes`; `espagnRed_of_links2` / `espagnRed_of_rs2` are the `HC.EspagnRed` wrappers.

## What the residue still asks (float64 pricing, `scratchpad/edge3/`)

On every checked `q` with `1 < ϖ(q) < λ(q)` and `ϖ(q)` not an integer, the two covers fail
exactly on **41 424 moduli, all in `[16590, 66239]`** (`edge4.py`, per integer, exact `φ`,
`f₁`), and on all of them `⌊ϖ(q)⌋ ∈ {1, 2}`, so `G_q(⌊ϖ⌋)` is `1` (`⌊ϖ⌋ = 1`) or
`1 + [q odd]` (`⌊ϖ⌋ = 2`) in closed form. The residue is there TRUE with margin `≥ 0.114` (at
`q = 60060`). Beyond them, `CoverB` can fail only where `ϖ₀`'s two-step iteration undershoots
the true edge of region (i) by less than `1`, which starts at `q ≈ 1.4997·10¹⁰` (`gap.py`); from
there on `λ(q) ≤ 639 < 754 ≤ ϖ(q)` (the exact product over `p ≤ 29` bounds `λ`), so the residue's
hypothesis `ϖ(q) < λ(q)` fails and nothing is asked. Closing the residue is a computation of
~41 000 closed-form evaluations (seconds), or an analytic argument on the explicit
`G_q ∈ {1, 2}`.
-/

namespace Principia.Common.TernaryGoldbach.EE

open Principia.Common.PSieve (gQ)
open Principia.Common.TernaryGoldbach.HC (omegaE cDeltaE kappaE betaE lambdaE tauE cSig cRho2
  varpi0 varpiE errE sumLogP)
open Principia.Common.TernaryGoldbach.HX (Luce)

/-! ## (1) The covers and the residue -/

/-- `N(q) = ⌊ϖ(q)⌋ + 1`, the first integer above the partial step. -/
noncomputable def edgeN (q : ℕ) : ℕ := ⌊varpiE q⌋₊ + 1

/-- **Cover A** — the dropped `(1 − ω)log s` pays for the transfer from the integer `N(q)`. -/
def CoverA (q : ℕ) : Prop :=
  Real.log ((edgeN q : ℝ) / varpiE q) + (q : ℝ) / q.totient * (omegaE * (7.284 * CY.f1 q *
      ((20000 * varpiE q) ^ (-(1 : ℝ) / 3) - (20000 * (edgeN q : ℝ)) ^ (-(1 : ℝ) / 3)))) ≤
    (1 - omegaE) * max 0 (Real.log (100000 / ((edgeN q : ℝ) * q)))

/-- **Cover B** — region (i) (`lem:paniz`) contains the partial step, checked at its two ends. -/
def CoverB (q : ℕ) : Prop :=
  varpiE q + Real.log q ≤ cSig 1.36 * ((q : ℝ) * varpiE q) ^ tauE ∧
    (edgeN q : ℝ) + Real.log q ≤ cSig 1.36 * ((q : ℝ) * edgeN q) ^ tauE

/-- **NAMED — the edge residue**: `HX.EspagnEdge`'s statement restricted to the checked `q` where
BOTH analytic covers fail. Float64: those are 41 424 moduli in `[16590, 66239]`, each with
`⌊ϖ(q)⌋ ∈ {1, 2}` (module docstring). A computation nobody ran, far smaller than `EspagnEdge`. -/
def EspagnEdgeRes : Prop :=
  ∀ q : ℕ, 1 ≤ q → ((q : ℝ) < 3.3e9 ∨ ((q : ℝ) < 2.2e10 ∧ 210 ∣ q)) →
    (⌊varpiE q⌋₊ : ℝ) < varpiE q → 1 < varpiE q → varpiE q < lambdaE q →
      ¬CoverA q → ¬CoverB q →
        errE q (varpiE q) + omegaE * (7.284 * (20000 * varpiE q) ^ (-(1 : ℝ) / 3) * CY.f1 q) ≤
          (q.totient : ℝ) / q * kappaE q

/-- The residue is implied by `HX.EspagnEdge` (it only adds hypotheses). -/
theorem edgeRes_of_edge (ed : HX.EspagnEdge) : EspagnEdgeRes :=
  fun q h1 h2 h3 h4 h5 _ _ => ed q h1 h2 h3 h4 h5

/-! ## (2) Cover B: the step is inside region (i) -/

/-- `c(1.36) > 0`. -/
theorem cSig_pos : 0 < cSig 1.36 := Real.exp_pos _

/-- **Concavity through the step**: if `a + log q ≤ c(qa)^τ` and `b + log q ≤ c(qb)^τ` with
`0 ≤ a ≤ R ≤ b`, `a < b`, then `R + log q ≤ c(qR)^τ`. -/
theorem region_concave (q : ℕ) {a b R : ℝ} (ha : 0 ≤ a) (hab : a < b) (haR : a ≤ R)
    (hRb : R ≤ b) (h1 : a + Real.log q ≤ cSig 1.36 * ((q : ℝ) * a) ^ tauE)
    (h2 : b + Real.log q ≤ cSig 1.36 * ((q : ℝ) * b) ^ tauE) :
    R + Real.log q ≤ cSig 1.36 * ((q : ℝ) * R) ^ tauE := by
  have hτ0 : 0 ≤ tauE := HX.tauE_pos.le
  have hτ1 : tauE ≤ 1 := HX.tauE_lt_one.le
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hba : 0 < b - a := by linarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (b - R) / (b - a) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = (R - a) / (b - a) := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; exact div_nonneg (by linarith) hba.le
  have hw0 : 0 ≤ w := by rw [hw]; exact div_nonneg (by linarith) hba.le
  have huw : u + w = 1 := by
    rw [hu, hw, ← add_div, div_eq_one_iff_eq hba.ne']
    ring
  have hcomb : u * a + w * b = R := by
    rw [hu, hw]
    field_simp
    ring
  have hb0 : 0 ≤ b := by linarith
  have hxa : (q : ℝ) * a ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (mul_nonneg hq0 ha)
  have hxb : (q : ℝ) * b ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (mul_nonneg hq0 hb0)
  have hconc := (Real.concaveOn_rpow hτ0 hτ1).2 hxa hxb hu0 hw0 huw
  simp only [smul_eq_mul] at hconc
  have hpt : u * ((q : ℝ) * a) + w * ((q : ℝ) * b) = (q : ℝ) * R := by
    rw [← hcomb]
    ring
  rw [hpt] at hconc
  have hc := cSig_pos
  have e1 := mul_le_mul_of_nonneg_left h1 hu0
  have e2 := mul_le_mul_of_nonneg_left h2 hw0
  have e3 := mul_le_mul_of_nonneg_left hconc hc.le
  have e4 : u * (a + Real.log q) + w * (b + Real.log q) = R + Real.log q := by
    rw [← hcomb]
    linear_combination Real.log q * huw
  nlinarith

/-- **Cover B makes the edge configuration impossible**: `Q₀ = Rsq ≥ Rq` and region (i) fails
at `R`, while `CoverB` puts the whole step `[ϖ, N]` inside region (i). -/
theorem false_of_coverB (q : ℕ) (hq : 1 ≤ q) (Q0 s : ℝ) (hs : 1 ≤ s) (hR1 : 1 ≤ Q0 / (s * q))
    (hnp : cSig 1.36 * Q0 ^ tauE < Q0 / (s * q) + Real.log q)
    (hvR : varpiE q < Q0 / (s * q)) (hN : Q0 / (s * q) < edgeN q) (hB : CoverB q) : False := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hsq : 0 < s * q := by positivity
  have hv0 : 0 ≤ varpiE q := by
    unfold varpiE
    exact le_max_of_le_right (le_max_of_le_right (div_nonneg (by norm_num)
      (Real.rpow_nonneg (mul_nonneg (Real.exp_pos _).le hq0.le) _)))
  have hreg := region_concave q hv0 (lt_trans hvR hN) hvR.le hN.le hB.1 hB.2
  have hQ0 : (q : ℝ) * (Q0 / (s * q)) ≤ Q0 := by
    rw [show (q : ℝ) * (Q0 / (s * q)) = Q0 / s by field_simp]
    have hQpos : 0 ≤ Q0 := by
      have := mul_le_mul_of_nonneg_left hR1 hsq.le
      rw [mul_div_cancel₀ _ hsq.ne'] at this
      linarith
    exact div_le_self hQpos hs
  have hmono : ((q : ℝ) * (Q0 / (s * q))) ^ tauE ≤ Q0 ^ tauE :=
    Real.rpow_le_rpow (by positivity) hQ0 HX.tauE_pos.le
  have := mul_le_mul_of_nonneg_left hmono cSig_pos.le
  linarith

/-! ## (3) Cover A: the transfer from the integer `N(q)` -/

/-- **`eq:luce` at an integer `N ≥ ϖ(q)`, explicit tail**:
`err_{q,N} + ω·7.284(20000N)^{−1/3}f₁ ≤ (φ/q)κ` — the cited check if `N < λ(q)`, `eq:malito`
(`eq:agammen`, `eq:sosor`) if `N ≥ λ(q)`. -/
theorem luceN (hm : CY.Malito) (cer : CY.CERange) (chk : HC.EspagnCheckCited) (q : ℕ)
    (hq : 1 ≤ q) (hr : (q : ℝ) < 3.3e9 ∨ ((q : ℝ) < 2.2e10 ∧ 210 ∣ q)) (N : ℕ) (hN1 : 1 ≤ N)
    (hv : varpiE q ≤ N) :
    errE q N + omegaE * (7.284 * (20000 * (N : ℝ)) ^ (-(1 : ℝ) / 3) * CY.f1 q) ≤
      (q.totient : ℝ) / q * kappaE q := by
  rcases lt_or_ge (N : ℝ) (lambdaE q) with hlam | hlam
  · exact chk q hq hr N hv hlam
  -- `N ≥ λ(q)`: `eq:malito` at `N`, as in `HX.luce_big`
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hκ := HX.kappaE_pos cer q hq
  have hW0 := (HX.omegaE_pos cer).le
  have hf := HX.f1_nonneg q
  have hR1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hR0 : (0 : ℝ) < N := by linarith
  have hy0 : 0 < (N : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hR0 _
  have hy3 : ((N : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR0.le]
    norm_num
  have hRm : (N : ℝ) ^ (-(1 : ℝ) / 3) = ((N : ℝ) ^ ((1 : ℝ) / 3))⁻¹ := by
    rw [show (-(1 : ℝ) / 3) = -((1 : ℝ) / 3) by ring, Real.rpow_neg hR0.le]
  have h20 : (20000 : ℝ) ^ (-(1 : ℝ) / 3) = ((20000 : ℝ) ^ ((1 : ℝ) / 3))⁻¹ := by
    rw [show (-(1 : ℝ) / 3) = -((1 : ℝ) / 3) by ring, Real.rpow_neg (by norm_num)]
  have hC0 : 0 ≤ (q : ℝ) / q.totient * (7.284 * (1 + betaE) * CY.f1 q / kappaE q) := by
    have hβ0 : 0 ≤ betaE := div_nonneg hW0 (Real.rpow_nonneg (by norm_num) _)
    have : 0 ≤ 7.284 * (1 + betaE) * CY.f1 q := by positivity
    positivity
  have hCy : (q : ℝ) / q.totient * (7.284 * (1 + betaE) * CY.f1 q / kappaE q) ≤
      (N : ℝ) ^ ((1 : ℝ) / 3) := by
    refine (pow_le_pow_iff_left₀ hC0 hy0.le (by norm_num : (3 : ℕ) ≠ 0)).mp ?_
    rw [hy3]
    exact hlam
  have hD : 7.284 * (1 + betaE) * CY.f1 q ≤
      (N : ℝ) ^ ((1 : ℝ) / 3) * ((q.totient : ℝ) / q * kappaE q) := by
    have e : (q : ℝ) / q.totient * (7.284 * (1 + betaE) * CY.f1 q / kappaE q) =
        7.284 * (1 + betaE) * CY.f1 q / ((q.totient : ℝ) / q * kappaE q) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)] at hCy
    linarith
  have h1 : errE q N ≤ 7.284 * ((N : ℝ) ^ ((1 : ℝ) / 3))⁻¹ * CY.f1 q := by
    have := (abs_le.mp (HX.errE_abs hm q hq N hR1)).2
    rwa [hRm] at this
  have h2 : (20000 * (N : ℝ)) ^ (-(1 : ℝ) / 3) =
      ((20000 : ℝ) ^ ((1 : ℝ) / 3))⁻¹ * ((N : ℝ) ^ ((1 : ℝ) / 3))⁻¹ := by
    rw [Real.mul_rpow (by norm_num) hR0.le, h20, hRm]
  rw [h2]
  have hLHS : errE q N + omegaE * (7.284 * (((20000 : ℝ) ^ ((1 : ℝ) / 3))⁻¹ *
      ((N : ℝ) ^ ((1 : ℝ) / 3))⁻¹) * CY.f1 q) ≤
      7.284 * (1 + betaE) * CY.f1 q * ((N : ℝ) ^ ((1 : ℝ) / 3))⁻¹ := by
    unfold betaE
    have e : 7.284 * (1 + omegaE / (20000 : ℝ) ^ ((1 : ℝ) / 3)) * CY.f1 q *
        ((N : ℝ) ^ ((1 : ℝ) / 3))⁻¹ = 7.284 * ((N : ℝ) ^ ((1 : ℝ) / 3))⁻¹ * CY.f1 q + omegaE *
          (7.284 * (((20000 : ℝ) ^ ((1 : ℝ) / 3))⁻¹ * ((N : ℝ) ^ ((1 : ℝ) / 3))⁻¹) * CY.f1 q) := by
      ring
    rw [e]
    linarith
  calc errE q N + omegaE * (7.284 * (((20000 : ℝ) ^ ((1 : ℝ) / 3))⁻¹ *
        ((N : ℝ) ^ ((1 : ℝ) / 3))⁻¹) * CY.f1 q)
      ≤ 7.284 * (1 + betaE) * CY.f1 q * ((N : ℝ) ^ ((1 : ℝ) / 3))⁻¹ := hLHS
    _ ≤ (q.totient : ℝ) / q * kappaE q := by
      rw [← div_eq_mul_inv, div_le_iff₀ hy0]
      linarith

/-- **`eq:karka` on the step from Cover A**: `err_{q,R} ≤ err_{q,N} + (φ/q)log(N/R)` (`G_q` is
constant on the step and non-decreasing), `luceN` at `N`, `max(0, −err_{q,T}) ≤
7.284(20000R)^{−1/3}f₁`, and `s ≥ max(1, 10⁵/(Nq))` pays the difference through the
`(1 − ω)log s` that `κ(q)` drops. -/
theorem karka_of_coverA (hm : CY.Malito) (cer : CY.CERange) (chk : HC.EspagnCheckCited)
    (q : ℕ) (hq : 1 ≤ q) (hr : (q : ℝ) < 3.3e9 ∨ ((q : ℝ) < 2.2e10 ∧ 210 ∣ q)) (Q0 s T : ℝ)
    (hQ0 : 100000 ≤ Q0) (hs : 1 ≤ s) (hR1 : 1 ≤ Q0 / (s * q)) (hT : 20000 * (Q0 / (s * q)) ≤ T)
    (hvR : varpiE q < Q0 / (s * q)) (hN : Q0 / (s * q) < edgeN q)
    (hfl : ⌊Q0 / (s * q)⌋₊ = ⌊varpiE q⌋₊) (hA : CoverA q) :
    errE q (Q0 / (s * q)) + omegaE * max 0 (-errE q T) ≤
      (q.totient : ℝ) / q * ((1 - omegaE) * (Real.log (s * q) - sumLogP q) + cDeltaE) := by
  set R := Q0 / (s * q) with hRdef
  set N := edgeN q with hNdef
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hu : (0 : ℝ) < (q.totient : ℝ) / q := div_pos hφ hq0
  have hs0 : 0 < s := by linarith
  have hR0 : 0 < R := by linarith
  have hN1 : 1 ≤ N := by rw [hNdef]; unfold edgeN; omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hvN : varpiE q ≤ N := le_trans hvR.le hN.le
  have hvpos : 0 < varpiE q := by
    have hR1' : 1 ≤ ⌊R⌋₊ := Nat.le_floor (by exact_mod_cast hR1)
    rw [hfl] at hR1'
    have := Nat.floor_pos.mp hR1'
    linarith
  -- `luceN` at `N`
  have hL := luceN hm cer chk q hq hr N hN1 hvN
  -- `G_q(R) ≤ G_q(N)`, so `err_R ≤ err_N + (φ/q)log(N/R)`
  have hG : gQ q R ≤ gQ q N := PSieve.gQ_mono q hN.le
  have hlogN : Real.log N - Real.log R = Real.log (N / R) := (Real.log_div (by linarith)
    hR0.ne').symm
  have herr : errE q R ≤ errE q N + (q.totient : ℝ) / q * Real.log (N / R) := by
    unfold errE
    rw [← hlogN]
    nlinarith
  -- the `tR` term
  have hmx := HX.max_errE_le hm q hq R T hR1 hT
  have hW0 := (HX.omegaE_pos cer).le
  have hmx' := mul_le_mul_of_nonneg_left hmx hW0
  -- `log s ≥ max 0 (log(10⁵/(Nq)))`
  have hsR : s * ((q : ℝ) * R) = Q0 := by
    rw [hRdef]
    field_simp
  have hlogs : max 0 (Real.log (100000 / ((N : ℝ) * q))) ≤ Real.log s := by
    refine max_le (Real.log_nonneg hs) ?_
    have hpos : (0 : ℝ) < 100000 / ((N : ℝ) * q) := by positivity
    refine Real.log_le_log hpos ?_
    rw [div_le_iff₀ (by positivity)]
    have h1 : (q : ℝ) * R ≤ (q : ℝ) * N := mul_le_mul_of_nonneg_left hN.le hq0.le
    have h2 := mul_le_mul_of_nonneg_left h1 hs0.le
    nlinarith
  -- Cover A, times `φ/q`
  have hlogNv : Real.log (N / R) ≤ Real.log (N / varpiE q) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_left (by linarith) hvpos hvR.le)
  have hrp : (20000 * R) ^ (-(1 : ℝ) / 3) ≤ (20000 * varpiE q) ^ (-(1 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  have hf := HX.f1_nonneg q
  have hA' := mul_le_mul_of_nonneg_left hA hu.le
  have hqq : (q.totient : ℝ) / q * ((q : ℝ) / q.totient) = 1 := by field_simp
  have hlogsq : Real.log (s * q) = Real.log s + Real.log q := Real.log_mul hs0.ne' hq0.ne'
  have hk : kappaE q = (1 - omegaE) * (Real.log q - sumLogP q) + cDeltaE := rfl
  have hW1 : 0 ≤ 1 - omegaE := by linarith [HX.omegaE_lt_one cer]
  have hsl := mul_le_mul_of_nonneg_left hlogs hW1
  have hsl' := mul_le_mul_of_nonneg_left hsl hu.le
  have hfr := mul_le_mul_of_nonneg_left hrp
    (mul_nonneg hW0 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 7.284) hf))
  have hlr := mul_le_mul_of_nonneg_left hlogNv hu.le
  rw [hlogsq]
  have e1 : (q.totient : ℝ) / q * ((q : ℝ) / q.totient * (omegaE * (7.284 * CY.f1 q *
      ((20000 * varpiE q) ^ (-(1 : ℝ) / 3) - (20000 * (N : ℝ)) ^ (-(1 : ℝ) / 3))))) =
      omegaE * (7.284 * CY.f1 q) * (20000 * varpiE q) ^ (-(1 : ℝ) / 3) -
        omegaE * (7.284 * (20000 * (N : ℝ)) ^ (-(1 : ℝ) / 3) * CY.f1 q) := by
    rw [← mul_assoc, hqq]
    ring
  rw [← hNdef, mul_add, e1] at hA'
  rw [hk] at hL
  linear_combination herr + hmx' + hL + hA' + hlr + hfr + hsl'

/-! ## (4) `prop:espagn` with the covers -/

/-- **`prop:espagn` from its links, the edge by the two covers and `EspagnEdgeRes`** —
`HX.espagn_of_links` with its fourth case (`⌊R⌋ < ϖ < R < λ`) split three ways: `CoverB`
(impossible), `CoverA` (`karka_of_coverA`), or neither (`EspagnEdgeRes`, then as before). -/
theorem espagn_of_links2 (cer : CY.CERange) (hm : CY.Malito) (hc : CY.Cante)
    (cl : HC.CharpyLo) (su : HX.Suspiro) (chk : HC.EspagnCheckCited) (res : EspagnEdgeRes)
    (lq : ∀ q : ℕ, 1 ≤ q → ¬((q : ℝ) < 3.3e9 ∨ ((q : ℝ) < 2.2e10 ∧ 210 ∣ q)) →
      lambdaE q ≤ varpiE q) :
    CY.Espagn := by
  intro Q0 Q h0 h1 h2 q hq1 hq2 s hs1 hs2
  have hQ0 : (0 : ℝ) < Q0 := by linarith
  have hQ : 1 < Q := by nlinarith
  have hLQ : 0 < Real.log Q := Real.log_pos hQ
  have hρ : Real.log Q0 ≤ 0.6 * Real.log Q := by rwa [div_le_iff₀ hLQ] at h2
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hsq : 0 < s * q := by positivity
  have hsqQ0 : s * q ≤ Q0 := by
    rw [le_div_iff₀ hq0] at hs2
    exact hs2
  have hR1 : 1 ≤ Q0 / (s * q) := by
    rw [le_div_iff₀ hsq]
    linarith
  have hT : Q / (s * q) = Q0 / (s * q) * (Q / Q0) := by
    field_simp
  have hTR : 20000 * (Q0 / (s * q)) ≤ Q / (s * q) := by
    have := div_le_div_of_nonneg_right h1 hsq.le
    rwa [mul_div_assoc] at this
  have hT1 : 1 ≤ Q / (s * q) := by linarith
  have hGT : 0 < gQ q (Q / (s * q)) := lt_of_lt_of_le one_pos (PSieve.one_le_gQ q _ hT1)
  have hL : 0 < Real.log Q + CY.cE := by linarith [cer.1]
  have hl0 : 0 ≤ Real.log Q0 := Real.log_nonneg (by linarith)
  have hB0 : 0 ≤ (Real.log Q0 + 1.36) / (Real.log Q + CY.cE) :=
    div_nonneg (by linarith) hL.le
  have hBW := HX.ratio_le_omega cer Q0 Q h0 hQ hρ
  have hS := HX.sumLogP_le q hq1
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq1)
  have hkar := fun hk => HX.ratio_le q hq1 Q0 Q s hQ0 (by linarith) hs1 hGT hL hB0 hBW hS hk
  by_cases hpan : Q0 / (s * q) + Real.log q ≤ cSig 1.36 * Q0 ^ tauE
  · -- (i) the `lem:paniz` region: `lem:trivo` and `paniz_alg`
    have hQQ0 : 182 ≤ Q / Q0 := by
      rw [le_div_iff₀ hQ0]
      linarith
    have htr := HX.trivo su cl q hq1 (Q0 / (s * q)) (Q / Q0) hR1 hQQ0
    rw [← hT, Real.log_div (by linarith) hQ0.ne'] at htr
    have hpa := HX.paniz_alg cer Q0 Q (Q0 / (s * q)) (Real.log q) (by linarith) hρ (by linarith)
      hpan
    rw [div_le_iff₀ hGT]
    exact le_trans htr (mul_le_mul_of_nonneg_right hpa hGT.le)
  · replace hpan := not_le.mp hpan
    by_cases hmia : Real.log q + (1.4709 - CY.cE) + omegaE * (CY.cE - 1.312) - cDeltaE ≤
        (1 - omegaE) * Real.log (s * q)
    · -- (ii) `eq:miasmar`: the easy error bounds
      apply hkar
      have e1 := HX.errE_le hc q hq1 _ hR1
      have e2 := HX.errE_ge cl q hq1 _ (by linarith : (182 : ℝ) ≤ Q / (s * q))
      have hW0 := (HX.omegaE_pos cer).le
      have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
      have hu : (0 : ℝ) ≤ (q.totient : ℝ) / q := div_nonneg hφ.le hq0.le
      have hSn := HX.sumLogP_nonneg q
      have hmx : max 0 (-errE q (Q / (s * q))) ≤
          (q.totient : ℝ) / q * (sumLogP q + (CY.cE - 1.312)) :=
        max_le (mul_nonneg hu (by linarith [cer.1])) (by linarith)
      have h3 := mul_le_mul_of_nonneg_left hmx hW0
      have h4 := mul_le_mul_of_nonneg_left hmia hu
      nlinarith
    · -- (iii) `R > ϖ(q)`
      replace hmia := not_le.mp hmia
      have hv := HX.varpiE_lt cer q hq1 Q0 s h0 hs1 hR1 hpan hmia
      apply hkar
      by_cases hlam : lambdaE q ≤ Q0 / (s * q)
      · exact HX.karka_of_luce cer q hq1 s _ _ hs1 (HX.luce_big hm cer q hq1 _ _ hR1 hTR hlam)
      · replace hlam := not_le.mp hlam
        by_cases hr : (q : ℝ) < 3.3e9 ∨ ((q : ℝ) < 2.2e10 ∧ 210 ∣ q)
        · by_cases hvf : varpiE q ≤ ⌊Q0 / (s * q)⌋₊
          · exact HX.karka_of_luce cer q hq1 s _ _ hs1
              (HX.luce_check hm cer chk q hq1 hr _ _ hR1 hTR hvf hlam)
          · -- the edge: `⌊R⌋ < ϖ < R`
            have hfl1 : (⌊Q0 / (s * q)⌋₊ : ℝ) < varpiE q := lt_of_not_ge hvf
            have hfl : ⌊Q0 / (s * q)⌋₊ = ⌊varpiE q⌋₊ :=
              le_antisymm (Nat.le_floor hfl1.le) (Nat.floor_le_floor hv.le)
            have hN : Q0 / (s * q) < edgeN q := by
              unfold edgeN
              rw [← hfl]
              push_cast
              exact Nat.lt_floor_add_one _
            by_cases hB : CoverB q
            · exact (false_of_coverB q hq1 Q0 s hs1 hR1 hpan hv hN hB).elim
            by_cases hA : CoverA q
            · exact karka_of_coverA hm cer chk q hq1 hr Q0 s _ h0 hs1 hR1 hTR hv hN hfl hA
            -- neither cover: the residue, then as in `HX.luce_edge`
            have hni : (⌊varpiE q⌋₊ : ℝ) < varpiE q := by rw [← hfl]; exact hfl1
            have hv1 : 1 < varpiE q := by
              have hn1 : 1 ≤ ⌊Q0 / (s * q)⌋₊ := Nat.le_floor (by exact_mod_cast hR1)
              have : (1 : ℝ) ≤ ⌊Q0 / (s * q)⌋₊ := by exact_mod_cast hn1
              linarith
            have hc := res q hq1 hr hni hv1 (lt_trans hv hlam) hA hB
            have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
            have hG : gQ q (Q0 / (s * q)) = gQ q (varpiE q) := by
              unfold PSieve.gQ
              rw [hfl]
            have hlog : Real.log (varpiE q) ≤ Real.log (Q0 / (s * q)) :=
              Real.log_le_log (by linarith) hv.le
            have he : errE q (Q0 / (s * q)) ≤ errE q (varpiE q) := by
              unfold errE
              rw [hG]
              have := mul_le_mul_of_nonneg_left hlog (div_nonneg hφ.le hq0.le)
              nlinarith
            have hmx := HX.max_errE_le hm q hq1 (varpiE q) (Q / (s * q)) hv1.le (by linarith)
            have hW0 := (HX.omegaE_pos cer).le
            have h3 := mul_le_mul_of_nonneg_left hmx hW0
            refine HX.karka_of_luce cer q hq1 s _ _ hs1 ?_
            unfold Luce
            linarith
        · exact absurd (lt_of_le_of_lt (lq q hq1 hr) hv) (not_lt.mpr hlam.le)

/-- **`HC.EspagnRed` with the edge cut down**: `lem:suspiro` from its cited small range and
`SuspiroBig`, the edge by `EspagnEdgeRes`, the large-`q` fact from `HX.EspagnLargeQ`. -/
theorem espagnRed_of_links2 (sb : HX.SuspiroBig) (res : EspagnEdgeRes) (lq : HX.EspagnLargeQ) :
    HC.EspagnRed := fun cer hm hc cl sm chk =>
  espagn_of_links2 cer hm hc cl (HX.suspiro_of sm.1 sb) chk res (lq cer sm)

/-- **`HC.EspagnRed` from Rosser–Schoenfeld, the edge residue and the large-`q` fact.** -/
theorem espagnRed_of_rs2 (rs : HX.RS75Theta) (h15 : GS.RS62Thm15) (res : EspagnEdgeRes)
    (lq : HX.EspagnLargeQ) : HC.EspagnRed :=
  espagnRed_of_links2 (HX.suspiroBig_of rs h15) res lq

end Principia.Common.TernaryGoldbach.EE
