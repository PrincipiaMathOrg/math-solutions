/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.NefumoLinks
import Principia.Common.TernaryGoldbach.OstopSpine
import Principia.Common.TernaryGoldbach.KSmall

set_option autoImplicit false

/-!
# `JokoW` FROM TRUE LINKS: the `D` terms of `prop:nefumo`, done right

`NefumoSpine.JokoW` carries `eq:joko` (929–933, 1501–1524) as printed:
`|∫_𝔐 S₊²S*e − mainI − rI| ≤ (2Z₊LS* + 4√(Z₊Z*)LS₊)x`. The printed argument is first-order
(`NefumoSpine`, finding 2). This file proves it from links that are each TRUE:

**`jokoW_of_links : DPoint → SummW η₊ → SummW η* → ZvsL η₊ → ZvsL η* → JokoW η₊ η*`**
(for `η₊, η* ∈ L¹(0,∞)`), and so
**`nefumoW_helf_final : Massacre → GatTail → DPoint → SummW η* → ZvsL η₊ → ZvsL η* →
T3W η₊ η* → RW.NefumoW η₊ η* η∘`**.

## The route (each step PROVED unless marked)

1. **`dI_eq`**: `∫_𝔐 kernS − mainI − rI = dI`, the arcs integral of `S₊²D* + S₊D₊M* + D₊M₊M*`,
   `D = S − M − R` (`dT`): [Arcs] for the complex integrand (`arcsComplex`, from `arcsReal` on
   `Re`/`Im`), continuity of `R` in `δ` (`continuous_rT`, via `continuous_twSum`), linearity, and
   the telescoping `S₊²S* − M₊²M* = (R-terms) + (D-terms)`.
2. **[DPoint]** (OPEN, generic): `|D| ≤ d_q = ∑_{p|q} (p/(p−1)) log p ∑_k |η(p^k/x)|` — the exact
   coefficient of `eq:mouche` (795–824): `(1/φ)∑_χ χ(a)τ(χ̄)χ*(p^k)` is `−e(ap^k/q)/(p−1)` when
   `p ∥ q` and `0` when `p² ∣ q`. Checked numerically for every `q ≤ 40`, every `a`, every `n ≤ 2q`
   (`scratchpad/nefumo/dpoint.py`: exact on `(n,q) = 1`; `|e − c| ≤ p/(p−1)`, attained).
3. **`dq_le`**: `d_q ≤ 2·LS` on `𝔐_{8,r}` — `∑_{p|q} (p/(p−1)) log p ≤ 2 log 2 + (3/2) log r ≤
   2 log r`, because the odd primes of a modulus multiply to at most `r` (`oddPart_le`). The
   budget's factor `2` pays both the weight `p/(p−1)` and the extra `log 2` of an even modulus,
   which the printed `LS = log r·max_p` does not see (`Σ_{p|q} log p` reaches `log 2r`).
4. **`dI_le`**: `|dI| ≤ x(D*A + D₊(√L*√A + √L₊√L*))`, `L = L_{r,δ₀}`: Cauchy–Schwarz over `a`
   (`∑_a|S₊| ≤ √φ√(∑|S₊|²)`) and over the arcs, `∫_𝔐|√φM|² = x²L` (`mM_sq_sum`).
5. **`amaj_le_zk`**: `A ≤ Z_{η²,2}` — `∫_𝔐 ≤ ∫_{(0,1]}` and Parseval (`OS.parseval_Ioc`).
6. **[ZvsL]** (OPEN, weight): `L_{r,δ₀}(η) ≤ Z_{η²,2}(x)` at `x ≥ 4.9·10²⁶` — about `13.6|η|₂²`
   (with the true `S = 6.80`) against about `|η|₂² log x ≈ 62|η|₂²`.
7. **[Summ]** (weight): `∑ Λ(n)|η(n/x)| < ∞`; `summW_plus` from `KS.ksmall_helf`; OPEN at `η*`.
8. **`joko_arith`** closes: `2LS*·A + 2LS₊(√L*√A + √L₊√L*) ≤ 2Z₊LS* + 4√(Z₊Z*)LS₊`.

So the source's line 3 is RIGHT, and first-order after all — but only with `eq:mouche`'s exact
coefficient, `A ≤ Z` and `L ≤ Z` in place of the printed "Cauchy–Schwarz and Plancherel over
`ℝ/ℤ`", which cannot see the `M` factors the telescoping produces.
-/

namespace Principia.Common.TernaryGoldbach.NF

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach Set
open scoped ArithmeticFunction

/-! ## [Arcs] for complex integrands -/

/-- `(∫_{a}^{b} g).re = ∫_{a}^{b} (g ·).re`. -/
theorem re_intervalIntegral (g : ℝ → ℂ) (a b : ℝ) (hg : IntervalIntegrable g volume a b) :
    (∫ δ in a..b, g δ).re = ∫ δ in a..b, (g δ).re := by
  have h := Complex.reCLM.intervalIntegral_comp_comm hg
  simp only [Complex.reCLM_apply] at h
  exact h.symm

/-- `(∫_{a}^{b} g).im = ∫_{a}^{b} (g ·).im`. -/
theorem im_intervalIntegral (g : ℝ → ℂ) (a b : ℝ) (hg : IntervalIntegrable g volume a b) :
    (∫ δ in a..b, g δ).im = ∫ δ in a..b, (g δ).im := by
  have h := Complex.imCLM.intervalIntegral_comp_comm hg
  simp only [Complex.imCLM_apply] at h
  exact h.symm

theorem majorSet_sub (x : ℝ) : Smooth.majorSet x ⊆ Icc (0 : ℝ) 1 := fun _ h =>
  Ioc_subset_Icc_self h.1

/-- **[Arcs] for continuous `1`-periodic complex `f`**, from `arcsReal` on `Re f` and `Im f`. -/
theorem arcsComplex (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (f : ℝ → ℂ) (hc : Continuous f)
    (hp : ∀ α, f (α + 1) = f α) :
    ∫ α in Smooth.majorSet x, f α = arcSum x (fun q a δ => f (pt x q a δ)) := by
  have hx0 : 0 < x := AI.x_pos hx
  have hI : Integrable f (volume.restrict (Smooth.majorSet x)) :=
    (hc.integrableOn_Icc (a := 0) (b := 1)).mono_set (majorSet_sub x)
  have hre := arcsReal x hx (fun α => (f α).re) (Complex.continuous_re.comp hc)
    (fun α => congrArg Complex.re (hp α))
  have him := arcsReal x hx (fun α => (f α).im) (Complex.continuous_im.comp hc)
    (fun α => congrArg Complex.im (hp α))
  have hint : ∀ q, IntervalIntegrable (fun δ => ∑ a ∈ cop q, f (pt x q a δ)) volume
      (-wq q) (wq q) := fun q =>
    (continuous_finsetSum _ fun a _ => hc.comp (continuous_pt x q a)).intervalIntegrable _ _
  apply Complex.ext
  · have h1 : (∫ α in Smooth.majorSet x, f α).re = ∫ α in Smooth.majorSet x, (f α).re := by
      have h := Complex.reCLM.integral_comp_comm hI
      simp only [Complex.reCLM_apply] at h
      exact h.symm
    rw [h1, hre]
    unfold arcSum
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Complex.div_ofReal_re, re_intervalIntegral _ _ _ (hint q)]
    congr 1
    refine intervalIntegral.integral_congr fun δ _ => ?_
    simp only [Complex.re_sum]
  · have h1 : (∫ α in Smooth.majorSet x, f α).im = ∫ α in Smooth.majorSet x, (f α).im := by
      have h := Complex.imCLM.integral_comp_comm hI
      simp only [Complex.imCLM_apply] at h
      exact h.symm
    rw [h1, him]
    unfold arcSum
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Complex.div_ofReal_im, im_intervalIntegral _ _ _ (hint q)]
    congr 1
    refine intervalIntegral.integral_congr fun δ _ => ?_
    simp only [Complex.im_sum]

/-! ## Continuity of the `err` part in `δ` -/

theorem continuous_twSum (η : ℝ → ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) :
    Continuous fun β => MajSp.twSum η χ x β := by
  by_cases hs : Summable fun n : ℕ =>
      ‖((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((η ((n : ℝ) / x) : ℝ) : ℂ)‖
  · unfold MajSp.twSum
    refine continuous_tsum (fun n => ?_) hs (fun n β => ?_)
    · exact continuous_const.mul (Spine.continuous_e.comp (continuous_const.mul continuous_id))
    · rw [norm_mul, e_norm, mul_one]
  · have h0 : ∀ β, MajSp.twSum η χ x β = 0 := fun β => by
      unfold MajSp.twSum
      refine tsum_eq_zero_of_not_summable fun h => hs ?_
      refine (summable_norm_iff.mpr h).congr fun n => ?_
      rw [norm_mul, e_norm, mul_one]
    have h00 : (fun β => MajSp.twSum η χ x β) = fun _ => 0 := funext h0
    rw [h00]
    exact continuous_const

theorem continuous_err (η : ℝ → ℝ) (h1 : Integrable η (volume.restrict (Set.Ioi 0)))
    {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) :
    Continuous fun δ => MajSp.err η χ δ x := by
  unfold MajSp.err
  split_ifs
  · exact (((continuous_twSum η χ x).comp (continuous_id.div_const x)).div_const _).sub
      (continuous_mainFT_of η h1)
  · simp only [sub_zero]
    exact ((continuous_twSum η χ x).comp (continuous_id.div_const x)).div_const _

theorem continuous_rT (η : ℝ → ℝ) (h1 : Integrable η (volume.restrict (Set.Ioi 0))) (x : ℝ)
    (q a : ℕ) : Continuous fun δ => rT η x q a δ := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    simp only [rT, dite_true]
    exact continuous_const
  · haveI : NeZero q := ⟨hq.ne'⟩
    have e1 : (fun δ => rT η x q a δ) = fun δ => ∑ χ : DirichletCharacter ℂ q,
        (x : ℂ) / (q.totient : ℂ) * gaussSum χ⁻¹ ZMod.stdAddChar *
          MajSp.err η χ.primitiveCharacter δ x * χ (a : ZMod q) :=
      funext fun δ => rT_eq η x q a δ
    rw [e1]
    exact continuous_finsetSum _ fun χ _ =>
      ((continuous_const.mul (continuous_err η h1 χ.primitiveCharacter x)).mul continuous_const)

theorem continuous_mT' (η : ℝ → ℝ) (h : Integrable η (volume.restrict (Set.Ioi 0))) (x : ℝ)
    (q : ℕ) : Continuous fun δ => mT η x q δ := by
  unfold mT
  exact continuous_const.mul (continuous_mainFT_of η h)


/-! ## The non-coprime remainder `D = S − M − R` and the identity `∫_𝔐 kernS = mainI + rI + dI` -/

/-- **`D = S − M − R`** on the arc about `a/q`: what `eq:beatit`'s primitive-character expansion
leaves over (the terms `(n, q) > 1`, `eq:mouche`). -/
noncomputable def dT (η : ℝ → ℝ) (x : ℝ) (q a : ℕ) (δ : ℝ) : ℂ :=
  Smooth.smSum η x (pt x q a δ) - mT η x q δ - rT η x q a δ

/-- **The `D` terms** (`eq:joko`): `S₊²D* + S₊D₊M* + D₊M₊M*`. -/
noncomputable def dI (ηp ηs : ℝ → ℝ) (N : ℕ) (x : ℝ) : ℂ :=
  arcSum x fun q a δ =>
    (Smooth.smSum ηp x (pt x q a δ) ^ 2 * dT ηs x q a δ +
      Smooth.smSum ηp x (pt x q a δ) * dT ηp x q a δ * mT ηs x q δ +
        dT ηp x q a δ * mT ηp x q δ * mT ηs x q δ) * e (-(N : ℝ) * pt x q a δ)

theorem continuous_kernS (ηp ηs : ℝ → ℝ) (N : ℕ) (x : ℝ) :
    Continuous (Smooth.kernS ηp ηs N x) := by
  unfold Smooth.kernS
  exact (((continuous_sm ηp x).pow 2).mul (continuous_sm ηs x)).mul
    (Spine.continuous_e.comp (continuous_const.mul continuous_id))

theorem kernS_add_one (ηp ηs : ℝ → ℝ) (N : ℕ) (x α : ℝ) :
    Smooth.kernS ηp ηs N x (α + 1) = Smooth.kernS ηp ηs N x α := by
  unfold Smooth.kernS
  rw [smSum_add_one, smSum_add_one]
  have h1 : e (-(N : ℝ) * (α + 1)) = e (-(N : ℝ) * α) * e (-(N : ℝ)) := by
    rw [e_add]
    congr 1
    ring
  have h2 : e (-(N : ℝ)) = 1 := (e_eq_one_iff _).mpr ⟨-(N : ℤ), by push_cast; ring⟩
  rw [h1, h2, mul_one]

/-- `arcSum` is linear. -/
theorem arcSum_sub3 (x : ℝ) (f g h : ℕ → ℕ → ℝ → ℂ)
    (hf : ∀ q, Continuous fun δ => ∑ a ∈ cop q, f q a δ)
    (hg : ∀ q, Continuous fun δ => ∑ a ∈ cop q, g q a δ)
    (hh : ∀ q, Continuous fun δ => ∑ a ∈ cop q, h q a δ) :
    arcSum x f - arcSum x g - arcSum x h = arcSum x fun q a δ => f q a δ - g q a δ - h q a δ := by
  unfold arcSum
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  have i1 : IntervalIntegrable (fun δ => ∑ a ∈ cop q, f q a δ) volume (-wq q) (wq q) :=
    (hf q).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun δ => ∑ a ∈ cop q, g q a δ) volume (-wq q) (wq q) :=
    (hg q).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun δ => ∑ a ∈ cop q, h q a δ) volume (-wq q) (wq q) :=
    (hh q).intervalIntegrable _ _
  have i12 : IntervalIntegrable (fun δ => ∑ a ∈ cop q, f q a δ - ∑ a ∈ cop q, g q a δ) volume
      (-wq q) (wq q) := i1.sub i2
  rw [← sub_div, ← sub_div, ← intervalIntegral.integral_sub i1 i2,
    ← intervalIntegral.integral_sub i12 i3]
  congr 1
  refine intervalIntegral.integral_congr fun δ _ => ?_
  simp only [Finset.sum_sub_distrib]

/-- **`∫_𝔐 S₊²S*e(−Nα) = mainI + rI + dI`**: [Arcs] for the complex integrand, linearity, and the
telescoping `S₊²S* = M₊²M* + (S₊²R* + S₊R₊M* + R₊M₊M*) + (S₊²D* + S₊D₊M* + D₊M₊M*)`. -/
theorem dI_eq (ηp ηs : ℝ → ℝ) (hp1 : Integrable ηp (volume.restrict (Set.Ioi 0)))
    (hs1 : Integrable ηs (volume.restrict (Set.Ioi 0))) (N : ℕ) (x : ℝ)
    (hx : 49 * 10 ^ 25 ≤ x) :
    (∫ α in Smooth.majorSet x, Smooth.kernS ηp ηs N x α) - mainI ηp ηs N x - rI ηp ηs N x =
      dI ηp ηs N x := by
  have cE : ∀ q a, Continuous fun δ => e (-(N : ℝ) * pt x q a δ) := fun q a =>
    Spine.continuous_e.comp (continuous_const.mul (continuous_pt x q a))
  have cS : ∀ (η : ℝ → ℝ) (q a : ℕ), Continuous fun δ => Smooth.smSum η x (pt x q a δ) :=
    fun η q a => (continuous_sm η x).comp (continuous_pt x q a)
  rw [arcsComplex x hx _ (continuous_kernS ηp ηs N x) (kernS_add_one ηp ηs N x)]
  unfold mainI rI dI
  rw [arcSum_sub3]
  · unfold arcSum
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    refine intervalIntegral.integral_congr fun δ _ => ?_
    refine Finset.sum_congr rfl fun a _ => ?_
    unfold Smooth.kernS dT
    ring
  · exact fun q => continuous_finsetSum _ fun a _ =>
      (continuous_kernS ηp ηs N x).comp (continuous_pt x q a)
  · exact fun q => continuous_finsetSum _ fun a _ =>
      (((continuous_mT' ηp hp1 x q).pow 2).mul (continuous_mT' ηs hs1 x q)).mul (cE q a)
  · exact fun q => continuous_finsetSum _ fun a _ =>
      ((((cS ηp q a).pow 2).mul (continuous_rT ηs hs1 x q a)).add
        (((cS ηp q a).mul (continuous_rT ηp hp1 x q a)).mul (continuous_mT' ηs hs1 x q))).add
        (((continuous_rT ηp hp1 x q a).mul (continuous_mT' ηp hp1 x q)).mul
          (continuous_mT' ηs hs1 x q)) |>.mul (cE q a)


/-! ## The links of [Joko] -/

/-- **The non-coprime mass with `eq:mouche`'s weights**:
`d_q(η) = ∑_{p|q} (p/(p−1)) log p ∑_{k≥1} |η(p^k/x)|`. -/
noncomputable def dq (η : ℝ → ℝ) (x : ℝ) (q : ℕ) : ℝ :=
  ∑ p ∈ q.primeFactors, (p : ℝ) / ((p : ℝ) - 1) * Real.log p *
    ∑' k : ℕ, |η ((p : ℝ) ^ (k + 1) / x)|

/-- **[DPoint]** (`eq:mouche`, 795–858, with its exact coefficient): `|S − M − R| ≤ d_q` at every
`a` coprime to `q`. On `(n, q) = 1` the expansion is exact (`GaussInduced.sum_char_gaussSum`); at
`n = p^k`, `p ∣ q`, the coefficient `(1/φ)∑_χ χ(a)τ(χ̄)χ*(n)` is `−e(an/q)/(p−1)` if `p ∥ q` and
`0` if `p² ∣ q`, so `|e(an/q) − ·| ≤ p/(p−1)`. OPEN; generic. -/
def DPoint : Prop :=
  ∀ (η : ℝ → ℝ) (x : ℝ), 0 < x → Summable (fun n : ℕ => Λ n * |η ((n : ℝ) / x)|) →
    ∀ q a : ℕ, 1 ≤ q → Nat.Coprime a q → ∀ δ : ℝ, ‖dT η x q a δ‖ ≤ dq η x q

/-- **[Summ]** `∑ Λ(n)|η(n/x)| < ∞` at every `x ≥ 4.9·10²⁶`. A WEIGHT link. -/
def SummW (η : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → Summable (fun n : ℕ => Λ n * |η ((n : ℝ) / x)|)

/-- **[ZvsL]** `L_{r,δ₀}(η) ≤ Z_{η²,2}(x)`: the major-arc mass of the MAIN term is at most the whole
`ℓ²` mass (`≈ 13.6|η|₂²` against `≈ |η|₂² log x`). A WEIGHT link. -/
def ZvsL (η : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → DS.lRD η ≤ MajSp.zk (fun t => η t ^ 2) 2 x

/-! ## The arithmetic of `LS`: `d_q ≤ 2·LS` on the arcs -/

theorem Qs_cases {q : ℕ} (hq : q ∈ Qs) :
    (Odd q ∧ 1 ≤ q ∧ q ≤ 150000) ∨ (Even q ∧ 1 ≤ q ∧ q ≤ 300000) := by
  unfold Qs DS.oddQ DS.evenQ at hq
  rcases Finset.mem_union.mp hq with h | h
  · obtain ⟨h1, h2⟩ := Finset.mem_filter.mp h
    exact Or.inl ⟨h2, Finset.mem_Icc.mp h1⟩
  · obtain ⟨h1, h2⟩ := Finset.mem_filter.mp h
    exact Or.inr ⟨h2, Finset.mem_Icc.mp h1⟩

/-- The odd primes dividing a modulus of `𝔐_{8,r}` have product `≤ r`. -/
theorem oddPart_le {q : ℕ} (hq : q ∈ Qs) :
    ∏ p ∈ q.primeFactors.filter (fun p => p ≠ 2), p ≤ 150000 := by
  have hdvd : ∏ p ∈ q.primeFactors.filter (fun p => p ≠ 2), p ∣ q :=
    dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _))
      (Nat.prod_primeFactors_dvd q)
  have hcop : Nat.Coprime (∏ p ∈ q.primeFactors.filter (fun p => p ≠ 2), p) 2 := by
    rw [Nat.coprime_prod_left_iff]
    intro p hp
    obtain ⟨hpf, hp2⟩ := Finset.mem_filter.mp hp
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hpf) Nat.prime_two).mpr hp2
  rcases Qs_cases hq with ⟨_, h1, h2⟩ | ⟨he, h1, h2⟩
  · exact le_trans (Nat.le_of_dvd (by omega) hdvd) h2
  · obtain ⟨m, hm⟩ := he
    have hm2 : q = m * 2 := by omega
    have hdvd2 : ∏ p ∈ q.primeFactors.filter (fun p => p ≠ 2), p ∣ m * 2 := by
      rw [← hm2]
      exact hdvd
    have hdm := hcop.dvd_of_dvd_mul_right hdvd2
    have hm0 : 0 < m := by omega
    exact le_trans (Nat.le_of_dvd hm0 hdm) (by omega)

theorem pf_le {q p : ℕ} (hq : q ∈ Qs) (hp : p ∈ q.primeFactors) : p ≤ 150000 := by
  by_cases h2 : p = 2
  · omega
  · have hmem : p ∈ q.primeFactors.filter (fun p => p ≠ 2) := Finset.mem_filter.mpr ⟨hp, h2⟩
    have hpos : 0 < ∏ p ∈ q.primeFactors.filter (fun p => p ≠ 2), p :=
      Finset.prod_pos fun r hr =>
        (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1).pos
    exact le_trans (Nat.le_of_dvd hpos (Finset.dvd_prod_of_mem _ hmem)) (oddPart_le hq)

/-- `∑_{p|q} (p/(p−1)) log p ≤ 2 log 2 + (3/2) log r ≤ 2 log r` on the arcs. -/
theorem wsum_le {q : ℕ} (hq : q ∈ Qs) :
    ∑ p ∈ q.primeFactors, (p : ℝ) / ((p : ℝ) - 1) * Real.log p ≤ 2 * Real.log 150000 := by
  have hf0 : ∀ p ∈ q.primeFactors, 0 ≤ (p : ℝ) / ((p : ℝ) - 1) * Real.log p := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    exact mul_nonneg (div_nonneg (by linarith) (by linarith)) (Real.log_nonneg (by linarith))
  rw [← Finset.sum_filter_add_sum_filter_not q.primeFactors (fun p => p = 2)]
  have hA : ∑ p ∈ q.primeFactors.filter (fun p => p = 2),
      (p : ℝ) / ((p : ℝ) - 1) * Real.log p ≤ 2 * Real.log 2 := by
    have hsub : q.primeFactors.filter (fun p => p = 2) ⊆ {2} := fun p hp => by
      rw [Finset.mem_singleton]
      exact (Finset.mem_filter.mp hp).2
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => ?_) (le_of_eq ?_)
    · have h2 : (2 : ℝ) ≤ p := by
        by_cases hp : p ∈ q.primeFactors
        · exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        · simp_all
      exact mul_nonneg (div_nonneg (by linarith) (by linarith)) (Real.log_nonneg (by linarith))
    · rw [Finset.sum_singleton]
      norm_num
  have hB : ∑ p ∈ q.primeFactors.filter (fun p => ¬ p = 2),
      (p : ℝ) / ((p : ℝ) - 1) * Real.log p ≤ 3 / 2 * Real.log 150000 := by
    have hterm : ∀ p ∈ q.primeFactors.filter (fun p => ¬ p = 2),
        (p : ℝ) / ((p : ℝ) - 1) * Real.log p ≤ 3 / 2 * Real.log p := by
      intro p hp
      obtain ⟨hpf, hp2⟩ := Finset.mem_filter.mp hp
      have hpr := Nat.prime_of_mem_primeFactors hpf
      have h3 : (3 : ℝ) ≤ p := by
        have := hpr.two_le
        have : p ≠ 2 := hp2
        exact_mod_cast (show 3 ≤ p by omega)
      have hl : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
      have hw : (p : ℝ) / ((p : ℝ) - 1) ≤ 3 / 2 := by
        rw [div_le_iff₀ (by linarith)]
        linarith
      exact mul_le_mul_of_nonneg_right hw hl
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have hne : ∀ p ∈ q.primeFactors.filter (fun p => ¬ p = 2), ((p : ℕ) : ℝ) ≠ 0 := fun p hp =>
      Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero
    rw [← Real.log_prod hne]
    have hP := oddPart_le hq
    have hPpos : (0 : ℝ) < ∏ p ∈ q.primeFactors.filter (fun p => ¬ p = 2), (p : ℝ) := by
      refine Finset.prod_pos fun p hp => ?_
      exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos
    refine Real.log_le_log hPpos ?_
    have hc : (∏ p ∈ q.primeFactors.filter (fun p => ¬ p = 2), (p : ℝ)) =
        ((∏ p ∈ q.primeFactors.filter (fun p => p ≠ 2), p : ℕ) : ℝ) := by
      push_cast
      rfl
    rw [hc]
    exact_mod_cast hP
  have h16 : 4 * Real.log 2 ≤ Real.log 150000 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num)
  linarith

/-- **`d_q ≤ 2·LS`** on the arcs of `𝔐_{8,r}` (`LSBound` prices `log r ∑_k |η(p^k/x)|`). -/
theorem dq_le (η : ℝ → ℝ) (x L : ℝ) (hL : MajSp.LSBound η x L) {q : ℕ} (hq : q ∈ Qs) :
    dq η x q ≤ 2 * L := by
  have hlog : 0 < Real.log 150000 := Real.log_pos (by norm_num)
  have hT : ∀ p ∈ q.primeFactors, ∑' k : ℕ, |η ((p : ℝ) ^ (k + 1) / x)| ≤ L / Real.log 150000 :=
    fun p hp => by
      rw [le_div_iff₀ hlog, mul_comm]
      exact (hL p (Nat.prime_of_mem_primeFactors hp) (pf_le hq hp)).2
  have hL0 : 0 ≤ L := by
    have h2 := (hL 2 Nat.prime_two (by norm_num)).2
    have h0 : 0 ≤ ∑' k : ℕ, |η ((2 : ℝ) ^ (k + 1) / x)| := tsum_nonneg fun _ => abs_nonneg _
    push_cast at h2
    nlinarith
  have hw := wsum_le hq
  unfold dq
  calc ∑ p ∈ q.primeFactors, (p : ℝ) / ((p : ℝ) - 1) * Real.log p *
        ∑' k : ℕ, |η ((p : ℝ) ^ (k + 1) / x)|
      ≤ ∑ p ∈ q.primeFactors, (p : ℝ) / ((p : ℝ) - 1) * Real.log p * (L / Real.log 150000) := by
        refine Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (hT p hp) ?_
        have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        exact mul_nonneg (div_nonneg (by linarith) (by linarith)) (Real.log_nonneg (by linarith))
    _ = (∑ p ∈ q.primeFactors, (p : ℝ) / ((p : ℝ) - 1) * Real.log p) *
          (L / Real.log 150000) := by rw [Finset.sum_mul]
    _ ≤ 2 * Real.log 150000 * (L / Real.log 150000) :=
        mul_le_mul_of_nonneg_right hw (div_nonneg hL0 hlog.le)
    _ = 2 * L := by field_simp

/-! ## Parseval on the circle: `A_η ≤ Z_{η²,2}` -/

/-- **`A_η(x) ≤ Z_{η²,2}(x)`**: `∫_𝔐 |S_η|² ≤ ∫_{(0,1]} |S_η|² = ∑ Λ(n)²η(n/x)²`
(`OS.parseval_Ioc`). -/
theorem amaj_le_zk (η : ℝ → ℝ) (x : ℝ) (hx : 0 < x)
    (hs : Summable (fun n : ℕ => Λ n * |η ((n : ℝ) / x)|)) :
    MajSp.amaj η x ≤ MajSp.zk (fun t => η t ^ 2) 2 x := by
  have ha : Summable fun n : ℕ => ‖((Λ n : ℝ) : ℂ) * ((η ((n : ℝ) / x) : ℝ) : ℂ)‖ := by
    refine hs.congr fun n => ?_
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg vonMangoldt_nonneg]
  have hpar := OS.parseval_Ioc _ ha
  have hsm : ∀ α, Smooth.smSum η x α =
      OS.eSum (fun n : ℕ => ((Λ n : ℝ) : ℂ) * ((η ((n : ℝ) / x) : ℝ) : ℂ)) α := fun _ => rfl
  have hcont : Continuous fun α => ‖Smooth.smSum η x α‖ ^ 2 := (continuous_sm η x).norm.pow 2
  have hmono : ∫ α in Smooth.majorSet x, ‖Smooth.smSum η x α‖ ^ 2 ≤
      ∫ α in Set.Ioc (0 : ℝ) 1, ‖Smooth.smSum η x α‖ ^ 2 :=
    setIntegral_mono_set (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (ae_of_all _ fun _ => sq_nonneg _) (Filter.Eventually.of_forall fun α hα => hα.1)
  simp_rw [hsm] at hmono
  rw [hpar] at hmono
  have hZ : ∑' n : ℕ, ‖((Λ n : ℝ) : ℂ) * ((η ((n : ℝ) / x) : ℝ) : ℂ)‖ ^ 2 =
      ∑' n : ℕ, (Λ n) ^ 2 * η ((n : ℝ) / x) ^ 2 := by
    refine tsum_congr fun n => ?_
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      mul_pow, sq_abs, sq_abs]
  rw [hZ] at hmono
  unfold MajSp.amaj MajSp.zk
  simp_rw [hsm]
  exact div_le_div_of_nonneg_right hmono hx.le


/-! ## The `D` terms, integrated -/

/-- `∑_q ∫ (√φ(q)|M_η|)² = x²·L_{r,δ₀}(η)` (`AI.lRD_eq_Qs`). -/
theorem mM_sq_sum (η : ℝ → ℝ) (x : ℝ) :
    ∑ q ∈ Qs, ∫ δ in (-wq q)..(wq q), (Real.sqrt (q.totient : ℝ) * ‖mT η x q δ‖) ^ 2 =
      x ^ 2 * DS.lRD η := by
  have hQ : AI.Qs = Qs := by
    unfold AI.Qs Qs
    rfl
  have hW : AI.wd = wq := by
    funext q
    unfold AI.wd wq
    rfl
  rw [AI.lRD_eq_Qs, hQ, hW, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (mem_Qs hq).1
  have e1 : (fun δ => (Real.sqrt (q.totient : ℝ) * ‖mT η x q δ‖) ^ 2) =
      fun δ => x ^ 2 * DS.cQ q * ‖MajSp.mainFT η δ‖ ^ 2 := by
    funext δ
    rw [mul_pow, Real.sq_sqrt hφ.le, norm_mT, mul_pow, sq_abs]
    unfold DS.cQ
    field_simp
  rw [e1, intervalIntegral.integral_const_mul]
  unfold DS.iQ
  ring

theorem lsbound_nonneg (η : ℝ → ℝ) (x L : ℝ) (hL : MajSp.LSBound η x L) : 0 ≤ L := by
  have h2 := (hL 2 Nat.prime_two (by norm_num)).2
  have h0 : 0 ≤ ∑' k : ℕ, |η ((2 : ℝ) ^ (k + 1) / x)| := tsum_nonneg fun _ => abs_nonneg _
  have hlog : 0 < Real.log 150000 := Real.log_pos (by norm_num)
  push_cast at h2
  nlinarith

/-- **The pointwise bound on the `D` integrand**, per modulus: with `|D| ≤ d_q` ([DPoint]),
`|∑_a (…)| ≤ D*∑|S₊|² + D₊(√φ|M*|)√(∑|S₊|²) + D₊(√φ|M₊|)(√φ|M*|)`. -/
theorem dA_le (dp : DPoint) (ηp ηs : ℝ → ℝ) (N : ℕ) (x : ℝ) (hx : 0 < x)
    (hsp : Summable (fun n : ℕ => Λ n * |ηp ((n : ℝ) / x)|))
    (hss : Summable (fun n : ℕ => Λ n * |ηs ((n : ℝ) / x)|)) (Dp Ds : ℝ)
    (hDp : ∀ q ∈ Qs, dq ηp x q ≤ Dp) (hDs : ∀ q ∈ Qs, dq ηs x q ≤ Ds) (hDp0 : 0 ≤ Dp)
    (q : ℕ) (hq : q ∈ Qs) (δ : ℝ) :
    ‖∑ a ∈ cop q, (Smooth.smSum ηp x (pt x q a δ) ^ 2 * dT ηs x q a δ +
      Smooth.smSum ηp x (pt x q a δ) * dT ηp x q a δ * mT ηs x q δ +
        dT ηp x q a δ * mT ηp x q δ * mT ηs x q δ) * e (-(N : ℝ) * pt x q a δ)‖ ≤
      Ds * aSq ηp x q δ + Dp * ((Real.sqrt (q.totient : ℝ) * ‖mT ηs x q δ‖) *
        Real.sqrt (aSq ηp x q δ)) + Dp * ((Real.sqrt (q.totient : ℝ) * ‖mT ηp x q δ‖) *
          (Real.sqrt (q.totient : ℝ) * ‖mT ηs x q δ‖)) := by
  have hq1 := (mem_Qs hq).1
  have hDa : ∀ a ∈ cop q, ‖dT ηp x q a δ‖ ≤ Dp := fun a ha =>
    le_trans (dp ηp x hx hsp q a hq1 (Finset.mem_filter.mp ha).2 δ) (hDp q hq)
  have hDb : ∀ a ∈ cop q, ‖dT ηs x q a δ‖ ≤ Ds := fun a ha =>
    le_trans (dp ηs x hx hss q a hq1 (Finset.mem_filter.mp ha).2 δ) (hDs q hq)
  have hpt : ∀ a ∈ cop q, ‖(Smooth.smSum ηp x (pt x q a δ) ^ 2 * dT ηs x q a δ +
      Smooth.smSum ηp x (pt x q a δ) * dT ηp x q a δ * mT ηs x q δ +
        dT ηp x q a δ * mT ηp x q δ * mT ηs x q δ) * e (-(N : ℝ) * pt x q a δ)‖ ≤
      Ds * ‖Smooth.smSum ηp x (pt x q a δ)‖ ^ 2 +
        Dp * ‖mT ηs x q δ‖ * ‖Smooth.smSum ηp x (pt x q a δ)‖ +
          Dp * (‖mT ηp x q δ‖ * ‖mT ηs x q δ‖) := by
    intro a ha
    rw [norm_mul, e_norm, mul_one]
    refine le_trans norm_add₃_le ?_
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow]
    have h1 := mul_le_mul_of_nonneg_left (hDb a ha) (sq_nonneg ‖Smooth.smSum ηp x (pt x q a δ)‖)
    have h2 := mul_le_mul_of_nonneg_left (hDa a ha)
      (mul_nonneg (norm_nonneg (Smooth.smSum ηp x (pt x q a δ))) (norm_nonneg (mT ηs x q δ)))
    have h3 := mul_le_mul_of_nonneg_left (hDa a ha)
      (mul_nonneg (norm_nonneg (mT ηp x q δ)) (norm_nonneg (mT ηs x q δ)))
    nlinarith
  have hS : ∑ a ∈ cop q, ‖Smooth.smSum ηp x (pt x q a δ)‖ ≤
      Real.sqrt (q.totient : ℝ) * Real.sqrt (aSq ηp x q δ) := by
    have h1 := sq_sum_le_card_mul_sum_sq (s := cop q)
      (f := fun a => ‖Smooth.smSum ηp x (pt x q a δ)‖)
    rw [card_cop] at h1
    rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
    exact Real.le_sqrt_of_sq_le h1
  have hcard : ∑ _a ∈ cop q, (1 : ℝ) = q.totient := by
    rw [Finset.sum_const, card_cop, nsmul_eq_mul, mul_one]
  have hφ : Real.sqrt (q.totient : ℝ) * Real.sqrt (q.totient : ℝ) = q.totient :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum hpt) ?_)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hA : ∑ a ∈ cop q, ‖Smooth.smSum ηp x (pt x q a δ)‖ ^ 2 = aSq ηp x q δ := rfl
  rw [hA, Finset.sum_const, card_cop, nsmul_eq_mul]
  have k1 := mul_le_mul_of_nonneg_left hS (mul_nonneg hDp0 (norm_nonneg (mT ηs x q δ)))
  have e1 : Dp * ((Real.sqrt (q.totient : ℝ) * ‖mT ηp x q δ‖) *
      (Real.sqrt (q.totient : ℝ) * ‖mT ηs x q δ‖)) =
        (q.totient : ℝ) * (Dp * (‖mT ηp x q δ‖ * ‖mT ηs x q δ‖)) := by
    rw [show Dp * ((Real.sqrt (q.totient : ℝ) * ‖mT ηp x q δ‖) *
        (Real.sqrt (q.totient : ℝ) * ‖mT ηs x q δ‖)) = (Real.sqrt (q.totient : ℝ) *
          Real.sqrt (q.totient : ℝ)) * (Dp * (‖mT ηp x q δ‖ * ‖mT ηs x q δ‖)) by ring, hφ]
  rw [e1]
  nlinarith

/-- **The `D` terms, integrated**: `|dI| ≤ x(D*·A + D₊(√L*√A + √L₊√L*))`,
`L = L_{r,δ₀}` (Cauchy–Schwarz over the arcs and `mM_sq_sum`). -/
theorem dI_le (dp : DPoint) (ηp ηs : ℝ → ℝ) (hp1 : Integrable ηp (volume.restrict (Set.Ioi 0)))
    (hs1 : Integrable ηs (volume.restrict (Set.Ioi 0))) (N : ℕ) (x : ℝ)
    (hx : 49 * 10 ^ 25 ≤ x) (hsp : Summable (fun n : ℕ => Λ n * |ηp ((n : ℝ) / x)|))
    (hss : Summable (fun n : ℕ => Λ n * |ηs ((n : ℝ) / x)|)) (Dp Ds : ℝ)
    (hDp : ∀ q ∈ Qs, dq ηp x q ≤ Dp) (hDs : ∀ q ∈ Qs, dq ηs x q ≤ Ds) (hDp0 : 0 ≤ Dp) :
    ‖dI ηp ηs N x‖ ≤ x * (Ds * MajSp.amaj ηp x + Dp * (Real.sqrt (DS.lRD ηs) *
      Real.sqrt (MajSp.amaj ηp x) + Real.sqrt (DS.lRD ηp) * Real.sqrt (DS.lRD ηs))) := by
  have hx0 : 0 < x := AI.x_pos hx
  have cA : ∀ q, Continuous fun δ => aSq ηp x q δ := fun q => continuous_arcSq ηp x q
  have cR : ∀ q, Continuous fun δ => Real.sqrt (aSq ηp x q δ) := fun q => (cA q).sqrt
  have cFs : ∀ q, Continuous fun δ => Real.sqrt (q.totient : ℝ) * ‖mT ηs x q δ‖ := fun q =>
    continuous_const.mul (continuous_mT ηs hs1 x q)
  have cFp : ∀ q, Continuous fun δ => Real.sqrt (q.totient : ℝ) * ‖mT ηp x q δ‖ := fun q =>
    continuous_const.mul (continuous_mT ηp hp1 x q)
  have i1 : ∀ q, IntervalIntegrable (fun δ => Ds * aSq ηp x q δ) volume (-wq q) (wq q) :=
    fun q => ((cA q).intervalIntegrable _ _).const_mul Ds
  have i2 : ∀ q, IntervalIntegrable (fun δ => Dp * ((Real.sqrt (q.totient : ℝ) *
      ‖mT ηs x q δ‖) * Real.sqrt (aSq ηp x q δ))) volume (-wq q) (wq q) :=
    fun q => (((cFs q).mul (cR q)).intervalIntegrable _ _).const_mul Dp
  have i3 : ∀ q, IntervalIntegrable (fun δ => Dp * ((Real.sqrt (q.totient : ℝ) *
      ‖mT ηp x q δ‖) * (Real.sqrt (q.totient : ℝ) * ‖mT ηs x q δ‖))) volume (-wq q) (wq q) :=
    fun q => (((cFp q).mul (cFs q)).intervalIntegrable _ _).const_mul Dp
  have i12 : ∀ q, IntervalIntegrable (fun δ => Ds * aSq ηp x q δ + Dp * ((Real.sqrt
      (q.totient : ℝ) * ‖mT ηs x q δ‖) * Real.sqrt (aSq ηp x q δ))) volume (-wq q) (wq q) :=
    fun q => (i1 q).add (i2 q)
  have hq : ∀ q ∈ Qs, ‖(∫ δ in (-wq q)..(wq q), ∑ a ∈ cop q,
      (Smooth.smSum ηp x (pt x q a δ) ^ 2 * dT ηs x q a δ +
        Smooth.smSum ηp x (pt x q a δ) * dT ηp x q a δ * mT ηs x q δ +
          dT ηp x q a δ * mT ηp x q δ * mT ηs x q δ) * e (-(N : ℝ) * pt x q a δ)) / (x : ℂ)‖ ≤
      (Ds * (∫ δ in (-wq q)..(wq q), aSq ηp x q δ) +
        Dp * (∫ δ in (-wq q)..(wq q), (Real.sqrt (q.totient : ℝ) * ‖mT ηs x q δ‖) *
          Real.sqrt (aSq ηp x q δ)) +
        Dp * (∫ δ in (-wq q)..(wq q), (Real.sqrt (q.totient : ℝ) * ‖mT ηp x q δ‖) *
          (Real.sqrt (q.totient : ℝ) * ‖mT ηs x q δ‖))) / x := by
    intro q hq
    have hww : -wq q ≤ wq q := by linarith [wq_nonneg q]
    have hb := intervalIntegral.norm_integral_le_of_norm_le hww
      (ae_of_all _ fun δ _ => dA_le dp ηp ηs N x hx0 hsp hss Dp Ds hDp hDs hDp0 q hq δ)
      ((i12 q).add (i3 q))
    rw [intervalIntegral.integral_add (i12 q) (i3 q), intervalIntegral.integral_add (i1 q) (i2 q),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at hb
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hx0.le]
    exact div_le_div_of_nonneg_right hb hx0.le
  have hsum : ‖dI ηp ηs N x‖ ≤ (Ds * (∑ q ∈ Qs, ∫ δ in (-wq q)..(wq q), aSq ηp x q δ) +
      Dp * (∑ q ∈ Qs, ∫ δ in (-wq q)..(wq q), (Real.sqrt (q.totient : ℝ) * ‖mT ηs x q δ‖) *
        Real.sqrt (aSq ηp x q δ)) +
      Dp * (∑ q ∈ Qs, ∫ δ in (-wq q)..(wq q), (Real.sqrt (q.totient : ℝ) * ‖mT ηp x q δ‖) *
        (Real.sqrt (q.totient : ℝ) * ‖mT ηs x q δ‖))) / x := by
    simp only [dI, arcSum]
    refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum hq) (le_of_eq ?_))
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum,
      Finset.mul_sum, Finset.mul_sum]
  have hA := sum_int_aSq arcsReal ηp x hx
  have hsq : ∑ q ∈ Qs, ∫ δ in (-wq q)..(wq q), Real.sqrt (aSq ηp x q δ) ^ 2 =
      x ^ 2 * MajSp.amaj ηp x := by
    rw [← hA]
    refine Finset.sum_congr rfl fun q _ => ?_
    exact intervalIntegral.integral_congr fun δ _ => Real.sq_sqrt (aSq_nonneg ηp x q δ)
  have hc1 := cs_sum_int Qs wq wq_nonneg
    (fun q δ => Real.sqrt (q.totient : ℝ) * ‖mT ηs x q δ‖) (fun q δ => Real.sqrt (aSq ηp x q δ))
    cFs cR
  have hc2 := cs_sum_int Qs wq wq_nonneg
    (fun q δ => Real.sqrt (q.totient : ℝ) * ‖mT ηp x q δ‖)
    (fun q δ => Real.sqrt (q.totient : ℝ) * ‖mT ηs x q δ‖) cFp cFs
  rw [hsq, mM_sq_sum] at hc1
  rw [mM_sq_sum, mM_sq_sum] at hc2
  have hs2 : ∀ L : ℝ, Real.sqrt (x ^ 2 * L) = x * Real.sqrt L := fun L => by
    rw [Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq hx0.le]
  rw [hs2, hs2] at hc1 hc2
  rw [hA] at hsum
  have k1 := mul_le_mul_of_nonneg_left hc1 hDp0
  have k2 := mul_le_mul_of_nonneg_left hc2 hDp0
  refine le_trans hsum ?_
  rw [div_le_iff₀ hx0]
  have e1 : x * (Ds * MajSp.amaj ηp x + Dp * (Real.sqrt (DS.lRD ηs) *
      Real.sqrt (MajSp.amaj ηp x) + Real.sqrt (DS.lRD ηp) * Real.sqrt (DS.lRD ηs))) * x =
        Ds * (x ^ 2 * MajSp.amaj ηp x) +
          Dp * (x * Real.sqrt (DS.lRD ηs) * (x * Real.sqrt (MajSp.amaj ηp x))) +
            Dp * (x * Real.sqrt (DS.lRD ηp) * (x * Real.sqrt (DS.lRD ηs))) := by ring
  rw [e1]
  linarith

/-! ## [Joko] from its links -/

/-- The closing arithmetic of [Joko]: `A ≤ Z₊`, `L₊ ≤ Z₊`, `L* ≤ Z*`. -/
theorem joko_arith (x A Lp Ls Zp Zs Rp Rs : ℝ) (hx : 0 ≤ x) (hLp : 0 ≤ Lp) (hLs : 0 ≤ Ls)
    (hA : A ≤ Zp) (hRp : Rp ≤ Zp) (hRs : Rs ≤ Zs) (hZp : 0 ≤ Zp) :
    x * (2 * Ls * A + 2 * Lp * (Real.sqrt Rs * Real.sqrt A + Real.sqrt Rp * Real.sqrt Rs)) ≤
      (2 * Zp * Ls + 4 * Real.sqrt (Zp * Zs) * Lp) * x := by
  have s1 : Real.sqrt Rs * Real.sqrt A ≤ Real.sqrt (Zp * Zs) := by
    rw [Real.sqrt_mul hZp, mul_comm]
    exact mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hRs) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
  have s2 : Real.sqrt Rp * Real.sqrt Rs ≤ Real.sqrt (Zp * Zs) := by
    rw [Real.sqrt_mul hZp]
    exact mul_le_mul (Real.sqrt_le_sqrt hRp) (Real.sqrt_le_sqrt hRs) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
  have h1 : 2 * Ls * A ≤ 2 * Zp * Ls := by nlinarith
  have h2 : 2 * Lp * (Real.sqrt Rs * Real.sqrt A + Real.sqrt Rp * Real.sqrt Rs) ≤
      4 * Real.sqrt (Zp * Zs) * Lp := by nlinarith
  have h3 : 2 * Ls * A + 2 * Lp * (Real.sqrt Rs * Real.sqrt A + Real.sqrt Rp * Real.sqrt Rs) ≤
      2 * Zp * Ls + 4 * Real.sqrt (Zp * Zs) * Lp := by linarith
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right h3 hx

/-- **[Joko] FROM ITS LINKS**: `eq:mouche`'s pointwise bound ([DPoint], generic), summability
([Summ]) and `L_{r,δ₀} ≤ Z_{η²,2}` ([ZvsL]) for both weights. Parseval on the circle
(`amaj_le_zk`), `d_q ≤ 2·LS` (`dq_le`) and Cauchy–Schwarz over the arcs (`dI_le`) are PROVED. -/
theorem jokoW_of_links (dp : DPoint) (ηp ηs : ℝ → ℝ)
    (hp1 : Integrable ηp (volume.restrict (Set.Ioi 0)))
    (hs1 : Integrable ηs (volume.restrict (Set.Ioi 0))) (swp : SummW ηp) (sws : SummW ηs)
    (zp : ZvsL ηp) (zs : ZvsL ηs) : JokoW ηp ηs := by
  intro N _ x hx Lp Ls hLp hLs
  rw [dI_eq ηp ηs hp1 hs1 N x hx]
  exact le_trans (dI_le dp ηp ηs hp1 hs1 N x hx (swp x hx) (sws x hx) (2 * Lp) (2 * Ls)
      (fun q hq => dq_le ηp x Lp hLp hq) (fun q hq => dq_le ηs x Ls hLs hq)
      (mul_nonneg zero_le_two (lsbound_nonneg ηp x Lp hLp)))
    (joko_arith x _ Lp Ls _ _ _ _ (MajSp.x_nonneg x hx) (lsbound_nonneg ηp x Lp hLp)
      (lsbound_nonneg ηs x Ls hLs) (amaj_le_zk ηp x (AI.x_pos hx) (swp x hx)) (zp x hx)
      (zs x hx) (MajSp.zk_sq_nonneg ηp x (MajSp.x_nonneg x hx)))


/-! ## The compositions -/

/-- **`RW.NefumoW` with [Arcs], [Tail] and [Joko] discharged**: [Massacre], [GatTail], [DPoint]
(generic) and the weight links [O1], [Madge], [Hosto], [T3], [Summ], [ZvsL]. Application only. -/
theorem nefumoW_of_rest2 (ms : Massacre) (gt : GatTail) (dp : DPoint) (ηp ηs ηo : ℝ → ℝ)
    (oi : OInt ηo) (md : Madge ηo) (hw : HostoW ηo ηs) (t3 : T3W ηp ηs) (swp : SummW ηp)
    (sws : SummW ηs) (zp : ZvsL ηp) (zs : ZvsL ηs) : RW.NefumoW ηp ηs ηo :=
  fun rg => nefumoW_of_rest ms gt ηp ηs ηo oi md hw t3
    (jokoW_of_links dp ηp ηs (memLp_one_iff_integrable.mp rg.1)
      (memLp_one_iff_integrable.mp rg.2.2.1) swp sws zp zs) rg

/-- **[Summ] at Helfgott's `η₊`** (`KS.ksmall_helf`). -/
theorem summW_plus : SummW HW.etaPlus := fun x hx => (KS.ksmall_helf x hx).1

/-- **`RW.NefumoW` at Helfgott's weights**: [Massacre], [GatTail], [DPoint] (generic) and
[Summ] at `η*`, [ZvsL] at `η₊` and `η*`, [T3] at `(η₊, η*)`. Application only. -/
theorem nefumoW_helf_final (ms : Massacre) (gt : GatTail) (dp : DPoint)
    (sws : SummW HW.etaStar) (zp : ZvsL HW.etaPlus) (zs : ZvsL HW.etaStar)
    (t3 : T3W HW.etaPlus HW.etaStar) : RW.NefumoW HW.etaPlus HW.etaStar HW.etaCirc :=
  nefumoW_of_rest2 ms gt dp HW.etaPlus HW.etaStar HW.etaCirc oInt_helf madge_helf hostoW_helf t3
    summW_plus sws zp zs

end Principia.Common.TernaryGoldbach.NF
