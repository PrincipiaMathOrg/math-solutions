/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIICortoLargeC

set_option autoImplicit false

/-!
# The corrected `lem:yutto` links `M2LC.YuttoMid2C`, `M2LC.YuttoBig2C`, spined

Helfgott's printed proof of `lem:yutto` (`minarcs.tex` 2878-3110) goes through Rankin's trick
with `ε = 1/log x`, which drops a factor `x^{2ε} = e²`. This module does NOT follow it. It keeps
his two identities (`eq:anna` and the expansion of `μ(r)/σ(r)`), but folds the second one into a
single Dirichlet convolution with NONNEGATIVE coefficients and truncates honestly instead of
using Rankin:

```
 Anna2   g₂(x) = ∑_{d ≤ x odd} μ(d)/σ(d)² · hY(2d, x/d)²                (eq:anna)    LINK
 ConvK   hY(k, y) = ∑_{a ≤ y} aK(k, a)·m(y/a),                                       LINK
         hY(k, y) = ∑_{r ≤ y, (r,k)=1} μ(r)/σ(r),  m(t) = ∑_{n ≤ t} μ(n)/n,
         aK(k, a) = 1/(a·∏_{p | a, p ∤ k}(p + 1))  (≥ 0, multiplicative in a)
 KSumH   ∑_{a ≤ N} aK(2d, a)√a        ≤ 8·∏_{p | d} ρ_H(p)    (d odd)   Euler product LINK
 KSumQ   ∑_{a ≤ N} aK(2d, a)a^{1/4}   ≤ 4·∏_{p | d} ρ_Q(p)    (d odd)   Euler product LINK
 DSumH   ∑_{d ≤ x odd} μ²(d)·d/σ(d)²·∏_{p|d} ρ_H(p)²     ≤ 8 + 4 log x              LINK
 DSumQ   ∑_{d ≤ N odd} μ²(d)·√d/σ(d)²·∏_{p|d} ρ_Q(p)²    ≤ 2.4                      LINK
 RamareMarraki  |m(x)| ≤ 0.03/log x  (x ≥ 11815)    LITERATURE (Ramaré 2013, Cor. 1.4)
 yuttoMid2C_of_links : M2LC.YuttoMid2C   from Anna2, ConvK, KSumH, DSumH, HC.RamareCited
 yuttoBig2C_of_links : M2LC.YuttoBig2C   + KSumQ, DSumQ, RamareMarraki                 PROVED
```

`ρ_H(p) = (p+1)/((p+1)(1 − q) + q)` with `q = p^{−1/2}`, `ρ_Q` the same with `q = p^{−3/4}`;
this is exactly `β_p/α_p`, the ratio of the local factor at `p | k` to the one at `p ∤ k`.

**Every link is true with margin** (sanity values, double precision, not proof steps): the
exact Euler products are `6.762` (vs `8`) and `3.521` (vs `4`); the `d`-sums are
`≈ 0.33 + 0.807 log x` (vs `8 + 4 log x`; `11.48` at `x = 10⁶`) and `1.748` (vs `2.4`).
`Anna2` and `ConvK` were checked in exact rational arithmetic for small `x`, `y`, `k`.

**Where the bounds come from.** Mid range (`x < 10¹⁰`, so every `t = x/(da) ≤ 10¹²`): only
`|m(t)| ≤ √(2/t)` (`HC.RamareCited`, first clause), giving
`|g₂(x)| ≤ (2/x)·8²·(8 + 4 log x) = (1024 + 512 log x)/x` against `(2451.51 + 1225.752 log x)/x`.
Large range: `|m(t)| ≤ √(2/t) + (0.03/log x)(x/t)^{1/4}` for `1 ≤ t ≤ x` (Marraki for
`t ≥ 11815`, since `log x ≤ (x/t)^{1/4} log t` once `log t ≥ 4`), then `(P + Q)² ≤ 11P² + 1.1Q²`:
`|g₂(x)| ≤ 1408(8 + 4 log x)/x + 0.038016/log²x ≤ 3/√x + 0.038128/log²x`.

**The new literature hypothesis.** `RamareMarraki` is O. Ramaré, *From explicit estimates for
primes to explicit estimates for the Möbius function*, Acta Arith. 157 (2013), 365-379,
Corollary 1.4 and the sentence after it: "`|∑_{d≤D} μ(d)/d| ≤ (3 log D − 10)/(100 (log D)²)`
for `D ≥ 50 000`. If we replace the `−10` by `0`, the resulting bound is valid from `11 815`
onward" — i.e. `≤ 0.03/log D` for `D ≥ 11815`; Helfgott's `eq:marraki` (`minarcs.tex` 654-658).
Stated verbatim. No computation of ours stands in for any step.
-/

namespace Principia.Common.TernaryGoldbach.M2Y

open Finset

/-! ## (0) Objects -/

/-- `μ(n)` as a real. -/
noncomputable def mu (n : ℕ) : ℝ := ((ArithmeticFunction.moebius n : ℤ) : ℝ)

/-- `σ(n)` as a real. -/
noncomputable def sg (n : ℕ) : ℝ := (ArithmeticFunction.sigma 1 n : ℝ)

/-- `hY(k, y) = ∑_{r ≤ y, (r, k) = 1} μ(r)/σ(r)`. -/
noncomputable def hY (k : ℕ) (y : ℝ) : ℝ :=
  ∑ r ∈ Icc 1 ⌊y⌋₊, if Nat.Coprime r k then mu r / sg r else 0

/-- `aK(k, a) = 1/(a·∏_{p | a, p ∤ k}(p + 1))`: `a^{-j}/(p+1)` at `p^j`, `p ∤ k`; `p^{-j}` at
`p | k`. -/
noncomputable def aK (k a : ℕ) : ℝ :=
  1 / ((a : ℝ) * ∏ p ∈ a.primeFactors.filter (fun p => ¬ p ∣ k), ((p : ℝ) + 1))

/-- `ρ_H(p) = (p+1)/((p+1)(1 − p^{-1/2}) + p^{-1/2})`. -/
noncomputable def rhoH (p : ℕ) : ℝ :=
  ((p : ℝ) + 1) / (((p : ℝ) + 1) * (1 - 1 / Real.sqrt p) + 1 / Real.sqrt p)

/-- `p^{-3/4}`. -/
noncomputable def qq (p : ℕ) : ℝ := 1 / (Real.sqrt p * Real.sqrt (Real.sqrt p))

/-- `ρ_Q(p) = (p+1)/((p+1)(1 − p^{-3/4}) + p^{-3/4})`. -/
noncomputable def rhoQ (p : ℕ) : ℝ := ((p : ℝ) + 1) / (((p : ℝ) + 1) * (1 - qq p) + qq p)

/-! ## (1) Links -/

/-- **Link [Anna2] — `eq:anna`, `v = 2`.** -/
def Anna2 : Prop :=
  ∀ x : ℝ, 0 ≤ x → HC.gYutto 2 x =
    ∑ d ∈ Icc 1 ⌊x⌋₊, if Nat.Coprime d 2 then mu d / sg d ^ 2 * hY (d * 2) (x / d) ^ 2 else 0

/-- **Link [ConvK] — `μ(r)1_{(r,k)=1}/σ(r) = (aK(k,·) ⋆ μ/id)(r)`, summed.** -/
def ConvK : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ y : ℝ, 0 ≤ y → hY k y = ∑ a ∈ Icc 1 ⌊y⌋₊, aK k a * HC.mertF (y / a)

/-- **Link [KSumH] — the `√a`-weighted Euler product, `k = 2d`, `d` odd.** -/
def KSumH : Prop :=
  ∀ d N : ℕ, Nat.Coprime d 2 →
    ∑ a ∈ Icc 1 N, aK (d * 2) a * Real.sqrt a ≤ 8 * ∏ p ∈ d.primeFactors, rhoH p

/-- **Link [KSumQ] — the `a^{1/4}`-weighted Euler product, `k = 2d`, `d` odd.** -/
def KSumQ : Prop :=
  ∀ d N : ℕ, Nat.Coprime d 2 →
    ∑ a ∈ Icc 1 N, aK (d * 2) a * Real.sqrt (Real.sqrt a) ≤ 4 * ∏ p ∈ d.primeFactors, rhoQ p

/-- **Link [DSumH] — the `d`-sum of the `√(2/t)` part.** -/
def DSumH : Prop :=
  ∀ x : ℝ, 1 ≤ x →
    ∑ d ∈ Icc 1 ⌊x⌋₊, (if Nat.Coprime d 2 then
      mu d ^ 2 * (d : ℝ) / sg d ^ 2 * ∏ p ∈ d.primeFactors, rhoH p ^ 2 else 0) ≤
      8 + 4 * Real.log x

/-- **Link [DSumQ] — the `d`-sum of the Marraki part.** -/
def DSumQ : Prop :=
  ∀ N : ℕ,
    ∑ d ∈ Icc 1 N, (if Nat.Coprime d 2 then
      mu d ^ 2 * Real.sqrt d / sg d ^ 2 * ∏ p ∈ d.primeFactors, rhoQ p ^ 2 else 0) ≤ 2.4

/-- **LITERATURE — Ramaré, Acta Arith. 157 (2013) 365-379, Corollary 1.4** (with `−10`
replaced by `0`, "valid from `11 815` onward"); Helfgott's `eq:marraki`:
`|∑_{n ≤ x} μ(n)/n| ≤ 0.03/log x` for `x ≥ 11815`. -/
def RamareMarraki : Prop :=
  ∀ x : ℝ, 11815 ≤ x → |HC.mertF x| ≤ 0.03 / Real.log x

/-! ## (2) Elementary facts -/

theorem mu_abs_le_sq (n : ℕ) : |mu n| ≤ mu n ^ 2 := by
  unfold mu
  have h := ArithmeticFunction.abs_moebius_le_one (n := n)
  rcases abs_le.mp h with ⟨h1, h2⟩
  generalize (ArithmeticFunction.moebius n : ℤ) = m at h1 h2 ⊢
  interval_cases m <;> norm_num

theorem sg_pos (n : ℕ) (hn : 1 ≤ n) : 0 < sg n := by
  unfold sg
  exact_mod_cast ArithmeticFunction.sigma_pos 1 n (by omega)

theorem aK_nonneg (k a : ℕ) : 0 ≤ aK k a := by
  unfold aK
  have : 0 ≤ ∏ p ∈ a.primeFactors.filter (fun p => ¬ p ∣ k), ((p : ℝ) + 1) :=
    Finset.prod_nonneg fun p _ => by positivity
  positivity

theorem qq_le_one (p : ℕ) (hp : 1 ≤ p) : 0 < qq p ∧ qq p ≤ 1 := by
  unfold qq
  have h1 : 1 ≤ Real.sqrt p := Real.one_le_sqrt.mpr (by exact_mod_cast hp)
  have h2 : 1 ≤ Real.sqrt (Real.sqrt p) := Real.one_le_sqrt.mpr h1
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by positivity)]
  nlinarith

theorem rhoQ_pos (p : ℕ) (hp : 1 ≤ p) : 0 < rhoQ p := by
  obtain ⟨h0, h1⟩ := qq_le_one p hp
  unfold rhoQ
  have : 1 ≤ ((p : ℝ) + 1) * (1 - qq p) + qq p := by
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    nlinarith
  have : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  positivity

/-- `|m(t)| ≤ √(2/t)` for `1 ≤ t ≤ 10¹²` (`HC.RamareCited`, first clause). -/
theorem mert_sqrt (hR : HC.RamareCited) (t : ℝ) (ht : 1 ≤ t) (ht2 : t ≤ 1e12) :
    |HC.mertF t| ≤ Real.sqrt (2 / t) :=
  hR.1 t (by linarith) ht2

/-- `√(2/(y/a)) = √(2/y)·√a`. -/
theorem sqrt_ratio (y a : ℝ) (hy : 0 < y) (ha : 0 < a) :
    Real.sqrt (2 / (y / a)) = Real.sqrt (2 / y) * Real.sqrt a := by
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  field_simp

/-- **The triangle inequality through `ConvK`.** -/
theorem hY_le (cv : ConvK) (k : ℕ) (hk : 1 ≤ k) (y : ℝ) (hy : 0 ≤ y) (B : ℕ → ℝ)
    (hB : ∀ a ∈ Icc 1 ⌊y⌋₊, |HC.mertF (y / a)| ≤ B a) :
    |hY k y| ≤ ∑ a ∈ Icc 1 ⌊y⌋₊, aK k a * B a := by
  rw [cv k hk y hy]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a ha => ?_)
  rw [abs_mul, abs_of_nonneg (aK_nonneg k a)]
  exact mul_le_mul_of_nonneg_left (hB a ha) (aK_nonneg k a)

/-- `1 ≤ a ≤ ⌊y⌋` gives `1 ≤ y/a ≤ y`. -/
theorem ratio_bounds (y : ℝ) (a : ℕ) (ha : a ∈ Icc 1 ⌊y⌋₊) :
    1 ≤ y / a ∧ y / a ≤ y ∧ 0 < (a : ℝ) := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha
  have ha0 : (1 : ℝ) ≤ a := by exact_mod_cast h1
  have hy : (a : ℝ) ≤ y := by
    have h0 : 0 < ⌊y⌋₊ := lt_of_lt_of_le h1 h2
    have hy0 : 0 ≤ y := by
      by_contra hn
      rw [Nat.floor_of_nonpos (by linarith)] at h0
      exact lt_irrefl 0 h0
    exact le_trans (by exact_mod_cast h2) (Nat.floor_le hy0)
  have hy1 : 0 < y := by linarith
  refine ⟨by rw [le_div_iff₀ (by linarith)]; linarith, ?_, by linarith⟩
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- The `√a` piece: `∑ aK·√(2/y)√a ≤ √(2/y)·8∏ρ_H`. -/
theorem sumH_le (kh : KSumH) (d : ℕ) (hd : Nat.Coprime d 2) (y : ℝ) :
    ∑ a ∈ Icc 1 ⌊y⌋₊, aK (d * 2) a * (Real.sqrt (2 / y) * Real.sqrt a) ≤
      Real.sqrt (2 / y) * (8 * ∏ p ∈ d.primeFactors, rhoH p) := by
  have e : ∑ a ∈ Icc 1 ⌊y⌋₊, aK (d * 2) a * (Real.sqrt (2 / y) * Real.sqrt a) =
      Real.sqrt (2 / y) * ∑ a ∈ Icc 1 ⌊y⌋₊, aK (d * 2) a * Real.sqrt a := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (kh d ⌊y⌋₊ hd) (Real.sqrt_nonneg _)

/-! ## (3) The middle range -/

/-- `|hY(2d, x/d)| ≤ √(2d/x)·8∏ρ_H` for `x ≤ 10¹²`. -/
theorem hY_mid (hR : HC.RamareCited) (cv : ConvK) (kh : KSumH) (x : ℝ) (hx : 1 ≤ x)
    (hx2 : x ≤ 1e12) (d : ℕ) (hd1 : 1 ≤ d) (hd : Nat.Coprime d 2) :
    |hY (d * 2) (x / d)| ≤ Real.sqrt (2 / (x / d)) * (8 * ∏ p ∈ d.primeFactors, rhoH p) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hy0 : 0 < x / d := by positivity
  have hyx : x / d ≤ x := div_le_self (by linarith) (by exact_mod_cast hd1)
  refine (hY_le cv (d * 2) (by omega) (x / d) hy0.le
    (fun a => Real.sqrt (2 / (x / d)) * Real.sqrt a) fun a ha => ?_).trans
    (sumH_le kh d hd (x / d))
  obtain ⟨h1, h2, ha0⟩ := ratio_bounds (x / d) a ha
  rw [← sqrt_ratio _ _ hy0 ha0]
  exact mert_sqrt hR _ h1 (by linarith)

/-- `(√(2/(x/d)))² = 2d/x`. -/
theorem sq_sqrt_ratio (x : ℝ) (hx : 0 < x) (d : ℕ) (hd1 : 1 ≤ d) :
    Real.sqrt (2 / (x / d)) ^ 2 = 2 * d / x := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  rw [Real.sq_sqrt (by positivity)]
  field_simp

/-- **The `d`-th term, middle range**:
`|μ(d)/σ(d)²·hY²| ≤ (128/x)·μ(d)²d/σ(d)²·∏ρ_H²`. -/
theorem term_mid (hR : HC.RamareCited) (cv : ConvK) (kh : KSumH) (x : ℝ) (hx : 1 ≤ x)
    (hx2 : x ≤ 1e12) (d : ℕ) (hd1 : 1 ≤ d) (hd : Nat.Coprime d 2) :
    |mu d / sg d ^ 2 * hY (d * 2) (x / d) ^ 2| ≤
      128 / x * (mu d ^ 2 * (d : ℝ) / sg d ^ 2 * ∏ p ∈ d.primeFactors, rhoH p ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hs := sg_pos d hd1
  have hh := hY_mid hR cv kh x hx hx2 d hd1 hd
  have hP0 : 0 ≤ ∏ p ∈ d.primeFactors, rhoH p ^ 2 := by
    rw [Finset.prod_pow]
    positivity
  have hsq : hY (d * 2) (x / d) ^ 2 ≤
      (Real.sqrt (2 / (x / d)) * (8 * ∏ p ∈ d.primeFactors, rhoH p)) ^ 2 := by
    rw [← sq_abs (hY (d * 2) (x / d))]
    exact pow_le_pow_left₀ (abs_nonneg _) hh 2
  have e : (Real.sqrt (2 / (x / d)) * (8 * ∏ p ∈ d.primeFactors, rhoH p)) ^ 2 =
      128 * d / x * ∏ p ∈ d.primeFactors, rhoH p ^ 2 := by
    rw [mul_pow, sq_sqrt_ratio x hx0 d hd1, mul_pow, ← Finset.prod_pow]
    ring
  rw [e] at hsq
  have hmu := mu_abs_le_sq d
  rw [abs_mul, abs_div, abs_of_nonneg (sq_nonneg (hY (d * 2) (x / d))),
    abs_of_pos (pow_pos hs 2)]
  have hm0 : 0 ≤ |mu d| / sg d ^ 2 := by positivity
  calc |mu d| / sg d ^ 2 * hY (d * 2) (x / d) ^ 2
      ≤ |mu d| / sg d ^ 2 * (128 * d / x * ∏ p ∈ d.primeFactors, rhoH p ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hm0
    _ ≤ mu d ^ 2 / sg d ^ 2 * (128 * d / x * ∏ p ∈ d.primeFactors, rhoH p ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact div_le_div_of_nonneg_right hmu (by positivity)
    _ = 128 / x * (mu d ^ 2 * (d : ℝ) / sg d ^ 2 * ∏ p ∈ d.primeFactors, rhoH p ^ 2) := by
        ring

/-- **`|g₂(x)| ≤ (128/x)·DSum`** for `1 ≤ x ≤ 10¹²`, from a per-term bound. -/
theorem g_le_sum (an : Anna2) (x : ℝ) (hx : 1 ≤ x) (T : ℕ → ℝ)
    (hT : ∀ d, 1 ≤ d → Nat.Coprime d 2 →
      |mu d / sg d ^ 2 * hY (d * 2) (x / d) ^ 2| ≤ T d) :
    |HC.gYutto 2 x| ≤ ∑ d ∈ Icc 1 ⌊x⌋₊, if Nat.Coprime d 2 then T d else 0 := by
  rw [an x (by linarith)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  have hd1 := (Finset.mem_Icc.mp hd).1
  split_ifs with h
  · exact hT d hd1 h
  · simp

/-- **[YuttoMid2C] from the links**, PROVED. -/
theorem yuttoMid2C_of_links (an : Anna2) (cv : ConvK) (kh : KSumH) (dh : DSumH)
    (hR : HC.RamareCited) : M2LC.YuttoMid2C := by
  intro x hx1 hx2
  have hx : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have h1 := g_le_sum an x hx _ fun d hd1 hd => term_mid hR cv kh x hx (by linarith) d hd1 hd
  have e : (∑ d ∈ Icc 1 ⌊x⌋₊, if Nat.Coprime d 2 then
      128 / x * (mu d ^ 2 * (d : ℝ) / sg d ^ 2 * ∏ p ∈ d.primeFactors, rhoH p ^ 2) else 0) =
      128 / x * ∑ d ∈ Icc 1 ⌊x⌋₊, (if Nat.Coprime d 2 then
        mu d ^ 2 * (d : ℝ) / sg d ^ 2 * ∏ p ∈ d.primeFactors, rhoH p ^ 2 else 0) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by split_ifs <;> simp
  rw [e] at h1
  have h2 := dh x hx
  have hL := Real.log_nonneg hx
  have h3 : 128 / x * ∑ d ∈ Icc 1 ⌊x⌋₊, (if Nat.Coprime d 2 then
        mu d ^ 2 * (d : ℝ) / sg d ^ 2 * ∏ p ∈ d.primeFactors, rhoH p ^ 2 else 0) ≤
      128 / x * (8 + 4 * Real.log x) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : 128 / x * (8 + 4 * Real.log x) ≤ (2451.51 + 1225.752 * Real.log x) / x := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by nlinarith) hx0.le
  linarith

/-! ## (4) The large range -/

theorem exp_four_lt : Real.exp 4 < 55 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [e]
  have h0 := Real.exp_pos 1
  calc Real.exp 1 ^ 4 ≤ 2.7182818286 ^ 4 := pow_le_pow_left₀ h0.le h.le 4
    _ < 55 := by norm_num

/-- `log x ≤ (x/t)^{1/4}·log t` for `e⁴ ≤ t ≤ x`. -/
theorem log_le_root (x t : ℝ) (ht : 55 ≤ t) (htx : t ≤ x) :
    Real.log x ≤ Real.sqrt (Real.sqrt (x / t)) * Real.log t := by
  have ht0 : 0 < t := by linarith
  set r := Real.sqrt (Real.sqrt (x / t)) with hr
  have hxt : 1 ≤ x / t := by rw [le_div_iff₀ ht0]; linarith
  have hr1 : 1 ≤ r := by
    rw [hr]
    exact Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr hxt)
  have hr4 : r ^ 4 = x / t := by
    rw [hr, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
      Real.sq_sqrt (by linarith)]
  have hlt : 4 ≤ Real.log t := by
    rw [Real.le_log_iff_exp_le ht0]
    linarith [exp_four_lt]
  have hlx : Real.log x = Real.log t + 4 * Real.log r := by
    have hx0 : 0 < x := by linarith
    have h4 : 4 * Real.log r = Real.log (x / t) := by
      rw [← hr4, Real.log_pow]
      push_cast
      ring
    rw [h4, Real.log_div hx0.ne' ht0.ne']
    ring
  have hlr := Real.log_le_sub_one_of_pos (show 0 < r by linarith)
  rw [hlx]
  nlinarith

/-- **`|m(t)| ≤ √(2/t) + (0.03/log x)(x/t)^{1/4}`** for `1 ≤ t ≤ x`, `x ≥ 10¹⁰`. -/
theorem mert_big (hR : HC.RamareCited) (hM : RamareMarraki) (x t : ℝ) (hx : 10000000000 ≤ x)
    (ht : 1 ≤ t) (htx : t ≤ x) :
    |HC.mertF t| ≤ Real.sqrt (2 / t) + 0.03 / Real.log x * Real.sqrt (Real.sqrt (x / t)) := by
  have hLx : 0 < Real.log x := Real.log_pos (by linarith)
  have hQ : 0 ≤ 0.03 / Real.log x * Real.sqrt (Real.sqrt (x / t)) := by positivity
  rcases lt_or_ge t 11815 with h | h
  · have := mert_sqrt hR t ht (by linarith)
    linarith
  · have hm := hM t h
    have hLt : 0 < Real.log t := Real.log_pos (by linarith)
    have hl := log_le_root x t (by linarith) htx
    have h2 : 0.03 / Real.log t ≤ 0.03 / Real.log x * Real.sqrt (Real.sqrt (x / t)) := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hLt hLx]
      nlinarith
    have := Real.sqrt_nonneg (2 / t)
    linarith

/-- `√√(x/((x/d)/a)) = √√d·√√a`. -/
theorem root_ratio (x : ℝ) (hx : 0 < x) (d a : ℝ) (hd : 0 < d) (ha : 0 < a) :
    Real.sqrt (Real.sqrt (x / (x / d / a))) =
      Real.sqrt (Real.sqrt d) * Real.sqrt (Real.sqrt a) := by
  have e : x / (x / d / a) = d * a := by field_simp
  rw [e, Real.sqrt_mul hd.le, Real.sqrt_mul (Real.sqrt_nonneg _)]

/-- The `a^{1/4}` piece. -/
theorem sumQ_le (kq : KSumQ) (d : ℕ) (hd : Nat.Coprime d 2) (y c : ℝ) (hc : 0 ≤ c) :
    ∑ a ∈ Icc 1 ⌊y⌋₊, aK (d * 2) a * (c * Real.sqrt (Real.sqrt a)) ≤
      c * (4 * ∏ p ∈ d.primeFactors, rhoQ p) := by
  have e : ∑ a ∈ Icc 1 ⌊y⌋₊, aK (d * 2) a * (c * Real.sqrt (Real.sqrt a)) =
      c * ∑ a ∈ Icc 1 ⌊y⌋₊, aK (d * 2) a * Real.sqrt (Real.sqrt a) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (kq d ⌊y⌋₊ hd) hc

/-- `|hY(2d, x/d)| ≤ P + Q`, large range. -/
theorem hY_big (hR : HC.RamareCited) (hM : RamareMarraki) (cv : ConvK) (kh : KSumH)
    (kq : KSumQ) (x : ℝ) (hx : 10000000000 ≤ x) (d : ℕ) (hd1 : 1 ≤ d) (hd : Nat.Coprime d 2) :
    |hY (d * 2) (x / d)| ≤ Real.sqrt (2 / (x / d)) * (8 * ∏ p ∈ d.primeFactors, rhoH p) +
      0.03 / Real.log x * Real.sqrt (Real.sqrt d) * (4 * ∏ p ∈ d.primeFactors, rhoQ p) := by
  have hx0 : 0 < x := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hy0 : 0 < x / d := by positivity
  have hyx : x / d ≤ x := div_le_self (by linarith) (by exact_mod_cast hd1)
  have hLx : 0 < Real.log x := Real.log_pos (by linarith)
  set c := 0.03 / Real.log x * Real.sqrt (Real.sqrt d) with hc
  have hc0 : 0 ≤ c := by positivity
  refine (hY_le cv (d * 2) (by omega) (x / d) hy0.le
    (fun a => Real.sqrt (2 / (x / d)) * Real.sqrt a + c * Real.sqrt (Real.sqrt a))
    fun a ha => ?_).trans ?_
  · obtain ⟨h1, h2, ha0⟩ := ratio_bounds (x / d) a ha
    have hm := mert_big hR hM x (x / d / a) hx h1 (le_trans h2 hyx)
    rw [root_ratio x hx0 d a hd0 ha0, sqrt_ratio _ _ hy0 ha0] at hm
    rw [hc]
    linarith
  · have e : ∑ a ∈ Icc 1 ⌊x / d⌋₊, aK (d * 2) a *
        (Real.sqrt (2 / (x / d)) * Real.sqrt a + c * Real.sqrt (Real.sqrt a)) =
        ∑ a ∈ Icc 1 ⌊x / d⌋₊, aK (d * 2) a * (Real.sqrt (2 / (x / d)) * Real.sqrt a) +
          ∑ a ∈ Icc 1 ⌊x / d⌋₊, aK (d * 2) a * (c * Real.sqrt (Real.sqrt a)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [e]
    have h1 := sumH_le kh d hd (x / d)
    have h2 := sumQ_le kq d hd (x / d) c hc0
    have e2 : c * (4 * ∏ p ∈ d.primeFactors, rhoQ p) =
        0.03 / Real.log x * Real.sqrt (Real.sqrt d) * (4 * ∏ p ∈ d.primeFactors, rhoQ p) := by
      rw [hc]
    linarith

/-- **The `d`-th term, large range**: `≤ (1408/x)·[DSumH term] + (0.01584/log²x)·[DSumQ term]`. -/
theorem term_big (hR : HC.RamareCited) (hM : RamareMarraki) (cv : ConvK) (kh : KSumH)
    (kq : KSumQ) (x : ℝ) (hx : 10000000000 ≤ x) (d : ℕ) (hd1 : 1 ≤ d) (hd : Nat.Coprime d 2) :
    |mu d / sg d ^ 2 * hY (d * 2) (x / d) ^ 2| ≤
      1408 / x * (mu d ^ 2 * (d : ℝ) / sg d ^ 2 * ∏ p ∈ d.primeFactors, rhoH p ^ 2) +
      0.01584 / Real.log x ^ 2 *
        (mu d ^ 2 * Real.sqrt d / sg d ^ 2 * ∏ p ∈ d.primeFactors, rhoQ p ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hs := sg_pos d hd1
  have hLx : 0 < Real.log x := Real.log_pos (by linarith)
  have hh := hY_big hR hM cv kh kq x hx d hd1 hd
  set P := Real.sqrt (2 / (x / d)) * (8 * ∏ p ∈ d.primeFactors, rhoH p) with hP
  set Q := 0.03 / Real.log x * Real.sqrt (Real.sqrt d) * (4 * ∏ p ∈ d.primeFactors, rhoQ p)
    with hQ
  have hQ0 : 0 ≤ Q := by
    rw [hQ]
    have : 0 ≤ ∏ p ∈ d.primeFactors, rhoQ p := Finset.prod_nonneg fun p hp =>
      (rhoQ_pos p (Nat.prime_of_mem_primeFactors hp).one_lt.le).le
    positivity
  have hsq : hY (d * 2) (x / d) ^ 2 ≤ 11 * P ^ 2 + 1.1 * Q ^ 2 := by
    rw [← sq_abs (hY (d * 2) (x / d))]
    have h0 := abs_nonneg (hY (d * 2) (x / d))
    have : |hY (d * 2) (x / d)| ^ 2 ≤ (P + Q) ^ 2 := pow_le_pow_left₀ h0 hh 2
    nlinarith [sq_nonneg (10 * P - Q)]
  have eP : 11 * P ^ 2 = 1408 * d / x * ∏ p ∈ d.primeFactors, rhoH p ^ 2 := by
    rw [hP, mul_pow, sq_sqrt_ratio x hx0 d hd1, mul_pow, ← Finset.prod_pow]
    ring
  have eQ : 1.1 * Q ^ 2 = 0.01584 / Real.log x ^ 2 * Real.sqrt d *
      ∏ p ∈ d.primeFactors, rhoQ p ^ 2 := by
    rw [hQ, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _), ← Finset.prod_pow]
    field_simp
    ring
  rw [eP, eQ] at hsq
  have hmu := mu_abs_le_sq d
  rw [abs_mul, abs_div, abs_of_nonneg (sq_nonneg (hY (d * 2) (x / d))),
    abs_of_pos (pow_pos hs 2)]
  have hm0 : 0 ≤ |mu d| / sg d ^ 2 := by positivity
  have hR0 : 0 ≤ 1408 * d / x * ∏ p ∈ d.primeFactors, rhoH p ^ 2 +
      0.01584 / Real.log x ^ 2 * Real.sqrt d * ∏ p ∈ d.primeFactors, rhoQ p ^ 2 :=
    le_trans (sq_nonneg _) hsq
  calc |mu d| / sg d ^ 2 * hY (d * 2) (x / d) ^ 2
      ≤ |mu d| / sg d ^ 2 * (1408 * d / x * ∏ p ∈ d.primeFactors, rhoH p ^ 2 +
          0.01584 / Real.log x ^ 2 * Real.sqrt d * ∏ p ∈ d.primeFactors, rhoQ p ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hm0
    _ ≤ mu d ^ 2 / sg d ^ 2 * (1408 * d / x * ∏ p ∈ d.primeFactors, rhoH p ^ 2 +
          0.01584 / Real.log x ^ 2 * Real.sqrt d * ∏ p ∈ d.primeFactors, rhoQ p ^ 2) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hmu (by positivity)) hR0
    _ = _ := by ring

/-- `1408(8 + 4 log x) ≤ 3√x` for `x ≥ 10¹⁰`. -/
theorem log_poly_le (x : ℝ) (hx : 10000000000 ≤ x) :
    1408 * (8 + 4 * Real.log x) ≤ 3 * Real.sqrt x := by
  set s := Real.sqrt x with hs
  have hs5 : 100000 ≤ s := by
    rw [hs, show (100000 : ℝ) = Real.sqrt 10000000000 by
      rw [show (10000000000 : ℝ) = 100000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  have hx0 : 0 < x := by linarith
  have hlx : Real.log x = 2 * Real.log s := by
    rw [hs, Real.log_sqrt hx0.le]
    ring
  have h1 := Real.log_le_sub_one_of_pos (show 0 < s / 100000 by positivity)
  rw [Real.log_div (by linarith) (by norm_num)] at h1
  have h2 : Real.log 100000 ≤ 17 * 0.6931471808 := by
    have h := Real.log_le_log (by norm_num) (show (100000 : ℝ) ≤ 2 ^ 17 by norm_num)
    rw [Real.log_pow] at h
    have := Real.log_two_lt_d9
    push_cast at h
    linarith
  rw [hlx]
  nlinarith

/-- **[YuttoBig2C] from the links**, PROVED. -/
theorem yuttoBig2C_of_links (an : Anna2) (cv : ConvK) (kh : KSumH) (kq : KSumQ) (dh : DSumH)
    (dq : DSumQ) (hR : HC.RamareCited) (hM : RamareMarraki) : M2LC.YuttoBig2C := by
  intro x hx
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hLx : 0 < Real.log x := Real.log_pos (by linarith)
  have h1 := g_le_sum an x hx1 _ fun d hd1 hd => term_big hR hM cv kh kq x hx d hd1 hd
  have e : (∑ d ∈ Icc 1 ⌊x⌋₊, if Nat.Coprime d 2 then
      1408 / x * (mu d ^ 2 * (d : ℝ) / sg d ^ 2 * ∏ p ∈ d.primeFactors, rhoH p ^ 2) +
      0.01584 / Real.log x ^ 2 *
        (mu d ^ 2 * Real.sqrt d / sg d ^ 2 * ∏ p ∈ d.primeFactors, rhoQ p ^ 2) else 0) =
      1408 / x * ∑ d ∈ Icc 1 ⌊x⌋₊, (if Nat.Coprime d 2 then
        mu d ^ 2 * (d : ℝ) / sg d ^ 2 * ∏ p ∈ d.primeFactors, rhoH p ^ 2 else 0) +
      0.01584 / Real.log x ^ 2 * ∑ d ∈ Icc 1 ⌊x⌋₊, (if Nat.Coprime d 2 then
        mu d ^ 2 * Real.sqrt d / sg d ^ 2 * ∏ p ∈ d.primeFactors, rhoQ p ^ 2 else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun d _ => by split_ifs <;> simp
  rw [e] at h1
  have h2 : 1408 / x * ∑ d ∈ Icc 1 ⌊x⌋₊, (if Nat.Coprime d 2 then
        mu d ^ 2 * (d : ℝ) / sg d ^ 2 * ∏ p ∈ d.primeFactors, rhoH p ^ 2 else 0) ≤
      1408 / x * (8 + 4 * Real.log x) :=
    mul_le_mul_of_nonneg_left (dh x hx1) (by positivity)
  have h3 : 0.01584 / Real.log x ^ 2 * ∑ d ∈ Icc 1 ⌊x⌋₊, (if Nat.Coprime d 2 then
        mu d ^ 2 * Real.sqrt d / sg d ^ 2 * ∏ p ∈ d.primeFactors, rhoQ p ^ 2 else 0) ≤
      0.01584 / Real.log x ^ 2 * 2.4 :=
    mul_le_mul_of_nonneg_left (dq ⌊x⌋₊) (by positivity)
  have h4 : 1408 / x * (8 + 4 * Real.log x) ≤ 3 / Real.sqrt x := by
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
    have hxx : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt hx0.le).symm
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hx0 hsx]
    have := log_poly_le x hx
    calc 1408 * (8 + 4 * Real.log x) * Real.sqrt x ≤ 3 * Real.sqrt x * Real.sqrt x :=
          mul_le_mul_of_nonneg_right this hsx.le
      _ = 3 * x := by rw [mul_assoc, ← hxx]
  have h5 : 0.01584 / Real.log x ^ 2 * 2.4 ≤ 0.038128 / Real.log x ^ 2 := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  linarith

end Principia.Common.TernaryGoldbach.M2Y
