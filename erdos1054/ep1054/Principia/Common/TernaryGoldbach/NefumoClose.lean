/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.NefumoJoko
import Principia.Common.TernaryGoldbach.EasySup
import Principia.Common.TernaryGoldbach.EasyStar
import Principia.Common.TernaryGoldbach.EasyThird
import Principia.Common.TernaryGoldbach.EasyBand27
import Principia.Common.TernaryGoldbach.RegWHelf
import Principia.Common.TernaryGoldbach.ClowerTaylor
import Principia.Common.TernaryGoldbach.BandSharp
import Principia.Common.Chebyshev.Upper
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.ZetaValues

set_option autoImplicit false

/-!
# `prop:nefumo` CLOSED down to one link: six of the seven links of `NF.nefumoW_helf_final` PROVED

`NefumoJoko.nefumoW_helf_final` proves `RW.NefumoW η₊ η* η∘` (the major-arc main term of
`ternvin.tex`, `prop:nefumo`) from seven links. This file PROVES six of them and composes:

**`nefumoW_helf_closed : NF.ZvsL η* → RW.NefumoW η₊ η* η∘`** (and `jokoW_helf : NF.ZvsL η* →
NF.JokoW η₊ η*`). The one link that stays OPEN is `ZvsL η*`; its price is at the end.

| link | status | how | margin |
|---|---|---|---|
| `DPoint` (generic) | `dPoint` | `eq:mouche` with its exact coefficient | exact |
| `SummW η*` | `summW_star` | `η*(t)t⁴ ≤ 48/49⁴` | — |
| `Massacre` | `massacre` | finite Euler product, `ζ(2)`, kernel sum | `2.8264249 ≤ 2.82643` |
| `GatTail` | `gatTail` | divisor identity for `1/φ²`, odd/even tails | ratio `≤ 0.96` |
| `T3W η₊ η*` | `t3W_helf` | `L¹–L∞` split + band transfer | closes at `|η*|₂ ≥ 0.0817` |
| `ZvsL η₊` | `zvsL_plus` | `S(r) ≤ 9.68`; primes, 26 steps, `θ` | `12.71 ≤ 18.09` |
| `ZvsL η*` | **OPEN** | `L ≤ 0.7903` proved; mass side open | truth `×1.5` |

## The six proofs

* **[DPoint]** (`dPoint`, 795–858). `D = S − M − R = ∑_n g_n(e(an/q) − c(n))` (`dT_eq`), where
  `c(n) = φ(q)⁻¹∑_χ τ(χ̄)χ(a)χ*(n)` (`cf`) and the principal-character part of `err` cancels `M`
  exactly (`mT_add_rT`, `τ(χ₀) = μ(q)`). On `(n,q) = 1`, `c(n) = e(an/q)` (`cf_unit`,
  `GaussInduced.sum_char_gaussSum`). At `n = p^k`, `p | q = p^v m`: every `χ` with `χ*(p^k) ≠ 0`
  is induced from level `m` (`mem_range_of_ne`), `τ(χ̄) = μ(p^v)ψ̄(p^v)τ(ψ̄)`
  (`GaussInduced.gaussSum_changeLevel`), so the character sum is `0` if `p² | q` and
  `−φ(m)e(ap^{k−1}/m)` if `p ∥ q` (`sum_pow_le`); `|c(p^k)| ≤ φ(m)/φ(q) ≤ 1/(p−1)` (`cf_pow_le`),
  hence `|e − c| ≤ p/(p−1)` and `|D| ≤ d_q` (`term_le`, `hasSum_dq`).
* **[Summ] at `η*`** (`summW_star`): `η*(t)t⁴ ≤ 48/49⁴` (`etaStar_pow4_le`, the Hölder bound of
  `EN.etaStar_mul_le` three powers up), so `Λ(n)η*(n/x) ≤ (48x⁴/49⁴)/n²`.
* **[Massacre]** (`massacre`). `∑_{q ∈ Qs} μ²/φ² ≤ ∏_{p ≤ 3·10⁵}(1 + 1/(p−1)²)` (the finite Euler
  bound `sum_le_euler`: `∏(1 + f) = ∑_{T ⊆ P}∏_T f`), and `1 + 1/(p−1)² = (1 − p⁻²)⁻¹(1 +
  2/(p²(p−1)))` (`factor_split`). `∏(1 − p⁻²)⁻¹ ≤ ζ(2) = π²/6` (`prod_zeta_le`, the `N`-smooth
  Euler product); `∏_{p ≤ 13}(1 + x_p) = 3684682/2147145`; `∑_{13 < p ≤ 3000} x_p` is bounded by the
  integers coprime to `30030`, rounded up to `10⁻¹²` and summed in the kernel (`midK`,
  `1265997672`); beyond `3000` it telescopes (`sum_Ioc_x_le`). Certified `2.8264249` against
  `2.82643` (margin `5.2·10⁻⁶`; the full product is `2.8264195`).
* **[GatTail]** (`gatTail`). `|𝔖₃(N) − W_N(δ)| ≤ ∑_{missed q} μ²/φ²` (`gat_core`), a missed odd
  `q` has `qμ ≥ 1`, a missed even one `qμ ≥ 2`, `μ = max(1/r, |δ|/(δ₀r/2))` (`missed_ge`), and each
  tail is `≤ 2.15502μ` (`tail_all`): for `μ ≥ 1` the whole odd sum is `≤ 1.5145` (`odd_sum_le`); for
  `μ < 1` the divisor identity `1/φ(q)² = q⁻²∑_{d | q}H(d)` (`maj_eq_div`,
  `H = ∏_{p|d}(2p−1)/(p−1)²`) and one `U`-bound per divisor (`inner_le`:
  `∑_{m odd, m ≥ y} 1/m² ≤ min(5/4, 3/(4y))`) give `μ((5/4)·1.71154·6/5 − 1/2) = 2.0673μ`
  (`odd_tail_small`); evens reduce to odds (`maj_two_mul`).
* **[T3W] at `(η₊, η*)`** (`t3W_helf`). Per modulus `∫|η̂₊||η̂*| ≤ |η*|₁∫|η̂∘| + |η₊ − η∘|₂|η*|₂`
  (`t3_per_q`), `∫_{−w}^{w}|η̂∘| ≤ 1.49` (`int_ft_circ_le`: `0.86676` on `[−0.57, 0.57]`,
  `40/(2π|δ|)³` beyond; truth `1.0163`), `c₃ ≤ 4.84` (`c3_le`: `2∏_{p odd}(1 + (p−1)^{−3/2})`,
  truth `3.852`), `|η*|₂ ≥ 0.089` (`l2_star_ge`: variance on `(0, 0.072]` and the `t⁻⁸` tail),
  `|η₊|₂ ≥ 0.7996` (`l2_plus_ge`), `|η₊ − η∘|₂ ≤ 1.7999·10⁻⁴`: `4.84(0.025579·1.49 + 1.8·10⁻⁴|η*|₂)
  ≤ 2.82643·0.7996|η*|₂` once `|η*|₂ ≥ 0.0817`. This is the verifier's transfer: evidence at
  `(η∘, η*)`, moved to `η₊` by the proved band bound.
* **[ZvsL] at `η₊`** (`zvsL_plus`). `L_{r,δ₀}(η₊) ≤ 2S(r)|η₊|₂² ≤ 12.71` with **`S(r) ≤ 9.68`**
  (`sR_le_sharp`, truth `6.7988`; the old `DS.sR_le` gave `48.44`): `1/φ(q) = q⁻¹∑_{d|q}G(d)`,
  `∑_{q, d|q} 1/q ≤ hOdd/d`, `∑_d G(d)/d ≤ 1.27398·12/11`. And `Z_{η₊²,2}(x) ≥ 60.3·0.3` by
  `Z_ge` (generic: `Λ(p) = log p ≥ log(a₀x)` on the primes of `(a₀x, a_kx]`, a step minorant),
  26 steps of `1/20` on `[1/2, 9/5]` (`etaPlus_sq_ge`: `η∘ ≥ lo³(2−hi)³(1−c)`, `|h₂₀₀ − h| ≤
  2.7·10⁻⁴`), and `0.92079y ≤ θ(y) ≤ 1.11y` for `y ≥ 10²⁴` (`theta_ge_lin`, from
  `Common.Chebyshev.theta_ge_chebyshev` and `log y ≤ 4y^{1/4}`).

## What stays open: `ZvsL η*`, priced

Proved here: `L_{r,δ₀}(η*) ≤ 2·9.68·(2/49) ≤ 0.7903` (`lRD_star_le`), so the open link is
exactly one explicit inequality, **`0.7903·x ≤ ∑_n Λ(n)²η*(n/x)²` for `x ≥ 4.9·10²⁶`**
(`zvsL_star_of_mass` turns it into `NF.ZvsL η*`), and the generic `Z_ge` reduces that to a step
minorant. True values: `L(η*) ≈ 2·6.80·0.0217 = 0.295`, `Z_{η*²,2} ≈ 1.19` (with
`log(a₀x)` uniform at `a₀ = 0.002`). So `ZvsL η*` is TRUE with room `×1.5` even against the proved
`0.7903`, but `Z_ge` needs a step minorant of `η*²` on `~50` steps of `t ∈ [0.002, 0.05]` capturing
`≥ 66%` of it; crude one-piece minorants (`s²e^{−8s²}·9`, endpoint cells) reach only `0.22–0.27`.
Cheapest route found (checked numerically at `s = 0.3, 0.66, 1, 1.5`, agreement to `10⁻¹⁵`): since
`η₂ = η₁ ∗_M η₁`, `η*(t) = 4∫_s^{2s}(e^{−w²/2} − e^{−2w²})w⁻¹dw`, `s = 49t` (integrate
`HW.mconv_eta2` by parts on `[s, 2s]` and `[2s, 4s]`, then `y = 2w`); then `η*(t) ≥
4∫_{σ_{i+1}}^{2σ_i}` on `[σ_i, σ_{i+1}]` and a one-dimensional cell certificate (`~100` exponential
bounds at grid points, cumulative sums) — not built here. Tightening the other side instead:
`|η*|₂² ≤ 4(log 2)²|η₂|₁|φ|₂²/49 = 1.2774/49` (pointwise Cauchy–Schwarz and Fubini) would lower
the target to `0.505`.

## Reuse

`GaussInduced.gaussSum_changeLevel`, `GaussInduced.sum_char_gaussSum`, `PA.sm_eq`, `PA.tw_eq`,
`EulerProduct.prod_primesBelow_geometric_eq_tsum_smoothNumbers`, `hasSum_zeta_two`,
`IsMultiplicative.prodPrimeFactors_one_add_of_squarefree`, `SingularSeries.norm_sing3Arith_le_maj`,
`EN.normsB27_helf`, `BS.band_sharp`, `DS.lRD_le`, `DP.mardiQ_of`, `NF.madge_helf`,
`Common.Chebyshev.theta_ge_chebyshev`, `Common.Chebyshev.theta_le_cheb`.
-/
namespace Principia.Common.TernaryGoldbach.NC

open ArithmeticFunction Finset MeasureTheory
open scoped ArithmeticFunction

/-! ## The finite Euler bound -/

/-- **The finite Euler bound**: for `f ≥ 0` on a finite set `P`, the sum of `∏_{p | d} f(p)` over
any finite set of squarefree `d` whose primes lie in `P` is at most `∏_{p ∈ P}(1 + f(p))`
(`Finset.prod_one_add`; `d ↦ primeFactors d` is injective on squarefree numbers). -/
theorem sum_le_euler (f : ℕ → ℝ) (P : Finset ℕ) (hf : ∀ p ∈ P, 0 ≤ f p) (D : Finset ℕ)
    (hD : ∀ d ∈ D, Squarefree d ∧ d.primeFactors ⊆ P) :
    ∑ d ∈ D, ∏ p ∈ d.primeFactors, f p ≤ ∏ p ∈ P, (1 + f p) := by
  have hinj : Set.InjOn Nat.primeFactors (D : Set ℕ) := by
    intro a ha b hb hab
    rw [← Nat.prod_primeFactors_of_squarefree (hD a ha).1,
      ← Nat.prod_primeFactors_of_squarefree (hD b hb).1, hab]
  rw [Finset.prod_one_add]
  calc ∑ d ∈ D, ∏ p ∈ d.primeFactors, f p
      = ∑ T ∈ D.image Nat.primeFactors, ∏ p ∈ T, f p :=
        (Finset.sum_image (f := fun T : Finset ℕ => ∏ p ∈ T, f p) hinj).symm
    _ ≤ ∑ T ∈ P.powerset, ∏ p ∈ T, f p := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro T hT
          obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hT
          exact Finset.mem_powerset.mpr (hD d hd).2
        · intro T hT _
          exact Finset.prod_nonneg fun p hp => hf p (Finset.mem_powerset.mp hT hp)

/-- `φ(q) = ∏_{p | q}(p − 1)` on squarefree `q`, in `ℝ`. -/
theorem totient_sqfree {q : ℕ} (hq : Squarefree q) :
    (q.totient : ℝ) = ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
  have hφ : q.totient = ∏ p ∈ q.primeFactors, (p - 1) := by
    rw [Nat.totient_eq_div_primeFactors_mul, Nat.prod_primeFactors_of_squarefree hq,
      Nat.div_self (Nat.pos_of_ne_zero hq.ne_zero), one_mul]
  rw [hφ, Nat.cast_prod]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]

/-- `μ²/φ² = ∏_{p | q} 1/(p − 1)²` on squarefree `q`. -/
theorem sing3Maj_sqfree {q : ℕ} (hq : Squarefree q) :
    SingularSeries.sing3Maj q = ∏ p ∈ q.primeFactors, 1 / ((p : ℝ) - 1) ^ 2 := by
  have hμ : (moebius q : ℝ) ^ 2 = 1 := by exact_mod_cast moebius_sq_eq_one_of_squarefree hq
  unfold SingularSeries.sing3Maj
  rw [hμ, totient_sqfree hq, ← Finset.prod_pow]
  simp only [one_div, Finset.prod_inv_distrib]

/-! ## [Massacre] -/

/-- **`∑_{q ∈ S} μ²/φ² ≤ ∏_{p < Y}(1 + 1/(p−1)²)`** for any finite `S ⊆ [1, Y)` (the finite
Euler bound; stated for an arbitrary `S` so that no concrete `Finset` is ever unfolded). -/
theorem sum_maj_le_prod (S : Finset ℕ) (Y : ℕ) (hS : ∀ q ∈ S, 1 ≤ q ∧ q < Y) :
    ∑ q ∈ S, DS.cQ q / (q.totient : ℝ) ≤
      ∏ p ∈ Nat.primesBelow Y, (1 + 1 / ((p : ℝ) - 1) ^ 2) := by
  have h1 : ∑ q ∈ S, DS.cQ q / (q.totient : ℝ) =
      ∑ q ∈ S.filter Squarefree, ∏ p ∈ q.primeFactors, 1 / ((p : ℝ) - 1) ^ 2 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs with hq
    · rw [← sing3Maj_sqfree hq]
      unfold DS.cQ SingularSeries.sing3Maj
      ring
    · unfold DS.cQ
      rw [moebius_eq_zero_of_not_squarefree hq]
      simp
  rw [h1]
  refine sum_le_euler _ _ (fun p _ => by positivity) _ fun q hq => ?_
  obtain ⟨hq1, hsq⟩ := Finset.mem_filter.mp hq
  refine ⟨hsq, fun p hp => ?_⟩
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hpq := Nat.dvd_of_mem_primeFactors hp
  obtain ⟨hq0, hqY⟩ := hS q hq1
  have hple := Nat.le_of_dvd (by omega : 0 < q) hpq
  rw [Nat.mem_primesBelow]
  exact ⟨by omega, hpr⟩

/-- The moduli of `𝔐` lie in `[1, 3·10⁵]`. -/
theorem Qs_range : ∀ q ∈ NF.Qs, 1 ≤ q ∧ q < 300001 := by
  intro q hq
  obtain ⟨hq0, hqle⟩ := NF.mem_Qs hq
  have hg : Nat.gcd q 2 ≤ 2 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_right q 2)
  exact ⟨hq0, by omega⟩

/-- `1 + 1/(p−1)² = (1 − p⁻²)⁻¹·(1 + 2/(p²(p−1)))`. -/
theorem factor_split (p : ℕ) (hp : 2 ≤ p) :
    1 + 1 / ((p : ℝ) - 1) ^ 2 =
      (1 - 1 / (p : ℝ) ^ 2)⁻¹ * (1 + 2 / ((p : ℝ) ^ 2 * ((p : ℝ) - 1))) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hq : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have e : (1 - 1 / (p : ℝ) ^ 2) = ((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ 2 := by
    field_simp
  rw [e, inv_div]
  field_simp
  ring

/-- **`∏_{p < N}(1 − p⁻²)⁻¹ ≤ π²/6`**: the Euler product over the `N`-smooth numbers is a
sub-sum of `ζ(2)`. -/
theorem prod_zeta_le (N : ℕ) :
    ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ 2)⁻¹ ≤ Real.pi ^ 2 / 6 := by
  let f : ℕ →* ℝ :=
    { toFun := fun n => 1 / (n : ℝ) ^ 2
      map_one' := by simp
      map_mul' := fun m n => by
        simp only [Nat.cast_mul]
        rw [mul_pow, one_div_mul_one_div] }
  have hs : Summable (fun n : ℕ => f n) := Real.summable_one_div_nat_pow.mpr one_lt_two
  have h := EulerProduct.prod_primesBelow_geometric_eq_tsum_smoothNumbers hs N
  have h2 : ∑' m : N.smoothNumbers, f m ≤ ∑' m : ℕ, f m :=
    Summable.tsum_subtype_le (fun m : ℕ => f m) _
      (fun a => show (0 : ℝ) ≤ 1 / (a : ℝ) ^ 2 by positivity) hs
  have h3 : ∑' m : ℕ, f m = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq
  calc ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ 2)⁻¹ = ∏ p ∈ N.primesBelow, (1 - f p)⁻¹ := rfl
    _ = ∑' m : N.smoothNumbers, f m := h
    _ ≤ ∑' m : ℕ, f m := h2
    _ = Real.pi ^ 2 / 6 := h3

/-- The rounded middle terms `⌊2·10¹²/(n²(n−1))⌋ + 1` for `13 < n`, `(n, 30030) = 1`. -/
def gMid (n : ℕ) : ℕ :=
  if 13 < n ∧ Nat.gcd n 30030 = 1 then 2 * 10 ^ 12 / (n ^ 2 * (n - 1)) + 1 else 0

set_option maxRecDepth 100000 in
/-- The kernel sum of the rounded middle terms. -/
theorem midK : (∑ n ∈ Finset.range 3001, gMid n) = 1265997672 := by
  decide +kernel

/-- `2/(n²(n−1)) ≤ (⌊2·10¹²/(n²(n−1))⌋ + 1)/10¹²`. -/
theorem x_le_round (n : ℕ) (hn : 2 ≤ n) :
    2 / ((n : ℝ) ^ 2 * ((n : ℝ) - 1)) ≤
      ((2 * 10 ^ 12 / (n ^ 2 * (n - 1)) + 1 : ℕ) : ℝ) / 10 ^ 12 := by
  set D := n ^ 2 * (n - 1) with hD
  have hD0 : 0 < D := by
    rw [hD]
    exact Nat.mul_pos (by positivity) (by omega)
  have hDr : ((n : ℝ) ^ 2 * ((n : ℝ) - 1)) = (D : ℝ) := by
    rw [hD, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hlt : 2 * 10 ^ 12 < (2 * 10 ^ 12 / D + 1) * D := by
    have := Nat.lt_div_mul_add (a := 2 * 10 ^ 12) hD0
    nlinarith
  have hltr : (2 * 10 ^ 12 : ℝ) ≤ ((2 * 10 ^ 12 / D + 1 : ℕ) : ℝ) * (D : ℝ) := by
    exact_mod_cast hlt.le
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD0
  rw [hDr, div_le_div_iff₀ hDpos (by norm_num)]
  linarith

/-- `x_n ≤ 1/(n−1)² − 1/n²`, so `∑_{a < n ≤ b} x_n ≤ 1/a² − 1/b²`. -/
theorem sum_Ioc_x_le (a : ℕ) (ha : 2 ≤ a) :
    ∀ b : ℕ, a ≤ b → ∑ n ∈ Finset.Ioc a b, 2 / ((n : ℝ) ^ 2 * ((n : ℝ) - 1)) ≤
      1 / (a : ℝ) ^ 2 - 1 / (b : ℝ) ^ 2 := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_Ioc_succ_top hb]
    have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast le_trans ha hb
    have key : 2 / (((b + 1 : ℕ) : ℝ) ^ 2 * (((b + 1 : ℕ) : ℝ) - 1)) ≤
        1 / (b : ℝ) ^ 2 - 1 / ((b + 1 : ℕ) : ℝ) ^ 2 := by
      push_cast
      have hb0 : (0 : ℝ) < b := by linarith
      have e1 : (b : ℝ) + 1 - 1 = b := by ring
      rw [e1]
      have e2 : 1 / (b : ℝ) ^ 2 - 1 / ((b : ℝ) + 1) ^ 2 - 2 / (((b : ℝ) + 1) ^ 2 * (b : ℝ)) =
          1 / ((b : ℝ) ^ 2 * ((b : ℝ) + 1) ^ 2) := by
        field_simp
        ring
      have e3 : 0 ≤ 1 / ((b : ℝ) ^ 2 * ((b : ℝ) + 1) ^ 2) := by positivity
      linarith
    linarith

/-- A prime `p > 13` is coprime to `30030 = 2·3·5·7·11·13`. -/
theorem coprime_30030 (p : ℕ) (hp : p.Prime) (h13 : 13 < p) : Nat.gcd p 30030 = 1 := by
  have hc : Nat.Coprime p 30030 := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => ?_
    rw [show (30030 : ℕ) = 2 * 3 * 5 * 7 * 11 * 13 by norm_num] at h
    have hle : ∀ k : ℕ, 0 < k → k ≤ 13 → ¬ p ∣ k := fun k hk hk13 hd =>
      absurd (Nat.le_of_dvd hk hd) (by omega)
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
          · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
            · exact hle 2 (by norm_num) (by norm_num) h
            · exact hle 3 (by norm_num) (by norm_num) h
          · exact hle 5 (by norm_num) (by norm_num) h
        · exact hle 7 (by norm_num) (by norm_num) h
      · exact hle 11 (by norm_num) (by norm_num) h
    · exact hle 13 (by norm_num) (by norm_num) h
  exact hc

/-- `x_p = 2/(p²(p−1)) ≥ 0` for `p ≥ 2`. -/
theorem x_nonneg (p : ℕ) (hp : 2 ≤ p) : 0 ≤ 2 / ((p : ℝ) ^ 2 * ((p : ℝ) - 1)) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  positivity

/-- **The middle and the tail**: `∑_{13 < p < 3·10⁵ + 1} x_p ≤ 1265997672/10¹² + 1/3000²`. -/
theorem sum_x_le (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime ∧ 13 < p ∧ p < 300001) :
    ∑ p ∈ Q, 2 / ((p : ℝ) ^ 2 * ((p : ℝ) - 1)) ≤ 1265997672 / 10 ^ 12 + 1 / 3000 ^ 2 := by
  rw [← Finset.sum_filter_add_sum_filter_not Q (fun p => p ≤ 3000)]
  have hA : ∑ p ∈ Q.filter (fun p => p ≤ 3000), 2 / ((p : ℝ) ^ 2 * ((p : ℝ) - 1)) ≤
      1265997672 / 10 ^ 12 := by
    have hsub : Q.filter (fun p => p ≤ 3000) ⊆
        (Finset.range 3001).filter (fun n => 13 < n ∧ Nat.gcd n 30030 = 1) := by
      intro p hp
      obtain ⟨hpQ, hp3⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpr, h13, -⟩ := hQ p hpQ
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h13,
        coprime_30030 p hpr h13⟩
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun n hn _ =>
      x_nonneg n (by have := (Finset.mem_filter.mp hn).2.1; omega)) ?_
    have hr : ∀ n ∈ (Finset.range 3001).filter (fun n => 13 < n ∧ Nat.gcd n 30030 = 1),
        2 / ((n : ℝ) ^ 2 * ((n : ℝ) - 1)) ≤ (gMid n : ℝ) / 10 ^ 12 := by
      intro n hn
      have hc := (Finset.mem_filter.mp hn).2
      have hg : gMid n = 2 * 10 ^ 12 / (n ^ 2 * (n - 1)) + 1 := if_pos hc
      rw [hg]
      exact x_le_round n (by omega)
    refine le_trans (Finset.sum_le_sum hr) ?_
    rw [← Finset.sum_div, Finset.sum_filter]
    have e : ∑ n ∈ Finset.range 3001,
        (if 13 < n ∧ Nat.gcd n 30030 = 1 then (gMid n : ℝ) else 0) =
          ((∑ n ∈ Finset.range 3001, gMid n : ℕ) : ℝ) := by
      rw [Nat.cast_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      unfold gMid
      split_ifs <;> simp
    rw [e, midK]
    norm_num
  have hB : ∑ p ∈ Q.filter (fun p => ¬ p ≤ 3000), 2 / ((p : ℝ) ^ 2 * ((p : ℝ) - 1)) ≤
      1 / 3000 ^ 2 := by
    have hsub : Q.filter (fun p => ¬ p ≤ 3000) ⊆ Finset.Ioc 3000 300000 := by
      intro p hp
      obtain ⟨hpQ, hp3⟩ := Finset.mem_filter.mp hp
      obtain ⟨-, -, hlt⟩ := hQ p hpQ
      exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun n hn _ =>
      x_nonneg n (by have := (Finset.mem_Ioc.mp hn).1; omega)) ?_
    have h := sum_Ioc_x_le 3000 (by norm_num) 300000 (by norm_num)
    have h0 : (0 : ℝ) ≤ 1 / ((300000 : ℕ) : ℝ) ^ 2 := by positivity
    push_cast at h h0 ⊢
    linarith
  linarith

/-- `e^y ≤ 1/(1 − y)` for `y < 1`. -/
theorem exp_le_inv (y : ℝ) (hy : y < 1) : Real.exp y ≤ 1 / (1 - y) := by
  have h1 := Real.add_one_le_exp (-y)
  have hpos : 0 < 1 - y := by linarith
  rw [le_div_iff₀ hpos]
  have h2 : Real.exp y * Real.exp (-y) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h3 : 0 < Real.exp y := Real.exp_pos y
  nlinarith

/-- **`∏_{p < 3·10⁵ + 1}(1 + 1/(p−1)²) ≤ 2.82643`** (truth `2.8264194868`): `ζ(2)` times the
product of `1 + 2/(p²(p−1))`, exact for `p ≤ 13`, sieved by `30030` up to `3000`, telescoped
above. -/
theorem prod_massacre_le :
    ∏ p ∈ Nat.primesBelow 300001, (1 + 1 / ((p : ℝ) - 1) ^ 2) ≤ 2.82643 := by
  set P := Nat.primesBelow 300001 with hP
  have hmem : ∀ p ∈ P, p.Prime ∧ p < 300001 := fun p hp => by
    have := Nat.mem_primesBelow.mp hp
    exact ⟨this.2, this.1⟩
  have h1 : ∏ p ∈ P, (1 + 1 / ((p : ℝ) - 1) ^ 2) =
      (∏ p ∈ P, (1 - 1 / (p : ℝ) ^ 2)⁻¹) *
        ∏ p ∈ P, (1 + 2 / ((p : ℝ) ^ 2 * ((p : ℝ) - 1))) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p hp => factor_split p (hmem p hp).1.two_le
  have hz := prod_zeta_le 300001
  have hpos : ∀ p ∈ P, 0 ≤ 1 + 2 / ((p : ℝ) ^ 2 * ((p : ℝ) - 1)) := fun p hp => by
    have := x_nonneg p (hmem p hp).1.two_le
    linarith
  have hA : ∏ p ∈ P.filter (fun p => p ≤ 13), (1 + 2 / ((p : ℝ) ^ 2 * ((p : ℝ) - 1))) ≤
      3684682 / 2147145 := by
    have hsub : P.filter (fun p => p ≤ 13) ⊆ ({2, 3, 5, 7, 11, 13} : Finset ℕ) := by
      intro p hp
      obtain ⟨hpP, hp13⟩ := Finset.mem_filter.mp hp
      have hpr := (hmem p hpP).1
      interval_cases p <;> first | decide | (norm_num at hpr)
    refine le_trans (Finset.prod_le_prod_of_subset_of_one_le hsub
      (fun p hp => hpos p (Finset.mem_filter.mp hp).1) fun p hp _ => by
      have h2 : 2 ≤ p := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        omega
      have := x_nonneg p h2
      linarith) (le_of_eq ?_)
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_singleton]
    norm_num
  have hB : ∏ p ∈ P.filter (fun p => ¬ p ≤ 13), (1 + 2 / ((p : ℝ) ^ 2 * ((p : ℝ) - 1))) ≤
      Real.exp (1265997672 / 10 ^ 12 + 1 / 3000 ^ 2) := by
    have hS := sum_x_le (P.filter (fun p => ¬ p ≤ 13)) fun p hp => by
      obtain ⟨hpP, hp13⟩ := Finset.mem_filter.mp hp
      exact ⟨(hmem p hpP).1, by omega, (hmem p hpP).2⟩
    refine le_trans ?_ (Real.exp_le_exp.mpr hS)
    rw [Real.exp_sum]
    refine Finset.prod_le_prod (fun p hp => hpos p (Finset.mem_filter.mp hp).1) fun p _ => ?_
    have := Real.add_one_le_exp (2 / ((p : ℝ) ^ 2 * ((p : ℝ) - 1)))
    linarith
  have hsplit := Finset.prod_filter_mul_prod_filter_not P (fun p => p ≤ 13)
    (f := fun p => 1 + 2 / ((p : ℝ) ^ 2 * ((p : ℝ) - 1)))
  have hBpos : 0 ≤ ∏ p ∈ P.filter (fun p => ¬ p ≤ 13),
      (1 + 2 / ((p : ℝ) ^ 2 * ((p : ℝ) - 1))) :=
    Finset.prod_nonneg fun p hp => hpos p (Finset.mem_filter.mp hp).1
  have hE := exp_le_inv (1265997672 / 10 ^ 12 + 1 / 3000 ^ 2) (by norm_num)
  have hX : ∏ p ∈ P, (1 + 2 / ((p : ℝ) ^ 2 * ((p : ℝ) - 1))) ≤
      3684682 / 2147145 * (1 / (1 - (1265997672 / 10 ^ 12 + 1 / 3000 ^ 2))) := by
    rw [← hsplit]
    exact mul_le_mul hA (hB.trans hE) hBpos (by norm_num)
  have hXpos : 0 ≤ ∏ p ∈ P, (1 + 2 / ((p : ℝ) ^ 2 * ((p : ℝ) - 1))) :=
    Finset.prod_nonneg hpos
  have hπ : Real.pi ^ 2 / 6 ≤ 3.141593 ^ 2 / 6 := by
    have := Real.pi_lt_d6
    have := Real.pi_pos
    nlinarith
  rw [h1]
  calc (∏ p ∈ P, (1 - 1 / (p : ℝ) ^ 2)⁻¹) * ∏ p ∈ P, (1 + 2 / ((p : ℝ) ^ 2 * ((p : ℝ) - 1)))
      ≤ (3.141593 ^ 2 / 6) *
          (3684682 / 2147145 * (1 / (1 - (1265997672 / 10 ^ 12 + 1 / 3000 ^ 2)))) :=
        mul_le_mul (hz.trans hπ) hX hXpos (by norm_num)
    _ ≤ 2.82643 := by norm_num

/-- **[Massacre] PROVED** (`eq:massacre`, 5581): `∑_{q ∈ Qs} μ²(q)/φ(q)² ≤ 2.82643`. -/
theorem massacre : NF.Massacre :=
  le_trans (sum_maj_le_prod NF.Qs 300001 Qs_range) prod_massacre_le

/-! ## [GatTail]: tail sums of `μ²/φ²` over the odd moduli -/

/-- `∑_{k ∈ [k₀, K)} 1/(2k+1)² ≤ 1/(4k₀) − 1/(4K)` (`1/(2k+1)² ≤ 1/(4k(k+1))`, telescoping). -/
theorem sum_Ico_odd_le (k0 : ℕ) (hk0 : 1 ≤ k0) :
    ∀ K : ℕ, k0 ≤ K → ∑ k ∈ Finset.Ico k0 K, 1 / (2 * (k : ℝ) + 1) ^ 2 ≤
      1 / (4 * (k0 : ℝ)) - 1 / (4 * (K : ℝ)) := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base => simp
  | succ K hK ih =>
    rw [Finset.sum_Ico_succ_top hK]
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast le_trans hk0 hK
    have key : 1 / (2 * (K : ℝ) + 1) ^ 2 ≤
        1 / (4 * (K : ℝ)) - 1 / (4 * ((K + 1 : ℕ) : ℝ)) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

/-- **Odd `m ≥ 2k₀ + 1`, `k₀ ≥ 1`**: `∑ 1/m² ≤ 1/(4k₀)`. -/
theorem sum_odd_inv_sq_le (A : Finset ℕ) (k0 : ℕ) (hk0 : 1 ≤ k0)
    (hA : ∀ m ∈ A, Odd m ∧ 2 * k0 + 1 ≤ m) :
    ∑ m ∈ A, 1 / (m : ℝ) ^ 2 ≤ 1 / (4 * (k0 : ℝ)) := by
  set K := max k0 (A.sup id + 1) with hKdef
  have hK : k0 ≤ K := le_max_left _ _
  have hsub : A ⊆ (Finset.Ico k0 K).image (fun k : ℕ => (2 * k + 1 : ℕ)) := by
    intro m hm
    obtain ⟨⟨k, hk⟩, hmk⟩ := hA m hm
    have hle : m ≤ A.sup id := Finset.le_sup (f := id) hm
    have hK2 : A.sup id + 1 ≤ K := le_max_right _ _
    exact Finset.mem_image.mpr ⟨k, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hk.symm⟩
  have hinj : Set.InjOn (fun k : ℕ => 2 * k + 1) (Finset.Ico k0 K : Set ℕ) :=
    fun a _ b _ h => by
      simp only at h
      omega
  have h0 : (0 : ℝ) ≤ 1 / (4 * (K : ℝ)) := by positivity
  calc ∑ m ∈ A, 1 / (m : ℝ) ^ 2
      ≤ ∑ m ∈ (Finset.Ico k0 K).image (fun k : ℕ => (2 * k + 1 : ℕ)), 1 / ((m : ℕ) : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = ∑ k ∈ Finset.Ico k0 K, 1 / (((2 * k + 1 : ℕ) : ℝ)) ^ 2 :=
        Finset.sum_image (f := fun m : ℕ => 1 / (m : ℝ) ^ 2) hinj
    _ = ∑ k ∈ Finset.Ico k0 K, 1 / (2 * (k : ℝ) + 1) ^ 2 := by push_cast; rfl
    _ ≤ 1 / (4 * (k0 : ℝ)) - 1 / (4 * (K : ℝ)) := sum_Ico_odd_le k0 hk0 K hK
    _ ≤ 1 / (4 * (k0 : ℝ)) := by linarith

/-- **`U(y) ≤ 3/(4y)` for `y > 1`**: odd `m` with `mν ≥ 1`, `0 < ν < 1`, have `∑ 1/m² ≤ (3/4)ν`. -/
theorem U_small (A : Finset ℕ) (ν : ℝ) (hν0 : 0 < ν) (hν1 : ν < 1)
    (hA : ∀ m ∈ A, Odd m ∧ 1 ≤ (m : ℝ) * ν) : ∑ m ∈ A, 1 / (m : ℝ) ^ 2 ≤ 3 / 4 * ν := by
  set k0 := ⌈(1 / ν - 1) / 2⌉₊ with hk0def
  have hinv : 1 < 1 / ν := by rw [lt_div_iff₀ hν0]; linarith
  have hk0 : 1 ≤ k0 := Nat.one_le_ceil_iff.mpr (by linarith)
  have hk0r : (1 / ν - 1) / 2 ≤ (k0 : ℝ) := Nat.le_ceil _
  have hA' : ∀ m ∈ A, Odd m ∧ 2 * k0 + 1 ≤ m := by
    intro m hm
    obtain ⟨hodd, hmν⟩ := hA m hm
    obtain ⟨k, hk⟩ := hodd
    refine ⟨⟨k, hk⟩, ?_⟩
    have hm : 1 / ν ≤ (m : ℝ) := by rw [div_le_iff₀ hν0]; linarith
    have hmk : (m : ℝ) = 2 * (k : ℝ) + 1 := by rw [hk]; push_cast; ring
    have hkk : (1 / ν - 1) / 2 ≤ (k : ℝ) := by linarith
    have : k0 ≤ k := Nat.ceil_le.mpr hkk
    omega
  refine le_trans (sum_odd_inv_sq_le A k0 hk0 hA') ?_
  have hk1 : (1 : ℝ) ≤ k0 := by exact_mod_cast hk0
  rw [div_le_iff₀ (by positivity)]
  have hmul : ν * (1 / ν) = 1 := by field_simp
  rcases le_or_gt ν (1 / 3) with h3 | h3
  · nlinarith
  · nlinarith

/-- **`U ≤ 5/4`**: for odd positive `m`, `∑ 1/m² ≤ 1 + 1/4`. -/
theorem U_all (A : Finset ℕ) (hA : ∀ m ∈ A, Odd m) : ∑ m ∈ A, 1 / (m : ℝ) ^ 2 ≤ 5 / 4 := by
  rw [← Finset.sum_filter_add_sum_filter_not A (fun m => m = 1)]
  have h1 : ∑ m ∈ A.filter (fun m => m = 1), 1 / (m : ℝ) ^ 2 ≤ 1 := by
    have hsub : A.filter (fun m => m = 1) ⊆ {1} := fun m hm => by
      rw [Finset.mem_singleton]
      exact (Finset.mem_filter.mp hm).2
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity) ?_
    simp
  have h2 := sum_odd_inv_sq_le (A.filter (fun m => ¬ m = 1)) 1 le_rfl fun m hm => by
    obtain ⟨hmA, hm1⟩ := Finset.mem_filter.mp hm
    obtain ⟨k, hk⟩ := hA m hmA
    exact ⟨⟨k, hk⟩, by omega⟩
  have e : (1 : ℝ) / (4 * ((1 : ℕ) : ℝ)) = 1 / 4 := by norm_num
  rw [e] at h2
  linarith
/-- `∑_{a < n ≤ b} 1/(n−1)² ≤ 1/(a−1) − 1/(b−1)` (`1/(n−1)² ≤ 1/(n−2) − 1/(n−1)`). -/
theorem sum_Ioc_inv_sq_le (a : ℕ) (ha : 2 ≤ a) :
    ∀ b : ℕ, a ≤ b → ∑ n ∈ Finset.Ioc a b, 1 / ((n : ℝ) - 1) ^ 2 ≤
      1 / ((a : ℝ) - 1) - 1 / ((b : ℝ) - 1) := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_Ioc_succ_top hb]
    have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast le_trans ha hb
    have key : 1 / (((b + 1 : ℕ) : ℝ) - 1) ^ 2 ≤
        1 / ((b : ℝ) - 1) - 1 / (((b + 1 : ℕ) : ℝ) - 1) := by
      push_cast
      rw [show (b : ℝ) + 1 - 1 = b by ring, div_sub_div _ _ (by linarith) (by positivity),
        div_le_div_iff₀ (by positivity) (by nlinarith)]
      nlinarith
    linarith

/-- **The odd-prime product**: for `0 ≤ f(p) ≤ c/(p−1)²` beyond `13`, over any set of odd primes,
`∏(1 + f(p)) ≤ ∏_{p ∈ {3,5,7,11,13}}(1 + f(p))·e^{c/12}`. -/
theorem odd_prod_le (f : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hf0 : ∀ p, 2 ≤ p → 0 ≤ f p)
    (hfc : ∀ p, 13 < p → f p ≤ c / ((p : ℝ) - 1) ^ 2) :
    ∏ p ∈ P, (1 + f p) ≤ (∏ p ∈ ({3, 5, 7, 11, 13} : Finset ℕ), (1 + f p)) * Real.exp (c / 12) := by
  have hpos : ∀ p ∈ P, 0 ≤ 1 + f p := fun p hp => by
    have := hf0 p (hP p hp).1.two_le
    linarith
  rw [← Finset.prod_filter_mul_prod_filter_not P (fun p => p ≤ 13)]
  have hA : ∏ p ∈ P.filter (fun p => p ≤ 13), (1 + f p) ≤
      ∏ p ∈ ({3, 5, 7, 11, 13} : Finset ℕ), (1 + f p) := by
    have hsub : P.filter (fun p => p ≤ 13) ⊆ ({3, 5, 7, 11, 13} : Finset ℕ) := by
      intro p hp
      obtain ⟨hpP, hp13⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpr, hp2⟩ := hP p hpP
      interval_cases p <;> first | decide | exact absurd rfl hp2 | (norm_num at hpr)
    refine Finset.prod_le_prod_of_subset_of_one_le hsub
      (fun p hp => hpos p (Finset.mem_filter.mp hp).1) fun p hp _ => ?_
    have h2 : 2 ≤ p := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      omega
    have := hf0 p h2
    linarith
  have hB : ∏ p ∈ P.filter (fun p => ¬ p ≤ 13), (1 + f p) ≤ Real.exp (c / 12) := by
    set M := P.sup id with hM
    have hsum : ∑ p ∈ P.filter (fun p => ¬ p ≤ 13), f p ≤ c / 12 := by
      have hsub : P.filter (fun p => ¬ p ≤ 13) ⊆ Finset.Ioc 13 (max 13 M) := by
        intro p hp
        obtain ⟨hpP, hp13⟩ := Finset.mem_filter.mp hp
        have hle : p ≤ M := Finset.le_sup (f := id) hpP
        exact Finset.mem_Ioc.mpr ⟨by omega, le_trans hle (le_max_right _ _)⟩
      have h1 : ∑ p ∈ P.filter (fun p => ¬ p ≤ 13), f p ≤
          ∑ p ∈ P.filter (fun p => ¬ p ≤ 13), c / ((p : ℝ) - 1) ^ 2 :=
        Finset.sum_le_sum fun p hp => hfc p (by have := (Finset.mem_filter.mp hp).2; omega)
      have h2 : ∑ p ∈ P.filter (fun p => ¬ p ≤ 13), c / ((p : ℝ) - 1) ^ 2 ≤
          ∑ n ∈ Finset.Ioc 13 (max 13 M), c / ((n : ℝ) - 1) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity
      have hM13 : (13 : ℝ) ≤ ((max 13 M : ℕ) : ℝ) := by exact_mod_cast le_max_left 13 M
      have h5 : 0 ≤ 1 / (((max 13 M : ℕ) : ℝ) - 1) := by
        apply div_nonneg zero_le_one
        linarith
      have h3 : ∑ n ∈ Finset.Ioc 13 (max 13 M), 1 / ((n : ℝ) - 1) ^ 2 ≤ 1 / 12 := by
        have h := sum_Ioc_inv_sq_le 13 (by norm_num) (max 13 M) (le_max_left _ _)
        have e : ((13 : ℕ) : ℝ) - 1 = 12 := by norm_num
        rw [e] at h
        linarith
      have h4 : ∑ n ∈ Finset.Ioc 13 (max 13 M), c / ((n : ℝ) - 1) ^ 2 =
          c * ∑ n ∈ Finset.Ioc 13 (max 13 M), 1 / ((n : ℝ) - 1) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun n _ => by ring
      have h6 := mul_le_mul_of_nonneg_left h3 hc
      calc ∑ p ∈ P.filter (fun p => ¬ p ≤ 13), f p ≤ _ := h1
        _ ≤ _ := h2
        _ = _ := h4
        _ ≤ c * (1 / 12) := h6
        _ = c / 12 := by ring
    refine le_trans ?_ (Real.exp_le_exp.mpr hsum)
    rw [Real.exp_sum]
    refine Finset.prod_le_prod (fun p hp => hpos p (Finset.mem_filter.mp hp).1) fun p _ => ?_
    have := Real.add_one_le_exp (f p)
    linarith
  have hApos : 0 ≤ ∏ p ∈ ({3, 5, 7, 11, 13} : Finset ℕ), (1 + f p) :=
    Finset.prod_nonneg fun p hp => by
      have h2 : 2 ≤ p := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        omega
      have := hf0 p h2
      linarith
  have hBpos : 0 ≤ ∏ p ∈ P.filter (fun p => ¬ p ≤ 13), (1 + f p) :=
    Finset.prod_nonneg fun p hp => hpos p (Finset.mem_filter.mp hp).1
  exact mul_le_mul hA hB hBpos hApos

/-- The odd primes below `M + 1`. -/
def oddPrimes (M : ℕ) : Finset ℕ := (Finset.range (M + 1)).filter (fun p => p.Prime ∧ p ≠ 2)

theorem mem_oddPrimes_of_dvd {q p M : ℕ} (hq : Odd q) (hq0 : 1 ≤ q) (hqM : q ≤ M)
    (hp : p ∈ q.primeFactors) : p ∈ oddPrimes M := by
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hpq := Nat.dvd_of_mem_primeFactors hp
  have hle := Nat.le_of_dvd (by omega) hpq
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpr, fun h2 => ?_⟩
  rw [h2] at hpq
  exact (Nat.not_even_iff_odd.mpr hq) (even_iff_two_dvd.mpr hpq)

/-- `sing3Maj q = 0` off the squarefree numbers. -/
theorem maj_of_not_sqfree {q : ℕ} (hq : ¬ Squarefree q) : SingularSeries.sing3Maj q = 0 := by
  unfold SingularSeries.sing3Maj
  rw [moebius_eq_zero_of_not_squarefree hq]
  simp

/-- **The large-`μ` case**: `∑_{q odd} μ²/φ² ≤ 1.3883·12/11 ≤ 1.5145`. -/
theorem odd_sum_le (s : Finset ℕ) (hs : ∀ q ∈ s, Odd q) :
    ∑ q ∈ s, SingularSeries.sing3Maj q ≤ 1.5145 := by
  set M := s.sup id with hM
  have h1 : ∑ q ∈ s, SingularSeries.sing3Maj q =
      ∑ q ∈ s.filter Squarefree, ∏ p ∈ q.primeFactors, 1 / ((p : ℝ) - 1) ^ 2 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs with hq
    · exact sing3Maj_sqfree hq
    · exact maj_of_not_sqfree hq
  rw [h1]
  have hE := sum_le_euler (fun p => 1 / ((p : ℝ) - 1) ^ 2) (oddPrimes M) (fun p _ => by positivity)
    (s.filter Squarefree) fun q hq => by
      obtain ⟨hqs, hsq⟩ := Finset.mem_filter.mp hq
      refine ⟨hsq, fun p hp => ?_⟩
      exact mem_oddPrimes_of_dvd (hs q hqs) (Nat.pos_of_ne_zero hsq.ne_zero)
        (Finset.le_sup (f := id) hqs) hp
  have hO := odd_prod_le (fun p => 1 / ((p : ℝ) - 1) ^ 2) 1 zero_le_one (oddPrimes M)
    (fun p hp => (Finset.mem_filter.mp hp).2) (fun p _ => by positivity) (fun p _ => le_rfl)
  have hexp := exp_le_inv (1 / 12) (by norm_num)
  have hS : ∏ p ∈ ({3, 5, 7, 11, 13} : Finset ℕ), (1 + 1 / ((p : ℝ) - 1) ^ 2) =
      1842341 / 1327104 := by
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
    norm_num
  rw [hS] at hO
  have hE0 : 0 ≤ Real.exp (1 / 12) := (Real.exp_pos _).le
  calc _ ≤ _ := hE
    _ ≤ 1842341 / 1327104 * Real.exp (1 / 12) := hO
    _ ≤ 1842341 / 1327104 * (1 / (1 - 1 / 12)) := mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ ≤ 1.5145 := by norm_num
/-- `h(p) = (2p − 1)/(p − 1)² = (p/(p − 1))² − 1`. -/
noncomputable def hfun (p : ℕ) : ℝ := (2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2

theorem hfun_nonneg (p : ℕ) (hp : 2 ≤ p) : 0 ≤ hfun p := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  unfold hfun
  apply div_nonneg (by linarith) (sq_nonneg _)

theorem one_add_hfun (p : ℕ) (hp : 2 ≤ p) : 1 + hfun p = ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  unfold hfun
  field_simp
  ring

/-- **The divisor identity** on squarefree `q`: `1/φ(q)² = q⁻²∑_{d | q} H(d)`,
`H = ∏_{p | d} h(p)` (`(q/φ(q))² = ∏_{p | q}(1 + h(p))`). -/
theorem maj_eq_div {q : ℕ} (hq : Squarefree q) :
    SingularSeries.sing3Maj q =
      (∑ d ∈ q.divisors, ArithmeticFunction.prodPrimeFactors hfun d) / (q : ℝ) ^ 2 := by
  have hq0 : q ≠ 0 := hq.ne_zero
  have h1 : ∑ d ∈ q.divisors, ArithmeticFunction.prodPrimeFactors hfun d =
      ∏ p ∈ q.primeFactors, (1 + ArithmeticFunction.prodPrimeFactors hfun p) :=
    (ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_add_of_squarefree
      (ArithmeticFunction.IsMultiplicative.prodPrimeFactors hfun) hq).symm
  have h2 : ∀ p ∈ q.primeFactors, 1 + ArithmeticFunction.prodPrimeFactors hfun p =
      ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    rw [ArithmeticFunction.prodPrimeFactors_apply hpr.ne_zero, hpr.primeFactors,
      Finset.prod_singleton]
    exact one_add_hfun p hpr.two_le
  have hprod : ∏ p ∈ q.primeFactors, (p : ℝ) = q := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hq]
  have hφ0 : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq0)).ne'
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
  have hμ : (moebius q : ℝ) ^ 2 = 1 := by exact_mod_cast moebius_sq_eq_one_of_squarefree hq
  rw [h1, Finset.prod_congr rfl h2, Finset.prod_pow, Finset.prod_div_distrib, hprod,
    ← totient_sqfree hq]
  unfold SingularSeries.sing3Maj
  rw [hμ]
  field_simp

/-- `H(d)/d = ∏_{p | d} h(p)/p` on squarefree `d`. -/
theorem H_div {d : ℕ} (hd : Squarefree d) :
    ArithmeticFunction.prodPrimeFactors hfun d / (d : ℝ) =
      ∏ p ∈ d.primeFactors, hfun p / (p : ℝ) := by
  have hprod : ∏ p ∈ d.primeFactors, (p : ℝ) = d := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd]
  rw [ArithmeticFunction.prodPrimeFactors_apply hd.ne_zero, Finset.prod_div_distrib, hprod]

theorem H_nonneg {d : ℕ} : 0 ≤ ArithmeticFunction.prodPrimeFactors hfun d := by
  rcases Nat.eq_zero_or_pos d with h | h
  · rw [h, ArithmeticFunction.map_zero]
  · rw [ArithmeticFunction.prodPrimeFactors_apply h.ne']
    exact Finset.prod_nonneg fun p hp => hfun_nonneg p (Nat.prime_of_mem_primeFactors hp).two_le

/-- **One divisor's share**: for `μ < 1`, `d ≥ 1`, and odd `q` with `qμ ≥ 1`,
`∑_{q, d | q} 1/q² ≤ (5/4)μ/d − [d = 1]μ/2` (`U_small` when `dμ < 1`, `U_all` otherwise). -/
theorem inner_le (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ < 1) (s : Finset ℕ)
    (hs : ∀ q ∈ s, Odd q ∧ 1 ≤ (q : ℝ) * μ) (d : ℕ) (hd : 1 ≤ d) :
    ∑ q ∈ s.filter (d ∣ ·), 1 / (q : ℝ) ^ 2 ≤
      5 / 4 * μ / d - (if d = 1 then μ / 2 else 0) := by
  set F := s.filter (d ∣ ·) with hF
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hinj : Set.InjOn (fun q : ℕ => q / d) (F : Set ℕ) := by
    intro a ha b hb hab
    have hda := (Finset.mem_filter.mp ha).2
    have hdb := (Finset.mem_filter.mp hb).2
    simp only at hab
    rw [← Nat.mul_div_cancel' hda, ← Nat.mul_div_cancel' hdb, hab]
  have e : ∑ q ∈ F, 1 / (q : ℝ) ^ 2 =
      1 / (d : ℝ) ^ 2 * ∑ m ∈ F.image (fun q : ℕ => q / d), 1 / ((m : ℕ) : ℝ) ^ 2 := by
    rw [Finset.sum_image hinj, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hdq := (Finset.mem_filter.mp hq).2
    have hc : (q : ℝ) = (d : ℝ) * ((q / d : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' hdq).symm
    rw [hc]
    field_simp
  have hA : ∀ m ∈ F.image (fun q : ℕ => q / d), Odd m ∧ 1 ≤ (m : ℝ) * ((d : ℝ) * μ) := by
    intro m hm
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hqs, hdq⟩ := Finset.mem_filter.mp hq
    obtain ⟨hodd, hqμ⟩ := hs q hqs
    have hqe : q = d * (q / d) := (Nat.mul_div_cancel' hdq).symm
    refine ⟨?_, ?_⟩
    · rw [hqe] at hodd
      exact (Nat.odd_mul.mp hodd).2
    · have hc : (q : ℝ) = (d : ℝ) * ((q / d : ℕ) : ℝ) := by exact_mod_cast hqe
      calc (1 : ℝ) ≤ (q : ℝ) * μ := hqμ
        _ = ((q / d : ℕ) : ℝ) * ((d : ℝ) * μ) := by rw [hc]; ring
  have hodd : ∀ m ∈ F.image (fun q : ℕ => q / d), Odd m := fun m hm => (hA m hm).1
  rw [e]
  rcases lt_or_ge ((d : ℝ) * μ) 1 with hdμ | hdμ
  · have hU := U_small _ ((d : ℝ) * μ) (by positivity) hdμ hA
    have h1 : 1 / (d : ℝ) ^ 2 * ∑ m ∈ F.image (fun q : ℕ => q / d), 1 / ((m : ℕ) : ℝ) ^ 2 ≤
        1 / (d : ℝ) ^ 2 * (3 / 4 * ((d : ℝ) * μ)) :=
      mul_le_mul_of_nonneg_left hU (by positivity)
    have e2 : 1 / (d : ℝ) ^ 2 * (3 / 4 * ((d : ℝ) * μ)) = 3 / 4 * μ / d := by
      field_simp
    rw [e2] at h1
    split_ifs with h1d
    · subst h1d
      norm_num at h1 ⊢
      linarith
    · have : 3 / 4 * μ / (d : ℝ) ≤ 5 / 4 * μ / d :=
        div_le_div_of_nonneg_right (by linarith) hd0.le
      linarith
  · have hd1 : d ≠ 1 := by
      rintro rfl
      norm_num at hdμ
      linarith
    rw [if_neg hd1, sub_zero]
    have hU := U_all _ hodd
    have h1 : 1 / (d : ℝ) ^ 2 * ∑ m ∈ F.image (fun q : ℕ => q / d), 1 / ((m : ℕ) : ℝ) ^ 2 ≤
        1 / (d : ℝ) ^ 2 * (5 / 4) :=
      mul_le_mul_of_nonneg_left hU (by positivity)
    have h2 : 1 / (d : ℝ) ^ 2 * (5 / 4) ≤ 5 / 4 * μ / d := by
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hd0]
      nlinarith
    linarith
/-- `H(1) = 1`. -/
theorem H_one : ArithmeticFunction.prodPrimeFactors hfun 1 = 1 := by
  rw [ArithmeticFunction.prodPrimeFactors_apply one_ne_zero, Nat.primeFactors_one,
    Finset.prod_empty]

/-- `h(p)/p ≤ 2/(p − 1)²`. -/
theorem hfun_div_le (p : ℕ) (hp : 2 ≤ p) : hfun p / (p : ℝ) ≤ 2 / ((p : ℝ) - 1) ^ 2 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  unfold hfun
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hsq : 0 ≤ ((p : ℝ) - 1) ^ 2 := sq_nonneg _
  nlinarith

/-- **The small-`μ` odd tail** (`0 < μ < 1`): `∑_{q odd, qμ ≥ 1} μ²/φ² ≤ 2.15502μ`, by the divisor
identity, one `U`-bound per divisor, and the Euler bound `∑ H(d)/d ≤ 1.71155·6/5`. -/
theorem odd_tail_small (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ < 1) (s : Finset ℕ)
    (hs : ∀ q ∈ s, Odd q ∧ 1 ≤ (q : ℝ) * μ) :
    ∑ q ∈ s, SingularSeries.sing3Maj q ≤ 2.15502 * μ := by
  set s' := s.filter Squarefree with hs'
  have hs's : ∀ q ∈ s', Odd q ∧ 1 ≤ (q : ℝ) * μ := fun q hq => hs q (Finset.mem_filter.mp hq).1
  have h0 : ∑ q ∈ s, SingularSeries.sing3Maj q = ∑ q ∈ s', SingularSeries.sing3Maj q := by
    rw [hs', Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs with h
    · rfl
    · exact maj_of_not_sqfree h
  rw [h0]
  rcases s'.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty]
    positivity
  set D := s'.biUnion Nat.divisors with hD
  have h1 : ∑ q ∈ s', SingularSeries.sing3Maj q =
      ∑ q ∈ s', ∑ d ∈ q.divisors,
        ArithmeticFunction.prodPrimeFactors hfun d * (1 / (q : ℝ) ^ 2) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [maj_eq_div (Finset.mem_filter.mp hq).2, ← Finset.sum_mul, div_eq_mul_one_div]
  have h2 : ∑ q ∈ s', ∑ d ∈ q.divisors,
      ArithmeticFunction.prodPrimeFactors hfun d * (1 / (q : ℝ) ^ 2) =
      ∑ d ∈ D, ∑ q ∈ s'.filter (d ∣ ·),
        ArithmeticFunction.prodPrimeFactors hfun d * (1 / (q : ℝ) ^ 2) := by
    refine Finset.sum_comm' fun q d => ?_
    constructor
    · rintro ⟨hq, hd⟩
      exact ⟨Finset.mem_filter.mpr ⟨hq, Nat.dvd_of_mem_divisors hd⟩,
        Finset.mem_biUnion.mpr ⟨q, hq, hd⟩⟩
    · rintro ⟨hq, -⟩
      obtain ⟨hqs, hdq⟩ := Finset.mem_filter.mp hq
      exact ⟨hqs, Nat.mem_divisors.mpr ⟨hdq, (Finset.mem_filter.mp hqs).2.ne_zero⟩⟩
  have hDpos : ∀ d ∈ D, 1 ≤ d := fun d hd => by
    obtain ⟨q, -, hdq⟩ := Finset.mem_biUnion.mp hd
    exact Nat.pos_of_mem_divisors hdq
  have h3 : ∀ d ∈ D, ∑ q ∈ s'.filter (d ∣ ·),
      ArithmeticFunction.prodPrimeFactors hfun d * (1 / (q : ℝ) ^ 2) ≤
        ArithmeticFunction.prodPrimeFactors hfun d *
          (5 / 4 * μ / d - (if d = 1 then μ / 2 else 0)) := by
    intro d hd
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (inner_le μ hμ hμ1 s' hs's d (hDpos d hd)) H_nonneg
  have h1D : (1 : ℕ) ∈ D := by
    obtain ⟨q, hq⟩ := hne
    exact Finset.mem_biUnion.mpr ⟨q, hq,
      Nat.one_mem_divisors.mpr (Finset.mem_filter.mp hq).2.ne_zero⟩
  have h4 : ∑ d ∈ D, ArithmeticFunction.prodPrimeFactors hfun d *
      (5 / 4 * μ / d - (if d = 1 then μ / 2 else 0)) =
      5 / 4 * μ * ∑ d ∈ D, ArithmeticFunction.prodPrimeFactors hfun d / d - μ / 2 := by
    have e : ∀ d ∈ D, ArithmeticFunction.prodPrimeFactors hfun d *
        (5 / 4 * μ / d - (if d = 1 then μ / 2 else 0)) =
        5 / 4 * μ * (ArithmeticFunction.prodPrimeFactors hfun d / d) -
          ArithmeticFunction.prodPrimeFactors hfun d * (if d = 1 then μ / 2 else 0) :=
      fun d _ => by ring
    rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_eq_single 1]
    · rw [if_pos rfl, H_one, one_mul]
    · intro d _ hd
      rw [if_neg hd, mul_zero]
    · intro h
      exact absurd h1D h
  set M := s'.sup id with hM
  have hD' : ∀ d ∈ D, Squarefree d ∧ d.primeFactors ⊆ oddPrimes M := by
    intro d hd
    obtain ⟨q, hq, hdq⟩ := Finset.mem_biUnion.mp hd
    obtain ⟨hqs, hsq⟩ := Finset.mem_filter.mp hq
    have hdvd := Nat.dvd_of_mem_divisors hdq
    refine ⟨hsq.squarefree_of_dvd hdvd, fun p hp => ?_⟩
    have hpq := Nat.primeFactors_mono hdvd hsq.ne_zero hp
    exact mem_oddPrimes_of_dvd (hs q hqs).1 (Nat.pos_of_ne_zero hsq.ne_zero)
      (Finset.le_sup (f := id) hq) hpq
  have h5 : ∑ d ∈ D, ArithmeticFunction.prodPrimeFactors hfun d / d ≤
      24360696499 / 14233190400 * (1 / (1 - 1 / 6)) := by
    rw [Finset.sum_congr rfl fun d hd => H_div (hD' d hd).1]
    have hE := sum_le_euler (fun p => hfun p / (p : ℝ)) (oddPrimes M)
      (fun p hp => div_nonneg (hfun_nonneg p ((Finset.mem_filter.mp hp).2.1.two_le))
        (Nat.cast_nonneg _)) D hD'
    have hO := odd_prod_le (fun p => hfun p / (p : ℝ)) 2 (by norm_num) (oddPrimes M)
      (fun p hp => (Finset.mem_filter.mp hp).2)
      (fun p hp => div_nonneg (hfun_nonneg p hp) (Nat.cast_nonneg _))
      (fun p hp => hfun_div_le p (by omega))
    have hS : ∏ p ∈ ({3, 5, 7, 11, 13} : Finset ℕ), (1 + hfun p / (p : ℝ)) =
        24360696499 / 14233190400 := by
      rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
      unfold hfun
      norm_num
    rw [hS] at hO
    have hexp := exp_le_inv (2 / 12) (by norm_num)
    calc _ ≤ _ := hE
      _ ≤ 24360696499 / 14233190400 * Real.exp (2 / 12) := hO
      _ ≤ 24360696499 / 14233190400 * (1 / (1 - 2 / 12)) :=
          mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ = 24360696499 / 14233190400 * (1 / (1 - 1 / 6)) := by norm_num
  rw [h1, h2]
  refine le_trans (Finset.sum_le_sum h3) ?_
  rw [h4]
  have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 5 / 4 * μ)
  have h7 : 5 / 4 * μ * (24360696499 / 14233190400 * (1 / (1 - 1 / 6))) - μ / 2 ≤
      2.15502 * μ := by nlinarith
  linarith

/-- **The odd tail** at every `μ > 0`: `∑_{q odd, qμ ≥ 1} μ²/φ² ≤ 2.15502μ`. -/
theorem odd_tail (μ : ℝ) (hμ : 0 < μ) (s : Finset ℕ) (hs : ∀ q ∈ s, Odd q ∧ 1 ≤ (q : ℝ) * μ) :
    ∑ q ∈ s, SingularSeries.sing3Maj q ≤ 2.15502 * μ := by
  rcases lt_or_ge μ 1 with h | h
  · exact odd_tail_small μ hμ h s hs
  · have := odd_sum_le s fun q hq => (hs q hq).1
    nlinarith

/-- `μ²/φ²` at `2m` equals its value at `m` for odd `m`. -/
theorem maj_two_mul {m : ℕ} (hm : Odd m) :
    SingularSeries.sing3Maj (2 * m) = SingularSeries.sing3Maj m := by
  have hc : Nat.Coprime 2 m := (Nat.coprime_comm.mp (Nat.coprime_two_right.mpr hm))
  unfold SingularSeries.sing3Maj
  rw [isMultiplicative_moebius.map_mul_of_coprime hc, moebius_apply_prime Nat.prime_two,
    Nat.totient_two_mul_of_odd hm]
  push_cast
  ring

/-- **The even tail**: `∑_{q even, qμ ≥ 2} μ²/φ² ≤ 2.15502μ` (`q = 2m`, `m` odd). -/
theorem even_tail (μ : ℝ) (hμ : 0 < μ) (s : Finset ℕ)
    (hs : ∀ q ∈ s, Even q ∧ 2 ≤ (q : ℝ) * μ) :
    ∑ q ∈ s, SingularSeries.sing3Maj q ≤ 2.15502 * μ := by
  set s' := s.filter Squarefree with hs'
  have h0 : ∑ q ∈ s, SingularSeries.sing3Maj q = ∑ q ∈ s', SingularSeries.sing3Maj q := by
    rw [hs', Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs with h
    · rfl
    · exact maj_of_not_sqfree h
  have hhalf : ∀ q ∈ s', q = 2 * (q / 2) ∧ Odd (q / 2) := by
    intro q hq
    obtain ⟨hqs, hsq⟩ := Finset.mem_filter.mp hq
    obtain ⟨k, hk⟩ := (hs q hqs).1
    have hq2 : q = 2 * (q / 2) := by omega
    refine ⟨hq2, ?_⟩
    rcases Nat.even_or_odd (q / 2) with he | ho
    · exfalso
      obtain ⟨j, hj⟩ := he
      have h4 : 2 * 2 ∣ q := ⟨j, by omega⟩
      exact absurd (Nat.isUnit_iff.mp (hsq 2 h4)) (by norm_num)
    · exact ho
  have hinj : Set.InjOn (fun q : ℕ => q / 2) (s' : Set ℕ) := by
    intro a ha b hb hab
    simp only at hab
    rw [(hhalf a ha).1, (hhalf b hb).1, hab]
  have h1 : ∑ q ∈ s', SingularSeries.sing3Maj q =
      ∑ m ∈ s'.image (fun q : ℕ => q / 2), SingularSeries.sing3Maj m := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun q hq => ?_
    obtain ⟨hq2, hodd⟩ := hhalf q hq
    conv_lhs => rw [hq2]
    exact maj_two_mul hodd
  rw [h0, h1]
  refine odd_tail μ hμ _ fun m hm => ?_
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨hq2, hodd⟩ := hhalf q hq
  refine ⟨hodd, ?_⟩
  have hqμ := (hs q (Finset.mem_filter.mp hq).1).2
  have hc : (q : ℝ) = 2 * ((q / 2 : ℕ) : ℝ) := by exact_mod_cast hq2
  rw [hc] at hqμ
  linarith

/-- **Both tails**: every finite set of missed moduli carries at most `4.31004μ`. -/
theorem tail_all (μ : ℝ) (hμ : 0 < μ) (s : Finset ℕ)
    (hs : ∀ q ∈ s, (Odd q → 1 ≤ (q : ℝ) * μ) ∧ (Even q → 2 ≤ (q : ℝ) * μ)) :
    ∑ q ∈ s, SingularSeries.sing3Maj q ≤ 4.31004 * μ := by
  rw [← Finset.sum_filter_add_sum_filter_not s Odd]
  have h1 := odd_tail μ hμ (s.filter Odd) fun q hq => by
    obtain ⟨hqs, hodd⟩ := Finset.mem_filter.mp hq
    exact ⟨hodd, (hs q hqs).1 hodd⟩
  have h2 := even_tail μ hμ (s.filter fun q => ¬ Odd q) fun q hq => by
    obtain ⟨hqs, hodd⟩ := Finset.mem_filter.mp hq
    have he : Even q := Nat.not_odd_iff_even.mp hodd
    exact ⟨he, (hs q hqs).2 he⟩
  linarith
/-- **What the arcs miss** (`q ≥ 1`, `μ = max(1/r, |δ|/(δ₀r/2))`): a modulus outside the window
has `qμ ≥ 1` (odd) or `qμ ≥ 2` (even), i.e. `q ≥ R` resp. `q ≥ 2R`, `R = 1/μ`. -/
theorem missed_ge (S : Finset ℕ)
    (hS : ∀ q, 1 ≤ q → q ∉ S → (Odd q → 150000 < q) ∧ (Even q → 300000 < q))
    (δ : ℝ) (q : ℕ) (hq1 : 1 ≤ q)
    (hq : ¬ (q ∈ S ∧ δ ∈ Set.Ioc (-NF.wq q) (NF.wq q))) :
    (Odd q → 1 ≤ (q : ℝ) * max (1 / 150000) (|δ| / 600000)) ∧
      (Even q → 2 ≤ (q : ℝ) * max (1 / 150000) (|δ| / 600000)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hm1 : (1 / 150000 : ℝ) ≤ max (1 / 150000) (|δ| / 600000) := le_max_left _ _
  have hm2 : |δ| / 600000 ≤ max (1 / 150000) (|δ| / 600000) := le_max_right _ _
  by_cases hqS : q ∈ S
  · have hδ : δ ∉ Set.Ioc (-NF.wq q) (NF.wq q) := fun h => hq ⟨hqS, h⟩
    have hw0 : 0 ≤ NF.wq q := NF.wq_nonneg q
    have habs : NF.wq q ≤ |δ| := by
      rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hδ
      rcases hδ with h | h
      · rw [abs_of_nonpos (by linarith)]
        linarith
      · rw [abs_of_pos (by linarith)]
        linarith
    have hwq : NF.wq q * q = (Nat.gcd q 2 : ℝ) * 600000 := by
      unfold NF.wq
      field_simp
    have hq2 : (Nat.gcd q 2 : ℝ) * 600000 ≤ |δ| * q := by
      rw [← hwq]
      exact mul_le_mul_of_nonneg_right habs hq0.le
    refine ⟨fun hodd => ?_, fun heven => ?_⟩
    · have hg : Nat.gcd q 2 = 1 := Nat.coprime_two_right.mpr hodd
      rw [hg, Nat.cast_one] at hq2
      have : (1 : ℝ) ≤ (q : ℝ) * (|δ| / 600000) := by
        rw [mul_div_assoc']
        rw [le_div_iff₀ (by norm_num)]
        linarith
      exact le_trans this (mul_le_mul_of_nonneg_left hm2 hq0.le)
    · have hg : Nat.gcd q 2 = 2 := Nat.gcd_eq_right (even_iff_two_dvd.mp heven)
      rw [hg, Nat.cast_ofNat] at hq2
      have : (2 : ℝ) ≤ (q : ℝ) * (|δ| / 600000) := by
        rw [mul_div_assoc']
        rw [le_div_iff₀ (by norm_num)]
        linarith
      exact le_trans this (mul_le_mul_of_nonneg_left hm2 hq0.le)
  · obtain ⟨ho, he⟩ := hS q hq1 hqS
    refine ⟨fun hodd => ?_, fun heven => ?_⟩
    · have h1 := ho hodd
      have h1r : (150000 : ℝ) < q := by exact_mod_cast h1
      have : (1 : ℝ) ≤ (q : ℝ) * (1 / 150000) := by
        rw [mul_one_div, le_div_iff₀ (by norm_num)]
        linarith
      exact le_trans this (mul_le_mul_of_nonneg_left hm1 hq0.le)
    · have h1 := he heven
      have h1r : (300000 : ℝ) < q := by exact_mod_cast h1
      have : (2 : ℝ) ≤ (q : ℝ) * (1 / 150000) := by
        rw [mul_one_div, le_div_iff₀ (by norm_num)]
        linarith
      exact le_trans this (mul_le_mul_of_nonneg_left hm1 hq0.le)

/-- **[GatTail] for any window set `S`** whose missed moduli exceed `r` (odd) resp. `2r` (even). -/
theorem gat_core (S : Finset ℕ)
    (hS : ∀ q, 1 ≤ q → q ∉ S → (Odd q → 150000 < q) ∧ (Even q → 300000 < q))
    (N : ℕ) (hN : 1 ≤ N) (δ : ℝ) :
    |SingularSeries.sing3 N - ∑ q ∈ S,
        (if δ ∈ Set.Ioc (-NF.wq q) (NF.wq q) then SingularSeries.sing3Local q N else 0)| ≤
      4.31004 * max (1 / 150000) (|δ| / 600000) := by
  set μ := max (1 / 150000 : ℝ) (|δ| / 600000) with hμdef
  have hμ : 0 < μ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  set k : ℕ → ℝ := fun q =>
    if q ∈ S ∧ δ ∈ Set.Ioc (-NF.wq q) (NF.wq q) then SingularSeries.sing3Local q N else 0
    with hkdef
  have hk0 : ∀ q ∉ S, k q = 0 := fun q hq => by
    simp only [hkdef]
    rw [if_neg fun h => hq h.1]
  have hwin : ∑ q ∈ S, (if δ ∈ Set.Ioc (-NF.wq q) (NF.wq q) then
      SingularSeries.sing3Local q N else 0) = ∑' q, k q := by
    rw [tsum_eq_sum hk0]
    refine Finset.sum_congr rfl fun q hq => ?_
    simp only [hkdef]
    by_cases h : δ ∈ Set.Ioc (-NF.wq q) (NF.wq q)
    · rw [if_pos h, if_pos ⟨hq, h⟩]
    · rw [if_neg h, if_neg fun h' => h h'.2]
  have hT : Summable (fun q => SingularSeries.sing3Arith N q) :=
    (SingularSeries.sing3_summable N hN).of_norm
  have hk : Summable k := summable_of_ne_finset_zero hk0
  set c : ℕ → ℝ := fun q =>
    if q ∈ S ∧ δ ∈ Set.Ioc (-NF.wq q) (NF.wq q) then 0 else SingularSeries.sing3Maj q
    with hcdef
  have hc0 : ∀ q, 0 ≤ c q := fun q => by
    simp only [hcdef]
    split_ifs
    · exact le_rfl
    · exact SingularSeries.sing3Maj_nonneg q
  have hcs : Summable c := by
    refine Summable.of_nonneg_of_le hc0 (fun q => ?_) SingularSeries.sing3Maj_summable
    simp only [hcdef]
    split_ifs
    · exact SingularSeries.sing3Maj_nonneg q
    · exact le_rfl
  have hpt : ∀ q, ‖SingularSeries.sing3Arith N q - k q‖ ≤ c q := by
    intro q
    simp only [hkdef, hcdef]
    split_ifs with h
    · rw [SingularSeries.sing3Arith_apply, sub_self, norm_zero]
    · rw [sub_zero]
      exact SingularSeries.norm_sing3Arith_le_maj N q
  unfold SingularSeries.sing3
  rw [hwin, ← hT.tsum_sub hk, ← Real.norm_eq_abs]
  refine le_trans (tsum_of_norm_bounded hcs.hasSum hpt) ?_
  refine hcs.tsum_le_of_sum_le fun t => ?_
  set t' := t.filter (fun q => ¬ (q ∈ S ∧ δ ∈ Set.Ioc (-NF.wq q) (NF.wq q)) ∧ 1 ≤ q)
    with ht'
  have e : ∑ q ∈ t, c q = ∑ q ∈ t', SingularSeries.sing3Maj q := by
    rw [ht', Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [hcdef]
    by_cases h : q ∈ S ∧ δ ∈ Set.Ioc (-NF.wq q) (NF.wq q)
    · rw [if_pos h, if_neg fun h' => h'.1 h]
    · rw [if_neg h]
      by_cases hq1 : 1 ≤ q
      · rw [if_pos ⟨h, hq1⟩]
      · rw [if_neg fun h' => hq1 h'.2]
        have hq0 : q = 0 := by omega
        rw [hq0]
        unfold SingularSeries.sing3Maj
        simp
  rw [e]
  refine tail_all μ hμ t' fun q hq => ?_
  obtain ⟨-, hnot, hq1⟩ := Finset.mem_filter.mp hq
  exact missed_ge S hS δ q hq1 hnot

/-- The moduli missing from `Qs` exceed `r` (odd) resp. `2r` (even). -/
theorem Qs_missed : ∀ q, 1 ≤ q → q ∉ NF.Qs → (Odd q → 150000 < q) ∧ (Even q → 300000 < q) := by
  intro q hq1 hqS
  refine ⟨fun hodd => ?_, fun heven => ?_⟩
  · by_contra hle
    apply hqS
    unfold NF.Qs DS.oddQ
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq1, by omega⟩,
      hodd⟩)
  · by_contra hle
    apply hqS
    unfold NF.Qs DS.evenQ
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq1, by omega⟩,
      heven⟩)

/-- **[GatTail] PROVED** (`eq:gat1o`, `eq:gat1e`, 5713–5726): what the arcs miss of `𝔖₃(N)` at `δ`
is at most `4.31004·max(1/r, |δ|/(δ₀r/2))`. The sharp ratio is `0.656`, at `|δ| = δ₀r/2`. -/
theorem gatTail : NF.GatTail := by
  intro N hN δ
  unfold NF.win
  exact gat_core NF.Qs Qs_missed N hN δ
/-! ## [T3W]: the weights of the `R₊M₊M*` term -/

/-- `y¹⁰e^{−y²/2} ≤ 3840` (`u⁵/5! ≤ e^u` at `u = y²/2`). -/
theorem pow10_exp_le (y : ℝ) : y ^ 10 * Real.exp (-y ^ 2 / 2) ≤ 3840 := by
  have hu : 0 ≤ y ^ 2 / 2 := by positivity
  have h := Real.pow_div_factorial_le_exp (y ^ 2 / 2) hu 5
  have hf : ((5 : ℕ).factorial : ℝ) = 120 := by norm_num [Nat.factorial]
  rw [hf] at h
  have h10 : y ^ 10 ≤ 3840 * Real.exp (y ^ 2 / 2) := by
    have e : y ^ 10 = 3840 * ((y ^ 2 / 2) ^ 5 / 120) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left h (by norm_num)
  have hE : Real.exp (y ^ 2 / 2) * Real.exp (-y ^ 2 / 2) = 1 := by
    rw [← Real.exp_add, show y ^ 2 / 2 + -y ^ 2 / 2 = 0 by ring, Real.exp_zero]
  have hE0 : 0 < Real.exp (-y ^ 2 / 2) := Real.exp_pos _
  calc y ^ 10 * Real.exp (-y ^ 2 / 2) ≤ 3840 * Real.exp (y ^ 2 / 2) * Real.exp (-y ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right h10 hE0.le
    _ = 3840 := by rw [mul_assoc, hE, mul_one]

/-- **`η*(t)·t⁸ ≤ 3840/49⁸`** for `t ≥ 0`. -/
theorem etaStar_pow8_le {t : ℝ} (ht : 0 ≤ t) : HW.etaStar t * t ^ 8 ≤ 3840 / 49 ^ 8 := by
  have hM : (0 : ℝ) ≤ 3840 / 49 ^ 8 := by positivity
  rcases ht.eq_or_lt with h0 | hpos
  · rw [← h0]
    simpa using hM
  set s := 49 * t with hs_def
  have hs : 0 < s := by positivity
  have hst : t = s / 49 := by rw [hs_def]; ring
  have heq : HW.etaStar t * t ^ 8 =
      ∫ y in s..4 * s, HW.eta2 (s / y) * HW.phi y / y * (s / 49) ^ 8 := by
    rw [HW.etaStar, ← hs_def, HW.mconv_eta2 HW.phi hs, intervalIntegral.integral_mul_const, hst]
  rw [heq]
  have hc : ContinuousOn (fun y => HW.eta2 (s / y) * (s / y ^ 2)) (Set.Ioi 0) :=
    (HW.eta2_div_contOn hs).mul (continuousOn_const.div (continuousOn_pow 2)
      fun y hy => pow_ne_zero 2 (Set.mem_Ioi.mp hy).ne')
  have hc2 : ContinuousOn (fun y => HW.eta2 (s / y) * HW.phi y / y * (s / 49) ^ 8)
      (Set.Ioi 0) :=
    ((((HW.eta2_div_contOn hs).mul HW.continuous_phi.continuousOn).div continuousOn_id
      fun y hy => (Set.mem_Ioi.mp hy).ne').mul continuousOn_const)
  have hsub : Set.uIcc s (4 * s) ⊆ Set.Ioi 0 := HW.uIcc_pos hs (by linarith)
  have hmono : ∫ y in s..4 * s, HW.eta2 (s / y) * HW.phi y / y * (s / 49) ^ 8 ≤
      ∫ y in s..4 * s, 3840 / 49 ^ 8 * (HW.eta2 (s / y) * (s / y ^ 2)) := by
    refine intervalIntegral.integral_mono_on (by linarith) ((hc2.mono hsub).intervalIntegrable)
      (((hc.mono hsub).intervalIntegrable).const_mul _) fun y hy => ?_
    have hy0 : 0 < y := lt_of_lt_of_le hs hy.1
    have hsy : s ≤ y := hy.1
    have he0 : 0 ≤ HW.eta2 (s / y) * (s / y ^ 2) :=
      mul_nonneg (HW.eta2_nonneg _) (div_nonneg hs.le (sq_nonneg y))
    have hr : HW.eta2 (s / y) * HW.phi y / y * (s / 49) ^ 8 =
        HW.eta2 (s / y) * (s / y ^ 2) * (y ^ 3 * s ^ 7 * Real.exp (-y ^ 2 / 2)) / 49 ^ 8 := by
      rw [HW.phi]
      field_simp
    have hs7 : s ^ 7 ≤ y ^ 7 := pow_le_pow_left₀ hs.le hsy 7
    have hE0 : 0 < Real.exp (-y ^ 2 / 2) := Real.exp_pos _
    have hG : y ^ 3 * s ^ 7 * Real.exp (-y ^ 2 / 2) ≤ 3840 := by
      have h1 : y ^ 3 * s ^ 7 ≤ y ^ 10 := by
        have := mul_le_mul_of_nonneg_left hs7 (pow_nonneg hy0.le 3)
        nlinarith
      have h2 := mul_le_mul_of_nonneg_right h1 hE0.le
      linarith [pow10_exp_le y]
    rw [hr]
    calc HW.eta2 (s / y) * (s / y ^ 2) * (y ^ 3 * s ^ 7 * Real.exp (-y ^ 2 / 2)) / 49 ^ 8
        ≤ HW.eta2 (s / y) * (s / y ^ 2) * 3840 / 49 ^ 8 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hG he0) (by norm_num)
      _ = 3840 / 49 ^ 8 * (HW.eta2 (s / y) * (s / y ^ 2)) := by ring
  rw [intervalIntegral.integral_const_mul, EN.int_eta2_sy2 hs, mul_one] at hmono
  exact hmono

/-- `∫_T^∞ η* ≤ (3840/49⁸)·T⁻⁷/7`. -/
theorem int_star_tail (T : ℝ) (hT : 0 < T) :
    ∫ t in Set.Ioi T, HW.etaStar t ≤ 3840 / 49 ^ 8 * (T ^ (-7 : ℝ) / 7) := by
  have hI : IntegrableOn (fun t : ℝ => 3840 / 49 ^ 8 * t ^ (-8 : ℝ)) (Set.Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hT).const_mul _
  have hS : IntegrableOn HW.etaStar (Set.Ioi T) := CT.integrable_star.integrableOn
  have hle : ∀ t ∈ Set.Ioi T, HW.etaStar t ≤ 3840 / 49 ^ 8 * t ^ (-8 : ℝ) := by
    intro t ht
    have ht0 : 0 < t := lt_trans hT ht
    have h8 := etaStar_pow8_le ht0.le
    rw [show (-8 : ℝ) = -((8 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_natCast,
      ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    exact h8
  calc ∫ t in Set.Ioi T, HW.etaStar t ≤ ∫ t in Set.Ioi T, 3840 / 49 ^ 8 * t ^ (-8 : ℝ) :=
        setIntegral_mono_on hS hI measurableSet_Ioi hle
    _ = 3840 / 49 ^ 8 * (T ^ (-7 : ℝ) / 7) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hT]
        norm_num

/-- `(∫_0^T η*)²/T ≤ ∫_0^∞ η*²` (the variance of `η*` on `(0, T]` is nonnegative). -/
theorem star_sq_ge (T : ℝ) (hT : 0 < T) :
    (∫ t in Set.Ioc 0 T, HW.etaStar t) ^ 2 / T ≤ ∫ t in Set.Ioi 0, HW.etaStar t ^ 2 := by
  have hS1 : IntegrableOn HW.etaStar (Set.Ioi 0) := RW.integrable_etaStar
  have hS2 : IntegrableOn (fun t => HW.etaStar t ^ 2) (Set.Ioi 0) :=
    DP.sq_integrable_of_memLp _ RW.memLp_etaStar_two
  have hsubT : Set.Ioc 0 T ⊆ Set.Ioi 0 := Set.Ioc_subset_Ioi_self
  have hI1 : IntegrableOn HW.etaStar (Set.Ioc 0 T) := hS1.mono_set hsubT
  have hI2 : IntegrableOn (fun t => HW.etaStar t ^ 2) (Set.Ioc 0 T) := hS2.mono_set hsubT
  obtain ⟨A, hA⟩ : ∃ A, A = ∫ t in Set.Ioc 0 T, HW.etaStar t := ⟨_, rfl⟩
  rw [← hA]
  have hTvol : volume.real (Set.Ioc (0 : ℝ) T) = T := by
    rw [measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hT.le]
  have hc : IntegrableOn (fun _ : ℝ => (A / T) ^ 2) (Set.Ioc 0 T) :=
    integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hvar : 0 ≤ ∫ t in Set.Ioc 0 T, (HW.etaStar t - A / T) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioc fun _ _ => sq_nonneg _
  have i1 : IntegrableOn (fun t => HW.etaStar t ^ 2 - 2 * (A / T) * HW.etaStar t)
      (Set.Ioc 0 T) := hI2.sub (hI1.const_mul (2 * (A / T)))
  have hexp : ∫ t in Set.Ioc 0 T, (HW.etaStar t - A / T) ^ 2 =
      (∫ t in Set.Ioc 0 T, HW.etaStar t ^ 2) - 2 * (A / T) * A + (A / T) ^ 2 * T := by
    have e : ∀ t, (HW.etaStar t - A / T) ^ 2 =
        (HW.etaStar t ^ 2 - 2 * (A / T) * HW.etaStar t) + (A / T) ^ 2 := fun t => by ring
    simp_rw [e]
    rw [integral_add i1 hc, integral_sub hI2 (hI1.const_mul (2 * (A / T))),
      integral_const_mul, setIntegral_const, hTvol, smul_eq_mul, ← hA]
    ring
  have hsq : A ^ 2 / T ≤ ∫ t in Set.Ioc 0 T, HW.etaStar t ^ 2 := by
    rw [hexp] at hvar
    have e2 : 2 * (A / T) * A - (A / T) ^ 2 * T = A ^ 2 / T := by
      field_simp
      ring
    linarith
  have hmono : ∫ t in Set.Ioc 0 T, HW.etaStar t ^ 2 ≤ ∫ t in Set.Ioi 0, HW.etaStar t ^ 2 :=
    setIntegral_mono_set hS2 (ae_of_all _ fun _ => sq_nonneg _)
      (Filter.Eventually.of_forall hsubT)
  linarith

/-- `∫_0^T η* ≥ √(π/2)/49 − (3840/49⁸)T⁻⁷/7`. -/
theorem star_Ioc_ge (T : ℝ) (hT : 0 < T) :
    Real.sqrt (Real.pi / 2) / 49 - 3840 / 49 ^ 8 * (1 / T ^ 7 / 7) ≤
      ∫ t in Set.Ioc 0 T, HW.etaStar t := by
  have hS1 : IntegrableOn HW.etaStar (Set.Ioi 0) := RW.integrable_etaStar
  have hI1 : IntegrableOn HW.etaStar (Set.Ioc 0 T) := hS1.mono_set Set.Ioc_subset_Ioi_self
  have hsplit : ∫ t in Set.Ioi 0, HW.etaStar t =
      (∫ t in Set.Ioc 0 T, HW.etaStar t) + ∫ t in Set.Ioi T, HW.etaStar t := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hT.le, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi hI1 (hS1.mono_set (Set.Ioi_subset_Ioi hT.le))]
  have htail := int_star_tail T hT
  have hT7 : T ^ (-7 : ℝ) = 1 / T ^ 7 := by
    rw [show (-7 : ℝ) = -((7 : ℕ) : ℝ) by norm_num, Real.rpow_neg hT.le, Real.rpow_natCast,
      one_div]
  rw [hT7] at htail
  rw [EN.int_etaStar] at hsplit
  linarith

/-- **`|η*|₂ ≥ 0.089`** (truth `0.1473`), at `T = 0.072`. -/
theorem l2_star_ge : 0.089 ≤ MajSp.l2 HW.etaStar := by
  have h1 := star_sq_ge 0.072 (by norm_num)
  have h2 := star_Ioc_ge 0.072 (by norm_num)
  have hpi : (1.2533 : ℝ) ≤ Real.sqrt (Real.pi / 2) := by
    refine Real.le_sqrt_of_sq_le ?_
    have := Real.pi_gt_d6
    norm_num
    linarith
  have h3 : (0.0239 : ℝ) ≤ 1.2533 / 49 - 3840 / 49 ^ 8 * (1 / (0.072 : ℝ) ^ 7 / 7) := by
    norm_num
  have h4 : 1.2533 / 49 ≤ Real.sqrt (Real.pi / 2) / 49 :=
    div_le_div_of_nonneg_right hpi (by norm_num)
  have hA : (0.0239 : ℝ) ≤ ∫ t in Set.Ioc 0 0.072, HW.etaStar t := by linarith
  have h5 : (0.0239 : ℝ) ^ 2 / 0.072 ≤ (∫ t in Set.Ioc 0 0.072, HW.etaStar t) ^ 2 / 0.072 :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hA 2) (by norm_num)
  have h6 : (0.089 : ℝ) ^ 2 ≤ (0.0239 : ℝ) ^ 2 / 0.072 := by norm_num
  unfold MajSp.l2
  exact Real.le_sqrt_of_sq_le (by linarith)
/-! ### `∫|η̂∘| ≤ 1.49` over every window -/

/-- `‖η̂∘(δ)‖ ≤ 0.86676` (`|η∘|₁ ≤ 49779341/57432375`). -/
theorem ft_circ_le_l1 (δ : ℝ) : ‖MajSp.mainFT HW.etaCirc δ‖ ≤ 0.86676 := by
  refine le_trans (NF.norm_mainFT_le _ δ) ?_
  unfold MajSp.l1
  have h := DS.l1_circ_sharp
  have h2 : (49779341 : ℝ) / 57432375 ≤ 0.86676 := by norm_num
  linarith

/-- `‖η̂∘(δ)‖ ≤ 40/(2π|δ|)³` (`Madge` and `|η∘'''|₁ ≤ 40`). -/
theorem ft_circ_le_decay (δ : ℝ) (hδ : δ ≠ 0) :
    ‖MajSp.mainFT HW.etaCirc δ‖ ≤ 40 / (2 * Real.pi * |δ|) ^ 3 := by
  refine le_trans (NF.madge_helf δ hδ) ?_
  have hpos : 0 < (2 * Real.pi * |δ|) ^ 3 :=
    pow_pos (mul_pos (mul_pos two_pos Real.pi_pos) (abs_pos.mpr hδ)) 3
  exact div_le_div_of_nonneg_right EN.l1_third_le hpos.le

/-- The tail integral of the `δ⁻³` majorant: `∫_D^u F ≤ (40/(2π)³)·D⁻²/2` for any continuous `F`
with `F(δ) ≤ 40/(2π|δ|)³`. -/
theorem int_tail_le (F : ℝ → ℝ) (hF : Continuous F) (D u : ℝ) (hD : 0 < D) (hDu : D ≤ u)
    (hb : ∀ δ, 0 < δ → F δ ≤ 40 / (2 * Real.pi * |δ|) ^ 3) :
    ∫ δ in D..u, F δ ≤ 40 / (2 * Real.pi) ^ 3 * (D ^ (-2 : ℝ) / 2) := by
  have h0 : (0 : ℝ) ∉ Set.uIcc D u := by
    rw [Set.uIcc_of_le hDu]
    intro h
    linarith [h.1]
  have hI : IntervalIntegrable (fun δ : ℝ => δ ^ (-3 : ℝ)) volume D u :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr h0)
  have hle : ∀ δ ∈ Set.Icc D u, F δ ≤ 40 / (2 * Real.pi) ^ 3 * δ ^ (-3 : ℝ) := by
    intro δ hδ
    have hδ0 : 0 < δ := lt_of_lt_of_le hD hδ.1
    refine le_trans (hb δ hδ0) (le_of_eq ?_)
    rw [abs_of_pos hδ0, show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hδ0.le,
      Real.rpow_natCast, mul_pow, ← div_div, div_eq_mul_inv]
  have hu : 0 ≤ u ^ (-2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hπ : 0 < 40 / (2 * Real.pi) ^ 3 := by positivity
  calc ∫ δ in D..u, F δ ≤ ∫ δ in D..u, 40 / (2 * Real.pi) ^ 3 * δ ^ (-3 : ℝ) :=
        intervalIntegral.integral_mono_on hDu (hF.intervalIntegrable _ _) (hI.const_mul _) hle
    _ = 40 / (2 * Real.pi) ^ 3 * ((u ^ ((-3 : ℝ) + 1) - D ^ ((-3 : ℝ) + 1)) / ((-3 : ℝ) + 1)) := by
        rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by norm_num, h0⟩)]
    _ ≤ 40 / (2 * Real.pi) ^ 3 * (D ^ (-2 : ℝ) / 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hπ.le
        rw [show (-3 : ℝ) + 1 = -2 by norm_num]
        have e : (u ^ (-2 : ℝ) - D ^ (-2 : ℝ)) / (-2) = D ^ (-2 : ℝ) / 2 - u ^ (-2 : ℝ) / 2 := by
          ring
        rw [e]
        linarith

/-- **`∫_{−w}^{w} |η̂∘| ≤ 1.49`** for every `w ≥ 0` (truth over `ℝ`: `1.0163`): `|η̂∘| ≤ 0.86676`
on `[−0.57, 0.57]`, `|η̂∘| ≤ 40/(2π|δ|)³` beyond. -/
theorem int_ft_circ_le (w : ℝ) (hw : 0 ≤ w) :
    ∫ δ in (-w)..w, ‖MajSp.mainFT HW.etaCirc δ‖ ≤ 1.49 := by
  set F : ℝ → ℝ := fun δ => ‖MajSp.mainFT HW.etaCirc δ‖ with hFdef
  have hF : Continuous F := (NF.continuous_mainFT_of _ NF.oInt_helf).norm
  have hmid : ∀ v, 0 ≤ v → ∫ δ in (-v)..v, F δ ≤ 2 * v * 0.86676 := by
    intro v hv
    have h : ∫ δ in (-v)..v, F δ ≤ ∫ δ in (-v)..v, (0.86676 : ℝ) :=
      intervalIntegral.integral_mono_on (by linarith : -v ≤ v)
        (hF.intervalIntegrable (-v) v) (continuous_const.intervalIntegrable (-v) v)
        (fun δ _ => ft_circ_le_l1 δ)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    linarith
  have hπ : (248.02 : ℝ) ≤ (2 * Real.pi) ^ 3 := by
    have := Real.pi_gt_d4
    have h1 : (6.283 : ℝ) ≤ 2 * Real.pi := by linarith
    calc (248.02 : ℝ) ≤ 6.283 ^ 3 := by norm_num
      _ ≤ (2 * Real.pi) ^ 3 := pow_le_pow_left₀ (by norm_num) h1 3
  have hD2 : (0.57 : ℝ) ^ (-2 : ℝ) = 1 / 0.57 ^ 2 := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num),
      Real.rpow_natCast, one_div]
  have htail : 40 / (2 * Real.pi) ^ 3 * ((0.57 : ℝ) ^ (-2 : ℝ) / 2) ≤ 0.2482 := by
    rw [hD2]
    have h1 : 40 / (2 * Real.pi) ^ 3 ≤ 40 / 248.02 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hπ
    have h2 : (0 : ℝ) ≤ 1 / 0.57 ^ 2 / 2 := by norm_num
    calc 40 / (2 * Real.pi) ^ 3 * (1 / 0.57 ^ 2 / 2) ≤ 40 / 248.02 * (1 / 0.57 ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ ≤ 0.2482 := by norm_num
  rcases le_or_gt w 0.57 with hw57 | hw57
  · have := hmid w hw
    nlinarith
  · have hR : ∫ δ in (0.57 : ℝ)..w, F δ ≤ 40 / (2 * Real.pi) ^ 3 * ((0.57 : ℝ) ^ (-2 : ℝ) / 2) :=
      int_tail_le F hF 0.57 w (by norm_num) hw57.le fun δ hδ => ft_circ_le_decay δ hδ.ne'
    have hL : ∫ δ in (-w)..(-0.57), F δ ≤
        40 / (2 * Real.pi) ^ 3 * ((0.57 : ℝ) ^ (-2 : ℝ) / 2) := by
      have e : ∫ δ in (-w)..(-0.57), F δ = ∫ δ in (0.57 : ℝ)..w, F (-δ) :=
        (intervalIntegral.integral_comp_neg (fun δ => F δ)).symm
      rw [e]
      refine int_tail_le (fun δ => F (-δ)) (hF.comp continuous_neg) 0.57 w (by norm_num)
        hw57.le fun δ hδ => ?_
      have h := ft_circ_le_decay (-δ) (neg_ne_zero.mpr hδ.ne')
      rw [abs_neg] at h
      exact h
    have hM := hmid 0.57 (by norm_num)
    have i1 : IntervalIntegrable F volume (-w) (-0.57) := hF.intervalIntegrable _ _
    have i2 : IntervalIntegrable F volume (-0.57) 0.57 := hF.intervalIntegrable _ _
    have i3 : IntervalIntegrable F volume 0.57 w := hF.intervalIntegrable _ _
    rw [← intervalIntegral.integral_add_adjacent_intervals (i1.trans i2) i3,
      ← intervalIntegral.integral_add_adjacent_intervals i1 i2]
    linarith

/-! ### `c₃ = ∑_{q ∈ Qs} μ²/φ^{3/2} ≤ 4.84` -/

/-- `f(p) = 1/((p − 1)√(p − 1))`. -/
noncomputable def fc (p : ℕ) : ℝ := 1 / (((p : ℝ) - 1) * Real.sqrt ((p : ℝ) - 1))

theorem fc_nonneg (p : ℕ) (hp : 1 ≤ p) : 0 ≤ fc p := by
  have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  unfold fc
  apply div_nonneg zero_le_one (mul_nonneg (by linarith) (Real.sqrt_nonneg _))

/-- `μ²/φ^{3/2} = ∏_{p | q} f(p)` on squarefree `q`. -/
theorem cQ_sqrt_sqfree {q : ℕ} (hq : Squarefree q) :
    DS.cQ q / Real.sqrt (q.totient : ℝ) = ∏ p ∈ q.primeFactors, fc p := by
  have hμ : ((moebius q : ℤ) : ℝ) ^ 2 = 1 := by
    exact_mod_cast moebius_sq_eq_one_of_squarefree hq
  have hnn : ∀ p ∈ q.primeFactors, 0 ≤ (p : ℝ) - 1 := fun p hp => by
    have := (Nat.prime_of_mem_primeFactors hp).one_le
    have h1 : (1 : ℝ) ≤ p := by exact_mod_cast this
    linarith
  unfold DS.cQ fc
  rw [hμ, totient_sqfree hq, Real.sqrt_prod _ hnn, div_div, ← Finset.prod_mul_distrib,
    one_div, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun p _ => (one_div _).symm

/-- `1/(m√m) ≤ 1/√(m − 2) − 1/√m` for `m ≥ 3`. -/
theorem inv_msqrt_le (m : ℝ) (hm : 3 ≤ m) :
    1 / (m * Real.sqrt m) ≤ 1 / Real.sqrt (m - 2) - 1 / Real.sqrt m := by
  set a := Real.sqrt (m - 2) with ha_def
  set b := Real.sqrt m with hb_def
  have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hb : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have ha2 : a ^ 2 = m - 2 := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = m := Real.sq_sqrt (by linarith)
  have key : (b - a) * (a + b) = 2 := by linear_combination hb2 - ha2
  have h1 : ((b - a) * b ^ 2 - a) * (a + b) = 2 * b ^ 2 - a ^ 2 - a * b := by
    linear_combination b ^ 2 * key
  have h2 : 0 ≤ 2 * b ^ 2 - a ^ 2 - a * b := by nlinarith
  have h3 : 0 ≤ (b - a) * b ^ 2 - a := by
    by_contra hneg
    have := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) (by linarith : 0 < a + b)
    linarith
  rw [← hb2, div_sub_div _ _ ha.ne' hb.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  have h4 := mul_le_mul_of_nonneg_left h3 hb.le
  nlinarith

/-- `∑_{7 ≤ j < J} f(2j+1) ≤ 1/√12 − 1/√(2J − 2)` (telescoping). -/
theorem sum_fc_odd_le : ∀ J : ℕ, 7 ≤ J → ∑ j ∈ Finset.Ico 7 J, fc (2 * j + 1) ≤
    1 / Real.sqrt 12 - 1 / Real.sqrt (2 * (J : ℝ) - 2) := by
  intro J hJ
  induction J, hJ using Nat.le_induction with
  | base => norm_num
  | succ J hJ ih =>
    rw [Finset.sum_Ico_succ_top hJ]
    have hJr : (7 : ℝ) ≤ J := by exact_mod_cast hJ
    have hk := inv_msqrt_le (2 * (J : ℝ)) (by linarith)
    have e1 : fc (2 * J + 1) = 1 / (2 * (J : ℝ) * Real.sqrt (2 * (J : ℝ))) := by
      unfold fc
      push_cast
      rw [show 2 * (J : ℝ) + 1 - 1 = 2 * (J : ℝ) by ring]
    have e2 : 2 * ((J + 1 : ℕ) : ℝ) - 2 = 2 * (J : ℝ) := by push_cast; ring
    rw [e1, e2]
    linarith

/-- `∑_{p ∈ Q} f(p) ≤ 1/√12` over any set of odd `p ≥ 15`. -/
theorem fc_tail (Q : Finset ℕ) (hQ : ∀ p ∈ Q, Odd p ∧ 15 ≤ p) :
    ∑ p ∈ Q, fc p ≤ 1 / Real.sqrt 12 := by
  set J := max 7 (Q.sup id + 1) with hJdef
  have hJ : 7 ≤ J := le_max_left _ _
  have hsub : Q ⊆ (Finset.Ico 7 J).image (fun j : ℕ => (2 * j + 1 : ℕ)) := by
    intro p hp
    obtain ⟨⟨k, hk⟩, h15⟩ := hQ p hp
    have hle : p ≤ Q.sup id := Finset.le_sup (f := id) hp
    have hJ2 : Q.sup id + 1 ≤ J := le_max_right _ _
    exact Finset.mem_image.mpr ⟨k, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hk.symm⟩
  have hinj : Set.InjOn (fun j : ℕ => (2 * j + 1 : ℕ)) (Finset.Ico 7 J : Set ℕ) :=
    fun a _ b _ h => by
      simp only at h
      omega
  have h1 := sum_fc_odd_le J hJ
  have h2 : 0 ≤ 1 / Real.sqrt (2 * (J : ℝ) - 2) := by positivity
  calc ∑ p ∈ Q, fc p ≤ ∑ p ∈ (Finset.Ico 7 J).image (fun j : ℕ => (2 * j + 1 : ℕ)), fc p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => by
          obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hp
          exact fc_nonneg _ (by omega)
    _ = ∑ j ∈ Finset.Ico 7 J, fc (2 * j + 1) := Finset.sum_image hinj
    _ ≤ 1 / Real.sqrt 12 := by linarith
/-- `odd_prod_le` with the tail sum supplied: `∏_{P}(1 + f) ≤ ∏_{3,…,13}(1 + f)·e^T`. -/
theorem odd_prod_le_T (f : ℕ → ℝ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hf0 : ∀ p, 2 ≤ p → 0 ≤ f p) (T : ℝ)
    (hT : ∑ p ∈ P.filter (fun p => ¬ p ≤ 13), f p ≤ T) :
    ∏ p ∈ P, (1 + f p) ≤ (∏ p ∈ ({3, 5, 7, 11, 13} : Finset ℕ), (1 + f p)) * Real.exp T := by
  have hpos : ∀ p ∈ P, 0 ≤ 1 + f p := fun p hp => by
    have := hf0 p (hP p hp).1.two_le
    linarith
  rw [← Finset.prod_filter_mul_prod_filter_not P (fun p => p ≤ 13)]
  have hA : ∏ p ∈ P.filter (fun p => p ≤ 13), (1 + f p) ≤
      ∏ p ∈ ({3, 5, 7, 11, 13} : Finset ℕ), (1 + f p) := by
    have hsub : P.filter (fun p => p ≤ 13) ⊆ ({3, 5, 7, 11, 13} : Finset ℕ) := by
      intro p hp
      obtain ⟨hpP, hp13⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpr, hp2⟩ := hP p hpP
      interval_cases p <;> first | decide | exact absurd rfl hp2 | (norm_num at hpr)
    refine Finset.prod_le_prod_of_subset_of_one_le hsub
      (fun p hp => hpos p (Finset.mem_filter.mp hp).1) fun p hp _ => ?_
    have h2 : 2 ≤ p := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      omega
    have := hf0 p h2
    linarith
  have hB : ∏ p ∈ P.filter (fun p => ¬ p ≤ 13), (1 + f p) ≤ Real.exp T := by
    refine le_trans ?_ (Real.exp_le_exp.mpr hT)
    rw [Real.exp_sum]
    refine Finset.prod_le_prod (fun p hp => hpos p (Finset.mem_filter.mp hp).1) fun p _ => ?_
    have := Real.add_one_le_exp (f p)
    linarith
  have hApos : 0 ≤ ∏ p ∈ ({3, 5, 7, 11, 13} : Finset ℕ), (1 + f p) :=
    Finset.prod_nonneg fun p hp => by
      have h2 : 2 ≤ p := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        omega
      have := hf0 p h2
      linarith
  have hBpos : 0 ≤ ∏ p ∈ P.filter (fun p => ¬ p ≤ 13), (1 + f p) :=
    Finset.prod_nonneg fun p hp => hpos p (Finset.mem_filter.mp hp).1
  exact mul_le_mul hA hB hBpos hApos

/-- `f(p) ≤ 1/(s r)` from `p − 1 = s` and `r² ≤ s`. -/
theorem fc_le (p : ℕ) (s r : ℝ) (hp : (p : ℝ) - 1 = s) (hs : 0 < s) (hr : 0 < r)
    (hsq : r ^ 2 ≤ s) : fc p ≤ 1 / (s * r) := by
  unfold fc
  rw [hp]
  exact one_div_le_one_div_of_le (mul_pos hs hr)
    (mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le hsq) hs.le)

/-- `∏_{p ∈ {3,5,7,11,13}}(1 + f(p)) ≤ 1.7182`. -/
theorem fc_small : ∏ p ∈ ({3, 5, 7, 11, 13} : Finset ℕ), (1 + fc p) ≤ 1.7182 := by
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  have h3 := fc_le 3 2 1.414213 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h5 := fc_le 5 4 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h7 := fc_le 7 6 2.449489 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h11 := fc_le 11 10 3.162277 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h13 := fc_le 13 12 3.464101 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have n3 := fc_nonneg 3 (by norm_num)
  have n5 := fc_nonneg 5 (by norm_num)
  have n7 := fc_nonneg 7 (by norm_num)
  have n11 := fc_nonneg 11 (by norm_num)
  have n13 := fc_nonneg 13 (by norm_num)
  have k1 : (1 + fc 11) * (1 + fc 13) ≤ (1 + 1 / (10 * 3.162277)) * (1 + 1 / (12 * 3.464101)) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  have k2 : (1 + fc 7) * ((1 + fc 11) * (1 + fc 13)) ≤ (1 + 1 / (6 * 2.449489)) *
      ((1 + 1 / (10 * 3.162277)) * (1 + 1 / (12 * 3.464101))) :=
    mul_le_mul (by linarith) k1 (by positivity) (by norm_num)
  have k3 : (1 + fc 5) * ((1 + fc 7) * ((1 + fc 11) * (1 + fc 13))) ≤ (1 + 1 / (4 * 2)) *
      ((1 + 1 / (6 * 2.449489)) * ((1 + 1 / (10 * 3.162277)) * (1 + 1 / (12 * 3.464101)))) :=
    mul_le_mul (by linarith) k2 (by positivity) (by norm_num)
  have k4 : (1 + fc 3) * ((1 + fc 5) * ((1 + fc 7) * ((1 + fc 11) * (1 + fc 13)))) ≤
      (1 + 1 / (2 * 1.414213)) * ((1 + 1 / (4 * 2)) * ((1 + 1 / (6 * 2.449489)) *
        ((1 + 1 / (10 * 3.162277)) * (1 + 1 / (12 * 3.464101))))) :=
    mul_le_mul (by linarith) k3 (by positivity) (by norm_num)
  refine le_trans k4 ?_
  norm_num

/-- `∑_{q ∈ S} μ²/φ^{3/2} ≤ ∏_{p < Y}(1 + f(p))` for any finite `S ⊆ [1, Y)`. -/
theorem sum_c3_le_prod (S : Finset ℕ) (Y : ℕ) (hS : ∀ q ∈ S, 1 ≤ q ∧ q < Y) :
    ∑ q ∈ S, DS.cQ q / Real.sqrt (q.totient : ℝ) ≤ ∏ p ∈ Nat.primesBelow Y, (1 + fc p) := by
  have h1 : ∑ q ∈ S, DS.cQ q / Real.sqrt (q.totient : ℝ) =
      ∑ q ∈ S.filter Squarefree, ∏ p ∈ q.primeFactors, fc p := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs with hq
    · exact cQ_sqrt_sqfree hq
    · unfold DS.cQ
      rw [moebius_eq_zero_of_not_squarefree hq]
      simp
  rw [h1]
  refine sum_le_euler _ _ (fun p hp => fc_nonneg p (Nat.mem_primesBelow.mp hp).2.one_le) _
    fun q hq => ?_
  obtain ⟨hq1, hsq⟩ := Finset.mem_filter.mp hq
  refine ⟨hsq, fun p hp => ?_⟩
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hpq := Nat.dvd_of_mem_primeFactors hp
  obtain ⟨hq0, hqY⟩ := hS q hq1
  have hple := Nat.le_of_dvd (by omega : 0 < q) hpq
  rw [Nat.mem_primesBelow]
  exact ⟨by omega, hpr⟩

/-- **`c₃ ≤ 4.84`** (truth `3.8523845`): `2·∏_{p odd}(1 + (p−1)^{−3/2})`, exact through `13`,
the rest `≤ exp(1/√12)`. -/
theorem c3_le : NF.c3 ≤ 4.84 := by
  unfold NF.c3
  refine le_trans (sum_c3_le_prod NF.Qs 300001 Qs_range) ?_
  set P := Nat.primesBelow 300001 with hP
  have hmem : ∀ p ∈ P, p.Prime := fun p hp => (Nat.mem_primesBelow.mp hp).2
  have hpos : ∀ p ∈ P, 0 ≤ 1 + fc p := fun p hp => by
    have := fc_nonneg p (hmem p hp).one_le
    linarith
  rw [← Finset.prod_filter_mul_prod_filter_not P (fun p => p = 2)]
  have h2 : ∏ p ∈ P.filter (fun p => p = 2), (1 + fc p) ≤ 2 := by
    have hsub : P.filter (fun p => p = 2) ⊆ {2} := fun p hp => by
      rw [Finset.mem_singleton]
      exact (Finset.mem_filter.mp hp).2
    refine le_trans (Finset.prod_le_prod_of_subset_of_one_le hsub
      (fun p hp => hpos p (Finset.mem_filter.mp hp).1) fun p hp _ => ?_) ?_
    · rw [Finset.mem_singleton] at hp
      subst hp
      have := fc_nonneg 2 (by norm_num)
      linarith
    · rw [Finset.prod_singleton]
      unfold fc
      norm_num
  have hT : ∑ p ∈ (P.filter (fun p => ¬ p = 2)).filter (fun p => ¬ p ≤ 13), fc p ≤ 0.288676 := by
    refine le_trans (fc_tail _ fun p hp => ?_) ?_
    · obtain ⟨hp1, hp13⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpP, hp2⟩ := Finset.mem_filter.mp hp1
      have hpr := hmem p hpP
      refine ⟨hpr.odd_of_ne_two hp2, ?_⟩
      rcases hpr.eq_two_or_odd' with h | ⟨k, hk⟩
      · exact absurd h hp2
      · omega
    · have h12 : (3.464101 : ℝ) ≤ Real.sqrt 12 := Real.le_sqrt_of_sq_le (by norm_num)
      have : 1 / Real.sqrt 12 ≤ 1 / 3.464101 := one_div_le_one_div_of_le (by norm_num) h12
      have h3 : (1 : ℝ) / 3.464101 ≤ 0.288676 := by norm_num
      linarith
  have hO := odd_prod_le_T fc (P.filter (fun p => ¬ p = 2))
    (fun p hp => ⟨hmem p (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩)
    (fun p hp => fc_nonneg p (by omega)) 0.288676 hT
  have hE := exp_le_inv 0.288676 (by norm_num)
  have hS := fc_small
  have hApos : 0 ≤ ∏ p ∈ ({3, 5, 7, 11, 13} : Finset ℕ), (1 + fc p) :=
    Finset.prod_nonneg fun p hp => by
      have h2 : 1 ≤ p := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        omega
      have := fc_nonneg p h2
      linarith
  have hOdd : ∏ p ∈ P.filter (fun p => ¬ p = 2), (1 + fc p) ≤
      1.7182 * (1 / (1 - 0.288676)) :=
    le_trans hO (mul_le_mul hS hE (Real.exp_pos _).le (by norm_num))
  have hOpos : 0 ≤ ∏ p ∈ P.filter (fun p => ¬ p = 2), (1 + fc p) :=
    Finset.prod_nonneg fun p hp => hpos p (Finset.mem_filter.mp hp).1
  calc (∏ p ∈ P.filter (fun p => p = 2), (1 + fc p)) *
        ∏ p ∈ P.filter (fun p => ¬ p = 2), (1 + fc p)
      ≤ 2 * (1.7182 * (1 / (1 - 0.288676))) := mul_le_mul h2 hOdd hOpos (by norm_num)
    _ ≤ 4.84 := by norm_num

/-! ### `|η₊|₂ ≥ 0.7996` -/

/-- **`|η₊|₂ ≥ 0.7996`** (truth `0.8001`): `η₊² ≥ η∘² − 2c·te^{−t²/2}` pointwise
(`|h₂₀₀ − h| ≤ c = 2.7·10⁻⁴`, `|η∘| ≤ 1`), `∫η∘² ≥ 0.64`, `∫te^{−t²/2} = 1`. -/
theorem l2_plus_ge : 0.7996 ≤ MajSp.l2 HW.etaPlus := by
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ), HW.etaCirc t ^ 2 - 2 * 2.7e-4 * (t * Real.exp (-t ^ 2 / 2)) ≤
      HW.etaPlus t ^ 2 := by
    intro t ht
    have ht0 : 0 < t := ht
    set a := HW.etaCirc t with ha_def
    set w := t * Real.exp (-t ^ 2 / 2) with hw_def
    set d := HW.hH 200 t - HW.hFun t with hd_def
    have hw0 : 0 ≤ w := mul_nonneg ht0.le (Real.exp_pos _).le
    have e1 : HW.etaPlus t = a + d * w := by
      rw [ha_def, hd_def, hw_def]
      unfold HW.etaPlus HW.etaCirc
      ring
    have ha1 : |a| ≤ 1 := HW.etaCirc_le t
    have hd1 : |d| ≤ 2.7e-4 := BS.band_sharp t ht0
    have had : -(2.7e-4) ≤ a * d := by
      have h1 : |a * d| ≤ 2.7e-4 := by
        rw [abs_mul]
        calc |a| * |d| ≤ 1 * 2.7e-4 := mul_le_mul ha1 hd1 (abs_nonneg _) zero_le_one
          _ = 2.7e-4 := one_mul _
      exact (abs_le.mp h1).1
    rw [e1]
    have h2 := mul_le_mul_of_nonneg_right had hw0
    nlinarith [sq_nonneg (d * w)]
  have hP2 : IntegrableOn (fun t => HW.etaPlus t ^ 2) (Set.Ioi 0) :=
    DP.sq_integrable_of_memLp _ RW.memLp_etaPlus_two
  have hA : IntegrableOn (fun t => HW.etaCirc t ^ 2) (Set.Ioi 0) :=
    EN.integrableOn_of_cont _ (EN.continuous_etaCirc.pow 2) fun t ht => by
      rw [EN.etaCirc_of_two_lt ht]
      ring
  have hB : IntegrableOn (fun t => 2 * 2.7e-4 * (t * Real.exp (-t ^ 2 / 2))) (Set.Ioi 0) :=
    EN.integrable_t_exp.const_mul _
  have hI : ∫ t in Set.Ioi 0, (HW.etaCirc t ^ 2 - 2 * 2.7e-4 * (t * Real.exp (-t ^ 2 / 2))) ≤
      ∫ t in Set.Ioi 0, HW.etaPlus t ^ 2 :=
    setIntegral_mono_on (hA.sub hB) hP2 measurableSet_Ioi hpt
  rw [integral_sub hA hB, integral_const_mul, EN.int_t_exp, EN.circ_sq_int] at hI
  have hG := EN.G6_bounds.1
  unfold MajSp.l2
  exact Real.le_sqrt_of_sq_le (by nlinarith)
/-- **The per-modulus weight at `(η₊, η*)`**: `∫_{−w}^{w}|η̂₊||η̂*| ≤ |η*|₁·1.49 + |η₊ − η∘|₂|η*|₂`
(`η̂₊ = η̂∘ + (η₊ − η∘)^`; `|η̂*| ≤ |η*|₁` against `∫|η̂∘| ≤ 1.49`; Cauchy–Schwarz and Plancherel on
the difference). -/
theorem t3_per_q (w : ℝ) (hw : 0 ≤ w) :
    ∫ δ in (-w)..w, ‖MajSp.mainFT HW.etaPlus δ‖ * ‖MajSp.mainFT HW.etaStar δ‖ ≤
      MajSp.l1 HW.etaStar * 1.49 +
        MajSp.l2 (fun t => HW.etaPlus t - HW.etaCirc t) * MajSp.l2 HW.etaStar := by
  have hp1 : Integrable HW.etaPlus (volume.restrict (Set.Ioi 0)) := RW.integrable_etaPlus
  have ho1 : Integrable HW.etaCirc (volume.restrict (Set.Ioi 0)) := NF.oInt_helf
  have hs1 : Integrable HW.etaStar (volume.restrict (Set.Ioi 0)) := RW.integrable_etaStar
  have hs2 : Integrable (fun t => HW.etaStar t ^ 2) (volume.restrict (Set.Ioi 0)) :=
    DP.sq_integrable_of_memLp _ RW.memLp_etaStar_two
  have hdm : Integrable (fun t => HW.etaPlus t - HW.etaCirc t) (volume.restrict (Set.Ioi 0)) :=
    hp1.sub ho1
  have hd2 : Integrable (fun t => (HW.etaPlus t - HW.etaCirc t) ^ 2)
      (volume.restrict (Set.Ioi 0)) :=
    DP.sq_integrable_of_memLp _ (RW.memLp_etaPlus_two.sub RW.memLp_etaCirc_two)
  have cO := (NF.continuous_mainFT_of HW.etaCirc ho1).norm
  have cS := (NF.continuous_mainFT_of HW.etaStar hs1).norm
  have cD := (NF.continuous_mainFT_of _ hdm).norm
  have cP := (NF.continuous_mainFT_of HW.etaPlus hp1).norm
  have hww : -w ≤ w := by linarith
  have hpt : ∀ δ, ‖MajSp.mainFT HW.etaPlus δ‖ * ‖MajSp.mainFT HW.etaStar δ‖ ≤
      MajSp.l1 HW.etaStar * ‖MajSp.mainFT HW.etaCirc δ‖ +
        ‖MajSp.mainFT (fun t => HW.etaPlus t - HW.etaCirc t) δ‖ *
          ‖MajSp.mainFT HW.etaStar δ‖ := by
    intro δ
    have hF : MajSp.mainFT HW.etaPlus δ = MajSp.mainFT HW.etaCirc δ +
        MajSp.mainFT (fun t => HW.etaPlus t - HW.etaCirc t) δ := by
      rw [NF.mainFT_sub _ _ hp1 ho1 δ]
      ring
    have h1 : ‖MajSp.mainFT HW.etaPlus δ‖ ≤ ‖MajSp.mainFT HW.etaCirc δ‖ +
        ‖MajSp.mainFT (fun t => HW.etaPlus t - HW.etaCirc t) δ‖ := by
      rw [hF]
      exact norm_add_le _ _
    have h2 := NF.norm_mainFT_le HW.etaStar δ
    have h3 := mul_le_mul_of_nonneg_right h1 (norm_nonneg (MajSp.mainFT HW.etaStar δ))
    have h4 := mul_le_mul_of_nonneg_left h2 (norm_nonneg (MajSp.mainFT HW.etaCirc δ))
    nlinarith
  have i1 : IntervalIntegrable (fun δ => MajSp.l1 HW.etaStar * ‖MajSp.mainFT HW.etaCirc δ‖)
      volume (-w) w := (cO.intervalIntegrable _ _).const_mul _
  have i2 : IntervalIntegrable (fun δ => ‖MajSp.mainFT (fun t => HW.etaPlus t - HW.etaCirc t) δ‖ *
      ‖MajSp.mainFT HW.etaStar δ‖) volume (-w) w := (cD.mul cS).intervalIntegrable _ _
  have hmono : ∫ δ in (-w)..w, ‖MajSp.mainFT HW.etaPlus δ‖ * ‖MajSp.mainFT HW.etaStar δ‖ ≤
      ∫ δ in (-w)..w, (MajSp.l1 HW.etaStar * ‖MajSp.mainFT HW.etaCirc δ‖ +
        ‖MajSp.mainFT (fun t => HW.etaPlus t - HW.etaCirc t) δ‖ *
          ‖MajSp.mainFT HW.etaStar δ‖) :=
    intervalIntegral.integral_mono_on hww ((cP.mul cS).intervalIntegrable _ _)
      (i1.add i2) (fun δ _ => hpt δ)
  rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul] at hmono
  have hJ := int_ft_circ_le w hw
  have hcs := NF.cs_int w hw (fun δ => ‖MajSp.mainFT (fun t => HW.etaPlus t - HW.etaCirc t) δ‖)
    (fun δ => ‖MajSp.mainFT HW.etaStar δ‖) cD cS
  beta_reduce at hcs
  have mD := DP.mardiQ_of _ hdm hd2 w hw
  have mS := DP.mardiQ_of _ hs1 hs2 w hw
  have sD : Real.sqrt (∫ δ in (-w)..w,
      ‖MajSp.mainFT (fun t => HW.etaPlus t - HW.etaCirc t) δ‖ ^ 2) ≤
        MajSp.l2 (fun t => HW.etaPlus t - HW.etaCirc t) := by
    rw [← Real.sqrt_sq (MajSp.l2_nonneg (fun t => HW.etaPlus t - HW.etaCirc t))]
    exact Real.sqrt_le_sqrt mD
  have sS : Real.sqrt (∫ δ in (-w)..w, ‖MajSp.mainFT HW.etaStar δ‖ ^ 2) ≤
      MajSp.l2 HW.etaStar := by
    rw [← Real.sqrt_sq (MajSp.l2_nonneg HW.etaStar)]
    exact Real.sqrt_le_sqrt mS
  have hpr := mul_le_mul sD sS (Real.sqrt_nonneg _) (MajSp.l2_nonneg _)
  have hL1 : 0 ≤ MajSp.l1 HW.etaStar := MajSp.l1_nonneg _
  have hJ' := mul_le_mul_of_nonneg_left hJ hL1
  linarith

/-- **[T3W] PROVED at Helfgott's `(η₊, η*)`** (1585–1588; `NefumoSpine`, finding 1): the
`R₊M₊M*` weight `t3Sum ≤ c₃(|η*|₁·1.49 + |η₊ − η∘|₂|η*|₂) ≤ 4.84(0.025579·1.49 + 1.8·10⁻⁴|η*|₂)`,
against `2.82643·|η₊|₂|η*|₂ ≥ 2.82643·0.7996·|η*|₂`, closes for `|η*|₂ ≥ 0.0817`; proved
`|η*|₂ ≥ 0.089`. -/
theorem t3W_helf : NF.T3W HW.etaPlus HW.etaStar := by
  obtain ⟨-, -, hd, -, -, hl1s, -, -, -⟩ :=
    EN.normsB27_helf (EN.bandSharp27_of_25 BS.bandSharp25)
  have hs := l2_star_ge
  have hp := l2_plus_ge
  have hc3 := c3_le
  set L1 := MajSp.l1 HW.etaStar with hL1def
  set Ls := MajSp.l2 HW.etaStar with hLsdef
  set Ld := MajSp.l2 (fun t => HW.etaPlus t - HW.etaCirc t) with hLddef
  have hq : ∀ q ∈ NF.Qs, DS.cQ q / Real.sqrt (q.totient : ℝ) *
      ∫ δ in (-NF.wq q)..(NF.wq q), ‖MajSp.mainFT HW.etaPlus δ‖ * ‖MajSp.mainFT HW.etaStar δ‖ ≤
        DS.cQ q / Real.sqrt (q.totient : ℝ) * (L1 * 1.49 + Ld * Ls) := fun q _ =>
    mul_le_mul_of_nonneg_left (t3_per_q (NF.wq q) (NF.wq_nonneg q))
      (div_nonneg (DS.cQ_nonneg q) (Real.sqrt_nonneg _))
  have hsum := Finset.sum_le_sum hq
  rw [← Finset.sum_mul] at hsum
  have hc3' : ∑ q ∈ NF.Qs, DS.cQ q / Real.sqrt (q.totient : ℝ) = NF.c3 := rfl
  rw [hc3'] at hsum
  have hpi : Real.sqrt (Real.pi / 2) ≤ 1.25332 := by
    rw [Real.sqrt_le_left (by norm_num)]
    have := Real.pi_lt_d6
    linarith
  have hL1 : L1 ≤ 0.025579 := by
    rw [hl1s]
    have : Real.sqrt (Real.pi / 2) / 49 ≤ 1.25332 / 49 :=
      div_le_div_of_nonneg_right hpi (by norm_num)
    have h2 : (1.25332 : ℝ) / 49 ≤ 0.025579 := by norm_num
    linarith
  have hLs0 : 0 ≤ Ls := MajSp.l2_nonneg _
  have hB0 : 0 ≤ L1 * 1.49 + Ld * Ls :=
    add_nonneg (mul_nonneg (MajSp.l1_nonneg _) (by norm_num))
      (mul_nonneg (MajSp.l2_nonneg _) hLs0)
  have hB : L1 * 1.49 + Ld * Ls ≤ 0.025579 * 1.49 + 1.7999e-4 * Ls := by
    have := mul_le_mul_of_nonneg_right hd hLs0
    nlinarith
  have k1 := mul_le_mul_of_nonneg_right hc3 hB0
  have k2 : 2.82643 * 0.7996 * Ls ≤ 2.82643 * MajSp.l2 HW.etaPlus * Ls := by
    have := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2.82643)
    exact mul_le_mul_of_nonneg_right this hLs0
  unfold NF.T3W NF.t3Sum
  nlinarith
/-! ## [ZvsL]: `L_{r,δ₀}(η) ≤ Z_{η²,2}(x)` -/

section ZSec

/-- **`θ(y) ≥ 0.92079·y` for `y ≥ 10²⁴`**: `θ(y) ≥ A(y − 30) − ½ log y − 3 − 2√y log y` with
`A > 0.9208` (`Common.Chebyshev.theta_ge_chebyshev`), and `log y ≤ 4y^{1/4}`. -/
theorem theta_ge_lin (y : ℝ) (hy : 10 ^ 24 ≤ y) : 0.92079 * y ≤ Chebyshev.theta y := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have h := Principia.Common.Chebyshev.theta_ge_chebyshev (x := y) (by linarith)
  have hA := Principia.Common.Chebyshev.chebyshevA_gt
  have hA1 : Principia.Common.Chebyshev.chebyshevA ≤ 1 := by
    have h1 := Principia.Common.Chebyshev.chebyshevA_le_log_two
    have h2 := Real.log_two_lt_d9
    linarith
  set u := y ^ ((1 : ℝ) / 4) with hu
  have hu0 : 0 ≤ u := Real.rpow_nonneg hy0.le _
  have hy4 : y = u ^ 4 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
    norm_num
  have hsq : Real.sqrt y = u ^ 2 := by
    rw [Real.sqrt_eq_rpow, hu, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
    norm_num
  have hlog : Real.log y ≤ 4 * u := by
    have h1 := Real.log_le_rpow_div hy0.le (by norm_num : (0 : ℝ) < 1 / 4)
    rw [← hu] at h1
    linarith
  have hu6 : (10 : ℝ) ^ 6 ≤ u := by
    have h1 : ((10 : ℝ) ^ 24) ^ ((1 : ℝ) / 4) = 10 ^ 6 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [← h1, hu]
    exact Real.rpow_le_rpow (by norm_num) hy (by norm_num)
  have hlog0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  rw [hsq] at h
  have k1 : 2 * u ^ 2 * Real.log y ≤ 8 * u ^ 3 := by
    have := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ 2 * u ^ 2)
    nlinarith
  have hAy : 0.9208 * y ≤ Principia.Common.Chebyshev.chebyshevA * y :=
    mul_le_mul_of_nonneg_right hA.le hy0.le
  have k2 : 10 * u ^ 3 ≤ 1e-5 * u ^ 4 := by
    have h3 : 0 ≤ u ^ 3 := pow_nonneg hu0 3
    nlinarith
  have k3 : 2 * u + 33 ≤ 2 * u ^ 3 := by nlinarith
  have k4 : Principia.Common.Chebyshev.chebyshevA * 30 ≤ 30 := by linarith
  nlinarith

/-- `θ(y) ≤ 1.11·y` for `y ≥ 3·10⁹` (`Common.Chebyshev.theta_le_cheb`). -/
theorem theta_le_lin (y : ℝ) (hy : 3 * 10 ^ 9 ≤ y) : Chebyshev.theta y ≤ 1.11 * y :=
  Principia.Common.Chebyshev.theta_le_cheb y hy

/-! ### `S(r) ≤ 9.68` -/

/-- `g(p) = 1/(p − 1)`, so `∏_{p | q}(1 + g(p)) = q/φ(q)` on squarefree `q`. -/
noncomputable def gfun (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1)

/-- **The divisor identity for `1/φ`**: `1/φ(q) = q⁻¹∑_{d | q} G(d)` on squarefree `q`. -/
theorem inv_totient_eq {q : ℕ} (hq : Squarefree q) :
    DS.cQ q = (∑ d ∈ q.divisors, ArithmeticFunction.prodPrimeFactors gfun d) / (q : ℝ) := by
  have hq0 : q ≠ 0 := hq.ne_zero
  have h1 : ∑ d ∈ q.divisors, ArithmeticFunction.prodPrimeFactors gfun d =
      ∏ p ∈ q.primeFactors, (1 + ArithmeticFunction.prodPrimeFactors gfun p) :=
    (ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_add_of_squarefree
      (ArithmeticFunction.IsMultiplicative.prodPrimeFactors gfun) hq).symm
  have h2 : ∀ p ∈ q.primeFactors, 1 + ArithmeticFunction.prodPrimeFactors gfun p =
      (p : ℝ) / ((p : ℝ) - 1) := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    rw [ArithmeticFunction.prodPrimeFactors_apply hpr.ne_zero, hpr.primeFactors,
      Finset.prod_singleton]
    have h2r : (2 : ℝ) ≤ p := by exact_mod_cast hpr.two_le
    have hne : (p : ℝ) - 1 ≠ 0 := by linarith
    unfold gfun
    field_simp
    ring
  have hprod : ∏ p ∈ q.primeFactors, (p : ℝ) = q := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hq]
  have hφ0 : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq0)).ne'
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
  have hμ : ((moebius q : ℤ) : ℝ) ^ 2 = 1 := by
    exact_mod_cast moebius_sq_eq_one_of_squarefree hq
  rw [h1, Finset.prod_congr rfl h2, Finset.prod_div_distrib, hprod, ← totient_sqfree hq]
  unfold DS.cQ
  rw [hμ]
  field_simp

theorem inv_pp_nonneg (p : ℕ) (hp : 2 ≤ p) : 0 ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  apply div_nonneg zero_le_one
  nlinarith

theorem inv_pp_le (p : ℕ) (hp : 13 < p) :
    1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 / ((p : ℝ) - 1) ^ 2 := by
  have h2 : (13 : ℝ) < p := by exact_mod_cast hp
  rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith

/-- **`S(r) ≤ 9.68`** (truth `6.7988`): `S = ∑_d G(d)∑_{q, d | q} 1/q ≤ hOdd·∑_d G(d)/d` and
`∑_d G(d)/d ≤ ∏_{p odd}(1 + 1/(p(p−1))) ≤ 1.27398·12/11`, `hOdd ≤ 6.95929`. -/
theorem sR_le_sharp : DS.sR ≤ 9.68 := by
  unfold DS.sR
  set S := DS.oddQ with hSdef
  have hS : ∀ q ∈ S, Odd q ∧ 1 ≤ q ∧ q ≤ 150000 := fun q hq => by
    rw [hSdef] at hq
    unfold DS.oddQ at hq
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hq
    exact ⟨h2, (Finset.mem_Icc.mp h1).1, (Finset.mem_Icc.mp h1).2⟩
  have hSm : ∀ m, Odd m → 1 ≤ m → m ≤ 150000 → m ∈ S := fun m ho h1 h2 => by
    rw [hSdef]
    unfold DS.oddQ
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1, h2⟩, ho⟩
  set s' := S.filter Squarefree with hs'
  have h0 : ∑ q ∈ S, DS.cQ q = ∑ q ∈ s', DS.cQ q := by
    rw [hs', Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs with h
    · rfl
    · unfold DS.cQ
      rw [moebius_eq_zero_of_not_squarefree h]
      simp
  rw [h0]
  set D := s'.biUnion Nat.divisors with hD
  have h1 : ∑ q ∈ s', DS.cQ q = ∑ q ∈ s', ∑ d ∈ q.divisors,
      ArithmeticFunction.prodPrimeFactors gfun d * (1 / (q : ℝ)) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [inv_totient_eq (Finset.mem_filter.mp hq).2, ← Finset.sum_mul, div_eq_mul_one_div]
  have h2 : ∑ q ∈ s', ∑ d ∈ q.divisors,
      ArithmeticFunction.prodPrimeFactors gfun d * (1 / (q : ℝ)) =
      ∑ d ∈ D, ∑ q ∈ s'.filter (d ∣ ·),
        ArithmeticFunction.prodPrimeFactors gfun d * (1 / (q : ℝ)) := by
    refine Finset.sum_comm' fun q d => ?_
    constructor
    · rintro ⟨hq, hd⟩
      exact ⟨Finset.mem_filter.mpr ⟨hq, Nat.dvd_of_mem_divisors hd⟩,
        Finset.mem_biUnion.mpr ⟨q, hq, hd⟩⟩
    · rintro ⟨hq, -⟩
      obtain ⟨hqs, hdq⟩ := Finset.mem_filter.mp hq
      exact ⟨hqs, Nat.mem_divisors.mpr ⟨hdq, (Finset.mem_filter.mp hqs).2.ne_zero⟩⟩
  have hG0 : ∀ d, 0 ≤ ArithmeticFunction.prodPrimeFactors gfun d := by
    intro d
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, ArithmeticFunction.map_zero]
    · rw [ArithmeticFunction.prodPrimeFactors_apply h.ne']
      refine Finset.prod_nonneg fun p hp => ?_
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      unfold gfun
      apply div_nonneg zero_le_one
      linarith
  have hH : ∑ n ∈ S, (1 : ℝ) / n ≤ 6.95929 := by
    have h1 := DS.hOdd_le
    have h3 : Real.log 149999 ≤ Real.log 150000 := Real.log_le_log (by norm_num) (by norm_num)
    have h4 := MajSp.log_r_le
    unfold DS.hOdd at h1
    rw [← hSdef] at h1
    linarith
  have h3 : ∀ d ∈ D, ∑ q ∈ s'.filter (d ∣ ·),
      ArithmeticFunction.prodPrimeFactors gfun d * (1 / (q : ℝ)) ≤
        ArithmeticFunction.prodPrimeFactors gfun d / d * 6.95929 := by
    intro d hd
    obtain ⟨q0, -, hdq0⟩ := Finset.mem_biUnion.mp hd
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hdq0
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    set F := s'.filter (d ∣ ·) with hF
    have hinj : Set.InjOn (fun q : ℕ => q / d) (F : Set ℕ) := by
      intro a ha b hb hab
      have hda := (Finset.mem_filter.mp ha).2
      have hdb := (Finset.mem_filter.mp hb).2
      simp only at hab
      rw [← Nat.mul_div_cancel' hda, ← Nat.mul_div_cancel' hdb, hab]
    have e : ∑ q ∈ F, 1 / (q : ℝ) =
        1 / (d : ℝ) * ∑ m ∈ F.image (fun q : ℕ => q / d), 1 / ((m : ℕ) : ℝ) := by
      rw [Finset.sum_image hinj, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q hq => ?_
      have hdq := (Finset.mem_filter.mp hq).2
      have hc : (q : ℝ) = (d : ℝ) * ((q / d : ℕ) : ℝ) := by
        exact_mod_cast (Nat.mul_div_cancel' hdq).symm
      rw [hc]
      field_simp
    have hsub : F.image (fun q : ℕ => q / d) ⊆ S := by
      intro m hm
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hm
      obtain ⟨hqs', hdq⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqs, hsq⟩ := Finset.mem_filter.mp hqs'
      obtain ⟨hodd, hq1, hq2⟩ := hS q hqs
      have hqe : q = d * (q / d) := (Nat.mul_div_cancel' hdq).symm
      have hodd' : Odd (q / d) := by
        rw [hqe] at hodd
        exact (Nat.odd_mul.mp hodd).2
      have hpos : 1 ≤ q / d := by
        rcases Nat.eq_zero_or_pos (q / d) with h | h
        · rw [h, mul_zero] at hqe
          omega
        · exact h
      exact hSm _ hodd' hpos (le_trans (Nat.div_le_self q d) hq2)
    have hle : ∑ m ∈ F.image (fun q : ℕ => q / d), 1 / ((m : ℕ) : ℝ) ≤
        ∑ n ∈ S, (1 : ℝ) / n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    rw [← Finset.mul_sum, e]
    have hmul := mul_le_mul_of_nonneg_left (hle.trans hH) (by positivity : (0 : ℝ) ≤ 1 / d)
    have hG := hG0 d
    calc ArithmeticFunction.prodPrimeFactors gfun d *
          (1 / (d : ℝ) * ∑ m ∈ F.image (fun q : ℕ => q / d), 1 / ((m : ℕ) : ℝ))
        ≤ ArithmeticFunction.prodPrimeFactors gfun d * (1 / (d : ℝ) * 6.95929) :=
          mul_le_mul_of_nonneg_left hmul hG
      _ = ArithmeticFunction.prodPrimeFactors gfun d / d * 6.95929 := by ring
  set M := s'.sup id with hM
  have hD' : ∀ d ∈ D, Squarefree d ∧ d.primeFactors ⊆ oddPrimes M := by
    intro d hd
    obtain ⟨q, hq, hdq⟩ := Finset.mem_biUnion.mp hd
    obtain ⟨hqs, hsq⟩ := Finset.mem_filter.mp hq
    have hdvd := Nat.dvd_of_mem_divisors hdq
    refine ⟨hsq.squarefree_of_dvd hdvd, fun p hp => ?_⟩
    have hpq := Nat.primeFactors_mono hdvd hsq.ne_zero hp
    exact mem_oddPrimes_of_dvd (hS q hqs).1 (Nat.pos_of_ne_zero hsq.ne_zero)
      (Finset.le_sup (f := id) hq) hpq
  have hGd : ∀ d ∈ D, ArithmeticFunction.prodPrimeFactors gfun d / d =
      ∏ p ∈ d.primeFactors, 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    intro d hd
    have hsq := (hD' d hd).1
    have hprod : ∏ p ∈ d.primeFactors, (p : ℝ) = d := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
    rw [ArithmeticFunction.prodPrimeFactors_apply hsq.ne_zero, ← hprod,
      ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    unfold gfun
    rw [div_div, mul_comm]
  have h5 : ∑ d ∈ D, ArithmeticFunction.prodPrimeFactors gfun d / d ≤
      1.27398 * (1 / (1 - 1 / 12)) := by
    rw [Finset.sum_congr rfl hGd]
    have hE := sum_le_euler (fun p => 1 / ((p : ℝ) * ((p : ℝ) - 1))) (oddPrimes M)
      (fun p hp => inv_pp_nonneg p (Finset.mem_filter.mp hp).2.1.two_le) D hD'
    have hO := odd_prod_le (fun p => 1 / ((p : ℝ) * ((p : ℝ) - 1))) 1 zero_le_one (oddPrimes M)
      (fun p hp => (Finset.mem_filter.mp hp).2) (fun p hp => inv_pp_nonneg p hp)
      (fun p hp => inv_pp_le p hp)
    have hS5 : ∏ p ∈ ({3, 5, 7, 11, 13} : Finset ℕ), (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤
        1.27398 := by
      rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
      norm_num
    have hexp := exp_le_inv (1 / 12) (by norm_num)
    calc _ ≤ _ := hE
      _ ≤ _ := hO
      _ ≤ 1.27398 * (1 / (1 - 1 / 12)) :=
          mul_le_mul hS5 hexp (Real.exp_pos _).le (by norm_num)
  rw [h1, h2]
  refine le_trans (Finset.sum_le_sum h3) ?_
  rw [← Finset.sum_mul]
  have h6 := mul_le_mul_of_nonneg_right h5 (by norm_num : (0 : ℝ) ≤ 6.95929)
  have h7 : 1.27398 * (1 / (1 - 1 / 12)) * 6.95929 ≤ (9.68 : ℝ) := by norm_num
  linarith

end ZSec
/-! ### `Z_{η²,2}(x)` from below: primes, a step minorant, and `θ` -/

section ZGen

/-- `θ(v) − θ(u) = ∑_{⌊u⌋ < p ≤ ⌊v⌋} log p`. -/
theorem theta_sub (u v : ℝ) (h : ⌊u⌋₊ ≤ ⌊v⌋₊) :
    Chebyshev.theta v - Chebyshev.theta u =
      ∑ p ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊, if p.Prime then Real.log p else 0 := by
  unfold Chebyshev.theta
  rw [Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le ⌊u⌋₊) h]
  ring

/-- The `Ioc` pieces of a monotone sequence of cut points telescope. -/
theorem sum_Ioc_tele (f : ℕ → ℝ) (N : ℕ → ℕ) (hN : ∀ i, N i ≤ N (i + 1)) :
    ∀ k : ℕ, ∑ i ∈ Finset.range k, ∑ n ∈ Finset.Ioc (N i) (N (i + 1)), f n =
      ∑ n ∈ Finset.Ioc (N 0) (N k), f n := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hmono : N 0 ≤ N k := by
      clear ih
      induction k with
      | zero => exact le_rfl
      | succ j hj => exact le_trans hj (hN j)
    rw [Finset.sum_range_succ, ih, Finset.sum_Ioc_consecutive _ hmono (hN k)]

/-- **`Z` from below**: for a step minorant `m_i ≤ η(t)²` on `(a_i, a_{i+1}]`,
`log(a₀x)·∑_i m_i(θ(a_{i+1}x) − θ(a_i x)) ≤ ∑_n Λ(n)²η(n/x)²` (only primes counted, `Λ(p) = log p
≥ log(a₀x)`). -/
theorem Z_ge (η : ℝ → ℝ) (x : ℝ) (hx : 0 < x) (k : ℕ) (a m : ℕ → ℝ) (ha0 : 0 < a 0)
    (hmono : ∀ i, a i ≤ a (i + 1)) (hm0 : ∀ i < k, 0 ≤ m i)
    (hm : ∀ i < k, ∀ t, a i < t → t ≤ a (i + 1) → m i ≤ η t ^ 2)
    (hs : Summable (fun n : ℕ => Λ n * |η ((n : ℝ) / x)|)) (hx1 : 1 ≤ a 0 * x) :
    Real.log (a 0 * x) * ∑ i ∈ Finset.range k,
        m i * (Chebyshev.theta (a (i + 1) * x) - Chebyshev.theta (a i * x)) ≤
      ∑' n : ℕ, (Λ n) ^ 2 * η ((n : ℝ) / x) ^ 2 := by
  have hapos : ∀ i, a 0 ≤ a i := by
    intro i
    induction i with
    | zero => exact le_rfl
    | succ j hj => exact le_trans hj (hmono j)
  set N : ℕ → ℕ := fun i => ⌊a i * x⌋₊ with hNdef
  have hN : ∀ i, N i ≤ N (i + 1) := fun i =>
    Nat.floor_le_floor (mul_le_mul_of_nonneg_right (hmono i) hx.le)
  set f : ℕ → ℝ := fun n => (Λ n) ^ 2 * η ((n : ℝ) / x) ^ 2 with hfdef
  have hf0 : ∀ n, 0 ≤ f n := fun n => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  -- summability of `f`
  have hS : ∀ n, Λ n * |η ((n : ℝ) / x)| ≤ ∑' j, Λ j * |η ((j : ℝ) / x)| := fun n =>
    hs.le_tsum n fun j _ => mul_nonneg vonMangoldt_nonneg (abs_nonneg _)
  have hfs : Summable f := by
    refine Summable.of_nonneg_of_le hf0 (fun n => ?_)
      (hs.mul_left (∑' j, Λ j * |η ((j : ℝ) / x)|))
    have h1 := hS n
    have h0 : 0 ≤ Λ n * |η ((n : ℝ) / x)| := mul_nonneg vonMangoldt_nonneg (abs_nonneg _)
    have e : f n = (Λ n * |η ((n : ℝ) / x)|) * (Λ n * |η ((n : ℝ) / x)|) := by
      simp only [hfdef]
      rw [← sq_abs (η ((n : ℝ) / x))]
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_right h1 h0
  -- the per-piece inequality
  have hlog0 : 0 ≤ Real.log (a 0 * x) := Real.log_nonneg hx1
  have hpiece : ∀ i < k, Real.log (a 0 * x) * (m i * (Chebyshev.theta (a (i + 1) * x) -
      Chebyshev.theta (a i * x))) ≤ ∑ n ∈ Finset.Ioc (N i) (N (i + 1)), f n := by
    intro i hi
    rw [theta_sub _ _ (hN i), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    split_ifs with hp
    · obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
      have hai : 0 ≤ a i * x := mul_nonneg (le_trans ha0.le (hapos i)) hx.le
      have hlt : a i * x < n := (Nat.floor_lt hai).mp hn1
      have hle : (n : ℝ) ≤ a (i + 1) * x := by
        have h := (Nat.le_floor_iff (mul_nonneg (le_trans ha0.le (hapos (i + 1))) hx.le)).mp hn2
        exact h
      have ht1 : a i < (n : ℝ) / x := by rw [lt_div_iff₀ hx]; linarith
      have ht2 : (n : ℝ) / x ≤ a (i + 1) := by rw [div_le_iff₀ hx]; linarith
      have hmi := hm i hi _ ht1 ht2
      have hΛ : Λ n = Real.log n := vonMangoldt_apply_prime hp
      have hlogn : Real.log (a 0 * x) ≤ Real.log n := by
        refine Real.log_le_log (by linarith) ?_
        have := mul_le_mul_of_nonneg_right (hapos i) hx.le
        linarith
      have hm0' := hm0 i hi
      simp only [hfdef]
      rw [hΛ]
      have k1 : Real.log (a 0 * x) * (m i * Real.log n) ≤ Real.log n * (m i * Real.log n) :=
        mul_le_mul_of_nonneg_right hlogn (mul_nonneg hm0' (le_trans hlog0 hlogn))
      have k2 : Real.log n * (m i * Real.log n) ≤
          Real.log n * (η ((n : ℝ) / x) ^ 2 * Real.log n) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmi (le_trans hlog0 hlogn))
          (le_trans hlog0 hlogn)
      nlinarith
    · rw [mul_zero, mul_zero]
      exact hf0 n
  calc Real.log (a 0 * x) * ∑ i ∈ Finset.range k,
        m i * (Chebyshev.theta (a (i + 1) * x) - Chebyshev.theta (a i * x))
      = ∑ i ∈ Finset.range k, Real.log (a 0 * x) *
          (m i * (Chebyshev.theta (a (i + 1) * x) - Chebyshev.theta (a i * x))) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range k, ∑ n ∈ Finset.Ioc (N i) (N (i + 1)), f n :=
        Finset.sum_le_sum fun i hi => hpiece i (Finset.mem_range.mp hi)
    _ = ∑ n ∈ Finset.Ioc (N 0) (N k), f n := sum_Ioc_tele f N hN k
    _ ≤ ∑' n, f n := hfs.sum_le_tsum _ fun n _ => hf0 n

end ZGen
/-! ### [ZvsL] at `η₊` -/

section ZPlus

/-- `t·e^{−t²/2} ≤ 1` (`t ≤ 1 + t²/2 ≤ e^{t²/2}`). -/
theorem t_exp_le_one (t : ℝ) : t * Real.exp (-t ^ 2 / 2) ≤ 1 := by
  have h1 := Real.add_one_le_exp (t ^ 2 / 2)
  have h2 : Real.exp (t ^ 2 / 2) * Real.exp (-t ^ 2 / 2) = 1 := by
    rw [← Real.exp_add, show t ^ 2 / 2 + -t ^ 2 / 2 = 0 by ring, Real.exp_zero]
  have h3 : 0 < Real.exp (-t ^ 2 / 2) := Real.exp_pos _
  have h4 : t ≤ t ^ 2 / 2 + 1 := by nlinarith [sq_nonneg (t - 1)]
  nlinarith

/-- **`η₊²` on an interval** `(lo, hi] ⊆ [0, 2]`: with `c ≥ max((lo−1)², (hi−1)²)/2`,
`η₊(t) ≥ lo³(2 − hi)³(1 − c) − 2.7·10⁻⁴` (`η∘ = t³(2−t)³e^{−(t−1)²/2}`, `e^{−u} ≥ 1 − u`,
`|h₂₀₀ − h| ≤ 2.7·10⁻⁴`, `te^{−t²/2} ≤ 1`). -/
theorem etaPlus_sq_ge (lo hi c : ℝ) (h0 : 0 ≤ lo) (h2 : hi ≤ 2) (hc1 : (lo - 1) ^ 2 / 2 ≤ c)
    (hc2 : (hi - 1) ^ 2 / 2 ≤ c) (hpos : 2.7e-4 ≤ lo ^ 3 * (2 - hi) ^ 3 * (1 - c))
    (t : ℝ) (ht1 : lo < t) (ht2 : t ≤ hi) :
    (lo ^ 3 * (2 - hi) ^ 3 * (1 - c) - 2.7e-4) ^ 2 ≤ HW.etaPlus t ^ 2 := by
  have ht0 : 0 < t := lt_of_le_of_lt h0 ht1
  have ht2' : t ≤ 2 := le_trans ht2 h2
  have hcirc := HW.etaCirc_eq ht0.le ht2'
  have htc : (t - 1) ^ 2 / 2 ≤ c := by
    rcases le_or_gt t 1 with h | h
    · have : (t - 1) ^ 2 ≤ (lo - 1) ^ 2 := by nlinarith
      linarith
    · have : (t - 1) ^ 2 ≤ (hi - 1) ^ 2 := by nlinarith
      linarith
  have hexp : 1 - c ≤ Real.exp (-(t - 1) ^ 2 / 2) := by
    have := Real.add_one_le_exp (-(t - 1) ^ 2 / 2)
    linarith
  have hlo3 : lo ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ h0 ht1.le 3
  have hhi3 : (2 - hi) ^ 3 ≤ (2 - t) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hlh : 0 ≤ lo ^ 3 * (2 - hi) ^ 3 := mul_nonneg (pow_nonneg h0 3) (pow_nonneg (by linarith) 3)
  have h1c : 0 ≤ 1 - c := by
    by_contra hneg
    have : lo ^ 3 * (2 - hi) ^ 3 * (1 - c) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hlh (le_of_lt (lt_of_not_ge hneg))
    linarith
  have hcirc_ge : lo ^ 3 * (2 - hi) ^ 3 * (1 - c) ≤ HW.etaCirc t := by
    rw [hcirc]
    calc lo ^ 3 * (2 - hi) ^ 3 * (1 - c) ≤ t ^ 3 * (2 - t) ^ 3 * (1 - c) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hlo3 hhi3 (pow_nonneg (by linarith) 3)
            (pow_nonneg ht0.le 3)) h1c
      _ ≤ t ^ 3 * (2 - t) ^ 3 * Real.exp (-(t - 1) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg (pow_nonneg ht0.le 3)
            (pow_nonneg (by linarith) 3))
  have hdiff : |HW.etaPlus t - HW.etaCirc t| ≤ 2.7e-4 := by
    have e : HW.etaPlus t - HW.etaCirc t =
        (HW.hH 200 t - HW.hFun t) * (t * Real.exp (-t ^ 2 / 2)) := by
      unfold HW.etaPlus HW.etaCirc
      ring
    have hw0 : 0 ≤ t * Real.exp (-t ^ 2 / 2) := mul_nonneg ht0.le (Real.exp_pos _).le
    rw [e, abs_mul, abs_of_nonneg hw0]
    have hb := BS.band_sharp t ht0
    calc |HW.hH 200 t - HW.hFun t| * (t * Real.exp (-t ^ 2 / 2)) ≤ 2.7e-4 * 1 :=
          mul_le_mul hb (t_exp_le_one t) hw0 (by norm_num)
      _ = 2.7e-4 := mul_one _
  have hge : lo ^ 3 * (2 - hi) ^ 3 * (1 - c) - 2.7e-4 ≤ HW.etaPlus t := by
    have := (abs_le.mp hdiff).1
    linarith
  exact pow_le_pow_left₀ (by linarith) hge 2

/-- The cut points `a_i = (10 + i)/20` on `[1/2, 9/5]`. -/
noncomputable def aP (i : ℕ) : ℝ := ((10 + i : ℕ) : ℝ) / 20

/-- `c_i = max((a_i − 1)², (a_{i+1} − 1)²)/2` (no interval straddles `1`). -/
noncomputable def cP (i : ℕ) : ℝ :=
  if i < 10 then (aP i - 1) ^ 2 / 2 else (aP (i + 1) - 1) ^ 2 / 2

/-- The step minorant of `η₊²`: `m_i ≤ (a_i³(2 − a_{i+1})³(1 − c_i) − 2.7·10⁻⁴)²`, rounded down
to four decimals (`zP_facts`). -/
noncomputable def mQ : ℕ → ℝ
  | 0 => 0.1110
  | 1 => 0.1681
  | 2 => 0.2387
  | 3 => 0.3204
  | 4 => 0.4089
  | 5 => 0.4983
  | 6 => 0.5819
  | 7 => 0.6527
  | 8 => 0.7046
  | 9 => 0.7327
  | 10 => 0.7327
  | 11 => 0.7046
  | 12 => 0.6527
  | 13 => 0.5819
  | 14 => 0.4983
  | 15 => 0.4089
  | 16 => 0.3204
  | 17 => 0.2387
  | 18 => 0.1681
  | 19 => 0.1110
  | 20 => 0.0679
  | 21 => 0.0380
  | 22 => 0.0191
  | 23 => 0.0083
  | 24 => 0.0030
  | 25 => 0.0008
  | _ => 0

theorem aP_mono (i : ℕ) : aP i ≤ aP (i + 1) := by
  unfold aP
  push_cast
  linarith

/-- `θ` at both ends, `y ≥ 10²⁴`. -/
theorem theta_both (y : ℝ) (hy : 10 ^ 24 ≤ y) :
    0.92079 * y ≤ Chebyshev.theta y ∧ Chebyshev.theta y ≤ 1.11 * y :=
  ⟨theta_ge_lin y hy, theta_le_lin y (by linarith)⟩

/-- `log x ≥ 61` for `x ≥ 4.9·10²⁶`. -/
theorem log_X0_ge (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : 61 ≤ Real.log x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  rw [Real.le_log_iff_exp_le hx0]
  have h1 : Real.exp 61 = Real.exp 1 ^ 61 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 : Real.exp 1 ^ 61 ≤ 2.7182818286 ^ 61 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le h2.le 61
  have h4 : (2.7182818286 : ℝ) ^ 61 ≤ 49 * 10 ^ 25 := by norm_num
  linarith
/-- The side conditions of `etaPlus_sq_ge` at the 26 steps. -/
theorem zP_facts : ∀ i < 26, 0 ≤ aP i ∧ aP (i + 1) ≤ 2 ∧ (aP i - 1) ^ 2 / 2 ≤ cP i ∧
    (aP (i + 1) - 1) ^ 2 / 2 ≤ cP i ∧ 2.7e-4 ≤ aP i ^ 3 * (2 - aP (i + 1)) ^ 3 * (1 - cP i) := by
  intro i hi
  interval_cases i <;> norm_num [aP, cP]

/-- The rounded minorant is below the exact one, and nonnegative. -/
theorem zP_mQ : ∀ i < 26, 0 ≤ mQ i ∧
    mQ i ≤ (aP i ^ 3 * (2 - aP (i + 1)) ^ 3 * (1 - cP i) - 2.7e-4) ^ 2 := by
  intro i hi
  interval_cases i <;> norm_num [aP, cP, mQ]

/-- `a_i ≥ 1/2`, so `a_i x ≥ 10²⁴` at `x ≥ 4.9·10²⁶`. -/
theorem aP_x_ge (k : ℕ) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : 10 ^ 24 ≤ aP k * x := by
  have h : (1 : ℝ) / 2 ≤ aP k := by
    unfold aP
    push_cast
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  nlinarith

/-- **The Abel sum at `η₊`**: `∑_i m_i(θ(a_{i+1}x) − θ(a_i x)) ≥ 0.3x` (bracket `0.31620`). -/
theorem zP_sum_ge (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : 0.3 * x ≤ ∑ i ∈ Finset.range 26,
    mQ i * (Chebyshev.theta (aP (i + 1) * x) - Chebyshev.theta (aP i * x)) := by
  have t0 := theta_both (aP 0 * x) (aP_x_ge 0 x hx)
  have e0 : aP 0 * x = 10 / 20 * x := by rw [show aP 0 = 10 / 20 by norm_num [aP]]
  have t1 := theta_both (aP 1 * x) (aP_x_ge 1 x hx)
  have e1 : aP 1 * x = 11 / 20 * x := by rw [show aP 1 = 11 / 20 by norm_num [aP]]
  have t2 := theta_both (aP 2 * x) (aP_x_ge 2 x hx)
  have e2 : aP 2 * x = 12 / 20 * x := by rw [show aP 2 = 12 / 20 by norm_num [aP]]
  have t3 := theta_both (aP 3 * x) (aP_x_ge 3 x hx)
  have e3 : aP 3 * x = 13 / 20 * x := by rw [show aP 3 = 13 / 20 by norm_num [aP]]
  have t4 := theta_both (aP 4 * x) (aP_x_ge 4 x hx)
  have e4 : aP 4 * x = 14 / 20 * x := by rw [show aP 4 = 14 / 20 by norm_num [aP]]
  have t5 := theta_both (aP 5 * x) (aP_x_ge 5 x hx)
  have e5 : aP 5 * x = 15 / 20 * x := by rw [show aP 5 = 15 / 20 by norm_num [aP]]
  have t6 := theta_both (aP 6 * x) (aP_x_ge 6 x hx)
  have e6 : aP 6 * x = 16 / 20 * x := by rw [show aP 6 = 16 / 20 by norm_num [aP]]
  have t7 := theta_both (aP 7 * x) (aP_x_ge 7 x hx)
  have e7 : aP 7 * x = 17 / 20 * x := by rw [show aP 7 = 17 / 20 by norm_num [aP]]
  have t8 := theta_both (aP 8 * x) (aP_x_ge 8 x hx)
  have e8 : aP 8 * x = 18 / 20 * x := by rw [show aP 8 = 18 / 20 by norm_num [aP]]
  have t9 := theta_both (aP 9 * x) (aP_x_ge 9 x hx)
  have e9 : aP 9 * x = 19 / 20 * x := by rw [show aP 9 = 19 / 20 by norm_num [aP]]
  have t10 := theta_both (aP 10 * x) (aP_x_ge 10 x hx)
  have e10 : aP 10 * x = 20 / 20 * x := by rw [show aP 10 = 20 / 20 by norm_num [aP]]
  have t11 := theta_both (aP 11 * x) (aP_x_ge 11 x hx)
  have e11 : aP 11 * x = 21 / 20 * x := by rw [show aP 11 = 21 / 20 by norm_num [aP]]
  have t12 := theta_both (aP 12 * x) (aP_x_ge 12 x hx)
  have e12 : aP 12 * x = 22 / 20 * x := by rw [show aP 12 = 22 / 20 by norm_num [aP]]
  have t13 := theta_both (aP 13 * x) (aP_x_ge 13 x hx)
  have e13 : aP 13 * x = 23 / 20 * x := by rw [show aP 13 = 23 / 20 by norm_num [aP]]
  have t14 := theta_both (aP 14 * x) (aP_x_ge 14 x hx)
  have e14 : aP 14 * x = 24 / 20 * x := by rw [show aP 14 = 24 / 20 by norm_num [aP]]
  have t15 := theta_both (aP 15 * x) (aP_x_ge 15 x hx)
  have e15 : aP 15 * x = 25 / 20 * x := by rw [show aP 15 = 25 / 20 by norm_num [aP]]
  have t16 := theta_both (aP 16 * x) (aP_x_ge 16 x hx)
  have e16 : aP 16 * x = 26 / 20 * x := by rw [show aP 16 = 26 / 20 by norm_num [aP]]
  have t17 := theta_both (aP 17 * x) (aP_x_ge 17 x hx)
  have e17 : aP 17 * x = 27 / 20 * x := by rw [show aP 17 = 27 / 20 by norm_num [aP]]
  have t18 := theta_both (aP 18 * x) (aP_x_ge 18 x hx)
  have e18 : aP 18 * x = 28 / 20 * x := by rw [show aP 18 = 28 / 20 by norm_num [aP]]
  have t19 := theta_both (aP 19 * x) (aP_x_ge 19 x hx)
  have e19 : aP 19 * x = 29 / 20 * x := by rw [show aP 19 = 29 / 20 by norm_num [aP]]
  have t20 := theta_both (aP 20 * x) (aP_x_ge 20 x hx)
  have e20 : aP 20 * x = 30 / 20 * x := by rw [show aP 20 = 30 / 20 by norm_num [aP]]
  have t21 := theta_both (aP 21 * x) (aP_x_ge 21 x hx)
  have e21 : aP 21 * x = 31 / 20 * x := by rw [show aP 21 = 31 / 20 by norm_num [aP]]
  have t22 := theta_both (aP 22 * x) (aP_x_ge 22 x hx)
  have e22 : aP 22 * x = 32 / 20 * x := by rw [show aP 22 = 32 / 20 by norm_num [aP]]
  have t23 := theta_both (aP 23 * x) (aP_x_ge 23 x hx)
  have e23 : aP 23 * x = 33 / 20 * x := by rw [show aP 23 = 33 / 20 by norm_num [aP]]
  have t24 := theta_both (aP 24 * x) (aP_x_ge 24 x hx)
  have e24 : aP 24 * x = 34 / 20 * x := by rw [show aP 24 = 34 / 20 by norm_num [aP]]
  have t25 := theta_both (aP 25 * x) (aP_x_ge 25 x hx)
  have e25 : aP 25 * x = 35 / 20 * x := by rw [show aP 25 = 35 / 20 by norm_num [aP]]
  have t26 := theta_both (aP 26 * x) (aP_x_ge 26 x hx)
  have e26 : aP 26 * x = 36 / 20 * x := by rw [show aP 26 = 36 / 20 by norm_num [aP]]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, mQ]
  linarith [t0.1, t0.2, e0, t1.1, t1.2, e1, t2.1, t2.2, e2, t3.1, t3.2, e3, t4.1, t4.2, e4,
    t5.1, t5.2, e5, t6.1, t6.2, e6, t7.1, t7.2, e7, t8.1, t8.2, e8, t9.1, t9.2, e9,
    t10.1, t10.2, e10, t11.1, t11.2, e11, t12.1, t12.2, e12, t13.1, t13.2, e13,
    t14.1, t14.2, e14, t15.1, t15.2, e15, t16.1, t16.2, e16, t17.1, t17.2, e17,
    t18.1, t18.2, e18, t19.1, t19.2, e19, t20.1, t20.2, e20, t21.1, t21.2, e21,
    t22.1, t22.2, e22, t23.1, t23.2, e23, t24.1, t24.2, e24, t25.1, t25.2, e25,
    t26.1, t26.2, e26]

/-- **[ZvsL] PROVED at Helfgott's `η₊`**: `L_{r,δ₀}(η₊) ≤ 2S(r)|η₊|₂² ≤ 2·9.68·0.81² = 12.71`,
while `Z_{η₊²,2}(x) ≥ log(x/2)·∑_i m_i(θ(a_{i+1}x) − θ(a_i x))/x ≥ 60.3·0.3` by 26 steps of `1/20`
on `[1/2, 9/5]` and `0.92079y ≤ θ(y) ≤ 1.11y`. -/
theorem zvsL_plus : NF.ZvsL HW.etaPlus := by
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hp1 : Integrable HW.etaPlus (volume.restrict (Set.Ioi 0)) := RW.integrable_etaPlus
  have hp2 : Integrable (fun t => HW.etaPlus t ^ 2) (volume.restrict (Set.Ioi 0)) :=
    DP.sq_integrable_of_memLp _ RW.memLp_etaPlus_two
  have hl := DS.lRD_le HW.etaPlus (DP.mardiQ_of _ hp1 hp2)
  have hsR := sR_le_sharp
  obtain ⟨-, -, -, -, -, -, -, -, hl2⟩ :=
    EN.normsB27_helf (EN.bandSharp27_of_25 BS.bandSharp25)
  have hl20 := MajSp.l2_nonneg HW.etaPlus
  have hsR0 : 0 ≤ DS.sR := DS.sR_nonneg
  have hL : DS.lRD HW.etaPlus ≤ 12.71 := by
    have h1 : MajSp.l2 HW.etaPlus ^ 2 ≤ 0.81 ^ 2 := pow_le_pow_left₀ hl20 hl2 2
    have h2 := mul_le_mul hsR h1 (sq_nonneg _) (by norm_num)
    nlinarith
  have hi := zP_facts
  have hZ := Z_ge HW.etaPlus x hx0 26 aP mQ (by norm_num [aP]) aP_mono
    (fun i hi' => (zP_mQ i hi').1)
    (fun i hi' t ht1 ht2 => by
      obtain ⟨h0, h2, hc1, hc2, hpos⟩ := hi i hi'
      exact le_trans (zP_mQ i hi').2
        (etaPlus_sq_ge (aP i) (aP (i + 1)) (cP i) h0 h2 hc1 hc2 hpos t ht1 ht2))
    (NF.summW_plus x hx) (by norm_num [aP]; linarith)
  have hlog : 60.3 ≤ Real.log (aP 0 * x) := by
    have h1 := log_X0_ge x hx
    have e : aP 0 * x = x / 2 := by norm_num [aP]; ring
    rw [e, Real.log_div hx0.ne' two_ne_zero]
    have h2 := Real.log_two_lt_d9
    linarith
  have hK := zP_sum_ge x hx
  have hS0 : 0 ≤ ∑ i ∈ Finset.range 26,
      mQ i * (Chebyshev.theta (aP (i + 1) * x) - Chebyshev.theta (aP i * x)) := by linarith
  have h60 := mul_le_mul hlog hK (by positivity) (le_trans (by norm_num) hlog)
  have e : MajSp.zk (fun t => HW.etaPlus t ^ 2) 2 x =
      (∑' n : ℕ, (Λ n) ^ 2 * HW.etaPlus ((n : ℝ) / x) ^ 2) / x := rfl
  rw [e, le_div_iff₀ hx0]
  nlinarith

end ZPlus
/-! ## [DPoint] -/

section DPointSec

open DirichletCharacter Principia.Common.Goldbach

/-- The character coefficient of `eq:beatit`: `c(n) = (1/φ(q))∑_χ τ(χ̄)χ(a)χ*(n)`. -/
noncomputable def cf (q : ℕ) [NeZero q] (a n : ℕ) : ℂ :=
  (∑ χ : DirichletCharacter ℂ q, gaussSum χ⁻¹ ZMod.stdAddChar * χ (a : ZMod q) *
    χ.primitiveCharacter (n : ZMod χ.conductor)) / (q.totient : ℂ)

theorem natCast_isCoprime {n q : ℕ} (h : Nat.Coprime n q) : IsCoprime (n : ℤ) (q : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
  exact h

/-- On `(n, q) = 1` the expansion is exact: `c(n) = e(an/q)`. -/
theorem cf_unit (q : ℕ) [NeZero q] (a n : ℕ) (ha : Nat.Coprime a q) (hn : Nat.Coprime n q) :
    cf q a n = ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q)) := by
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hp : ∀ χ : DirichletCharacter ℂ q, χ.primitiveCharacter (n : ZMod χ.conductor) =
      χ (n : ZMod q) := by
    intro χ
    have h := χ.primitiveCharacter_apply_of_isCoprime (natCast_isCoprime hn)
    simpa only [Int.cast_natCast] using h
  have hu : IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime n q).mpr hn
  have h2 := GaussInduced.sum_char_gaussSum (N := q) (ZMod.unitOfCoprime a ha) (n : ZMod q)
  rw [ZMod.coe_unitOfCoprime, if_pos hu] at h2
  unfold cf
  simp_rw [hp]
  have e : ∑ χ : DirichletCharacter ℂ q, gaussSum χ⁻¹ ZMod.stdAddChar * χ (a : ZMod q) *
      χ (n : ZMod q) = ∑ χ : DirichletCharacter ℂ q, gaussSum χ⁻¹ ZMod.stdAddChar *
        (χ (a : ZMod q) * χ (n : ZMod q)) := Finset.sum_congr rfl fun χ _ => by ring
  rw [e, h2]
  field_simp

/-- `χ*(p^k) ≠ 0` forces the conductor of `χ` to divide the `p`-free part `m` of `q = p^v m`. -/
theorem cond_dvd_of_ne {q p m v k : ℕ} (hk : k ≠ 0) (hqm : q = p ^ v * m)
    (χ : DirichletCharacter ℂ q)
    (h : χ.primitiveCharacter ((p ^ k : ℕ) : ZMod χ.conductor) ≠ 0) : χ.conductor ∣ m := by
  have h' : χ.primitiveCharacter (((p ^ k : ℕ) : ℤ) : ZMod χ.conductor) ≠ 0 := by
    rw [Int.cast_natCast]
    exact h
  rw [apply_ne_zero_iff, Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast] at h'
  have h1 : Nat.Coprime p χ.conductor := Nat.Coprime.coprime_dvd_left (dvd_pow_self p hk) h'
  have hc : Nat.Coprime (p ^ v) χ.conductor := Nat.Coprime.pow_left v h1
  have hd : χ.conductor ∣ p ^ v * m := by
    rw [← hqm]
    exact χ.conductor_dvd_level
  exact hc.symm.dvd_of_dvd_mul_left hd

/-- ... hence `χ` is induced from level `m`. -/
theorem mem_range_of_ne {q p m v k : ℕ} (hk : k ≠ 0) (hqm : q = p ^ v * m) (hmq : m ∣ q)
    (χ : DirichletCharacter ℂ q)
    (h : χ.primitiveCharacter ((p ^ k : ℕ) : ZMod χ.conductor) ≠ 0) :
    χ ∈ Set.range (changeLevel (R := ℂ) hmq) := by
  have hfm := cond_dvd_of_ne hk hqm χ h
  refine ⟨changeLevel hfm χ.primitiveCharacter, ?_⟩
  rw [← changeLevel_trans]
  exact χ.changeLevel_primitiveCharacter

/-- The summand at an induced character `χ = ψ ↑ q`, `ψ` mod `m`, `q/m = p^v`. -/
theorem term_cl {q m p v k : ℕ} [NeZero q] [NeZero m] (hmq : m ∣ q) (hqm : q / m = p ^ v)
    (hcop : Nat.Coprime p m) (a : ℕ) (ha : Nat.Coprime a q) (ψ : DirichletCharacter ℂ m) :
    gaussSum (changeLevel hmq ψ)⁻¹ ZMod.stdAddChar * changeLevel hmq ψ (a : ZMod q) *
      (changeLevel hmq ψ).primitiveCharacter
        ((p ^ k : ℕ) : ZMod (changeLevel hmq ψ).conductor) =
    (moebius (p ^ v) : ℂ) * (ψ⁻¹ ((p ^ v : ℕ) : ZMod m) * gaussSum ψ⁻¹ ZMod.stdAddChar *
      ψ (a : ZMod m) * ψ ((p ^ k : ℕ) : ZMod m)) := by
  rw [← map_inv, GaussInduced.gaussSum_changeLevel ψ⁻¹ q hmq, hqm]
  have h1 : changeLevel hmq ψ (a : ZMod q) = ψ (a : ZMod m) := by
    have h := changeLevel_eq_cast_of_dvd' ψ hmq (natCast_isCoprime ha)
    simpa only [Int.cast_natCast] using h
  have h2 : (changeLevel hmq ψ).primitiveCharacter
      ((p ^ k : ℕ) : ZMod (changeLevel hmq ψ).conductor) = ψ ((p ^ k : ℕ) : ZMod m) := by
    have h := primitiveCharacter_changeLevel_apply hmq ψ ((p ^ k : ℕ) : ℤ)
    have h' := ψ.primitiveCharacter_apply_of_isCoprime
      (natCast_isCoprime (Nat.Coprime.pow_left k hcop))
    simp only [Int.cast_natCast] at h h'
    rw [h, h']
  rw [h1, h2]
  ring

/-- **The character sum at `n = p^k`, `p ∣ q`**, is at most `φ(m)` (`m` the `p`-free part):
`0` when `p² ∣ q`, and `−φ(m)e(ap^{k−1}/m)` when `p ∥ q`. -/
theorem sum_pow_le {q m p v : ℕ} [NeZero q] [NeZero m] (hp : p.Prime) (hv : 1 ≤ v)
    (hqm : q = p ^ v * m) (hcop : Nat.Coprime p m) (a k : ℕ) (hk : k ≠ 0)
    (ha : Nat.Coprime a q) :
    ‖∑ χ : DirichletCharacter ℂ q, gaussSum χ⁻¹ ZMod.stdAddChar * χ (a : ZMod q) *
      χ.primitiveCharacter ((p ^ k : ℕ) : ZMod χ.conductor)‖ ≤ m.totient := by
  have hmq : m ∣ q := ⟨p ^ v, by rw [hqm, mul_comm]⟩
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hqdm : q / m = p ^ v := by
    rw [hqm]
    exact Nat.mul_div_cancel _ hm0
  have ham : Nat.Coprime a m := Nat.Coprime.coprime_dvd_right hmq ha
  have hre := Fintype.sum_of_injective (changeLevel (R := ℂ) hmq) (changeLevel_injective hmq)
    (fun ψ => gaussSum (changeLevel hmq ψ)⁻¹ ZMod.stdAddChar * changeLevel hmq ψ (a : ZMod q) *
      (changeLevel hmq ψ).primitiveCharacter
        ((p ^ k : ℕ) : ZMod (changeLevel hmq ψ).conductor))
    (fun χ : DirichletCharacter ℂ q => gaussSum χ⁻¹ ZMod.stdAddChar * χ (a : ZMod q) *
      χ.primitiveCharacter ((p ^ k : ℕ) : ZMod χ.conductor))
    (fun χ hχ => by
      by_contra hne
      apply hχ
      refine mem_range_of_ne hk hqm hmq χ fun h0 => hne ?_
      rw [h0, mul_zero])
    (fun _ => rfl)
  rw [← hre]
  simp_rw [term_cl hmq hqdm hcop a ha]
  rw [← Finset.mul_sum, norm_mul]
  rcases Nat.lt_or_ge v 2 with hv2 | hv2
  · have hv1 : v = 1 := by omega
    subst hv1
    have hpu : IsUnit ((p : ℕ) : ZMod m) := (ZMod.isUnit_iff_coprime p m).mpr hcop
    have hpk : IsUnit ((p ^ (k - 1) : ℕ) : ZMod m) :=
      (ZMod.isUnit_iff_coprime _ m).mpr (Nat.Coprime.pow_left _ hcop)
    have hterm : ∀ ψ : DirichletCharacter ℂ m, ψ⁻¹ ((p ^ 1 : ℕ) : ZMod m) *
        gaussSum ψ⁻¹ ZMod.stdAddChar * ψ (a : ZMod m) * ψ ((p ^ k : ℕ) : ZMod m) =
          gaussSum ψ⁻¹ ZMod.stdAddChar *
            (ψ ((ZMod.unitOfCoprime a ham : (ZMod m)ˣ) : ZMod m) *
              ψ ((p ^ (k - 1) : ℕ) : ZMod m)) := by
      intro ψ
      have hsplit : ((p ^ k : ℕ) : ZMod m) = ((p : ℕ) : ZMod m) * ((p ^ (k - 1) : ℕ) : ZMod m) := by
        have e : p ^ k = p * p ^ (k - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [e, Nat.cast_mul]
      have hinv : ψ⁻¹ ((p : ℕ) : ZMod m) * ψ ((p : ℕ) : ZMod m) = 1 := by
        rw [← MulChar.mul_apply, MulChar.inv_mul, MulChar.one_apply hpu]
      rw [pow_one, hsplit, map_mul, ZMod.coe_unitOfCoprime]
      linear_combination (gaussSum ψ⁻¹ ZMod.stdAddChar * ψ (a : ZMod m) *
        ψ ((p ^ (k - 1) : ℕ) : ZMod m)) * hinv
    simp_rw [hterm]
    rw [GaussInduced.sum_char_gaussSum, if_pos hpk, moebius_apply_prime_pow hp one_ne_zero,
      if_pos rfl, norm_mul, GaussInduced.norm_std, Complex.norm_natCast]
    norm_num
  · have hμ : (moebius (p ^ v) : ℂ) = 0 := by
      rw [moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
      simp
    rw [hμ, norm_zero, zero_mul]
    exact Nat.cast_nonneg _

/-- **`|c(p^k)| ≤ 1/(p−1)`** for a prime `p ∣ q` and `k ≥ 1`: `φ(q) = φ(p^v)φ(m) ≥ (p−1)φ(m)`. -/
theorem cf_pow_le (q : ℕ) [NeZero q] (p : ℕ) (hp : p.Prime) (hpq : p ∣ q) (a k : ℕ) (hk : k ≠ 0)
    (ha : Nat.Coprime a q) : ‖cf q a (p ^ k)‖ ≤ 1 / ((p : ℝ) - 1) := by
  have hq0 : q ≠ 0 := NeZero.ne q
  obtain ⟨v, hv⟩ : ∃ v, v = q.factorization p := ⟨_, rfl⟩
  have hpv : p ^ v ∣ q := by
    rw [hv]
    exact Nat.ordProj_dvd q p
  obtain ⟨m, hm⟩ : ∃ m, m = q / p ^ v := ⟨_, rfl⟩
  have hqm : q = p ^ v * m := by
    rw [hm]
    exact (Nat.mul_div_cancel' hpv).symm
  have hcop : Nat.Coprime p m := by
    rw [hm, hv]
    exact Nat.coprime_ordCompl hp hq0
  have hm0 : m ≠ 0 := fun h => hq0 (by rw [hqm, h, mul_zero])
  haveI : NeZero m := ⟨hm0⟩
  have hv1 : 1 ≤ v := by
    rw [hv]
    exact hp.factorization_pos_of_dvd hq0 hpq
  have hS := sum_pow_le hp hv1 hqm hcop a k hk ha
  have hφq : (q.totient : ℝ) = ((p ^ v).totient : ℝ) * (m.totient : ℝ) := by
    rw [← Nat.cast_mul, ← Nat.totient_mul (Nat.Coprime.pow_left v hcop), ← hqm]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hφpv : (p : ℝ) - 1 ≤ ((p ^ v).totient : ℝ) := by
    rw [Nat.totient_prime_pow hp (by omega)]
    have h1 : 1 ≤ p ^ (v - 1) := Nat.one_le_pow _ _ hp.pos
    have h2 : (p - 1 : ℕ) ≤ p ^ (v - 1) * (p - 1) := Nat.le_mul_of_pos_left _ h1
    have h3 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hp.one_le, Nat.cast_one]
    rw [← h3]
    exact_mod_cast h2
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hmpos : (0 : ℝ) < m.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hden : (0 : ℝ) < ((p ^ v).totient : ℝ) * (m.totient : ℝ) :=
    mul_pos (by linarith) hmpos
  unfold cf
  rw [norm_div, Complex.norm_natCast, hφq, div_le_div_iff₀ hden hp1]
  have k1 := mul_le_mul_of_nonneg_right hS hp1.le
  have k2 := mul_le_mul_of_nonneg_right hφpv hmpos.le
  nlinarith

/-- `∑_n [p ∣ n]Λ(n)|η(n/x)| = log p·∑_k |η(p^{k+1}/x)|` (only the powers of `p` carry `Λ`). -/
theorem tsum_pdvd (η : ℝ → ℝ) (x : ℝ) (p : ℕ) (hp : p.Prime) :
    ∑' n : ℕ, (if p ∣ n then Λ n * |η ((n : ℝ) / x)| else 0) =
      Real.log p * ∑' k : ℕ, |η ((p : ℝ) ^ (k + 1) / x)| := by
  rw [← tsum_mul_left]
  have hinj : Function.Injective (fun k : ℕ => p ^ (k + 1)) := by
    intro i j hij
    have h := Nat.pow_right_injective hp.two_le hij
    omega
  have hsupp : Function.support
      (fun n : ℕ => if p ∣ n then Λ n * |η ((n : ℝ) / x)| else 0) ⊆
        Set.range (fun k : ℕ => p ^ (k + 1)) := by
    intro n hn
    rw [Function.mem_support] at hn
    have hpn : p ∣ n := by
      by_contra h
      exact hn (if_neg h)
    have hΛ : Λ n ≠ 0 := by
      intro h
      apply hn
      rw [if_pos hpn, h, zero_mul]
    rw [vonMangoldt_ne_zero_iff, isPrimePow_nat_iff] at hΛ
    obtain ⟨r, j, hr, hj, rfl⟩ := hΛ
    have hpr : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hpn)
    refine ⟨j - 1, ?_⟩
    change p ^ (j - 1 + 1) = r ^ j
    rw [hpr, Nat.sub_add_cancel hj]
  rw [← hinj.tsum_eq hsupp]
  refine tsum_congr fun k => ?_
  rw [if_pos (dvd_pow_self p (Nat.succ_ne_zero k)), vonMangoldt_apply_pow (Nat.succ_ne_zero k),
    vonMangoldt_apply_prime hp, Nat.cast_pow]

/-- **`M + R = ∑_χ τ(χ̄)χ(a)S_{χ*}(δ/x)/φ(q)`**: the principal-character main term of `err`
cancels `M` exactly (`τ(χ₀) = μ(q)`). -/
theorem mT_add_rT (η : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0) (q : ℕ) [NeZero q] (a : ℕ)
    (ha : Nat.Coprime a q) (δ : ℝ) :
    NF.mT η x q δ + NF.rT η x q a δ = ∑ χ : DirichletCharacter ℂ q,
      gaussSum χ⁻¹ ZMod.stdAddChar * χ (a : ZMod q) * PA.twP η x δ χ / (q.totient : ℂ) := by
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  have hsplit : ∀ χ : DirichletCharacter ℂ q, (x : ℂ) / (q.totient : ℂ) *
      gaussSum χ⁻¹ ZMod.stdAddChar * MajSp.err η χ.primitiveCharacter δ x * χ (a : ZMod q) =
      gaussSum χ⁻¹ ZMod.stdAddChar * χ (a : ZMod q) * PA.twP η x δ χ / (q.totient : ℂ) -
        (x : ℂ) / (q.totient : ℂ) * gaussSum χ⁻¹ ZMod.stdAddChar * χ (a : ZMod q) *
          (if χ.conductor = 1 then MajSp.mainFT η δ else 0) := by
    intro χ
    have hinv : (x : ℂ) * (1 / (x : ℂ)) = 1 := mul_one_div_cancel hxc
    unfold MajSp.err PA.twP
    linear_combination (gaussSum χ⁻¹ ZMod.stdAddChar * χ (a : ZMod q) *
      MajSp.twSum η χ.primitiveCharacter x (δ / x) / (q.totient : ℂ)) * hinv
  rw [NF.rT_eq, Finset.sum_congr rfl fun χ _ => hsplit χ, Finset.sum_sub_distrib]
  have hsingle : ∑ χ : DirichletCharacter ℂ q, (x : ℂ) / (q.totient : ℂ) *
      gaussSum χ⁻¹ ZMod.stdAddChar * χ (a : ZMod q) *
        (if χ.conductor = 1 then MajSp.mainFT η δ else 0) =
      (x : ℂ) / (q.totient : ℂ) * (moebius q : ℂ) * MajSp.mainFT η δ := by
    rw [Finset.sum_eq_single (1 : DirichletCharacter ℂ q)]
    · rw [if_pos (conductor_one (R := ℂ) (n := q)), inv_one, GaussInduced.gaussSum_one,
        MulChar.one_apply hu]
      ring
    · intro χ _ hχ
      rw [if_neg (fun h => hχ (eq_one_iff_conductor_eq_one.mpr h)), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hsingle]
  unfold NF.mT
  push_cast
  ring

/-- **`D = S − M − R = ∑_n g_n (e(an/q) − c(n))`**, `g_n = Λ(n)η(n/x)e(nδ/x)`. -/
theorem dT_eq (η : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0) (q : ℕ) [NeZero q] (a : ℕ)
    (ha : Nat.Coprime a q) (δ : ℝ) (hs : Summable (fun n : ℕ => Λ n * |η ((n : ℝ) / x)|)) :
    NF.dT η x q a δ = ∑' n : ℕ, PA.gT η x δ n *
      (ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q)) - cf q a n) := by
  have hc : ∀ (N : ℕ) (ψ : DirichletCharacter ℂ N) (n : ℕ), ‖ψ (n : ZMod N)‖ ≤ 1 :=
    fun N ψ n => DirichletCharacter.norm_le_one ψ _
  have hsχ : ∀ χ : DirichletCharacter ℂ q, Summable fun n : ℕ =>
      gaussSum χ⁻¹ ZMod.stdAddChar * χ (a : ZMod q) / (q.totient : ℂ) *
        (PA.gT η x δ n * χ.primitiveCharacter (n : ZMod χ.conductor)) :=
    fun χ => (PA.summable_gT_mul η x δ hs _ (hc _ χ.primitiveCharacter)).mul_left _
  have hcf : ∀ n : ℕ, ∑ χ : DirichletCharacter ℂ q,
      gaussSum χ⁻¹ ZMod.stdAddChar * χ (a : ZMod q) / (q.totient : ℂ) *
        (PA.gT η x δ n * χ.primitiveCharacter (n : ZMod χ.conductor)) =
      PA.gT η x δ n * cf q a n := by
    intro n
    unfold cf
    rw [Finset.sum_div, Finset.mul_sum]
    exact Finset.sum_congr rfl fun χ _ => by ring
  have h2s : Summable fun n : ℕ => PA.gT η x δ n * cf q a n :=
    (summable_sum fun χ _ => hsχ χ).congr hcf
  have h1s : Summable fun n : ℕ =>
      PA.gT η x δ n * ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q)) :=
    PA.summable_gT_mul η x δ hs _ fun n => le_of_eq (GaussInduced.norm_std _)
  have hY : NF.mT η x q δ + NF.rT η x q a δ = ∑' n : ℕ, PA.gT η x δ n * cf q a n := by
    rw [mT_add_rT η x hx q a ha δ]
    have h1 : ∀ χ : DirichletCharacter ℂ q, gaussSum χ⁻¹ ZMod.stdAddChar * χ (a : ZMod q) *
        PA.twP η x δ χ / (q.totient : ℂ) = ∑' n : ℕ, gaussSum χ⁻¹ ZMod.stdAddChar *
          χ (a : ZMod q) / (q.totient : ℂ) *
            (PA.gT η x δ n * χ.primitiveCharacter (n : ZMod χ.conductor)) := by
      intro χ
      rw [show PA.twP η x δ χ = PA.tw η x δ χ.primitiveCharacter from rfl, PA.tw_eq,
        tsum_mul_left]
      ring
    rw [Finset.sum_congr rfl fun χ _ => h1 χ, ← Summable.tsum_finsetSum fun χ _ => hsχ χ]
    exact tsum_congr hcf
  unfold NF.dT
  rw [show NF.pt x q a δ = (a : ℝ) / q + δ / x from rfl, PA.sm_eq, sub_sub, hY,
    ← Summable.tsum_sub h1s h2s]
  exact tsum_congr fun n => by ring

/-- **The pointwise bound**: `|g_n(e(an/q) − c(n))| ≤ ∑_{p | q, p | n} (p/(p−1))Λ(n)|η(n/x)|`. -/
theorem term_le (η : ℝ → ℝ) (x δ : ℝ) (q : ℕ) [NeZero q] (a : ℕ) (ha : Nat.Coprime a q)
    (n : ℕ) :
    ‖PA.gT η x δ n * (ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q)) - cf q a n)‖ ≤
      ∑ p ∈ q.primeFactors, (if p ∣ n then (p : ℝ) / ((p : ℝ) - 1) *
        (Λ n * |η ((n : ℝ) / x)|) else 0) := by
  have hnn : 0 ≤ Λ n * |η ((n : ℝ) / x)| := mul_nonneg vonMangoldt_nonneg (abs_nonneg _)
  have hpos : ∀ p ∈ q.primeFactors, 0 ≤ (if p ∣ n then (p : ℝ) / ((p : ℝ) - 1) *
      (Λ n * |η ((n : ℝ) / x)|) else 0) := by
    intro p hp
    split_ifs
    · have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      exact mul_nonneg (div_nonneg (by linarith) (by linarith)) hnn
    · exact le_rfl
  rw [norm_mul, PA.norm_gT]
  by_cases hu : Nat.Coprime n q
  · rw [cf_unit q a n ha hu, sub_self, norm_zero, mul_zero]
    exact Finset.sum_nonneg hpos
  by_cases hΛ : Λ n = 0
  · calc _ = (0 : ℝ) := by rw [hΛ, zero_mul, zero_mul]
      _ ≤ _ := Finset.sum_nonneg hpos
  have hpp : IsPrimePow n := vonMangoldt_ne_zero_iff.mp hΛ
  obtain ⟨r, j, hr, hj, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
  have hrq : r ∣ q := by
    by_contra h
    exact hu (Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hr).mpr h))
  have hrPF : r ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hr, hrq, NeZero.ne q⟩
  have hcf := cf_pow_le q r hr hrq a j hj.ne' ha
  have hstd := GaussInduced.norm_std ((a : ZMod q) * ((r ^ j : ℕ) : ZMod q))
  have h2 : (2 : ℝ) ≤ r := by exact_mod_cast hr.two_le
  have hne : (r : ℝ) - 1 ≠ 0 := by linarith
  have hdiff : ‖ZMod.stdAddChar ((a : ZMod q) * ((r ^ j : ℕ) : ZMod q)) - cf q a (r ^ j)‖ ≤
      (r : ℝ) / ((r : ℝ) - 1) := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [hstd]
    have e : 1 + 1 / ((r : ℝ) - 1) = (r : ℝ) / ((r : ℝ) - 1) := by
      rw [one_add_div hne, sub_add_cancel]
    rw [← e]
    linarith
  have h1 := Finset.single_le_sum hpos hrPF
  rw [if_pos (dvd_pow_self r hj.ne')] at h1
  calc _ ≤ Λ (r ^ j) * |η (((r ^ j : ℕ) : ℝ) / x)| * ((r : ℝ) / ((r : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left hdiff hnn
    _ = (r : ℝ) / ((r : ℝ) - 1) * (Λ (r ^ j) * |η (((r ^ j : ℕ) : ℝ) / x)|) := by ring
    _ ≤ _ := h1

/-- `∑_n ∑_{p | q, p | n} (p/(p−1))Λ(n)|η(n/x)| = d_q`. -/
theorem hasSum_dq (η : ℝ → ℝ) (x : ℝ) (q : ℕ)
    (hs : Summable (fun n : ℕ => Λ n * |η ((n : ℝ) / x)|)) :
    HasSum (fun n : ℕ => ∑ p ∈ q.primeFactors, (if p ∣ n then (p : ℝ) / ((p : ℝ) - 1) *
      (Λ n * |η ((n : ℝ) / x)|) else 0)) (NF.dq η x q) := by
  have hnn : ∀ n : ℕ, 0 ≤ Λ n * |η ((n : ℝ) / x)| :=
    fun n => mul_nonneg vonMangoldt_nonneg (abs_nonneg _)
  have hp : ∀ p ∈ q.primeFactors, HasSum (fun n : ℕ => if p ∣ n then (p : ℝ) / ((p : ℝ) - 1) *
      (Λ n * |η ((n : ℝ) / x)|) else 0)
        ((p : ℝ) / ((p : ℝ) - 1) * Real.log p * ∑' k : ℕ, |η ((p : ℝ) ^ (k + 1) / x)|) := by
    intro p hpPF
    have hpr := Nat.prime_of_mem_primeFactors hpPF
    have hsum : Summable (fun n : ℕ => if p ∣ n then Λ n * |η ((n : ℝ) / x)| else 0) := by
      refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
      · split_ifs
        · exact hnn n
        · exact le_rfl
      · split_ifs
        · exact le_rfl
        · exact hnn n
    have h1 := hsum.hasSum.mul_left ((p : ℝ) / ((p : ℝ) - 1))
    rw [tsum_pdvd η x p hpr] at h1
    have e : ∀ n : ℕ, (if p ∣ n then (p : ℝ) / ((p : ℝ) - 1) * (Λ n * |η ((n : ℝ) / x)|)
        else 0) = (p : ℝ) / ((p : ℝ) - 1) * (if p ∣ n then Λ n * |η ((n : ℝ) / x)| else 0) :=
      fun n => by split_ifs <;> simp
    simp_rw [e]
    rw [mul_assoc]
    exact h1
  unfold NF.dq
  exact hasSum_sum hp

/-- **[DPoint] PROVED** (`eq:mouche`, 795–858, with its exact coefficient): for every weight `η`,
every `x > 0` with `∑Λ(n)|η(n/x)| < ∞`, every `q ≥ 1` and `(a, q) = 1`, `|S − M − R| ≤ d_q`. -/
theorem dPoint : NF.DPoint := by
  intro η x hx hs q a hq ha δ
  haveI : NeZero q := ⟨by omega⟩
  rw [dT_eq η x hx.ne' q a ha δ hs]
  exact tsum_of_norm_bounded (hasSum_dq η x q hs) fun n => term_le η x δ q a ha n

end DPointSec
/-! ## [Summ] at `η*` -/

section SummSec

open Set

/-- `y⁶e^{−y²/2} ≤ 48` (`u³/3! ≤ e^u` at `u = y²/2`). -/
theorem pow6_exp_le (y : ℝ) : y ^ 6 * Real.exp (-y ^ 2 / 2) ≤ 48 := by
  have hu : 0 ≤ y ^ 2 / 2 := by positivity
  have h := Real.pow_div_factorial_le_exp (y ^ 2 / 2) hu 3
  have hf : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hf] at h
  have h6 : y ^ 6 ≤ 48 * Real.exp (y ^ 2 / 2) := by
    have e : y ^ 6 = 48 * ((y ^ 2 / 2) ^ 3 / 6) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left h (by norm_num)
  have hE : Real.exp (y ^ 2 / 2) * Real.exp (-y ^ 2 / 2) = 1 := by
    rw [← Real.exp_add, show y ^ 2 / 2 + -y ^ 2 / 2 = 0 by ring, Real.exp_zero]
  have hE0 : 0 < Real.exp (-y ^ 2 / 2) := Real.exp_pos _
  calc y ^ 6 * Real.exp (-y ^ 2 / 2) ≤ 48 * Real.exp (y ^ 2 / 2) * Real.exp (-y ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right h6 hE0.le
    _ = 48 := by rw [mul_assoc, hE, mul_one]

/-- **`η*(t)·t⁴ ≤ 48/49⁴`** for `t ≥ 0` (the Hölder bound of `EN.etaStar_mul_le`, one power up:
`|η₂|₁ = 1` and `y⁶e^{−y²/2} ≤ 48`). -/
theorem etaStar_pow4_le {t : ℝ} (ht : 0 ≤ t) : HW.etaStar t * t ^ 4 ≤ 48 / 49 ^ 4 := by
  have hM : (0 : ℝ) ≤ 48 / 49 ^ 4 := by positivity
  rcases ht.eq_or_lt with h0 | hpos
  · rw [← h0]
    simpa using hM
  set s := 49 * t with hs_def
  have hs : 0 < s := by positivity
  have hst : t = s / 49 := by rw [hs_def]; ring
  have heq : HW.etaStar t * t ^ 4 =
      ∫ y in s..4 * s, HW.eta2 (s / y) * HW.phi y / y * (s / 49) ^ 4 := by
    rw [HW.etaStar, ← hs_def, HW.mconv_eta2 HW.phi hs, intervalIntegral.integral_mul_const, hst]
  rw [heq]
  have hc : ContinuousOn (fun y => HW.eta2 (s / y) * (s / y ^ 2)) (Ioi 0) :=
    (HW.eta2_div_contOn hs).mul (continuousOn_const.div (continuousOn_pow 2)
      fun y hy => pow_ne_zero 2 (mem_Ioi.mp hy).ne')
  have hc2 : ContinuousOn (fun y => HW.eta2 (s / y) * HW.phi y / y * (s / 49) ^ 4) (Ioi 0) :=
    ((((HW.eta2_div_contOn hs).mul HW.continuous_phi.continuousOn).div continuousOn_id
      fun y hy => (mem_Ioi.mp hy).ne').mul continuousOn_const)
  have hsub : uIcc s (4 * s) ⊆ Ioi 0 := HW.uIcc_pos hs (by linarith)
  have hmono : ∫ y in s..4 * s, HW.eta2 (s / y) * HW.phi y / y * (s / 49) ^ 4 ≤
      ∫ y in s..4 * s, 48 / 49 ^ 4 * (HW.eta2 (s / y) * (s / y ^ 2)) := by
    refine intervalIntegral.integral_mono_on (by linarith) ((hc2.mono hsub).intervalIntegrable)
      (((hc.mono hsub).intervalIntegrable).const_mul _) fun y hy => ?_
    have hy0 : 0 < y := lt_of_lt_of_le hs hy.1
    have hsy : s ≤ y := hy.1
    have he0 : 0 ≤ HW.eta2 (s / y) * (s / y ^ 2) :=
      mul_nonneg (HW.eta2_nonneg _) (div_nonneg hs.le (sq_nonneg y))
    have hr : HW.eta2 (s / y) * HW.phi y / y * (s / 49) ^ 4 =
        HW.eta2 (s / y) * (s / y ^ 2) * (y ^ 3 * s ^ 3 * Real.exp (-y ^ 2 / 2)) / 49 ^ 4 := by
      rw [HW.phi]
      field_simp
    have hs3 : s ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ hs.le hsy 3
    have hE0 : 0 < Real.exp (-y ^ 2 / 2) := Real.exp_pos _
    have hG : y ^ 3 * s ^ 3 * Real.exp (-y ^ 2 / 2) ≤ 48 := by
      have h1 : y ^ 3 * s ^ 3 ≤ y ^ 6 := by
        have := mul_le_mul_of_nonneg_left hs3 (pow_nonneg hy0.le 3)
        nlinarith
      have h2 := mul_le_mul_of_nonneg_right h1 hE0.le
      linarith [pow6_exp_le y]
    rw [hr]
    calc HW.eta2 (s / y) * (s / y ^ 2) * (y ^ 3 * s ^ 3 * Real.exp (-y ^ 2 / 2)) / 49 ^ 4
        ≤ HW.eta2 (s / y) * (s / y ^ 2) * 48 / 49 ^ 4 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hG he0) (by norm_num)
      _ = 48 / 49 ^ 4 * (HW.eta2 (s / y) * (s / y ^ 2)) := by ring
  rw [intervalIntegral.integral_const_mul, EN.int_eta2_sy2 hs, mul_one] at hmono
  exact hmono

/-- **[Summ] at Helfgott's `η*`**: `Λ(n)η*(n/x) ≤ n·(48/49⁴)(x/n)⁴ ≤ (48x⁴/49⁴)/n²`. -/
theorem summW_star : NF.SummW HW.etaStar := by
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg vonMangoldt_nonneg (abs_nonneg _))
    (fun n => ?_) ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left (48 / 49 ^ 4 * x ^ 4))
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have ht : 0 < (n : ℝ) / x := div_pos hnpos hx0
  have hη0 : 0 ≤ HW.etaStar ((n : ℝ) / x) := (HW.etaStar_pos ht).le
  have h4 := etaStar_pow4_le ht.le
  have hΛ : Λ n ≤ n := by
    have h1 : Λ n ≤ Real.log n := vonMangoldt_le_log
    have h2 := Real.log_le_sub_one_of_pos hnpos
    linarith
  rw [abs_of_nonneg hη0]
  have hη : HW.etaStar ((n : ℝ) / x) * (n : ℝ) ^ 4 ≤ 48 / 49 ^ 4 * x ^ 4 := by
    have e : HW.etaStar ((n : ℝ) / x) * (n : ℝ) ^ 4 =
        HW.etaStar ((n : ℝ) / x) * ((n : ℝ) / x) ^ 4 * x ^ 4 := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right h4 (by positivity)
  have key : Λ n * HW.etaStar ((n : ℝ) / x) * (n : ℝ) ^ 2 ≤ 48 / 49 ^ 4 * x ^ 4 :=
    calc Λ n * HW.etaStar ((n : ℝ) / x) * (n : ℝ) ^ 2
        ≤ (n : ℝ) * HW.etaStar ((n : ℝ) / x) * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hΛ hη0) (sq_nonneg _)
      _ = HW.etaStar ((n : ℝ) / x) * (n : ℝ) ^ 3 := by ring
      _ ≤ HW.etaStar ((n : ℝ) / x) * (n : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn1 (by norm_num)) hη0
      _ ≤ 48 / 49 ^ 4 * x ^ 4 := hη
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  rw [mul_one_div, le_div_iff₀ hn2]
  exact key

end SummSec
/-! ## The open link, typed: `ZvsL η*` from one explicit `ℓ²`-mass inequality -/

/-- **`L_{r,δ₀}(η*) ≤ 0.7903`**: `L ≤ 2S(r)|η*|₂² ≤ 2·9.68·(2/49) = 0.79020…` (`DS.lRD_le`,
`sR_le_sharp`, `EN.l2_etaStar_sq`). The half of `ZvsL η*` that is PROVED. -/
theorem lRD_star_le : DS.lRD HW.etaStar ≤ 0.7903 := by
  have hl := DS.lRD_le HW.etaStar (DP.mardiQ_of _ RW.integrable_etaStar
    (DP.sq_integrable_of_memLp _ RW.memLp_etaStar_two))
  have hsR := sR_le_sharp
  have h2 := EN.l2_etaStar_sq
  have h3 := mul_le_mul hsR h2 (sq_nonneg (MajSp.l2 HW.etaStar)) (by norm_num)
  nlinarith

/-- **`ZvsL η*` from one explicit inequality**: it suffices that
`0.7903·x ≤ ∑_n Λ(n)²η*(n/x)²` at every `x ≥ 4.9·10²⁶` (the other side is `lRD_star_le`). This is
the whole remaining obligation of `prop:nefumo` on Helfgott's weights; the truth is `≈ 1.19·x`. -/
theorem zvsL_star_of_mass (h : ∀ x : ℝ, 49 * 10 ^ 25 ≤ x →
      0.7903 * x ≤ ∑' n : ℕ, (Λ n) ^ 2 * HW.etaStar ((n : ℝ) / x) ^ 2) :
    NF.ZvsL HW.etaStar := by
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have e : MajSp.zk (fun t => HW.etaStar t ^ 2) 2 x =
      (∑' n : ℕ, (Λ n) ^ 2 * HW.etaStar ((n : ℝ) / x) ^ 2) / x := rfl
  rw [e, le_div_iff₀ hx0]
  calc DS.lRD HW.etaStar * x ≤ 0.7903 * x := mul_le_mul_of_nonneg_right lRD_star_le hx0.le
    _ ≤ _ := h x hx
/-! ## The compositions -/

/-- **[Joko] at Helfgott's weights, from [ZvsL] at `η*` alone** (`NF.jokoW_of_links` with [DPoint],
[Summ] at both weights and [ZvsL] at `η₊` supplied). -/
theorem jokoW_helf (zs : NF.ZvsL HW.etaStar) : NF.JokoW HW.etaPlus HW.etaStar :=
  NF.jokoW_of_links dPoint HW.etaPlus HW.etaStar RW.integrable_etaPlus RW.integrable_etaStar
    NF.summW_plus summW_star zvsL_plus zs

/-- **`RW.NefumoW` at Helfgott's weights from the one link that stays open**, [ZvsL] at `η*`:
[Massacre], [GatTail], [DPoint], [Summ] at `η*`, [ZvsL] at `η₊` and [T3W] are PROVED here. -/
theorem nefumoW_helf_closed (zs : NF.ZvsL HW.etaStar) :
    RW.NefumoW HW.etaPlus HW.etaStar HW.etaCirc :=
  NF.nefumoW_helf_final massacre gatTail dPoint summW_star zvsL_plus zs t3W_helf

end Principia.Common.TernaryGoldbach.NC
