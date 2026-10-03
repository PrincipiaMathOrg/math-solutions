/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.KernelLinks

set_option autoImplicit false

/-!
# `KernelLinks.TotientSqSum (10^6)` is a theorem, and the chain is down to THREE hypotheses

`KernelLinks.chain_of_totSq` carried four hypotheses, of which `ts : TotientSqSum (10^6)` was the
only one that is not research: `∑_{q ≤ 3·10⁵} μ(q)²q²/φ(q)² ≤ 10⁶` is a finite sum, and it is
true with room. `totientSqSum_holds` discharges it with no hypotheses, so `chain_no_totSq` carries
**three** — Platt's numerical GRH verification, the window approximation, and the minor-arc sup
bound.

## The route, and why it is not the kernel computation

The obvious route is to sieve `φ` and the squarefree indicator over `[1, 3·10⁵]` and sum scaled
integers in the kernel. **It was measured first and abandoned, and the measurement is the reason.**
`Nat.totient n` unfolds to `#{i ∈ range n | n.Coprime i}`, so evaluating it costs the kernel a
list of length `n`; `∑_{q ≤ N} φ(q)` by `decide +kernel` takes `+0.3 s` over the import baseline at
`N = 100`, `+10.3 s` at `N = 300`, and **does not finish inside 900 s at `N = 1000`**. That is
super-quadratic, and `N = 3·10⁵` is four orders of magnitude further out. The honest fix is a
kernel-verified linear sieve for `φ` with a random-access table, and the kernel has no random
access: a packed-bignum table costs `O(size)` per read, so `3·10⁵` reads of a `3·10⁵`-field table
is `10¹¹` bytes of copying. `KernelCert/Sieve.lean` is fast precisely because every operation is on
the *whole* bitset at once, and a `φ` table is not that shape.

So this file proves the bound analytically, and every product in it is a product over 25 primes
that `norm_num` evaluates exactly. No sieve, no `decide +kernel`, no certificate.

## The route in one line

For every `q ≠ 0`, Euler's product gives `(q/φ(q))² = ∏_{p ∣ q} (p/(p−1))² = ∏_{p ∣ q} (1 + gw p)`
(`sq_ratio` — this needs no squarefreeness). Split the prime divisors at `100`:

* the **rough** factors are at most two (`card_rough`: three distinct primes `> 100` would force
  `q ≥ 101³ = 1030301 > 3·10⁵`) and each is `≤ (101/100)²`, so together `≤ (101/100)⁴`
  (`rough_le`);
* the **smooth** factors expand over subsets of `sps` (`Finset.prod_add`), which turns the sum over
  `q` into a sum over `U ⊆ sps` of `(∏_U gw) · #{q ≤ 3·10⁵ : q squarefree, U ⊆ q.primeFactors}`;
* that count is bounded through `4 ∤ q` alone (`cnt_bnd`): writing `q = (∏_U p)·n`, squarefreeness
  forbids `2 ∣ n` when `∏_U p` is even and `4 ∣ n` when it is odd, so the count is
  `≤ (1/2)·3·10⁵/∏_U p + 1` or `≤ (3/4)·3·10⁵/∏_U p + 1`.

**`ww 2 = 1` is where the two densities become one constant.** `(1/2)·(gw 2 / 2) = 3/4 = 3/4`, so
replacing `gw 2 / 2` by `1` makes the even case and the odd case charge the same `3/4`
(`prod_ww_even`, `prod_ww_odd`), and the whole subset sum collapses to one product
(`sum_pow_prod`).

## Squarefreeness is the whole margin, and the file uses exactly one bit of it

`∑_{q ≤ 3·10⁵} q²/φ(q)² = 1329254.41` **exceeds** `10⁶` (`totsq1.py`, exact integer bracket at
scale `10⁹`: `[1329254.4049, 1329254.4052]`), while the squarefree sum is `583116.31`
(bracket `[583116.30619, 583116.30637]`) — a ratio of `2.2796`. So any route that drops `μ(q)²`
fails, including the divisor-identity route recommended in `FareyKernel.LocalTermWeightSum`'s
docstring, which bounds `∑_{q ≤ P} q²/φ(q)² ≤ 4.4311·P = 1.3293·10⁶` — that is the *all-`q`* sum,
to three figures (`4.4311 · 3·10⁵ = 1329330` against the measured `1329254`), and it is the wrong
sum. **This file does not use full squarefreeness either**: it uses only `4 ∤ q`, which is the
single cheapest bit of it and already enough.

## The numbers, every one recomputed in this session

`totsq1.py` (linear sieve for `φ` and the squarefree flag, integer bracket at scale `10⁹`) and
`totsq3.py` (the five constants below as exact `Fraction`s) — nothing carried from a previous round.

| quantity | value |
|---|---|
| `∑_{q ≤ 3·10⁵} μ(q)²q²/φ(q)²` (true) | `583116.3062`, so `10⁶` holds with `1.7149×` |
| `∑_{q ≤ 3·10⁵} q²/φ(q)²` (true) | `1329254.405` — **above** `10⁶` |
| `W = ∏_{p ∈ sps} (1 + ww p)` | `3.531884115`, charged as `3533/1000` |
| `G = ∏_{p ∈ sps} (1 + gw p)` | `69.078661`, charged as `70` |
| `R = (101/100)⁴` | `104060401/100000000` |
| the bound with exact `W`, `G` | `827012.76` |
| **the bound Lean checks** | `16545499698599/20000000 = 827274.98` |

So the theorem passes with `1.2088×` of margin, and the bound is `1.4187×` the true value — the
loss is the rough factor `R` and the `3/4` density, both deliberate.

## What this does NOT do

It proves nothing about ternary Goldbach. `chain_no_totSq` still carries `grh` (Platt's finite
verification, `1.59·10⁷×` beyond anything kernel-certified here), `wa` (`WindowApproxUnder`, the
analytic heart, truth unknown) and `mn` (the minor-arc sup bound, needing Helfgott's log-free
Type I/II analysis). Removing `ts` removes the only slot that was ever going to be removed by
arithmetic.
-/

namespace Principia.Common.TernaryGoldbach.TotientSq

open Finset

/-- The 25 primes below `101`. -/
def sps : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97}

/-- `gw p = (p/(p-1))^2 - 1`, the per-prime excess of the weight. -/
noncomputable def gw (p : ℕ) : ℝ := (2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2

/-- `ww p = gw p / p`, except `ww 2 = 1`. -/
noncomputable def ww (p : ℕ) : ℝ := if p = 2 then 1 else gw p / (p : ℝ)

set_option maxRecDepth 8000 in
/-- Every prime below `101` is listed in `sps`. -/
theorem mem_sps {p : ℕ} (hp : p.Prime) (h : p < 101) : p ∈ sps := by
  have hall : ∀ r ∈ Finset.range 101, Nat.Prime r → r ∈ sps := by decide
  exact hall p (Finset.mem_range.mpr h) hp

/-- Every member of `sps` is at least `2`. -/
theorem two_le_sps {p : ℕ} (hp : p ∈ sps) : 2 ≤ p := by
  have hall : ∀ r ∈ sps, 2 ≤ r := by decide
  exact hall p hp

theorem gw_nonneg {p : ℕ} (hp : 2 ≤ p) : 0 ≤ gw p := by
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  exact div_nonneg (by linarith) (sq_nonneg _)

theorem one_add_gw {p : ℕ} (hp : 2 ≤ p) : 1 + gw p = ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h1 : ((p : ℝ) - 1) ≠ 0 := by intro h; nlinarith
  unfold gw
  field_simp
  ring

/-- Euler's product formula, squared: the weight of `q` is a product over its prime divisors,
for every `q ≠ 0` — squarefree or not. -/
theorem sq_ratio (q : ℕ) (hq : q ≠ 0) :
    (q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 = ∏ p ∈ q.primeFactors, (1 + gw p) := by
  have h2 : ∀ p ∈ q.primeFactors, 2 ≤ p := fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).two_le
  have hpos : ∀ p ∈ q.primeFactors, (0 : ℝ) < (p : ℝ) - 1 := by
    intro p hp
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h2 p hp
    linarith
  have hd : (0 : ℝ) < ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := Finset.prod_pos hpos
  have hφ : (0 : ℝ) < (Nat.totient q : ℝ) := by
    have := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)
    exact_mod_cast this
  have key : (Nat.totient q : ℝ) * ∏ p ∈ q.primeFactors, (p : ℝ)
      = (q : ℝ) * ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    have hn := congrArg (fun n : ℕ => (n : ℝ)) (Nat.totient_mul_prod_primeFactors q)
    push_cast at hn
    rw [hn]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    have h1 : 1 ≤ p := le_trans (by norm_num) (h2 p hp)
    push_cast [h1]
    ring
  have hstep : ∏ p ∈ q.primeFactors, (1 + gw p)
      = (∏ p ∈ q.primeFactors, ((p : ℝ) / ((p : ℝ) - 1))) ^ 2 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun p hp => one_add_gw (h2 p hp)
  have hratio : (∏ p ∈ q.primeFactors, (p : ℝ)) / (∏ p ∈ q.primeFactors, ((p : ℝ) - 1))
      = (q : ℝ) / (Nat.totient q : ℝ) := by
    rw [div_eq_div_iff hd.ne' hφ.ne']
    linarith [key]
  rw [hstep, Finset.prod_div_distrib, hratio, div_pow]

/-! ## The divisor expansion -/

/-- `Finset.prod_add`, in the shape used twice below. -/
theorem sum_pow_prod (s : Finset ℕ) (f : ℕ → ℝ) :
    ∑ U ∈ s.powerset, ∏ p ∈ U, f p = ∏ p ∈ s, (1 + f p) := by
  have h := Finset.prod_add f (fun _ => (1 : ℝ)) s
  simp only [Finset.prod_const_one, mul_one] at h
  rw [← h]
  exact Finset.prod_congr rfl fun p _ => add_comm (f p) 1

/-- The indicator sum over `s.powerset` collapses to a product over `s ∩ t`. -/
theorem sum_ind_eq (s t : Finset ℕ) :
    ∑ U ∈ s.powerset, (if U ⊆ t then ∏ p ∈ U, gw p else 0) = ∏ p ∈ s ∩ t, (1 + gw p) := by
  classical
  rw [← Finset.sum_filter]
  have hset : {U ∈ s.powerset | U ⊆ t} = (s ∩ t).powerset := by
    ext U
    simp [Finset.mem_powerset, Finset.subset_inter_iff]
  rw [hset, sum_pow_prod]

/-! ## The rough part: at most two prime factors above 100, each contributing `< (101/100)^2` -/

theorem le_101 {q p : ℕ} (hp : p ∈ q.primeFactors) (hns : p ∉ sps) : 101 ≤ p := by
  by_contra h
  exact hns (mem_sps (Nat.prime_of_mem_primeFactors hp) (by omega))

/-- A `q ≤ 300000` has at most two prime factors above `100`: three would force
`q ≥ 101^3 = 1030301`. -/
theorem card_rough (q : ℕ) (h0 : q ≠ 0) (hle : q ≤ 300000) :
    #(q.primeFactors \ sps) ≤ 2 := by
  classical
  by_contra h
  obtain ⟨T, hT, hcard⟩ :=
    Finset.exists_subset_card_eq (s := q.primeFactors \ sps) (n := 3) (by omega)
  have hsub : T ⊆ q.primeFactors := fun p hp => (Finset.mem_sdiff.mp (hT hp)).1
  have hdvd : ∏ p ∈ T, p ∣ q :=
    dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ hsub) (Nat.prod_primeFactors_dvd q)
  have hge : ∏ _p ∈ T, 101 ≤ ∏ p ∈ T, p := by
    refine Finset.prod_le_prod' fun p hp => ?_
    exact le_101 (Finset.mem_sdiff.mp (hT hp)).1 (Finset.mem_sdiff.mp (hT hp)).2
  rw [Finset.prod_const, hcard] at hge
  have hq := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd
  norm_num at hge
  omega

theorem rough_le (q : ℕ) (h0 : q ≠ 0) (hle : q ≤ 300000) :
    ∏ p ∈ q.primeFactors \ sps, (1 + gw p) ≤ (101 / 100 : ℝ) ^ 4 := by
  classical
  have h2 : ∀ p ∈ q.primeFactors \ sps, 2 ≤ p := fun p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1).two_le
  have hfac : ∀ p ∈ q.primeFactors \ sps, 1 + gw p ≤ (101 / 100 : ℝ) ^ 2 := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_sdiff.mp hp
    have h101 : (101 : ℝ) ≤ (p : ℝ) := by exact_mod_cast le_101 hp1 hp2
    have hd : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hmono : (p : ℝ) / ((p : ℝ) - 1) ≤ 101 / 100 := by
      rw [div_le_iff₀ hd]
      linarith
    have hx : (0 : ℝ) ≤ (p : ℝ) / ((p : ℝ) - 1) := div_nonneg (by linarith) (by linarith)
    rw [one_add_gw (h2 p hp)]
    nlinarith [hmono, hx]
  have hnn : ∀ p ∈ q.primeFactors \ sps, (0 : ℝ) ≤ 1 + gw p := by
    intro p hp
    have := gw_nonneg (h2 p hp)
    linarith
  calc ∏ p ∈ q.primeFactors \ sps, (1 + gw p)
      ≤ ∏ _p ∈ q.primeFactors \ sps, (101 / 100 : ℝ) ^ 2 := Finset.prod_le_prod hnn hfac
    _ = ((101 / 100 : ℝ) ^ 2) ^ #(q.primeFactors \ sps) := Finset.prod_const _
    _ ≤ ((101 / 100 : ℝ) ^ 2) ^ 2 := pow_le_pow_right₀ (by norm_num) (card_rough q h0 hle)
    _ = (101 / 100 : ℝ) ^ 4 := by ring

/-! ## The per-term bound -/

theorem term_le (q : ℕ) (h1 : 1 ≤ q) (hle : q ≤ 300000) :
    (ArithmeticFunction.moebius q : ℝ) ^ 2 * (q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2
      ≤ (101 / 100 : ℝ) ^ 4 * ∑ U ∈ sps.powerset,
          (if Squarefree q ∧ U ⊆ q.primeFactors then ∏ p ∈ U, gw p else 0) := by
  classical
  by_cases hsf : Squarefree q
  · have hmu : (ArithmeticFunction.moebius q : ℝ) ^ 2 = 1 := by
      have h := congrArg (fun z : ℤ => (z : ℝ))
        (ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf)
      push_cast at h
      exact h
    have hif : ∀ U : Finset ℕ,
        (if Squarefree q ∧ U ⊆ q.primeFactors then ∏ p ∈ U, gw p else 0)
          = (if U ⊆ q.primeFactors then ∏ p ∈ U, gw p else 0) := by
      intro U
      by_cases h : U ⊆ q.primeFactors <;> simp [h, hsf]
    rw [hmu, one_mul, sq_ratio q (by omega), Finset.sum_congr rfl (fun U _ => hif U), sum_ind_eq]
    have hnn : (0 : ℝ) ≤ ∏ p ∈ q.primeFactors ∩ sps, (1 + gw p) := by
      refine Finset.prod_nonneg fun p hp => ?_
      have := gw_nonneg
        ((Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hp).1).two_le)
      linarith
    calc ∏ p ∈ q.primeFactors, (1 + gw p)
        = (∏ p ∈ q.primeFactors ∩ sps, (1 + gw p))
            * ∏ p ∈ q.primeFactors \ sps, (1 + gw p) :=
          (Finset.prod_inter_mul_prod_sdiff q.primeFactors sps (fun p => 1 + gw p)).symm
      _ ≤ (∏ p ∈ q.primeFactors ∩ sps, (1 + gw p)) * (101 / 100 : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_left (rough_le q (by omega) hle) hnn
      _ = (101 / 100 : ℝ) ^ 4 * ∏ p ∈ sps ∩ q.primeFactors, (1 + gw p) := by
          rw [Finset.inter_comm]; ring
  · have hmu : ArithmeticFunction.moebius q = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf
    have hz : ∑ U ∈ sps.powerset,
        (if Squarefree q ∧ U ⊆ q.primeFactors then ∏ p ∈ U, gw p else 0) = 0 :=
      Finset.sum_eq_zero fun U _ => by simp [hsf]
    rw [hmu, hz]
    norm_num

/-! ## The count: the squarefree multiples of `∏ U` below `300000` -/

theorem prod_dvd_sub {q : ℕ} {U : Finset ℕ} (h : U ⊆ q.primeFactors) : ∏ p ∈ U, p ∣ q :=
  dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ h) (Nat.prod_primeFactors_dvd q)

theorem not_four_dvd {x : ℕ} (h : Squarefree x) : ¬ (4 ∣ x) := by
  intro h4
  have h22 : (2 : ℕ) * 2 ∣ x := by omega
  exact Nat.prime_two.one_lt.ne' (Nat.isUnit_iff.mp (h 2 h22))

theorem card_not_dvd (Z k : ℕ) : #({n ∈ Finset.Ioc 0 Z | ¬ k ∣ n}) = Z - Z / k := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := Finset.Ioc 0 Z) (fun n => k ∣ n)
  rw [Nat.Ioc_filter_dvd_card_eq_div, Nat.card_Ioc] at h
  omega

theorem cnt_bnd (U : Finset ℕ) (k : ℕ) (hm : 0 < ∏ p ∈ U, p)
    (hprop : ∀ n : ℕ, Squarefree ((∏ p ∈ U, p) * n) → ¬ k ∣ n) :
    #({q ∈ Finset.Icc 1 300000 | Squarefree q ∧ U ⊆ q.primeFactors})
      ≤ (300000 / ∏ p ∈ U, p) - (300000 / ∏ p ∈ U, p) / k := by
  classical
  rw [← card_not_dvd]
  refine Finset.card_le_card_of_injOn (fun q => q / ∏ p ∈ U, p) ?_ ?_
  · intro q hq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at hq
    obtain ⟨⟨hq1, hq2⟩, hsf, hsub⟩ := hq
    have heq : (∏ p ∈ U, p) * (q / ∏ p ∈ U, p) = q := Nat.mul_div_cancel' (prod_dvd_sub hsub)
    have hn0 : 0 < q / ∏ p ∈ U, p := by
      rcases Nat.eq_zero_or_pos (q / ∏ p ∈ U, p) with h | h
      · rw [h, Nat.mul_zero] at heq; omega
      · exact h
    have hnle : q / ∏ p ∈ U, p ≤ 300000 / ∏ p ∈ U, p := by
      refine (Nat.le_div_iff_mul_le hm).mpr ?_
      calc (q / ∏ p ∈ U, p) * (∏ p ∈ U, p) = q := by rw [Nat.mul_comm]; exact heq
        _ ≤ 300000 := hq2
    have hnk : ¬ k ∣ (q / ∏ p ∈ U, p) := hprop _ (by rw [heq]; exact hsf)
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ioc]
    exact ⟨⟨hn0, hnle⟩, hnk⟩
  · intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at ha hb
    have hda : (∏ p ∈ U, p) ∣ a := prod_dvd_sub ha.2.2
    have hdb : (∏ p ∈ U, p) ∣ b := prod_dvd_sub hb.2.2
    have hab' : a / ∏ p ∈ U, p = b / ∏ p ∈ U, p := hab
    rw [← Nat.mul_div_cancel' hda, ← Nat.mul_div_cancel' hdb, hab']

/-! ## The two product identities — and where `ww 2 = 1` earns its keep

`ww 2 = 1` is not a convention: it is exactly the factor that turns the *two* densities
(`1/2` for an even `∏ U`, `3/4` for an odd one) into the *single* constant `3/4`, because
`(1/2)·(gw 2/2) = 3/4` too. -/

theorem prod_ww_odd {U : Finset ℕ} (h2 : 2 ∉ U) :
    (∏ p ∈ U, gw p) / (∏ p ∈ U, (p : ℝ)) = ∏ p ∈ U, ww p := by
  rw [← Finset.prod_div_distrib]
  refine (Finset.prod_congr rfl fun p hp => ?_).symm
  have hne : p ≠ 2 := fun h => h2 (h ▸ hp)
  simp [ww, hne]

theorem prod_ww_even {U : Finset ℕ} (hU : U ⊆ sps) (h2 : 2 ∈ U) :
    (∏ p ∈ U, gw p) / (∏ p ∈ U, (p : ℝ)) = 3 / 2 * ∏ p ∈ U, ww p := by
  classical
  have hgw2 : gw 2 = 3 := by norm_num [gw]
  have hg : ∏ p ∈ U, gw p = 3 * ∏ p ∈ U.erase 2, gw p := by
    rw [← Finset.mul_prod_erase U gw h2, hgw2]
  have hp2 : ∏ p ∈ U, (p : ℝ) = 2 * ∏ p ∈ U.erase 2, (p : ℝ) := by
    rw [← Finset.mul_prod_erase U (fun p => (p : ℝ)) h2]
    norm_num
  have hw : ∏ p ∈ U, ww p = ∏ p ∈ U.erase 2, (gw p / (p : ℝ)) := by
    rw [← Finset.mul_prod_erase U ww h2, show ww 2 = 1 from by simp [ww], one_mul]
    exact Finset.prod_congr rfl fun p hp => by simp [ww, (Finset.mem_erase.mp hp).1]
  have hden : (0 : ℝ) < ∏ p ∈ U.erase 2, (p : ℝ) := by
    refine Finset.prod_pos fun p hp => ?_
    have h := two_le_sps (hU (Finset.mem_of_mem_erase hp))
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h
    linarith
  rw [hg, hp2, hw, Finset.prod_div_distrib]
  field_simp

/-! ## The per-subset bound -/

theorem cnt_le (U : Finset ℕ) (hU : U ⊆ sps) :
    (∏ p ∈ U, gw p)
        * (#({q ∈ Finset.Icc 1 300000 | Squarefree q ∧ U ⊆ q.primeFactors}) : ℝ)
      ≤ 3 / 4 * 300000 * (∏ p ∈ U, ww p) + ∏ p ∈ U, gw p := by
  classical
  have hmN : 0 < ∏ p ∈ U, p := by
    refine Finset.prod_pos fun p hp => ?_
    have := two_le_sps (hU hp)
    omega
  have hcast : ((∏ p ∈ U, p : ℕ) : ℝ) = ∏ p ∈ U, (p : ℝ) := by push_cast; ring
  have hmR : (0 : ℝ) < ∏ p ∈ U, (p : ℝ) := by
    rw [← hcast]
    exact_mod_cast hmN
  have hgwnn : (0 : ℝ) ≤ ∏ p ∈ U, gw p :=
    Finset.prod_nonneg fun p hp => gw_nonneg (two_le_sps (hU hp))
  set Z : ℕ := 300000 / ∏ p ∈ U, p with hZdef
  have hZR : (Z : ℝ) ≤ 300000 / ∏ p ∈ U, (p : ℝ) := by
    rw [le_div_iff₀ hmR, ← hcast, ← Nat.cast_mul]
    exact_mod_cast Nat.div_mul_le_self 300000 (∏ p ∈ U, p)
  by_cases h2 : 2 ∈ U
  · have hcard : #({q ∈ Finset.Icc 1 300000 | Squarefree q ∧ U ⊆ q.primeFactors})
        ≤ Z - Z / 2 := by
      refine cnt_bnd U 2 hmN fun n hn h2n => not_four_dvd hn ?_
      obtain ⟨a, ha⟩ := Finset.dvd_prod_of_mem (fun p => p) h2
      obtain ⟨b, hb⟩ := h2n
      exact ⟨a * b, by rw [ha, hb]; ring⟩
    have hom : 2 * (Z - Z / 2) ≤ Z + 1 := by
      have h : ∀ W : ℕ, 2 * (W - W / 2) ≤ W + 1 := fun W => by omega
      exact h Z
    have hcR : (#({q ∈ Finset.Icc 1 300000 | Squarefree q ∧ U ⊆ q.primeFactors}) : ℝ)
        ≤ ((Z : ℝ) + 1) / 2 := by
      have h1 : (#({q ∈ Finset.Icc 1 300000 | Squarefree q ∧ U ⊆ q.primeFactors}) : ℝ)
          ≤ ((Z - Z / 2 : ℕ) : ℝ) := by exact_mod_cast hcard
      have h2' : ((2 * (Z - Z / 2) : ℕ) : ℝ) ≤ ((Z + 1 : ℕ) : ℝ) := by exact_mod_cast hom
      push_cast at h2'
      linarith
    have hkey : (∏ p ∈ U, gw p) * (Z : ℝ) ≤ 300000 * (3 / 2 * ∏ p ∈ U, ww p) :=
      calc (∏ p ∈ U, gw p) * (Z : ℝ)
          ≤ (∏ p ∈ U, gw p) * (300000 / ∏ p ∈ U, (p : ℝ)) :=
            mul_le_mul_of_nonneg_left hZR hgwnn
        _ = 300000 * ((∏ p ∈ U, gw p) / ∏ p ∈ U, (p : ℝ)) := by ring
        _ = 300000 * (3 / 2 * ∏ p ∈ U, ww p) := by rw [prod_ww_even hU h2]
    have hstep := mul_le_mul_of_nonneg_left hcR hgwnn
    nlinarith [hgwnn, hkey, hstep]
  · have hcard : #({q ∈ Finset.Icc 1 300000 | Squarefree q ∧ U ⊆ q.primeFactors})
        ≤ Z - Z / 4 :=
      cnt_bnd U 4 hmN fun n hn h4n => not_four_dvd hn (h4n.mul_left _)
    have hom : 4 * (Z - Z / 4) ≤ 3 * Z + 3 := by
      have h : ∀ W : ℕ, 4 * (W - W / 4) ≤ 3 * W + 3 := fun W => by omega
      exact h Z
    have hcR : (#({q ∈ Finset.Icc 1 300000 | Squarefree q ∧ U ⊆ q.primeFactors}) : ℝ)
        ≤ (3 * (Z : ℝ) + 3) / 4 := by
      have h1 : (#({q ∈ Finset.Icc 1 300000 | Squarefree q ∧ U ⊆ q.primeFactors}) : ℝ)
          ≤ ((Z - Z / 4 : ℕ) : ℝ) := by exact_mod_cast hcard
      have h2' : ((4 * (Z - Z / 4) : ℕ) : ℝ) ≤ ((3 * Z + 3 : ℕ) : ℝ) := by exact_mod_cast hom
      push_cast at h2'
      linarith
    have hkey : (∏ p ∈ U, gw p) * (Z : ℝ) ≤ 300000 * (∏ p ∈ U, ww p) :=
      calc (∏ p ∈ U, gw p) * (Z : ℝ)
          ≤ (∏ p ∈ U, gw p) * (300000 / ∏ p ∈ U, (p : ℝ)) :=
            mul_le_mul_of_nonneg_left hZR hgwnn
        _ = 300000 * ((∏ p ∈ U, gw p) / ∏ p ∈ U, (p : ℝ)) := by ring
        _ = 300000 * (∏ p ∈ U, ww p) := by rw [prod_ww_odd h2]
    have hstep := mul_le_mul_of_nonneg_left hcR hgwnn
    nlinarith [hgwnn, hkey, hstep]

/-! ## The two numerical products, over the 25 primes of `sps` -/

theorem prod_ww_le : ∏ p ∈ sps, (1 + ww p) ≤ 3533 / 1000 := by
  norm_num [sps, gw, ww, Finset.prod_insert]

theorem prod_gw_le : ∏ p ∈ sps, (1 + gw p) ≤ 70 := by
  norm_num [sps, gw, Finset.prod_insert]

/-! ## Assembly -/

theorem sum_le_bnd :
    ∑ q ∈ Finset.Icc 1 300000,
        (ArithmeticFunction.moebius q : ℝ) ^ 2 * (q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2
      ≤ (101 / 100 : ℝ) ^ 4
          * (3 / 4 * 300000 * (∏ p ∈ sps, (1 + ww p)) + ∏ p ∈ sps, (1 + gw p)) := by
  classical
  calc ∑ q ∈ Finset.Icc 1 300000,
        (ArithmeticFunction.moebius q : ℝ) ^ 2 * (q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2
      ≤ ∑ q ∈ Finset.Icc 1 300000, ((101 / 100 : ℝ) ^ 4 * ∑ U ∈ sps.powerset,
          (if Squarefree q ∧ U ⊆ q.primeFactors then ∏ p ∈ U, gw p else 0)) :=
        Finset.sum_le_sum fun q hq =>
          term_le q (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2
    _ = (101 / 100 : ℝ) ^ 4 * ∑ U ∈ sps.powerset, ∑ q ∈ Finset.Icc 1 300000,
          (if Squarefree q ∧ U ⊆ q.primeFactors then ∏ p ∈ U, gw p else 0) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ = (101 / 100 : ℝ) ^ 4 * ∑ U ∈ sps.powerset, (∏ p ∈ U, gw p)
          * (#({q ∈ Finset.Icc 1 300000 | Squarefree q ∧ U ⊆ q.primeFactors}) : ℝ) := by
        refine congrArg _ (Finset.sum_congr rfl fun U _ => ?_)
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ (101 / 100 : ℝ) ^ 4 * ∑ U ∈ sps.powerset,
          (3 / 4 * 300000 * (∏ p ∈ U, ww p) + ∏ p ∈ U, gw p) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun U hU => ?_) (by norm_num)
        exact cnt_le U (Finset.mem_powerset.mp hU)
    _ = (101 / 100 : ℝ) ^ 4
          * (3 / 4 * 300000 * (∏ p ∈ sps, (1 + ww p)) + ∏ p ∈ sps, (1 + gw p)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_pow_prod, sum_pow_prod]

/-- **The deliverable.** `∑_{q ≤ 3·10⁵} μ(q)²q²/φ(q)² ≤ 10⁶`, with no hypotheses. -/
theorem totientSqSum_holds : KernelLinks.TotientSqSum (10 ^ 6) := by
  have hb := sum_le_bnd
  have hw := prod_ww_le
  have hg := prod_gw_le
  have hgnn : (0 : ℝ) ≤ ∏ p ∈ sps, (1 + ww p) :=
    Finset.prod_nonneg fun p hp => by
      have := gw_nonneg (two_le_sps hp)
      unfold ww
      split_ifs <;> [norm_num; positivity]
  show ∑ q ∈ Finset.Icc 1 300000,
      (ArithmeticFunction.moebius q : ℝ) ^ 2 * (q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2
      ≤ (10 : ℝ) ^ 6
  calc ∑ q ∈ Finset.Icc 1 300000,
        (ArithmeticFunction.moebius q : ℝ) ^ 2 * (q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2
      ≤ (101 / 100 : ℝ) ^ 4
          * (3 / 4 * 300000 * (∏ p ∈ sps, (1 + ww p)) + ∏ p ∈ sps, (1 + gw p)) := hb
    _ ≤ (101 / 100 : ℝ) ^ 4 * (3 / 4 * 300000 * (3533 / 1000) + 70) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        linarith
    _ ≤ (10 : ℝ) ^ 6 := by norm_num

/-- `MajorPlatt.KernelTailBound (1/10⁵)` with NO hypotheses. -/
theorem kernelTail_holds : MajorPlatt.KernelTailBound (1 / 10 ^ 5) :=
  KernelLinks.kernelTailBound_holds totientSqSum_holds

/-- **The chain, at THREE hypotheses**: Platt's numerical GRH verification, the window
approximation and the minor-arc sup bound. K3's arithmetic sum is gone. -/
theorem chain_no_totSq (grh : Spine.PlattGRH)
    (wa : MajorPlatt.WindowApproxUnder 1000 (1 / 2) (fun q => 10 ^ 8 / (q : ℝ)))
    (mn : Spine.MinorSupBound MajorPlatt.Pcut MajorPlatt.Qcut (3 / 10)) :
    Principia.Erdos1054.Cite_Helfgott_weighted :=
  KernelLinks.chain_of_totSq grh wa mn totientSqSum_holds

end Principia.Common.TernaryGoldbach.TotientSq
