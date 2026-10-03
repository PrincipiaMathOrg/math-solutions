/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.Spine

set_option autoImplicit false

/-!
# Link 7 of the ternary-Goldbach spine, DISCHARGED: prime-power and parity removal

`Spine.lean` reduces the EP1054 trusted input `Cite_Helfgott_weighted` to four open links. This
file **proves one of them outright**:

  `Spine.PrimePowerRemoval cPP : ∀ odd H ≥ 10^27,
      lambdaTriple H − cPP·H^{3/2}(log H)² ≤ ternaryLogCount H`

`primePowerRemoval_ten : Spine.PrimePowerRemoval 10` is the instance
`Spine.ternaryLogCountLower_of_links_main` and `..._sharp` consume, so both of those now take
**three** hypotheses instead of four (`ternaryLogCountLower_of_three_links`,
`cite_Helfgott_weighted_of_three_links` below).

## What the difference actually is

`lambdaTriple H` sums `Λ(n₁)Λ(n₂)Λ(n₃)` over every ordered triple with `n₁+n₂+n₃ = H`;
`ternaryLogCount H` keeps only the triples whose three coordinates are **odd primes**. Reading both
definitions: neither imposes distinctness, and both range over the same `Finset.range H` twice with
the same natural subtraction in the third coordinate, so distinctness and the index set contribute
nothing to the difference. `Λ` vanishes off the prime powers, so a surviving summand of
`lambdaTriple` that `ternaryLogCount` drops has some coordinate which is a prime power but not an
odd prime — that is, a **proper prime power** `p^k` (`k ≥ 2`) or the value **2**. Nothing else can
happen, and in particular the parity bookkeeping is not a separate case: `2` is exactly the one
prime the `Odd` guard removes.

## The counting, and why the naive version does not fit

The brief's first shape — "`≤ √H log H` choices of a bad coordinate, `≤ H` for a second,
`(log H)³` per term" — gives `H^{3/2}(log H)⁴`, which overshoots the allowed `H^{3/2}(log H)²` by
`(log H)²`. The fix is the standard one and is the whole arithmetic content here: **sum `Λ` over a
coordinate instead of counting it**. Writing `badLambda n = Λ n` off the odd primes and `0` on
them,

  `lambdaTriple H − ternaryLogCount H ≤ 3·(log H)·(∑_{n<H} Λ n)·(∑_{n<H} badLambda n)`,

because each dropped summand is captured by the term that carries `badLambda` in its offending
coordinate (`term_le`), and one `Λ` in each of the three sums is spent on the trivial `Λ ≤ log H`.
Then Mathlib's Chebyshev bounds supply the two sums:

* `Chebyshev.psi_le`         : `∑_{n<H} Λ n ≤ ψ(H) ≤ log 4·H + 2√H log H ≤ 1.3865·H`;
* `Chebyshev.psi_sub_theta_le`: `∑_{n<H} badLambda n ≤ (ψ−θ)(H) + log 2 ≤ 2√H log H + 0.694`.

So the difference is at most `3·L·(1.3865 H)·(2√H L + 0.694) = 8.319·H^{3/2}L² + 2.887·H·L`, and
`H ≥ 10^27` makes the second term negligible against any slack in the first. `8.319 = 3·log 4·2` is
what THIS ASSEMBLY gives from the inputs it uses — three coordinates, `2√H log H` from Mathlib's
`ψ−θ`, and `log 4` from Chebyshev's `ψ` bound — and `primePowerRemoval_of` is stated at
`8.32 ≤ cPP`, the round number just above it.

**IT IS NOT A FLOOR, and an earlier version of this docstring wrongly said so** (corrected by the
round-2 auditor, 2026-09-29). The lossy input is not `psi_le` (worth only `log 4 = 1.386 → 1`) but
Mathlib's `psi_sub_theta_le : |ψ x − θ x| ≤ 2√x·log x`, whose `log x` is a full factor
`≈ 62` of pure slack at the threshold: the true order of `ψ − θ` is `√x` with **no** log, and
`(ψ(x)−θ(x))/√x` measures 1.279, 1.174, 1.158, 1.102, 1.063, 1.051 at `x = 10³…10⁸`.
Rosser–Schoenfeld 1962 (Thms 12 & 13; recorded at `HELFGOTT-PROOF-MAP.md:231`, and what
Helfgott himself uses) gives
`∑_{n ≤ N, n not prime} Λ(n) < 1.4262 √N`. Since `lambdaTriple_sub_le` below is shape-agnostic,
feeding that in instead yields `3·1.3865·1.4262 = 5.9323·H^{3/2}L + 2.8867·H·L`, so the required
constant at `H = 10^27` is `0.09542` and DECREASING in `H` — i.e. `PrimePowerRemoval 0.1` is
reachable, `87×` below `8.32`.

**We deliberately did not pursue it, and the reason is measured rather than assumed.** `cPP` enters
the spine's budget only as `cPP/10⁴`, so dropping `10 → 0.1` relaxes the admissible minor-arc
constant `κ` from `0.46339` to `0.46409` — **0.15 %**, against a minor-arc shortfall of `9.13×`. The
prime-power term is simply not where this route is tight, so porting Rosser–Schoenfeld buys nothing
the campaign needs.

`cPP = 8.32`, `9` and `10` all clear the spine's budget `c₀ + κ·cL2 + cPP/10⁴ ≤ cMaj` at both
instantiations (`0.42126 ≤ 0.5` and `0.64526 ≤ 0.65` at `cPP = 10`; smaller `cPP` only helps), so
nothing downstream has to change.

## The adversarial pass

`PrimePowerRemoval` is a `def … : Prop` about `lambdaTriple` and `ternaryLogCount`, both concretely
defined — there is no function, witness or measure to instantiate degenerately, so round 1's
"satisfy it with a zero witness" attack has no surface here. What can be checked is whether the
*proof* is doing work, and four theorems say it is:

* `badSum_pos` — the bad set is not empty: `badLambda 2 = Λ 2 = log 2 > 0`, so the sum the removal
  term pays for is strictly positive for every `H ≥ 3`. The decomposition is not vacuous.
* `naive_shape_exceeds_budget` — if `badSum` is replaced by the only bound available without the
  rarity of prime powers (namely `lamSum`, of size `H`), the resulting `3·L·H²` exceeds
  `c·H^{3/2}L²` for **every** `c ≤ 10⁴`, i.e. by a factor of at least `10³` beyond `cPP = 10`. The
  `ψ−θ` input is load-bearing, not decoration.
* `primePowerRemoval_mono` — the obligation genuinely weakens as `cPP` grows, so quoting a larger
  constant is a real (if weaker) result and not a change of statement.
* `primePowerRemoval_all` — the `Odd H` of the link is *not used*, and rather than leave that as a
  remark the stronger `Odd`-free statement is the theorem actually proved, with
  `primePowerRemoval_of` reinstating the hypothesis to match the spine's `Prop`. An unused
  hypothesis one cannot see is where a silent weakening would hide.

A fifth check is negative and worth recording: `PrimePowerRemoval 0` would force
`lambdaTriple = ternaryLogCount` (with `Spine.ternaryLogCount_le_lambdaTriple`), and refuting it
needs an *odd* `H ≥ 10^27` with a prime-power representation — which is not constructible without a
ternary-Goldbach-type input. So the necessity of a positive `cPP` is argued here, not proved.
-/

namespace Principia.Common.TernaryGoldbach.PrimePower

open ArithmeticFunction
open Principia.Common.TernaryGoldbach.Spine
open scoped ArithmeticFunction

/-! ## `Λ` off the odd primes -/

/-- **`Λ` with the odd primes deleted.** `badLambda n = Λ n` unless `n` is an odd prime, in which
case it is `0`. Its support is exactly the set of prime powers that `ternaryLogCount`'s guard
rejects: the proper prime powers and `2`. -/
noncomputable def badLambda (n : ℕ) : ℝ := if n.Prime ∧ Odd n then 0 else Λ n

theorem badLambda_nonneg (n : ℕ) : 0 ≤ badLambda n := by
  unfold badLambda
  split
  · exact le_refl 0
  · exact vonMangoldt_nonneg

/-- Off the odd primes `badLambda` *is* `Λ`, which is what lets a dropped summand be captured. -/
theorem badLambda_eq_of_not {n : ℕ} (h : ¬(n.Prime ∧ Odd n)) : badLambda n = Λ n := by
  unfold badLambda; rw [if_neg h]

theorem badLambda_two : badLambda 2 = Real.log 2 := by
  unfold badLambda
  rw [if_neg (by decide), vonMangoldt_apply_prime Nat.prime_two]
  norm_num

/-- `Λ n ≤ log H` for every `n ≤ H`: the trivial bound, spent once in each of the three
coordinates. -/
theorem lambda_le_log (H n : ℕ) (hn : n ≤ H) (hH : 1 ≤ H) : Λ n ≤ Real.log (H : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · have : Λ 0 = 0 := by simp
    rw [this]
    exact Real.log_nonneg (by exact_mod_cast hH)
  · refine le_trans vonMangoldt_le_log (Real.log_le_log ?_ ?_)
    · exact_mod_cast hpos
    · exact_mod_cast hn

/-! ## Two `Finset` manipulations

The first moves a `Finset.range` sum into the `Finset.Ioc` that `Chebyshev.psi` is written over;
the second is the reindexing the *third* coordinate needs, since `H − p − q` is not a free
summation variable. -/

/-- `∑_{n < H} f n ≤ ∑_{0 < n ≤ H} f n` for non-negative `f` vanishing at `0`. -/
theorem sum_range_le_sum_Ioc (H : ℕ) (f : ℕ → ℝ) (hf0 : f 0 = 0) (hf : ∀ n, 0 ≤ f n) :
    ∑ n ∈ Finset.range H, f n ≤ ∑ n ∈ Finset.Ioc 0 H, f n := by
  rw [← Finset.sum_erase (Finset.range H) hf0]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hf i)
  intro n hn
  simp only [Finset.mem_erase, Finset.mem_range] at hn
  simp only [Finset.mem_Ioc]
  omega

/-- **The third-coordinate reindexing.** For `q ≥ 1` the map `p ↦ H − p − q` is injective on
`{p : p + q < H}` and lands in `Finset.range H`, so a sum of `f (H − p − q)` over `p` is bounded by
the same sum over a free variable. `q ≥ 1` is needed: at `p = q = 0` the image is `H ∉ range H`,
and that term is killed instead by `Λ 0 = 0` at the point of use. -/
theorem sum_shift_le (H q : ℕ) (hq : 1 ≤ q) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    ∑ p ∈ Finset.range H, (if p + q < H then f (H - p - q) else 0)
      ≤ ∑ n ∈ Finset.range H, f n := by
  rw [← Finset.sum_filter]
  have hinj : ∀ x ∈ (Finset.range H).filter (fun p => p + q < H),
      ∀ y ∈ (Finset.range H).filter (fun p => p + q < H),
      H - x - q = H - y - q → x = y := by
    intro x hx y hy hxy
    simp only [Finset.mem_filter, Finset.mem_range] at hx hy
    omega
  have hsub : ((Finset.range H).filter (fun p => p + q < H)).image (fun p => H - p - q)
      ⊆ Finset.range H := by
    intro n hn
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨p, ⟨hp1, hp2⟩, rfl⟩ := hn
    simp only [Finset.mem_range]
    omega
  calc ∑ p ∈ (Finset.range H).filter (fun p => p + q < H), f (H - p - q)
      = ∑ n ∈ ((Finset.range H).filter (fun p => p + q < H)).image (fun p => H - p - q), f n :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ n ∈ Finset.range H, f n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hf i)

/-- Pull a constant out of a guarded summand. -/
theorem sum_ite_mul_left (H : ℕ) (k : ℝ) (f : ℕ → ℝ) (c : ℕ → Prop) [∀ p, Decidable (c p)] :
    ∑ p ∈ Finset.range H, (if c p then k * f p else 0)
      = k * ∑ p ∈ Finset.range H, (if c p then f p else 0) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  split
  · rfl
  · rw [mul_zero]

/-! ## The two one-dimensional sums -/

/-- `∑_{n < H} Λ n`, the Chebyshev `ψ` sum in the shape the triple sums use. -/
noncomputable def lamSum (H : ℕ) : ℝ := ∑ n ∈ Finset.range H, Λ n

/-- `∑_{n < H} badLambda n`: `Λ` summed over the prime powers that are **not** odd primes. This is
the quantity whose smallness (`≈ √H log H`, not `H`) is the entire reason the link is affordable. -/
noncomputable def badSum (H : ℕ) : ℝ := ∑ n ∈ Finset.range H, badLambda n

theorem lamSum_nonneg (H : ℕ) : 0 ≤ lamSum H :=
  Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg

theorem badSum_nonneg (H : ℕ) : 0 ≤ badSum H :=
  Finset.sum_nonneg fun n _ => badLambda_nonneg n

/-- **The bad set is not empty.** `2` is a prime the `Odd` guard rejects, so `badSum H ≥ log 2 > 0`
for every `H ≥ 3`: the removal term pays for something that is really there. -/
theorem badSum_pos (H : ℕ) (hH : 3 ≤ H) : 0 < badSum H := by
  have hmem : (2 : ℕ) ∈ Finset.range H := Finset.mem_range.mpr (by omega)
  have h := Finset.single_le_sum (f := badLambda) (fun i _ => badLambda_nonneg i) hmem
  rw [badLambda_two] at h
  have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  exact lt_of_lt_of_le this h

theorem lamSum_le_psi (H : ℕ) : lamSum H ≤ Chebyshev.psi (H : ℝ) := by
  have e : Chebyshev.psi (H : ℝ) = ∑ n ∈ Finset.Ioc 0 H, Λ n := by
    rw [Chebyshev.psi, Nat.floor_natCast]
  rw [lamSum, e]
  exact sum_range_le_sum_Ioc H _ (by simp) (fun _ => vonMangoldt_nonneg)

/-- **`badSum` is `ψ − θ` plus the one prime the parity guard removes.** The `+ log 2` is the entire
contribution of "a coordinate equals `2`"; since `H` is odd it cannot be avoided, and since it is a
single term it costs nothing. -/
theorem badSum_le_psi_sub_theta (H : ℕ) :
    badSum H ≤ (Chebyshev.psi (H : ℝ) - Chebyshev.theta (H : ℝ)) + Real.log 2 := by
  have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hterm : ∀ n : ℕ, badLambda n
      ≤ (if ¬ n.Prime then Λ n else 0) + (if n = 2 then Real.log 2 else 0) := by
    intro n
    unfold badLambda
    by_cases h : n.Prime ∧ Odd n
    · rw [if_pos h]
      have h1 : (0 : ℝ) ≤ (if ¬ n.Prime then Λ n else 0) := by
        split
        · exact vonMangoldt_nonneg
        · exact le_refl 0
      have h2 : (0 : ℝ) ≤ (if n = 2 then Real.log 2 else 0) := by
        split
        · exact hl2
        · exact le_refl 0
      linarith
    · rw [if_neg h]
      by_cases hp : n.Prime
      · have h2 : n = 2 := by
          rcases hp.eq_two_or_odd' with h' | h'
          · exact h'
          · exact absurd ⟨hp, h'⟩ h
        subst h2
        rw [if_neg (not_not.mpr Nat.prime_two), if_pos rfl,
          vonMangoldt_apply_prime Nat.prime_two]
        norm_num
      · rw [if_pos hp]
        have h2 : (0 : ℝ) ≤ (if n = 2 then Real.log 2 else 0) := by
          split
          · exact hl2
          · exact le_refl 0
        linarith
  have hsplit : (Chebyshev.psi (H : ℝ) - Chebyshev.theta (H : ℝ))
      = ∑ n ∈ Finset.Ioc 0 H, (if ¬ n.Prime then Λ n else 0) := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, Finset.sum_filter]
  have hA : ∑ n ∈ Finset.range H, (if ¬ n.Prime then Λ n else 0)
      ≤ Chebyshev.psi (H : ℝ) - Chebyshev.theta (H : ℝ) := by
    rw [hsplit]
    refine sum_range_le_sum_Ioc H _ (by simp) (fun n => ?_)
    split
    · exact vonMangoldt_nonneg
    · exact le_refl 0
  have hB : ∑ n ∈ Finset.range H, (if n = 2 then Real.log 2 else 0) ≤ Real.log 2 := by
    rw [Finset.sum_ite_eq' (Finset.range H) 2 (fun _ => Real.log 2)]
    split
    · exact le_refl _
    · exact hl2
  calc badSum H
      ≤ ∑ n ∈ Finset.range H,
          ((if ¬ n.Prime then Λ n else 0) + (if n = 2 then Real.log 2 else 0)) :=
        Finset.sum_le_sum fun n _ => hterm n
    _ = (∑ n ∈ Finset.range H, (if ¬ n.Prime then Λ n else 0))
        + ∑ n ∈ Finset.range H, (if n = 2 then Real.log 2 else 0) := Finset.sum_add_distrib
    _ ≤ (Chebyshev.psi (H : ℝ) - Chebyshev.theta (H : ℝ)) + Real.log 2 := by linarith

/-! ## The three dropped-summand sums -/

/-- The dropped summands with the offending coordinate **first**. -/
noncomputable def badTriple1 (H : ℕ) : ℝ :=
  ∑ p ∈ Finset.range H, ∑ q ∈ Finset.range H,
    if p + q < H then badLambda p * Λ q * Λ (H - p - q) else 0

/-- The dropped summands with the offending coordinate **second**. -/
noncomputable def badTriple2 (H : ℕ) : ℝ :=
  ∑ p ∈ Finset.range H, ∑ q ∈ Finset.range H,
    if p + q < H then Λ p * badLambda q * Λ (H - p - q) else 0

/-- The dropped summands with the offending coordinate **third**. This is the one that needs
`sum_shift_le`, because `H − p − q` is not a summation variable. -/
noncomputable def badTriple3 (H : ℕ) : ℝ :=
  ∑ p ∈ Finset.range H, ∑ q ∈ Finset.range H,
    if p + q < H then Λ p * Λ q * badLambda (H - p - q) else 0

/-- **The termwise step.** Every summand of `lambdaTriple` is covered by the corresponding summand
of `ternaryLogCount` plus the three `badTriple` summands. If the guard of `ternaryLogCount` holds
the two agree (`Λ = log` at a prime); if it fails while `p + q < H`, one of the three coordinates
fails `Prime ∧ Odd`, and `badLambda` equals `Λ` there, so exactly one of the three extra terms
reproduces the whole product. -/
theorem term_le (H p q : ℕ) :
    (if p + q < H then Λ p * Λ q * Λ (H - p - q) else 0)
      ≤ (if p + q < H ∧ p.Prime ∧ q.Prime ∧ (H - p - q).Prime ∧ Odd p ∧ Odd q ∧
            Odd (H - p - q)
          then Real.log p * Real.log q * Real.log ((H - p - q : ℕ) : ℝ) else 0)
        + (if p + q < H then badLambda p * Λ q * Λ (H - p - q) else 0)
        + (if p + q < H then Λ p * badLambda q * Λ (H - p - q) else 0)
        + (if p + q < H then Λ p * Λ q * badLambda (H - p - q) else 0) := by
  by_cases hpq : p + q < H
  · have hn1 : (0 : ℝ) ≤ badLambda p * Λ q * Λ (H - p - q) :=
      mul_nonneg (mul_nonneg (badLambda_nonneg p) vonMangoldt_nonneg) vonMangoldt_nonneg
    have hn2 : (0 : ℝ) ≤ Λ p * badLambda q * Λ (H - p - q) :=
      mul_nonneg (mul_nonneg vonMangoldt_nonneg (badLambda_nonneg q)) vonMangoldt_nonneg
    have hn3 : (0 : ℝ) ≤ Λ p * Λ q * badLambda (H - p - q) :=
      mul_nonneg (mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg)
        (badLambda_nonneg (H - p - q))
    rw [if_pos hpq]
    rw [show (if p + q < H then badLambda p * Λ q * Λ (H - p - q) else 0)
        = badLambda p * Λ q * Λ (H - p - q) from if_pos hpq]
    rw [show (if p + q < H then Λ p * badLambda q * Λ (H - p - q) else 0)
        = Λ p * badLambda q * Λ (H - p - q) from if_pos hpq]
    rw [show (if p + q < H then Λ p * Λ q * badLambda (H - p - q) else 0)
        = Λ p * Λ q * badLambda (H - p - q) from if_pos hpq]
    by_cases h1 : p.Prime ∧ Odd p
    · by_cases h2 : q.Prime ∧ Odd q
      · by_cases h3 : (H - p - q).Prime ∧ Odd (H - p - q)
        · have heq : Real.log (p : ℝ) * Real.log (q : ℝ) * Real.log ((H - p - q : ℕ) : ℝ)
              = Λ p * Λ q * Λ (H - p - q) := by
            rw [vonMangoldt_apply_prime h1.1, vonMangoldt_apply_prime h2.1,
              vonMangoldt_apply_prime h3.1]
          rw [if_pos ⟨hpq, h1.1, h2.1, h3.1, h1.2, h2.2, h3.2⟩, heq]
          linarith
        · rw [if_neg (fun hs => h3 ⟨hs.2.2.2.1, hs.2.2.2.2.2.2⟩), badLambda_eq_of_not h3]
          linarith
      · rw [if_neg (fun hs => h2 ⟨hs.2.2.1, hs.2.2.2.2.2.1⟩), badLambda_eq_of_not h2]
        linarith
    · rw [if_neg (fun hs => h1 ⟨hs.2.1, hs.2.2.2.2.1⟩), badLambda_eq_of_not h1]
      linarith
  · have hs : ¬(p + q < H ∧ p.Prime ∧ q.Prime ∧ (H - p - q).Prime ∧ Odd p ∧ Odd q ∧
        Odd (H - p - q)) := fun h => hpq h.1
    rw [if_neg hpq, if_neg hs]
    rw [show (if p + q < H then badLambda p * Λ q * Λ (H - p - q) else 0) = 0 from if_neg hpq]
    rw [show (if p + q < H then Λ p * badLambda q * Λ (H - p - q) else 0) = 0 from if_neg hpq]
    rw [show (if p + q < H then Λ p * Λ q * badLambda (H - p - q) else 0) = 0 from if_neg hpq]
    norm_num

/-- **The decomposition.** `lambdaTriple` is below `ternaryLogCount` plus the three sums of dropped
summands. Nothing here is asymptotic; it is `term_le` summed twice. -/
theorem lambdaTriple_le (H : ℕ) :
    lambdaTriple H ≤ ternaryLogCount H + badTriple1 H + badTriple2 H + badTriple3 H := by
  simp only [lambdaTriple, ternaryLogCount, badTriple1, badTriple2, badTriple3]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun q _ => term_le H p q

/-! ## Bounding the three sums

Each is `badSum · log H · lamSum` — one coordinate pays `badLambda`, one pays the trivial
`Λ ≤ log H`, and one pays `Λ` summed freely. -/

theorem badTriple1_le (H : ℕ) (hH : 1 ≤ H) :
    badTriple1 H ≤ badSum H * (Real.log (H : ℝ) * lamSum H) := by
  have hLnn : (0 : ℝ) ≤ Real.log (H : ℝ) := Real.log_nonneg (by exact_mod_cast hH)
  calc badTriple1 H
      ≤ ∑ p ∈ Finset.range H, badLambda p * (Real.log (H : ℝ) * lamSum H) := by
        refine Finset.sum_le_sum fun p _ => ?_
        calc ∑ q ∈ Finset.range H,
              (if p + q < H then badLambda p * Λ q * Λ (H - p - q) else 0)
            ≤ ∑ q ∈ Finset.range H, badLambda p * Λ q * Real.log (H : ℝ) := by
              refine Finset.sum_le_sum fun q _ => ?_
              by_cases hc : p + q < H
              · rw [if_pos hc]
                exact mul_le_mul_of_nonneg_left (lambda_le_log H (H - p - q) (by omega) hH)
                  (mul_nonneg (badLambda_nonneg p) vonMangoldt_nonneg)
              · rw [if_neg hc]
                exact mul_nonneg (mul_nonneg (badLambda_nonneg p) vonMangoldt_nonneg) hLnn
          _ = badLambda p * (Real.log (H : ℝ) * lamSum H) := by
              rw [lamSum, Finset.mul_sum, Finset.mul_sum]
              exact Finset.sum_congr rfl fun q _ => by ring
    _ = badSum H * (Real.log (H : ℝ) * lamSum H) := by rw [badSum, ← Finset.sum_mul]

theorem badTriple2_le (H : ℕ) (hH : 1 ≤ H) :
    badTriple2 H ≤ lamSum H * (Real.log (H : ℝ) * badSum H) := by
  have hLnn : (0 : ℝ) ≤ Real.log (H : ℝ) := Real.log_nonneg (by exact_mod_cast hH)
  calc badTriple2 H
      ≤ ∑ p ∈ Finset.range H, Λ p * (Real.log (H : ℝ) * badSum H) := by
        refine Finset.sum_le_sum fun p _ => ?_
        calc ∑ q ∈ Finset.range H,
              (if p + q < H then Λ p * badLambda q * Λ (H - p - q) else 0)
            ≤ ∑ q ∈ Finset.range H, Λ p * badLambda q * Real.log (H : ℝ) := by
              refine Finset.sum_le_sum fun q _ => ?_
              by_cases hc : p + q < H
              · rw [if_pos hc]
                exact mul_le_mul_of_nonneg_left (lambda_le_log H (H - p - q) (by omega) hH)
                  (mul_nonneg vonMangoldt_nonneg (badLambda_nonneg q))
              · rw [if_neg hc]
                exact mul_nonneg (mul_nonneg vonMangoldt_nonneg (badLambda_nonneg q)) hLnn
          _ = Λ p * (Real.log (H : ℝ) * badSum H) := by
              rw [badSum, Finset.mul_sum, Finset.mul_sum]
              exact Finset.sum_congr rfl fun q _ => by ring
    _ = lamSum H * (Real.log (H : ℝ) * badSum H) := by rw [lamSum, ← Finset.sum_mul]

theorem badTriple3_le (H : ℕ) (hH : 1 ≤ H) :
    badTriple3 H ≤ Real.log (H : ℝ) * (lamSum H * badSum H) := by
  have hLnn : (0 : ℝ) ≤ Real.log (H : ℝ) := Real.log_nonneg (by exact_mod_cast hH)
  have step1 : badTriple3 H
      ≤ ∑ p ∈ Finset.range H, ∑ q ∈ Finset.range H,
          (if p + q < H then Real.log (H : ℝ) * (Λ q * badLambda (H - p - q)) else 0) := by
    refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => ?_
    by_cases hc : p + q < H
    · rw [if_pos hc, if_pos hc]
      have hrw : Λ p * Λ q * badLambda (H - p - q)
          = (Λ q * badLambda (H - p - q)) * Λ p := by ring
      have hrw2 : Real.log (H : ℝ) * (Λ q * badLambda (H - p - q))
          = (Λ q * badLambda (H - p - q)) * Real.log (H : ℝ) := by ring
      rw [hrw, hrw2]
      exact mul_le_mul_of_nonneg_left (lambda_le_log H p (by omega) hH)
        (mul_nonneg vonMangoldt_nonneg (badLambda_nonneg (H - p - q)))
    · rw [if_neg hc, if_neg hc]
  have step2 : ∑ p ∈ Finset.range H, ∑ q ∈ Finset.range H,
      (if p + q < H then Real.log (H : ℝ) * (Λ q * badLambda (H - p - q)) else 0)
      ≤ Real.log (H : ℝ) * (lamSum H * badSum H) := by
    rw [Finset.sum_comm]
    calc ∑ q ∈ Finset.range H, ∑ p ∈ Finset.range H,
          (if p + q < H then Real.log (H : ℝ) * (Λ q * badLambda (H - p - q)) else 0)
        ≤ ∑ q ∈ Finset.range H, Real.log (H : ℝ) * (Λ q * badSum H) := by
          refine Finset.sum_le_sum fun q _ => ?_
          rcases Nat.eq_zero_or_pos q with rfl | hq
          · have hz : Λ 0 = 0 := by simp
            have : ∀ p ∈ Finset.range H,
                (if p + 0 < H then Real.log (H : ℝ) * (Λ 0 * badLambda (H - p - 0)) else 0)
                  = (0 : ℝ) := by
              intro p _
              split
              · rw [hz, zero_mul, mul_zero]
              · rfl
            rw [Finset.sum_congr rfl this, Finset.sum_const, smul_zero, hz, zero_mul, mul_zero]
          · calc ∑ p ∈ Finset.range H,
                  (if p + q < H then Real.log (H : ℝ) * (Λ q * badLambda (H - p - q)) else 0)
                = ∑ p ∈ Finset.range H,
                    (if p + q < H then (Real.log (H : ℝ) * Λ q) * badLambda (H - p - q)
                      else 0) := by
                  refine Finset.sum_congr rfl fun p _ => ?_
                  split
                  · ring
                  · rfl
              _ = (Real.log (H : ℝ) * Λ q)
                    * ∑ p ∈ Finset.range H,
                        (if p + q < H then badLambda (H - p - q) else 0) :=
                  sum_ite_mul_left H _ _ _
              _ ≤ (Real.log (H : ℝ) * Λ q) * badSum H := by
                  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hLnn vonMangoldt_nonneg)
                  exact sum_shift_le H q hq badLambda badLambda_nonneg
              _ = Real.log (H : ℝ) * (Λ q * badSum H) := by ring
      _ = Real.log (H : ℝ) * (lamSum H * badSum H) := by
          rw [lamSum, Finset.sum_mul, Finset.mul_sum]
  exact le_trans step1 step2

/-- **The whole bookkeeping in one line**, with no asymptotics yet: the difference between the two
counts is at most `3·(log H)·(∑Λ)·(∑badLambda)`. -/
theorem lambdaTriple_sub_le (H : ℕ) (hH : 1 ≤ H) :
    lambdaTriple H - ternaryLogCount H ≤ 3 * (Real.log (H : ℝ) * (lamSum H * badSum H)) := by
  have h1 := badTriple1_le H hH
  have h2 := badTriple2_le H hH
  have h3 := badTriple3_le H hH
  have h0 := lambdaTriple_le H
  nlinarith [h0, h1, h2, h3]

/-! ## The two Chebyshev inputs at the threshold -/

/-- `∑_{n < H} Λ n ≤ 1.3865·H`. Chebyshev's `ψ x ≤ log 4·x + 2√x log x` with the second term
absorbed by `log H ≤ √H/10⁴`; `log 4 < 1.3863` and `2/10⁴ = 0.0002`. -/
theorem lamSum_le_of_large (H : ℕ) (hH : 10 ^ 27 ≤ H) : lamSum H ≤ 1.3865 * (H : ℝ) := by
  have hHR : (10 : ℝ) ^ 27 ≤ (H : ℝ) := by exact_mod_cast hH
  have hten : (0 : ℝ) < (10 : ℝ) ^ 27 := by positivity
  have h1 : (1 : ℝ) ≤ (H : ℝ) := by nlinarith
  have hpsi := Chebyshev.psi_le h1
  have hlam := lamSum_le_psi H
  have hLS := Spine.log_le_sqrt_div H hH
  have hSnn : (0 : ℝ) ≤ Real.sqrt (H : ℝ) := Real.sqrt_nonneg _
  have hSS : Real.sqrt (H : ℝ) * Real.sqrt (H : ℝ) = (H : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  have hlog4 : Real.log 4 ≤ 1.3863 := by
    have h : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [h]; linarith [Real.log_two_lt_d9]
  have h2 : 2 * Real.sqrt (H : ℝ) * Real.log (H : ℝ) ≤ 2 * (H : ℝ) / 10 ^ 4 := by
    nlinarith [hLS, hSnn, hSS]
  have h3 : Real.log 4 * (H : ℝ) ≤ 1.3863 * (H : ℝ) :=
    mul_le_mul_of_nonneg_right hlog4 (by positivity)
  linarith

/-- `∑_{n < H} badLambda n ≤ 2√H log H + 0.694`: Mathlib's `ψ − θ ≤ 2√x log x` for the proper prime
powers, plus `Λ 2 = log 2 < 0.694` for the one prime the `Odd` guard removes. -/
theorem badSum_le_of_large (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    badSum H ≤ 2 * Real.sqrt (H : ℝ) * Real.log (H : ℝ) + 0.694 := by
  have hHR : (10 : ℝ) ^ 27 ≤ (H : ℝ) := by exact_mod_cast hH
  have hten : (0 : ℝ) < (10 : ℝ) ^ 27 := by positivity
  have h1 : (1 : ℝ) ≤ (H : ℝ) := by nlinarith
  have hpt := Chebyshev.psi_sub_theta_le h1
  have hbad := badSum_le_psi_sub_theta H
  have hl2 : Real.log 2 ≤ 0.694 := le_of_lt (lt_trans Real.log_two_lt_d9 (by norm_num))
  linarith

/-! ## THE LINK, DISCHARGED -/

/-- **Link 7, proved without `Odd H`** — the strictly stronger statement, recorded so the unused
hypothesis is a theorem rather than a remark.

The constant: `3` coordinates × `log 4 = 1.3863…` (Chebyshev's `ψ`) × `2` (Mathlib's `ψ − θ`) gives
`6 log 4 = 8.31776…`, and `8.32` is the round number above it once `log H ≤ √H/10⁴` has absorbed
lower-order pieces.

Dropping `Odd H` is not a gap: parity enters the *goal* through `ternaryLogCount`'s guard
(`Spine.lowerWith_needs_odd` shows an even `H` makes the spine's conclusion false), and the one
place it touches *this* link is the coordinate value `2` — which `badSum_le_psi_sub_theta` charges
unconditionally, at `log 2`. So the removal inequality holds for every `H ≥ 10^27`. -/
theorem primePowerRemoval_all (cPP : ℝ) (hc : 8.32 ≤ cPP) :
    ∀ H : ℕ, 10 ^ 27 ≤ H →
      lambdaTriple H - cPP * ((H : ℝ) * Real.sqrt (H : ℝ)) * Real.log (H : ℝ) ^ 2
        ≤ ternaryLogCount H := by
  intro H hH
  have hHR : (10 : ℝ) ^ 27 ≤ (H : ℝ) := by exact_mod_cast hH
  have hten : (0 : ℝ) < (10 : ℝ) ^ 27 := by positivity
  have hXpos : (0 : ℝ) < (H : ℝ) := by nlinarith
  have hH1 : 1 ≤ H := le_trans (by norm_num) hH
  have hL61 : (61 : ℝ) ≤ Real.log (H : ℝ) := Spine.log_ge_61 H hH
  have hSnn : (0 : ℝ) ≤ Real.sqrt (H : ℝ) := Real.sqrt_nonneg _
  have hS13 : (10 : ℝ) ^ 13 ≤ Real.sqrt (H : ℝ) := by
    rw [show ((10 : ℝ) ^ 13) = Real.sqrt ((10 : ℝ) ^ 26) by
      rw [show ((10 : ℝ) ^ 26) = ((10 : ℝ) ^ 13) ^ 2 by ring, Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hlamB := lamSum_le_of_large H hH
  have hbadB := badSum_le_of_large H hH
  have hlam0 := lamSum_nonneg H
  have hbad0 := badSum_nonneg H
  have hdiff := lambdaTriple_sub_le H hH1
  -- the product bound
  have hprod : lamSum H * badSum H
      ≤ (1.3865 * (H : ℝ)) * (2 * Real.sqrt (H : ℝ) * Real.log (H : ℝ) + 0.694) := by
    refine mul_le_mul hlamB hbadB hbad0 ?_
    nlinarith
  have hstep : 3 * (Real.log (H : ℝ) * (lamSum H * badSum H))
      ≤ 3 * (Real.log (H : ℝ)
          * ((1.3865 * (H : ℝ)) * (2 * Real.sqrt (H : ℝ) * Real.log (H : ℝ) + 0.694))) := by
    have := mul_le_mul_of_nonneg_left hprod (show (0 : ℝ) ≤ Real.log (H : ℝ) by linarith)
    linarith
  -- the numeric comparison
  have hSL : (2.89 : ℝ) ≤ 0.001 * (Real.sqrt (H : ℝ) * Real.log (H : ℝ)) := by nlinarith
  have hbudget : 3 * (Real.log (H : ℝ)
        * ((1.3865 * (H : ℝ)) * (2 * Real.sqrt (H : ℝ) * Real.log (H : ℝ) + 0.694)))
      ≤ cPP * ((H : ℝ) * Real.sqrt (H : ℝ)) * Real.log (H : ℝ) ^ 2 := by
    have hXL : (0 : ℝ) ≤ (H : ℝ) * Real.log (H : ℝ) := by positivity
    have hslack : (0 : ℝ)
        ≤ (H : ℝ) * Real.log (H : ℝ) * (0.001 * (Real.sqrt (H : ℝ) * Real.log (H : ℝ)) - 2.89) :=
      mul_nonneg hXL (by linarith)
    have hc2 : (0.001 : ℝ) * ((H : ℝ) * Real.sqrt (H : ℝ) * Real.log (H : ℝ) ^ 2)
        ≤ (cPP - 8.319) * ((H : ℝ) * Real.sqrt (H : ℝ) * Real.log (H : ℝ) ^ 2) := by
      refine mul_le_mul_of_nonneg_right (by linarith) ?_
      positivity
    nlinarith [hslack, hc2]
  linarith

/-- **Link 7 is proved for every `cPP ≥ 8.32`**: `Spine.PrimePowerRemoval cPP` is
`primePowerRemoval_all` with the (unused) `Odd H` hypothesis reinstated, so it is exactly the
proposition the spine's assembly consumes. -/
theorem primePowerRemoval_of (cPP : ℝ) (hc : 8.32 ≤ cPP) : PrimePowerRemoval cPP :=
  fun H _ hH => primePowerRemoval_all cPP hc H hH

/-- The obligation weakens as the constant grows, so a larger `cPP` is a real result. -/
theorem primePowerRemoval_mono {c d : ℝ} (hcd : c ≤ d) (h : PrimePowerRemoval c) :
    PrimePowerRemoval d := by
  intro H hodd hH
  have hnn : (0 : ℝ) ≤ (H : ℝ) * Real.sqrt (H : ℝ) * Real.log (H : ℝ) ^ 2 := by
    have : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
    positivity
  have := h H hodd hH
  nlinarith [mul_le_mul_of_nonneg_right hcd hnn]

/-- **The spine's instance.** `Spine.ternaryLogCountLower_of_links_main` and `..._sharp` both
consume `PrimePowerRemoval 10`. -/
theorem primePowerRemoval_ten : PrimePowerRemoval 10 := primePowerRemoval_of 10 (by norm_num)

/-- `cPP = 9` also holds; the budget charge `cPP/10⁴` drops from `0.001` to `0.0009`. -/
theorem primePowerRemoval_nine : PrimePowerRemoval 9 := primePowerRemoval_of 9 (by norm_num)

/-- The smallest constant **this assembly, with these Mathlib inputs**, proves: `3·log 4·2 =
8.31776616…`. It is *not* a floor for the obligation — Rosser–Schoenfeld's log-free `ψ−θ`
bound would
reach `≈ 0.0955` (see the module docstring), which we skip because `cPP` is charged to the
budget only as `cPP/10⁴` and the gain is 0.15 % on `κ`. The name is kept for continuity; read it as
"this route's constant", not as a lower bound. -/
theorem primePowerRemoval_floor : PrimePowerRemoval 8.32 :=
  primePowerRemoval_of 8.32 (le_refl _)

/-! ## What the spine now needs

Three links, not four. -/

/-- **`ternaryLogCountLower_of_links_main` with the prime-power link discharged.** Exactly three
hypotheses remain: the circle-method identity, the major-arc lower bound, and the minor-arc sup
bound. -/
theorem ternaryLogCountLower_of_three_links (P Q : ℕ → ℕ) (cm : CircleMethodIdentity)
    (mj : MajorArcLower P Q (1 / 2)) (mn : MinorSupBound P Q (3 / 10)) :
    TernaryLogCountLower :=
  Spine.ternaryLogCountLower_of_links_main P Q cm mj mn primePowerRemoval_ten

/-- The same, delivered at the EP1054 input itself. -/
theorem cite_Helfgott_weighted_of_three_links (P Q : ℕ → ℕ) (cm : CircleMethodIdentity)
    (mj : MajorArcLower P Q (1 / 2)) (mn : MinorSupBound P Q (3 / 10)) :
    Principia.Erdos1054.Cite_Helfgott_weighted :=
  Spine.cite_Helfgott_weighted_of_links_main P Q cm mj mn primePowerRemoval_ten

/-- The sharp instantiation, likewise. -/
theorem ternaryLogCountLower_of_three_links_sharp (P Q : ℕ → ℕ) (cm : CircleMethodIdentity)
    (mj : MajorArcLower P Q (13 / 20)) (mn : MinorSupBound P Q (46 / 100)) :
    TernaryLogCountLower :=
  Spine.ternaryLogCountLower_of_links_sharp P Q cm mj mn primePowerRemoval_ten

/-! ## The adversarial pass -/

/-- **The rarity of prime powers is load-bearing.** Without it the only bound available for
`badSum H` is `lamSum H`, of size `H`, and the resulting `3·(log H)·H²` exceeds the budget
`c·H^{3/2}(log H)²` for **every** `c ≤ 10⁴` — a factor `10³` beyond the `cPP = 10` actually used.
So `Chebyshev.psi_sub_theta_le` is not decoration: it is the only reason the link is affordable. -/
theorem naive_shape_exceeds_budget (H : ℕ) (hH : 10 ^ 27 ≤ H) (c : ℝ) (hc : c ≤ 10 ^ 4) :
    c * ((H : ℝ) * Real.sqrt (H : ℝ)) * Real.log (H : ℝ) ^ 2
      < 3 * Real.log (H : ℝ) * ((H : ℝ) * (H : ℝ)) := by
  have hHR : (10 : ℝ) ^ 27 ≤ (H : ℝ) := by exact_mod_cast hH
  have hten : (0 : ℝ) < (10 : ℝ) ^ 27 := by positivity
  have hXpos : (0 : ℝ) < (H : ℝ) := by nlinarith
  have hL61 : (61 : ℝ) ≤ Real.log (H : ℝ) := Spine.log_ge_61 H hH
  have hLS := Spine.log_le_sqrt_div H hH
  have hSpos : (0 : ℝ) < Real.sqrt (H : ℝ) := Real.sqrt_pos.mpr hXpos
  have hSS : Real.sqrt (H : ℝ) * Real.sqrt (H : ℝ) = (H : ℝ) :=
    Real.mul_self_sqrt (le_of_lt hXpos)
  -- `c·L ≤ 10⁴·(√H/10⁴) = √H`, hence `c·√H·L ≤ H < 3H`
  have hcL : c * Real.log (H : ℝ) ≤ Real.sqrt (H : ℝ) := by nlinarith
  have h1 : Real.sqrt (H : ℝ) * (c * Real.log (H : ℝ))
      ≤ Real.sqrt (H : ℝ) * Real.sqrt (H : ℝ) :=
    mul_le_mul_of_nonneg_left hcL (le_of_lt hSpos)
  have h2 : c * (Real.sqrt (H : ℝ) * Real.log (H : ℝ)) < 3 * (H : ℝ) := by
    rw [hSS] at h1; nlinarith [h1, hXpos]
  have hHL : (0 : ℝ) < (H : ℝ) * Real.log (H : ℝ) :=
    mul_pos hXpos (by linarith)
  nlinarith [mul_lt_mul_of_pos_right h2 hHL]

end Principia.Common.TernaryGoldbach.PrimePower
