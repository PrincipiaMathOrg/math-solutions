/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Spine
import Principia.Erdos1054.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.FactorisationProperties
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Data.Nat.Squarefree
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false

/-!
# EP1054 §4.3, the family `𝒜₀(X)`: the `A0Family` package of the spine

Discharges the obligations of `Principia.Erdos1054.Spine` for paper
`Campaigns/Erdos-1054/collab-paper/EP1054.tex`, lines 1198–1302 (the construction of the
positive-density family `𝒜₀(X) = {pqrk}` of abundant witnesses and the unlabeled lemma on it).

Leaves (proved from the definitions and the pinned Mathlib alone):
* `leaf_Eq_SvBasic` — `eq:sv-basic` (line 1212): `s(n) ∈ 𝓡` and `f(s(n)) ≤ n` for `n ≥ 2`. The
  proper divisors of `n` are exactly the divisors `≤ n/minFac n`
  (`divisors_filter_le_eq_properDivisors`, ported from `problems/Erdos1054LeftTail.lean`), so
  `s(n)` is a divisor-prefix sum of `n`.
* `leaf_Eq_SvD` — `eq:sv-D` (line 1226): `D = ∏_{p < n} p` is squarefree and
  `σ(D)/D = ∏(1 + 1/p) ≥ 1 + ∑ 1/p`, unbounded by Mathlib's `not_summable_one_div_on_primes`.
* `leaf_SvA0_abundancySubmul` — `σ(ab)/(ab) ≤ (σ(a)/a)(σ(b)/b)` (line 1292), from
  `Nat.divisors_mul` (`divisors (ab) = divisors a * divisors b` pointwise).
* `leaf_SvA0_sigmaHarmonic` — `∑_{j ≤ J} σ(j)/j² ≤ ζ(2) ∑_{a ≤ J} 1/a` (lines 1261–1266). The
  proof writes `σ(j)/j² = ∑_{d ∣ j} d/j²` and substitutes `j = d a`, which gives
  `∑_{da ≤ J} 1/(d a²) ≤ (∑ 1/d)(∑ 1/a²)` — the paper's `1/(d² a)` with the roles of `d` and `a`
  swapped; the bound is the same.
* `leaf_Lem_SvA0Unique` — unique factorization (lines 1251–1252, 1285–1287), for `X ≥ 64`:
  `p > X^{11/30}` (else `X < 2pqrk ≤ 2X^{5/6}`), then the size separation of `p, q, r, k` forces
  `p = p'`, `q = q'`, `r = r'`, `k = k'` one prime at a time.
* `leaf_Lem_SvA0QLarge` — `q > n^{7/9}` (lines 1257, 1299–1301), for `X ≥ 1`.

Links (proved from exactly the dependencies the spine names):
* `link_Eq_SvTwoSided` (lines 1253–1256, 1289–1299) — from `SvA0_abundancySubmul`; lower bound by
  `Nat.abundancyIndex_le_of_dvd` (`D ∣ t`), upper bound `C_δ = 8 · 4ζ(2) · σ(D)/D`.
* `link_SvA0_jSum` (lines 1267–1273) — from `SvA0_sigmaHarmonic`; `harmonic_le_one_add_log`,
  `log_add_one_le_harmonic`, and the indicator bound `1[σ(j)/j > 4ζ(2)] ≤ (σ(j)/j)/(4ζ(2))`. The
  bad `j` cost at most `¼ H(J₂)`, giving `≥ (1/240) log X + ¼ log D − 1`.
* `link_Lem_SvA0Count` (lines 1245–1250, 1274–1283) — from `SvA0_jSum`, `Lem_SvA0Unique`,
  `Std_primes_dyadic_lower`, `Std_Mertens2`. The tuples `(p, q, r, Dj)` inject into `𝒜₀(X)`
  (`count_core`); each fibre has `≥ c₀ t / log X` primes `p ∈ (t, 2t]`, `t = X/(2qrk) ≥ 2`; the
  reciprocal sums are `≥ (1/480) log X` (over `j`), `≥ ½ log(5/4)` (over `r`) and
  `≥ ½ log(22/21)` (over `q`) by `Std_Mertens2` over power windows (`mertens_window`). The
  constant is `c₀ log(5/4) log(22/21) / (3840 D)`.

Not declared here: `Lem_SvA0` is the conjunction of the four assertions and is assembled by the
spine with `And.intro` (`Spine.spine_Lem_SvA0`); it has no `Link_`.
-/

namespace Principia.Erdos1054.Proofs.A0Family

open Finset Principia.Erdos1054

lemma divisors_filter_le_eq_properDivisors {m : ℕ} (hm : 2 ≤ m) :
    m.divisors.filter (· ≤ m / m.minFac) = m.properDivisors := by
  classical
  have hm0 : m ≠ 0 := by omega
  have hp : (m.minFac).Prime := Nat.minFac_prime (by omega)
  ext q
  simp only [Finset.mem_filter, Nat.mem_divisors, Nat.mem_properDivisors]
  constructor
  · rintro ⟨⟨hqd, -⟩, hle⟩
    refine ⟨hqd, ?_⟩
    have h1 : m / m.minFac < m := Nat.div_lt_self (by omega) hp.one_lt
    omega
  · rintro ⟨hqd, hqlt⟩
    refine ⟨⟨hqd, hm0⟩, ?_⟩
    obtain ⟨t, ht⟩ := hqd
    have ht2 : 2 ≤ t := by
      rcases Nat.lt_or_ge t 2 with h | h
      · exfalso
        have hcases : t = 0 ∨ t = 1 := by omega
        rcases hcases with h0 | h1
        · rw [h0, Nat.mul_zero] at ht; omega
        · rw [h1, mul_one] at ht; omega
      · exact h
    have hp' : (t.minFac).Prime := Nat.minFac_prime (by omega)
    have hpc : t.minFac ∣ t := Nat.minFac_dvd _
    have htm : t ∣ m := ⟨q, by rw [ht]; ring⟩
    have hpm : t.minFac ∣ m := hpc.trans htm
    have hle1 : m.minFac ≤ t.minFac := Nat.minFac_le_of_dvd hp'.two_le hpm
    have hmul : q * t.minFac ≤ m := by
      have hdvd : q * t.minFac ∣ m := by
        have h1 : q * t.minFac ∣ q * t := Nat.mul_dvd_mul_left q hpc
        rwa [← ht] at h1
      exact Nat.le_of_dvd (by omega) hdvd
    have hfin : q * m.minFac ≤ m := le_trans (Nat.mul_le_mul_left q hle1) hmul
    have hmp : (m / m.minFac) * m.minFac = m := Nat.div_mul_cancel (Nat.minFac_dvd m)
    have hcomp : q * m.minFac ≤ (m / m.minFac) * m.minFac := by rw [hmp]; exact hfin
    exact Nat.le_of_mul_le_mul_right hcomp hp.pos

lemma aliquot_eq_sum_properDivisors (n : ℕ) : aliquot n = ∑ d ∈ n.properDivisors, d := by
  simp only [aliquot, sig, ArithmeticFunction.sigma_one_apply,
    Nat.sum_divisors_eq_sum_properDivisors_add_self, Nat.add_sub_cancel]

lemma isRep_aliquot_self {m : ℕ} (hm : 2 ≤ m) : IsRep (aliquot m) m := by
  have hd : m / m.minFac ∈ m.divisors := by
    rw [Nat.mem_divisors]
    exact ⟨Nat.div_dvd_of_dvd (Nat.minFac_dvd m), by omega⟩
  obtain ⟨k, hk1, hk2, hFk⟩ := Fdiv_eq_prefixSumDivisors m (m / m.minFac) hd
  refine ⟨k, hk1, hk2, ?_⟩
  rw [← hFk, Fdiv, divisors_filter_le_eq_properDivisors hm, aliquot_eq_sum_properDivisors]

end Principia.Erdos1054.Proofs.A0Family

namespace Principia.Erdos1054.Proofs

open Finset Principia.Erdos1054 Principia.Erdos1054.Proofs.A0Family

theorem leaf_Eq_SvBasic : Principia.Erdos1054.Eq_SvBasic := by
  intro n hn
  exact ⟨⟨n, by omega, isRep_aliquot_self hn⟩, Nat.sInf_le ⟨by omega, isRep_aliquot_self hn⟩⟩

end Principia.Erdos1054.Proofs

namespace Principia.Erdos1054.Proofs.A0Family

open Finset Principia.Erdos1054

lemma sig_cast (n : ℕ) : (sig n : ℝ) = ∑ d ∈ n.divisors, (d : ℝ) := by
  simp only [sig, ArithmeticFunction.sigma_one_apply, Nat.cast_sum]

lemma sig_mul_le (a b : ℕ) : sig (a * b) ≤ sig a * sig b := by
  simp only [sig, ArithmeticFunction.sigma_one_apply]
  rw [Nat.divisors_mul, Finset.mul_def, Finset.sum_mul_sum]
  calc ∑ u ∈ (a.divisors ×ˢ b.divisors).image (fun p : ℕ × ℕ => p.1 * p.2), u
      ≤ ∑ u ∈ a.divisors ×ˢ b.divisors, u.1 * u.2 :=
        Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)
    _ = ∑ i ∈ a.divisors, ∑ j ∈ b.divisors, i * j := Finset.sum_product _ _ _

lemma abundancy_nonneg (n : ℕ) : 0 ≤ abundancy n := by
  unfold abundancy; positivity

lemma abundancy_mul_le {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    abundancy (a * b) ≤ abundancy a * abundancy b := by
  unfold abundancy
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have h1 : (sig (a * b) : ℝ) ≤ (sig a : ℝ) * sig b := by exact_mod_cast sig_mul_le a b
  rw [div_mul_div_comm, Nat.cast_mul]
  exact div_le_div_of_nonneg_right h1 (by positivity)

lemma abundancy_eq_cast (n : ℕ) : abundancy n = ((n.abundancyIndex : ℚ) : ℝ) := by
  simp [abundancy, Nat.abundancyIndex, sig, ArithmeticFunction.sigma_one_apply]

lemma abundancy_le_of_dvd {m n : ℕ} (hn : n ≠ 0) (h : m ∣ n) : abundancy m ≤ abundancy n := by
  rw [abundancy_eq_cast, abundancy_eq_cast]
  exact_mod_cast Nat.abundancyIndex_le_of_dvd hn h

lemma sig_prime {p : ℕ} (hp : p.Prime) : sig p = p + 1 := by
  simp only [sig, ArithmeticFunction.sigma_one_apply, hp.divisors]
  rw [Finset.sum_pair (Ne.symm hp.one_lt.ne')]
  ring

lemma abundancy_prime {p : ℕ} (hp : p.Prime) : abundancy p = 1 + 1 / (p : ℝ) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  unfold abundancy
  rw [sig_prime hp]
  push_cast
  field_simp

lemma abundancy_prime_le_two {p : ℕ} (hp : p.Prime) : abundancy p ≤ 2 := by
  rw [abundancy_prime hp]
  have : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have h2 : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact this
  linarith

lemma le_sig (n : ℕ) (hn : n ≠ 0) : n ≤ sig n := by
  simp only [sig, ArithmeticFunction.sigma_one_apply]
  exact Finset.single_le_sum (fun i _ => Nat.zero_le i) (Nat.mem_divisors_self n hn)

lemma aliquot_div_eq {t : ℕ} (ht : t ≠ 0) : (aliquot t : ℝ) / t = abundancy t - 1 := by
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  unfold abundancy aliquot
  rw [Nat.cast_sub (le_sig t ht)]
  field_simp

end Principia.Erdos1054.Proofs.A0Family

namespace Principia.Erdos1054.Proofs

open Finset Principia.Erdos1054 Principia.Erdos1054.Proofs.A0Family

theorem leaf_SvA0_abundancySubmul : Principia.Erdos1054.SvA0_abundancySubmul := by
  intro a b ha hb
  exact abundancy_mul_le ha hb

end Principia.Erdos1054.Proofs

namespace Principia.Erdos1054.Proofs.A0Family

open Finset Principia.Erdos1054

lemma sum_inv_sq_le_zeta2 (J : ℕ) :
    ∑ a ∈ Icc 1 J, (1 : ℝ) / (a : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 :=
  sum_le_hasSum (Icc 1 J) (fun _ _ => by positivity) hasSum_zeta_two

lemma one_add_sum_le_prod (s : Finset ℕ) (x : ℕ → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) :
    1 + ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 + x i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hxa : 0 ≤ x a := hx a (Finset.mem_insert_self a s)
    have ih' := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
    have hs : 0 ≤ ∑ i ∈ s, x i :=
      Finset.sum_nonneg (fun i hi => hx i (Finset.mem_insert_of_mem hi))
    have h2 : (1 + x a) * (1 + ∑ i ∈ s, x i) ≤ (1 + x a) * ∏ i ∈ s, (1 + x i) :=
      mul_le_mul_of_nonneg_left ih' (by linarith)
    nlinarith

lemma tendsto_sum_prime_recip :
    Filter.Tendsto (fun n : ℕ => ∑ p ∈ (Finset.range n).filter Nat.Prime, (1 : ℝ) / p)
      Filter.atTop Filter.atTop := by
  have h := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (f := Set.indicator {p | p.Prime} (fun n : ℕ => (1 : ℝ) / n))
    (fun n => Set.indicator_nonneg (fun _ _ => by positivity) n)).1
    not_summable_one_div_on_primes
  refine h.congr (fun n => ?_)
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hp : i.Prime <;> simp [hp]

lemma le_rpow_one_div {c X : ℝ} {n : ℕ} (hn : n ≠ 0) (hX : 0 ≤ X)
    (h : c ^ n ≤ X) : c ≤ X ^ ((1 : ℝ) / n) := by
  have h1 : (X ^ ((1 : ℝ) / n)) ^ n = X := by
    rw [one_div]; exact Real.rpow_inv_natCast_pow hX hn
  have h2 : 0 ≤ X ^ ((1 : ℝ) / n) := Real.rpow_nonneg hX _
  exact le_of_pow_le_pow_left₀ hn h2 (by rw [h1]; exact h)

lemma two_le_rpow_sixth {X : ℝ} (hX : 64 ≤ X) : (2 : ℝ) ≤ X ^ ((1 : ℝ) / 6) := by
  have h := le_rpow_one_div (c := 2) (X := X) (n := 6) (by norm_num)
    (by linarith) (by norm_num; linarith)
  have e : ((6 : ℕ) : ℝ) = 6 := by norm_num
  rw [e] at h
  exact h

end Principia.Erdos1054.Proofs.A0Family

namespace Principia.Erdos1054.Proofs

open Finset Principia.Erdos1054 Principia.Erdos1054.Proofs.A0Family

theorem leaf_SvA0_sigmaHarmonic : Principia.Erdos1054.SvA0_sigmaHarmonic := by
  intro J _
  have h1 : ∀ j ∈ Icc 1 J,
      (sig j : ℝ) / (j : ℝ) ^ 2 = ∑ d ∈ j.divisors, (d : ℝ) / (j : ℝ) ^ 2 := by
    intro j _
    rw [sig_cast, Finset.sum_div]
  rw [Finset.sum_congr rfl h1]
  have hcomm : ∀ (j d : ℕ), j ∈ Icc 1 J ∧ d ∈ j.divisors ↔
      j ∈ (Icc 1 J).filter (d ∣ ·) ∧ d ∈ Icc 1 J := by
    intro j d
    simp only [Finset.mem_Icc, Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hj1, hjJ⟩, hdj, _⟩
      have hdle : d ≤ j := Nat.le_of_dvd (by omega) hdj
      have hd1 : 0 < d := Nat.pos_of_dvd_of_pos hdj (by omega)
      exact ⟨⟨⟨hj1, hjJ⟩, hdj⟩, hd1, by omega⟩
    · rintro ⟨⟨⟨hj1, hjJ⟩, hdj⟩, _, _⟩
      exact ⟨⟨hj1, hjJ⟩, hdj, by omega⟩
  rw [Finset.sum_comm' hcomm]
  have h3 : ∀ d ∈ Icc 1 J, ∑ j ∈ (Icc 1 J).filter (d ∣ ·), (d : ℝ) / (j : ℝ) ^ 2 ≤
      (1 / (d : ℝ)) * ∑ a ∈ Icc 1 J, (1 : ℝ) / (a : ℝ) ^ 2 := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.1 hd).1
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    have hsub : (Icc 1 J).filter (d ∣ ·) ⊆ (Icc 1 J).image (fun a => d * a) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjJ⟩, a, rfl⟩ := hj
      refine Finset.mem_image.2 ⟨a, ?_, rfl⟩
      have ha1 : 1 ≤ a := by
        rcases Nat.eq_zero_or_pos a with h | h
        · subst h; omega
        · exact h
      have : a ≤ d * a := Nat.le_mul_of_pos_left a (by omega)
      exact Finset.mem_Icc.2 ⟨ha1, by omega⟩
    calc ∑ j ∈ (Icc 1 J).filter (d ∣ ·), (d : ℝ) / (j : ℝ) ^ 2
        ≤ ∑ j ∈ (Icc 1 J).image (fun a => d * a), (d : ℝ) / (j : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ ∑ a ∈ Icc 1 J, (d : ℝ) / ((d * a : ℕ) : ℝ) ^ 2 :=
          Finset.sum_image_le_of_nonneg (fun _ _ => by positivity)
      _ = (1 / (d : ℝ)) * ∑ a ∈ Icc 1 J, (1 : ℝ) / (a : ℝ) ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun a ha => ?_)
          have ha0 : (a : ℝ) ≠ 0 := by
            have := (Finset.mem_Icc.1 ha).1
            exact_mod_cast (show a ≠ 0 by omega)
          push_cast
          field_simp
  calc ∑ d ∈ Icc 1 J, ∑ j ∈ (Icc 1 J).filter (d ∣ ·), (d : ℝ) / (j : ℝ) ^ 2
      ≤ ∑ d ∈ Icc 1 J, (1 / (d : ℝ)) * ∑ a ∈ Icc 1 J, (1 : ℝ) / (a : ℝ) ^ 2 :=
        Finset.sum_le_sum h3
    _ = (∑ d ∈ Icc 1 J, 1 / (d : ℝ)) * ∑ a ∈ Icc 1 J, (1 : ℝ) / (a : ℝ) ^ 2 := by
        rw [Finset.sum_mul]
    _ ≤ (∑ d ∈ Icc 1 J, 1 / (d : ℝ)) * (Real.pi ^ 2 / 6) :=
        mul_le_mul_of_nonneg_left (sum_inv_sq_le_zeta2 J)
          (Finset.sum_nonneg (fun _ _ => by positivity))
    _ = Real.pi ^ 2 / 6 * ∑ a ∈ Icc 1 J, (1 : ℝ) / a := mul_comm _ _

theorem leaf_Eq_SvD : Principia.Erdos1054.Eq_SvD := by
  intro δ hδ _
  obtain ⟨n, hn⟩ := (Filter.tendsto_atTop.1 tendsto_sum_prime_recip (1 / δ + 1)).exists
  have hPp : ∀ p ∈ (Finset.range n).filter Nat.Prime, p.Prime :=
    fun p hp => (Finset.mem_filter.1 hp).2
  refine ⟨∏ p ∈ (Finset.range n).filter Nat.Prime, p, ?_, ?_⟩
  · apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro a ha b hb hab
      exact Nat.coprime_iff_isRelPrime.1 ((Nat.coprime_primes (hPp a ha) (hPp b hb)).2 hab)
    · intro p hp
      exact (hPp p hp).prime.squarefree
  · have hsig : sig (∏ p ∈ (Finset.range n).filter Nat.Prime, p) =
        ∏ p ∈ (Finset.range n).filter Nat.Prime, sig p :=
      ArithmeticFunction.isMultiplicative_sigma.map_prod_of_prime _ hPp
    have hab : abundancy (∏ p ∈ (Finset.range n).filter Nat.Prime, p) =
        ∏ p ∈ (Finset.range n).filter Nat.Prime, abundancy p := by
      unfold abundancy
      rw [hsig, Nat.cast_prod, Nat.cast_prod, Finset.prod_div_distrib]
    rw [hab, Finset.prod_congr rfl (fun p hp => abundancy_prime (hPp p hp))]
    have := one_add_sum_le_prod ((Finset.range n).filter Nat.Prime) (fun p => 1 / (p : ℝ))
      (fun _ _ => by positivity)
    linarith

theorem leaf_Lem_SvA0Unique : Principia.Erdos1054.Lem_SvA0Unique := by
  intro δ _ _ D _
  refine ⟨64, fun X hX => ?_⟩
  intro p q r k p' q' r' k' h h' heq
  have hX1 : (1 : ℝ) < X := by linarith
  have hX0 : (0 : ℝ) < X := by linarith
  obtain ⟨hp, hq, hr, -, hk1, hk2, hr1, hr2, hq1, hq2, hp1, hp2⟩ := h
  obtain ⟨hp', hq', hr', -, hk1', hk2', hr1', hr2', hq1', hq2', hp1', hp2'⟩ := h'
  have e1 : X ^ ((1 : ℝ) / 60) < X ^ ((1 : ℝ) / 15) :=
    Real.rpow_lt_rpow_of_exponent_lt hX1 (by norm_num)
  have e2 : X ^ ((1 : ℝ) / 12) < X ^ ((7 : ℝ) / 20) :=
    Real.rpow_lt_rpow_of_exponent_lt hX1 (by norm_num)
  have e3 : X ^ ((1 : ℝ) / 60) < X ^ ((7 : ℝ) / 20) :=
    Real.rpow_lt_rpow_of_exponent_lt hX1 (by norm_num)
  have e4 : X ^ ((1 : ℝ) / 12) < X ^ ((11 : ℝ) / 30) :=
    Real.rpow_lt_rpow_of_exponent_lt hX1 (by norm_num)
  have e5 : X ^ ((1 : ℝ) / 60) < X ^ ((11 : ℝ) / 30) :=
    Real.rpow_lt_rpow_of_exponent_lt hX1 (by norm_num)
  have hk'0 : 0 < k' := by
    have : (0 : ℝ) < k' := lt_of_le_of_lt (Real.rpow_nonneg hX0.le _) hk1'
    exact_mod_cast this
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr.pos
  have hkR : (0 : ℝ) < k := lt_of_le_of_lt (Real.rpow_nonneg hX0.le _) hk1
  have hpbig : X ^ ((11 : ℝ) / 30) < (p : ℝ) := by
    by_contra hcon
    rw [not_lt] at hcon
    have h1 : X < 2 * p * q * r * k := by
      rw [div_lt_iff₀ (by positivity)] at hp1
      linarith
    have h2 : 2 * (p : ℝ) * q * r * k ≤ 2 * X ^ ((11 : ℝ) / 30) * X ^ ((11 : ℝ) / 30) *
        X ^ ((1 : ℝ) / 12) * X ^ ((1 : ℝ) / 60) := by
      gcongr
    have h3 : 2 * X ^ ((11 : ℝ) / 30) * X ^ ((11 : ℝ) / 30) * X ^ ((1 : ℝ) / 12) *
        X ^ ((1 : ℝ) / 60) = 2 * X ^ ((5 : ℝ) / 6) := by
      rw [mul_assoc 2, mul_assoc 2, mul_assoc 2, ← Real.rpow_add hX0, ← Real.rpow_add hX0,
        ← Real.rpow_add hX0]
      norm_num
    have h4 : X = X ^ ((5 : ℝ) / 6) * X ^ ((1 : ℝ) / 6) := by
      rw [← Real.rpow_add hX0]; norm_num
    have h5 : (2 : ℝ) ≤ X ^ ((1 : ℝ) / 6) := two_le_rpow_sixth hX
    have h6 : 0 < X ^ ((5 : ℝ) / 6) := Real.rpow_pos_of_pos hX0 _
    nlinarith
  -- p = p'
  have hpdvd : p ∣ p' * q' * r' * k' := by rw [← heq]; exact ⟨q * r * k, by ring⟩
  have hpp' : p = p' := by
    rcases (Nat.Prime.dvd_mul hp).1 hpdvd with h1 | h1
    · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
      · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
        · exact (Nat.prime_dvd_prime_iff_eq hp hp').1 h3
        · exfalso
          have h4 : (p : ℝ) ≤ q' := by exact_mod_cast Nat.le_of_dvd hq'.pos h3
          linarith
      · exfalso
        have h4 : (p : ℝ) ≤ r' := by exact_mod_cast Nat.le_of_dvd hr'.pos h2
        linarith
    · exfalso
      have h4 : (p : ℝ) ≤ k' := by exact_mod_cast Nat.le_of_dvd hk'0 h1
      linarith
  subst hpp'
  have hqrk : q * r * k = q' * r' * k' := by
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    calc p * (q * r * k) = p * q * r * k := by ring
      _ = p * q' * r' * k' := heq
      _ = p * (q' * r' * k') := by ring
  have hqdvd : q ∣ q' * r' * k' := by rw [← hqrk]; exact ⟨r * k, by ring⟩
  have hqq' : q = q' := by
    rcases (Nat.Prime.dvd_mul hq).1 hqdvd with h1 | h1
    · rcases (Nat.Prime.dvd_mul hq).1 h1 with h2 | h2
      · exact (Nat.prime_dvd_prime_iff_eq hq hq').1 h2
      · exfalso
        have h4 : (q : ℝ) ≤ r' := by exact_mod_cast Nat.le_of_dvd hr'.pos h2
        linarith
    · exfalso
      have h4 : (q : ℝ) ≤ k' := by exact_mod_cast Nat.le_of_dvd hk'0 h1
      linarith
  subst hqq'
  have hrk : r * k = r' * k' := by
    apply Nat.eq_of_mul_eq_mul_left hq.pos
    calc q * (r * k) = q * r * k := by ring
      _ = q * r' * k' := hqrk
      _ = q * (r' * k') := by ring
  have hrdvd : r ∣ r' * k' := by rw [← hrk]; exact ⟨k, rfl⟩
  have hrr' : r = r' := by
    rcases (Nat.Prime.dvd_mul hr).1 hrdvd with h1 | h1
    · exact (Nat.prime_dvd_prime_iff_eq hr hr').1 h1
    · exfalso
      have h4 : (r : ℝ) ≤ k' := by exact_mod_cast Nat.le_of_dvd hk'0 h1
      linarith
  subst hrr'
  have hkk' : k = k' := Nat.eq_of_mul_eq_mul_left hr.pos hrk
  exact ⟨rfl, rfl, rfl, hkk'⟩

theorem leaf_Lem_SvA0QLarge : Principia.Erdos1054.Lem_SvA0QLarge := by
  intro δ _ _ D _
  refine ⟨1, fun X hX => ?_⟩
  intro p q r k h
  have hX0 : 0 < X := by linarith
  obtain ⟨hp, hq, hr, -, hk1, hk2, hr1, hr2, hq1, hq2, hp1, hp2⟩ := h
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hl : ((r : ℝ) * k) ≤ X ^ ((1 : ℝ) / 10) := by
    have e : X ^ ((1 : ℝ) / 12) * X ^ ((1 : ℝ) / 60) = X ^ ((1 : ℝ) / 10) := by
      rw [← Real.rpow_add hX0]; norm_num
    rw [← e]
    exact mul_le_mul hr2 hk2 (by positivity) (Real.rpow_nonneg hX0.le _)
  have hl7 : ((r : ℝ) * k) ^ 7 ≤ X ^ ((7 : ℝ) / 10) := by
    have e : X ^ ((7 : ℝ) / 10) = (X ^ ((1 : ℝ) / 10)) ^ 7 := by
      rw [← Real.rpow_mul_natCast hX0.le]; norm_num
    rw [e]
    exact pow_le_pow_left₀ (by positivity) hl 7
  have hq2' : X ^ ((7 : ℝ) / 10) < (q : ℝ) ^ 2 := by
    have e : X ^ ((7 : ℝ) / 10) = (X ^ ((7 : ℝ) / 20)) ^ 2 := by
      rw [← Real.rpow_mul_natCast hX0.le]; norm_num
    rw [e]
    exact pow_lt_pow_left₀ hq1 (Real.rpow_nonneg hX0.le _) (by norm_num)
  have hn' : ((q * r * k : ℕ) : ℝ) = q * (r * k) := by push_cast; ring
  have hn0 : (0 : ℝ) ≤ ((q * r * k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hn7 : ((q * r * k : ℕ) : ℝ) ^ 7 < (q : ℝ) ^ 9 := by
    rw [hn']
    calc ((q : ℝ) * (r * k)) ^ 7 = (q : ℝ) ^ 7 * ((r : ℝ) * k) ^ 7 := mul_pow _ _ _
      _ ≤ (q : ℝ) ^ 7 * X ^ ((7 : ℝ) / 10) := mul_le_mul_of_nonneg_left hl7 (by positivity)
      _ < (q : ℝ) ^ 7 * (q : ℝ) ^ 2 := mul_lt_mul_of_pos_left hq2' (by positivity)
      _ = (q : ℝ) ^ 9 := by ring
  by_contra hcon
  rw [not_lt] at hcon
  have h9 : (q : ℝ) ^ 9 ≤ (((q * r * k : ℕ) : ℝ) ^ ((7 : ℝ) / 9)) ^ 9 :=
    pow_le_pow_left₀ hq0.le hcon 9
  rw [← Real.rpow_mul_natCast hn0] at h9
  have e : (7 / 9 : ℝ) * ((9 : ℕ) : ℝ) = ((7 : ℕ) : ℝ) := by norm_num
  rw [e, Real.rpow_natCast] at h9
  linarith

theorem link_Eq_SvTwoSided : Principia.Erdos1054.Spine.Link_Eq_SvTwoSided := by
  intro hsub δ hδ _ D hD
  obtain ⟨hDsq, hDab⟩ := hD
  have hD0 : D ≠ 0 := hDsq.ne_zero
  have hD1 : 1 ≤ D := Nat.one_le_iff_ne_zero.2 hD0
  have hZ : (0 : ℝ) < 4 * (Real.pi ^ 2 / 6) := by positivity
  have hδinv : (0 : ℝ) < 1 / δ := by positivity
  have hDab0 : 0 < abundancy D := by linarith
  refine ⟨8 * (abundancy D * (4 * (Real.pi ^ 2 / 6))), by positivity, 0, fun X hX => ?_⟩
  intro p q r k h t ht
  obtain ⟨hp, hq, hr, ⟨j, hkj, hj⟩, hk1, -, -, -, -, -, -, -⟩ := h
  have hk0 : 0 < k := by
    have : (0 : ℝ) < k := lt_of_le_of_lt (Real.rpow_nonneg hX _) hk1
    exact_mod_cast this
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0; rw [Nat.mul_zero] at hkj; omega
    · exact h0
  have habk : abundancy k ≤ abundancy D * (4 * (Real.pi ^ 2 / 6)) := by
    rw [hkj]
    calc abundancy (D * j) ≤ abundancy D * abundancy j := hsub D j hD1 hj1
      _ ≤ abundancy D * (4 * (Real.pi ^ 2 / 6)) :=
          mul_le_mul_of_nonneg_left hj (abundancy_nonneg D)
  have hAZ : 0 ≤ abundancy D * (4 * (Real.pi ^ 2 / 6)) := by positivity
  have hpa := abundancy_prime_le_two hp
  have hqa := abundancy_prime_le_two hq
  have hra := abundancy_prime_le_two hr
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hq1 : 1 ≤ q := hq.one_lt.le
  have hr1 : 1 ≤ r := hr.one_lt.le
  have hqr : abundancy (q * r) ≤ 4 := by
    calc abundancy (q * r) ≤ abundancy q * abundancy r := hsub q r hq1 hr1
      _ ≤ 2 * 2 := mul_le_mul hqa hra (abundancy_nonneg r) (by norm_num)
      _ = 4 := by norm_num
  have hpq : abundancy (p * q) ≤ 4 := by
    calc abundancy (p * q) ≤ abundancy p * abundancy q := hsub p q hp1 hq1
      _ ≤ 2 * 2 := mul_le_mul hpa hqa (abundancy_nonneg q) (by norm_num)
      _ = 4 := by norm_num
  have hpqr : abundancy (p * q * r) ≤ 8 := by
    calc abundancy (p * q * r) ≤ abundancy (p * q) * abundancy r :=
          hsub (p * q) r (Nat.mul_pos hp1 hq1) hr1
      _ ≤ 4 * 2 := mul_le_mul hpq hra (abundancy_nonneg r) (by norm_num)
      _ = 8 := by norm_num
  have key : 1 ≤ t ∧ D ∣ t ∧ abundancy t ≤ 8 * (abundancy D * (4 * (Real.pi ^ 2 / 6))) := by
    have hDk : D ∣ k := ⟨j, hkj⟩
    rcases ht with rfl | rfl | rfl | rfl
    · exact ⟨hk0, hDk, by linarith⟩
    · refine ⟨Nat.mul_pos hr1 hk0, Dvd.dvd.mul_left hDk r, ?_⟩
      calc abundancy (r * k) ≤ abundancy r * abundancy k := hsub r k hr1 hk0
        _ ≤ 2 * (abundancy D * (4 * (Real.pi ^ 2 / 6))) :=
            mul_le_mul hra habk (abundancy_nonneg k) (by norm_num)
        _ ≤ 8 * (abundancy D * (4 * (Real.pi ^ 2 / 6))) := by linarith
    · refine ⟨Nat.mul_pos (Nat.mul_pos hq1 hr1) hk0, Dvd.dvd.mul_left hDk (q * r), ?_⟩
      calc abundancy (q * r * k) ≤ abundancy (q * r) * abundancy k :=
            hsub (q * r) k (Nat.mul_pos hq1 hr1) hk0
        _ ≤ 4 * (abundancy D * (4 * (Real.pi ^ 2 / 6))) :=
            mul_le_mul hqr habk (abundancy_nonneg k) (by norm_num)
        _ ≤ 8 * (abundancy D * (4 * (Real.pi ^ 2 / 6))) := by linarith
    · refine ⟨Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp1 hq1) hr1) hk0,
        Dvd.dvd.mul_left hDk (p * q * r), ?_⟩
      calc abundancy (p * q * r * k) ≤ abundancy (p * q * r) * abundancy k :=
            hsub (p * q * r) k (Nat.mul_pos (Nat.mul_pos hp1 hq1) hr1) hk0
        _ ≤ 8 * (abundancy D * (4 * (Real.pi ^ 2 / 6))) :=
            mul_le_mul hpqr habk (abundancy_nonneg k) (by norm_num)
  obtain ⟨ht1, hDt, htab⟩ := key
  have ht0 : t ≠ 0 := by omega
  have hmono : abundancy D ≤ abundancy t := abundancy_le_of_dvd ht0 hDt
  rw [aliquot_div_eq ht0]
  constructor
  · linarith
  · linarith

end Principia.Erdos1054.Proofs

namespace Principia.Erdos1054.Proofs.A0Family

open Finset Principia.Erdos1054

lemma sum_Icc_one_div_eq_harmonic (n : ℕ) :
    ∑ j ∈ Icc 1 n, (1 : ℝ) / j = (harmonic n : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  exact Finset.sum_congr rfl (fun _ _ => one_div _)

/-- The inclusion–exclusion step of `SvA0_jSum` (EP1054.tex lines 1268–1271), for an arbitrary
`G ⊆ [1, J₂]` whose complement consists of `j ≤ m` or `σ(j)/j > Z`. -/
lemma jsum_core (J2 m : ℕ) (Z : ℝ) (hZ : 0 < Z) (G : Finset ℕ) (hGsub : G ⊆ Icc 1 J2)
    (hG : ∀ j ∈ Icc 1 J2, j ∉ G → j ≤ m ∨ Z < abundancy j) :
    ∑ j ∈ Icc 1 J2, (1 : ℝ) / j - ∑ j ∈ Icc 1 m, (1 : ℝ) / j
      - (1 / Z) * ∑ j ∈ Icc 1 J2, (sig j : ℝ) / (j : ℝ) ^ 2 ≤ ∑ j ∈ G, (1 : ℝ) / j := by
  have hsplit : ∑ j ∈ Icc 1 J2 \ G, (1 : ℝ) / j + ∑ j ∈ G, (1 : ℝ) / j =
      ∑ j ∈ Icc 1 J2, (1 : ℝ) / j :=
    Finset.sum_sdiff hGsub
  have hbad : ∑ j ∈ Icc 1 J2 \ G, (1 : ℝ) / j ≤
      ∑ j ∈ Icc 1 J2 \ G, ((if j ≤ m then (1 : ℝ) / j else 0) +
        (1 / Z) * ((sig j : ℝ) / (j : ℝ) ^ 2)) := by
    apply Finset.sum_le_sum
    intro j hj
    rw [Finset.mem_sdiff] at hj
    have hnn : 0 ≤ (1 / Z) * ((sig j : ℝ) / (j : ℝ) ^ 2) := by positivity
    have hinv : 0 ≤ (1 : ℝ) / j := by positivity
    rcases hG j hj.1 hj.2 with h | h
    · rw [if_pos h]; linarith
    · have e : (1 / Z) * ((sig j : ℝ) / (j : ℝ) ^ 2) = (abundancy j / Z) * (1 / j) := by
        unfold abundancy; ring
      have h1 : 1 ≤ abundancy j / Z := by rw [le_div_iff₀ hZ]; linarith
      have h2 : (1 : ℝ) / j ≤ (1 / Z) * ((sig j : ℝ) / (j : ℝ) ^ 2) := by
        rw [e]; exact le_mul_of_one_le_left hinv h1
      split_ifs <;> linarith
  have hext : ∑ j ∈ Icc 1 J2 \ G, ((if j ≤ m then (1 : ℝ) / j else 0) +
        (1 / Z) * ((sig j : ℝ) / (j : ℝ) ^ 2)) ≤
      ∑ j ∈ Icc 1 J2, ((if j ≤ m then (1 : ℝ) / j else 0) +
        (1 / Z) * ((sig j : ℝ) / (j : ℝ) ^ 2)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
    intro j _ _
    have : 0 ≤ (1 / Z) * ((sig j : ℝ) / (j : ℝ) ^ 2) := by positivity
    have : (0 : ℝ) ≤ 1 / j := by positivity
    split_ifs <;> linarith
  have hsplit2 : ∑ j ∈ Icc 1 J2, ((if j ≤ m then (1 : ℝ) / j else 0) +
        (1 / Z) * ((sig j : ℝ) / (j : ℝ) ^ 2)) =
      ∑ j ∈ (Icc 1 J2).filter (· ≤ m), (1 : ℝ) / j +
        (1 / Z) * ∑ j ∈ Icc 1 J2, (sig j : ℝ) / (j : ℝ) ^ 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_filter, Finset.mul_sum]
  have hsmall : ∑ j ∈ (Icc 1 J2).filter (· ≤ m), (1 : ℝ) / j ≤ ∑ j ∈ Icc 1 m, (1 : ℝ) / j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
      omega
    · intro j _ _; positivity
  linarith

/-- Mertens' second theorem over a power window: `∑_{X^a < p ≤ X^b} 1/p ≥ ½ log(b/a)` for large
`X` (EP1054.tex lines 1275–1283). -/
lemma mertens_window (hM : Principia.Erdos1054.Std_Mertens2) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      (1 / 2) * Real.log (b / a) ≤
        ∑ p ∈ (Finset.Iic ⌊X ^ b⌋₊).filter Nat.Prime \ (Finset.Iic ⌊X ^ a⌋₊).filter Nat.Prime,
          (1 : ℝ) / p := by
  obtain ⟨M, C, hC⟩ := hM
  have hb : 0 < b := lt_trans ha hab
  have hL : 0 < Real.log (b / a) := Real.log_pos (by rw [one_lt_div ha]; exact hab)
  have hC4 : 0 ≤ 4 * |C| / (a * Real.log (b / a)) := by positivity
  have hl2 : 0 ≤ Real.log 2 / a := by positivity
  refine ⟨Real.exp (max (4 * |C| / (a * Real.log (b / a))) (Real.log 2 / a) + 1),
    fun X hX => ?_⟩
  have hm1 := le_max_left (4 * |C| / (a * Real.log (b / a))) (Real.log 2 / a)
  have hm2 := le_max_right (4 * |C| / (a * Real.log (b / a))) (Real.log 2 / a)
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hu : max (4 * |C| / (a * Real.log (b / a))) (Real.log 2 / a) + 1 ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos _) hX
    rwa [Real.log_exp] at h
  have hu0 : 0 < Real.log X := by linarith
  have hlogXa : Real.log (X ^ a) = a * Real.log X := Real.log_rpow hXpos a
  have hlogXb : Real.log (X ^ b) = b * Real.log X := Real.log_rpow hXpos b
  have hXa2 : 2 ≤ X ^ a := by
    have h1 : Real.log 2 ≤ a * Real.log X := by
      have : Real.log 2 / a ≤ Real.log X := by linarith
      rwa [div_le_iff₀ ha, mul_comm] at this
    have h2 : Real.log 2 ≤ Real.log (X ^ a) := by rw [hlogXa]; exact h1
    exact (Real.log_le_log_iff (by norm_num) (Real.rpow_pos_of_pos hXpos a)).1 h2
  have hX1 : 1 ≤ X := by
    have : (1 : ℝ) ≤ Real.exp (max (4 * |C| / (a * Real.log (b / a))) (Real.log 2 / a) + 1) :=
      Real.one_le_exp (by linarith)
    linarith
  have hXab : X ^ a ≤ X ^ b := Real.rpow_le_rpow_of_exponent_le hX1 hab.le
  have hXb2 : 2 ≤ X ^ b := le_trans hXa2 hXab
  have hsub : (Finset.Iic ⌊X ^ a⌋₊).filter Nat.Prime ⊆ (Finset.Iic ⌊X ^ b⌋₊).filter Nat.Prime :=
    Finset.filter_subset_filter _ (Finset.Iic_subset_Iic.2 (Nat.floor_mono hXab))
  rw [Finset.sum_sdiff_eq_sub hsub]
  obtain ⟨hA1, hA2⟩ := abs_le.1 (hC (X ^ a) hXa2)
  obtain ⟨hB1, hB2⟩ := abs_le.1 (hC (X ^ b) hXb2)
  rw [hlogXa, Real.log_mul ha.ne' hu0.ne'] at hA1 hA2
  rw [hlogXb, Real.log_mul hb.ne' hu0.ne'] at hB1 hB2
  have hdiv : Real.log (b / a) = Real.log b - Real.log a := Real.log_div hb.ne' ha.ne'
  have hau : 0 < a * Real.log X := mul_pos ha hu0
  have hbu : 0 < b * Real.log X := mul_pos hb hu0
  have e1 : C / (a * Real.log X) ≤ |C| / (a * Real.log X) :=
    div_le_div_of_nonneg_right (le_abs_self C) hau.le
  have e2 : C / (b * Real.log X) ≤ |C| / (a * Real.log X) := by
    calc C / (b * Real.log X) ≤ |C| / (b * Real.log X) :=
          div_le_div_of_nonneg_right (le_abs_self C) hbu.le
      _ ≤ |C| / (a * Real.log X) :=
          div_le_div_of_nonneg_left (abs_nonneg C) hau
            (mul_le_mul_of_nonneg_right hab.le hu0.le)
  have e3 : |C| / (a * Real.log X) ≤ Real.log (b / a) / 4 := by
    rw [div_le_iff₀ hau]
    have h1 : 4 * |C| / (a * Real.log (b / a)) ≤ Real.log X := by linarith
    rw [div_le_iff₀ (by positivity)] at h1
    nlinarith
  linarith

lemma triple_sum (J R Q : Finset ℕ) (a b c : ℕ → ℝ) :
    ∑ x ∈ (J ×ˢ R) ×ˢ Q, a x.1.1 * b x.1.2 * c x.2 =
      (∑ j ∈ J, a j) * (∑ r ∈ R, b r) * (∑ q ∈ Q, c q) := by
  rw [Finset.sum_product, Finset.sum_product, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  show ∑ q ∈ Q, a j * b r * c q = a j * b r * ∑ q ∈ Q, c q
  rw [Finset.mul_sum]

/-- For a triple `x = ((j, r), q)`, the parameter `t = X/(2 q r k)` with `k = D j`: the primes
`p` of the family are those in `(t, 2t]` (EP1054.tex line 1274, `T = 2t`). -/
noncomputable def ttf (D : ℕ) (X : ℝ) (x : (ℕ × ℕ) × ℕ) : ℝ :=
  X / (2 * (x.2 : ℝ) * x.1.2 * ((D * x.1.1 : ℕ) : ℝ))

/-- The primes `p ∈ (t, 2t]` for the triple `x`. -/
noncomputable def PsetF (D : ℕ) (X : ℝ) (x : (ℕ × ℕ) × ℕ) : Finset ℕ :=
  Nat.primesLE ⌊2 * ttf D X x⌋₊ \ Nat.primesLE ⌊ttf D X x⌋₊

/-- The counting core of `Lem_SvA0Count` (EP1054.tex lines 1274–1283): an injection of the
tuples `(p, q, r, D j)` into `𝒜₀(X)`, with the prime count in each fibre bounded below by the
dyadic prime input and the three reciprocal sums bounded below by the hypotheses. -/
lemma count_core {D : ℕ} (hD : 1 ≤ D) {X : ℝ} (hX : 16 ≤ X) {c₀ L1 L2 : ℝ} (hc₀ : 0 < c₀)
    (hL1 : 0 ≤ L1) (hL2 : 0 ≤ L2)
    (hdy : ∀ t : ℝ, 2 ≤ t →
      c₀ * t / Real.log t ≤ (Nat.primeCounting ⌊2 * t⌋₊ : ℝ) - (Nat.primeCounting ⌊t⌋₊ : ℝ))
    {Jg Rg Qg : Finset ℕ}
    (hJsum : ((1 : ℝ) / 240 - 1 / 480) * Real.log X ≤ ∑ j ∈ Jg, (1 : ℝ) / j)
    (hRsum : 1 / 2 * L1 ≤ ∑ r ∈ Rg, (1 : ℝ) / r)
    (hQsum : 1 / 2 * L2 ≤ ∑ q ∈ Qg, (1 : ℝ) / q)
    (hJ : ∀ j ∈ Jg, 1 ≤ j ∧ X ^ ((1 : ℝ) / 120) < (D : ℝ) * j ∧ (D : ℝ) * j ≤ X ^ ((1 : ℝ) / 60) ∧
      abundancy j ≤ 4 * (Real.pi ^ 2 / 6))
    (hR : ∀ r ∈ Rg, r.Prime ∧ X ^ ((1 : ℝ) / 15) < (r : ℝ) ∧ (r : ℝ) ≤ X ^ ((1 : ℝ) / 12))
    (hQ : ∀ q ∈ Qg, q.Prime ∧ X ^ ((7 : ℝ) / 20) < (q : ℝ) ∧ (q : ℝ) ≤ X ^ ((11 : ℝ) / 30))
    (hU : ∀ p q r k p' q' r' k' : ℕ, S4a.A0Tuple D X p q r k → S4a.A0Tuple D X p' q' r' k' →
      p * q * r * k = p' * q' * r' * k' → p = p' ∧ q = q' ∧ r = r' ∧ k = k') :
    c₀ * L1 * L2 / (3840 * D) * X ≤ ((S4a.A0 D X).card : ℝ) := by
  have hX1 : (1 : ℝ) < X := by linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos hX1
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hX815 : 4 ≤ X ^ ((8 : ℝ) / 15) := by
    have h1 := le_rpow_one_div (c := 4) (X := X) (n := 2) (by norm_num) hX0.le
      (by norm_num; linarith)
    rw [show ((2 : ℕ) : ℝ) = 2 by norm_num] at h1
    exact le_trans h1 (Real.rpow_le_rpow_of_exponent_le hX1.le (by norm_num))
  have hsplitX : X = X ^ ((7 : ℝ) / 15) * X ^ ((8 : ℝ) / 15) := by
    rw [← Real.rpow_add hX0]; norm_num
  have hprod : X ^ ((11 : ℝ) / 30) * X ^ ((1 : ℝ) / 12) * X ^ ((1 : ℝ) / 60) =
      X ^ ((7 : ℝ) / 15) := by
    rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]; norm_num
  have hmul := mul_le_mul_of_nonneg_right hX815 (Real.rpow_nonneg hX0.le ((7 : ℝ) / 15))
  -- `t` lies in `[2, X]` for every triple
  have htt : ∀ x ∈ (Jg ×ˢ Rg) ×ˢ Qg, 2 ≤ ttf D X x ∧ ttf D X x ≤ X := by
    intro x hx
    rw [Finset.mem_product, Finset.mem_product] at hx
    obtain ⟨⟨hj, hr⟩, hq⟩ := hx
    obtain ⟨hj1, hjA, hjB, -⟩ := hJ _ hj
    obtain ⟨hrp, -, hr2⟩ := hR _ hr
    obtain ⟨hqp, -, hq2⟩ := hQ _ hq
    have hk : ((D * x.1.1 : ℕ) : ℝ) = (D : ℝ) * x.1.1 := by push_cast; ring
    have hq0 : (2 : ℝ) ≤ x.2 := by exact_mod_cast hqp.two_le
    have hr0 : (2 : ℝ) ≤ x.1.2 := by exact_mod_cast hrp.two_le
    have hk0 : (0 : ℝ) < (D : ℝ) * x.1.1 := lt_of_le_of_lt (Real.rpow_nonneg hX0.le _) hjA
    have hk1 : (1 : ℝ) ≤ (D : ℝ) * x.1.1 := by
      have : (1 : ℝ) ≤ ((D * x.1.1 : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hD hj1
      linarith
    have hY : (x.2 : ℝ) * x.1.2 * ((D : ℝ) * x.1.1) ≤ X ^ ((7 : ℝ) / 15) := by
      rw [← hprod]
      exact mul_le_mul (mul_le_mul hq2 hr2 (by linarith) (Real.rpow_nonneg hX0.le _)) hjB
        hk0.le (by positivity)
    have hY1 : (1 : ℝ) ≤ (x.2 : ℝ) * x.1.2 * ((D : ℝ) * x.1.1) :=
      one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)) hk1
    unfold ttf
    rw [hk]
    constructor
    · rw [le_div_iff₀ (by linarith)]
      linarith
    · exact div_le_self hX0.le (by linarith)
  -- every (triple, prime) is a valid tuple of `𝒜₀(X)`
  have hvalid : ∀ x ∈ (Jg ×ˢ Rg) ×ˢ Qg, ∀ p ∈ PsetF D X x,
      S4a.A0Tuple D X p x.2 x.1.2 (D * x.1.1) := by
    intro x hx p hp
    obtain ⟨h2, -⟩ := htt x hx
    rw [Finset.mem_product, Finset.mem_product] at hx
    obtain ⟨⟨hj, hr⟩, hq⟩ := hx
    obtain ⟨-, hjA, hjB, hjab⟩ := hJ _ hj
    obtain ⟨hrp, hr1, hr2⟩ := hR _ hr
    obtain ⟨hqp, hq1, hq2⟩ := hQ _ hq
    unfold PsetF at hp
    rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE] at hp
    obtain ⟨⟨hp2, hpp⟩, hpn⟩ := hp
    have hpt : ttf D X x < p := by
      have : ⌊ttf D X x⌋₊ < p := by
        by_contra hc
        exact hpn ⟨not_lt.1 hc, hpp⟩
      exact (Nat.floor_lt (by linarith)).1 this
    have hp2' : (p : ℝ) ≤ 2 * ttf D X x := (Nat.le_floor_iff (by linarith)).1 hp2
    have hk : ((D * x.1.1 : ℕ) : ℝ) = (D : ℝ) * x.1.1 := by push_cast; ring
    have e : 2 * ttf D X x = X / ((x.2 : ℝ) * x.1.2 * ((D * x.1.1 : ℕ) : ℝ)) := by
      unfold ttf; ring
    refine ⟨hpp, hqp, hrp, ⟨x.1.1, rfl, hjab⟩, ?_, ?_, hr1, hr2, hq1, hq2, hpt, ?_⟩
    · rw [hk]; exact hjA
    · rw [hk]; exact hjB
    · rw [← e]; exact hp2'
  -- the fibre count
  have hcardP : ∀ x ∈ (Jg ×ˢ Rg) ×ˢ Qg,
      c₀ * X / (2 * D) * (1 / Real.log X) *
          ((1 / (x.1.1 : ℝ)) * (1 / (x.1.2 : ℝ)) * (1 / (x.2 : ℝ))) ≤
        ((PsetF D X x).card : ℝ) := by
    intro x hx
    obtain ⟨h2, hle⟩ := htt x hx
    have hsub : Nat.primesLE ⌊ttf D X x⌋₊ ⊆ Nat.primesLE ⌊2 * ttf D X x⌋₊ := by
      intro p hp
      rw [Nat.mem_primesLE] at hp ⊢
      exact ⟨le_trans hp.1 (Nat.floor_mono (by linarith)), hp.2⟩
    have hcard : ((PsetF D X x).card : ℝ) =
        (Nat.primeCounting ⌊2 * ttf D X x⌋₊ : ℝ) - (Nat.primeCounting ⌊ttf D X x⌋₊ : ℝ) := by
      have h := Finset.card_sdiff_add_card_eq_card hsub
      rw [Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting] at h
      have h' : ((PsetF D X x).card : ℝ) + (Nat.primeCounting ⌊ttf D X x⌋₊ : ℝ) =
          (Nat.primeCounting ⌊2 * ttf D X x⌋₊ : ℝ) := by
        unfold PsetF; exact_mod_cast h
      linarith
    have hlogt : 0 < Real.log (ttf D X x) := Real.log_pos (by linarith)
    have hlogt' : Real.log (ttf D X x) ≤ Real.log X := Real.log_le_log (by linarith) hle
    have h1 := hdy (ttf D X x) h2
    have h3 : c₀ * ttf D X x / Real.log X ≤ c₀ * ttf D X x / Real.log (ttf D X x) :=
      div_le_div_of_nonneg_left (mul_nonneg hc₀.le (by linarith)) hlogt hlogt'
    have h4 : c₀ * X / (2 * D) * (1 / Real.log X) *
        ((1 / (x.1.1 : ℝ)) * (1 / (x.1.2 : ℝ)) * (1 / (x.2 : ℝ))) =
        c₀ * ttf D X x / Real.log X := by
      unfold ttf; push_cast; ring
    rw [h4, hcard]
    linarith
  -- the injection into `𝒜₀(X)`
  have hmaps : Set.MapsTo
      (fun y : (Σ _ : (ℕ × ℕ) × ℕ, ℕ) => y.2 * y.1.2 * y.1.1.2 * (D * y.1.1.1))
      ↑(((Jg ×ˢ Rg) ×ˢ Qg).sigma (PsetF D X)) ↑(S4a.A0 D X) := by
    intro y hy
    rw [Finset.mem_coe, Finset.mem_sigma] at hy
    have hv := hvalid y.1 hy.1 y.2 hy.2
    show y.2 * y.1.2 * y.1.1.2 * (D * y.1.1.1) ∈ S4a.A0 D X
    classical
    unfold S4a.A0
    rw [Finset.mem_filter]
    refine ⟨?_, y.2, y.1.2, y.1.1.2, D * y.1.1.1, hv, rfl⟩
    obtain ⟨hpp, hqp, hrp, -, hk1, -, -, -, -, -, -, hp2⟩ := hv
    have hk0 : 0 < D * y.1.1.1 := by
      have : (0 : ℝ) < ((D * y.1.1.1 : ℕ) : ℝ) :=
        lt_of_le_of_lt (Real.rpow_nonneg hX0.le _) hk1
      exact_mod_cast this
    have hqrk : (0 : ℝ) < (y.1.2 : ℝ) * y.1.1.2 * ((D * y.1.1.1 : ℕ) : ℝ) := by
      have : 0 < y.1.2 * y.1.1.2 * (D * y.1.1.1) :=
        Nat.mul_pos (Nat.mul_pos hqp.pos hrp.pos) hk0
      exact_mod_cast this
    rw [le_div_iff₀ hqrk] at hp2
    rw [Finset.mem_Icc]
    refine ⟨Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hpp.pos hqp.pos) hrp.pos) hk0, ?_⟩
    apply Nat.le_floor
    have e : (((y.2 * y.1.2 * y.1.1.2 * (D * y.1.1.1)) : ℕ) : ℝ) =
        (y.2 : ℝ) * ((y.1.2 : ℝ) * y.1.1.2 * ((D * y.1.1.1 : ℕ) : ℝ)) := by
      push_cast; ring
    rw [e]
    exact hp2
  have hinj : Set.InjOn
      (fun y : (Σ _ : (ℕ × ℕ) × ℕ, ℕ) => y.2 * y.1.2 * y.1.1.2 * (D * y.1.1.1))
      ↑(((Jg ×ˢ Rg) ×ˢ Qg).sigma (PsetF D X)) := by
    rintro ⟨⟨⟨j, r⟩, q⟩, p⟩ h1 ⟨⟨⟨j', r'⟩, q'⟩, p'⟩ h2 hf
    rw [Finset.mem_coe, Finset.mem_sigma] at h1 h2
    have hv1 := hvalid _ h1.1 _ h1.2
    have hv2 := hvalid _ h2.1 _ h2.2
    obtain ⟨e1, e2, e3, e4⟩ := hU _ _ _ _ _ _ _ _ hv1 hv2 hf
    change p = p' at e1
    change q = q' at e2
    change r = r' at e3
    change D * j = D * j' at e4
    have e5 : j = j' := Nat.eq_of_mul_eq_mul_left hD e4
    subst e1 e2 e3 e5
    rfl
  have hS := Finset.card_le_card_of_injOn _ hmaps hinj
  -- the reciprocal sums
  have hSJ0 : 0 ≤ ∑ j ∈ Jg, (1 : ℝ) / j := Finset.sum_nonneg (fun _ _ => by positivity)
  have hSR0 : 0 ≤ ∑ r ∈ Rg, (1 : ℝ) / r := Finset.sum_nonneg (fun _ _ => by positivity)
  have hSJ : 1 / 480 ≤ (∑ j ∈ Jg, (1 : ℝ) / j) / Real.log X := by
    rw [le_div_iff₀ hL]; linarith
  have hK : 0 ≤ c₀ * X / (2 * D) := div_nonneg (mul_nonneg hc₀.le hX0.le) (by positivity)
  have hmain : c₀ * X / (2 * D) * ((∑ j ∈ Jg, (1 : ℝ) / j) / Real.log X) *
      (∑ r ∈ Rg, (1 : ℝ) / r) * (∑ q ∈ Qg, (1 : ℝ) / q) ≤ ((S4a.A0 D X).card : ℝ) := by
    have e : ∑ x ∈ (Jg ×ˢ Rg) ×ˢ Qg,
        (1 / (x.1.1 : ℝ)) * (1 / (x.1.2 : ℝ)) * (1 / (x.2 : ℝ)) =
        (∑ j ∈ Jg, (1 : ℝ) / j) * (∑ r ∈ Rg, (1 : ℝ) / r) * (∑ q ∈ Qg, (1 : ℝ) / q) :=
      triple_sum Jg Rg Qg (fun j => 1 / (j : ℝ)) (fun r => 1 / (r : ℝ)) (fun q => 1 / (q : ℝ))
    calc c₀ * X / (2 * D) * ((∑ j ∈ Jg, (1 : ℝ) / j) / Real.log X) *
          (∑ r ∈ Rg, (1 : ℝ) / r) * (∑ q ∈ Qg, (1 : ℝ) / q)
        = ∑ x ∈ (Jg ×ˢ Rg) ×ˢ Qg, c₀ * X / (2 * D) * (1 / Real.log X) *
            ((1 / (x.1.1 : ℝ)) * (1 / (x.1.2 : ℝ)) * (1 / (x.2 : ℝ))) := by
          rw [← Finset.mul_sum, e]; ring
      _ ≤ ∑ x ∈ (Jg ×ˢ Rg) ×ˢ Qg, ((PsetF D X x).card : ℝ) := Finset.sum_le_sum hcardP
      _ = ((((Jg ×ˢ Rg) ×ˢ Qg).sigma (PsetF D X)).card : ℝ) := by
          rw [Finset.card_sigma, Nat.cast_sum]
      _ ≤ ((S4a.A0 D X).card : ℝ) := by exact_mod_cast hS
  have step1 : c₀ * X / (2 * D) * (1 / 480) ≤
      c₀ * X / (2 * D) * ((∑ j ∈ Jg, (1 : ℝ) / j) / Real.log X) :=
    mul_le_mul_of_nonneg_left hSJ hK
  have step2 : c₀ * X / (2 * D) * (1 / 480) * (1 / 2 * L1) ≤
      c₀ * X / (2 * D) * ((∑ j ∈ Jg, (1 : ℝ) / j) / Real.log X) * (∑ r ∈ Rg, (1 : ℝ) / r) :=
    mul_le_mul step1 hRsum (mul_nonneg (by norm_num) hL1) (mul_nonneg hK (div_nonneg hSJ0 hL.le))
  have step3 : c₀ * X / (2 * D) * (1 / 480) * (1 / 2 * L1) * (1 / 2 * L2) ≤
      c₀ * X / (2 * D) * ((∑ j ∈ Jg, (1 : ℝ) / j) / Real.log X) * (∑ r ∈ Rg, (1 : ℝ) / r) *
        (∑ q ∈ Qg, (1 : ℝ) / q) :=
    mul_le_mul step2 hQsum (mul_nonneg (by norm_num) hL2)
      (mul_nonneg (mul_nonneg hK (div_nonneg hSJ0 hL.le)) hSR0)
  calc c₀ * L1 * L2 / (3840 * D) * X
      = c₀ * X / (2 * D) * (1 / 480) * (1 / 2 * L1) * (1 / 2 * L2) := by ring
    _ ≤ _ := step3
    _ ≤ _ := hmain

end Principia.Erdos1054.Proofs.A0Family

namespace Principia.Erdos1054.Proofs

open Finset Principia.Erdos1054 Principia.Erdos1054.Proofs.A0Family

theorem link_SvA0_jSum : Principia.Erdos1054.Spine.Link_SvA0_jSum := by
  intro hsh D hD ε hε
  refine ⟨max ((D : ℝ) ^ 120) (Real.exp (1 / ε)), fun X hX => ?_⟩
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hD0 : (0 : ℝ) < D := by linarith
  have hXD : (D : ℝ) ^ 120 ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp (1 / ε) ≤ X := le_trans (le_max_right _ _) hX
  have hX1 : 1 ≤ X := le_trans (one_le_pow₀ hDR) hXD
  have hX0 : 0 < X := by linarith
  have hlogX : 1 / ε ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos _) hXe
    rwa [Real.log_exp] at h
  have hεL : 1 ≤ ε * Real.log X := by
    have h := mul_le_mul_of_nonneg_left hlogX hε.le
    rwa [mul_one_div_cancel hε.ne'] at h
  have hA : (D : ℝ) ≤ X ^ ((1 : ℝ) / 120) := by
    have h := le_rpow_one_div (c := (D : ℝ)) (X := X) (n := 120) (by norm_num) hX0.le hXD
    rwa [show ((120 : ℕ) : ℝ) = 120 by norm_num] at h
  have hAB : X ^ ((1 : ℝ) / 120) ≤ X ^ ((1 : ℝ) / 60) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
  have hA1 : 1 ≤ X ^ ((1 : ℝ) / 120) / D := by rw [le_div_iff₀ hD0]; linarith
  have hB1 : 1 ≤ X ^ ((1 : ℝ) / 60) / D := by rw [le_div_iff₀ hD0]; linarith
  have hm1 : 1 ≤ ⌊X ^ ((1 : ℝ) / 120) / D⌋₊ := Nat.le_floor (by exact_mod_cast hA1)
  have hJ21 : 1 ≤ ⌊X ^ ((1 : ℝ) / 60) / D⌋₊ := Nat.le_floor (by exact_mod_cast hB1)
  have hmle : (⌊X ^ ((1 : ℝ) / 120) / D⌋₊ : ℝ) ≤ X ^ ((1 : ℝ) / 120) / D :=
    Nat.floor_le (by linarith)
  have hJ2lt : X ^ ((1 : ℝ) / 60) / D < (⌊X ^ ((1 : ℝ) / 60) / D⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hZ : (0 : ℝ) < 4 * (Real.pi ^ 2 / 6) := by positivity
  refine le_trans ?_ (jsum_core ⌊X ^ ((1 : ℝ) / 60) / D⌋₊ ⌊X ^ ((1 : ℝ) / 120) / D⌋₊
    (4 * (Real.pi ^ 2 / 6)) hZ _ ?_ ?_)
  · have hH2 : Real.log ((⌊X ^ ((1 : ℝ) / 60) / D⌋₊ : ℝ) + 1) ≤
        ∑ j ∈ Icc 1 ⌊X ^ ((1 : ℝ) / 60) / D⌋₊, (1 : ℝ) / j := by
      rw [sum_Icc_one_div_eq_harmonic]
      have h := log_add_one_le_harmonic ⌊X ^ ((1 : ℝ) / 60) / D⌋₊
      push_cast at h
      exact h
    have hHm : ∑ j ∈ Icc 1 ⌊X ^ ((1 : ℝ) / 120) / D⌋₊, (1 : ℝ) / j ≤
        1 + Real.log (⌊X ^ ((1 : ℝ) / 120) / D⌋₊ : ℝ) := by
      rw [sum_Icc_one_div_eq_harmonic]
      exact harmonic_le_one_add_log _
    have hsig := hsh ⌊X ^ ((1 : ℝ) / 60) / D⌋₊ hJ21
    have hbad : (1 / (4 * (Real.pi ^ 2 / 6))) *
        ∑ j ∈ Icc 1 ⌊X ^ ((1 : ℝ) / 60) / D⌋₊, (sig j : ℝ) / (j : ℝ) ^ 2 ≤
        (∑ j ∈ Icc 1 ⌊X ^ ((1 : ℝ) / 60) / D⌋₊, (1 : ℝ) / j) / 4 := by
      rw [one_div_mul_eq_div, div_le_iff₀ hZ]
      linarith
    have hBpos : 0 < X ^ ((1 : ℝ) / 60) / D := div_pos (Real.rpow_pos_of_pos hX0 _) hD0
    have hJ2log : Real.log (X ^ ((1 : ℝ) / 60) / D) ≤
        Real.log ((⌊X ^ ((1 : ℝ) / 60) / D⌋₊ : ℝ) + 1) :=
      Real.log_le_log hBpos hJ2lt.le
    have hmpos : (0 : ℝ) < (⌊X ^ ((1 : ℝ) / 120) / D⌋₊ : ℝ) := Nat.cast_pos.2 hm1
    have hmlog : Real.log (⌊X ^ ((1 : ℝ) / 120) / D⌋₊ : ℝ) ≤
        Real.log (X ^ ((1 : ℝ) / 120) / D) :=
      Real.log_le_log hmpos hmle
    have hlB : Real.log (X ^ ((1 : ℝ) / 60) / D) = (1 / 60) * Real.log X - Real.log D := by
      rw [Real.log_div (Real.rpow_pos_of_pos hX0 _).ne' hD0.ne', Real.log_rpow hX0]
    have hlA : Real.log (X ^ ((1 : ℝ) / 120) / D) = (1 / 120) * Real.log X - Real.log D := by
      rw [Real.log_div (Real.rpow_pos_of_pos hX0 _).ne' hD0.ne', Real.log_rpow hX0]
    have hlD : 0 ≤ Real.log D := Real.log_nonneg hDR
    linarith
  · intro j hj
    exact (Finset.mem_filter.1 hj).1
  · intro j hj hjG
    rw [Finset.mem_filter] at hjG
    by_cases h1 : (j : ℝ) ≤ X ^ ((1 : ℝ) / 120) / D
    · left
      exact Nat.le_floor h1
    · right
      by_contra h2
      exact hjG ⟨hj, not_le.1 h1, not_lt.1 h2⟩

theorem link_Lem_SvA0Count : Principia.Erdos1054.Spine.Link_Lem_SvA0Count := by
  intro hjs hU hdy hM δ hδ hδ1 D hD
  have hD1 : 1 ≤ D := Nat.one_le_iff_ne_zero.2 hD.1.ne_zero
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD1
  obtain ⟨X₁, hX₁⟩ := hjs D hD1 (1 / 480) (by norm_num)
  obtain ⟨X₂, hX₂⟩ := hU δ hδ hδ1 D hD
  obtain ⟨c₀, hc₀, hdy'⟩ := hdy
  obtain ⟨X₃, hX₃⟩ := mertens_window hM (a := 1 / 15) (b := 1 / 12) (by norm_num) (by norm_num)
  obtain ⟨X₄, hX₄⟩ := mertens_window hM (a := 7 / 20) (b := 11 / 30) (by norm_num) (by norm_num)
  have hL1 : 0 < Real.log ((1 / 12 : ℝ) / (1 / 15)) := Real.log_pos (by norm_num)
  have hL2 : 0 < Real.log ((11 / 30 : ℝ) / (7 / 20)) := Real.log_pos (by norm_num)
  refine ⟨c₀ * Real.log ((1 / 12 : ℝ) / (1 / 15)) * Real.log ((11 / 30 : ℝ) / (7 / 20)) /
    (3840 * D), by positivity, max (max X₁ X₂) (max (max X₃ X₄) 16), fun X hX => ?_⟩
  have hXa : X₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXb : X₂ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXc : X₃ ≤ X :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hX
  have hXd : X₄ ≤ X :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hX
  have hX16 : 16 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hX0 : (0 : ℝ) < X := by linarith
  refine count_core hD1 hX16 hc₀ hL1.le hL2.le hdy' (hX₁ X hXa) (hX₃ X hXc) (hX₄ X hXd)
    ?_ ?_ ?_ (hX₂ X hXb)
  · intro j hj
    rw [Finset.mem_filter, Finset.mem_Icc] at hj
    obtain ⟨⟨hj1, hjJ⟩, hjA, hjab⟩ := hj
    have hB0 : 0 ≤ X ^ ((1 : ℝ) / 60) / D := div_nonneg (Real.rpow_nonneg hX0.le _) hDR.le
    have hjB : (j : ℝ) ≤ X ^ ((1 : ℝ) / 60) / D := (Nat.le_floor_iff hB0).1 hjJ
    rw [div_lt_iff₀ hDR] at hjA
    rw [le_div_iff₀ hDR] at hjB
    refine ⟨hj1, ?_, ?_, hjab⟩
    · linarith
    · linarith
  · intro r hr
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter, Finset.mem_Iic,
      Finset.mem_Iic] at hr
    obtain ⟨⟨hr1, hrp⟩, hr2⟩ := hr
    refine ⟨hrp, ?_, (Nat.le_floor_iff (Real.rpow_nonneg hX0.le _)).1 hr1⟩
    have : ⌊X ^ ((1 : ℝ) / 15)⌋₊ < r := by
      by_contra hc
      exact hr2 ⟨not_lt.1 hc, hrp⟩
    exact (Nat.floor_lt (Real.rpow_nonneg hX0.le _)).1 this
  · intro q hq
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter, Finset.mem_Iic,
      Finset.mem_Iic] at hq
    obtain ⟨⟨hq1, hqp⟩, hq2⟩ := hq
    refine ⟨hqp, ?_, (Nat.le_floor_iff (Real.rpow_nonneg hX0.le _)).1 hq1⟩
    have : ⌊X ^ ((7 : ℝ) / 20)⌋₊ < q := by
      by_contra hc
      exact hq2 ⟨not_lt.1 hc, hqp⟩
    exact (Nat.floor_lt (Real.rpow_nonneg hX0.le _)).1 this

end Principia.Erdos1054.Proofs
