/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.Aliquot.Basic
import Principia.Common.Aliquot.Count
import Principia.Common.Aliquot.Euler
import Principia.Common.LucaPomerance.Lemma21
import Mathlib.NumberTheory.Chebyshev

set_option autoImplicit false

/-!
# Chen–Zhao: a lower bound for the untouchable numbers, for every modulus

Y.-G. Chen and Q.-Q. Zhao, *Nonaliquot numbers*, Publ. Math. Debrecen 78 (2011) 439–442,
Theorem 1: for every modulus `M`, `#{n ≤ x : n ∉ s(ℕ)} ≥ g_M x + o(x)` with
`g_M = ∑_{d ∣ M} φ(M/d)/(M/d) · max(0, 1/(2d) − 1/(σ(2d) − 2d))`.

Here the modulus is written `Q` (Chen–Zhao's `2M`) and the classes by `g = gcd(N, Q)` (their
`2d`), so the constant is (`czConst`)
```
czConst Q = ∑_{g ∣ Q, 2 ∣ g} φ(Q/g)/Q · cz(σ(g)/g),     cz t = max(0, 1 − 1/(t − 1)).
```
**`chenZhao_count`:** for every `Q ≥ 1` and `ε > 0`, eventually
`(czConst Q − ε) X ≤ #{N ≤ X : N untouchable}`.

## The argument (Chen–Zhao's, with the library's Luca–Pomerance lemma for their Lemma 1)

Fix an even class `g ∣ Q` with `σ(g) > 2g`, and an `N ≤ X` with `gcd(N, Q) = g` that is `s(m)`.
* If `m` is outside the density-zero set `E` of `Common.LucaPomerance.LP21` and large, then
  `v_p(m) < v_p(σ(m))` for every prime `p ∣ Q`, so `gcd(s(m), Q) = gcd(m, Q)` (`gcd_aliq_eq`):
  `m = g m₁` with `gcd(m₁, Q/g) = 1`, and `s(m) ≥ s(g) m₁` (`aliq_mul_le`) gives
  `m₁ ≤ X/s(g)`. So these `N` number at most `#{m₁ ≤ X/s(g) : gcd(m₁, Q/g) = 1}`.
* Otherwise `m ∈ E` or `m` is small. If `m` is even, `m ≤ 2 s(m) ≤ 2X` (`le_two_mul_aliq`),
  and there are `o(X)` such `m`. If `m` is odd, `σ(m) = N + m` is odd, so `m = k²`
  (`exists_sq_of_sigma_odd`), and the values `s(k²) ≤ X` number `≤ π(X) + X/T`
  (`s(p²) = p + 1`; `k³ ≤ s(k²)²` for composite `k`).
The class has `≥ ⌊X/Q⌋ φ(Q/g)` members, so it keeps `≥ φ(Q/g)/Q · (1 − g/s(g)) X − O(1)`
untouchables, and `φ(Q/g)/Q · (1 − g/s(g)) = wQ Q g · cz(σ(g)/g)`.

Chen–Zhao cite De Koninck–Luca for "`k ∣ σ(n)` for almost all `n`"; the congruence they use,
`s(m) ≡ −m (mod 2M)`, is exactly what `gcd_aliq_eq` delivers from Luca–Pomerance's (i).
-/

namespace Principia.Common.Aliquot

open Finset Filter
open Principia.Common.LucaPomerance.Aliquot (aliq le_sigma)
open Principia.Common.LucaPomerance.LP21 (lpY)

/-- The untouchable (nonaliquot) numbers: `N ≠ s(m)` for every `m ≥ 1`. -/
def Untouchable : Set ℕ := {N | ∀ m : ℕ, 1 ≤ m → aliq m ≠ N}

/-- **The Chen–Zhao constant** of the modulus `Q`. -/
noncomputable def czConst (Q : ℕ) : ℝ :=
  ∑ g ∈ Q.divisors.filter (2 ∣ ·), wQ Q g * cz (hRatio g)

/-! ## 1. Analytic inputs: `y(n) → ∞`, and `π(X) = o(X)` -/

/-- The Luca–Pomerance level `y(n) = log log n / log log log n` eventually exceeds any `B`. -/
theorem exists_le_lpY (B : ℝ) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → B ≤ lpY n := by
  set B' := max B 1 with hB'
  have hB'1 : 1 ≤ B' := le_max_right _ _
  set y₀ : ℝ := 4 * B' ^ 2 + 1 with hy₀
  refine ⟨⌈Real.exp (Real.exp y₀)⌉₊, fun n hn => ?_⟩
  have hn' : Real.exp (Real.exp y₀) ≤ n := Nat.ceil_le.1 hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (Real.exp_pos _) hn'
  have hlog1 : Real.exp y₀ ≤ Real.log n := (Real.le_log_iff_exp_le hnpos).2 hn'
  have hlog1pos : 0 < Real.log n := lt_of_lt_of_le (Real.exp_pos _) hlog1
  have hy : y₀ ≤ Real.log (Real.log n) := (Real.le_log_iff_exp_le hlog1pos).2 hlog1
  unfold lpY
  set y := Real.log (Real.log n) with hydef
  have hy1 : 1 < y := by nlinarith [sq_nonneg B']
  have hy0 : 0 ≤ y := by linarith
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  have hsq : Real.log y ≤ 2 * Real.sqrt y := by
    have h1 : Real.log (Real.sqrt y) ≤ Real.sqrt y - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (by linarith))
    have h2 : Real.log (Real.sqrt y) = Real.log y / 2 := Real.log_sqrt hy0
    linarith
  have hB2 : 2 * B' ≤ Real.sqrt y := by
    have h1 : Real.sqrt ((2 * B') ^ 2) = 2 * B' := Real.sqrt_sq (by linarith)
    rw [← h1]
    exact Real.sqrt_le_sqrt (by nlinarith)
  rw [le_div_iff₀ hlogy]
  calc B * Real.log y ≤ B' * Real.log y :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hlogy.le
    _ ≤ B' * (2 * Real.sqrt y) := mul_le_mul_of_nonneg_left hsq (by linarith)
    _ = (2 * B') * Real.sqrt y := by ring
    _ ≤ Real.sqrt y * Real.sqrt y := mul_le_mul_of_nonneg_right hB2 (Real.sqrt_nonneg _)
    _ = y := Real.mul_self_sqrt hy0

/-- `#{p ≤ X prime} ≤ ε X` eventually (Chebyshev's bound, Mathlib). -/
theorem exists_card_primes_le (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → (#{p ∈ Icc 1 X | p.Prime} : ℝ) ≤ ε * X := by
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1
    (Chebyshev.eventually_primeCounting_le (ε := 1) one_pos)
  set c : ℝ := Real.log 4 + 1 with hc
  have hc0 : 0 < c := by
    have : 0 < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  refine ⟨max ⌈x₁⌉₊ ⌈Real.exp (c / ε)⌉₊, fun X hX => ?_⟩
  have hX1 : x₁ ≤ X := Nat.ceil_le.1 (le_trans (le_max_left _ _) hX)
  have hX2 : Real.exp (c / ε) ≤ X := Nat.ceil_le.1 (le_trans (le_max_right _ _) hX)
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos _) hX2
  have hπ := hx₁ X hX1
  rw [Nat.floor_natCast] at hπ
  have hlogX : c / ε ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).2 hX2
  have hlogpos : 0 < Real.log X := lt_of_lt_of_le (div_pos hc0 hε) hlogX
  have hcard : #{p ∈ Icc 1 X | p.Prime} ≤ Nat.primeCounting X := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    rw [Nat.primesLE, Nat.primesBelow, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hp.2⟩
  have hce : c ≤ ε * Real.log X := by
    have := (div_le_iff₀ hε).1 hlogX
    linarith
  calc (#{p ∈ Icc 1 X | p.Prime} : ℝ) ≤ Nat.primeCounting X := by exact_mod_cast hcard
    _ ≤ c * X / Real.log X := hπ
    _ ≤ ε * X := by
        rw [div_le_iff₀ hlogpos]
        nlinarith [mul_le_mul_of_nonneg_left hce hXpos.le]

/-! ## 2. The squares `k²` with `k` odd: their values `s(k²)` are `o(X)` -/

/-- The values `s(k²) ≤ X` with `2 ≤ k ≤ X`. -/
def oddSqVals (X : ℕ) : Finset ℕ := ((Icc 2 X).image (fun k => aliq (k ^ 2))).filter (· ≤ X)

theorem card_cube_le (X T : ℕ) (hT : 0 < T) (hX : T ^ 3 ≤ X) :
    #{k ∈ Icc 1 X | k ^ 3 ≤ X ^ 2} ≤ X / T := by
  have hsub : {k ∈ Icc 1 X | k ^ 3 ≤ X ^ 2} ⊆ Icc 1 (X / T) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    rw [Finset.mem_Icc]
    refine ⟨hk.1.1, ?_⟩
    by_contra h
    push Not at h
    have h1 : X < k * T := Nat.lt_mul_of_div_lt h hT
    have h2 : X ^ 3 < (k * T) ^ 3 := Nat.pow_lt_pow_left h1 (by norm_num)
    have h3 : (k * T) ^ 3 ≤ X ^ 2 * X := by
      rw [mul_pow]
      exact Nat.mul_le_mul hk.2 hX
    have h4 : X ^ 2 * X = X ^ 3 := by ring
    rw [h4] at h3
    exact absurd (lt_of_lt_of_le h2 h3) (lt_irrefl _)
  calc #{k ∈ Icc 1 X | k ^ 3 ≤ X ^ 2} ≤ #(Icc 1 (X / T)) := Finset.card_le_card hsub
    _ = X / T := by simp

theorem card_oddSqVals_le (X T : ℕ) (hT : 0 < T) (hX : T ^ 3 ≤ X) :
    #(oddSqVals X) ≤ #{p ∈ Icc 1 X | p.Prime} + X / T := by
  have hsub : oddSqVals X ⊆ ({p ∈ Icc 1 X | p.Prime}).image (· + 1) ∪
      ({k ∈ Icc 1 X | k ^ 3 ≤ X ^ 2}).image (fun k => aliq (k ^ 2)) := by
    intro N hN
    rw [oddSqVals, Finset.mem_filter, Finset.mem_image] at hN
    obtain ⟨⟨k, hk, hkN⟩, hNX⟩ := hN
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
    by_cases hkp : k.Prime
    · left
      refine ⟨k, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨by omega, hk.2⟩, hkp⟩
      · rw [← hkN, aliq_sq_prime hkp]
    · right
      refine ⟨k, ?_, hkN⟩
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, hk.2⟩, ?_⟩
      have h1 := cube_le_sq_aliq_sq hk.1 hkp
      rw [hkN] at h1
      exact h1.trans (Nat.pow_le_pow_left hNX 2)
  calc #(oddSqVals X)
      ≤ #(({p ∈ Icc 1 X | p.Prime}).image (· + 1)) +
          #(({k ∈ Icc 1 X | k ^ 3 ≤ X ^ 2}).image (fun k => aliq (k ^ 2))) :=
        (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    _ ≤ #{p ∈ Icc 1 X | p.Prime} + #{k ∈ Icc 1 X | k ^ 3 ≤ X ^ 2} :=
        Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ ≤ #{p ∈ Icc 1 X | p.Prime} + X / T := Nat.add_le_add_left (card_cube_le X T hT hX) _

/-! ## 3. One class `gcd(N, Q) = g` -/

/-- The cofactors `m₁ ≤ X/s(g)` coprime to `Q/g`; the pre-images in the class are `g m₁`. -/
def preSet (Q g X : ℕ) : Finset ℕ := {m ∈ Icc 1 (X / aliq g) | (Q / g).Coprime m}

open Classical in
/-- The exceptional values: `s(m)` for `m ≤ 2X` in `E` or below `n₁`, and the `s(k²)`. -/
noncomputable def badSet (E : Set ℕ) (n₁ X : ℕ) : Finset ℕ :=
  ({m ∈ Icc 1 (2 * X) | m ∈ E ∨ m < n₁}).image aliq ∪ oddSqVals X

open Classical in
/-- **One class.** Every `N ≤ X` with `gcd(N, Q) = g` is untouchable, or `s(g m₁)` with
`m₁ ∈ preSet`, or exceptional. -/
theorem card_class_le (Q g X n₁ : ℕ) (E : Set ℕ) (hQ : 0 < Q) (hg : g ∣ Q) (hg2 : 2 ∣ g)
    (hgs : 2 * g < ArithmeticFunction.sigma 1 g)
    (hgood : ∀ m, m ∉ E → n₁ ≤ m → Nat.gcd (aliq m) Q = Nat.gcd m Q) :
    #{N ∈ Icc 1 X | Nat.gcd N Q = g} ≤
      #{N ∈ Icc 1 X | Nat.gcd N Q = g ∧ N ∈ Untouchable} + #(preSet Q g X) +
        #{N ∈ badSet E n₁ X | Nat.gcd N Q = g} := by
  set S := ({N ∈ Icc 1 X | Nat.gcd N Q = g} : Finset ℕ) with hS
  have hg0 : 0 < g := Nat.pos_of_dvd_of_pos hg hQ
  have hs0 : 0 < aliq g := by
    unfold aliq
    omega
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (fun N => N ∈ Untouchable)
  have h1 : S.filter (fun N => N ∈ Untouchable) =
      {N ∈ Icc 1 X | Nat.gcd N Q = g ∧ N ∈ Untouchable} := by
    rw [hS, Finset.filter_filter]
  have h2 : S.filter (fun N => ¬ N ∈ Untouchable) ⊆
      (preSet Q g X).image (fun m => aliq (g * m)) ∪ {N ∈ badSet E n₁ X | Nat.gcd N Q = g} := by
    intro N hN
    rw [Finset.mem_filter, hS, Finset.mem_filter, Finset.mem_Icc] at hN
    obtain ⟨⟨⟨hN1, hNX⟩, hgcd⟩, hNU⟩ := hN
    obtain ⟨m, hm1, hmN⟩ : ∃ m, 1 ≤ m ∧ aliq m = N := by
      simp only [Untouchable, Set.mem_setOf_eq, not_forall, ne_eq, not_not] at hNU
      obtain ⟨m, hm1, hm⟩ := hNU
      exact ⟨m, hm1, hm⟩
    have h2N : 2 ∣ N := by
      have h := Nat.gcd_dvd_left N Q
      rw [hgcd] at h
      exact hg2.trans h
    rw [Finset.mem_union]
    by_cases hgm : m ∉ E ∧ n₁ ≤ m
    · left
      have hmg : Nat.gcd m Q = g := by rw [← hgood m hgm.1 hgm.2, hmN, hgcd]
      have hgdm : g ∣ m := hmg ▸ Nat.gcd_dvd_left m Q
      obtain ⟨m₁, rfl⟩ := hgdm
      rw [Finset.mem_image]
      refine ⟨m₁, ?_, hmN⟩
      have hm₁ : 0 < m₁ := by
        rcases Nat.eq_zero_or_pos m₁ with h | h
        · subst h
          simp at hm1
        · exact h
      have hgQ : g * (Q / g) = Q := Nat.mul_div_cancel' hg
      have hcop : (Q / g).Coprime m₁ := by
        have h3 : g * Nat.gcd m₁ (Q / g) = g * 1 := by
          rw [← Nat.gcd_mul_left, hgQ, hmg, mul_one]
        exact Nat.Coprime.symm (Nat.eq_of_mul_eq_mul_left hg0 h3)
      have hle : aliq g * m₁ ≤ X := (aliq_mul_le g m₁ hm₁).trans (by rw [hmN]; exact hNX)
      rw [preSet, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hm₁, (Nat.le_div_iff_mul_le hs0).2 (by rw [mul_comm]; exact hle)⟩, hcop⟩
    · right
      rw [Finset.mem_filter]
      refine ⟨?_, hgcd⟩
      rw [badSet, Finset.mem_union]
      by_cases hm2 : 2 ∣ m
      · left
        rw [Finset.mem_image]
        refine ⟨m, ?_, hmN⟩
        rw [Finset.mem_filter, Finset.mem_Icc]
        have hm2' : 2 ≤ m := by
          obtain ⟨c, hc⟩ := hm2
          omega
        have hle := le_two_mul_aliq hm2' hm2
        refine ⟨⟨hm1, by omega⟩, ?_⟩
        by_contra hc
        push Not at hc
        exact hgm ⟨hc.1, hc.2⟩
      · right
        have hσodd : Odd (ArithmeticFunction.sigma 1 m) := by
          rw [sigma_eq_aliq_add, hmN]
          exact Even.add_odd (even_iff_two_dvd.2 h2N) (Nat.odd_iff.2 (by omega))
        obtain ⟨k, rfl⟩ := exists_sq_of_sigma_odd (by omega) hm2 hσodd
        rw [oddSqVals, Finset.mem_filter, Finset.mem_image]
        refine ⟨⟨k, ?_, hmN⟩, hNX⟩
        rw [Finset.mem_Icc]
        have hk2 : 2 ≤ k := by
          rcases Nat.lt_or_ge k 2 with h | h
          · interval_cases k
            · simp at hm1
            · rw [one_pow, aliq_one] at hmN
              omega
          · exact h
        have hkk : k ≤ aliq (k ^ 2) :=
          le_aliq_of_dvd (pow_pos (by omega) 2) (Dvd.intro k (by ring)) (by nlinarith)
        exact ⟨hk2, by omega⟩
  calc #S = #(S.filter (fun N => N ∈ Untouchable)) +
        #(S.filter (fun N => ¬ N ∈ Untouchable)) := hsplit.symm
    _ ≤ #{N ∈ Icc 1 X | Nat.gcd N Q = g ∧ N ∈ Untouchable} +
          (#((preSet Q g X).image (fun m => aliq (g * m))) +
            #{N ∈ badSet E n₁ X | Nat.gcd N Q = g}) := by
        rw [h1]
        exact Nat.add_le_add_left ((Finset.card_le_card h2).trans (Finset.card_union_le _ _)) _
    _ ≤ #{N ∈ Icc 1 X | Nat.gcd N Q = g ∧ N ∈ Untouchable} + #(preSet Q g X) +
          #{N ∈ badSet E n₁ X | Nat.gcd N Q = g} := by
        have := Finset.card_image_le (s := preSet Q g X) (f := fun m => aliq (g * m))
        omega

/-- **The real bound of one class**: `#class − #preSet ≥ wQ Q g · cz(σ(g)/g) · X − 2 φ(Q/g)`. -/
theorem class_real_bound (Q g X : ℕ) (hQ : 0 < Q) (hg : g ∣ Q)
    (hgs : 2 * g < ArithmeticFunction.sigma 1 g) :
    wQ Q g * cz (hRatio g) * X - 2 * Nat.totient (Q / g) ≤
      (#{N ∈ Icc 1 X | Nat.gcd N Q = g} : ℝ) - #(preSet Q g X) := by
  have hg0 : 0 < g := Nat.pos_of_dvd_of_pos hg hQ
  have hgQ : g * (Q / g) = Q := Nat.mul_div_cancel' hg
  have hR0 : 0 < Q / g := Nat.div_pos (Nat.le_of_dvd hQ hg) hg0
  have hsg : g < ArithmeticFunction.sigma 1 g := by omega
  have hc1 : X / Q * Nat.totient (Q / g) ≤ #{N ∈ Icc 1 X | Nat.gcd N Q = g} :=
    card_class_ge Q g X hQ hg
  have hc2 : #(preSet Q g X) ≤ (X / aliq g / (Q / g) + 1) * Nat.totient (Q / g) :=
    card_coprime_Icc_le (Q / g) (X / aliq g) hR0
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hgr : (0 : ℝ) < g := by exact_mod_cast hg0
  have hRr : (0 : ℝ) < ((Q / g : ℕ) : ℝ) := by exact_mod_cast hR0
  have hQgR : (Q : ℝ) = g * ((Q / g : ℕ) : ℝ) := by exact_mod_cast hgQ.symm
  have hsr : ((aliq g : ℕ) : ℝ) = (ArithmeticFunction.sigma 1 g : ℝ) - g := by
    rw [Nat.cast_sub hsg.le]
  have hsr0 : (0 : ℝ) < ((aliq g : ℕ) : ℝ) := by
    rw [hsr]
    have : (g : ℝ) < ArithmeticFunction.sigma 1 g := by exact_mod_cast hsg
    linarith
  have hA0 : (0 : ℝ) ≤ (Nat.totient (Q / g) : ℝ) := Nat.cast_nonneg _
  have hXQ : (X : ℝ) / Q - 1 ≤ ((X / Q : ℕ) : ℝ) := by
    have h := Nat.lt_div_mul_add (a := X) hQ
    have h' : (X : ℝ) < ((X / Q : ℕ) : ℝ) * Q + Q := by exact_mod_cast h
    rw [div_sub_one hQr.ne', div_le_iff₀ hQr]
    linarith
  have hXs : ((X / aliq g / (Q / g) : ℕ) : ℝ) ≤
      (X : ℝ) / (((aliq g : ℕ) : ℝ) * ((Q / g : ℕ) : ℝ)) := by
    rw [Nat.div_div_eq_div_mul]
    have := Nat.cast_div_le (α := ℝ) (m := X) (n := aliq g * (Q / g))
    rwa [Nat.cast_mul] at this
  have hc1r : ((X / Q : ℕ) : ℝ) * (Nat.totient (Q / g) : ℝ) ≤
      (#{N ∈ Icc 1 X | Nat.gcd N Q = g} : ℝ) := by
    exact_mod_cast hc1
  have hc2r : (#(preSet Q g X) : ℝ) ≤
      (((X / aliq g / (Q / g) : ℕ) : ℝ) + 1) * (Nat.totient (Q / g) : ℝ) := by
    exact_mod_cast hc2
  have e1 : (Nat.totient (Q / g) : ℝ) * X / Q - Nat.totient (Q / g) ≤
      (#{N ∈ Icc 1 X | Nat.gcd N Q = g} : ℝ) :=
    calc (Nat.totient (Q / g) : ℝ) * X / Q - Nat.totient (Q / g)
        = ((X : ℝ) / Q - 1) * (Nat.totient (Q / g) : ℝ) := by ring
      _ ≤ ((X / Q : ℕ) : ℝ) * (Nat.totient (Q / g) : ℝ) := mul_le_mul_of_nonneg_right hXQ hA0
      _ ≤ _ := hc1r
  have e2 : (#(preSet Q g X) : ℝ) ≤
      (Nat.totient (Q / g) : ℝ) * X / (((aliq g : ℕ) : ℝ) * ((Q / g : ℕ) : ℝ)) +
        Nat.totient (Q / g) :=
    calc (#(preSet Q g X) : ℝ)
        ≤ (((X / aliq g / (Q / g) : ℕ) : ℝ) + 1) * (Nat.totient (Q / g) : ℝ) := hc2r
      _ ≤ ((X : ℝ) / (((aliq g : ℕ) : ℝ) * ((Q / g : ℕ) : ℝ)) + 1) *
            (Nat.totient (Q / g) : ℝ) := mul_le_mul_of_nonneg_right (by linarith) hA0
      _ = _ := by ring
  have h2 : (2 : ℝ) < hRatio g := by
    unfold hRatio
    rw [lt_div_iff₀ hgr]
    exact_mod_cast hgs
  have hcz : wQ Q g * cz (hRatio g) * X = (Nat.totient (Q / g) : ℝ) * X / Q -
      (Nat.totient (Q / g) : ℝ) * X / (((aliq g : ℕ) : ℝ) * ((Q / g : ℕ) : ℝ)) := by
    have hne : (ArithmeticFunction.sigma 1 g : ℝ) - g ≠ 0 := by
      rw [← hsr]
      exact hsr0.ne'
    have hne' : (ArithmeticFunction.sigma 1 g : ℝ) / g - 1 ≠ 0 := by
      rw [div_sub_one hgr.ne']
      exact div_ne_zero hne hgr.ne'
    unfold wQ cz
    rw [if_pos h2]
    unfold hRatio
    rw [hQgR, hsr]
    field_simp
    ring
  rw [hcz]
  linarith

/-! ## 4. All classes together -/

/-- The classes that contribute: even `g ∣ Q` with `σ(g) > 2g`. -/
noncomputable def goodClasses (Q : ℕ) : Finset ℕ :=
  Q.divisors.filter (fun g => 2 ∣ g ∧ 2 * g < ArithmeticFunction.sigma 1 g)

theorem czConst_eq (Q : ℕ) :
    czConst Q = ∑ g ∈ goodClasses Q, wQ Q g * cz (hRatio g) := by
  unfold czConst goodClasses
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro g _
  by_cases h2 : 2 ∣ g
  · by_cases h3 : 2 * g < ArithmeticFunction.sigma 1 g
    · rw [if_pos h2, if_pos ⟨h2, h3⟩]
    · have hle : hRatio g ≤ 2 := by
        unfold hRatio
        rcases Nat.eq_zero_or_pos g with hg0 | hg0
        · subst hg0
          simp
        · rw [div_le_iff₀ (by exact_mod_cast hg0)]
          push Not at h3
          exact_mod_cast h3
      have hcz : cz (hRatio g) = 0 := by
        unfold cz
        rw [if_neg (by linarith)]
      rw [if_pos h2, if_neg (fun h => h3 h.2), hcz, mul_zero]
  · rw [if_neg h2, if_neg (fun h => h2 h.1)]

open Classical in
/-- **All classes:** `czConst Q · X − C ≤ #{untouchable ≤ X} + #badSet`. -/
theorem sum_classes_bound (Q X n₁ : ℕ) (E : Set ℕ) (hQ : 0 < Q)
    (hgood : ∀ m, m ∉ E → n₁ ≤ m → Nat.gcd (aliq m) Q = Nat.gcd m Q) :
    czConst Q * X - 2 * ∑ g ∈ goodClasses Q, (Nat.totient (Q / g) : ℝ) ≤
      (#{N ∈ Icc 1 X | N ∈ Untouchable} : ℝ) + #(badSet E n₁ X) := by
  have hmem : ∀ g ∈ goodClasses Q, g ∣ Q ∧ 2 ∣ g ∧ 2 * g < ArithmeticFunction.sigma 1 g := by
    intro g hg
    rw [goodClasses, Finset.mem_filter] at hg
    exact ⟨Nat.dvd_of_mem_divisors hg.1, hg.2.1, hg.2.2⟩
  -- the natural-number inequality summed over the classes
  have hnat : ∑ g ∈ goodClasses Q, #{N ∈ Icc 1 X | Nat.gcd N Q = g} ≤
      #{N ∈ Icc 1 X | N ∈ Untouchable} + ∑ g ∈ goodClasses Q, #(preSet Q g X) +
        #(badSet E n₁ X) := by
    have hU : ∑ g ∈ goodClasses Q, #{N ∈ Icc 1 X | Nat.gcd N Q = g ∧ N ∈ Untouchable} ≤
        #{N ∈ Icc 1 X | N ∈ Untouchable} := by
      have heq : ∀ g ∈ goodClasses Q, #{N ∈ Icc 1 X | Nat.gcd N Q = g ∧ N ∈ Untouchable} =
          #{N ∈ ({N ∈ Icc 1 X | N ∈ Untouchable} : Finset ℕ) | Nat.gcd N Q = g} := by
        intro g _
        rw [Finset.filter_filter]
        congr 1
        apply Finset.filter_congr
        intro N _
        exact and_comm
      rw [Finset.sum_congr rfl heq, Finset.sum_card_fiberwise_eq_card_filter]
      exact Finset.card_filter_le _ _
    have hB : ∑ g ∈ goodClasses Q, #{N ∈ badSet E n₁ X | Nat.gcd N Q = g} ≤ #(badSet E n₁ X) := by
      rw [Finset.sum_card_fiberwise_eq_card_filter]
      exact Finset.card_filter_le _ _
    calc ∑ g ∈ goodClasses Q, #{N ∈ Icc 1 X | Nat.gcd N Q = g}
        ≤ ∑ g ∈ goodClasses Q, (#{N ∈ Icc 1 X | Nat.gcd N Q = g ∧ N ∈ Untouchable} +
            #(preSet Q g X) + #{N ∈ badSet E n₁ X | Nat.gcd N Q = g}) := by
          apply Finset.sum_le_sum
          intro g hg
          obtain ⟨h1, h2, h3⟩ := hmem g hg
          exact card_class_le Q g X n₁ E hQ h1 h2 h3 hgood
      _ = ∑ g ∈ goodClasses Q, #{N ∈ Icc 1 X | Nat.gcd N Q = g ∧ N ∈ Untouchable} +
            ∑ g ∈ goodClasses Q, #(preSet Q g X) +
            ∑ g ∈ goodClasses Q, #{N ∈ badSet E n₁ X | Nat.gcd N Q = g} := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ ≤ _ := by omega
  have hnatr : (∑ g ∈ goodClasses Q, (#{N ∈ Icc 1 X | Nat.gcd N Q = g} : ℝ)) ≤
      (#{N ∈ Icc 1 X | N ∈ Untouchable} : ℝ) + ∑ g ∈ goodClasses Q, (#(preSet Q g X) : ℝ) +
        #(badSet E n₁ X) := by
    exact_mod_cast hnat
  have hreal : czConst Q * X - 2 * ∑ g ∈ goodClasses Q, (Nat.totient (Q / g) : ℝ) ≤
      ∑ g ∈ goodClasses Q, ((#{N ∈ Icc 1 X | Nat.gcd N Q = g} : ℝ) - #(preSet Q g X)) := by
    rw [czConst_eq, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro g hg
    obtain ⟨h1, _, h3⟩ := hmem g hg
    exact class_real_bound Q g X hQ h1 h3
  rw [Finset.sum_sub_distrib] at hreal
  linarith

/-! ## 5. The theorem -/

open Classical in
/-- **Chen–Zhao, Theorem 1 (general modulus).** For every `Q ≥ 1` and `ε > 0`, eventually
`(czConst Q − ε) X ≤ #{1 ≤ N ≤ X : N untouchable}`. -/
theorem chenZhao_count (Q : ℕ) (hQ : 0 < Q) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (czConst Q - ε) * X ≤ (#{N ∈ Icc 1 X | N ∈ Untouchable} : ℝ) := by
  classical
  obtain ⟨E, hEd, hE⟩ := Principia.Common.LucaPomerance.LP21.lucaPomerance_lemma21
  obtain ⟨n₀, hn₀⟩ := exists_le_lpY (Q : ℝ)
  obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ℕ, n₁ = max n₀ 2 := ⟨_, rfl⟩
  have hgood : ∀ m, m ∉ E → n₁ ≤ m → Nat.gcd (aliq m) Q = Nat.gcd m Q := by
    intro m hm hmn
    have hm2 : 2 ≤ m := by omega
    have hly : (Q : ℝ) ≤ lpY m := hn₀ m (by omega)
    apply gcd_aliq_eq hm2 hQ
    intro p hp hpQ
    apply (hE m hm).1 p hp
    have : (p : ℝ) ≤ Q := by exact_mod_cast Nat.le_of_dvd hQ hpQ
    linarith
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 2 * ∑ g ∈ goodClasses Q, (Nat.totient (Q / g) : ℝ) :=
    ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hC]
    positivity
  -- thresholds
  obtain ⟨N₁, hN₁⟩ := hEd (ε / 10) (by positivity)
  obtain ⟨X₂, hX₂⟩ := exists_card_primes_le (ε / 5) (by positivity)
  obtain ⟨T, hT⟩ : ∃ T : ℕ, T = ⌈5 / ε⌉₊ + 1 := ⟨_, rfl⟩
  have hT0 : 0 < T := by omega
  have hTr : 5 / ε ≤ (T : ℝ) := by
    have := Nat.le_ceil (5 / ε)
    rw [hT]
    push_cast
    linarith
  obtain ⟨X₄, hX₄⟩ : ∃ X₄ : ℕ, X₄ = ⌈((n₁ : ℝ) + C) * 5 / ε⌉₊ := ⟨_, rfl⟩
  refine ⟨max (max N₁ X₂) (max (T ^ 3) X₄), fun X hX => ?_⟩
  have hXN₁ : N₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXX₂ : X₂ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXT : T ^ 3 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXX₄ : X₄ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hXr : (0 : ℝ) ≤ X := Nat.cast_nonneg _
  -- the main bound
  have hmain := sum_classes_bound Q X n₁ E hQ hgood
  rw [← hC] at hmain
  -- the bad set
  have hbad1 : #({m ∈ Icc 1 (2 * X) | m ∈ E ∨ m < n₁}) ≤
      #({m ∈ Icc 1 (2 * X) | m ∈ E}) + n₁ := by
    rw [Finset.filter_or]
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add_left ?_ _)
    calc #({m ∈ Icc 1 (2 * X) | m < n₁}) ≤ #(Finset.range n₁) := by
          apply Finset.card_le_card
          intro m hm
          rw [Finset.mem_filter] at hm
          exact Finset.mem_range.2 hm.2
      _ = n₁ := Finset.card_range n₁
  have hbad : #(badSet E n₁ X) ≤
      #({m ∈ Icc 1 (2 * X) | m ∈ E}) + n₁ + (#{p ∈ Icc 1 X | p.Prime} + X / T) := by
    calc #(badSet E n₁ X) ≤ #(({m ∈ Icc 1 (2 * X) | m ∈ E ∨ m < n₁}).image aliq) +
          #(oddSqVals X) := by
          rw [badSet]
          exact Finset.card_union_le _ _
      _ ≤ #({m ∈ Icc 1 (2 * X) | m ∈ E ∨ m < n₁}) + #(oddSqVals X) :=
          Nat.add_le_add_right Finset.card_image_le _
      _ ≤ _ := Nat.add_le_add hbad1 (card_oddSqVals_le X T hT0 hXT)
  have hbadr : (#(badSet E n₁ X) : ℝ) ≤
      (#({m ∈ Icc 1 (2 * X) | m ∈ E}) : ℝ) + n₁ + ((#{p ∈ Icc 1 X | p.Prime} : ℝ) +
        ((X / T : ℕ) : ℝ)) := by
    exact_mod_cast hbad
  -- the four small terms
  have hE' : (#({m ∈ Icc 1 (2 * X) | m ∈ E}) : ℝ) ≤ ε / 5 * X := by
    have := hN₁ (2 * X) (by omega)
    push_cast at this
    linarith
  have hP' : (#{p ∈ Icc 1 X | p.Prime} : ℝ) ≤ ε / 5 * X := hX₂ X hXX₂
  have hT' : ((X / T : ℕ) : ℝ) ≤ ε / 5 * X := by
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT0
    calc ((X / T : ℕ) : ℝ) ≤ (X : ℝ) / T := Nat.cast_div_le
      _ ≤ ε / 5 * X := by
        rw [div_le_iff₀ hTpos]
        have : (5 : ℝ) ≤ ε * T := by
          have := (div_le_iff₀ hε).1 hTr
          linarith
        nlinarith [mul_nonneg hXr (sub_nonneg.2 this)]
  have hn₁C : (n₁ : ℝ) + C ≤ ε / 5 * X := by
    have h := Nat.ceil_le.1 (hX₄ ▸ hXX₄)
    have h' : ((n₁ : ℝ) + C) * 5 ≤ X * ε := (div_le_iff₀ hε).1 h
    linarith
  rw [sub_mul]
  linarith

end Principia.Common.Aliquot
