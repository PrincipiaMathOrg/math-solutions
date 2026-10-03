/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.SW.Rate
import Principia.Common.SW.ChebyshevDyadic
import Mathlib.NumberTheory.Chebyshev

/-!
# Siegel–Walfisz, dyadic lower bound for primes in progressions

`sw_dyadic_count`: there are absolute constants `C, c > 0` such that for every modulus `q ≥ 1`,
every residue `a` coprime to `q` and every `t ≥ exp(C q²)`,

  `#{p prime : t < p ≤ 2t, p ≡ a (mod q)} ≥ c·t / (q log t)`.

Route. Character orthogonality over the window `s = (⌊t⌋, ⌊2t⌋]` (`psi_ap_orthogonality_finset`)
gives `φ(q)·ψ(s; q, a) ≥ ψ(s, χ₀) − ∑_{χ ≠ χ₀} ‖ψ(s, χ)‖` (`orth_lower`). The principal term is at
least `∑_{p ∈ s} log p ≥ (log 4/12)·t` (Chebyshev/Erdős, `sum_log_primes_dyadic_real`; every prime
`p > t ≥ q` is prime to `q`), so **no prime number theorem is needed**. Each non-principal term is
`≤ 3 C₅ t exp(−c₅ (log t)^{1/10})` by the sharp Siegel–Walfisz bound `psi_sharp_SW_rate` (at
`B = 1`, valid since `q ≤ q² ≤ log t`), and there are fewer than `q ≤ (log t)^{1/2}` of them. Prime
powers
cost `ψ(2t) − θ(2t) ≤ 2√(2t) log(2t)` (Mathlib). The threshold `t ≥ exp(C q²)` makes every error
term small compared with `t/q` for one absolute `C`.
-/

set_option autoImplicit false

namespace Principia.Common.SW

open ArithmeticFunction

/-- Character orthogonality for the von Mangoldt sum over an arbitrary finite set `s` (the master's
`psi_ap_orthogonality`, whose proof never used that `s` is an initial segment). -/
theorem psi_ap_orthogonality_finset (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (s : Finset ℕ) :
    (q.totient : ℂ) * (∑ n ∈ s, if a = ((n : ZMod q)) then ((vonMangoldt n : ℝ) : ℂ) else 0)
      = ∑ χ : DirichletCharacter ℂ q, (χ a⁻¹) *
          (∑ n ∈ s, χ ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ)) := by
  symm
  calc ∑ χ : DirichletCharacter ℂ q, (χ a⁻¹) *
      (∑ n ∈ s, χ ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ))
      = ∑ χ : DirichletCharacter ℂ q, ∑ n ∈ s,
          (χ a⁻¹ * χ ((n : ZMod q))) * ((vonMangoldt n : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro χ _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
    _ = ∑ n ∈ s, ∑ χ : DirichletCharacter ℂ q,
          (χ a⁻¹ * χ ((n : ZMod q))) * ((vonMangoldt n : ℝ) : ℂ) := Finset.sum_comm
    _ = ∑ n ∈ s,
          (if a = ((n : ZMod q)) then (q.totient : ℂ) else 0) * ((vonMangoldt n : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro n _
        rw [← Finset.sum_mul,
          DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) ha ((n : ZMod q))]
    _ = (q.totient : ℂ) * (∑ n ∈ s,
          if a = ((n : ZMod q)) then ((vonMangoldt n : ℝ) : ℂ) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        split_ifs
        · ring
        · ring

open scoped Classical in
/-- The real lower bound from orthogonality: `φ(q)·ψ(s; q, a) ≥ ψ(s, χ₀) − ∑_{χ≠1} ‖ψ(s, χ)‖`. -/
theorem orth_lower (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (s : Finset ℕ) :
    (∑ n ∈ s, if IsUnit ((n : ℕ) : ZMod q) then vonMangoldt n else 0)
      - ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          ‖∑ n ∈ s, χ ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ)‖
      ≤ (q.totient : ℝ) * ∑ n ∈ s, if a = ((n : ZMod q)) then vonMangoldt n else 0 := by
  have hAP := psi_ap_orthogonality_finset q a ha s
  have ha_inv : IsUnit (a⁻¹ : ZMod q) := IsUnit.of_mul_eq_one a (ZMod.inv_mul_of_unit a ha)
  have hone : (1 : DirichletCharacter ℂ q) a⁻¹ = 1 := MulChar.one_apply ha_inv
  have hψ₀ : (∑ n ∈ s, (1 : DirichletCharacter ℂ q) ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ))
      = (((∑ n ∈ s, if IsUnit ((n : ℕ) : ZMod q) then vonMangoldt n else 0 : ℝ)) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro n _
    by_cases h : IsUnit ((n : ℕ) : ZMod q)
    · rw [MulChar.one_apply h, if_pos h, one_mul]
    · rw [MulChar.map_nonunit _ h, if_neg h, zero_mul, Complex.ofReal_zero]
  have hSreal : (∑ n ∈ s, if a = ((n : ZMod q)) then ((vonMangoldt n : ℝ) : ℂ) else 0)
      = (((∑ n ∈ s, if a = ((n : ZMod q)) then vonMangoldt n else 0 : ℝ)) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro n _
    by_cases h : a = ((n : ZMod q))
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, Complex.ofReal_zero]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (1 : DirichletCharacter ℂ q)),
    hone, one_mul, hψ₀, hSreal] at hAP
  set A := ∑ n ∈ s, if a = ((n : ZMod q)) then vonMangoldt n else 0 with hA
  set S₀ := ∑ n ∈ s, if IsUnit ((n : ℕ) : ZMod q) then vonMangoldt n else 0 with hS₀
  set R := ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
    χ a⁻¹ * (∑ n ∈ s, χ ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ)) with hR
  have hRle : ‖R‖ ≤ ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      ‖∑ n ∈ s, χ ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ)‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => ?_)
    rw [norm_mul]
    calc ‖χ a⁻¹‖ * ‖∑ n ∈ s, χ ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ)‖
        ≤ 1 * ‖∑ n ∈ s, χ ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ)‖ :=
          mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) (norm_nonneg _)
      _ = ‖∑ n ∈ s, χ ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ)‖ := one_mul _
  have hdiff : (((q.totient : ℝ) * A - S₀ : ℝ) : ℂ) = R := by
    push_cast
    linear_combination hAP
  have habs : |(q.totient : ℝ) * A - S₀| ≤ ‖R‖ := by
    rw [← hdiff, Complex.norm_real, Real.norm_eq_abs]
  have := neg_abs_le ((q.totient : ℝ) * A - S₀)
  linarith

/-- `K u⁵ ≤ exp(a u)` once `u ≥ 720 K / a⁶` (from `(a u)⁶/6! ≤ exp(a u)`). -/
lemma poly_le_exp6 (K a u : ℝ) (ha : 0 < a) (hu : 0 ≤ u)
    (hbig : 720 * K / a ^ 6 ≤ u) : K * u ^ 5 ≤ Real.exp (a * u) := by
  have h1 := Real.pow_div_factorial_le_exp (a * u) (mul_nonneg ha.le hu) 6
  have h720 : ((Nat.factorial 6 : ℕ) : ℝ) = 720 := by norm_num [Nat.factorial]
  rw [h720] at h1
  have ha6 : 0 < a ^ 6 := by positivity
  have h2 : 720 * K ≤ u * a ^ 6 := (div_le_iff₀ ha6).mp hbig
  have h3 : K * u ^ 5 ≤ (a * u) ^ 6 / 720 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 720)]
    have hu5 : 0 ≤ u ^ 5 := pow_nonneg hu 5
    calc K * u ^ 5 * 720 = (720 * K) * u ^ 5 := by ring
      _ ≤ (u * a ^ 6) * u ^ 5 := mul_le_mul_of_nonneg_right h2 hu5
      _ = (a * u) ^ 6 := by ring
  linarith

/-- `K L³ ≤ exp L` once `L ≥ 24 K` (from `L⁴/4! ≤ exp L`). -/
lemma poly_le_exp4 (K L : ℝ) (hL : 0 ≤ L) (hbig : 24 * K ≤ L) :
    K * L ^ 3 ≤ Real.exp L := by
  have h1 := Real.pow_div_factorial_le_exp L hL 4
  have h24 : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [h24] at h1
  have h3 : K * L ^ 3 ≤ L ^ 4 / 24 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 24)]
    have hL3 : 0 ≤ L ^ 3 := pow_nonneg hL 3
    calc K * L ^ 3 * 24 = (24 * K) * L ^ 3 := by ring
      _ ≤ L * L ^ 3 := mul_le_mul_of_nonneg_right hbig hL3
      _ = L ^ 4 := by ring
  linarith

set_option maxHeartbeats 4000000 in
-- One long assembly (constants, orthogonality, three error terms): well over the default budget.
open scoped Classical in
/-- **Siegel–Walfisz, dyadic lower bound.** There are absolute constants `C, c > 0` such that for
every modulus `q ≥ 1`, every residue `a` coprime to `q` and every `t ≥ exp(C q²)`,
`#{p prime : ⌊t⌋ < p ≤ ⌊2t⌋, p ≡ a (mod q)} ≥ c·t/(q log t)`. -/
theorem sw_dyadic_count :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, 1 ≤ q → ∀ a : ℕ, Nat.Coprime a q →
      ∀ t : ℝ, Real.exp (C * (q : ℝ) ^ 2) ≤ t →
        c * t / ((q : ℝ) * Real.log t) ≤
          (((Finset.Ioc ⌊t⌋₊ ⌊2 * t⌋₊).filter (fun p => p.Prime ∧ p % q = a % q)).card : ℝ) := by
  obtain ⟨c₅, C₅, X₅, hc₅, hC₅, hsw⟩ := psi_sharp_SW_rate 1 le_rfl
  set c₀ : ℝ := Real.log 4 / 12 with hc₀def
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hc₀ : 0 < c₀ := by rw [hc₀def]; positivity
  set K : ℝ := 6 * C₅ / c₀ with hKdef
  have hK : 0 ≤ K := by rw [hKdef]; positivity
  set U₁ : ℝ := 720 * K / c₅ ^ 6 with hU₁def
  have hU₁ : 0 ≤ U₁ := by rw [hU₁def]; positivity
  set C : ℝ := max (max 1 (Real.log 12005001))
    (max (Real.log (|X₅| + 1)) (max (U₁ ^ 10) (12288 / c₀ ^ 2))) with hCdef
  have hC1 : 1 ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC2 : Real.log 12005001 ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hC3 : Real.log (|X₅| + 1) ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC4 : U₁ ^ 10 ≤ C :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hC5 : 12288 / c₀ ^ 2 ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  refine ⟨C, by linarith, c₀ / 8, by positivity, ?_⟩
  intro q hq a hcop t ht
  haveI : NeZero q := ⟨by omega⟩
  -- ### scales
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hq2 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := one_le_pow₀ hq1
  have hqq : (q : ℝ) ≤ (q : ℝ) ^ 2 := by
    rw [sq]
    exact le_mul_of_one_le_left hq0.le hq1
  have htpos : 0 < t := lt_of_lt_of_le (Real.exp_pos _) ht
  set L := Real.log t with hLdef
  have htexp : Real.exp L = t := Real.exp_log htpos
  have hLCq : C * (q : ℝ) ^ 2 ≤ L := by
    have := Real.log_le_log (Real.exp_pos _) ht
    rwa [Real.log_exp] at this
  have hLC : C ≤ L := le_trans (le_mul_of_one_le_right (by linarith) hq2) hLCq
  have hLq2 : (q : ℝ) ^ 2 ≤ L := le_trans (le_mul_of_one_le_left (by positivity) hC1) hLCq
  have hL1 : 1 ≤ L := le_trans hC1 hLC
  have hL0 : 0 ≤ L := by linarith
  have hexp_ge : ∀ y : ℝ, y ≤ L → Real.exp y ≤ t := by
    intro y hy
    rw [← htexp]
    exact Real.exp_le_exp.mpr hy
  have ht_big : (12005001 : ℝ) ≤ t := by
    have := hexp_ge _ (le_trans hC2 hLC)
    rwa [Real.exp_log (by norm_num)] at this
  have htX : X₅ ≤ t := by
    have := hexp_ge _ (le_trans hC3 hLC)
    rw [Real.exp_log (by positivity)] at this
    linarith [le_abs_self X₅]
  have ht2 : (2 : ℝ) ≤ t := by linarith
  have hqt : (q : ℝ) ≤ t := by
    have := Real.add_one_le_exp L
    linarith
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2t : Real.log (2 * t) = Real.log 2 + L := Real.log_mul (by norm_num) htpos.ne'
  have hlog2t_le : Real.log (2 * t) ≤ 2 * L := by linarith
  have hlog2t_ge : L ≤ Real.log (2 * t) := by linarith
  have hlog2t0 : 0 ≤ Real.log (2 * t) := by linarith
  -- `u = (log t)^{1/10}`
  set u : ℝ := L ^ ((1 : ℝ) / 10) with hudef
  have hu0 : 0 ≤ u := Real.rpow_nonneg hL0 _
  have hu10 : u ^ 10 = L := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul hL0]
    norm_num
  have hqu : (q : ℝ) ≤ u ^ 5 := by
    have h : (q : ℝ) ^ 2 ≤ (u ^ 5) ^ 2 := by
      calc (q : ℝ) ^ 2 ≤ L := hLq2
        _ = (u ^ 5) ^ 2 := by rw [← hu10]; ring
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp h
  have huU : U₁ ≤ u := by
    have h : U₁ ^ 10 ≤ u ^ 10 := by rw [hu10]; exact le_trans hC4 hLC
    exact (pow_le_pow_iff_left₀ hU₁ hu0 (by norm_num)).mp h
  -- ### the window `s = (⌊t⌋, ⌊2t⌋]`
  have hfl : ⌊t⌋₊ ≤ ⌊2 * t⌋₊ := Nat.floor_le_floor (by linarith)
  set s : Finset ℕ := Finset.Ioc ⌊t⌋₊ ⌊2 * t⌋₊ with hs
  have hIco : Finset.Ico (⌊t⌋₊ + 1) (⌊2 * t⌋₊ + 1) = s := Finset.Ico_add_one_add_one_eq_Ioc _ _
  have hmem : ∀ n ∈ s, t < n ∧ (n : ℝ) ≤ 2 * t := by
    intro n hn
    rw [hs, Finset.mem_Ioc] at hn
    constructor
    · have h1 : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
      have h2 : (⌊t⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn.1
      linarith
    · exact le_trans (by exact_mod_cast hn.2) (Nat.floor_le (by linarith))
  -- ### the principal character: `ψ(s, χ₀) ≥ ∑_{p ∈ s} log p ≥ c₀ t`
  have hS₀ : c₀ * t ≤ ∑ n ∈ s, if IsUnit ((n : ℕ) : ZMod q) then vonMangoldt n else 0 := by
    have hcheb := sum_log_primes_dyadic_real t ht_big
    rw [hIco, Finset.sum_filter] at hcheb
    refine hcheb.trans (Finset.sum_le_sum fun n hn => ?_)
    by_cases hp : n.Prime
    · have hnq : q < n := by
        have h := (hmem n hn).1
        exact_mod_cast (lt_of_le_of_lt hqt h)
      have hunit : IsUnit ((n : ℕ) : ZMod q) := by
        rw [ZMod.isUnit_iff_coprime]
        refine (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun hd => ?_)
        have := Nat.le_of_dvd (by omega) hd
        omega
      rw [if_pos hp, if_pos hunit, vonMangoldt_apply_prime hp]
    · rw [if_neg hp]
      split_ifs
      · exact vonMangoldt_nonneg
      · exact le_rfl
  -- ### the non-principal characters: `‖ψ(s, χ)‖ ≤ 3 C₅ t e^{-c₅ u}`
  have hqlogt : (q : ℝ) ≤ Real.log t ^ (1 : ℝ) := by rw [Real.rpow_one, ← hLdef]; linarith
  have hqlog2t : (q : ℝ) ≤ Real.log (2 * t) ^ (1 : ℝ) := by rw [Real.rpow_one]; linarith
  have hE2 : Real.exp (-(c₅ * Real.log (2 * t) ^ ((1 : ℝ) / 10))) ≤ Real.exp (-(c₅ * u)) := by
    apply Real.exp_le_exp.mpr
    have h : u ≤ Real.log (2 * t) ^ ((1 : ℝ) / 10) :=
      Real.rpow_le_rpow hL0 hlog2t_ge (by norm_num)
    exact neg_le_neg (mul_le_mul_of_nonneg_left h hc₅.le)
  have hχ : ∀ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      ‖∑ n ∈ s, χ ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ)‖ ≤
        3 * C₅ * t * Real.exp (-(c₅ * u)) := by
    intro χ hχmem
    have hne := Finset.ne_of_mem_erase hχmem
    have hsplit : ∑ n ∈ s, χ ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ) =
        (∑ n ∈ Finset.range (⌊2 * t⌋₊ + 1), χ ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ)) -
          ∑ n ∈ Finset.range (⌊t⌋₊ + 1), χ ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ) := by
      rw [← Finset.sum_range_add_sum_Ico _ (show ⌊t⌋₊ + 1 ≤ ⌊2 * t⌋₊ + 1 by omega), hIco]
      ring
    have h1 := hsw (2 * t) (by linarith) q χ hne hqlog2t
    have h2 := hsw t htX q χ hne hqlogt
    have h1' := h1.trans (mul_le_mul_of_nonneg_left hE2 (by positivity : (0 : ℝ) ≤ C₅ * (2 * t)))
    have h2' : _ ≤ C₅ * t * Real.exp (-(c₅ * u)) := h2
    rw [hsplit]
    refine (norm_sub_le _ _).trans ?_
    linarith
  -- the number of non-principal characters is `< φ(q) ≤ q`
  have hcard : (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card = q.totient - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
  have hcardq : ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ) ≤ q := by
    rw [hcard]
    have : q.totient - 1 ≤ q := le_trans (Nat.sub_le _ _) (Nat.totient_le q)
    exact_mod_cast this
  -- `q · 3C₅ e^{-c₅u} ≤ c₀/2`
  have hKu := poly_le_exp6 K c₅ u hc₅ hu0 huU
  have hEE : Real.exp (-(c₅ * u)) * Real.exp (c₅ * u) = 1 := by
    rw [← Real.exp_add]
    simp
  have hsmall : 3 * C₅ * u ^ 5 * Real.exp (-(c₅ * u)) ≤ c₀ / 2 := by
    have h1 : c₀ / 2 * K = 3 * C₅ := by
      rw [hKdef]
      field_simp [hc₀.ne']
      ring
    have hEu : 0 ≤ Real.exp (-(c₅ * u)) := (Real.exp_pos _).le
    calc 3 * C₅ * u ^ 5 * Real.exp (-(c₅ * u)) = c₀ / 2 * (K * u ^ 5) * Real.exp (-(c₅ * u)) := by
          rw [← h1]
          ring
      _ ≤ c₀ / 2 * Real.exp (c₅ * u) * Real.exp (-(c₅ * u)) := by
          apply mul_le_mul_of_nonneg_right _ hEu
          exact mul_le_mul_of_nonneg_left hKu (by positivity)
      _ = c₀ / 2 * (Real.exp (-(c₅ * u)) * Real.exp (c₅ * u)) := by ring
      _ = c₀ / 2 := by rw [hEE, mul_one]
  have hRsum : ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      ‖∑ n ∈ s, χ ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ)‖ ≤ c₀ / 2 * t := by
    have hEu : 0 ≤ Real.exp (-(c₅ * u)) := (Real.exp_pos _).le
    calc ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          ‖∑ n ∈ s, χ ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ)‖
        ≤ ∑ _χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            3 * C₅ * t * Real.exp (-(c₅ * u)) := Finset.sum_le_sum hχ
      _ = ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ) *
            (3 * C₅ * t * Real.exp (-(c₅ * u))) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ u ^ 5 * (3 * C₅ * t * Real.exp (-(c₅ * u))) :=
          mul_le_mul_of_nonneg_right (le_trans hcardq hqu) (by positivity)
      _ = t * (3 * C₅ * u ^ 5 * Real.exp (-(c₅ * u))) := by ring
      _ ≤ t * (c₀ / 2) := mul_le_mul_of_nonneg_left hsmall htpos.le
      _ = c₀ / 2 * t := by ring
  -- ### orthogonality: `φ(q)·ψ(s; q, a) ≥ c₀ t / 2`
  have haU : IsUnit ((a : ℕ) : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr hcop
  have horth := orth_lower q ((a : ℕ) : ZMod q) haU s
  set A := ∑ n ∈ s, if ((a : ℕ) : ZMod q) = ((n : ZMod q)) then vonMangoldt n else 0 with hAdef
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun n _ => by
    split_ifs
    · exact vonMangoldt_nonneg
    · exact le_rfl
  have hφA : c₀ / 2 * t ≤ (q.totient : ℝ) * A := by linarith
  have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hqA : c₀ / 2 * t ≤ (q : ℝ) * A :=
    le_trans hφA (mul_le_mul_of_nonneg_right hφq hA0)
  -- ### from `ψ(s; q, a)` to the prime count: prime powers cost `≤ 2√(2t) log(2t)`
  set cnt : ℝ := ((s.filter (fun p => p.Prime ∧ p % q = a % q)).card : ℝ) with hcnt
  set D : ℝ := 2 * √(2 * t) * Real.log (2 * t) with hD
  have hA_upper : A ≤ Real.log (2 * t) * cnt + D := by
    have hterm : ∀ n ∈ s,
        (if ((a : ℕ) : ZMod q) = ((n : ZMod q)) then vonMangoldt n else 0) ≤
          (if (n.Prime ∧ n % q = a % q) then Real.log (2 * t) else 0) +
            (if ¬ n.Prime then vonMangoldt n else 0) := by
      intro n hn
      obtain ⟨hn1, hn2⟩ := hmem n hn
      by_cases heq : ((a : ℕ) : ZMod q) = ((n : ZMod q))
      · rw [if_pos heq]
        have hmod : n % q = a % q := ((ZMod.natCast_eq_natCast_iff' a n q).mp heq).symm
        by_cases hp : n.Prime
        · rw [if_pos ⟨hp, hmod⟩, if_neg (not_not.mpr hp), add_zero, vonMangoldt_apply_prime hp]
          exact Real.log_le_log (by linarith) hn2
        · rw [if_neg (fun h => hp h.1), if_pos hp, zero_add]
      · rw [if_neg heq]
        apply add_nonneg
        · split_ifs <;> first | exact hlog2t0 | exact le_rfl
        · split_ifs <;> first | exact vonMangoldt_nonneg | exact le_rfl
    have hnp : ∑ n ∈ s, (if ¬ n.Prime then vonMangoldt n else 0) ≤ D := by
      rw [← Finset.sum_filter]
      have hsub : s.filter (fun n => ¬ n.Prime) ⊆
          (Finset.Ioc 0 ⌊2 * t⌋₊).filter (fun n => ¬ n.Prime) := by
        intro n hn
        rw [hs, Finset.mem_filter, Finset.mem_Ioc] at hn
        rw [Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨by omega, hn.1.2⟩, hn.2⟩
      have h1 : ∑ n ∈ s.filter (fun n => ¬ n.Prime), vonMangoldt n ≤
          ∑ n ∈ (Finset.Ioc 0 ⌊2 * t⌋₊).filter (fun n => ¬ n.Prime), vonMangoldt n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => vonMangoldt_nonneg)
      have h2 := Chebyshev.psi_sub_theta_eq_sum_not_prime (2 * t)
      have h3 := Chebyshev.psi_sub_theta_le (x := 2 * t) (by linarith)
      rw [hD]
      linarith
    have hcntsum : ∑ n ∈ s, (if (n.Prime ∧ n % q = a % q) then Real.log (2 * t) else 0) =
        Real.log (2 * t) * cnt := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcnt, mul_comm]
    calc A ≤ ∑ n ∈ s, ((if (n.Prime ∧ n % q = a % q) then Real.log (2 * t) else 0) +
            (if ¬ n.Prime then vonMangoldt n else 0)) := Finset.sum_le_sum hterm
      _ = (∑ n ∈ s, (if (n.Prime ∧ n % q = a % q) then Real.log (2 * t) else 0)) +
            ∑ n ∈ s, (if ¬ n.Prime then vonMangoldt n else 0) := Finset.sum_add_distrib
      _ ≤ Real.log (2 * t) * cnt + D := by rw [hcntsum]; linarith
  -- `8 q √(2t) log(2t) ≤ c₀ t`, via squares and `512 L³ ≤ c₀² e^L`
  have hqD : (q : ℝ) * D ≤ c₀ * t / 4 := by
    have hsq2t : √(2 * t) ^ 2 = 2 * t := Real.sq_sqrt (by linarith)
    have hsqrt0 : 0 ≤ √(2 * t) := Real.sqrt_nonneg _
    have hpoly : 512 / c₀ ^ 2 * L ^ 3 ≤ Real.exp L :=
      poly_le_exp4 (512 / c₀ ^ 2) L hL0 (by
        have : 24 * (512 / c₀ ^ 2) = 12288 / c₀ ^ 2 := by ring
        rw [this]
        exact le_trans hC5 hLC)
    rw [htexp] at hpoly
    have hc₀sq : 0 < c₀ ^ 2 := by positivity
    have h512 : 512 * L ^ 3 ≤ c₀ ^ 2 * t := by
      have := mul_le_mul_of_nonneg_left hpoly hc₀sq.le
      have e : c₀ ^ 2 * (512 / c₀ ^ 2 * L ^ 3) = 512 * L ^ 3 := by
        field_simp [hc₀sq.ne']
      linarith
    have hlsq : Real.log (2 * t) ^ 2 ≤ 4 * L ^ 2 := by
      calc Real.log (2 * t) ^ 2 ≤ (2 * L) ^ 2 := pow_le_pow_left₀ hlog2t0 hlog2t_le 2
        _ = 4 * L ^ 2 := by ring
    have hql : (q : ℝ) ^ 2 * Real.log (2 * t) ^ 2 ≤ L * (4 * L ^ 2) :=
      mul_le_mul hLq2 hlsq (by positivity) hL0
    have hD0 : 0 ≤ D := by
      rw [hD]
      exact mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hlog2t0
    have hsqD : (4 * ((q : ℝ) * D)) ^ 2 ≤ (c₀ * t) ^ 2 := by
      have e : (4 * ((q : ℝ) * D)) ^ 2 =
          64 * (√(2 * t) ^ 2) * ((q : ℝ) ^ 2 * Real.log (2 * t) ^ 2) := by
        rw [hD]
        ring
      rw [e, hsq2t]
      have ht0 : 0 ≤ 2 * t := by linarith
      calc 64 * (2 * t) * ((q : ℝ) ^ 2 * Real.log (2 * t) ^ 2)
          ≤ 64 * (2 * t) * (L * (4 * L ^ 2)) :=
            mul_le_mul_of_nonneg_left hql (by positivity)
        _ = t * (512 * L ^ 3) := by ring
        _ ≤ t * (c₀ ^ 2 * t) := mul_le_mul_of_nonneg_left h512 htpos.le
        _ = (c₀ * t) ^ 2 := by ring
    have h := (sq_le_sq₀ (by positivity) (by positivity)).mp hsqD
    linarith
  -- ### conclusion
  have hcnt0 : 0 ≤ cnt := by rw [hcnt]; positivity
  have hmul : (q : ℝ) * A ≤ (q : ℝ) * (Real.log (2 * t) * cnt) + (q : ℝ) * D := by
    have := mul_le_mul_of_nonneg_left hA_upper hq0.le
    linarith
  have hlogcnt : (q : ℝ) * (Real.log (2 * t) * cnt) ≤ (q : ℝ) * (2 * L * cnt) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlog2t_le hcnt0) hq0.le
  have hfinal : c₀ / 8 * t ≤ cnt * ((q : ℝ) * L) := by linarith
  have hqL : 0 < (q : ℝ) * L := by positivity
  rw [div_le_iff₀ hqL]
  exact hfinal

end Principia.Common.SW
