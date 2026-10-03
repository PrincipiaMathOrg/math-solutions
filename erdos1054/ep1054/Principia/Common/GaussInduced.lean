/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

set_option autoImplicit false

/-!
# Gauss sums of induced Dirichlet characters, and the orthogonality relations over `ℂ`

Mathlib has the Gauss sum `gaussSum χ ψ`, the twisting identity for PRIMITIVE characters
(`gaussSum_mulShift_of_isPrimitive`) and the character orthogonality `sum_characters_eq`. It lacks
the two facts every major-arc argument uses: `|τ(χ)|² = N` for a primitive character modulo a
COMPOSITE `N` (Mathlib has it only for fields), and the value of `τ` on an induced character. This
file proves both, with `ψ = ZMod.stdAddChar` (`j ↦ e(j/N)`):

* `parseval` — Plancherel on `ZMod N`: `∑_a |∑_b f(b) e(ab/N)|² = N ∑_b |f(b)|²`.
* `norm_sq_gaussSum_primitive` — `|τ(χ)|² = N` for `χ` primitive mod `N`.
* `gaussSum_changeLevel_prime` — ONE PRIME STEP: for `χ` mod `q` and a prime `p`,
  `τ(χ ↑ pq) = −χ(p)·τ(χ)` (no primitivity needed). The proof splits `χ ↑ pq` as
  `χ(b mod q) − [p ∣ b]χ(b mod q)`; the first sum is killed by translation by `q`
  (`e(q/pq) ≠ 1`), the second is `χ(p)τ(χ)` after `b = pc`.
* `gaussSum_changeLevel` — THE INDUCED-CHARACTER FORMULA, by strong induction on the level:
  `τ(χ ↑ q) = μ(q/d)·χ(q/d)·τ(χ)` for every `χ` mod `d ∣ q`.
* `norm_sq_gaussSum_le` — `|τ(χ)|² ≤ μ²(q/q*)·q* ≤ q*` for EVERY `χ` mod `q` (`q*` the conductor).
  The printed "`|τ(χ)|² = μ²(q/q*)q*`" is only `≤`: `τ` also vanishes when `(q/q*, q*) > 1`
  (`printed_gauss_eq_false`: a nontrivial `χ` mod `3` induced to `9` has `τ = 0`, printed `3`).
* `gaussSum_one` — `τ(χ₀) = μ(q)` (the Ramanujan sum `c_q(1)`), from the formula at `d = 1`.
* The orthogonality relations in the form the circle method consumes:
  `sum_char_gaussSum` (`∑_χ τ(χ̄)χ(u)χ(m) = φ(q)·[m unit]·e(um/q)`, i.e. `eq:beatit` pointwise),
  `sum_norm_sq_char_comb` (`∑_a |∑_χ c_χ χ(a)|² = φ(q)∑_χ |c_χ|²`) and
  `sum_norm_sq_gaussSum_inv` (`∑_χ |τ(χ̄)|² = φ(q)²`).

Everything is campaign-agnostic: it is used by `TernaryGoldbach.PerArcSpine` (Helfgott's
`lem:drujal`, per-arc) and is what any `√(conductor)`-weighted major-arc bound needs.
-/

namespace Principia.Common.GaussInduced

open ZMod DirichletCharacter ArithmeticFunction

variable {N : ℕ} [NeZero N]

/-! ## The standard additive character -/

/-- `ψ(j) = e(j/N)` on natural numbers. -/
theorem std_natCast (j : ℕ) :
    stdAddChar (j : ZMod N) = Complex.exp (2 * Real.pi * Complex.I * j / N) := by
  have h := stdAddChar_coe (N := N) (j : ℤ)
  rw [Int.cast_natCast] at h
  rw [h]
  push_cast
  ring

/-- `ψ(t) = 1` only at `t = 0`. -/
theorem std_eq_one_iff (t : ZMod N) : stdAddChar t = 1 ↔ t = 0 := by
  rw [← (stdAddChar (N := N)).map_zero_eq_one, injective_stdAddChar.eq_iff]

/-- `|ψ(t)| = 1`. -/
theorem norm_std (t : ZMod N) : ‖stdAddChar t‖ = 1 := by
  rw [stdAddChar_apply]
  exact Circle.norm_coe _

/-- **Additive orthogonality**: `∑_a ψ(at) = N·[t = 0]`. -/
theorem sum_std_mul (t : ZMod N) :
    ∑ a : ZMod N, stdAddChar (a * t) = if t = 0 then (N : ℂ) else 0 := by
  split_ifs with h
  · simp [h, ZMod.card]
  · calc ∑ a : ZMod N, stdAddChar (a * t) = ∑ a : ZMod N, (stdAddChar.mulShift t) a := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [AddChar.mulShift_apply, mul_comm]
      _ = 0 := AddChar.sum_eq_zero_of_ne_one (isPrimitive_stdAddChar N h)

/-- **Plancherel on `ZMod N`**: `∑_a |∑_b f(b)ψ(ab)|² = N ∑_b |f(b)|²`. -/
theorem parseval (f : ZMod N → ℂ) :
    ∑ a : ZMod N, ‖∑ b, f b * stdAddChar (a * b)‖ ^ 2 = N * ∑ b, ‖f b‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  have key : ∀ a : ZMod N, ((‖∑ b, f b * stdAddChar (a * b)‖ : ℂ)) ^ 2 =
      ∑ b, ∑ c, f b * (starRingEnd ℂ) (f c) * stdAddChar (a * (b - c)) := by
    intro a
    rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    rw [(starRingEnd ℂ).map_mul, ← AddChar.map_neg_eq_conj, mul_sub, sub_eq_add_neg,
      AddChar.map_add_eq_mul]
    ring
  have step : ∀ b c : ZMod N,
      ∑ a : ZMod N, f b * (starRingEnd ℂ) (f c) * stdAddChar (a * (b - c)) =
        if b = c then (N : ℂ) * (‖f b‖ : ℂ) ^ 2 else 0 := by
    intro b c
    rw [← Finset.mul_sum, sum_std_mul]
    by_cases h : b = c
    · subst h
      rw [sub_self, if_pos rfl, if_pos rfl, Complex.mul_conj']
      ring
    · rw [if_neg (sub_ne_zero.mpr h), if_neg h, mul_zero]
  calc ∑ a : ZMod N, ((‖∑ b, f b * stdAddChar (a * b)‖ : ℂ)) ^ 2
      = ∑ a : ZMod N, ∑ b, ∑ c, f b * (starRingEnd ℂ) (f c) * stdAddChar (a * (b - c)) :=
        Finset.sum_congr rfl fun a _ => key a
    _ = ∑ b : ZMod N, ∑ c, ∑ a : ZMod N,
          f b * (starRingEnd ℂ) (f c) * stdAddChar (a * (b - c)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ b : ZMod N, ∑ c : ZMod N, if b = c then (N : ℂ) * (‖f b‖ : ℂ) ^ 2 else 0 := by
        simp_rw [step]
    _ = (N : ℂ) * ∑ b, (‖f b‖ : ℂ) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

/-! ## Counting units -/

/-- `∑_a [a unit] = φ(N)`. -/
theorem sum_isUnit (N : ℕ) [NeZero N] :
    ∑ a : ZMod N, (if IsUnit a then (1 : ℝ) else 0) = N.totient := by
  have h : ∀ a : ZMod N, (if IsUnit a then (1 : ℝ) else 0) = (1 : MulChar (ZMod N) ℝ) a := by
    intro a
    by_cases ha : IsUnit a
    · rw [if_pos ha, MulChar.one_apply ha]
    · rw [if_neg ha, MulChar.map_nonunit _ ha]
  simp_rw [h]
  rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]

/-- `|χ(a)|² = [a unit]`. -/
theorem norm_sq_char (χ : DirichletCharacter ℂ N) (a : ZMod N) :
    ‖χ a‖ ^ 2 = if IsUnit a then (1 : ℝ) else 0 := by
  by_cases ha : IsUnit a
  · rw [if_pos ha, ← ha.unit_spec, DirichletCharacter.unit_norm_eq_one, one_pow]
  · rw [if_neg ha, MulChar.map_nonunit _ ha, norm_zero]
    norm_num

/-- `∑_a |χ(a)|² = φ(N)`. -/
theorem sum_norm_sq_char (χ : DirichletCharacter ℂ N) :
    ∑ a : ZMod N, ‖χ a‖ ^ 2 = N.totient := by
  simp_rw [norm_sq_char]
  exact sum_isUnit N

/-! ## Primitive characters: `|τ(χ)|² = N` -/

/-- **`|τ(χ)|² = N` for a primitive character modulo any `N ≥ 1`**: Plancherel applied to `χ`,
whose Fourier transform is `χ̄·τ(χ)` (`gaussSum_mulShift_of_isPrimitive`). -/
theorem norm_sq_gaussSum_primitive {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    ‖gaussSum χ stdAddChar‖ ^ 2 = N := by
  have hP := parseval (N := N) (fun b => χ b)
  have hshift : ∀ a : ZMod N,
      ∑ b, χ b * stdAddChar (a * b) = χ⁻¹ a * gaussSum χ stdAddChar := by
    intro a
    rw [← gaussSum_mulShift_of_isPrimitive _ hχ a]
    simp only [gaussSum, AddChar.mulShift_apply]
  simp_rw [hshift, norm_mul, mul_pow] at hP
  rw [← Finset.sum_mul, sum_norm_sq_char, sum_norm_sq_char] at hP
  have hφ : (0 : ℝ) < N.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos N)
  have h2 : (N.totient : ℝ) * ‖gaussSum χ stdAddChar‖ ^ 2 = (N.totient : ℝ) * N := by
    rw [hP]
    ring
  exact mul_left_cancel₀ hφ.ne' h2

/-! ## One prime step up in level -/

/-- `χ ↑ pq` at `b`: `χ(b mod q)` unless `p ∣ b`. -/
theorem changeLevel_prime_apply {q p : ℕ} [NeZero q] [NeZero (p * q)] (hp : p.Prime)
    (χ : DirichletCharacter ℂ q) (b : ZMod (p * q)) :
    changeLevel (dvd_mul_left q p) χ b = if p ∣ b.val then 0 else χ (b.val : ZMod q) := by
  by_cases hb : IsUnit b
  · have hcop : Nat.Coprime b.val (p * q) := by
      rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
      exact hb
    have hnd : ¬ p ∣ b.val := fun hd =>
      hp.one_lt.ne' (Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd hd (dvd_mul_right p q)))
    rw [if_neg hnd]
    conv_lhs => rw [← hb.unit_spec]
    rw [changeLevel_eq_cast_of_dvd, hb.unit_spec, ZMod.cast_eq_val]
  · rw [MulChar.map_nonunit _ hb]
    split_ifs with hd
    · rfl
    · symm
      apply MulChar.map_nonunit
      intro hu
      apply hb
      rw [← ZMod.natCast_zmod_val b, ZMod.isUnit_iff_coprime]
      rw [ZMod.isUnit_iff_coprime] at hu
      exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hp).2 hd).symm hu

/-- The residue `b mod q` is invariant under `b ↦ b + q` in `ZMod (pq)`. -/
theorem val_add_q {q p : ℕ} [NeZero q] [NeZero (p * q)] (b : ZMod (p * q)) :
    (((b + (q : ZMod (p * q))).val : ℕ) : ZMod q) = (b.val : ZMod q) := by
  rw [← ZMod.cast_eq_val, ← ZMod.cast_eq_val, ZMod.cast_add (dvd_mul_left q p),
    ZMod.cast_natCast (dvd_mul_left q p), ZMod.natCast_self, add_zero]

/-- **Translation kills a lifted sum**: `∑_{b mod pq} g(b mod q)ψ(b) = 0` (`p ≥ 2`). -/
theorem sum_lift_std {q p : ℕ} [NeZero q] [NeZero (p * q)] (hp : p.Prime)
    (g : ZMod q → ℂ) : ∑ b : ZMod (p * q), g (b.val : ZMod q) * stdAddChar b = 0 := by
  set S := ∑ b : ZMod (p * q), g (b.val : ZMod q) * stdAddChar b with hS
  have hq0 : 0 < q := NeZero.pos q
  have hne : stdAddChar ((q : ℕ) : ZMod (p * q)) ≠ 1 := by
    rw [Ne, std_eq_one_iff, ZMod.natCast_eq_zero_iff]
    intro hd
    have h1 := Nat.le_of_dvd hq0 hd
    have h2 : 2 * q ≤ p * q := Nat.mul_le_mul_right q hp.two_le
    omega
  have hshift : S = S * stdAddChar ((q : ℕ) : ZMod (p * q)) := by
    conv_lhs => rw [hS, ← Equiv.sum_comp (Equiv.addRight ((q : ℕ) : ZMod (p * q)))]
    rw [hS, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Equiv.coe_addRight, val_add_q, AddChar.map_add_eq_mul]
    ring
  have h0 : S * (1 - stdAddChar ((q : ℕ) : ZMod (p * q))) = 0 := by
    rw [mul_sub, mul_one, ← hshift, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h).symm hne

/-- `ψ_{pq}(pc) = ψ_q(c)`. -/
theorem std_mul_prime {q p : ℕ} [NeZero q] [NeZero (p * q)] (hp : p.Prime) (c : ZMod q) :
    stdAddChar (((p * c.val : ℕ)) : ZMod (p * q)) = stdAddChar c := by
  conv_rhs => rw [← ZMod.natCast_zmod_val c]
  rw [std_natCast, std_natCast]
  congr 1
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  push_cast
  field_simp

/-- **The multiples of `p`**: `∑_{b mod pq, p ∣ b} χ(b mod q)ψ(b) = χ(p)τ(χ)`. -/
theorem sum_mult_prime {q p : ℕ} [NeZero q] [NeZero (p * q)] (hp : p.Prime)
    (χ : DirichletCharacter ℂ q) :
    ∑ b : ZMod (p * q), (if p ∣ b.val then χ (b.val : ZMod q) else 0) * stdAddChar b =
      χ p * gaussSum χ stdAddChar := by
  have hlt : ∀ c : ZMod q, p * c.val < p * q := fun c =>
    Nat.mul_lt_mul_of_pos_left (ZMod.val_lt c) hp.pos
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter, gaussSum, Finset.mul_sum]
  symm
  refine Finset.sum_nbij' (fun c => ((p * c.val : ℕ) : ZMod (p * q)))
    (fun b => ((b.val / p : ℕ) : ZMod q)) ?_ ?_ ?_ ?_ ?_
  · intro c _
    rw [Finset.mem_filter, ZMod.val_cast_of_lt (hlt c)]
    exact ⟨Finset.mem_univ _, dvd_mul_right _ _⟩
  · intro b _
    exact Finset.mem_univ _
  · intro c _
    rw [ZMod.val_cast_of_lt (hlt c), Nat.mul_div_cancel_left _ hp.pos, ZMod.natCast_zmod_val]
  · intro b hb
    have hd : p ∣ b.val := (Finset.mem_filter.1 hb).2
    have hbl : b.val / p < q := by
      rw [Nat.div_lt_iff_lt_mul hp.pos]
      calc b.val < p * q := ZMod.val_lt b
        _ = q * p := mul_comm p q
    rw [ZMod.val_cast_of_lt hbl, Nat.mul_div_cancel' hd, ZMod.natCast_zmod_val]
  · intro c _
    rw [ZMod.val_cast_of_lt (hlt c), std_mul_prime hp, Nat.cast_mul, ZMod.natCast_zmod_val,
      map_mul]
    ring

/-- **One prime step**: `τ(χ ↑ pq) = −χ(p)·τ(χ)` for every `χ` mod `q` and every prime `p`. -/
theorem gaussSum_changeLevel_prime {q p : ℕ} [NeZero q] [NeZero (p * q)] (hp : p.Prime)
    (χ : DirichletCharacter ℂ q) :
    gaussSum (changeLevel (dvd_mul_left q p) χ) (stdAddChar (N := p * q)) =
      -χ p * gaussSum χ stdAddChar := by
  rw [gaussSum]
  simp_rw [changeLevel_prime_apply hp]
  have h : ∀ b : ZMod (p * q), (if p ∣ b.val then 0 else χ (b.val : ZMod q)) * stdAddChar b =
      χ (b.val : ZMod q) * stdAddChar b -
        (if p ∣ b.val then χ (b.val : ZMod q) else 0) * stdAddChar b := by
    intro b
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun b _ => h b, Finset.sum_sub_distrib, sum_lift_std hp,
    sum_mult_prime hp]
  ring

/-! ## The induced-character formula -/

/-- The Möbius/character bookkeeping of one prime step: with `m = q'/d`,
`−χ'(p)·μ(m)χ(m) = μ(pm)χ(pm)`, where `χ' = χ ↑ q'`. -/
theorem step_coeff {d q' p : ℕ} [NeZero d] [NeZero q'] (hp : p.Prime) (hd : d ∣ q')
    (χ : DirichletCharacter ℂ d) :
    -changeLevel hd χ p * ((moebius (q' / d) : ℂ) * χ ((q' / d : ℕ) : ZMod d)) =
      (moebius (p * (q' / d)) : ℂ) * χ ((p * (q' / d) : ℕ) : ZMod d) := by
  set m := q' / d with hm
  have hq' : q' = d * m := (Nat.mul_div_cancel' hd).symm
  by_cases hpq : p ∣ q'
  · have hnu : ¬ IsUnit ((p : ℕ) : ZMod q') := by
      rw [ZMod.isUnit_iff_coprime]
      intro hc
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc hpq)
    rw [MulChar.map_nonunit _ hnu]
    by_cases hpm : p ∣ m
    · have hns : ¬ Squarefree (p * m) := by
        intro hsq
        obtain ⟨k, hk⟩ := hpm
        have hpp : p * p ∣ p * m := ⟨k, by rw [hk]; ring⟩
        exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsq p hpp))
      rw [moebius_eq_zero_of_not_squarefree hns]
      simp
    · have hpd : p ∣ d := by
        rw [hq'] at hpq
        exact (hp.dvd_mul.mp hpq).resolve_right hpm
      have hnd : ¬ IsUnit ((p : ℕ) : ZMod d) := by
        rw [ZMod.isUnit_iff_coprime]
        intro hc
        exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc hpd)
      rw [Nat.cast_mul, map_mul χ, MulChar.map_nonunit _ hnd]
      ring
  · have hcop : Nat.Coprime p q' := (Nat.Prime.coprime_iff_not_dvd hp).2 hpq
    have hpm : Nat.Coprime p m := Nat.Coprime.coprime_dvd_right ⟨d, by rw [hq']; ring⟩ hcop
    have hcl : changeLevel hd χ ((p : ℕ) : ZMod q') = χ ((p : ℕ) : ZMod d) := by
      have h := changeLevel_eq_cast_of_dvd' χ hd (a := (p : ℤ))
        (Int.isCoprime_iff_gcd_eq_one.mpr (by rw [Int.gcd_natCast_natCast]; exact hcop))
      simpa only [Int.cast_natCast] using h
    rw [hcl, isMultiplicative_moebius.map_mul_of_coprime hpm, moebius_apply_prime hp,
      Nat.cast_mul, map_mul χ]
    push_cast
    ring

/-- **THE INDUCED-CHARACTER FORMULA**: for `χ` mod `d` and `d ∣ q`,
`τ(χ ↑ q) = μ(q/d)·χ(q/d)·τ(χ)`. Strong induction on `q`, one prime at a time
(`gaussSum_changeLevel_prime`). No primitivity is assumed. -/
theorem gaussSum_changeLevel {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) :
    ∀ (q : ℕ) [NeZero q] (h : d ∣ q),
      gaussSum (changeLevel h χ) (stdAddChar (N := q)) =
        (moebius (q / d) : ℂ) * χ ((q / d : ℕ) : ZMod d) * gaussSum χ stdAddChar := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro _ h
    by_cases hqd : q = d
    · subst hqd
      rw [Nat.div_self (NeZero.pos q), moebius_apply_one, Nat.cast_one, map_one,
        changeLevel_self]
      push_cast
      ring
    · have hm1 : q / d ≠ 1 := by
        intro h1
        exact hqd ((Nat.div_eq_iff_eq_mul_left (NeZero.pos d) h).mp h1 |>.trans (one_mul d))
      obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
      have hdp : d * p ∣ q := Nat.mul_dvd_of_dvd_div h hpm
      obtain ⟨q', rfl⟩ : p ∣ q := Dvd.dvd.trans (Dvd.intro_left d rfl) hdp
      have hd' : d ∣ q' := by
        have h2 : p * d ∣ p * q' := by rw [mul_comm p d]; exact hdp
        exact Nat.dvd_of_mul_dvd_mul_left hp.pos h2
      have hq'0 : q' ≠ 0 := by
        intro h0
        exact NeZero.ne (p * q') (by rw [h0, mul_zero])
      haveI : NeZero q' := ⟨hq'0⟩
      have hlt : q' < p * q' := by
        have := hp.two_le
        have := Nat.pos_of_ne_zero hq'0
        nlinarith
      have htrans : changeLevel h χ = changeLevel (dvd_mul_left q' p) (changeLevel hd' χ) :=
        changeLevel_trans χ hd' (dvd_mul_left q' p)
      rw [htrans, gaussSum_changeLevel_prime hp, ih q' hlt hd', Nat.mul_div_assoc p hd']
      rw [← step_coeff hp hd' χ]
      ring

/-- **`|τ(χ)|² ≤ μ²(q/q*)·q*`** for EVERY Dirichlet character `χ` mod `q` (`q*` its conductor):
the formula at `χ = χ* ↑ q` and `|τ(χ*)|² = q*`. -/
theorem norm_sq_gaussSum_le_moebius (χ : DirichletCharacter ℂ N) :
    ‖gaussSum χ stdAddChar‖ ^ 2 ≤
      ((moebius (N / χ.conductor) : ℤ) : ℝ) ^ 2 * χ.conductor := by
  haveI : NeZero χ.conductor := ⟨conductor_ne_zero χ⟩
  conv_lhs => rw [← χ.changeLevel_primitiveCharacter]
  rw [gaussSum_changeLevel χ.primitiveCharacter N χ.conductor_dvd_level, norm_mul, norm_mul,
    mul_pow, mul_pow, norm_sq_gaussSum_primitive χ.primitiveCharacter_isPrimitive]
  have h1 : ‖χ.primitiveCharacter ((N / χ.conductor : ℕ) : ZMod χ.conductor)‖ ^ 2 ≤ 1 := by
    have := DirichletCharacter.norm_le_one χ.primitiveCharacter
      ((N / χ.conductor : ℕ) : ZMod χ.conductor)
    nlinarith [norm_nonneg (χ.primitiveCharacter ((N / χ.conductor : ℕ) : ZMod χ.conductor))]
  have h2 : ‖((moebius (N / χ.conductor) : ℤ) : ℂ)‖ ^ 2 =
      ((moebius (N / χ.conductor) : ℤ) : ℝ) ^ 2 := by
    rw [Complex.norm_intCast, sq_abs]
  rw [h2]
  have h3 : (0 : ℝ) ≤ ((moebius (N / χ.conductor) : ℤ) : ℝ) ^ 2 * χ.conductor := by positivity
  nlinarith

/-- **`|τ(χ)|² ≤ q*`** (the conductor) for every `χ` mod `q`. -/
theorem norm_sq_gaussSum_le (χ : DirichletCharacter ℂ N) :
    ‖gaussSum χ stdAddChar‖ ^ 2 ≤ χ.conductor := by
  refine le_trans (norm_sq_gaussSum_le_moebius χ) ?_
  have hm : ((moebius (N / χ.conductor) : ℤ) : ℝ) ^ 2 ≤ 1 := by
    have h := abs_moebius_le_one (n := N / χ.conductor)
    have h' : |((moebius (N / χ.conductor) : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast h
    nlinarith [abs_nonneg ((moebius (N / χ.conductor) : ℤ) : ℝ), sq_abs
      ((moebius (N / χ.conductor) : ℤ) : ℝ)]
  have hc : (0 : ℝ) ≤ χ.conductor := Nat.cast_nonneg _
  nlinarith

/-- **The printed `|τ(χ)|² = μ²(q/q*)q*` (`ternvin.tex` 1261) is FALSE; only `≤` holds.** A
concrete counterexample: `χ` a nontrivial character mod `3`, induced to level `9`. Its conductor is
`3`, so the printed value is `μ(3)²·3 = 3`, but `τ(χ ↑ 9) = μ(3)χ(3)τ(χ) = 0` since `χ(3) = 0`. -/
theorem printed_gauss_eq_false : ∃ χ : DirichletCharacter ℂ 9,
    ‖gaussSum χ stdAddChar‖ ^ 2 ≠ ((moebius (9 / χ.conductor) : ℤ) : ℝ) ^ 2 * χ.conductor := by
  have h2 : (2 : ZMod 3) ≠ 1 := by decide
  obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ h2
  have hu : IsUnit (2 : ZMod 3) := ⟨⟨2, 2, by decide, by decide⟩, rfl⟩
  have hne : χ ≠ 1 := fun h => hχ (by rw [h]; exact MulChar.one_apply hu)
  have hc3 : χ.conductor = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp χ.conductor_dvd_level with h | h
    · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h) hne
    · exact h
  have h39 : (3 : ℕ) ∣ 9 := by norm_num
  refine ⟨changeLevel h39 χ, ?_⟩
  rw [DirichletCharacter.conductor_changeLevel, hc3, gaussSum_changeLevel χ 9 h39]
  have h93 : (9 : ℕ) / 3 = 3 := by norm_num
  have h30 : ((3 : ℕ) : ZMod 3) = 0 := ZMod.natCast_self 3
  rw [h93, h30, MulChar.map_zero, mul_zero, zero_mul, norm_zero,
    moebius_apply_prime Nat.prime_three]
  norm_num

/-- `τ` of the trivial character mod `1` is `1`. -/
theorem gaussSum_one_level_one :
    gaussSum (1 : DirichletCharacter ℂ 1) (stdAddChar (N := 1)) = 1 := by
  rw [gaussSum, Fintype.sum_subsingleton _ 0, MulChar.one_apply (isUnit_of_subsingleton _),
    AddChar.map_zero_eq_one, one_mul]

/-- **`τ(χ₀) = μ(q)`** (the Ramanujan sum `c_q(1)`): the formula at `d = 1`. -/
theorem gaussSum_one : gaussSum (1 : DirichletCharacter ℂ N) stdAddChar = moebius N := by
  have h1 : (1 : DirichletCharacter ℂ N) = changeLevel (one_dvd N) (1 : DirichletCharacter ℂ 1) :=
    (map_one _).symm
  rw [h1, gaussSum_changeLevel (1 : DirichletCharacter ℂ 1) N (one_dvd N),
    gaussSum_one_level_one, Nat.div_one,
    MulChar.one_apply (isUnit_of_subsingleton _)]
  ring

/-! ## Orthogonality, in the form the circle method consumes -/

/-- **`eq:beatit`, pointwise**: for a unit `u` and any `m`,
`∑_χ τ(χ̄)χ(u)χ(m) = φ(N)·[m unit]·ψ(um)`. -/
theorem sum_char_gaussSum (u : (ZMod N)ˣ) (m : ZMod N) :
    ∑ χ : DirichletCharacter ℂ N, gaussSum χ⁻¹ stdAddChar * (χ u * χ m) =
      if IsUnit m then (N.totient : ℂ) * stdAddChar ((u : ZMod N) * m) else 0 := by
  split_ifs with hm
  · set w : (ZMod N)ˣ := u * hm.unit with hw
    have hwv : (w : ZMod N) = u * m := by rw [hw, Units.val_mul, hm.unit_spec]
    have h1 : ∀ χ : DirichletCharacter ℂ N, gaussSum χ⁻¹ stdAddChar * (χ u * χ m) =
        gaussSum χ⁻¹ (stdAddChar.mulShift (w : ZMod N)) := by
      intro χ
      rw [← map_mul, ← hwv, gaussSum_mulShift_eq χ⁻¹ stdAddChar w, inv_inv]
      ring
    simp_rw [h1]
    simp only [gaussSum, AddChar.mulShift_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    have h2 : ∀ b : ZMod N, ∑ χ : DirichletCharacter ℂ N, χ⁻¹ b =
        if b = 1 then (N.totient : ℂ) else 0 := by
      intro b
      rw [← DirichletCharacter.sum_characters_eq ℂ b]
      exact Fintype.sum_equiv (Equiv.inv _) _ _ (fun χ => rfl)
    simp_rw [h2, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), mul_one, hwv]
  · refine Finset.sum_eq_zero fun χ _ => ?_
    rw [MulChar.map_nonunit _ hm, mul_zero, mul_zero]

/-- **Orthogonality of characters (Parseval on `(ZMod N)ˣ`)**:
`∑_a |∑_χ c_χ χ(a)|² = φ(N)·∑_χ |c_χ|²`. -/
theorem sum_norm_sq_char_comb (c : DirichletCharacter ℂ N → ℂ) :
    ∑ a : ZMod N, ‖∑ χ, c χ * χ a‖ ^ 2 = N.totient * ∑ χ, ‖c χ‖ ^ 2 := by
  classical
  apply Complex.ofReal_injective
  push_cast
  have key : ∀ a : ZMod N, ((‖∑ χ, c χ * χ a‖ : ℂ)) ^ 2 =
      ∑ χ, ∑ ψ, c χ * (starRingEnd ℂ) (c ψ) * (χ * ψ⁻¹) a := by
    intro a
    rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun χ _ => Finset.sum_congr rfl fun ψ _ => ?_
    have hs : (starRingEnd ℂ) (ψ a) = ψ⁻¹ a := MulChar.star_apply' ψ a
    rw [(starRingEnd ℂ).map_mul, hs, MulChar.mul_apply]
    ring
  have horth : ∀ χ ψ : DirichletCharacter ℂ N,
      ∑ a : ZMod N, c χ * (starRingEnd ℂ) (c ψ) * (χ * ψ⁻¹) a =
        if χ = ψ then (N.totient : ℂ) * (‖c χ‖ : ℂ) ^ 2 else 0 := by
    intro χ ψ
    rw [← Finset.mul_sum]
    by_cases h : χ = ψ
    · subst h
      rw [if_pos rfl, mul_inv_cancel, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient,
        Complex.mul_conj']
      ring
    · rw [if_neg h, MulChar.sum_eq_zero_of_ne_one (fun h1 => h (mul_inv_eq_one.mp h1)),
        mul_zero]
  calc ∑ a : ZMod N, ((‖∑ χ, c χ * χ a‖ : ℂ)) ^ 2
      = ∑ a : ZMod N, ∑ χ, ∑ ψ, c χ * (starRingEnd ℂ) (c ψ) * (χ * ψ⁻¹) a :=
        Finset.sum_congr rfl fun a _ => key a
    _ = ∑ χ, ∑ ψ, ∑ a : ZMod N, c χ * (starRingEnd ℂ) (c ψ) * (χ * ψ⁻¹) a := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun χ _ => Finset.sum_comm
    _ = ∑ χ : DirichletCharacter ℂ N, ∑ ψ : DirichletCharacter ℂ N,
          if χ = ψ then (N.totient : ℂ) * (‖c χ‖ : ℂ) ^ 2 else 0 := by
        simp_rw [horth]
    _ = (N.totient : ℂ) * ∑ χ, (‖c χ‖ : ℂ) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun χ _ => by rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

/-- **`∑_χ |τ(χ̄)|² = φ(N)²`**: `sum_norm_sq_char_comb` at `c_χ = τ(χ̄)`, whose combination is
`φ(N)·[a unit]·ψ(a)` by `sum_char_gaussSum`. -/
theorem sum_norm_sq_gaussSum_inv :
    ∑ χ : DirichletCharacter ℂ N, ‖gaussSum χ⁻¹ stdAddChar‖ ^ 2 = (N.totient : ℝ) ^ 2 := by
  have h := sum_norm_sq_char_comb (N := N) (fun χ => gaussSum χ⁻¹ stdAddChar)
  have hpt : ∀ a : ZMod N, ‖∑ χ : DirichletCharacter ℂ N, gaussSum χ⁻¹ stdAddChar * χ a‖ ^ 2 =
      (N.totient : ℝ) ^ 2 * (if IsUnit a then (1 : ℝ) else 0) := by
    intro a
    by_cases ha : IsUnit a
    · have h1 := sum_char_gaussSum (N := N) ha.unit 1
      simp only [map_one, mul_one, if_pos isUnit_one, ha.unit_spec] at h1
      rw [h1, if_pos ha, norm_mul, norm_std, Complex.norm_natCast]
      ring
    · rw [if_neg ha, Finset.sum_eq_zero fun χ _ => by rw [MulChar.map_nonunit _ ha, mul_zero]]
      simp
  simp_rw [hpt] at h
  rw [← Finset.mul_sum, sum_isUnit] at h
  have hφ : (0 : ℝ) < N.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos N)
  have h2 : (N.totient : ℝ) * ∑ χ : DirichletCharacter ℂ N, ‖gaussSum χ⁻¹ stdAddChar‖ ^ 2 =
      (N.totient : ℝ) * (N.totient : ℝ) ^ 2 := by
    rw [← h]
    ring
  exact mul_left_cancel₀ hφ.ne' h2

end Principia.Common.GaussInduced
