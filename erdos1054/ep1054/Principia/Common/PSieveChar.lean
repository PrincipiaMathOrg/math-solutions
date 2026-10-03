/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.PSieveArcs
import Principia.Common.GaussInduced

set_option autoImplicit false

/-!
# Bombieri's character identity for `∑_{(b,q)=1} |S(b/q + β)|²`, lifted to one common modulus

For coefficients `aₙ` supported on `n` coprime to `m` (`ternvin.tex` 2383-2389, Bombieri,
Astérisque 18, pp. 24-25, and 2432-2445, Selberg's identity in the proof of Thm. 7A):

* `char_sum_eq` — `∑_{b mod m} χ̄(b) S(b/m + β) = τ(χ̄)·S_χ(β)`, `S_χ(β) = ∑ aₙχ(n)e(nβ)`. This
  single identity is BOTH of the source's steps: the decomposition of `∑_b |S(b/m+β)|²` into
  characters, and Selberg's `χ̄(r)χ(n)τ(χ̄)μ(r) = ∑_{b mod qr} χ̄(b)e(nb/qr)`, which is its
  instance for a character induced from a primitive one mod `q` (`τ(χ̄ ↑ qr) = μ(r)χ̄(r)τ(χ̄)`,
  `GaussInduced.gaussSum_changeLevel`).
* `sum_char_normsq` — orthogonality: `∑_χ |∑_b χ̄(b)f(b)|² = φ(m)∑_{b unit}|f(b)|²`.
* `normsq_gauss_inv` — `|τ(χ̄)|² = μ²(m/d)·[(m/d, d) = 1]·d`, `d` the conductor.
* `tS_eq` — for `m ∣ M` and `aₙ` supported on `n` coprime to `M`:
  `T_m(β) = ∑_{ψ mod M} κ(m, ψ)·|S_ψ(β)|²`, `κ(m,ψ) = [d ∣ m]·μ²(m/d)[(m/d,d)=1]·d/φ(m)`,
  `d = cond ψ`. Lifting every modulus to ONE modulus `M` indexes the whole family of moduli by a
  single set of characters: a character `χ mod m` and its lift `ψ mod M` have the same `S`, and
  the lift is a bijection onto `{ψ : cond ψ ∣ m}` (`changeLevel_injective`,
  `changeLevel_primitiveCharacter`). This is what lets `prop:bellen` swap the sum over moduli
  with the sum over primitive characters without a dependent reindexing.
-/

namespace Principia.Common.PSieve

open ZMod DirichletCharacter ArithmeticFunction Principia.Common.Goldbach
open scoped ArithmeticFunction.Moebius

/-- **`S_χ(β) = ∑ₙ aₙ χ(n) e(nβ)`**. -/
noncomputable def eSc (a : ℕ → ℂ) {N : ℕ} (χ : DirichletCharacter ℂ N) (β : ℝ) : ℂ :=
  ∑' n : ℕ, a n * χ n * e ((n : ℝ) * β)

/-- **`κ(m, ψ) = [d ∣ m]·μ²(m/d)·[(m/d, d) = 1]·d/φ(m)`**, `d = cond ψ`. -/
noncomputable def kap (m : ℕ) {M : ℕ} (ψ : DirichletCharacter ℂ M) : ℝ :=
  if ψ.conductor ∣ m then
    ((μ (m / ψ.conductor) : ℤ) : ℝ) ^ 2 *
      (if Nat.Coprime (m / ψ.conductor) ψ.conductor then 1 else 0) * ψ.conductor / m.totient
  else 0

/-- `κ ≥ 0`. -/
theorem kap_nonneg (m : ℕ) {M : ℕ} (ψ : DirichletCharacter ℂ M) : 0 ≤ kap m ψ := by
  unfold kap
  split_ifs <;> positivity

/-! ## The identity `∑_b χ̄(b)S(b/m + β) = τ(χ̄)S_χ(β)` -/

/-- **`e(n·b/m) = ψ_m(nb)`** for `b ∈ ZMod m`. -/
theorem e_std (m : ℕ) [NeZero m] (n : ℕ) (b : ZMod m) :
    e ((n : ℝ) * ((b.val : ℝ) / m)) = stdAddChar ((n : ZMod m) * b) := by
  have h1 : (n : ZMod m) * b = ((n * b.val : ℕ) : ZMod m) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [h1, GaussInduced.std_natCast]
  unfold e
  congr 1
  push_cast
  ring

/-- **`∑_b χ̄(b)ψ_m(nb) = χ(n)τ(χ̄)`** for `n` coprime to `m`. -/
theorem sum_inv_std (m : ℕ) [NeZero m] (χ : DirichletCharacter ℂ m) (n : ℕ)
    (hn : Nat.Coprime n m) :
    ∑ b : ZMod m, χ⁻¹ b * stdAddChar ((n : ZMod m) * b) =
      χ n * gaussSum χ⁻¹ stdAddChar := by
  have h := gaussSum_mulShift_eq χ⁻¹ stdAddChar (ZMod.unitOfCoprime n hn)
  rw [inv_inv, ZMod.coe_unitOfCoprime] at h
  rw [← h, gaussSum]
  rfl

/-- **Bombieri / Selberg**: for `aₙ` supported on `n` coprime to `m`,
`∑_{b mod m} χ̄(b)S(b/m + β) = τ(χ̄)·S_χ(β)`. -/
theorem char_sum_eq (a : ℕ → ℂ) (ha : Summable fun n => ‖a n‖) (m : ℕ) [NeZero m]
    (hcop : ∀ n : ℕ, a n ≠ 0 → Nat.Coprime n m) (χ : DirichletCharacter ℂ m) (β : ℝ) :
    ∑ b : ZMod m, χ⁻¹ b * eS a ((b.val : ℝ) / m + β) =
      gaussSum χ⁻¹ stdAddChar * eSc a χ β := by
  have hs : ∀ b : ZMod m, Summable fun n : ℕ =>
      χ⁻¹ b * (a n * e ((n : ℝ) * ((b.val : ℝ) / m + β))) := by
    intro b
    refine Summable.mul_left _ (summable_norm_iff.mp (ha.congr fun n => ?_))
    rw [norm_mul, e_norm, mul_one]
  unfold eS eSc
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun b _ => hs b)]
  refine tsum_congr fun n => ?_
  by_cases h0 : a n = 0
  · simp [h0]
  have hcn := hcop n h0
  have e1 : ∀ b : ZMod m, χ⁻¹ b * (a n * e ((n : ℝ) * ((b.val : ℝ) / m + β))) =
      a n * e ((n : ℝ) * β) * (χ⁻¹ b * stdAddChar ((n : ZMod m) * b)) := by
    intro b
    rw [← e_std, mul_add, ← e_add]
    ring
  simp_rw [e1]
  rw [← Finset.mul_sum, sum_inv_std m χ n hcn]
  ring

/-! ## Orthogonality -/

/-- `∑_χ χ̄(b)χ(c) = φ(m)·[b unit]·[c = b]`. -/
theorem sum_inv_mul (m : ℕ) [NeZero m] (b c : ZMod m) :
    ∑ χ : DirichletCharacter ℂ m, χ⁻¹ b * χ c =
      if IsUnit b then (if c = b then (m.totient : ℂ) else 0) else 0 := by
  split_ifs with hb hcb
  · subst hcb
    have h1 : ∀ χ : DirichletCharacter ℂ m, χ⁻¹ c * χ c = 1 := by
      intro χ
      rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply hb]
    simp_rw [h1]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ m
    rw [Nat.card_eq_fintype_card] at this
    rw [this]
  · obtain ⟨u, rfl⟩ := hb
    have h1 : ∀ χ : DirichletCharacter ℂ m, χ⁻¹ u * χ c = χ ((↑u⁻¹ : ZMod m) * c) := by
      intro χ
      have hc : c = (u : ZMod m) * ((↑u⁻¹ : ZMod m) * c) := by
        rw [← mul_assoc, Units.mul_inv, one_mul]
      conv_lhs => rw [hc]
      rw [map_mul, ← mul_assoc, ← MulChar.mul_apply, inv_mul_cancel,
        MulChar.one_apply u.isUnit, one_mul]
    simp_rw [h1]
    rw [DirichletCharacter.sum_characters_eq, if_neg]
    intro h2
    apply hcb
    have h3 : (u : ZMod m) * ((↑u⁻¹ : ZMod m) * c) = (u : ZMod m) := by rw [h2, mul_one]
    rwa [← mul_assoc, Units.mul_inv, one_mul] at h3
  · refine Finset.sum_eq_zero fun χ _ => ?_
    have : χ⁻¹ b = 0 := MulChar.map_nonunit _ hb
    rw [this, zero_mul]

/-- **Orthogonality (Parseval on `(ZMod m)ˣ`)**: `∑_χ |∑_b χ̄(b)f(b)|² = φ(m)∑_{b unit}|f(b)|²`. -/
theorem sum_char_normsq (m : ℕ) [NeZero m] (f : ZMod m → ℂ) :
    ∑ χ : DirichletCharacter ℂ m, ‖∑ b, χ⁻¹ b * f b‖ ^ 2 =
      m.totient * ∑ b : ZMod m, (if IsUnit b then ‖f b‖ ^ 2 else 0) := by
  apply Complex.ofReal_injective
  push_cast
  have key : ∀ χ : DirichletCharacter ℂ m, ((‖∑ b, χ⁻¹ b * f b‖ : ℂ)) ^ 2 =
      ∑ b, ∑ c, f b * (starRingEnd ℂ) (f c) * (χ⁻¹ b * χ c) := by
    intro χ
    rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    have hs : (starRingEnd ℂ) (χ⁻¹ c) = χ c := by
      have h0 : (starRingEnd ℂ) (χ⁻¹ c) = χ⁻¹⁻¹ c := MulChar.star_apply' χ⁻¹ c
      rw [h0, inv_inv]
    rw [(starRingEnd ℂ).map_mul, hs]
    ring
  simp_rw [key]
  rw [Finset.sum_comm]
  have step : ∀ b : ZMod m, ∑ χ : DirichletCharacter ℂ m,
      ∑ c, f b * (starRingEnd ℂ) (f c) * (χ⁻¹ b * χ c) =
        if IsUnit b then (m.totient : ℂ) * (‖f b‖ : ℂ) ^ 2 else 0 := by
    intro b
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_inv_mul]
    split_ifs with hb
    · simp_rw [mul_ite, mul_zero]
      rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), Complex.mul_conj']
      ring
    · simp
  simp_rw [step]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp

/-! ## `|τ(χ̄)|²` -/

/-- **`|τ(χ̄)|² = μ²(m/d)·[(m/d, d) = 1]·d`**, `d = cond χ` (the induced-character formula
`GaussInduced.gaussSum_changeLevel` and `|τ| ² = d` for primitive characters). -/
theorem normsq_gauss_inv (m : ℕ) [NeZero m] (χ : DirichletCharacter ℂ m) :
    ‖gaussSum χ⁻¹ stdAddChar‖ ^ 2 =
      ((μ (m / χ.conductor) : ℤ) : ℝ) ^ 2 *
        (if Nat.Coprime (m / χ.conductor) χ.conductor then 1 else 0) * χ.conductor := by
  have hci := DirichletCharacter.conductor_inv χ
  haveI : NeZero χ⁻¹.conductor := ⟨conductor_ne_zero χ⁻¹⟩
  have hform := GaussInduced.gaussSum_changeLevel χ⁻¹.primitiveCharacter m
    χ⁻¹.conductor_dvd_level
  rw [χ⁻¹.changeLevel_primitiveCharacter] at hform
  rw [hform, norm_mul, norm_mul, mul_pow, mul_pow,
    GaussInduced.norm_sq_gaussSum_primitive χ⁻¹.primitiveCharacter_isPrimitive,
    GaussInduced.norm_sq_char]
  simp only [ZMod.isUnit_iff_coprime, Complex.norm_intCast, sq_abs, hci]

/-! ## Lifting to one modulus -/

/-- `S_χ` only sees `χ` on the support: if two characters agree on every `n` with `aₙ ≠ 0`,
their `S` agree. -/
theorem eSc_congr (a : ℕ → ℂ) {N N' : ℕ} (χ : DirichletCharacter ℂ N)
    (χ' : DirichletCharacter ℂ N') (h : ∀ n : ℕ, a n ≠ 0 → χ n = χ' n) (β : ℝ) :
    eSc a χ β = eSc a χ' β := by
  unfold eSc
  refine tsum_congr fun n => ?_
  by_cases h0 : a n = 0
  · simp [h0]
  · rw [h n h0]

/-- The lift of `χ mod m` to `M` agrees with `χ` on every `n` coprime to `M`. -/
theorem lift_apply {m M : ℕ} [NeZero M] (hmM : m ∣ M) (χ : DirichletCharacter ℂ m) (n : ℕ)
    (hn : Nat.Coprime n M) : changeLevel hmM χ n = χ n := by
  have h := changeLevel_eq_cast_of_dvd' χ hmM (a := (n : ℤ))
    (Int.isCoprime_iff_gcd_eq_one.mpr (by rw [Int.gcd_natCast_natCast]; exact hn))
  simpa only [Int.cast_natCast] using h

open Classical in
/-- **The lifts of the characters mod `m` are exactly the `ψ mod M` with `cond ψ ∣ m`.** -/
theorem image_lift {m M : ℕ} [NeZero m] [NeZero M] (hmM : m ∣ M) :
    (Finset.univ : Finset (DirichletCharacter ℂ m)).image (changeLevel hmM) =
      Finset.univ.filter (fun ψ => ψ.conductor ∣ m) := by
  ext ψ
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro ⟨χ, rfl⟩
    rw [conductor_changeLevel]
    exact χ.conductor_dvd_level
  · intro h
    refine ⟨changeLevel h ψ.primitiveCharacter, ?_⟩
    rw [← changeLevel_trans, ψ.changeLevel_primitiveCharacter]

/-- **`T_m(β) = ∑_{ψ mod M} κ(m, ψ)|S_ψ(β)|²`** for `1 ≤ m`, `m ∣ M` and `aₙ` supported on `n`
coprime to `M`. -/
theorem tS_eq (a : ℕ → ℂ) (ha : Summable fun n => ‖a n‖) (m M : ℕ) [NeZero M] (hm : 1 ≤ m)
    (hmM : m ∣ M) (hcop : ∀ n : ℕ, a n ≠ 0 → Nat.Coprime n M) (β : ℝ) :
    tS (fun α => ‖eS a α‖ ^ 2) m β =
      ∑ ψ : DirichletCharacter ℂ M, kap m ψ * ‖eSc a ψ β‖ ^ 2 := by
  classical
  haveI : NeZero m := ⟨by omega⟩
  have hcopm : ∀ n : ℕ, a n ≠ 0 → Nat.Coprime n m := fun n hn =>
    Nat.Coprime.coprime_dvd_right hmM (hcop n hn)
  have hφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  -- orthogonality + the identity
  have h1 := sum_char_normsq m (fun b => eS a ((b.val : ℝ) / m + β))
  simp_rw [char_sum_eq a ha m hcopm, norm_mul, mul_pow, normsq_gauss_inv] at h1
  -- the residues
  have hres : ∑ b : ZMod m, (if IsUnit b then ‖eS a ((b.val : ℝ) / m + β)‖ ^ 2 else 0) =
      tS (fun α => ‖eS a α‖ ^ 2) m β := by
    unfold tS cop
    rw [← Finset.sum_filter]
    refine Finset.sum_nbij' (fun b => b.val) (fun c => (c : ZMod m)) ?_ ?_ ?_ ?_ ?_
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨ZMod.val_lt b, ?_⟩
      rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
      exact hb
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_range] at hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (ZMod.isUnit_iff_coprime c m).mpr hc.2
    · intro b _
      exact ZMod.natCast_zmod_val b
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_range] at hc
      exact ZMod.val_cast_of_lt hc.1
    · intro b _
      rfl
  rw [hres] at h1
  -- lift every character to `M`
  have hlift : ∀ χ : DirichletCharacter ℂ m,
      ((μ (m / χ.conductor) : ℤ) : ℝ) ^ 2 *
        (if Nat.Coprime (m / χ.conductor) χ.conductor then 1 else 0) * χ.conductor *
          ‖eSc a χ β‖ ^ 2 =
      m.totient * (kap m (changeLevel hmM χ) * ‖eSc a (changeLevel hmM χ) β‖ ^ 2) := by
    intro χ
    have hc : (changeLevel hmM χ).conductor = χ.conductor := conductor_changeLevel χ hmM
    have hS : eSc a χ β = eSc a (changeLevel hmM χ) β :=
      eSc_congr a _ _ (fun n hn => (lift_apply hmM χ n (hcop n hn)).symm) β
    unfold kap
    rw [hc, if_pos χ.conductor_dvd_level, hS]
    field_simp
  simp_rw [hlift] at h1
  rw [← Finset.mul_sum] at h1
  have h2 := mul_left_cancel₀ hφ.ne' h1
  rw [← h2]
  have hinj := changeLevel_injective (R := ℂ) hmM
  rw [← Finset.sum_image (f := fun ψ => kap m ψ * ‖eSc a ψ β‖ ^ 2)
    (fun x _ y _ hxy => hinj hxy), image_lift hmM, Finset.sum_filter]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  split_ifs with hd
  · rfl
  · unfold kap
    rw [if_neg hd, zero_mul]

end Principia.Common.PSieve
