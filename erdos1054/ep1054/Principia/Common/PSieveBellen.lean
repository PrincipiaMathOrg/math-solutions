/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.PSieveChar
import Principia.Common.PSieveSwap

set_option autoImplicit false

/-!
# `prop:bellen` (Helfgott, `ternvin.tex` 2491-2603) — PROVED: `bellenG : BellenG`

The large sieve for primes over major arcs, in the scale-free form `PSieve.BellenG`: for `ℓ¹`
coefficients coprime to every modulus `≤ 2Q` and `B` bounding every `G_q(2Q₀/sq)/G_q(2Q/sq)`
(`q ≤ 2Q₀` even, `1 ≤ s ≤ 2Q₀/q`),
`∫_{(0,1] ∩ 𝔐} |S|² ≤ B ∫_{(0,1]} |S|²`, `𝔐 = oeArcs(Q₀/2Q², Q₀)` (Helfgott's `𝔐_{δ₀,Q₀}` at
`Q = √(x/2δ₀)`).

## The proof, as composed here

```
 ∫_{(0,1]∩𝔐} |S|²  = ∑_{m} ∫_{|β| ≤ h₀/ρ(m)} T_m(β)                  arc_reduce (PSieveArcs)
 T_m(β)            = ∑_{ψ mod M} κ(m,ψ)|S_ψ(β)|²,   M = ⌊2Q⌋!           tS_eq (PSieveChar)
                  ⇒ ∑_ψ ∑_m κ(m,ψ) ∫_{|β| ≤ h₀/ρ(m)} |S_ψ|²              (Fubini for finite sums)
 per ψ, d = cond ψ: ∑_{ρ(m) ≤ y} κ(m,ψ) = (d/φ(d))·G_d(y/d)       (d even)   sum_kap_even
                                        = (d/φ(d))·2G_{2d}(y/2d)  (d odd)    sum_kap_odd
                  ⇒ the ratio bound of the G-swap is the hypothesis on B      hrat
                  ≤ B ∑_ψ ∑_m κ(m,ψ) ∫_{|β| ≤ h/ρ(m)} |S_ψ|²               swap_bound (PSieveSwap)
                  = B ∫_{(0,1] ∩ oeArcs(1/2Q, Q)} |S|² ≤ B ∫_{(0,1]} |S|²     arc_reduce, ⊆
```

The source's two maxima (over `q* odd` with `G_{2q*}` and over `q* even`, 2546-2551), which it
remarks are equal, are one family here: the lift to `M` and the radius `ρ(m)` (`2m` for odd `m`,
`m` for even `m`) put the odd moduli's factor `2` (2540-2541) inside `sum_kap_odd`.

## Corrections to the printed proof (each found by formalizing it)

* `prop:bellen` asks `δ₀ ≥ 1`; the character identity needs the support coprime to every
  modulus `≤ 2Q = √(2x/δ₀)`, i.e. `δ₀ ≥ 2` for primes `> √x`. `BellenG` asks for the coprimality.
* The display `Σ₁ ≤ ∑_q φ(q)⁻¹ ∫ ∑_b |S(b/q + α)|²` (2579-2586) is missing the sum over
  characters — as printed it is `φ(q)` times too strong; the proof uses the correct form
  (orthogonality, `sum_char_normsq`).
* `eq:malkr`'s "=" (2378) is an equality only because the arcs are disjoint, which needs
  `δ₀Q₀² ≤ x/2`; it is proved (`arcs_disjoint`) rather than assumed.
-/

namespace Principia.Common.PSieve

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach DirichletCharacter
open scoped ArithmeticFunction.Moebius

/-! ## (1) Continuity and periodicity -/

/-- `‖aₙe(nα)‖ = ‖aₙ‖`. -/
theorem norm_term (a : ℕ → ℂ) (n : ℕ) (α : ℝ) : ‖a n * e ((n : ℝ) * α)‖ = ‖a n‖ := by
  rw [norm_mul, e_norm, mul_one]

/-- `S = ∑ aₙe(nα)` is continuous for `∑‖aₙ‖ < ∞`. -/
theorem eS_cont (a : ℕ → ℂ) (ha : Summable fun n => ‖a n‖) : Continuous (eS a) := by
  unfold eS
  refine continuous_tsum (fun n => ?_) ha fun n α => le_of_eq (norm_term a n α)
  unfold e
  fun_prop

/-- `S_χ = ∑ aₙχ(n)e(nβ)` is continuous for `∑‖aₙ‖ < ∞`. -/
theorem eSc_cont (a : ℕ → ℂ) (ha : Summable fun n => ‖a n‖) {N : ℕ}
    (χ : DirichletCharacter ℂ N) : Continuous (eSc a χ) := by
  unfold eSc
  refine continuous_tsum (fun n => ?_) ha fun n β => ?_
  · unfold e
    fun_prop
  · rw [norm_mul, norm_mul, e_norm, mul_one]
    exact mul_le_of_le_one_right (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)

/-- `S(α + 1) = S(α)`. -/
theorem eS_add_one (a : ℕ → ℂ) (α : ℝ) : eS a (α + 1) = eS a α := by
  unfold eS
  refine tsum_congr fun n => ?_
  have h1 : e (n : ℝ) = 1 := (e_eq_one_iff (n : ℝ)).mpr ⟨n, (Int.cast_natCast n).symm⟩
  rw [mul_add, mul_one, ← e_add, h1, mul_one]

/-! ## (2) The `G`-sums of `κ` -/

/-- The summand of `G_d`: `μ²(r)/φ(r)` for `(r,d) = 1`, else `0`. -/
noncomputable def gterm (d r : ℕ) : ℝ :=
  if Nat.Coprime r d then ((μ r : ℤ) : ℝ) ^ 2 / r.totient else 0

/-- `G_d(z) = ∑_{1 ≤ r ≤ z} gterm d r`. -/
theorem gQ_eq (d : ℕ) (z : ℝ) : gQ d z = ∑ r ∈ Finset.Icc 1 ⌊z⌋₊, gterm d r := by
  unfold gQ gterm
  rw [Finset.sum_filter]

/-- `κ(m, ψ) = [d ∣ m]·(d/φ(d))·gterm d (m/d)`, `d = cond ψ`. -/
theorem kap_eq {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) (m : ℕ) (hm : 1 ≤ m) :
    kap m ψ = if ψ.conductor ∣ m then
      (ψ.conductor : ℝ) / ψ.conductor.totient * gterm ψ.conductor (m / ψ.conductor) else 0 := by
  have hd0 : 0 < ψ.conductor := Nat.pos_of_ne_zero (conductor_ne_zero ψ)
  unfold kap gterm
  split_ifs with hd hc
  · have hr : 0 < m / ψ.conductor := Nat.div_pos (Nat.le_of_dvd hm hd) hd0
    have ht : m.totient = ψ.conductor.totient * (m / ψ.conductor).totient := by
      conv_lhs => rw [← Nat.mul_div_cancel' hd]
      exact Nat.totient_mul hc.symm
    have h1 : (0 : ℝ) < ψ.conductor.totient := by exact_mod_cast Nat.totient_pos.mpr hd0
    have h2 : (0 : ℝ) < (m / ψ.conductor).totient := by exact_mod_cast Nat.totient_pos.mpr hr
    rw [ht]
    push_cast
    field_simp
  · simp
  · rfl

/-- **Reindexing `m = d r`**: `∑_{1 ≤ m ≤ N, ρ(m) ≤ y} κ(m,ψ) = (d/φ(d))·∑_{1 ≤ r ≤ N, ρ(dr) ≤ y}
gterm d r`. -/
theorem sum_kap_div {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) (N : ℕ) (y : ℝ)
    (hy : y < N + 1) :
    ∑ m ∈ (Finset.Icc 1 N).filter (fun m => rho m ≤ y), kap m ψ =
      (ψ.conductor : ℝ) / ψ.conductor.totient *
        ∑ r ∈ (Finset.Icc 1 N).filter (fun r => rho (ψ.conductor * r) ≤ y),
          gterm ψ.conductor r := by
  classical
  set d := ψ.conductor with hdd
  have hd0 : 0 < d := Nat.pos_of_ne_zero (conductor_ne_zero ψ)
  have e1 : ∀ m ∈ (Finset.Icc 1 N).filter (fun m => rho m ≤ y), kap m ψ =
      if d ∣ m then (d : ℝ) / d.totient * gterm d (m / d) else 0 := fun m hm =>
    kap_eq ψ m (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
  rw [Finset.sum_congr rfl e1, ← Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_nbij' (fun m => m / d) (fun r => d * r) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hm
    have hmd : d * (m / d) = m := Nat.mul_div_cancel' h4
    refine ⟨⟨Nat.div_pos (Nat.le_of_dvd h1 h4) hd0, le_trans (Nat.div_le_self m d) h2⟩, ?_⟩
    rw [hmd]
    exact h3
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_Icc] at hr ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hr
    refine ⟨⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hd0.ne' (by omega)), ?_⟩, h3⟩,
      dvd_mul_right d r⟩
    have h6 := (rho_bounds (d * r)).1
    have h7 : ((d * r : ℕ) : ℝ) < N + 1 := by linarith
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast h7)
  · intro m hm
    simp only [Finset.mem_filter] at hm
    exact Nat.mul_div_cancel' hm.2
  · intro r _
    exact Nat.mul_div_cancel_left r hd0
  · intro m _
    rfl

/-- `G_q(z) = 0` for `z < 1`. -/
theorem gQ_lt_one (q : ℕ) (z : ℝ) (hz : z < 1) : gQ q z = 0 := by
  have h0 : ⌊z⌋₊ = 0 := Nat.floor_eq_zero.mpr hz
  unfold gQ
  rw [h0]
  rfl

/-- `gterm (2d) r = [r odd]·gterm d r`. -/
theorem gterm_two_left (d r : ℕ) : gterm (2 * d) r = if Odd r then gterm d r else 0 := by
  unfold gterm
  by_cases hr : Odd r
  · have h2 : Nat.Coprime r 2 := Nat.coprime_two_right.mpr hr
    rw [if_pos hr]
    by_cases hc : Nat.Coprime r d
    · rw [if_pos (Nat.Coprime.mul_right h2 hc), if_pos hc]
    · have hc2 : ¬ Nat.Coprime r (2 * d) := fun h =>
        hc (Nat.Coprime.coprime_dvd_right (dvd_mul_left d 2) h)
      rw [if_neg hc2, if_neg hc]
  · have h2 : ¬ Nat.Coprime r (2 * d) := fun h =>
      hr (Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 d) h))
    rw [if_neg hr, if_neg h2]

/-- **`gterm d (2r) = [r odd]·gterm d r`** for odd `d`: `μ(2r)² = μ(r)²`, `φ(2r) = φ(r)`,
`(2r, d) = (r, d)` for odd `r`; `4 ∣ 2r` kills even `r`. -/
theorem gterm_two_mul (d r : ℕ) (hd : Odd d) :
    gterm d (2 * r) = if Odd r then gterm d r else 0 := by
  unfold gterm
  by_cases hr : Odd r
  · have h2r : Nat.Coprime 2 r := Nat.coprime_two_left.mpr hr
    have h2d : Nat.Coprime 2 d := Nat.coprime_two_left.mpr hd
    have hc : Nat.Coprime (2 * r) d ↔ Nat.Coprime r d := by
      rw [Nat.coprime_mul_iff_left]
      exact ⟨fun h => h.2, fun h => ⟨h2d, h⟩⟩
    have hmu : μ (2 * r) = -μ r := by
      rw [isMultiplicative_moebius.map_mul_of_coprime h2r, moebius_apply_prime Nat.prime_two]
      ring
    have hphi : (2 * r).totient = r.totient := by
      rw [Nat.totient_mul h2r, Nat.totient_two, one_mul]
    rw [if_pos hr]
    simp only [hc, hmu, hphi]
    push_cast
    rw [neg_sq]
  · rw [if_neg hr]
    have hns : ¬ Squarefree (2 * r) := by
      intro hsq
      obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp hr
      have h4 : 2 * 2 ∣ 2 * r := ⟨k, by rw [hk]; ring⟩
      have := hsq 2 h4
      exact absurd (Nat.isUnit_iff.mp this) (by norm_num)
    rw [moebius_eq_zero_of_not_squarefree hns]
    simp

/-- **`d` even**: `∑_{1 ≤ r ≤ N, ρ(dr) ≤ y} gterm d r = G_d(y/d)` (`y < N + 1`). -/
theorem sum_gterm_even (d : ℕ) (hd : Even d) (hd1 : 1 ≤ d) (N : ℕ) (y : ℝ) (hy : y < N + 1) :
    ∑ r ∈ (Finset.Icc 1 N).filter (fun r => rho (d * r) ≤ y), gterm d r = gQ d (y / d) := by
  rw [gQ_eq]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  ext r
  simp only [Finset.mem_filter, Finset.mem_Icc]
  have hrho : rho (d * r) = (d : ℝ) * r := by
    rw [rho_even (hd.mul_right r)]
    push_cast
    ring
  rw [hrho]
  constructor
  · rintro ⟨⟨h1, -⟩, h3⟩
    refine ⟨h1, Nat.le_floor ?_⟩
    rw [le_div_iff₀ hd0]
    linarith
  · rintro ⟨h1, h2⟩
    have hpos : 0 < ⌊y / d⌋₊ := by omega
    have hyd : 1 ≤ y / d := Nat.floor_pos.mp hpos
    have hr : (r : ℝ) ≤ y / d := le_trans (by exact_mod_cast h2) (Nat.floor_le (by linarith))
    have hdr : (d : ℝ) * r ≤ y := by rwa [le_div_iff₀ hd0, mul_comm] at hr
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast h1
    have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    have hrN : (r : ℝ) < N + 1 := by nlinarith
    refine ⟨⟨h1, ?_⟩, hdr⟩
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast hrN)

/-- **`d` odd**: `∑_{1 ≤ r ≤ N, ρ(dr) ≤ y} gterm d r = 2·G_{2d}(y/2d)` (`y < N + 1`): odd `r`
with `2dr ≤ y`, and even `r = 2r'` with `dr ≤ y`, contribute the same (the source's "factor
of 2", 2540-2541). -/
theorem sum_gterm_odd (d : ℕ) (hd : Odd d) (N : ℕ) (y : ℝ) (hy : y < N + 1) :
    ∑ r ∈ (Finset.Icc 1 N).filter (fun r => rho (d * r) ≤ y), gterm d r =
      2 * gQ (2 * d) (y / (2 * d)) := by
  classical
  have hd1 : 1 ≤ d := hd.pos
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  set Z := ⌊y / (2 * d)⌋₊ with hZ
  set F := (Finset.Icc 1 N).filter (fun r => rho (d * r) ≤ y) with hF
  -- the odd part
  have hodd : F.filter (fun r => _root_.Odd r) =
      (Finset.Icc 1 Z).filter (fun r => _root_.Odd r) := by
    ext r
    simp only [hF, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨h1, -⟩, h3⟩, ho⟩
      rw [rho_odd (hd.mul ho)] at h3
      push_cast at h3
      refine ⟨⟨h1, Nat.le_floor ?_⟩, ho⟩
      rw [le_div_iff₀ (by positivity)]
      linarith
    · rintro ⟨⟨h1, h2⟩, ho⟩
      rw [rho_odd (hd.mul ho)]
      push_cast
      have hpos : 0 < Z := by omega
      have hyd : 1 ≤ y / (2 * d) := Nat.floor_pos.mp hpos
      have hZle : ((Z : ℕ) : ℝ) ≤ y / (2 * (d : ℝ)) := by
        rw [hZ]
        exact Nat.floor_le (by linarith)
      have hr : (r : ℝ) ≤ y / (2 * (d : ℝ)) := le_trans (Nat.cast_le.mpr h2) hZle
      have hdr : 2 * ((d : ℝ) * r) ≤ y := by
        rw [le_div_iff₀ (by positivity)] at hr
        linarith
      have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast h1
      have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
      have hrN : (r : ℝ) < N + 1 := by nlinarith
      exact ⟨⟨⟨h1, by exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast hrN)⟩, hdr⟩, ho⟩
  -- the even part, `r = 2r'`
  have heven : ∑ r ∈ F.filter (fun r => ¬ _root_.Odd r), gterm d r =
      ∑ r ∈ Finset.Icc 1 Z, gterm d (2 * r) := by
    refine Finset.sum_nbij' (fun r => r / 2) (fun r => 2 * r) ?_ ?_ ?_ ?_ ?_
    · intro r hr
      simp only [hF, Finset.mem_filter, Finset.mem_Icc] at hr ⊢
      obtain ⟨⟨⟨h1, -⟩, h3⟩, he⟩ := hr
      obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp he
      have hk2 : r / 2 = k := by omega
      rw [hk2]
      rw [hk, rho_even (Even.mul_left ⟨k, rfl⟩ d)] at h3
      push_cast at h3
      refine ⟨by omega, Nat.le_floor ?_⟩
      rw [le_div_iff₀ (by positivity)]
      linarith
    · intro r hr
      simp only [hF, Finset.mem_filter, Finset.mem_Icc] at hr ⊢
      obtain ⟨h1, h2⟩ := hr
      have hpos : 0 < Z := by omega
      have hyd : 1 ≤ y / (2 * d) := Nat.floor_pos.mp hpos
      have hZle : ((Z : ℕ) : ℝ) ≤ y / (2 * (d : ℝ)) := by
        rw [hZ]
        exact Nat.floor_le (by linarith)
      have hr : (r : ℝ) ≤ y / (2 * (d : ℝ)) := le_trans (Nat.cast_le.mpr h2) hZle
      have hdr : (d : ℝ) * (2 * r) ≤ y := by
        rw [le_div_iff₀ (by positivity)] at hr
        linarith
      rw [rho_even (Even.mul_left (even_two_mul r) d)]
      push_cast
      have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast h1
      have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
      have hrN : ((2 * r : ℕ) : ℝ) < N + 1 := by push_cast; nlinarith
      refine ⟨⟨⟨by omega, by exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast hrN)⟩, hdr⟩,
        ?_⟩
      exact Nat.not_odd_iff_even.mpr (even_two_mul r)
    · intro r hr
      simp only [hF, Finset.mem_filter] at hr
      obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp hr.2
      show 2 * (r / 2) = r
      omega
    · intro r _
      show 2 * r / 2 = r
      omega
    · intro r hr
      simp only [hF, Finset.mem_filter] at hr
      obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp hr.2
      have : 2 * (r / 2) = r := by omega
      rw [this]
  have hsplit := (Finset.sum_filter_add_sum_filter_not F (fun r => _root_.Odd r) (gterm d)).symm
  rw [hsplit, hodd, heven]
  simp_rw [gterm_two_mul d _ hd]
  rw [← Finset.sum_filter, gQ_eq]
  simp_rw [gterm_two_left]
  rw [← Finset.sum_filter]
  ring

/-! ## (3) The assembly -/

/-- Coprime to every `1 ≤ m ≤ N` gives coprime to `N!`. -/
theorem coprime_fact (n N : ℕ) (h : ∀ m : ℕ, 1 ≤ m → m ≤ N → Nat.Coprime n m) :
    Nat.Coprime n N.factorial := by
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Nat.factorial_succ]
    exact Nat.Coprime.mul_right (h (k + 1) (by omega) le_rfl)
      (ih fun m h1 h2 => h m h1 (by omega))

/-- **The ratio bound of the `G`-swap, for one character `ψ`**, from the hypothesis on `B`:
`∑_{ρ(m) ≤ 2Q₀/s} κ(m,ψ) ≤ B ∑_{ρ(m) ≤ 2Q/s} κ(m,ψ)` for `s ∈ [1, 2Q₀]`. -/
theorem kap_ratio {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) (N : ℕ) (Q₀ Q B : ℝ)
    (hQ0Q : Q₀ ≤ Q) (hN : 2 * Q < N + 1) (hB0 : 0 ≤ B)
    (hB : ∀ q : ℕ, Even q → 1 ≤ q → (q : ℝ) ≤ 2 * Q₀ → ∀ s : ℝ, 1 ≤ s → s ≤ 2 * Q₀ / q →
      gQ q (2 * Q₀ / (s * q)) ≤ B * gQ q (2 * Q / (s * q)))
    (s : ℝ) (hs1 : 1 ≤ s) (hs2 : s ≤ 2 * Q₀) :
    ∑ m ∈ (Finset.Icc 1 N).filter (fun m => rho m ≤ 2 * Q₀ / s), kap m ψ ≤
      B * ∑ m ∈ (Finset.Icc 1 N).filter (fun m => rho m ≤ 2 * Q / s), kap m ψ := by
  have hs0 : 0 < s := by linarith
  have hQ00 : 0 < Q₀ := by linarith
  have hy₀ : 2 * Q₀ / s < N + 1 := by
    have : 2 * Q₀ / s ≤ 2 * Q₀ := div_le_self (by linarith) hs1
    linarith
  have hy : 2 * Q / s < N + 1 := by
    have : 2 * Q / s ≤ 2 * Q := div_le_self (by linarith) hs1
    linarith
  rw [sum_kap_div ψ N _ hy₀, sum_kap_div ψ N _ hy]
  set d := ψ.conductor with hdd
  have hd1 : 1 ≤ d := Nat.pos_of_ne_zero (conductor_ne_zero ψ)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hc : (0 : ℝ) ≤ (d : ℝ) / d.totient := by positivity
  suffices hG : ∑ r ∈ (Finset.Icc 1 N).filter (fun r => rho (d * r) ≤ 2 * Q₀ / s), gterm d r ≤
      B * ∑ r ∈ (Finset.Icc 1 N).filter (fun r => rho (d * r) ≤ 2 * Q / s), gterm d r by
    calc (d : ℝ) / d.totient *
          ∑ r ∈ (Finset.Icc 1 N).filter (fun r => rho (d * r) ≤ 2 * Q₀ / s), gterm d r
        ≤ (d : ℝ) / d.totient *
          (B * ∑ r ∈ (Finset.Icc 1 N).filter (fun r => rho (d * r) ≤ 2 * Q / s), gterm d r) :=
          mul_le_mul_of_nonneg_left hG hc
      _ = B * ((d : ℝ) / d.totient *
          ∑ r ∈ (Finset.Icc 1 N).filter (fun r => rho (d * r) ≤ 2 * Q / s), gterm d r) := by
          ring
  rcases Nat.even_or_odd d with he | ho
  · rw [sum_gterm_even d he hd1 N _ hy₀, sum_gterm_even d he hd1 N _ hy]
    have e1 : 2 * Q₀ / s / d = 2 * Q₀ / (s * d) := by rw [div_div]
    have e2 : 2 * Q / s / d = 2 * Q / (s * d) := by rw [div_div]
    rw [e1, e2]
    by_cases hsd : s ≤ 2 * Q₀ / d
    · have hdQ : (d : ℝ) ≤ 2 * Q₀ := by
        rw [le_div_iff₀ hd0] at hsd
        nlinarith
      exact hB d he hd1 hdQ s hs1 hsd
    · push Not at hsd
      have hlt : 2 * Q₀ / (s * d) < 1 := by
        rw [div_lt_one (by positivity)]
        rw [div_lt_iff₀ hd0] at hsd
        linarith
      rw [gQ_lt_one _ _ hlt]
      exact mul_nonneg hB0 (gQ_nonneg _ _)
  · rw [sum_gterm_odd d ho N _ hy₀, sum_gterm_odd d ho N _ hy]
    have e1 : 2 * Q₀ / s / (2 * d) = 2 * Q₀ / (s * ((2 * d : ℕ) : ℝ)) := by
      push_cast
      rw [div_div]
    have e2 : 2 * Q / s / (2 * d) = 2 * Q / (s * ((2 * d : ℕ) : ℝ)) := by
      push_cast
      rw [div_div]
    rw [e1, e2]
    have h2d0 : (0 : ℝ) < ((2 * d : ℕ) : ℝ) := by positivity
    suffices h : gQ (2 * d) (2 * Q₀ / (s * ((2 * d : ℕ) : ℝ))) ≤
        B * gQ (2 * d) (2 * Q / (s * ((2 * d : ℕ) : ℝ))) by linarith
    by_cases hsd : s ≤ 2 * Q₀ / ((2 * d : ℕ) : ℝ)
    · have hdQ : ((2 * d : ℕ) : ℝ) ≤ 2 * Q₀ := by
        rw [le_div_iff₀ h2d0] at hsd
        nlinarith
      exact hB (2 * d) (even_two_mul d) (by omega) hdQ s hs1 hsd
    · push Not at hsd
      have hlt : 2 * Q₀ / (s * ((2 * d : ℕ) : ℝ)) < 1 := by
        rw [div_lt_one (by positivity)]
        rw [div_lt_iff₀ h2d0] at hsd
        linarith
      rw [gQ_lt_one _ _ hlt]
      exact mul_nonneg hB0 (gQ_nonneg _ _)

/-- **`∫_{−w}^{w} T_m = ∑_{ψ mod M} κ(m,ψ) ∫_{−w}^{w} |S_ψ|²`** (`tS_eq` under the integral). -/
theorem int_tS (a : ℕ → ℂ) (ha : Summable fun n => ‖a n‖) (m M : ℕ) [NeZero M] (hm : 1 ≤ m)
    (hmM : m ∣ M) (hcop : ∀ n : ℕ, a n ≠ 0 → Nat.Coprime n M) (w : ℝ) :
    ∫ β in (-w)..w, tS (fun α => ‖eS a α‖ ^ 2) m β =
      ∑ ψ : DirichletCharacter ℂ M, kap m ψ * ∫ β in (-w)..w, ‖eSc a ψ β‖ ^ 2 := by
  rw [intervalIntegral.integral_congr (fun β _ => tS_eq a ha m M hm hmM hcop β),
    intervalIntegral.integral_finsetSum
      (fun ψ _ => (((eSc_cont a ha ψ).norm.pow 2).intervalIntegrable _ _).const_mul _)]
  simp_rw [intervalIntegral.integral_const_mul]

/-- **`prop:bellen`, PROVED** (`ternvin.tex` 2491-2603), in the scale-free form `BellenG`. -/
theorem bellenG : BellenG := by
  intro a Q₀ Q B ha hQ01 hQ0Q hsupp hB
  have hQ1 : 1 ≤ Q := le_trans hQ01 hQ0Q
  have hQ0 : 0 < Q := by linarith
  set N := ⌊2 * Q⌋₊ with hNdef
  have hN : 2 * Q < N + 1 := Nat.lt_floor_add_one _
  have hNle : (N : ℝ) ≤ 2 * Q := Nat.floor_le (by linarith)
  haveI : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩
  have hcopM : ∀ n : ℕ, a n ≠ 0 → Nat.Coprime n N.factorial := fun n hn =>
    coprime_fact n N fun m h1 h2 => hsupp n hn m h1 (le_trans (by exact_mod_cast h2) hNle)
  have hFc : Continuous fun α => ‖eS a α‖ ^ 2 := ((eS_cont a ha).norm).pow 2
  have hFp : ∀ α, ‖eS a (α + 1)‖ ^ 2 = ‖eS a α‖ ^ 2 := fun α => by rw [eS_add_one]
  -- `B ≥ 0`, from the ratio at `q = 2`, `s = 1`
  have hB0 : 0 ≤ B := by
    have h := hB 2 even_two (by norm_num) (by push_cast; linarith) 1 le_rfl
      (by push_cast; linarith)
    have g1 : 1 ≤ gQ 2 (2 * Q₀ / (1 * ((2 : ℕ) : ℝ))) :=
      one_le_gQ _ _ (by push_cast; linarith)
    have g2 := gQ_nonneg 2 (2 * Q / (1 * ((2 : ℕ) : ℝ)))
    by_contra hneg
    push Not at hneg
    nlinarith
  set h₀ := Q₀ / (2 * Q ^ 2) with hh₀def
  have hh₀ : 0 < h₀ := by positivity
  have hh : (0 : ℝ) < 1 / (2 * Q) := by positivity
  have hh₀Q₀ : h₀ * Q₀ ≤ 1 / 2 := by
    rw [hh₀def, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hhQ : 1 / (2 * Q) * Q ≤ 1 / 2 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith
  have hN₀ : 2 * Q₀ < N + 1 := by linarith
  have hsub : ∫ α in Set.Ioc (0 : ℝ) 1 ∩ oeArcs (1 / (2 * Q)) Q, ‖eS a α‖ ^ 2 ≤
      ∫ α in Set.Ioc (0 : ℝ) 1, ‖eS a α‖ ^ 2 :=
    setIntegral_mono_set (hFc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
      (Filter.Eventually.of_forall fun α => by positivity)
      (Filter.Eventually.of_forall Set.inter_subset_left)
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hsub hB0)
  rw [arc_reduce _ hFc hFp h₀ Q₀ N hh₀ hQ01 hh₀Q₀ hN₀,
    arc_reduce _ hFc hFp (1 / (2 * Q)) Q N hh hQ1 hhQ hN]
  have hfam : ∀ (L : ℝ) (m : ℕ), m ∈ fam N L → 1 ≤ m ∧ m ∣ N.factorial := by
    intro L m hm
    have h := Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1
    exact ⟨h.1, Nat.dvd_factorial h.1 h.2⟩
  rw [Finset.sum_congr rfl fun m hm =>
      int_tS a ha m N.factorial (hfam _ m hm).1 (hfam _ m hm).2 hcopM _,
    Finset.sum_congr rfl fun m hm =>
      int_tS a ha m N.factorial (hfam _ m hm).1 (hfam _ m hm).2 hcopM _,
    Finset.sum_comm, Finset.sum_comm (s := fam N Q), Finset.mul_sum]
  refine Finset.sum_le_sum fun ψ _ => ?_
  have hKK : 2 * Q * h₀ = 2 * Q₀ * (1 / (2 * Q)) := by
    rw [hh₀def]
    field_simp
  have huu : h₀ ≤ 1 / (2 * Q) := by
    rw [hh₀def, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  exact swap_bound (fun β => ‖eSc a ψ β‖ ^ 2) ((eSc_cont a ha ψ).norm.pow 2)
    (fun β => sq_nonneg _) (Finset.Icc 1 N) (fun m => kap m ψ) rho
    (fun m _ => kap_nonneg m ψ)
    (fun m hm => le_trans one_le_two (two_le_rho (Finset.mem_Icc.mp hm).1))
    (2 * Q₀) (2 * Q) h₀ (1 / (2 * Q)) B hh₀ huu (by linarith) hB0 hKK
    (fun s hs1 hs2 => kap_ratio ψ N Q₀ Q B hQ0Q hN hB0 hB s hs1 hs2)

end Principia.Common.PSieve
