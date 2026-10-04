/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIICrustoCudo

set_option autoImplicit false

/-!
# `M2H.MonroFleming` spined to ONE counting link: `CountSq`

`M2F.Monro2` (`lem:monro` with `eq:mudo`, constant `1.27`) rests on Helfgott's numerical check
`f(x) ≤ 1.26981x` (`minarcs.tex` 2780-2787, "by checking all integers smaller than a constant"),
which is NOT among the cited computations (`HelfgottCited`). This file replaces it by
`Monro2B` — the same statement with the error constant `10.25` (`≥ 1.5·(1 + 1/√2)·4`, from the
provable `f(x) ≤ 1.5x` and the proved `∑_{d odd} d^{−3/2} ≤ 2` in place of
`(1 − 2^{−3/2})ζ(3/2)`) — which still closes `M2H.MonroFleming` (`2·10.25 = 20.5 ≤ 22.6418`),
and reduces `Monro2B` to one per-modulus counting statement:

```
 CountSq     square-free l ∈ (a, b] coprime to square-free k, b/2 ≤ a ≤ b:
             |# − (6/π²)(k/σ(k))(b − a)| ≤ 1.5·∑_{e ∣ k} √(b/e)                LINK
 odd_lt      ∑_{s < Y odd} s^{−1/2} ≤ √Y                                       PROVED
 hh_sum      ∑_{r < y odd} ∑_{d ∣ r} (rd)^{−1/2} ≤ 2√y                         PROVED
 div_sum_le  ∑_{e ∣ 2r₁r₂} √(z/r₁r₂e) ≤ (1 + 1/√2)√z·h(r₁)h(r₂)              PROVED
 term_bd     one (r₁, r₂) term of srto − (4/π²)z·mutedSum, via CountSq          PROVED
 monro2B_of_count     : CountSq → Monro2B                                       PROVED
 monroFlem_of_monro2B : Monro2B → M2H.MonroFleming                              PROVED
```

`CountSq` is the book's `eq:etze`-`eq:totor` for one modulus: Möbius inversion of the two
conditions, the Euler product `∑_{(m,k)=1} μ(m)/m² = (6/π²)∏_{p ∣ k}(1 − p^{−2})^{−1}`, the
`O*(1)` per lattice count, and `f(x) = #{m ≤ x sq-free} + (x²/2)∑_{m > x sq-free} m^{−2} ≤ 1.5x`
(`b − a ≤ b/2`). Checked numerically before stating (`scratchpad/count_test.py`: worst ratio
`0.53` over 20000 random `(k, a, b)`).
-/

namespace Principia.Common.TernaryGoldbach.M2B

open ArithmeticFunction

/-! ## (0) Objects and links -/

/-- `#{a < l ≤ b : l square-free, (l, k) = 1}`. -/
noncomputable def nSq (k : ℕ) (a b : ℝ) : ℝ :=
  (((Finset.Icc 1 ⌊b⌋₊).filter (fun l : ℕ =>
    a < (l : ℝ) ∧ Nat.Coprime l k ∧ Squarefree l)).card : ℝ)

/-- **Link [CountSq]** — square-free `l` coprime to a square-free `k` in `(a, b]`, `b/2 ≤ a ≤ b`:
`|# − (6/π²)(k/σ(k))(b − a)| ≤ 1.5·∑_{e ∣ k} √(b/e)`. -/
def CountSq : Prop :=
  ∀ k : ℕ, Squarefree k → ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 2 * a →
    |nSq k a b - 6 / Real.pi ^ 2 * ((k : ℝ) / (sigma 1 k : ℝ)) * (b - a)| ≤
      1.5 * ∑ e ∈ k.divisors, Real.sqrt (b / e)

/-- **Link [Monro2B]** — `lem:monro` at `v = 2` with the error constant `10.25`. -/
def Monro2B : Prop :=
  ∀ y z : ℝ, 0 < y → 0 < z →
    |M2F.srto y z - 4 / Real.pi ^ 2 * z * M2F.mutedSum y| ≤ 10.25 * y * Real.sqrt z

/-! ## (1) Odd sums of `s^{−1/2}` -/

theorem sqrt_step (n : ℕ) :
    1 / Real.sqrt (2 * (n : ℝ) + 3) ≤
      Real.sqrt (2 * (n : ℝ) + 3) - Real.sqrt (2 * (n : ℝ) + 1) := by
  set a := Real.sqrt (2 * (n : ℝ) + 1) with ha
  set b := Real.sqrt (2 * (n : ℝ) + 3) with hb
  have ha2 : a ^ 2 = 2 * (n : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = 2 * (n : ℝ) + 3 := Real.sq_sqrt (by positivity)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 < b := Real.sqrt_pos.mpr (by positivity)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  rw [div_le_iff₀ hb0]
  nlinarith

/-- `∑_{s ≤ 2n+1 odd} s^{−1/2} ≤ √(2n+1)`. -/
theorem odd_isqrt (n : ℕ) :
    ∑ s ∈ (Finset.range (n + 1)), 1 / Real.sqrt (2 * (s : ℝ) + 1) ≤
      Real.sqrt (2 * (n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h := sqrt_step n
    push_cast
    have e : 2 * ((n : ℝ) + 1) + 1 = 2 * (n : ℝ) + 3 := by ring
    rw [e]
    linarith

/-- `∑_{s ∈ S} s^{−1/2} ≤ √Y` for any set `S` of odd `s < Y`. -/
theorem odd_lt (Y : ℝ) (S : Finset ℕ) (hS : ∀ s ∈ S, Nat.Coprime s 2 ∧ (s : ℝ) < Y) :
    ∑ s ∈ S, 1 / Real.sqrt s ≤ Real.sqrt Y := by
  rcases le_or_gt Y 1 with hY | hY
  · have hE : S = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun s hs => ?_
      obtain ⟨h1, h2⟩ := hS s hs
      have : s ≠ 0 := by
        rintro rfl
        simp at h1
      have : (1 : ℝ) ≤ s := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
      linarith
    rw [hE, Finset.sum_empty]
    exact Real.sqrt_nonneg _
  · set K := ⌈(Y - 1) / 2⌉₊ with hK
    have hsub : S ⊆ (Finset.range K).image (fun t : ℕ => 2 * t + 1) := by
      intro s hs
      obtain ⟨h1, h2⟩ := hS s hs
      have hodd : s % 2 = 1 := Nat.odd_iff.mp (Nat.coprime_two_right.mp h1)
      rw [Finset.mem_image]
      refine ⟨s / 2, ?_, by omega⟩
      rw [Finset.mem_range, hK, Nat.lt_ceil]
      have : ((s / 2 : ℕ) : ℝ) * 2 + 1 = s := by
        have : s / 2 * 2 + 1 = s := by omega
        exact_mod_cast this
      linarith
    have hinj : Set.InjOn (fun t : ℕ => 2 * t + 1) (Finset.range K) := fun a _ b _ h => by
      simp only at h
      omega
    calc ∑ s ∈ S, 1 / Real.sqrt s
        ≤ ∑ s ∈ (Finset.range K).image (fun t : ℕ => 2 * t + 1), 1 / Real.sqrt (s : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = ∑ t ∈ Finset.range K, 1 / Real.sqrt (2 * (t : ℝ) + 1) := by
          rw [Finset.sum_image hinj]
          push_cast
          rfl
      _ ≤ Real.sqrt Y := by
          rcases Nat.eq_zero_or_pos K with h0 | hpos
          · rw [h0, Finset.range_zero, Finset.sum_empty]
            exact Real.sqrt_nonneg _
          · obtain ⟨n, hn⟩ : ∃ n, K = n + 1 := ⟨K - 1, by omega⟩
            rw [hn]
            refine (odd_isqrt n).trans (Real.sqrt_le_sqrt ?_)
            have h1 : n < K := by omega
            rw [hK, Nat.lt_ceil] at h1
            linarith

/-- `h(r) = ∑_{d ∣ r} (rd)^{−1/2}`. -/
noncomputable def hh (r : ℕ) : ℝ := ∑ d ∈ r.divisors, 1 / Real.sqrt ((r : ℝ) * d)

theorem hh_nonneg (r : ℕ) : 0 ≤ hh r := Finset.sum_nonneg fun _ _ => by positivity

/-- **`∑_{r < y odd} h(r) ≤ 2√y`** (`r = ds`; `∑_{s < y/d odd} s^{−1/2} ≤ √(y/d)`,
`∑_{d odd} d^{−3/2} ≤ 2`). -/
theorem hh_sum (y : ℝ) (hy : 0 < y) :
    ∑ r ∈ Finset.Ico 1 ⌈y⌉₊, (if Nat.Coprime r 2 then hh r else 0) ≤ 2 * Real.sqrt y := by
  set B := ⌈y⌉₊ with hB
  have e1 : ∑ r ∈ Finset.Ico 1 B, (if Nat.Coprime r 2 then hh r else 0) =
      ∑ p ∈ M2C.dep (Finset.Ico 1 B) Nat.divisors,
        (if Nat.Coprime p.1 2 then 1 / Real.sqrt ((p.1 : ℝ) * p.2) else 0) := by
    rw [← M2C.sum_dep]
    refine Finset.sum_congr rfl fun r _ => ?_
    unfold hh
    split_ifs
    · rfl
    · simp
  have e2 : ∑ p ∈ M2C.dep (Finset.Ico 1 B) Nat.divisors,
        (if Nat.Coprime p.1 2 then 1 / Real.sqrt ((p.1 : ℝ) * p.2) else 0) =
      ∑ p ∈ M2C.dep (Finset.Ico 1 B) (fun d => (Finset.Ico 1 B).filter (fun s => d * s < B)),
        (if Nat.Coprime (p.1 * p.2) 2 then 1 / Real.sqrt (((p.1 * p.2 : ℕ) : ℝ) * p.1) else 0) := by
    refine Finset.sum_nbij' (fun p => (p.2, p.1 / p.2)) (fun p => (p.1 * p.2, p.1)) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨r, d⟩ hp
      simp only [M2C.mem_dep, Finset.mem_Ico, Nat.mem_divisors,
        Finset.mem_filter] at hp ⊢
      obtain ⟨⟨h1, h2⟩, hd, -⟩ := hp
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
      have hdr : d ≤ r := Nat.le_of_dvd (by omega) hd
      have hq : d * (r / d) = r := Nat.mul_div_cancel' hd
      have hq0 : 0 < r / d := Nat.div_pos hdr hd0
      refine ⟨⟨hd0, by omega⟩, ⟨hq0, by
        have : r / d ≤ r := Nat.div_le_self r d
        omega⟩, by omega⟩
    · rintro ⟨d, s⟩ hp
      simp only [M2C.mem_dep, Finset.mem_Ico, Nat.mem_divisors,
        Finset.mem_filter] at hp ⊢
      obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := hp
      refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (by positivity), h5⟩, ⟨s, rfl⟩, by positivity⟩
    · rintro ⟨r, d⟩ hp
      simp only [M2C.mem_dep, Finset.mem_Ico, Nat.mem_divisors] at hp
      change (d * (r / d), d) = (r, d)
      rw [Nat.mul_div_cancel' hp.2.1]
    · rintro ⟨d, s⟩ hp
      simp only [M2C.mem_dep, Finset.mem_Ico] at hp
      change (d, d * s / d) = (d, s)
      rw [Nat.mul_div_cancel_left s (by omega)]
    · rintro ⟨r, d⟩ hp
      simp only [M2C.mem_dep, Finset.mem_Ico, Nat.mem_divisors] at hp
      simp only
      rw [Nat.mul_div_cancel' hp.2.1]
  rw [e1, e2, ← M2C.sum_dep]
  have hin : ∀ d ∈ Finset.Ico 1 B,
      ∑ s ∈ (Finset.Ico 1 B).filter (fun s => d * s < B),
        (if Nat.Coprime (d * s) 2 then 1 / Real.sqrt (((d * s : ℕ) : ℝ) * d) else 0) ≤
      (if Nat.Coprime d 2 then Real.sqrt y * (1 / ((d : ℝ) * Real.sqrt d)) else 0) := by
    intro d hd
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Ico.mp hd).1
    have hd0 : (0 : ℝ) < d := by linarith
    split_ifs with hdc
    · have hterm : ∀ s ∈ (Finset.Ico 1 B).filter (fun s => d * s < B),
          (if Nat.Coprime (d * s) 2 then 1 / Real.sqrt (((d * s : ℕ) : ℝ) * d) else 0) =
            1 / (d : ℝ) * (if Nat.Coprime s 2 then 1 / Real.sqrt s else 0) := by
        intro s _
        have hiff : Nat.Coprime (d * s) 2 ↔ Nat.Coprime s 2 := by
          rw [Nat.coprime_mul_iff_left]
          exact ⟨fun h => h.2, fun h => ⟨hdc, h⟩⟩
        by_cases hs : Nat.Coprime s 2
        · rw [if_pos (hiff.mpr hs), if_pos hs]
          push_cast
          have : Real.sqrt ((d : ℝ) * s * d) = d * Real.sqrt s := by
            rw [show (d : ℝ) * s * d = d ^ 2 * s by ring, Real.sqrt_mul (by positivity),
              Real.sqrt_sq hd0.le]
          rw [this]
          field_simp
        · rw [if_neg (fun h => hs (hiff.mp h)), if_neg hs, mul_zero]
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Finset.sum_filter]
      have hodd := odd_lt (y / d) (((Finset.Ico 1 B).filter (fun s => d * s < B)).filter
        (fun s => Nat.Coprime s 2)) (by
          intro s hs
          simp only [Finset.mem_filter, Finset.mem_Ico] at hs
          refine ⟨hs.2, ?_⟩
          have h1 : ((d * s : ℕ) : ℝ) < y := Nat.lt_ceil.mp hs.1.2
          push_cast at h1
          rw [lt_div_iff₀ hd0]
          linarith)
      calc 1 / (d : ℝ) * ∑ s ∈ ((Finset.Ico 1 B).filter (fun s => d * s < B)).filter
            (fun s => Nat.Coprime s 2), 1 / Real.sqrt s
          ≤ 1 / (d : ℝ) * Real.sqrt (y / d) :=
            mul_le_mul_of_nonneg_left hodd (by positivity)
        _ = Real.sqrt y * (1 / ((d : ℝ) * Real.sqrt d)) := by
            rw [Real.sqrt_div' _ hd0.le]
            field_simp
    · refine le_of_eq (Finset.sum_eq_zero fun s _ => ?_)
      rw [if_neg]
      intro h
      exact hdc (Nat.Coprime.coprime_mul_right h)
  refine (Finset.sum_le_sum hin).trans ?_
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  have hB1 : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr (by
    rw [hB]
    exact (Nat.ceil_pos.mpr hy).ne')
  have hIco : Finset.Ico 1 B = Finset.Icc 1 (B - 1) := by
    ext d
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [hIco]
  have h2 := M2F.odd32_le (B - 1)
  have hs0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  nlinarith

/-! ## (2) One `(r₁, r₂)` term -/

/-- `σ(2) = 3`. -/
theorem sigma_two : sigma 1 2 = 3 := by
  rw [sigma_one_apply, Nat.Prime.divisors Nat.prime_two, Finset.sum_pair (by norm_num)]

/-- `∑_{e ∣ ab} f(e) ≤ ∑_{a' ∣ a} ∑_{b' ∣ b} f(a'b')` for `f ≥ 0`. -/
theorem sum_divisors_mul_le (a b : ℕ) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    ∑ e ∈ (a * b).divisors, f e ≤ ∑ a' ∈ a.divisors, ∑ b' ∈ b.divisors, f (a' * b') := by
  have hsub : (a * b).divisors ⊆
      (a.divisors ×ˢ b.divisors).image (fun p : ℕ × ℕ => p.1 * p.2) := by
    intro e he
    rw [Nat.mem_divisors] at he
    obtain ⟨k1, k2, h1, h2, rfl⟩ := Nat.dvd_mul.mp he.1
    have ha : a ≠ 0 := left_ne_zero_of_mul he.2
    have hb : b ≠ 0 := right_ne_zero_of_mul he.2
    exact Finset.mem_image.mpr ⟨(k1, k2), Finset.mem_product.mpr
      ⟨Nat.mem_divisors.mpr ⟨h1, ha⟩, Nat.mem_divisors.mpr ⟨h2, hb⟩⟩, rfl⟩
  calc ∑ e ∈ (a * b).divisors, f e
      ≤ ∑ e ∈ (a.divisors ×ˢ b.divisors).image (fun p : ℕ × ℕ => p.1 * p.2), f e :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => hf _
    _ ≤ ∑ p ∈ a.divisors ×ˢ b.divisors, f (p.1 * p.2) :=
        Finset.sum_image_le_of_nonneg fun u _ => hf u
    _ = ∑ a' ∈ a.divisors, ∑ b' ∈ b.divisors, f (a' * b') := Finset.sum_product _ _ _

/-- `∑_a ∑_b ∑_c c₀·(u_a·(v_b·w_c)) = (∑u)·c₀·(∑v)·(∑w)`. -/
theorem triple_sum (A B C : Finset ℕ) (u v w : ℕ → ℝ) (c0 : ℝ) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, c0 * (u a * (v b * w c)) =
      (∑ a ∈ A, u a) * c0 * (∑ b ∈ B, v b) * (∑ c ∈ C, w c) := by
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show u a * c0 * (∑ b ∈ B, v b) * (∑ c ∈ C, w c) =
    u a * c0 * ((∑ b ∈ B, v b) * (∑ c ∈ C, w c)) by ring, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-- `∑_{e ∣ 2r₁r₂} √(z/(r₁r₂e)) ≤ (1 + 1/√2)·√z·h(r₁)h(r₂)`. -/
theorem div_sum_le (z : ℝ) (r1 r2 : ℕ) :
    ∑ e ∈ (2 * r1 * r2).divisors, Real.sqrt (z / ((r1 : ℝ) * r2) / e) ≤
      (1 + 1 / Real.sqrt 2) * Real.sqrt z * hh r1 * hh r2 := by
  set F : ℕ → ℝ := fun n => Real.sqrt (z / ((r1 : ℝ) * r2) / n) with hF
  have hf : ∀ n : ℕ, 0 ≤ F n := fun n => Real.sqrt_nonneg _
  have step1 := sum_divisors_mul_le (2 * r1) r2 F hf
  have step2 := sum_divisors_mul_le 2 r1 (fun a' => ∑ b' ∈ r2.divisors, F (a' * b'))
    (fun n => Finset.sum_nonneg fun _ _ => hf _)
  have hpt : ∀ d3 d1 d2 : ℕ, F (d3 * d1 * d2) =
      Real.sqrt z * (1 / Real.sqrt d3 * (1 / Real.sqrt ((r1 : ℝ) * d1) *
        (1 / Real.sqrt ((r2 : ℝ) * d2)))) := by
    intro d3 d1 d2
    simp only [hF]
    push_cast
    rw [show z / ((r1 : ℝ) * r2) / ((d3 : ℝ) * d1 * d2) =
      z / ((d3 : ℝ) * (((r1 : ℝ) * d1) * ((r2 : ℝ) * d2))) by ring,
      Real.sqrt_div' _ (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity)]
    ring
  have hd2 : ∑ d3 ∈ (2 : ℕ).divisors, 1 / Real.sqrt d3 = 1 + 1 / Real.sqrt 2 := by
    rw [Nat.Prime.divisors Nat.prime_two, Finset.sum_insert (by decide)]
    simp
  calc ∑ e ∈ (2 * r1 * r2).divisors, F e
      ≤ ∑ a' ∈ (2 * r1).divisors, ∑ b' ∈ r2.divisors, F (a' * b') := step1
    _ ≤ ∑ d3 ∈ (2 : ℕ).divisors, ∑ d1 ∈ r1.divisors, ∑ d2 ∈ r2.divisors, F (d3 * d1 * d2) := step2
    _ = ∑ d3 ∈ (2 : ℕ).divisors, ∑ d1 ∈ r1.divisors, ∑ d2 ∈ r2.divisors,
          Real.sqrt z * (1 / Real.sqrt d3 * (1 / Real.sqrt ((r1 : ℝ) * d1) *
            (1 / Real.sqrt ((r2 : ℝ) * d2)))) := by
        refine Finset.sum_congr rfl fun d3 _ => Finset.sum_congr rfl fun d1 _ =>
          Finset.sum_congr rfl fun d2 _ => hpt d3 d1 d2
    _ = (1 + 1 / Real.sqrt 2) * Real.sqrt z * hh r1 * hh r2 := by
        rw [← hd2]
        unfold hh
        exact triple_sum _ _ _ _ _ _ _

/-- The `l`-range endpoint of `eq:cudo` is `b·M`, `b = z/r₁r₂`, `M = max(1/2, r₁/y, r₂/y)`. -/
theorem a_eq (y z : ℝ) (hy : 0 < y) (hz : 0 < z) (r1 r2 : ℕ) (h1 : 0 < r1) (h2 : 0 < r2) :
    max (z / y / ((min r1 r2 : ℕ) : ℝ)) (z / (2 * r1 * r2)) =
      z / ((r1 : ℝ) * r2) * max (1 / 2) (max ((r1 : ℝ) / y) ((r2 : ℝ) / y)) := by
  have h1' : (0 : ℝ) < r1 := by exact_mod_cast h1
  have h2' : (0 : ℝ) < r2 := by exact_mod_cast h2
  have hb : 0 ≤ z / ((r1 : ℝ) * r2) := by positivity
  rw [mul_max_of_nonneg _ _ hb, max_comm]
  rcases le_total r1 r2 with h | h
  · have hr : (r1 : ℝ) / y ≤ (r2 : ℝ) / y :=
      div_le_div_of_nonneg_right (by exact_mod_cast h) hy.le
    rw [min_eq_left h, max_eq_right hr]
    congr 1
    · field_simp
    · field_simp
  · have hr : (r2 : ℝ) / y ≤ (r1 : ℝ) / y :=
      div_le_div_of_nonneg_right (by exact_mod_cast h) hy.le
    rw [min_eq_right h, max_eq_left hr]
    congr 1
    · field_simp
    · field_simp

/-- **One `(r₁, r₂)` term of `srto − (4/π²)z·mutedSum`**, bounded through `CountSq`. -/
theorem term_bd (cc : CountSq) (y z : ℝ) (hy : 0 < y) (hz : 0 < z) (r1 r2 : ℕ)
    (hr1 : r1 ∈ Finset.Ico 1 ⌈y⌉₊) (hr2 : r2 ∈ Finset.Ico 1 ⌈y⌉₊) :
    |(if Nat.Coprime r1 r2 ∧ Nat.Coprime (r1 * r2) 2 then
        ((moebius r1 : ℤ) : ℝ) * ((moebius r2 : ℤ) : ℝ) * M2F.lcnt y z r1 r2 else 0) -
      4 / Real.pi ^ 2 * z * (if Nat.Coprime r1 r2 ∧ Nat.Coprime (r1 * r2) 2 then
        M2F.tm r1 r2 * (1 - max (1 / 2) (max ((r1 : ℝ) / y) ((r2 : ℝ) / y))) else 0)| ≤
      1.5 * ((1 + 1 / Real.sqrt 2) * Real.sqrt z * (if Nat.Coprime r1 2 then hh r1 else 0) *
        (if Nat.Coprime r2 2 then hh r2 else 0)) := by
  have hi1 : 0 ≤ (if Nat.Coprime r1 2 then hh r1 else 0) := by
    split_ifs
    · exact hh_nonneg _
    · exact le_rfl
  have hi2 : 0 ≤ (if Nat.Coprime r2 2 then hh r2 else 0) := by
    split_ifs
    · exact hh_nonneg _
    · exact le_rfl
  have hRHS : 0 ≤ 1.5 * ((1 + 1 / Real.sqrt 2) * Real.sqrt z *
      (if Nat.Coprime r1 2 then hh r1 else 0) * (if Nat.Coprime r2 2 then hh r2 else 0)) := by
    have : 0 ≤ (1 + 1 / Real.sqrt 2) * Real.sqrt z := by positivity
    have := mul_nonneg (mul_nonneg this hi1) hi2
    linarith
  by_cases hc : Nat.Coprime r1 r2 ∧ Nat.Coprime (r1 * r2) 2
  · rw [if_pos hc, if_pos hc]
    obtain ⟨hc12, hc2⟩ := hc
    have ho1 : Nat.Coprime r1 2 := (Nat.coprime_mul_iff_left.mp hc2).1
    have ho2 : Nat.Coprime r2 2 := (Nat.coprime_mul_iff_left.mp hc2).2
    rw [if_pos ho1, if_pos ho2]
    rw [if_pos ho1, if_pos ho2] at hRHS
    have hr1' := Finset.mem_Ico.mp hr1
    have hr2' := Finset.mem_Ico.mp hr2
    have h1p : 0 < r1 := hr1'.1
    have h2p : 0 < r2 := hr2'.1
    have h1R : (0 : ℝ) < r1 := by exact_mod_cast h1p
    have h2R : (0 : ℝ) < r2 := by exact_mod_cast h2p
    have hr1y : (r1 : ℝ) < y := Nat.lt_ceil.mp hr1'.2
    have hr2y : (r2 : ℝ) < y := Nat.lt_ceil.mp hr2'.2
    by_cases hsq : Squarefree r1 ∧ Squarefree r2
    · obtain ⟨hs1, hs2⟩ := hsq
      have h2r1 : Nat.Coprime 2 r1 := ho1.symm
      have h2r2 : Nat.Coprime 2 r2 := ho2.symm
      have hc2r : Nat.Coprime (2 * r1) r2 := Nat.coprime_mul_iff_left.mpr ⟨h2r2, hc12⟩
      have hk : Squarefree (2 * r1 * r2) :=
        Nat.squarefree_mul_iff.mpr ⟨hc2r, Nat.squarefree_mul_iff.mpr
          ⟨h2r1, Nat.prime_two.squarefree, hs1⟩, hs2⟩
      set M := max (1 / 2 : ℝ) (max ((r1 : ℝ) / y) ((r2 : ℝ) / y)) with hM
      set b := z / ((r1 : ℝ) * r2) with hb
      have hM1 : M < 1 := by
        rw [hM]
        refine max_lt (by norm_num) (max_lt ?_ ?_)
        · rw [div_lt_one hy]; exact hr1y
        · rw [div_lt_one hy]; exact hr2y
      have hM2 : 1 / 2 ≤ M := le_max_left _ _
      have hb0 : 0 ≤ b := by positivity
      have haeq := a_eq y z hy hz r1 r2 h1p h2p
      rw [← hb, ← hM] at haeq
      have hlc : M2F.lcnt y z r1 r2 =
          nSq (2 * r1 * r2) (max (z / y / ((min r1 r2 : ℕ) : ℝ)) (z / (2 * r1 * r2))) b := rfl
      have hcnt := cc (2 * r1 * r2) hk
        (max (z / y / ((min r1 r2 : ℕ) : ℝ)) (z / (2 * r1 * r2))) b (by rw [haeq]; positivity)
        (by rw [haeq]; nlinarith) (by rw [haeq]; nlinarith)
      have hs1R : (0 : ℝ) < (sigma 1 r1 : ℝ) := by
        exact_mod_cast (ArithmeticFunction.sigma_pos 1 r1 h1p.ne')
      have hs2R : (0 : ℝ) < (sigma 1 r2 : ℝ) := by
        exact_mod_cast (ArithmeticFunction.sigma_pos 1 r2 h2p.ne')
      have hsk : (sigma 1 (2 * r1 * r2) : ℝ) = 3 * (sigma 1 r1 : ℝ) * (sigma 1 r2 : ℝ) := by
        rw [isMultiplicative_sigma.map_mul_of_coprime hc2r,
          isMultiplicative_sigma.map_mul_of_coprime h2r1, sigma_two]
        push_cast
        ring
      have hmain : 4 / Real.pi ^ 2 * z * (M2F.tm r1 r2 * (1 - M)) =
          ((moebius r1 : ℤ) : ℝ) * ((moebius r2 : ℤ) : ℝ) *
            (6 / Real.pi ^ 2 * (((2 * r1 * r2 : ℕ) : ℝ) / (sigma 1 (2 * r1 * r2) : ℝ)) *
              (b - max (z / y / ((min r1 r2 : ℕ) : ℝ)) (z / (2 * r1 * r2)))) := by
        rw [haeq, hsk, hb]
        unfold M2F.tm
        have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
        push_cast
        field_simp
        ring
      have hmu1 : |((moebius r1 : ℤ) : ℝ)| = 1 := by
        rw [← Int.cast_abs, abs_moebius_eq_one_of_squarefree hs1, Int.cast_one]
      have hmu2 : |((moebius r2 : ℤ) : ℝ)| = 1 := by
        rw [← Int.cast_abs, abs_moebius_eq_one_of_squarefree hs2, Int.cast_one]
      rw [hlc, hmain, ← mul_sub, abs_mul, abs_mul, hmu1, hmu2, one_mul, one_mul]
      refine hcnt.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
      have := div_sum_le z r1 r2
      linarith
    · have h0 : ((moebius r1 : ℤ) : ℝ) * ((moebius r2 : ℤ) : ℝ) = 0 := by
        by_contra hne
        apply hsq
        refine ⟨moebius_ne_zero_iff_squarefree.mp fun h => hne ?_,
          moebius_ne_zero_iff_squarefree.mp fun h => hne ?_⟩
        · rw [h]; simp
        · rw [h]; simp
      have htm : M2F.tm r1 r2 = 0 := by
        unfold M2F.tm
        rw [h0, zero_div]
      rw [h0, htm, zero_mul, zero_mul, mul_zero, sub_zero, abs_zero]
      exact hRHS
  · rw [if_neg hc, if_neg hc, mul_zero, sub_zero, abs_zero]
    exact hRHS

/-! ## (3) `Monro2B` from `CountSq`, and `M2H.MonroFleming` from `Monro2B` -/

/-- **`Monro2B` from `CountSq`, PROVED**: per `(r₁, r₂)` the main terms agree exactly
(`6/π²·k/σ(k) = (4/π²)·r₁r₂/σ(r₁)σ(r₂)` at `k = 2r₁r₂`, and the `l`-interval has length
`(z/r₁r₂)(1 − M)`), the errors are `1.5∑_{e ∣ 2r₁r₂}√(z/r₁r₂e) ≤ 1.5(1 + 1/√2)√z·h(r₁)h(r₂)`,
and `∑_{r < y odd} h(r) ≤ 2√y`; `6(1 + 1/√2) ≤ 10.25`. -/
theorem monro2B_of_count (cc : CountSq) : Monro2B := by
  intro y z hy hz
  have hdiff : M2F.srto y z - 4 / Real.pi ^ 2 * z * M2F.mutedSum y =
      ∑ r1 ∈ Finset.Ico 1 ⌈y⌉₊, ∑ r2 ∈ Finset.Ico 1 ⌈y⌉₊,
        ((if Nat.Coprime r1 r2 ∧ Nat.Coprime (r1 * r2) 2 then
            ((moebius r1 : ℤ) : ℝ) * ((moebius r2 : ℤ) : ℝ) * M2F.lcnt y z r1 r2 else 0) -
          4 / Real.pi ^ 2 * z * (if Nat.Coprime r1 r2 ∧ Nat.Coprime (r1 * r2) 2 then
            M2F.tm r1 r2 * (1 - max (1 / 2) (max ((r1 : ℝ) / y) ((r2 : ℝ) / y))) else 0)) := by
    unfold M2F.srto M2F.mutedSum
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r1 _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hdiff]
  set g : ℕ → ℝ := fun r => if Nat.Coprime r 2 then hh r else 0 with hg
  have hg0 : ∀ r, 0 ≤ g r := fun r => by
    simp only [hg]
    split_ifs
    · exact hh_nonneg _
    · exact le_rfl
  have hsum := hh_sum y hy
  have hG0 : 0 ≤ ∑ r ∈ Finset.Ico 1 ⌈y⌉₊, g r := Finset.sum_nonneg fun r _ => hg0 r
  have hc0 : 0 ≤ 1.5 * ((1 + 1 / Real.sqrt 2) * Real.sqrt z) := by positivity
  have hs2 : 1 / Real.sqrt 2 ≤ 0.7072 := by
    have h2 : (1.4142 : ℝ) ≤ Real.sqrt 2 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  calc _ ≤ ∑ r1 ∈ Finset.Ico 1 ⌈y⌉₊, |∑ r2 ∈ Finset.Ico 1 ⌈y⌉₊, _| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r1 ∈ Finset.Ico 1 ⌈y⌉₊, ∑ r2 ∈ Finset.Ico 1 ⌈y⌉₊, 1.5 * ((1 + 1 / Real.sqrt 2) *
          Real.sqrt z * g r1 * g r2) := by
        refine Finset.sum_le_sum fun r1 hr1 => (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun r2 hr2 => ?_)
        exact term_bd cc y z hy hz r1 r2 hr1 hr2
    _ = 1.5 * ((1 + 1 / Real.sqrt 2) * Real.sqrt z) *
          ((∑ r ∈ Finset.Ico 1 ⌈y⌉₊, g r) * (∑ r ∈ Finset.Ico 1 ⌈y⌉₊, g r)) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r1 _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r2 _ => ?_
        ring
    _ ≤ 1.5 * ((1 + 1 / Real.sqrt 2) * Real.sqrt z) * ((2 * Real.sqrt y) * (2 * Real.sqrt y)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hsum hsum hG0 (by positivity)) hc0
    _ ≤ 10.25 * y * Real.sqrt z := by
        have hy2 : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy.le
        have hz0 : 0 ≤ Real.sqrt z := Real.sqrt_nonneg z
        have e : 1.5 * ((1 + 1 / Real.sqrt 2) * Real.sqrt z) *
            ((2 * Real.sqrt y) * (2 * Real.sqrt y)) =
            6 * (1 + 1 / Real.sqrt 2) * (y * Real.sqrt z) := by
          rw [show (2 * Real.sqrt y) * (2 * Real.sqrt y) = 4 * (Real.sqrt y * Real.sqrt y) by ring,
            hy2]
          ring
        rw [e]
        have hyz : 0 ≤ y * Real.sqrt z := by positivity
        have h6 : 6 * (1 + 1 / Real.sqrt 2) ≤ 10.25 := by linarith
        calc 6 * (1 + 1 / Real.sqrt 2) * (y * Real.sqrt z) ≤ 10.25 * (y * Real.sqrt z) :=
              mul_le_mul_of_nonneg_right h6 hyz
          _ = 10.25 * y * Real.sqrt z := by ring

/-- **`M2H.MonroFleming` from `Monro2B`, PROVED** (`M2F.monroFleming_of_links` with
`M2C.crustoCudo_holds` and the constant `10.25`: `2·10.25 = 20.5 ≤ 22.6418`). -/
theorem monroFlem_of_monro2B (mo : Monro2B) : M2H.MonroFleming := by
  intro x U W hU hW hUW
  have hW0 : 0 < W := by linarith
  have hU0 : 0 < U := by linarith
  have hx : 0 < x := by nlinarith
  have hxW : 0 < x / W := by positivity
  rw [M2C.crustoCudo_holds x U W hU hW hUW]
  set S := x / (W * U) with hSdef
  have hS0 : 0 < S := by positivity
  have hterm : ∀ s ∈ (Finset.Icc 1 ⌊S⌋₊).filter (fun s => Nat.Coprime s 2),
      M2F.srto (S / s) (x / W / s) ≤
        x / W * (4 / Real.pi ^ 2 * (1 / (s : ℝ) * ∫ u in (1 / 2 : ℝ)..1, HC.gYutto 2 (u * S / s)))
          + 10.25 * S * Real.sqrt (x / W) * (1 / ((s : ℝ) * Real.sqrt s)) := by
    intro s hs
    have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
    have hs0 : (0 : ℝ) < s := by linarith
    have hy : 0 < S / s := by positivity
    have hz : 0 < x / W / s := by positivity
    have h1 := (abs_le.mp (mo (S / s) (x / W / s) hy hz)).2
    rw [M2F.muted_eq (S / s) hy] at h1
    have e1 : ∫ u in (1 / 2 : ℝ)..1, HC.gYutto 2 (u * (S / s)) =
        ∫ u in (1 / 2 : ℝ)..1, HC.gYutto 2 (u * S / s) := by
      congr 1
      funext u
      rw [mul_div_assoc]
    rw [e1] at h1
    have hsq : Real.sqrt (x / W / s) = Real.sqrt (x / W) / Real.sqrt s :=
      Real.sqrt_div' _ hs0.le
    have hss : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
    have e2 : 10.25 * (S / s) * Real.sqrt (x / W / s) =
        10.25 * S * Real.sqrt (x / W) * (1 / ((s : ℝ) * Real.sqrt s)) := by
      rw [hsq]
      field_simp
    have e3 : 4 / Real.pi ^ 2 * (x / W / s) * ∫ u in (1 / 2 : ℝ)..1, HC.gYutto 2 (u * S / s) =
        x / W * (4 / Real.pi ^ 2 * (1 / (s : ℝ) * ∫ u in (1 / 2 : ℝ)..1,
          HC.gYutto 2 (u * S / s))) := by ring
    linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have hodd := M2F.odd32_le ⌊S⌋₊
  have hP0 : 0 ≤ x / W * Real.sqrt (x / W) / U := by positivity
  have h2 : 10.25 * S * Real.sqrt (x / W) *
      ∑ s ∈ (Finset.Icc 1 ⌊S⌋₊).filter (fun s => Nat.Coprime s 2),
        1 / ((s : ℝ) * Real.sqrt s) ≤ 10.25 * S * Real.sqrt (x / W) * 2 :=
    mul_le_mul_of_nonneg_left hodd (by positivity)
  have hSP : 10.25 * S * Real.sqrt (x / W) * 2 = 20.5 * (x / W * Real.sqrt (x / W) / U) := by
    rw [hSdef]
    field_simp
    ring
  have hr : 22.6418 * (x / W) ^ ((3 : ℝ) / 2) / U = 22.6418 * (x / W * Real.sqrt (x / W) / U) := by
    rw [M2F.rp32 _ hxW]
    ring
  have hc : HC.cortoLHS 2 S = ∑ s ∈ (Finset.Icc 1 ⌊S⌋₊).filter (fun s => Nat.Coprime s 2),
      1 / (s : ℝ) * ∫ u in (1 / 2 : ℝ)..1, HC.gYutto 2 (u * S / s) := rfl
  rw [hr, ← hc]
  nlinarith

end Principia.Common.TernaryGoldbach.M2B
