/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIIMonroFleming

set_option autoImplicit false

/-!
# `M2F.CrustoCudo` PROVED: `eq:crusto` + `eq:cudo` as an exact identity of finite sums

`M2F.CrustoCudo` (`TypeIIMonroFleming`, `7878a7d8`) asks, for `1 ≤ U`, `1 ≤ W`, `UW ≤ x`,
`S = x/WU`,

`S₁(U, W) = ∑_{max(x/2W, U) < m ≤ x/W, m odd} (∑_{d ∣ m, d > U} μ(d))²
          = ∑_{s ≤ S odd} srto(S/s, x/Ws)`,

`minarcs.tex` 2640-2665. Proved here by the book's change of variables
`d₁ = r₁l`, `d₂ = r₂l`, `l = (d₁, d₂)`, `m = r₁r₂ls`, made a bijection between the NON-ZERO terms
(`Finset.sum_bij_ne_zero`): `μ(d₁)μ(d₂) ≠ 0` forces `d₁, d₂` square-free, hence `l` square-free
and coprime to `r₁r₂`, `μ(r₁l)μ(r₂l) = μ(r₁)μ(r₂)`; oddness of `m` gives oddness of `s, r₁, r₂, l`.
The real side conditions match exactly (`real_fwd`, `real_bwd`): `m ≤ x/W ⟺ l ≤ (x/Ws)/r₁r₂`,
`m > x/2W ⟺ l > (x/Ws)/2r₁r₂`, `r₁l, r₂l > U ⟺ l > U/min(r₁, r₂)` (with `z/y = U`), and
`r_i < S/s`, `s ≤ S` are implied (`r₁sU < r₁s·r₂l = m ≤ x/W`).

```
 sum_dep        nested dependent sums as one sum over a flat Finset             PROVED
 split / join   (m, d₁, d₂) ↔ (s, r₁, r₂, l), mutually inverse on the supports  PROVED
 s1_flat        S₁ = ∑_{(m, d₁, d₂)} μ(d₁)μ(d₂)                                PROVED
 rhs_flat       ∑_s srto(S/s, x/Ws) = ∑_{(s, r₁, r₂, l)} [cnd] μ(r₁)μ(r₂)      PROVED
 crustoCudo_holds         : M2F.CrustoCudo                                      PROVED
 monroFleming_of_monro2   : M2F.Monro2 → M2H.MonroFleming                      PROVED
```

So `M2H.MonroFleming` now owes exactly `M2F.Monro2` (`lem:monro`, `eq:mudo`).
-/

namespace Principia.Common.TernaryGoldbach.M2C

open ArithmeticFunction

/-! ## (0) Dependent products of finsets -/

/-- `{(c, a) : c ∈ s, a ∈ t c}`. -/
def dep {γ α : Type} [DecidableEq α] (s : Finset γ) (t : γ → Finset α) : Finset (γ × α) :=
  (s ×ˢ s.biUnion t).filter (fun p => p.2 ∈ t p.1)

theorem mem_dep {γ α : Type} [DecidableEq α] (s : Finset γ) (t : γ → Finset α) (p : γ × α) :
    p ∈ dep s t ↔ p.1 ∈ s ∧ p.2 ∈ t p.1 := by
  unfold dep
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, p.1, h1, h2⟩, h2⟩

theorem sum_dep {γ α : Type} [DecidableEq α] (s : Finset γ) (t : γ → Finset α)
    (f : γ × α → ℝ) : ∑ c ∈ s, ∑ a ∈ t c, f (c, a) = ∑ p ∈ dep s t, f p :=
  (Finset.sum_finset_product _ s t (fun p => mem_dep s t p)).symm

/-! ## (1) Arithmetic of the change of variables `d₁ = r₁l`, `d₂ = r₂l`, `m = r₁r₂ls` -/

/-- `μ(r₁l)μ(r₂l) = μ(r₁)μ(r₂)` for square-free `l` coprime to `r₁`, `r₂`. -/
theorem mu_pair (r1 r2 l : ℕ) (h1 : Nat.Coprime r1 l) (h2 : Nat.Coprime r2 l)
    (hl : Squarefree l) :
    (moebius (r1 * l) : ℤ) * moebius (r2 * l) = moebius r1 * moebius r2 := by
  rw [isMultiplicative_moebius.map_mul_of_coprime h1,
    isMultiplicative_moebius.map_mul_of_coprime h2]
  have hsq : (moebius l : ℤ) * moebius l = 1 := by
    have := abs_moebius_eq_one_of_squarefree hl
    rcases abs_eq (zero_le_one' ℤ) |>.mp this with h | h <;> rw [h] <;> norm_num
  calc (moebius r1 : ℤ) * moebius l * (moebius r2 * moebius l)
      = moebius r1 * moebius r2 * (moebius l * moebius l) := by ring
    _ = moebius r1 * moebius r2 := by rw [hsq, mul_one]

/-- The splitting map `(m, d₁, d₂) ↦ (s, r₁, r₂, l)`, `l = (d₁, d₂)`. -/
def split (a : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (a.1 / (a.2.1 / Nat.gcd a.2.1 a.2.2 * (a.2.2 / Nat.gcd a.2.1 a.2.2) * Nat.gcd a.2.1 a.2.2),
    a.2.1 / Nat.gcd a.2.1 a.2.2, a.2.2 / Nat.gcd a.2.1 a.2.2, Nat.gcd a.2.1 a.2.2)

/-- Its inverse `(s, r₁, r₂, l) ↦ (r₁r₂ls, r₁l, r₂l)`. -/
def join (b : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (b.2.1 * b.2.2.1 * b.2.2.2 * b.1, b.2.1 * b.2.2.2, b.2.2.1 * b.2.2.2)

theorem split_facts (m d1 d2 : ℕ) (h1 : d1 ∣ m) (h2 : d2 ∣ m) (hm : m ≠ 0) :
    0 < Nat.gcd d1 d2 ∧ d1 / Nat.gcd d1 d2 * Nat.gcd d1 d2 = d1 ∧
      d2 / Nat.gcd d1 d2 * Nat.gcd d1 d2 = d2 ∧
      d1 / Nat.gcd d1 d2 * (d2 / Nat.gcd d1 d2) * Nat.gcd d1 d2 *
        (m / (d1 / Nat.gcd d1 d2 * (d2 / Nat.gcd d1 d2) * Nat.gcd d1 d2)) = m ∧
      Nat.Coprime (d1 / Nat.gcd d1 d2) (d2 / Nat.gcd d1 d2) := by
  have hd1 : 0 < d1 := Nat.pos_of_dvd_of_pos h1 (Nat.pos_of_ne_zero hm)
  set g := Nat.gcd d1 d2 with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hd1
  have e1 : d1 / g * g = d1 := Nat.div_mul_cancel (Nat.gcd_dvd_left d1 d2)
  have e2 : d2 / g * g = d2 := Nat.div_mul_cancel (Nat.gcd_dvd_right d1 d2)
  have hL : d1 / g * (d2 / g) * g = Nat.lcm d1 d2 := by
    refine Nat.eq_of_mul_eq_mul_left hg0 ?_
    rw [Nat.gcd_mul_lcm]
    calc g * (d1 / g * (d2 / g) * g) = (d1 / g * g) * (d2 / g * g) := by ring
      _ = d1 * d2 := by rw [e1, e2]
  refine ⟨hg0, e1, e2, ?_, Nat.coprime_div_gcd_div_gcd hg0⟩
  rw [hL]
  exact Nat.mul_div_cancel' (Nat.lcm_dvd h1 h2)

theorem join_split (m d1 d2 : ℕ) (h1 : d1 ∣ m) (h2 : d2 ∣ m) (hm : m ≠ 0) :
    join (split (m, d1, d2)) = (m, d1, d2) := by
  obtain ⟨_, e1, e2, e3, _⟩ := split_facts m d1 d2 h1 h2 hm
  simp only [split, join]
  rw [e1, e2, e3]

theorem split_join (s r1 r2 l : ℕ) (hl : 0 < l) (h1 : 0 < r1) (h2 : 0 < r2)
    (hr : Nat.Coprime r1 r2) : split (join (s, r1, r2, l)) = (s, r1, r2, l) := by
  simp only [split, join]
  have hg : Nat.gcd (r1 * l) (r2 * l) = l := by
    rw [Nat.gcd_mul_right, hr.gcd_eq_one, one_mul]
  rw [hg, Nat.mul_div_cancel _ hl, Nat.mul_div_cancel _ hl]
  have hp : 0 < r1 * r2 * l := by positivity
  rw [show r1 * r2 * l * s = s * (r1 * r2 * l) by ring, Nat.mul_div_cancel _ hp]

/-! ## (2) The real side conditions -/

theorem real_fwd (x U W : ℝ) (hU : 1 ≤ U) (hW : 1 ≤ W) (hUW : U * W ≤ x)
    (r1 r2 l s : ℕ) (h1 : 1 ≤ r1) (h2 : 1 ≤ r2) (hs : 1 ≤ s)
    (hl : l ≤ ⌊x / W / s / ((r1 : ℝ) * r2)⌋₊)
    (hlo : max (x / W / s / (x / (W * U) / s) / ((min r1 r2 : ℕ) : ℝ))
      (x / W / s / (2 * r1 * r2)) < l) :
    (r1 : ℝ) * r2 * l * s ≤ x / W ∧ x / (2 * W) < (r1 : ℝ) * r2 * l * s ∧
      U < (r1 : ℝ) * l ∧ U < (r2 : ℝ) * l := by
  have hW0 : 0 < W := by linarith
  have hU0 : 0 < U := by linarith
  have hx : 0 < x := by nlinarith
  have hr1 : (1 : ℝ) ≤ r1 := by exact_mod_cast h1
  have hr2 : (1 : ℝ) ≤ r2 := by exact_mod_cast h2
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hzy : x / W / s / (x / (W * U) / s) = U := by field_simp
  rw [hzy, max_lt_iff] at hlo
  obtain ⟨hlo1, hlo2⟩ := hlo
  refine ⟨?_, ?_, ?_⟩
  · have h := le_trans (Nat.cast_le.mpr hl) (Nat.floor_le (by positivity))
    rw [le_div_iff₀ (by positivity), le_div_iff₀ (by positivity),
      le_div_iff₀ (by positivity)] at h
    rw [le_div_iff₀ hW0]
    nlinarith
  · rw [div_lt_iff₀ (by positivity), div_lt_iff₀ (by positivity),
      div_lt_iff₀ (by positivity)] at hlo2
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  · rcases le_total r1 r2 with h | h
    · rw [min_eq_left h, div_lt_iff₀ (by positivity)] at hlo1
      have : (r1 : ℝ) ≤ r2 := by exact_mod_cast h
      constructor <;> nlinarith
    · rw [min_eq_right h, div_lt_iff₀ (by positivity)] at hlo1
      have : (r2 : ℝ) ≤ r1 := by exact_mod_cast h
      constructor <;> nlinarith

theorem real_bwd (x U W : ℝ) (hU : 1 ≤ U) (hW : 1 ≤ W) (hUW : U * W ≤ x)
    (r1 r2 l s : ℕ) (h1 : 1 ≤ r1) (h2 : 1 ≤ r2) (hs : 1 ≤ s)
    (hm : (r1 : ℝ) * r2 * l * s ≤ x / W) (hm2 : x / (2 * W) < (r1 : ℝ) * r2 * l * s)
    (hd1 : U < (r1 : ℝ) * l) (hd2 : U < (r2 : ℝ) * l) :
    s ≤ ⌊x / (W * U)⌋₊ ∧ r1 < ⌈x / (W * U) / s⌉₊ ∧ r2 < ⌈x / (W * U) / s⌉₊ ∧
      l ≤ ⌊x / W / s / ((r1 : ℝ) * r2)⌋₊ ∧
      max (x / W / s / (x / (W * U) / s) / ((min r1 r2 : ℕ) : ℝ))
        (x / W / s / (2 * r1 * r2)) < l := by
  have hW0 : 0 < W := by linarith
  have hU0 : 0 < U := by linarith
  have hx : 0 < x := by nlinarith
  have hr1 : (1 : ℝ) ≤ r1 := by exact_mod_cast h1
  have hr2 : (1 : ℝ) ≤ r2 := by exact_mod_cast h2
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hzy : x / W / s / (x / (W * U) / s) = U := by field_simp
  rw [hzy]
  rw [le_div_iff₀ hW0] at hm
  rw [div_lt_iff₀ (by positivity)] at hm2
  refine ⟨Nat.le_floor ?_, Nat.lt_ceil.mpr ?_, Nat.lt_ceil.mpr ?_, Nat.le_floor ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hd1.le (by positivity : (0 : ℝ) ≤ s * W * r2)]
  · rw [lt_div_iff₀ (by positivity), lt_div_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left hd2 (by positivity : (0 : ℝ) < r1 * s * W)]
  · rw [lt_div_iff₀ (by positivity), lt_div_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left hd1 (by positivity : (0 : ℝ) < r2 * s * W)]
  · rw [le_div_iff₀ (by positivity), le_div_iff₀ (by positivity), le_div_iff₀ hW0]
    nlinarith
  · rw [max_lt_iff]
    constructor
    · rcases le_total r1 r2 with h | h
      · rw [min_eq_left h, div_lt_iff₀ (by positivity)]
        linarith
      · rw [min_eq_right h, div_lt_iff₀ (by positivity)]
        linarith
    · rw [div_lt_iff₀ (by positivity), div_lt_iff₀ (by positivity),
        div_lt_iff₀ (by positivity)]
      nlinarith

/-! ## (3) Both sides as sums over flat index sets -/

/-- The `d`-range of `c_m = ∑_{d ∣ m, d > U} μ(d)`. -/
noncomputable def dSet (U : ℝ) (m : ℕ) : Finset ℕ :=
  m.divisors.filter (fun d : ℕ => U < (d : ℝ))

/-- `{(m, d₁, d₂)}`: the index set of `S₁` expanded. -/
noncomputable def aSet (x U W : ℝ) : Finset (ℕ × ℕ × ℕ) :=
  dep (T2S.mSet x U W) (fun m => dSet U m ×ˢ dSet U m)

/-- The `s`-range of `eq:crusto`. -/
noncomputable def sSet (x U W : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊x / (W * U)⌋₊).filter (fun s => Nat.Coprime s 2)

/-- The `r`-range of `eq:srto` at `y = S/s`. -/
noncomputable def rSet (x U W : ℝ) (s : ℕ) : Finset ℕ :=
  Finset.Ico 1 ⌈x / (W * U) / s⌉₊

/-- The `l`-range of `eq:cudo` at `y = S/s`, `z = x/Ws`. -/
noncomputable def lSet (x U W : ℝ) (s r1 r2 : ℕ) : Finset ℕ :=
  (Finset.Icc 1 ⌊x / W / s / ((r1 : ℝ) * r2)⌋₊).filter (fun l : ℕ =>
    max (x / W / s / (x / (W * U) / s) / ((min r1 r2 : ℕ) : ℝ)) (x / W / s / (2 * r1 * r2)) <
      (l : ℝ) ∧ Nat.Coprime l (2 * r1 * r2) ∧ Squarefree l)

/-- `{(s, r₁, r₂, l)}`: the index set of `eq:crusto`'s right side. -/
noncomputable def bSet (x U W : ℝ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  dep (sSet x U W) (fun s => dep (rSet x U W s) (fun r1 => dep (rSet x U W s) (lSet x U W s r1)))

/-- The `(r₁, r₂)` weight of `eq:srto`. -/
noncomputable def gT (r1 r2 : ℕ) : ℝ :=
  if Nat.Coprime r1 r2 ∧ Nat.Coprime (r1 * r2) 2 then
    ((moebius r1 : ℤ) : ℝ) * ((moebius r2 : ℤ) : ℝ)
  else 0

theorem s1_flat (x U W : ℝ) : T2S.s1 x U W =
    ∑ a ∈ aSet x U W, ((moebius a.2.1 : ℤ) : ℝ) * ((moebius a.2.2 : ℤ) : ℝ) := by
  unfold aSet
  rw [← sum_dep]
  unfold T2S.s1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_product]
  unfold T2S.cU dSet
  rw [sq, Finset.sum_mul_sum]

theorem srto_eq (x U W : ℝ) (s : ℕ) :
    M2F.srto (x / (W * U) / s) (x / W / s) =
      ∑ r1 ∈ rSet x U W s, ∑ r2 ∈ rSet x U W s, ∑ _l ∈ lSet x U W s r1 r2, gT r1 r2 := by
  unfold M2F.srto M2F.lcnt rSet
  refine Finset.sum_congr rfl fun r1 _ => Finset.sum_congr rfl fun r2 _ => ?_
  unfold gT lSet
  split_ifs
  · rw [Finset.sum_const, nsmul_eq_mul]
    ring
  · simp

theorem rhs_flat (x U W : ℝ) :
    ∑ s ∈ (Finset.Icc 1 ⌊x / (W * U)⌋₊).filter (fun s => Nat.Coprime s 2),
      M2F.srto (x / (W * U) / s) (x / W / s) = ∑ w ∈ bSet x U W, gT w.2.1 w.2.2.1 := by
  unfold bSet
  rw [← sum_dep]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [srto_eq, ← sum_dep]
  refine Finset.sum_congr rfl fun r1 _ => ?_
  rw [← sum_dep]

/-! ## (4) The bijection -/

theorem memA (x U W : ℝ) (m d1 d2 : ℕ) (ha : (m, d1, d2) ∈ aSet x U W) :
    m ∈ T2S.mSet x U W ∧ (d1 ∣ m ∧ U < (d1 : ℝ)) ∧ (d2 ∣ m ∧ U < (d2 : ℝ)) ∧ m ≠ 0 := by
  unfold aSet dSet at ha
  simp only [mem_dep, Finset.mem_product, Finset.mem_filter, Nat.mem_divisors] at ha
  exact ⟨ha.1, ⟨ha.2.1.1.1, ha.2.1.2⟩, ⟨ha.2.2.1.1, ha.2.2.2⟩, ha.2.1.1.2⟩

theorem split_good (x U W : ℝ) (hU : 1 ≤ U) (hW : 1 ≤ W) (hUW : U * W ≤ x) (m d1 d2 : ℕ)
    (ha : (m, d1, d2) ∈ aSet x U W)
    (hf : ((moebius d1 : ℤ) : ℝ) * ((moebius d2 : ℤ) : ℝ) ≠ 0) :
    split (m, d1, d2) ∈ bSet x U W ∧
      ((moebius d1 : ℤ) : ℝ) * ((moebius d2 : ℤ) : ℝ) =
        gT (split (m, d1, d2)).2.1 (split (m, d1, d2)).2.2.1 := by
  obtain ⟨hmS, ⟨hd1m, hUd1⟩, ⟨hd2m, hUd2⟩, hm0⟩ := memA x U W m d1 d2 ha
  have hsq1 : Squarefree d1 :=
    moebius_ne_zero_iff_squarefree.mp fun h => hf (by rw [h]; simp)
  have hsq2 : Squarefree d2 :=
    moebius_ne_zero_iff_squarefree.mp fun h => hf (by rw [h]; simp)
  obtain ⟨hg0, e1, e2, e3, hcop⟩ := split_facts m d1 d2 hd1m hd2m hm0
  simp only [split]
  set g := Nat.gcd d1 d2 with hg
  set r1 := d1 / g with hr1
  set r2 := d2 / g with hr2
  set s := m / (r1 * r2 * g) with hs
  have hd1 : 0 < d1 := Nat.pos_of_dvd_of_pos hd1m (Nat.pos_of_ne_zero hm0)
  have hd2 : 0 < d2 := Nat.pos_of_dvd_of_pos hd2m (Nat.pos_of_ne_zero hm0)
  have hr1p : 0 < r1 := Nat.pos_of_ne_zero fun h => by rw [h, zero_mul] at e1; omega
  have hr2p : 0 < r2 := Nat.pos_of_ne_zero fun h => by rw [h, zero_mul] at e2; omega
  have hsp : 0 < s := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at e3; omega
  rw [← e1] at hsq1
  rw [← e2] at hsq2
  obtain ⟨hc1, -, hsqg⟩ := Nat.squarefree_mul_iff.mp hsq1
  obtain ⟨hc2, -, -⟩ := Nat.squarefree_mul_iff.mp hsq2
  unfold T2S.mSet at hmS
  rw [Finset.mem_filter, Finset.mem_Icc] at hmS
  obtain ⟨⟨-, hmN⟩, hodd, hmax⟩ := hmS
  have hoddm : Odd m := Nat.odd_iff.mpr hodd
  rw [← e3] at hoddm
  obtain ⟨hodd3, hodds⟩ := Nat.odd_mul.mp hoddm
  obtain ⟨hodd12, hoddg⟩ := Nat.odd_mul.mp hodd3
  have hmR : (m : ℝ) = (r1 : ℝ) * r2 * g * s := by
    rw [← e3]
    push_cast
    ring
  have hd1R : (d1 : ℝ) = (r1 : ℝ) * g := by
    rw [← e1]
    push_cast
    ring
  have hd2R : (d2 : ℝ) = (r2 : ℝ) * g := by
    rw [← e2]
    push_cast
    ring
  have hmx : (m : ℝ) ≤ x / W :=
    le_trans (Nat.cast_le.mpr hmN) (Nat.floor_le (by
      have : (0 : ℝ) < W := by linarith
      have : (0 : ℝ) < x := by nlinarith
      positivity))
  rw [max_lt_iff] at hmax
  obtain ⟨f1, f2, f3, f4, f5⟩ := real_bwd x U W hU hW hUW r1 r2 g s hr1p hr2p hsp
    (by rw [← hmR]; exact hmx) (by rw [← hmR]; exact hmax.1) (by rw [← hd1R]; exact hUd1)
    (by rw [← hd2R]; exact hUd2)
  have hcg : Nat.Coprime g (2 * r1 * r2) :=
    Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.coprime_two_right.mpr hoddg) hc1.symm)
      hc2.symm
  refine ⟨?_, ?_⟩
  · simp only [bSet, mem_dep, sSet, rSet, lSet, Finset.mem_filter, Finset.mem_Icc,
      Finset.mem_Ico]
    exact ⟨⟨⟨hsp, f1⟩, Nat.coprime_two_right.mpr hodds⟩, ⟨hr1p, f2⟩, ⟨hr2p, f3⟩,
      ⟨hg0, f4⟩, f5, hcg, hsqg⟩
  · unfold gT
    rw [if_pos ⟨hcop, Nat.coprime_two_right.mpr hodd12⟩]
    rw [← Int.cast_mul, ← Int.cast_mul]
    congr 1
    conv_lhs => rw [← e1, ← e2]
    exact mu_pair r1 r2 g hc1 hc2 hsqg

theorem join_good (x U W : ℝ) (hU : 1 ≤ U) (hW : 1 ≤ W) (hUW : U * W ≤ x) (s r1 r2 l : ℕ)
    (hb : (s, r1, r2, l) ∈ bSet x U W) (hgb : gT r1 r2 ≠ 0) :
    join (s, r1, r2, l) ∈ aSet x U W ∧
      ((moebius (r1 * l) : ℤ) : ℝ) * ((moebius (r2 * l) : ℤ) : ℝ) ≠ 0 ∧
      split (join (s, r1, r2, l)) = (s, r1, r2, l) := by
  simp only [bSet, mem_dep, sSet, rSet, lSet, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_Ico] at hb
  obtain ⟨⟨⟨hs1, -⟩, hs2⟩, ⟨hr1, -⟩, ⟨hr2, -⟩, ⟨hl1, hlN⟩, hlo, hcl, hsql⟩ := hb
  unfold gT at hgb
  split_ifs at hgb with hc
  · obtain ⟨hm, hm2, hd1, hd2⟩ := real_fwd x U W hU hW hUW r1 r2 l s hr1 hr2 hs1 hlN hlo
    have hcl2 : Nat.Coprime l 2 := Nat.Coprime.coprime_dvd_right ⟨r1 * r2, by ring⟩ hcl
    have hcl1 : Nat.Coprime r1 l :=
      (Nat.Coprime.coprime_dvd_right ⟨2 * r2, by ring⟩ hcl).symm
    have hcl3 : Nat.Coprime r2 l :=
      (Nat.Coprime.coprime_dvd_right ⟨2 * r1, by ring⟩ hcl).symm
    have hoddm : Odd (r1 * r2 * l * s) :=
      Nat.odd_mul.mpr ⟨Nat.odd_mul.mpr ⟨Nat.coprime_two_right.mp hc.2,
        Nat.coprime_two_right.mp hcl2⟩, Nat.coprime_two_right.mp hs2⟩
    have hmpos : 0 < r1 * r2 * l * s := by positivity
    have hr2s : (1 : ℝ) ≤ (r2 : ℝ) * s := by
      have : 1 ≤ r2 * s := Nat.one_le_iff_ne_zero.mpr (by positivity)
      exact_mod_cast this
    have hr1s : (1 : ℝ) ≤ (r1 : ℝ) * s := by
      have : 1 ≤ r1 * s := Nat.one_le_iff_ne_zero.mpr (by positivity)
      exact_mod_cast this
    have hl0 : (0 : ℝ) < l := by exact_mod_cast hl1
    have hr10 : (0 : ℝ) < r1 := by exact_mod_cast hr1
    refine ⟨?_, ?_, split_join s r1 r2 l hl1 hr1 hr2 hc.1⟩
    · simp only [join, aSet, dSet, T2S.mSet, mem_dep, Finset.mem_product, Finset.mem_filter,
        Nat.mem_divisors, Finset.mem_Icc]
      push_cast
      refine ⟨⟨⟨hmpos, Nat.le_floor (by push_cast; exact hm)⟩, Nat.odd_iff.mp hoddm,
        max_lt hm2 ?_⟩, ⟨⟨⟨r2 * s, by ring⟩, hmpos.ne'⟩, hd1⟩, ⟨⟨r1 * s, by ring⟩, hmpos.ne'⟩,
        hd2⟩
      nlinarith
    · rw [← Int.cast_mul, mu_pair r1 r2 l hcl1 hcl3 hsql, Int.cast_mul]
      exact hgb
  · exact absurd rfl hgb

/-! ## (5) `CrustoCudo`, PROVED -/

/-- **`M2F.CrustoCudo` — `eq:crusto` + `eq:cudo`, PROVED**: the change of variables
`(m, d₁, d₂) ↦ (s, r₁, r₂, l)`, `l = (d₁, d₂)`, `d_i = r_il`, `m = r₁r₂ls`, is a bijection between
the non-zero terms of `S₁ = ∑_m (∑_{d ∣ m, d > U} μ(d))²` and those of
`∑_s ∑_{r₁, r₂} μ(r₁)μ(r₂)·lcnt`. -/
theorem crustoCudo_holds : M2F.CrustoCudo := by
  intro x U W hU hW hUW
  rw [s1_flat, rhs_flat]
  refine Finset.sum_bij_ne_zero (fun a _ _ => split a) ?_ ?_ ?_ ?_
  · rintro ⟨m, d1, d2⟩ ha hf
    exact (split_good x U W hU hW hUW m d1 d2 ha hf).1
  · rintro ⟨m, d1, d2⟩ ha _ ⟨m', d1', d2'⟩ ha' _ he
    obtain ⟨-, ⟨h1, -⟩, ⟨h2, -⟩, h0⟩ := memA x U W m d1 d2 ha
    obtain ⟨-, ⟨h1', -⟩, ⟨h2', -⟩, h0'⟩ := memA x U W m' d1' d2' ha'
    have := congrArg join he
    rwa [join_split m d1 d2 h1 h2 h0, join_split m' d1' d2' h1' h2' h0'] at this
  · rintro ⟨s, r1, r2, l⟩ hb hgb
    obtain ⟨hA, hf, hsj⟩ := join_good x U W hU hW hUW s r1 r2 l hb hgb
    exact ⟨join (s, r1, r2, l), hA, hf, hsj⟩
  · rintro ⟨m, d1, d2⟩ ha hf
    exact (split_good x U W hU hW hUW m d1 d2 ha hf).2

/-- **`M2H.MonroFleming` from `M2F.Monro2` alone, PROVED** (`M2F.monroFleming_of_links` with
`crustoCudo_holds`). -/
theorem monroFleming_of_monro2 (mo : M2F.Monro2) : M2H.MonroFleming :=
  M2F.monroFleming_of_links crustoCudo_holds mo

end Principia.Common.TernaryGoldbach.M2C
