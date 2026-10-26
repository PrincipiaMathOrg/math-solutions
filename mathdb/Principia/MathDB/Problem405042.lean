import Mathlib.Data.Real.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Constructions
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# MathDB #405042 — two multi-affine equations with exponentially many components

Write-up: `mathdb-open-problems/problems/405042/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress`.
Source: Basu, contribution to **Oberwolfach Report 9/2025, pp. 445–446**, asking whether
two real *multi-affine* equations of bounded total degree have a number of real connected
components bounded independently of the number of variables.  (Multi-affine = degree at
most one in each individual variable.)  The answer is **no**.

## The witness

In `2m` variables `x₁,y₁,…,x_m,y_m` — here indexed by `Var m = Bool × Fin m`, with
`(false,i) ↦ xᵢ` and `(true,i) ↦ yᵢ` — put `zᵢ = xᵢyᵢ` and

`F = ∑ᵢ zᵢ − m`,  `G = ∑_{i<j} zᵢzⱼ − m(m−1)/2`.

(`m(m−1)/2` is `C(m,2)`, written in real arithmetic so no natural subtraction appears.)

## What is proved

* `Fp_multiaffine`, `Gp_multiaffine` — **degree ≤ 1 in every individual variable**, by
  exhibiting each polynomial as a sum of *squarefree* monomials and reading `degreeOf`
  off the support.  `degreeOf_mul_le` is too lossy here: it bounds a four-factor product
  by 4, when the point is that the four factors are *distinct* variables.
* `Fp_totalDegree ≤ 2`, `Gp_totalDegree ≤ 4` — the degrees stay bounded as `m` grows.
* `sq_sum_eq` — `(∑ zᵢ)² = ∑ zᵢ² + 2∑_{i<j} zᵢzⱼ`, proved by trichotomy on `(i,j)` and
  `Finset.sum_comm`, not by any Finset bijection.
* `key_identity` — the write-up's equation (2), `∑(zᵢ−1)² = F² + 2(m−1)F − 2G`.
* `common_zero_iff` — hence the common real zero set is **exactly** `{xᵢyᵢ = 1 ∀i}`.
  The reverse direction needs no count of `#{i<j}`: `F = 0` is immediate, and then (2)
  with vanishing left side forces `G = 0`.
* `pt_mem` + `sep` + `pt_injective` — the `2^m` sign witnesses `pt ε` all lie in the zero
  set, are distinct, and **no preconnected subset of the zero set contains two of them**.

`sep` is the component statement in elementary form: it says the zero set has at least
`2^m` connected components, without constructing the `ConnectedComponents` quotient.  The
disconnecting pair is `{v | 0 < v (false,i)}` and `{v | v (false,i) < 0}`, which cover the
zero set because `xᵢyᵢ = 1` forces `xᵢ ≠ 0`.

`not_bounded` packages these: for every `m`, two multi-affine polynomials of total degree
at most 2 and 4 in `2m` variables whose common real zero set has at least `2^m` connected
components.  Degrees fixed, components unbounded — the degree-only bound fails.

## What is deliberately NOT here

The write-up also proves each component is *homeomorphic to `ℝ^m`* (so there are **exactly**
`2^m`), and gives a smooth strengthening `G + ρ/2 = 0` whose components are diffeomorphic to
`ℝ^m × S^{m−2}`.  Neither is needed: refuting a *boundedness* claim needs a lower bound on
the count, not the exact count, and the elementary separation above supplies it.  Both are
checked numerically/symbolically in `Campaigns/MathDB-Formalization/verify_405042.py`.

Values checked in `Campaigns/MathDB-Formalization/verify_405042.py`.
-/

namespace Principia.MathDB.P405042

open MvPolynomial

/-- The `2m` variables: `(false,i)` is `xᵢ`, `(true,i)` is `yᵢ`. -/
abbrev Var (m : ℕ) := Bool × Fin m

/-- Exponent vector of the squarefree monomial `xᵢyᵢ`. -/
noncomputable def e2 (m : ℕ) (i : Fin m) : Var m →₀ ℕ :=
  Finsupp.single (false, i) 1 + Finsupp.single (true, i) 1

/-- Exponent vector of the squarefree monomial `xᵢyᵢxⱼyⱼ`. -/
noncomputable def e4 (m : ℕ) (i j : Fin m) : Var m →₀ ℕ := e2 m i + e2 m j

/-- `zᵢ = xᵢyᵢ`, as a polynomial. -/
noncomputable def zp (m : ℕ) (i : Fin m) : MvPolynomial (Var m) ℝ :=
  X (false, i) * X (true, i)

theorem zp_eq_monomial (m : ℕ) (i : Fin m) :
    zp m i = monomial (e2 m i) (1 : ℝ) := by
  rw [e2, monomial_single_add, ← X_pow_eq_monomial, zp, pow_one, pow_one]

/-- `F = ∑ᵢ zᵢ − m`. -/
noncomputable def Fp (m : ℕ) : MvPolynomial (Var m) ℝ :=
  (∑ i : Fin m, zp m i) - C (m : ℝ)

/-- `G = ∑_{i<j} zᵢzⱼ − m(m−1)/2`. -/
noncomputable def Gp (m : ℕ) : MvPolynomial (Var m) ℝ :=
  (∑ i : Fin m, ∑ j : Fin m, if i < j then zp m i * zp m j else 0)
    - C ((m : ℝ) * ((m : ℝ) - 1) / 2)

/-! ### Multi-affinity: degree at most one in every individual variable -/

theorem e2_apply (m : ℕ) (i : Fin m) (v : Var m) : e2 m i v ≤ 1 := by
  rw [e2]
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  rcases eq_or_ne ((false, i) : Var m) v with h1 | h1
  · rw [if_pos h1, if_neg ?_]
    · omega
    · intro h2
      rw [← h1] at h2
      exact absurd (congrArg Prod.fst h2) (by simp)
  · rw [if_neg h1]
    split_ifs <;> omega

/-- `e2 m i` is supported on the two variables `xᵢ, yᵢ`, so it vanishes elsewhere. -/
theorem e2_eq_zero {m : ℕ} {i : Fin m} {v : Var m} (h : v.2 ≠ i) : e2 m i v = 0 := by
  rw [e2]
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  rw [if_neg (fun hx => h (by rw [← hx])), if_neg (fun hx => h (by rw [← hx]))]
  omega

theorem e4_apply {m : ℕ} {i j : Fin m} (hij : i ≠ j) (v : Var m) : e4 m i j v ≤ 1 := by
  rw [e4, Finsupp.add_apply]
  by_cases h : v.2 = i
  · rw [e2_eq_zero (i := j) (by rw [h]; exact hij), add_zero]
    exact e2_apply m i v
  · rw [e2_eq_zero h, zero_add]
    exact e2_apply m j v

theorem Fp_multiaffine (m : ℕ) (v : Var m) : degreeOf v (Fp m) ≤ 1 := by
  rw [Fp, sub_eq_add_neg]
  refine le_trans (degreeOf_add_le _ _ _) ?_
  refine max_le ?_ ?_
  · refine le_trans (degreeOf_sum_le _ _ _) ?_
    refine Finset.sup_le (fun i _ => ?_)
    rw [zp_eq_monomial, degreeOf_le_iff]
    intro s hs
    rw [support_monomial, if_neg one_ne_zero] at hs
    simp only [Finset.mem_singleton] at hs
    subst hs
    exact e2_apply m i v
  · rw [← C_neg, degreeOf_C]
    omega

theorem Gp_multiaffine (m : ℕ) (v : Var m) : degreeOf v (Gp m) ≤ 1 := by
  rw [Gp, sub_eq_add_neg]
  refine le_trans (degreeOf_add_le _ _ _) (max_le ?_ ?_)
  · refine le_trans (degreeOf_sum_le _ _ _) (Finset.sup_le (fun i _ => ?_))
    refine le_trans (degreeOf_sum_le _ _ _) (Finset.sup_le (fun j _ => ?_))
    by_cases hij : i < j
    · rw [if_pos hij]
      have hne : i ≠ j := ne_of_lt hij
      have : zp m i * zp m j = monomial (e4 m i j) (1 : ℝ) := by
        rw [zp_eq_monomial, zp_eq_monomial, monomial_mul, e4, one_mul]
      rw [this, degreeOf_le_iff]
      intro s hs
      rw [support_monomial, if_neg one_ne_zero] at hs
      simp only [Finset.mem_singleton] at hs
      subst hs
      exact e4_apply hne v
    · rw [if_neg hij, degreeOf_zero]
      omega
  · rw [← C_neg, degreeOf_C]
    omega

/-! ### The total degrees stay bounded as `m` grows -/

theorem zp_totalDegree (m : ℕ) (i : Fin m) : (zp m i).totalDegree ≤ 2 := by
  refine le_trans (totalDegree_mul _ _) ?_
  have h1 : (X (false, i) : MvPolynomial (Var m) ℝ).totalDegree ≤ 1 := by
    rw [totalDegree_X]
  have h2 : (X (true, i) : MvPolynomial (Var m) ℝ).totalDegree ≤ 1 := by
    rw [totalDegree_X]
  omega

theorem Fp_totalDegree (m : ℕ) : (Fp m).totalDegree ≤ 2 := by
  rw [Fp, sub_eq_add_neg]
  refine le_trans (totalDegree_add _ _) (max_le ?_ ?_)
  · refine le_trans (totalDegree_finsetSum _ _) (Finset.sup_le (fun i _ => zp_totalDegree m i))
  · rw [← C_neg, totalDegree_C]
    omega

theorem Gp_totalDegree (m : ℕ) : (Gp m).totalDegree ≤ 4 := by
  rw [Gp, sub_eq_add_neg]
  refine le_trans (totalDegree_add _ _) (max_le ?_ ?_)
  · refine le_trans (totalDegree_finsetSum _ _) (Finset.sup_le (fun i _ => ?_))
    refine le_trans (totalDegree_finsetSum _ _) (Finset.sup_le (fun j _ => ?_))
    by_cases hij : i < j
    · rw [if_pos hij]
      refine le_trans (totalDegree_mul _ _) ?_
      have := zp_totalDegree m i
      have := zp_totalDegree m j
      omega
    · rw [if_neg hij, totalDegree_zero]
      omega
  · rw [← C_neg, totalDegree_C]
    omega

/-! ### The algebraic identity -/

/-- `zᵢ` as a real function of a point. -/
def zv {m : ℕ} (v : Var m → ℝ) (i : Fin m) : ℝ := v (false, i) * v (true, i)

/-- The off-diagonal sum `∑_{i<j} zᵢzⱼ`, written with an `if` rather than a filtered
`Finset`, so that trichotomy closes the identity below pointwise. -/
def offSum {m : ℕ} (z : Fin m → ℝ) : ℝ := ∑ i, ∑ j, if i < j then z i * z j else 0

theorem sq_sum_eq {m : ℕ} (z : Fin m → ℝ) :
    (∑ i, z i) ^ 2 = (∑ i, (z i) ^ 2) + 2 * offSum z := by
  have hsq : (∑ i, z i) ^ 2 = ∑ i, ∑ j, z i * z j := by
    rw [sq, Finset.sum_mul_sum]
  have hlt : ∀ i j : Fin m, z i * z j
      = (if i < j then z i * z j else 0) + (if j < i then z i * z j else 0)
        + (if i = j then z i * z j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · rw [if_pos h, if_neg (asymm h), if_neg (ne_of_lt h)]; ring
    · rw [if_neg (by omega : ¬ i < j), if_neg (by omega : ¬ j < i), if_pos h]; ring
    · rw [if_neg (asymm h), if_pos h, if_neg (by omega : ¬ i = j)]; ring
  have hswap : (∑ i : Fin m, ∑ j : Fin m, if j < i then z i * z j else 0) = offSum z := by
    rw [Finset.sum_comm, offSum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
      by_cases h : i < j
      · rw [if_pos h, if_pos h, mul_comm]
      · rw [if_neg h, if_neg h]))
  have hdiag : (∑ i : Fin m, ∑ j : Fin m, if i = j then z i * z j else 0)
      = ∑ i, (z i) ^ 2 := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_ite_eq Finset.univ i (fun j => z i * z j), if_pos (Finset.mem_univ i), sq]
  have hsplit : (∑ i : Fin m, ∑ j : Fin m, z i * z j)
      = ((∑ i : Fin m, ∑ j : Fin m, if i < j then z i * z j else 0)
          + (∑ i : Fin m, ∑ j : Fin m, if j < i then z i * z j else 0))
        + (∑ i : Fin m, ∑ j : Fin m, if i = j then z i * z j else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => hlt i j)
  rw [hsq, hsplit, hswap, hdiag, ← offSum]
  ring

/-- **The write-up's identity (2).** -/
theorem key_identity {m : ℕ} (z : Fin m → ℝ) :
    (∑ i, (z i - 1) ^ 2)
      = ((∑ i, z i) - m) ^ 2 + 2 * ((m : ℝ) - 1) * ((∑ i, z i) - m)
        - 2 * (offSum z - (m : ℝ) * ((m : ℝ) - 1) / 2) := by
  have hexp : (∑ i, (z i - 1) ^ 2) = (∑ i, (z i) ^ 2) - 2 * (∑ i, z i) + m := by
    have : ∀ i : Fin m, (z i - 1) ^ 2 = (z i) ^ 2 - 2 * z i + 1 := fun i => by ring
    simp only [this]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp
  have hs := sq_sum_eq z
  rw [hexp]
  linarith [hs]

/-! ### The common zero set -/

theorem eval_Fp {m : ℕ} (v : Var m → ℝ) :
    eval v (Fp m) = (∑ i, zv v i) - m := by
  rw [Fp, map_sub, eval_C, map_sum]
  simp [zp, zv]

theorem eval_Gp {m : ℕ} (v : Var m → ℝ) :
    eval v (Gp m) = offSum (zv v) - (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  rw [Gp, map_sub, eval_C, map_sum, offSum]
  refine congrArg (· - _) (Finset.sum_congr rfl (fun i _ => ?_))
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : i < j
  · simp [h, zp, zv, mul_assoc, mul_left_comm]
  · simp [h]

/-- **The common real zero set is exactly `{xᵢyᵢ = 1 for every i}`.** -/
theorem common_zero_iff {m : ℕ} (v : Var m → ℝ) :
    (eval v (Fp m) = 0 ∧ eval v (Gp m) = 0) ↔ ∀ i, zv v i = 1 := by
  constructor
  · rintro ⟨hF, hG⟩
    rw [eval_Fp] at hF
    rw [eval_Gp] at hG
    have hid := key_identity (zv v)
    have hzero : (∑ i, (zv v i - 1) ^ 2) = 0 := by rw [hid, hF, hG]; ring
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sq_nonneg (zv v j - 1))).1 hzero i (Finset.mem_univ i)
    have h2 : zv v i - 1 = 0 := by
      by_contra hne
      have hpos : 0 < (zv v i - 1) ^ 2 := by positivity
      linarith [hpos]
    linarith
  · intro h
    have hF : eval v (Fp m) = 0 := by
      rw [eval_Fp]
      simp only [h]
      simp
    refine ⟨hF, ?_⟩
    have hid := key_identity (zv v)
    have hzero : (∑ i, (zv v i - 1) ^ 2) = 0 := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [h i]; ring
    rw [eval_Fp] at hF
    rw [eval_Gp]
    rw [hzero, hF] at hid
    norm_num at hid
    linarith [hid]

/-- The common real zero set of the two equations. -/
def V (m : ℕ) : Set (Var m → ℝ) := {v | eval v (Fp m) = 0 ∧ eval v (Gp m) = 0}

/-! ### The `2^m` separated witnesses -/

/-- The witness with sign pattern `ε`: `xᵢ = yᵢ = ±1`. -/
def pt {m : ℕ} (ε : Fin m → Bool) : Var m → ℝ := fun p => if ε p.2 then 1 else -1

theorem pt_mem {m : ℕ} (ε : Fin m → Bool) : pt ε ∈ V m := by
  rw [V, Set.mem_setOf_eq, common_zero_iff]
  intro i
  rw [zv, pt, pt]
  by_cases h : ε i <;> simp [h]

theorem pt_injective {m : ℕ} : Function.Injective (pt (m := m)) := by
  intro ε ε' h
  funext i
  have := congrFun h (false, i)
  rw [pt, pt] at this
  by_cases h1 : ε i <;> by_cases h2 : ε' i <;> simp [h1, h2] at this ⊢ <;> norm_num at this

/-- **No preconnected subset of the zero set contains two different sign witnesses.**
Hence the zero set has at least `2^m` connected components. -/
theorem sep {m : ℕ} (ε ε' : Fin m → Bool) (hne : ε ≠ ε')
    (S : Set (Var m → ℝ)) (hSV : S ⊆ V m) (hconn : IsPreconnected S)
    (h1 : pt ε ∈ S) (h2 : pt ε' ∈ S) : False := by
  obtain ⟨i, hi⟩ : ∃ i, ε i ≠ ε' i := Function.ne_iff.1 hne
  set U : Set (Var m → ℝ) := {v | 0 < v (false, i)} with hU
  set W : Set (Var m → ℝ) := {v | v (false, i) < 0} with hW
  have hUo : IsOpen U := isOpen_lt continuous_const (continuous_apply (false, i))
  have hWo : IsOpen W := isOpen_lt (continuous_apply (false, i)) continuous_const
  have hcover : S ⊆ U ∪ W := by
    intro v hv
    have hz : zv v i = 1 := ((common_zero_iff v).1 (hSV hv)) i
    have hx : v (false, i) ≠ 0 := by
      intro h0
      rw [zv, h0, zero_mul] at hz
      exact zero_ne_one hz
    rcases lt_or_gt_of_ne hx with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hdisj : ∀ v, ¬ (v ∈ U ∧ v ∈ W) := by
    rintro v ⟨hu, hw⟩
    rw [hU, Set.mem_setOf_eq] at hu
    rw [hW, Set.mem_setOf_eq] at hw
    linarith
  -- the two witnesses sit in different halves
  have hpt : ∀ (δ : Fin m → Bool), (δ i = true → pt δ ∈ U) ∧ (δ i = false → pt δ ∈ W) := by
    intro δ
    constructor
    · intro hd; rw [hU, Set.mem_setOf_eq, pt]; simp [hd]
    · intro hd; rw [hW, Set.mem_setOf_eq, pt]; simp [hd]
  have hcases : ((pt ε ∈ U) ∧ (pt ε' ∈ W)) ∨ ((pt ε' ∈ U) ∧ (pt ε ∈ W)) := by
    cases hb : ε i with
    | true =>
      have : ε' i = false := by
        cases hb' : ε' i with
        | true => exact absurd (hb.trans hb'.symm) hi
        | false => rfl
      exact Or.inl ⟨(hpt ε).1 hb, (hpt ε').2 this⟩
    | false =>
      have : ε' i = true := by
        cases hb' : ε' i with
        | true => rfl
        | false => exact absurd (hb.trans hb'.symm) hi
      exact Or.inr ⟨(hpt ε').1 this, (hpt ε).2 hb⟩
  rcases hcases with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨w, _, hw⟩ := hconn U W hUo hWo hcover ⟨pt ε, h1, ha⟩ ⟨pt ε', h2, hb⟩
    exact hdisj w hw
  · obtain ⟨w, _, hw⟩ := hconn U W hUo hWo hcover ⟨pt ε', h2, ha⟩ ⟨pt ε, h1, hb⟩
    exact hdisj w hw

/-- **The degree-only component bound is FALSE.**  For every `m`, the two multi-affine
polynomials `Fp m` and `Gp m` in `2m` variables have total degrees at most `2` and `4`,
and their common real zero set contains `2^m` pairwise-separated points: distinct sign
witnesses never lie in a common preconnected subset.  So the number of real connected
components is at least `2^m`, unbounded in the number of variables while the degrees
stay fixed. -/
theorem not_bounded (m : ℕ) :
    (∀ v : Var m, degreeOf v (Fp m) ≤ 1) ∧
    (∀ v : Var m, degreeOf v (Gp m) ≤ 1) ∧
    (Fp m).totalDegree ≤ 2 ∧ (Gp m).totalDegree ≤ 4 ∧
    Function.Injective (pt (m := m)) ∧
    (∀ ε : Fin m → Bool, pt ε ∈ V m) ∧
    (∀ ε ε' : Fin m → Bool, ε ≠ ε' → ∀ S : Set (Var m → ℝ), S ⊆ V m →
      IsPreconnected S → ¬ (pt ε ∈ S ∧ pt ε' ∈ S)) :=
  ⟨Fp_multiaffine m, Gp_multiaffine m, Fp_totalDegree m, Gp_totalDegree m,
   pt_injective, pt_mem, fun ε ε' h S hS hc hmem => sep ε ε' h S hS hc hmem.1 hmem.2⟩

end Principia.MathDB.P405042
