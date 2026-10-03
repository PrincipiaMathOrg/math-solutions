/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# A certified lower bound for an expectation over independent prime-power factors

For a list `L` of triples `(p, e, lo)` this module defines the finite sum
```
Ex L Φ = ∑_{a₁ ∈ [lo₁, e₁]} wt₁(a₁) ∑_{a₂} wt₂(a₂) ⋯ Φ(rat p₁ a₁ · rat p₂ a₂ ⋯),
```
with `wt p e a = (p − 1)/p^{a+1}` for `a < e`, `1/p^e` for `a = e`, and
`rat p a = (p^{a+1} − 1)/((p − 1) p^a)` (`= σ(p^a)/p^a` for a prime `p`). With `Φ = cz`,
`cz t = max(0, 1 − 1/(t − 1))`, and the list of the prime powers of a modulus `Q`, it is the
Chen–Zhao constant of `Q` (`Aliquot/Euler.lean` proves the identification).

The sum has as many terms as `Q` has divisors (millions for the moduli that matter), so it is
not evaluated. Instead `dp` runs a *rounded* dynamic programme in natural numbers: a state is a
list of pairs `(h, w)` standing for "weight `w/WS` sits at abundancy `≥ h/HS`"; each prime
multiplies the abundancies (rounded **down**, then merged into a coarse grid by `rnd`) and the
weights (rounded **down**). `dp_le` proves, for every `rnd` with `rnd h ≤ h`, that
```
dp rnd HS WS L ≤ WS · Ex L cz.
```
Soundness never uses sortedness or the size of the fuel: merging preserves the weighted sum
`val` in every branch, and every rounding only decreases it, because `cz` is monotone and
nonnegative. The numerical value of `dp` for a concrete list is then one `decide +kernel`.
-/

namespace Principia.Common.Aliquot

open Finset

/-! ## 1. The exact objects -/

/-- Numerator of the weight `wt p e a`. -/
def wNum (p e a : ℕ) : ℕ := if a < e then p - 1 else 1

/-- Denominator of the weight `wt p e a`. -/
def wDen (p e a : ℕ) : ℕ := if a < e then p ^ (a + 1) else p ^ e

/-- `(p^{a+1} − 1)/(p − 1)`, which is `σ(p^a)` for a prime `p`. -/
def sigPP (p a : ℕ) : ℕ := (p ^ (a + 1) - 1) / (p - 1)

/-- `wt p e a = wNum/wDen`: the density of `{n : min(v_p(n), e) = a}`. -/
noncomputable def wt (p e a : ℕ) : ℝ := (wNum p e a : ℝ) / (wDen p e a : ℝ)

/-- `rat p a = sigPP p a / p^a`, which is `σ(p^a)/p^a` for a prime `p`. -/
noncomputable def rat (p a : ℕ) : ℝ := (sigPP p a : ℝ) / ((p ^ a : ℕ) : ℝ)

/-- The Chen–Zhao integrand `cz t = (t − 2)/(t − 1)` for `t > 2`, else `0`. -/
noncomputable def cz (t : ℝ) : ℝ := if 2 < t then (t - 2) / (t - 1) else 0

/-- `Ex L Φ`: the expectation of `Φ(∏ rat)` over independent exponents with weights `wt`. -/
noncomputable def Ex : List (ℕ × ℕ × ℕ) → (ℝ → ℝ) → ℝ
  | [], Φ => Φ 1
  | q :: L, Φ =>
      ∑ a ∈ Finset.Icc q.2.2 q.2.1, wt q.1 q.2.1 a * Ex L (fun t => Φ (rat q.1 a * t))

theorem wt_nonneg (p e a : ℕ) : 0 ≤ wt p e a := by
  unfold wt
  positivity

theorem rat_nonneg (p a : ℕ) : 0 ≤ rat p a := by
  unfold rat
  positivity

theorem cz_nonneg (t : ℝ) : 0 ≤ cz t := by
  unfold cz
  split_ifs with h
  · apply div_nonneg <;> linarith
  · exact le_rfl

theorem cz_mono {s t : ℝ} (hst : s ≤ t) : cz s ≤ cz t := by
  unfold cz
  split_ifs with hs ht ht
  · have hs1 : 0 < s - 1 := by linarith
    have ht1 : 0 < t - 1 := by linarith
    rw [div_le_div_iff₀ hs1 ht1]
    nlinarith
  · linarith
  · apply div_nonneg <;> linarith
  · exact le_rfl

theorem Ex_mono : ∀ (L : List (ℕ × ℕ × ℕ)) (Φ₁ Φ₂ : ℝ → ℝ), (∀ t, Φ₁ t ≤ Φ₂ t) →
    Ex L Φ₁ ≤ Ex L Φ₂
  | [], Φ₁, Φ₂, h => h 1
  | q :: L, Φ₁, Φ₂, h => by
      simp only [Ex]
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (Ex_mono L _ _ (fun t => h _)) (wt_nonneg _ _ _)

theorem Ex_nonneg : ∀ (L : List (ℕ × ℕ × ℕ)) (Φ : ℝ → ℝ), (∀ t, 0 ≤ Φ t) → 0 ≤ Ex L Φ
  | [], Φ, h => h 1
  | q :: L, Φ, h => by
      simp only [Ex]
      apply Finset.sum_nonneg
      intro a _
      exact mul_nonneg (wt_nonneg _ _ _) (Ex_nonneg L _ (fun t => h _))

/-- `psi L t = Ex L (u ↦ cz(t u))`: the value of a state at abundancy `t`. -/
noncomputable def psi (L : List (ℕ × ℕ × ℕ)) (t : ℝ) : ℝ := Ex L (fun u => cz (t * u))

theorem psi_nonneg (L : List (ℕ × ℕ × ℕ)) (t : ℝ) : 0 ≤ psi L t :=
  Ex_nonneg L _ (fun _ => cz_nonneg _)

theorem psi_mono (L : List (ℕ × ℕ × ℕ)) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    psi L s ≤ psi L t := by
  apply Ex_mono
  intro u
  rcases le_or_gt 0 u with hu | hu
  · exact cz_mono (mul_le_mul_of_nonneg_right hst hu)
  · have h1 : s * u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs hu.le
    have h2 : cz (s * u) = 0 := by
      unfold cz
      rw [if_neg (by linarith)]
    rw [h2]
    exact cz_nonneg _

theorem psi_nil (t : ℝ) : psi [] t = cz t := by
  simp [psi, Ex]

theorem psi_cons (q : ℕ × ℕ × ℕ) (L : List (ℕ × ℕ × ℕ)) (t : ℝ) :
    psi (q :: L) t = ∑ a ∈ Finset.Icc q.2.2 q.2.1, wt q.1 q.2.1 a * psi L (t * rat q.1 a) := by
  simp only [psi, Ex]
  apply Finset.sum_congr rfl
  intro a _
  congr 2
  funext u
  rw [mul_assoc]

theorem psi_one (L : List (ℕ × ℕ × ℕ)) : psi L 1 = Ex L cz := by
  simp [psi]

/-! ## 2. The rounded dynamic programme (computable, natural numbers only) -/

/-- Rounding to a banded relative grid: step `s` below `2·HS`, `2s` below `4·HS`, `4s` below
`8·HS`, and `8s` beyond. Only `band_le` is used by the soundness proof. -/
def band (HS s h : ℕ) : ℕ :=
  if h < 2 * HS then h / s * s
  else if h < 4 * HS then h / (2 * s) * (2 * s)
  else if h < 8 * HS then h / (4 * s) * (4 * s)
  else h / (8 * s) * (8 * s)

theorem band_le (HS s h : ℕ) : band HS s h ≤ h := by
  unfold band
  split_ifs <;> exact Nat.div_mul_le_self _ _

/-- Merge two lists sorted by key, adding the weights of equal keys (fuel-bounded). -/
def mergeF : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ)
  | 0, l1, l2 => l1 ++ l2
  | _ + 1, [], l2 => l2
  | _ + 1, x :: t, [] => x :: t
  | n + 1, x :: t1, y :: t2 =>
      if x.1 < y.1 then x :: mergeF n t1 (y :: t2)
      else if y.1 < x.1 then y :: mergeF n (x :: t1) t2
      else (x.1, x.2 + y.2) :: mergeF n t1 t2

/-- Merge adjacent equal keys, carrying the pending pair `x`. -/
def coalesceAux : ℕ × ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
  | x, [] => [x]
  | x, y :: t => if x.1 = y.1 then coalesceAux (x.1, x.2 + y.2) t else x :: coalesceAux y t

/-- Merge adjacent equal keys. -/
def coalesce : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | x :: t => coalesceAux x t

/-- Multiply every state by the exponent-`a` factor of the prime `p` (both roundings down). -/
def mapA (rnd : ℕ → ℕ) (p e a : ℕ) (l : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  l.map (fun x => (rnd (x.1 * sigPP p a / p ^ a), x.2 * wNum p e a / wDen p e a))

/-- The fuel of `mergeF`; any value is sound, a large one makes the merge exact. -/
def mergeFuel : ℕ := 100000000

/-- One prime of the programme: all exponents `a ∈ [lo, e]`, merged. -/
def stepPE (rnd : ℕ → ℕ) (p e lo : ℕ) (l : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (List.range' lo (e + 1 - lo)).foldr
    (fun a acc => mergeF mergeFuel (coalesce (mapA rnd p e a l)) acc) []

/-- Accumulate `⌊w (h − 2HS)/(h − HS)⌋` over the states with `h > 2HS`. -/
def finalStep (HS acc : ℕ) (x : ℕ × ℕ) : ℕ :=
  if 2 * HS < x.1 then acc + x.2 * (x.1 - 2 * HS) / (x.1 - HS) else acc

/-- The final lower bound of `WS · cz`, summed over the states. -/
def finalSum (HS : ℕ) (l : List (ℕ × ℕ)) : ℕ := l.foldl (finalStep HS) 0

/-- **The programme.** Start with weight `WS` at abundancy `HS` (i.e. `1`), run every prime. -/
def dp (rnd : ℕ → ℕ) (HS WS : ℕ) (L : List (ℕ × ℕ × ℕ)) : ℕ :=
  finalSum HS (L.foldl (fun st q => stepPE rnd q.1 q.2.1 q.2.2 st) [(HS, WS)])

/-! ## 3. Soundness -/

/-- `val φ l = ∑_{(h, w) ∈ l} w · φ(h)`. -/
noncomputable def val (φ : ℕ → ℝ) (l : List (ℕ × ℕ)) : ℝ :=
  (l.map (fun x => (x.2 : ℝ) * φ x.1)).sum

theorem val_nil (φ : ℕ → ℝ) : val φ [] = 0 := by
  simp [val]

theorem val_cons (φ : ℕ → ℝ) (x : ℕ × ℕ) (l : List (ℕ × ℕ)) :
    val φ (x :: l) = (x.2 : ℝ) * φ x.1 + val φ l := by
  simp [val]

theorem val_append (φ : ℕ → ℝ) (l1 l2 : List (ℕ × ℕ)) :
    val φ (l1 ++ l2) = val φ l1 + val φ l2 := by
  simp [val]

theorem val_mergeF (φ : ℕ → ℝ) (n : ℕ) :
    ∀ l1 l2 : List (ℕ × ℕ), val φ (mergeF n l1 l2) = val φ l1 + val φ l2 := by
  induction n with
  | zero => intro l1 l2; simp only [mergeF, val_append]
  | succ n ih =>
    intro l1 l2
    rcases l1 with _ | ⟨x, t1⟩
    · simp [mergeF, val_nil]
    rcases l2 with _ | ⟨y, t2⟩
    · simp [mergeF, val_nil]
    simp only [mergeF]
    split_ifs with h1 h2
    · simp only [val_cons, ih]
      ring
    · simp only [val_cons, ih]
      ring
    · have hxy : x.1 = y.1 := by omega
      rw [val_cons, ih, val_cons, val_cons, hxy]
      push_cast
      ring

theorem val_coalesceAux (φ : ℕ → ℝ) :
    ∀ (t : List (ℕ × ℕ)) (x : ℕ × ℕ), val φ (coalesceAux x t) = (x.2 : ℝ) * φ x.1 + val φ t
  | [], x => by simp [coalesceAux, val_cons, val_nil]
  | y :: t, x => by
      simp only [coalesceAux]
      split_ifs with h
      · rw [val_coalesceAux φ t, val_cons, h]
        push_cast
        ring
      · rw [val_cons, val_coalesceAux φ t, val_cons]

theorem val_coalesce (φ : ℕ → ℝ) (l : List (ℕ × ℕ)) : val φ (coalesce l) = val φ l := by
  rcases l with _ | ⟨x, t⟩
  · simp [coalesce]
  · simp only [coalesce]
    rw [val_coalesceAux, val_cons]

theorem val_add (φ ψ : ℕ → ℝ) (l : List (ℕ × ℕ)) :
    val (fun h => φ h + ψ h) l = val φ l + val ψ l := by
  induction l with
  | nil => simp [val_nil]
  | cons x t ih =>
    rw [val_cons, val_cons, val_cons, ih]
    ring

theorem val_zero (l : List (ℕ × ℕ)) : val (fun _ => 0) l = 0 := by
  induction l with
  | nil => simp [val_nil]
  | cons x t ih => rw [val_cons, ih]; ring

theorem val_le_val {φ ψ : ℕ → ℝ} (h : ∀ n, φ n ≤ ψ n) (l : List (ℕ × ℕ)) :
    val φ l ≤ val ψ l := by
  induction l with
  | nil => simp [val_nil]
  | cons x t ih =>
    rw [val_cons, val_cons]
    have := mul_le_mul_of_nonneg_left (h x.1) (Nat.cast_nonneg (α := ℝ) x.2)
    linarith

/-- `∑_{a ∈ as} val (φ a) l = val (∑_{a ∈ as} φ a) l`. -/
theorem sum_val (φ : ℕ → ℕ → ℝ) (l : List (ℕ × ℕ)) :
    ∀ as : List ℕ, ((as.map (fun a => val (φ a) l)).sum) =
      val (fun h => (as.map (fun a => φ a h)).sum) l
  | [] => by simp [val_zero]
  | a :: as => by
      rw [List.map_cons, List.sum_cons, sum_val φ l as]
      simp only [List.map_cons, List.sum_cons]
      rw [val_add]

theorem val_stepPE_eq (rnd : ℕ → ℕ) (p e : ℕ) (φ : ℕ → ℝ) (l : List (ℕ × ℕ)) :
    ∀ as : List ℕ,
      val φ (as.foldr (fun a acc => mergeF mergeFuel (coalesce (mapA rnd p e a l)) acc) []) =
        (as.map (fun a => val φ (mapA rnd p e a l))).sum
  | [] => by simp [val_nil]
  | a :: as => by
      rw [List.foldr_cons, val_mergeF, val_coalesce, val_stepPE_eq rnd p e φ l as,
        List.map_cons, List.sum_cons]

/-- One exponent: the rounded states are worth at most the exact ones. -/
theorem val_mapA_le (rnd : ℕ → ℕ) (hrnd : ∀ h, rnd h ≤ h) (HS : ℕ) (L : List (ℕ × ℕ × ℕ))
    (p e a : ℕ) (l : List (ℕ × ℕ)) :
    val (fun h => psi L ((h : ℝ) / HS)) (mapA rnd p e a l) ≤
      val (fun h => wt p e a * psi L ((h : ℝ) / HS * rat p a)) l := by
  induction l with
  | nil => simp [mapA, val_nil]
  | cons x t ih =>
    have ih' : val (fun h => psi L ((h : ℝ) / HS)) (mapA rnd p e a t) ≤
        val (fun h => wt p e a * psi L ((h : ℝ) / HS * rat p a)) t := ih
    simp only [mapA, List.map_cons] at ih' ⊢
    rw [val_cons, val_cons]
    have hw : ((x.2 * wNum p e a / wDen p e a : ℕ) : ℝ) ≤ (x.2 : ℝ) * wt p e a := by
      calc ((x.2 * wNum p e a / wDen p e a : ℕ) : ℝ)
          ≤ ((x.2 * wNum p e a : ℕ) : ℝ) / (wDen p e a : ℝ) := Nat.cast_div_le
        _ = (x.2 : ℝ) * wt p e a := by
          unfold wt
          push_cast
          ring
    have hh : ((rnd (x.1 * sigPP p a / p ^ a) : ℕ) : ℝ) / HS ≤ (x.1 : ℝ) / HS * rat p a := by
      have h1 : ((rnd (x.1 * sigPP p a / p ^ a) : ℕ) : ℝ) ≤
          ((x.1 * sigPP p a : ℕ) : ℝ) / ((p ^ a : ℕ) : ℝ) :=
        (Nat.cast_le.2 (hrnd _)).trans Nat.cast_div_le
      have h2 : ((x.1 * sigPP p a : ℕ) : ℝ) / ((p ^ a : ℕ) : ℝ) / HS =
          (x.1 : ℝ) / HS * rat p a := by
        unfold rat
        push_cast
        simp only [div_eq_mul_inv]
        ring
      rw [← h2]
      exact div_le_div_of_nonneg_right h1 (Nat.cast_nonneg _)
    have hpsi : psi L (((rnd (x.1 * sigPP p a / p ^ a) : ℕ) : ℝ) / HS) ≤
        psi L ((x.1 : ℝ) / HS * rat p a) :=
      psi_mono L (by positivity) hh
    have hprod : ((x.2 * wNum p e a / wDen p e a : ℕ) : ℝ) *
        psi L (((rnd (x.1 * sigPP p a / p ^ a) : ℕ) : ℝ) / HS) ≤
        (x.2 : ℝ) * (wt p e a * psi L ((x.1 : ℝ) / HS * rat p a)) := by
      rw [← mul_assoc]
      exact mul_le_mul hw hpsi (psi_nonneg _ _)
        (mul_nonneg (Nat.cast_nonneg _) (wt_nonneg _ _ _))
    linarith

/-- `∑_{a ∈ Icc lo e} f a` as a list sum over `List.range' lo (e + 1 − lo)`. -/
theorem sum_Icc_eq_list (lo e : ℕ) (f : ℕ → ℝ) :
    ∑ a ∈ Finset.Icc lo e, f a = ((List.range' lo (e + 1 - lo)).map f).sum := by
  rw [Nat.Icc_eq_range']
  rfl

/-- **One prime of the programme is sound.** -/
theorem val_stepPE_le (rnd : ℕ → ℕ) (hrnd : ∀ h, rnd h ≤ h) (HS : ℕ) (L : List (ℕ × ℕ × ℕ))
    (q : ℕ × ℕ × ℕ) (l : List (ℕ × ℕ)) :
    val (fun h => psi L ((h : ℝ) / HS)) (stepPE rnd q.1 q.2.1 q.2.2 l) ≤
      val (fun h => psi (q :: L) ((h : ℝ) / HS)) l := by
  unfold stepPE
  rw [val_stepPE_eq]
  calc ((List.range' q.2.2 (q.2.1 + 1 - q.2.2)).map
          (fun a => val (fun h => psi L ((h : ℝ) / HS)) (mapA rnd q.1 q.2.1 a l))).sum
      ≤ ((List.range' q.2.2 (q.2.1 + 1 - q.2.2)).map
          (fun a => val (fun h => wt q.1 q.2.1 a * psi L ((h : ℝ) / HS * rat q.1 a)) l)).sum := by
        apply List.sum_le_sum
        intro a _
        exact val_mapA_le rnd hrnd HS L q.1 q.2.1 a l
    _ = val (fun h => ((List.range' q.2.2 (q.2.1 + 1 - q.2.2)).map
          (fun a => wt q.1 q.2.1 a * psi L ((h : ℝ) / HS * rat q.1 a))).sum) l :=
        sum_val (fun a h => wt q.1 q.2.1 a * psi L ((h : ℝ) / HS * rat q.1 a)) l _
    _ = val (fun h => psi (q :: L) ((h : ℝ) / HS)) l := by
        congr 1
        funext h
        rw [psi_cons, sum_Icc_eq_list]

theorem finalStep_foldl_le (HS : ℕ) (hHS : 0 < HS) :
    ∀ (l : List (ℕ × ℕ)) (acc : ℕ),
      ((l.foldl (finalStep HS) acc : ℕ) : ℝ) ≤ acc + val (fun h => cz ((h : ℝ) / HS)) l
  | [], acc => by simp [val_nil]
  | x :: t, acc => by
      rw [List.foldl_cons, val_cons]
      have ih := finalStep_foldl_le HS hHS t (finalStep HS acc x)
      have hstep : ((finalStep HS acc x : ℕ) : ℝ) ≤ acc + (x.2 : ℝ) * cz ((x.1 : ℝ) / HS) := by
        unfold finalStep
        split_ifs with h
        · have hHSr : (0 : ℝ) < HS := by exact_mod_cast hHS
          have hx1 : (2 * HS : ℝ) < x.1 := by exact_mod_cast h
          have hcz : cz ((x.1 : ℝ) / HS) = ((x.1 : ℝ) - 2 * HS) / ((x.1 : ℝ) - HS) := by
            unfold cz
            have h2 : (2 : ℝ) < (x.1 : ℝ) / HS := by
              rw [lt_div_iff₀ hHSr]
              linarith
            rw [if_pos h2]
            have hd : (x.1 : ℝ) - HS ≠ 0 := by linarith
            field_simp
          have hsub1 : ((x.1 - 2 * HS : ℕ) : ℝ) = (x.1 : ℝ) - 2 * HS := by
            rw [Nat.cast_sub h.le]
            push_cast
            ring
          have hsub2 : ((x.1 - HS : ℕ) : ℝ) = (x.1 : ℝ) - HS := by
            rw [Nat.cast_sub (by omega)]
          push_cast
          have hdiv : ((x.2 * (x.1 - 2 * HS) / (x.1 - HS) : ℕ) : ℝ) ≤
              (x.2 : ℝ) * cz ((x.1 : ℝ) / HS) := by
            calc ((x.2 * (x.1 - 2 * HS) / (x.1 - HS) : ℕ) : ℝ)
                ≤ ((x.2 * (x.1 - 2 * HS) : ℕ) : ℝ) / ((x.1 - HS : ℕ) : ℝ) := Nat.cast_div_le
              _ = (x.2 : ℝ) * cz ((x.1 : ℝ) / HS) := by
                rw [hcz]
                push_cast
                rw [hsub1, hsub2]
                ring
          linarith
        · have : 0 ≤ (x.2 : ℝ) * cz ((x.1 : ℝ) / HS) :=
            mul_nonneg (Nat.cast_nonneg _) (cz_nonneg _)
          linarith
      linarith

theorem finalSum_le (HS : ℕ) (hHS : 0 < HS) (l : List (ℕ × ℕ)) :
    (finalSum HS l : ℝ) ≤ val (fun h => cz ((h : ℝ) / HS)) l := by
  have := finalStep_foldl_le HS hHS l 0
  simpa [finalSum] using this

theorem foldl_step_le (rnd : ℕ → ℕ) (hrnd : ∀ h, rnd h ≤ h) (HS : ℕ) (hHS : 0 < HS) :
    ∀ (L : List (ℕ × ℕ × ℕ)) (st : List (ℕ × ℕ)),
      (finalSum HS (L.foldl (fun st q => stepPE rnd q.1 q.2.1 q.2.2 st) st) : ℝ) ≤
        val (fun h => psi L ((h : ℝ) / HS)) st
  | [], st => by
      simp only [List.foldl_nil]
      have := finalSum_le HS hHS st
      simpa [psi_nil] using this
  | q :: L, st => by
      rw [List.foldl_cons]
      exact (foldl_step_le rnd hrnd HS hHS L _).trans (val_stepPE_le rnd hrnd HS L q st)

/-- **Soundness of the programme**: `dp rnd HS WS L ≤ WS · Ex L cz`. -/
theorem dp_le (rnd : ℕ → ℕ) (hrnd : ∀ h, rnd h ≤ h) (HS WS : ℕ) (hHS : 0 < HS)
    (L : List (ℕ × ℕ × ℕ)) : (dp rnd HS WS L : ℝ) ≤ WS * Ex L cz := by
  have h := foldl_step_le rnd hrnd HS hHS L [(HS, WS)]
  have hHSr : (HS : ℝ) ≠ 0 := by exact_mod_cast hHS.ne'
  rw [val_cons, val_nil, div_self hHSr, psi_one, add_zero] at h
  exact h

end Principia.Common.Aliquot
