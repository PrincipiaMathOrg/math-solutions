/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.DrujalSpine
import Principia.Common.GaussInduced

set_option autoImplicit false

/-!
# `DS.PerArc` for EVERY weight: the spine of `ternvin.tex` 1233–1270, all links PROVED

`DS.PerArc η` is the per-arc estimate of `lem:drujal`: for `q ≤ r·gcd(q,2)`, `|δ| ≤ gcd(q,2)δ₀r/2q`,
`|∑_{(a,q)=1} |S_η(a/q+δ/x)|² − μ²(q)/φ(q)·x²|η̂(−δ)|²|
   ≤ μ²/φ·x²·ET(2|η|₁+ET) + E²x² + φ(q)·B_q·(2∑Λ|η(n/x)| + B_q)`.
This file writes Helfgott's proof as eight links, composes them (`perArc_of_links`), PROVES every
link, and so proves `perArc : ∀ η, DS.PerArc η` — generic in the weight, under nothing but the
summability of `∑ Λ(n)|η(n/x)|` that `PerArc` itself supplies. `perArc_helf` is the instance
`η = η₊`.

## The spine

```
 [P1 BeatIt]   S(a/q+δ/x) = X_a + O*(B),  X_a = ∑_χ τ(χ̄)S_χ/φ(q)·χ(a)       (eq:beatit, 838–899)
 [P1b Mass]    B := ∑_{(n,q)>1} Λ(n)|η(n/x)| ≤ B_q/2                         (857–858)
 [P2 ToPrim]   |S_χ − S_{χ*}| ≤ B                                             (1239, `χ ↦ χ*`)
 [P3 Orth]     ∑_{(a,q)=1} |∑_χ c_χχ(a)|² = φ(q)∑_χ|c_χ|²                    (1237–1242)
 [P4 Gauss]    τ(χ₀) = μ(q);  |τ(χ̄)|² ≤ q*;  ∑_χ|τ(χ̄)|² = φ(q)²             (1247–1253)
 [P5 Principal] ||S_{χ₀*}|² − x²|η̂|²| ≤ x²·ET(2|η|₁+ET)                     (1264–1267)
 [P6 Others]   χ ≠ χ₀ ⇒ q*|S_{χ*}|² ≤ E²x²          (EBound, √(conductor)-weighted, MajSp corr. 1)
 [P7 SqDiff]   ||u|²−|v|²| ≤ |u−v|(|u|+|v|)
   ⇒ (i) |∑_a|S|² − ∑_a|X_a|²| ≤ φB(2Σ+B)   (ii) ∑_a|X_a|² = ∑_χ|τ(χ̄)|²|S_χ|²/φ
     (iii) |… − ∑_χ|τ(χ̄)|²|S_{χ*}|²/φ| ≤ φ·2BΣ   (iv) |… − cQ·x²|η̂|²| ≤ cQx²ET(…) + E²x²
     ⇒ PerArc, since φB(2Σ+B) + 2φBΣ ≤ φB_q(2Σ+B_q) = kArc (Σ = ∑Λ|η(n/x)|).
```

## Two deviations from the printed argument (each makes the proof MORE careful, not weaker)

1. **The imprimitive-to-primitive error is taken where it is cheap.** Helfgott (838–858) proves
   `eq:beatit` with `S_{χ*}` directly, via `∑_χ τ(χ̄,a)χ*(n)/φ(q) = μ((q,n^∞))/φ((q,n^∞))·e(an/q)`.
   Here `X_a` uses the imprimitive `S_χ` (so `S − X_a` is exactly the non-coprime part, `P1`), and
   `χ ↦ χ*` is paid AFTER orthogonality, weighted by `∑_χ|τ(χ̄)|² = φ(q)²` (`P4`). The total is
   `φ(q)(4BΣ + B²) ≤ φ(q)B_q(2Σ + B_q)` since `2B ≤ B_q` (`P1b`): inside `kArc`, with room.
2. **`|τ(χ)|² = μ²(q/q*)q*` (1261) is an inequality**, `≤`: `τ(χ) = μ(q/q*)χ*(q/q*)τ(χ*)` also
   vanishes when `(q/q*, q*) > 1`. Only `≤ q*` is used (`GaussInduced.norm_sq_gaussSum_le`).

## Junk values

`smSum`, `twSum` are `tsum`s. Every manipulation runs under the `Summable (Λ(n)|η(n/x)|)` binder of
`PerArc`; each twisted summand is dominated by it (`summable_gT_mul`). `mainFT` is a Bochner
integral: `‖∫ f‖ ≤ ∫ ‖f‖` holds with no integrability (junk `0` on both sides), so `|η̂| ≤ |η|₁`
needs no hypothesis.
-/

namespace Principia.Common.TernaryGoldbach.PA

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach
open scoped ArithmeticFunction

/-! ## The objects -/

/-- **`g_n = Λ(n)η(n/x)e(nδ/x)`**, the summand shared by every exponential sum below. -/
noncomputable def gT (η : ℝ → ℝ) (x δ : ℝ) (n : ℕ) : ℂ :=
  ((Λ n : ℝ) : ℂ) * ((η ((n : ℝ) / x) : ℝ) : ℂ) * e ((n : ℝ) * (δ / x))

/-- **`S_{η,χ}(δ/x, x)`** for `χ` mod `q` (imprimitive in general). -/
noncomputable def tw (η : ℝ → ℝ) (x δ : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  MajSp.twSum η χ x (δ / x)

/-- **`S_{η,χ*}(δ/x, x)`**, `χ*` the primitive character inducing `χ`. -/
noncomputable def twP (η : ℝ → ℝ) (x δ : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  MajSp.twSum η χ.primitiveCharacter x (δ / x)

/-- **`X_a = ∑_χ τ(χ̄)S_{η,χ}(δ/x)/φ(q)·χ(a)`**, the character expansion of the coprime part. -/
noncomputable def xMain (η : ℝ → ℝ) (x δ : ℝ) (q : ℕ) [NeZero q] (a : ZMod q) : ℂ :=
  ∑ χ : DirichletCharacter ℂ q,
    gaussSum χ⁻¹ ZMod.stdAddChar * tw η x δ χ / (q.totient : ℂ) * χ a

open Classical in
/-- **`B = ∑_{(n,q)>1} Λ(n)|η(n/x)|`**, the non-coprime mass (half of `eq:beatit`'s error). -/
noncomputable def bNon (η : ℝ → ℝ) (x : ℝ) (q : ℕ) : ℝ :=
  ∑' n : ℕ, if IsUnit (n : ZMod q) then 0 else Λ n * |η ((n : ℝ) / x)|

/-! ## The links -/

/-- **[P1] `eq:beatit`, per residue** (838–899): `S(a/q + δ/x) = X_a + O*(B)` for `(a,q) = 1`. -/
def BeatIt : Prop :=
  ∀ (η : ℝ → ℝ) (x δ : ℝ) (q : ℕ) [NeZero q],
    Summable (fun n : ℕ => Λ n * |η ((n : ℝ) / x)|) → ∀ a : ℕ, Nat.Coprime a q →
      ‖Smooth.smSum η x ((a : ℝ) / q + δ / x) - xMain η x δ q a‖ ≤ bNon η x q

/-- **[P1b] The non-coprime mass** (857–858): `0 ≤ B` and `2B ≤ B_q`, `B_q = DS.bQ`. -/
def MassLink : Prop :=
  ∀ (η : ℝ → ℝ) (x : ℝ) (q : ℕ), q ≠ 0 →
    Summable (fun n : ℕ => Λ n * |η ((n : ℝ) / x)|) →
      0 ≤ bNon η x q ∧ 2 * bNon η x q ≤ DS.bQ η x q

/-- **[P2] Imprimitive to primitive**: `|S_χ − S_{χ*}| ≤ B` (they differ only at `(n,q) > 1`). -/
def ToPrimitive : Prop :=
  ∀ (η : ℝ → ℝ) (x δ : ℝ) (q : ℕ) [NeZero q],
    Summable (fun n : ℕ => Λ n * |η ((n : ℝ) / x)|) → ∀ χ : DirichletCharacter ℂ q,
      ‖tw η x δ χ - twP η x δ χ‖ ≤ bNon η x q

/-- **[P3] Orthogonality over the reduced residues**:
`∑_{a<q, (a,q)=1} |∑_χ c_χ χ(a)|² = φ(q)∑_χ |c_χ|²`. -/
def Orth : Prop :=
  ∀ (q : ℕ) [NeZero q] (c : DirichletCharacter ℂ q → ℂ),
    ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ‖∑ χ : DirichletCharacter ℂ q, c χ * χ (a : ZMod q)‖ ^ 2 =
      q.totient * ∑ χ : DirichletCharacter ℂ q, ‖c χ‖ ^ 2

/-- **[P4] Gauss sums** (1247–1253): `τ(χ₀) = μ(q)`, `|τ(χ̄)|² ≤ q*`, `∑_χ |τ(χ̄)|² = φ(q)²`. -/
def Gauss : Prop :=
  ∀ (q : ℕ) [NeZero q],
    gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar = (moebius q : ℂ) ∧
      (∀ χ : DirichletCharacter ℂ q, ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 ≤ χ.conductor) ∧
      ∑ χ : DirichletCharacter ℂ q, ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 = (q.totient : ℝ) ^ 2

/-- **[P5] The principal character** (`eq:glenkin`, 1264–1267): `S_{χ₀*} = x(η̂(−δ) + err_T)`, so
`||S_{χ₀*}|² − x²|η̂(−δ)|²| ≤ x²·ET(2|η|₁ + ET)`. -/
def Principal : Prop :=
  ∀ (η : ℝ → ℝ) (x δ T : ℝ) (q : ℕ) [NeZero q], x ≠ 0 → MajSp.ETBound η 600000 x T →
    |δ| ≤ 600000 →
      |‖twP η x δ (1 : DirichletCharacter ℂ q)‖ ^ 2 - x ^ 2 * ‖MajSp.mainFT η δ‖ ^ 2| ≤
        x ^ 2 * (T * (2 * MajSp.l1 η + T))

/-- **[P6] The other characters** (`eq:brahms` + `EBound`): `χ ≠ χ₀ ⇒ q*·|S_{χ*}|² ≤ E²x²`. -/
def Others : Prop :=
  ∀ (η : ℝ → ℝ) (x δ E : ℝ) (q : ℕ) [NeZero q], x ≠ 0 → MajSp.EBound η x E → 1 ≤ q →
    q ≤ 150000 * Nat.gcd q 2 → |δ| ≤ (Nat.gcd q 2 : ℝ) * 600000 / q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        (χ.conductor : ℝ) * ‖twP η x δ χ‖ ^ 2 ≤ E ^ 2 * x ^ 2

/-- **[P7] Squares**: `||u|² − |v|²| ≤ |u − v|(|u| + |v|)`. -/
def SqDiff : Prop := ∀ u v : ℂ, |‖u‖ ^ 2 - ‖v‖ ^ 2| ≤ ‖u - v‖ * (‖u‖ + ‖v‖)

/-! ## Elementary facts about the sums -/

/-- `|g_n| = Λ(n)|η(n/x)|`. -/
theorem norm_gT (η : ℝ → ℝ) (x δ : ℝ) (n : ℕ) : ‖gT η x δ n‖ = Λ n * |η ((n : ℝ) / x)| := by
  unfold gT
  rw [norm_mul, norm_mul, e_norm, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg vonMangoldt_nonneg, Real.norm_eq_abs]

/-- A bounded twist of `g` is summable. -/
theorem summable_gT_mul (η : ℝ → ℝ) (x δ : ℝ)
    (hs : Summable (fun n : ℕ => Λ n * |η ((n : ℝ) / x)|)) (c : ℕ → ℂ)
    (hc : ∀ n, ‖c n‖ ≤ 1) : Summable (fun n => gT η x δ n * c n) := by
  refine Summable.of_norm_bounded hs fun n => ?_
  rw [norm_mul, norm_gT]
  exact mul_le_of_le_one_right (mul_nonneg vonMangoldt_nonneg (abs_nonneg _)) (hc n)

/-- `Σ = ∑ Λ(n)|η(n/x)| ≥ 0`. -/
theorem sAbs_nonneg (η : ℝ → ℝ) (x : ℝ) : 0 ≤ DS.sAbs η x :=
  tsum_nonneg fun _ => mul_nonneg vonMangoldt_nonneg (abs_nonneg _)

open Classical in
/-- The summands of `B`. -/
theorem summable_bNon (η : ℝ → ℝ) (x : ℝ) (q : ℕ)
    (hs : Summable (fun n : ℕ => Λ n * |η ((n : ℝ) / x)|)) :
    Summable (fun n : ℕ => if IsUnit (n : ZMod q) then 0 else Λ n * |η ((n : ℝ) / x)|) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · split_ifs
    · exact le_rfl
    · exact mul_nonneg vonMangoldt_nonneg (abs_nonneg _)
  · split_ifs
    · exact mul_nonneg vonMangoldt_nonneg (abs_nonneg _)
    · exact le_rfl

/-- `S_{η,χ} = ∑ g_n χ(n)`. -/
theorem tw_eq (η : ℝ → ℝ) (x δ : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    tw η x δ χ = ∑' n : ℕ, gT η x δ n * χ (n : ZMod q) := by
  unfold tw MajSp.twSum gT
  exact tsum_congr fun n => by ring

/-- `|S_{η,χ}| ≤ Σ`. -/
theorem norm_tw_le (η : ℝ → ℝ) (x δ : ℝ) (hs : Summable (fun n : ℕ => Λ n * |η ((n : ℝ) / x)|))
    {q : ℕ} (χ : DirichletCharacter ℂ q) : ‖tw η x δ χ‖ ≤ DS.sAbs η x := by
  rw [tw_eq]
  refine tsum_of_norm_bounded hs.hasSum fun n => ?_
  rw [norm_mul, norm_gT]
  exact mul_le_of_le_one_right (mul_nonneg vonMangoldt_nonneg (abs_nonneg _))
    (DirichletCharacter.norm_le_one χ _)

/-- `|S_{η,χ*}| ≤ Σ`. -/
theorem norm_twP_le (η : ℝ → ℝ) (x δ : ℝ) (hs : Summable (fun n : ℕ => Λ n * |η ((n : ℝ) / x)|))
    {q : ℕ} (χ : DirichletCharacter ℂ q) : ‖twP η x δ χ‖ ≤ DS.sAbs η x :=
  norm_tw_le η x δ hs χ.primitiveCharacter

/-- `e(n(a/q + β)) = ψ(an)·e(nβ)`. -/
theorem e_split (q : ℕ) [NeZero q] (a n : ℕ) (β : ℝ) :
    e ((n : ℝ) * ((a : ℝ) / q + β)) =
      ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q)) * e ((n : ℝ) * β) := by
  have h1 : e ((n : ℝ) * ((a : ℝ) / q)) = ZMod.stdAddChar (((a * n : ℕ)) : ZMod q) := by
    rw [GaussInduced.std_natCast]
    unfold e
    congr 1
    push_cast
    ring
  rw [mul_add, ← e_add, h1, Nat.cast_mul]

/-- `S(a/q + δ/x) = ∑ g_n ψ(an)`. -/
theorem sm_eq (η : ℝ → ℝ) (x δ : ℝ) (q : ℕ) [NeZero q] (a : ℕ) :
    Smooth.smSum η x ((a : ℝ) / q + δ / x) =
      ∑' n : ℕ, gT η x δ n * ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q)) := by
  unfold Smooth.smSum gT
  refine tsum_congr fun n => ?_
  rw [e_split q a n (δ / x)]
  ring

/-- `|S_η(α,x)| ≤ Σ`. -/
theorem norm_sm_le (η : ℝ → ℝ) (x α : ℝ) (hs : Summable (fun n : ℕ => Λ n * |η ((n : ℝ) / x)|)) :
    ‖Smooth.smSum η x α‖ ≤ DS.sAbs η x := by
  unfold Smooth.smSum
  refine tsum_of_norm_bounded hs.hasSum fun n => ?_
  rw [norm_mul, norm_mul, e_norm, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg vonMangoldt_nonneg, Real.norm_eq_abs]

/-- `∑_{a<q} G(a mod q) = ∑_{b : ZMod q} G(b)`. -/
theorem sum_range_zmod {M : Type*} [AddCommMonoid M] (q : ℕ) [NeZero q] (G : ZMod q → M) :
    ∑ a ∈ Finset.range q, G (a : ZMod q) = ∑ b : ZMod q, G b := by
  refine Finset.sum_nbij' (fun a => (a : ZMod q)) (fun b => b.val) ?_ ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_univ _
  · intro b _
    exact Finset.mem_range.mpr (ZMod.val_lt b)
  · intro a ha
    exact ZMod.val_cast_of_lt (Finset.mem_range.mp ha)
  · intro b _
    exact ZMod.natCast_zmod_val b
  · intro a _
    rfl

/-- A character of level `1` is `1` at every integer. -/
theorem char_level_one {N : ℕ} (hN : N = 1) (ψ : DirichletCharacter ℂ N) (n : ℕ) :
    ψ (n : ZMod N) = 1 := by
  subst hN
  rw [DirichletCharacter.level_one ψ]
  exact MulChar.one_apply (isUnit_of_subsingleton _)

/-! ## The composition: `(i)`–`(iv)` and `perArc_of_links` -/

/-- **(i)** `P1` and `P7` summed over the `φ(q)` reduced residues:
`|∑_a |S|² − ∑_a |X_a|²| ≤ φ(q)·B(2Σ + B)`. -/
theorem arc_vs_x (h1 : BeatIt) (h7 : SqDiff) (η : ℝ → ℝ) (x δ : ℝ) (q : ℕ) [NeZero q]
    (hs : Summable (fun n : ℕ => Λ n * |η ((n : ℝ) / x)|)) :
    |DS.arcSq η x q δ - ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ‖xMain η x δ q (a : ZMod q)‖ ^ 2| ≤
      q.totient * (bNon η x q * (2 * DS.sAbs η x + bNon η x q)) := by
  unfold DS.arcSq
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hcard : ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
    rw [Nat.totient_eq_card_coprime]
    congr 1
    exact Finset.filter_congr fun a _ => Nat.coprime_comm
  calc ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        |‖Smooth.smSum η x ((a : ℝ) / q + δ / x)‖ ^ 2 - ‖xMain η x δ q (a : ZMod q)‖ ^ 2|
      ≤ ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          bNon η x q * (2 * DS.sAbs η x + bNon η x q) := by
        refine Finset.sum_le_sum fun a ha => ?_
        have hd := h1 η x δ q hs a (Finset.mem_filter.mp ha).2
        have hS := norm_sm_le η x ((a : ℝ) / q + δ / x) hs
        have hX : ‖xMain η x δ q (a : ZMod q)‖ ≤ ‖Smooth.smSum η x ((a : ℝ) / q + δ / x)‖ +
            ‖Smooth.smSum η x ((a : ℝ) / q + δ / x) - xMain η x δ q (a : ZMod q)‖ := by
          calc ‖xMain η x δ q (a : ZMod q)‖ = ‖Smooth.smSum η x ((a : ℝ) / q + δ / x) -
                (Smooth.smSum η x ((a : ℝ) / q + δ / x) - xMain η x δ q (a : ZMod q))‖ := by
                rw [sub_sub_cancel]
            _ ≤ _ := norm_sub_le _ _
        have hsum : ‖Smooth.smSum η x ((a : ℝ) / q + δ / x)‖ + ‖xMain η x δ q (a : ZMod q)‖ ≤
            2 * DS.sAbs η x + bNon η x q := by linarith
        exact le_trans (h7 _ _) (mul_le_mul hd hsum
          (add_nonneg (norm_nonneg _) (norm_nonneg _)) (le_trans (norm_nonneg _) hd))
    _ = q.totient * (bNon η x q * (2 * DS.sAbs η x + bNon η x q)) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]

/-- **(ii)** `P3` at `c_χ = τ(χ̄)S_χ/φ(q)`: `∑_a |X_a|² = ∑_χ |τ(χ̄)|²|S_χ|²/φ(q)`. -/
theorem x_eq_w (h3 : Orth) (η : ℝ → ℝ) (x δ : ℝ) (q : ℕ) [NeZero q] :
    ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ‖xMain η x δ q (a : ZMod q)‖ ^ 2 =
      (∑ χ : DirichletCharacter ℂ q,
        ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 * ‖tw η x δ χ‖ ^ 2) / q.totient := by
  unfold xMain
  rw [h3 q (fun χ => gaussSum χ⁻¹ ZMod.stdAddChar * tw η x δ χ / (q.totient : ℂ))]
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  simp_rw [norm_div, norm_mul, Complex.norm_natCast, div_pow, mul_pow]
  rw [← Finset.sum_div]
  field_simp

/-- **(iii)** `P2`, `P7` and `∑_χ |τ(χ̄)|² = φ(q)²` (`P4`): replacing `S_χ` by `S_{χ*}` costs
`φ(q)·2BΣ`. -/
theorem w_vs_p (h2 : ToPrimitive) (h4 : Gauss) (h7 : SqDiff) (η : ℝ → ℝ) (x δ : ℝ) (q : ℕ)
    [NeZero q] (hs : Summable (fun n : ℕ => Λ n * |η ((n : ℝ) / x)|)) :
    |(∑ χ : DirichletCharacter ℂ q,
        ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 * ‖tw η x δ χ‖ ^ 2) / q.totient -
      (∑ χ : DirichletCharacter ℂ q,
        ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 * ‖twP η x δ χ‖ ^ 2) / q.totient| ≤
      q.totient * (2 * bNon η x q * DS.sAbs η x) := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  rw [← sub_div, abs_div, abs_of_pos hφ, div_le_iff₀ hφ, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hb : ∀ χ : DirichletCharacter ℂ q,
      |‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 * ‖tw η x δ χ‖ ^ 2 -
        ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 * ‖twP η x δ χ‖ ^ 2| ≤
          ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 * (2 * bNon η x q * DS.sAbs η x) := by
    intro χ
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _)]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have hd := h2 η x δ q hs χ
    have ht := norm_tw_le η x δ hs χ
    have htp := norm_twP_le η x δ hs χ
    calc |‖tw η x δ χ‖ ^ 2 - ‖twP η x δ χ‖ ^ 2|
        ≤ ‖tw η x δ χ - twP η x δ χ‖ * (‖tw η x δ χ‖ + ‖twP η x δ χ‖) := h7 _ _
      _ ≤ bNon η x q * (DS.sAbs η x + DS.sAbs η x) :=
          mul_le_mul hd (add_le_add ht htp) (add_nonneg (norm_nonneg _) (norm_nonneg _))
            (le_trans (norm_nonneg _) hd)
      _ = 2 * bNon η x q * DS.sAbs η x := by ring
  calc ∑ χ : DirichletCharacter ℂ q,
        |‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 * ‖tw η x δ χ‖ ^ 2 -
          ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 * ‖twP η x δ χ‖ ^ 2|
      ≤ ∑ χ : DirichletCharacter ℂ q,
          ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 * (2 * bNon η x q * DS.sAbs η x) :=
        Finset.sum_le_sum fun χ _ => hb χ
    _ = (q.totient : ℝ) ^ 2 * (2 * bNon η x q * DS.sAbs η x) := by
        rw [← Finset.sum_mul, (h4 q).2.2]
    _ = q.totient * (2 * bNon η x q * DS.sAbs η x) * q.totient := by ring

/-- **(iv)** `P4`, `P5`, `P6`: the principal character carries the main term, the `φ(q) − 1`
others at most `E²x²` in total. -/
theorem p_vs_main (h4 : Gauss) (h5 : Principal) (h6 : Others) (η : ℝ → ℝ) (x δ T E : ℝ) (q : ℕ)
    [NeZero q] (hx : x ≠ 0) (hT : MajSp.ETBound η 600000 x T) (hE : MajSp.EBound η x E)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 150000 * Nat.gcd q 2)
    (hδ : |δ| ≤ (Nat.gcd q 2 : ℝ) * 600000 / q) :
    |(∑ χ : DirichletCharacter ℂ q,
        ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 * ‖twP η x δ χ‖ ^ 2) / q.totient -
      DS.cQ q * x ^ 2 * ‖MajSp.mainFT η δ‖ ^ 2| ≤
      DS.cQ q * x ^ 2 * (T * (2 * MajSp.l1 η + T)) + E ^ 2 * x ^ 2 := by
  classical
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hδ' : |δ| ≤ 600000 := by
    have hg : (Nat.gcd q 2 : ℝ) ≤ q := by exact_mod_cast Nat.gcd_le_left 2 (NeZero.pos q)
    refine le_trans hδ ?_
    rw [div_le_iff₀ hq0]
    nlinarith
  obtain ⟨hg1, hgle, -⟩ := h4 q
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ q)), inv_one, hg1]
  set R := ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
    ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 * ‖twP η x δ χ‖ ^ 2 with hRdef
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hcard : ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ) ≤ q.totient := by
    have hc : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
      rw [← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
    have h := Finset.card_erase_le (s := (Finset.univ : Finset (DirichletCharacter ℂ q)))
      (a := 1)
    rw [Finset.card_univ, hc] at h
    exact_mod_cast h
  have hR : R ≤ q.totient * (E ^ 2 * x ^ 2) := by
    calc R ≤ ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), E ^ 2 * x ^ 2 := by
          refine Finset.sum_le_sum fun χ hχ => ?_
          have hne : χ ≠ 1 := Finset.ne_of_mem_erase hχ
          calc ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 * ‖twP η x δ χ‖ ^ 2
              ≤ (χ.conductor : ℝ) * ‖twP η x δ χ‖ ^ 2 :=
                mul_le_mul_of_nonneg_right (hgle χ) (sq_nonneg _)
            _ ≤ E ^ 2 * x ^ 2 := h6 η x δ E q hx hE hq1 hq2 hδ χ hne
      _ = (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card * (E ^ 2 * x ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ q.totient * (E ^ 2 * x ^ 2) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
  have hP := h5 η x δ T q hx hT hδ'
  have hμ : ‖((moebius q : ℤ) : ℂ)‖ ^ 2 = ((moebius q : ℤ) : ℝ) ^ 2 := by
    rw [Complex.norm_intCast, sq_abs]
  rw [hμ]
  unfold DS.cQ
  set m2 := ((moebius q : ℤ) : ℝ) ^ 2 with hm2
  set P1 := ‖twP η x δ (1 : DirichletCharacter ℂ q)‖ ^ 2
  set F2 := ‖MajSp.mainFT η δ‖ ^ 2
  have key : (m2 * P1 + R) / q.totient - m2 / q.totient * x ^ 2 * F2 =
      m2 / q.totient * (P1 - x ^ 2 * F2) + R / q.totient := by
    field_simp
    ring
  rw [key]
  have hc0 : 0 ≤ m2 / q.totient := div_nonneg (sq_nonneg _) hφ.le
  have ha : |m2 / q.totient * (P1 - x ^ 2 * F2)| ≤
      m2 / q.totient * (x ^ 2 * (T * (2 * MajSp.l1 η + T))) := by
    rw [abs_mul, abs_of_nonneg hc0]
    exact mul_le_mul_of_nonneg_left hP hc0
  have hb : |R / q.totient| ≤ E ^ 2 * x ^ 2 := by
    rw [abs_of_nonneg (div_nonneg hR0 hφ.le), div_le_iff₀ hφ]
    linarith
  have hsplit := abs_add_le (m2 / q.totient * (P1 - x ^ 2 * F2)) (R / q.totient)
  have heq : m2 / q.totient * (x ^ 2 * (T * (2 * MajSp.l1 η + T))) =
      m2 / q.totient * x ^ 2 * (T * (2 * MajSp.l1 η + T)) := by ring
  linarith

/-- The closing arithmetic: `φB(2Σ+B) + 2φBΣ ≤ φB_q(2Σ+B_q)` when `0 ≤ 2B ≤ B_q`, `Σ ≥ 0`. -/
theorem close_all (Sq Xq W P M B s φ bq C : ℝ) (h1 : |Sq - Xq| ≤ φ * (B * (2 * s + B)))
    (h2 : Xq = W) (h3 : |W - P| ≤ φ * (2 * B * s)) (h4 : |P - M| ≤ C) (hB : 0 ≤ B)
    (hb : 2 * B ≤ bq) (hs : 0 ≤ s) (hφ : 0 ≤ φ) : |Sq - M| ≤ C + φ * bq * (2 * s + bq) := by
  subst h2
  have k1 : B * (2 * s + B) + 2 * B * s ≤ bq * (2 * s + bq) := by
    nlinarith [mul_nonneg hs (sub_nonneg.2 hb), mul_nonneg hB (sub_nonneg.2 hb)]
  have k2 := mul_le_mul_of_nonneg_left k1 hφ
  have t : |Sq - M| ≤ |Sq - Xq| + |Xq - P| + |P - M| := by
    calc |Sq - M| = |(Sq - Xq) + (Xq - P) + (P - M)| := by ring_nf
      _ ≤ |Sq - Xq| + |Xq - P| + |P - M| := abs_add_three _ _ _
  nlinarith

/-- **THE COMPOSITION**: the eight links give `DS.PerArc η` for every weight. The proof is
application of `(i)`–`(iv)` and `close_all`. -/
theorem perArc_of_links (h1 : BeatIt) (hm : MassLink) (h2 : ToPrimitive) (h3 : Orth)
    (h4 : Gauss) (h5 : Principal) (h6 : Others) (h7 : SqDiff) (η : ℝ → ℝ) : DS.PerArc η := by
  intro x hx hs T E hT hE q hq1 hq2 δ hδ
  haveI : NeZero q := ⟨Nat.one_le_iff_ne_zero.mp hq1⟩
  have hx0 : x ≠ 0 := (MinSp.x_pos x hx).ne'
  obtain ⟨hB, hb⟩ := hm η x q (NeZero.ne q) hs
  exact close_all _ _ _ _ _ _ _ _ _ _ (arc_vs_x h1 h7 η x δ q hs) (x_eq_w h3 η x δ q)
    (w_vs_p h2 h4 h7 η x δ q hs) (p_vs_main h4 h5 h6 η x δ T E q hx0 hT hE hq1 hq2 hδ) hB hb
    (sAbs_nonneg η x) (Nat.cast_nonneg _)

/-! ## The links, PROVED -/

/-- **[P7] PROVED.** -/
theorem sqDiff : SqDiff := by
  intro u v
  have h1 : ‖u‖ ^ 2 - ‖v‖ ^ 2 = (‖u‖ - ‖v‖) * (‖u‖ + ‖v‖) := by ring
  rw [h1, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg u) (norm_nonneg v))]
  exact mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le u v)
    (add_nonneg (norm_nonneg u) (norm_nonneg v))

/-- **[P1] PROVED**: the characters expand `e(an/q)` exactly on `(n,q) = 1`
(`GaussInduced.sum_char_gaussSum`), so `S − X_a = ∑_{(n,q)>1} g_n e(an/q)`. -/
theorem beatIt : BeatIt := by
  intro η x δ q _ hs a ha
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hX : xMain η x δ q a = ∑' n : ℕ, gT η x δ n *
      (if IsUnit (n : ZMod q) then ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q)) else 0) := by
    unfold xMain
    simp_rw [tw_eq]
    have h1 : ∀ χ : DirichletCharacter ℂ q,
        gaussSum χ⁻¹ ZMod.stdAddChar * (∑' n : ℕ, gT η x δ n * χ (n : ZMod q)) /
            (q.totient : ℂ) * χ (a : ZMod q) =
          ∑' n : ℕ, gaussSum χ⁻¹ ZMod.stdAddChar / (q.totient : ℂ) * χ (a : ZMod q) *
            (gT η x δ n * χ (n : ZMod q)) := by
      intro χ
      rw [tsum_mul_left]
      ring
    rw [Finset.sum_congr rfl fun χ _ => h1 χ]
    rw [← Summable.tsum_finsetSum fun χ _ =>
      (summable_gT_mul η x δ hs _ fun n => DirichletCharacter.norm_le_one χ _).mul_left _]
    refine tsum_congr fun n => ?_
    have h2 := GaussInduced.sum_char_gaussSum (N := q) (ZMod.unitOfCoprime a ha) (n : ZMod q)
    rw [ZMod.coe_unitOfCoprime] at h2
    have h3 : ∑ χ : DirichletCharacter ℂ q, gaussSum χ⁻¹ ZMod.stdAddChar / (q.totient : ℂ) *
        χ (a : ZMod q) * (gT η x δ n * χ (n : ZMod q)) =
          gT η x δ n / (q.totient : ℂ) * ∑ χ : DirichletCharacter ℂ q,
            gaussSum χ⁻¹ ZMod.stdAddChar * (χ (a : ZMod q) * χ (n : ZMod q)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun χ _ => by ring
    rw [h3, h2]
    split_ifs
    · field_simp
    · ring
  have hc1 : ∀ n : ℕ, ‖ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))‖ ≤ 1 :=
    fun n => le_of_eq (GaussInduced.norm_std _)
  have hc2 : ∀ n : ℕ, ‖(if IsUnit (n : ZMod q) then
      ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q)) else 0)‖ ≤ 1 := by
    intro n
    split_ifs
    · exact hc1 n
    · rw [norm_zero]
      exact zero_le_one
  rw [sm_eq, hX, ← Summable.tsum_sub (summable_gT_mul η x δ hs _ hc1)
    (summable_gT_mul η x δ hs _ hc2)]
  refine tsum_of_norm_bounded (summable_bNon η x q hs).hasSum fun n => ?_
  rw [← mul_sub, norm_mul, norm_gT]
  split_ifs with hu
  · rw [sub_self, norm_zero, mul_zero]
  · rw [sub_zero, GaussInduced.norm_std, mul_one]

/-- **[P1b] PROVED**: a non-coprime `n` with `Λ(n) ≠ 0` is a power of a prime `p ∣ q`, and the
powers of `p` carry `log p ∑_k |η(p^{k+1}/x)|`. -/
theorem massLink : MassLink := by
  classical
  intro η x q hq hs
  have hnn : ∀ n : ℕ, 0 ≤ Λ n * |η ((n : ℝ) / x)| :=
    fun n => mul_nonneg vonMangoldt_nonneg (abs_nonneg _)
  refine ⟨tsum_nonneg fun n => ?_, ?_⟩
  · split_ifs
    · exact le_rfl
    · exact hnn n
  have hdom : ∀ n : ℕ, (if IsUnit (n : ZMod q) then 0 else Λ n * |η ((n : ℝ) / x)|) ≤
      ∑ p ∈ q.primeFactors, (if p ∣ n then Λ n * |η ((n : ℝ) / x)| else 0) := by
    intro n
    have hpos : ∀ p ∈ q.primeFactors, 0 ≤ (if p ∣ n then Λ n * |η ((n : ℝ) / x)| else 0) := by
      intro p _
      split_ifs
      · exact hnn n
      · exact le_rfl
    split_ifs with hu
    · exact Finset.sum_nonneg hpos
    · rw [ZMod.isUnit_iff_coprime] at hu
      obtain ⟨p, hp, hpn, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hu
      have hpPF : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpq, hq⟩
      have h1 := Finset.single_le_sum hpos hpPF
      rw [if_pos hpn] at h1
      exact h1
  have hsumP : ∀ p ∈ q.primeFactors,
      Summable (fun n : ℕ => if p ∣ n then Λ n * |η ((n : ℝ) / x)| else 0) := by
    intro p _
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
    · split_ifs
      · exact hnn n
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact hnn n
  have hstep := Summable.tsum_le_tsum hdom (summable_bNon η x q hs) (summable_sum hsumP)
  rw [Summable.tsum_finsetSum hsumP] at hstep
  have hp_eq : ∀ p ∈ q.primeFactors,
      ∑' n : ℕ, (if p ∣ n then Λ n * |η ((n : ℝ) / x)| else 0) =
        Real.log p * ∑' k : ℕ, |η ((p : ℝ) ^ (k + 1) / x)| := by
    intro p hpPF
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpPF
    rw [← tsum_mul_left]
    have hinj : Function.Injective (fun k : ℕ => p ^ (k + 1)) := by
      intro i j hij
      have h := Nat.pow_right_injective hp.two_le hij
      omega
    have hsupp : Function.support
        (fun n : ℕ => if p ∣ n then Λ n * |η ((n : ℝ) / x)| else 0) ⊆
          Set.range (fun k : ℕ => p ^ (k + 1)) := by
      intro n hn
      rw [Function.mem_support] at hn
      have hpn : p ∣ n := by
        by_contra h
        exact hn (if_neg h)
      have hΛ : Λ n ≠ 0 := by
        intro h
        apply hn
        rw [if_pos hpn, h, zero_mul]
      rw [vonMangoldt_ne_zero_iff, isPrimePow_nat_iff] at hΛ
      obtain ⟨r, j, hr, hj, rfl⟩ := hΛ
      have hpr : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hpn)
      refine ⟨j - 1, ?_⟩
      change p ^ (j - 1 + 1) = r ^ j
      rw [hpr, Nat.sub_add_cancel hj]
    rw [← hinj.tsum_eq hsupp]
    refine tsum_congr fun k => ?_
    rw [if_pos (dvd_pow_self p (Nat.succ_ne_zero k)), vonMangoldt_apply_pow (Nat.succ_ne_zero k),
      vonMangoldt_apply_prime hp, Nat.cast_pow]
  rw [Finset.sum_congr rfl hp_eq] at hstep
  unfold DS.bQ
  unfold bNon
  linarith

/-- **[P2] PROVED**: `χ(n) = χ*(n)` for `(n,q) = 1`, and `|χ*(n)| ≤ 1` otherwise. -/
theorem toPrimitive : ToPrimitive := by
  intro η x δ q _ hs χ
  have hc : ∀ (N : ℕ) (ψ : DirichletCharacter ℂ N) (n : ℕ), ‖ψ (n : ZMod N)‖ ≤ 1 :=
    fun N ψ n => DirichletCharacter.norm_le_one ψ _
  rw [twP, tw_eq, ← tw, tw_eq, ← Summable.tsum_sub (summable_gT_mul η x δ hs _ (hc q χ))
    (summable_gT_mul η x δ hs _ (hc _ χ.primitiveCharacter))]
  refine tsum_of_norm_bounded (summable_bNon η x q hs).hasSum fun n => ?_
  rw [← mul_sub, norm_mul, norm_gT]
  split_ifs with hu
  · have hcop : IsCoprime (n : ℤ) (q : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact (ZMod.isUnit_iff_coprime n q).mp hu
    have h := χ.primitiveCharacter_apply_of_isCoprime hcop
    simp only [Int.cast_natCast] at h
    rw [h, sub_self, norm_zero, mul_zero]
  · rw [MulChar.map_nonunit _ hu, zero_sub, norm_neg]
    exact mul_le_of_le_one_right (mul_nonneg vonMangoldt_nonneg (abs_nonneg _)) (hc _ _ n)

/-- **[P3] PROVED** from `GaussInduced.sum_norm_sq_char_comb`: the non-coprime `a` contribute `0`,
and `a ↦ a mod q` is a bijection `range q ≃ ZMod q`. -/
theorem orth : Orth := by
  intro q _ c
  rw [Finset.sum_filter_of_ne]
  · rw [sum_range_zmod q (fun b => ‖∑ χ : DirichletCharacter ℂ q, c χ * χ b‖ ^ 2)]
    exact GaussInduced.sum_norm_sq_char_comb c
  · intro a _ hne
    by_contra hcop
    apply hne
    have hnu : ¬ IsUnit (a : ZMod q) := by
      rw [ZMod.isUnit_iff_coprime]
      exact hcop
    rw [Finset.sum_eq_zero fun χ _ => by rw [MulChar.map_nonunit _ hnu, mul_zero], norm_zero]
    ring

/-- **[P4] PROVED** in `GaussInduced` (the induced-character formula). -/
theorem gauss : Gauss := by
  intro q _
  refine ⟨GaussInduced.gaussSum_one, fun χ => ?_, GaussInduced.sum_norm_sq_gaussSum_inv⟩
  have h := GaussInduced.norm_sq_gaussSum_le χ⁻¹
  rwa [DirichletCharacter.conductor_inv] at h

/-- **[P5] PROVED**: `χ₀* = 1` mod `1`, so `S_{χ₀*} = x(η̂(−δ) + err_T)`; `|η̂(−δ)| ≤ |η|₁`. -/
theorem principal : Principal := by
  intro η x δ T q _ hx hT hδ
  have hval := char_level_one (DirichletCharacter.conductor_one (R := ℂ) (n := q))
    (1 : DirichletCharacter ℂ q).primitiveCharacter
  have htw : twP η x δ (1 : DirichletCharacter ℂ q) =
      MajSp.twSum η (1 : DirichletCharacter ℂ 1) x (δ / x) := by
    unfold twP MajSp.twSum
    refine tsum_congr fun n => ?_
    rw [hval n, char_level_one rfl (1 : DirichletCharacter ℂ 1) n]
  set F := MajSp.mainFT η δ with hF
  set e0 := MajSp.err η (1 : DirichletCharacter ℂ 1) δ x with he0
  have herr : e0 = MajSp.twSum η (1 : DirichletCharacter ℂ 1) x (δ / x) / x - F := by
    rw [he0]
    unfold MajSp.err
    rw [if_pos rfl]
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have htw' : twP η x δ (1 : DirichletCharacter ℂ q) = (x : ℂ) * (F + e0) := by
    rw [htw, herr]
    field_simp
    ring
  have hT0 : ‖e0‖ ≤ T := hT δ hδ
  have hFl : ‖F‖ ≤ MajSp.l1 η := by
    rw [hF]
    unfold MajSp.mainFT MajSp.l1
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only
    rw [norm_mul, e_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [htw', norm_mul, Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs, ← mul_sub, abs_mul,
    abs_of_nonneg (sq_nonneg x)]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg x)
  have h7 := sqDiff (F + e0) F
  rw [add_sub_cancel_left] at h7
  have hFe : ‖F + e0‖ ≤ ‖F‖ + ‖e0‖ := norm_add_le _ _
  have hn0 : 0 ≤ ‖e0‖ := norm_nonneg _
  have hsum : ‖F + e0‖ + ‖F‖ ≤ 2 * MajSp.l1 η + T := by linarith
  calc |‖F + e0‖ ^ 2 - ‖F‖ ^ 2| ≤ ‖e0‖ * (‖F + e0‖ + ‖F‖) := h7
    _ ≤ T * (2 * MajSp.l1 η + T) :=
        mul_le_mul hT0 hsum (add_nonneg (norm_nonneg _) (norm_nonneg _)) (le_trans hn0 hT0)

/-- **[P6] PROVED**: for `χ ≠ χ₀` the conductor is `≠ 1`, so `err_{χ*} = S_{χ*}/x`, and `EBound`
bounds `√q*·|err_{χ*}|`. -/
theorem others : Others := by
  intro η x δ E q _ hx hE hq1 hq2 hδ χ hχ
  have hc1 : χ.conductor ≠ 1 := fun h => hχ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)
  have hb := hE q hq1 hq2 χ δ hδ
  have herr : MajSp.err η χ.primitiveCharacter δ x = twP η x δ χ / x := by
    unfold MajSp.err twP
    rw [if_neg hc1, sub_zero]
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have htw : twP η x δ χ = (x : ℂ) * MajSp.err η χ.primitiveCharacter δ x := by
    rw [herr]
    field_simp
  have hs0 : 0 ≤ Real.sqrt (χ.conductor : ℝ) * ‖MajSp.err η χ.primitiveCharacter δ x‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hsq := pow_le_pow_left₀ hs0 hb 2
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at hsq
  rw [htw, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  calc (χ.conductor : ℝ) * (x ^ 2 * ‖MajSp.err η χ.primitiveCharacter δ x‖ ^ 2)
      = x ^ 2 * ((χ.conductor : ℝ) * ‖MajSp.err η χ.primitiveCharacter δ x‖ ^ 2) := by ring
    _ ≤ x ^ 2 * E ^ 2 := mul_le_mul_of_nonneg_left hsq (sq_nonneg x)
    _ = E ^ 2 * x ^ 2 := by ring

/-! ## `PerArc`, discharged -/

/-- **`DS.PerArc η` for EVERY weight `η`** (`ternvin.tex` 1233–1270): the composition fed by the
eight proved links. -/
theorem perArc (η : ℝ → ℝ) : DS.PerArc η :=
  perArc_of_links beatIt massLink toPrimitive orth gauss principal others sqDiff η

/-- **`DS.PerArc HW.etaPlus`**, Helfgott's `η₊`. -/
theorem perArc_helf : DS.PerArc HW.etaPlus := perArc HW.etaPlus

/-- **`DrujalE100` with `PerArc` discharged**: `ArcInt`, `MardiQ`, `KSmall` remain. -/
theorem drujalE100_of_rest (η : ℝ → ℝ) (ai : DS.ArcInt η) (mq : DS.MardiQ η)
    (ks : DS.KSmall η) : DS.DrujalE100 η :=
  DS.drujalE100_of_spine η (perArc η) ai mq ks

/-- **`DrujalLowD` with `PerArc` discharged**: `ArcInt`, `BandQ`, `TailQ`, `KSmall` remain. -/
theorem drujalLowD_of_rest (η ηo : ℝ → ℝ) (ai : DS.ArcInt η) (bq : DS.BandQ η ηo)
    (tq : DS.TailQ ηo) (ks : DS.KSmall η) : DS.DrujalLowD η ηo :=
  DS.drujalLowD_of_spine η ηo (perArc η) ai bq tq ks

end Principia.Common.TernaryGoldbach.PA
