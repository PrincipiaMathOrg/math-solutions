import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# MathDB #371420 — an aperiodic torus translation

Write-up: `mathdb-open-problems/problems/371420/solution.md`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress`.  (Note the extension:
this batch publishes `solution.md`, not `solution.tex`.)
Source: arXiv:2511.08227v1, **Conjecture 2** — for any `C^r` (`r > 1`) or `C^∞`
diffeomorphism `f` of a compact surface,

`limsup_{n→∞} #P_n(f) / exp(n · h_top(f)) > 0`,

where `P_n(f)` is the set of fixed points of `fⁿ`.  **Neither the displayed conjecture nor
the MathDB transcription assumes positive topological entropy** — that omission is the gap,
and the write-up's scope section is explicit that Sarig's affirmative theorem does assume
it.  So the witness below has to be a smooth surface diffeomorphism and nothing more, which
it is.

## The witness

`T = AddCircle (1 : ℝ)`, `M = T × T` is the flat 2-torus, and `f [x,y] = [x + √2, y]`
(`al` is `√2` in `T`).  This is an isometry of a compact surface, so a `C^∞`
diffeomorphism; `f_bij` exhibits the inverse as translation by `−√2`.

## What is proved

* `iterate_f` — `fⁿ (x,y) = (x + n·√2, y)`.
* `no_periodic` — **`P_n(f) = ∅` for every `n ≥ 1`**: a fixed point of `fⁿ` forces
  `n√2 ∈ ℤ`, contradicting `irrational_sqrt_two`.
* `ratio_eq_zero`, `limsup_eq_zero`, `not_conj` — the conjecture's quotient has `limsup`
  zero, hence is not positive.

**The entropy never appears.**  The write-up refutes the conjecture by computing both
`P_n(f) = ∅` *and* `h_top(f) = 0`.  The second is not needed: the numerator is zero for
every `n ≥ 1`, so the quotient is zero whatever the entropy is.  Accordingly `not_conj`
quantifies over **all** `h : ℝ` and proves the `limsup` is `0` for each — a strictly
stronger statement than the one the write-up needs, and one that avoids topological
entropy entirely (Mathlib has no usable development of it).

**Not Lean-checked** (read off, as `#360860` reads off its barycentre formula): that `M` is
a smooth compact surface and that `f` is `C^∞`.  These are the standard facts that a
translation descends to a quotient group and is smooth there; what *is* checked is the
bijectivity of `f` with an explicit inverse, and the whole dynamical content.

Values checked in `Campaigns/MathDB-Formalization/verify_371420.py`.
-/

namespace Principia.MathDB.P371420

open Filter

/-- The circle `ℝ/ℤ`. -/
abbrev T : Type := AddCircle (1 : ℝ)

/-- The flat 2-torus. -/
abbrev M : Type := T × T

/-- The translation amount `√2`, as an element of `ℝ/ℤ`. -/
noncomputable def al : T := ((Real.sqrt 2 : ℝ) : T)

/-- The witness: the irrational translation `[x,y] ↦ [x + √2, y]`. -/
noncomputable def f (p : M) : M := (p.1 + al, p.2)

/-- Its inverse is translation by `−√2`, so `f` is a bijection of the torus. -/
noncomputable def g (p : M) : M := (p.1 - al, p.2)

theorem f_bij : Function.Bijective f := by
  constructor
  · intro p q h
    rw [f, f, Prod.mk.injEq] at h
    exact Prod.ext (by simpa using h.1) h.2
  · intro p
    refine ⟨g p, ?_⟩
    rw [f, g]
    simp

theorem g_left (p : M) : g (f p) = p := by
  rw [f, g]; simp

theorem iterate_f (n : ℕ) (p : M) : f^[n] p = (p.1 + n • al, p.2) := by
  induction n generalizing p with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, f]
    simp [succ_nsmul]
    abel

/-- `n • √2 ≠ 0` in `ℝ/ℤ` for `n ≥ 1`: otherwise `√2` would be rational. -/
theorem nsmul_al_ne_zero {n : ℕ} (hn : 1 ≤ n) : n • al ≠ 0 := by
  intro h
  rw [al, ← AddCircle.coe_nsmul] at h
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).1 h
  -- `hk : k • (1 : ℝ) = n • √2`, i.e. `(k : ℝ) = n * √2`
  have hk' : (k : ℝ) = (n : ℝ) * Real.sqrt 2 := by
    simpa [nsmul_eq_mul] using hk
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have : Real.sqrt 2 = (k : ℝ) / (n : ℝ) := by
    field_simp [hn0] at hk' ⊢
    linarith [hk']
  exact irrational_sqrt_two ⟨(k : ℚ) / (n : ℚ), by
    push_cast
    rw [this]⟩

/-- **The witness has no periodic points of any period `n ≥ 1`.** -/
theorem no_periodic {n : ℕ} (hn : 1 ≤ n) (p : M) : f^[n] p ≠ p := by
  intro h
  rw [iterate_f] at h
  have h1 : p.1 + n • al = p.1 := congrArg Prod.fst h
  exact nsmul_al_ne_zero hn (by
    have := add_right_cancel (a := n • al) (b := p.1) (c := (0 : T))
    simpa using add_left_cancel (a := p.1) (by simpa using h1))

/-- The set of `n`-periodic points is empty for `n ≥ 1`. -/
theorem per_eq_empty {n : ℕ} (hn : 1 ≤ n) : {p : M | f^[n] p = p} = ∅ := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  exact no_periodic hn p

/-- The conjecture's numerator: the number of `n`-periodic points. -/
noncomputable def pcount (n : ℕ) : ℕ := Nat.card {p : M | f^[n] p = p}

theorem pcount_eq_zero {n : ℕ} (hn : 1 ≤ n) : pcount n = 0 := by
  rw [pcount, per_eq_empty hn]
  simp

/-- **The conjecture's ratio vanishes for every `n ≥ 1` and EVERY value of the entropy.**
This is why the refutation needs no topological entropy. -/
theorem ratio_eq_zero (h : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (pcount n : ℝ) / Real.exp ((n : ℝ) * h) = 0 := by
  rw [pcount_eq_zero hn]
  simp

theorem limsup_eq_zero (h : ℝ) :
    limsup (fun n : ℕ => (pcount n : ℝ) / Real.exp ((n : ℝ) * h)) atTop = 0 := by
  have hev : ∀ᶠ n : ℕ in atTop,
      (pcount n : ℝ) / Real.exp ((n : ℝ) * h) = (0 : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact ratio_eq_zero h hn
  rw [limsup_congr hev, limsup_const]

/-- **Conjecture 2 of arXiv:2511.08227v1 is FALSE as stated.**  The irrational torus
translation is a smooth diffeomorphism of a compact surface for which the conjectured
limsup is `0`, not positive — and this holds for *every* real value `h` of the topological
entropy, so no computation of `h_top(f)` is needed. -/
theorem not_conj (h : ℝ) :
    ¬ (0 < limsup (fun n : ℕ => (pcount n : ℝ) / Real.exp ((n : ℝ) * h)) atTop) := by
  rw [limsup_eq_zero h]
  exact lt_irrefl 0

end Principia.MathDB.P371420
