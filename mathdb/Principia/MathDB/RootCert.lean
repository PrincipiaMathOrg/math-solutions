import Mathlib

/-!
# Root-existence certificates from a contraction bound

Several MathDB rows are **refutations** whose witness is a complex number: a polynomial `P` is
claimed to have all its zeros in `Re < 0` (Hurwitz stability), or to be zero-free in some region,
and the write-up exhibits a disk in the forbidden region together with a *Rouché certificate* —
bounds showing the linear term of the Taylor expansion at the disk's centre dominates everything
else on the boundary.

Mathlib has no Rouché theorem, no argument principle and no winding number, so the write-ups'
route is unavailable. **It is also unnecessary.** Rouché is being used here only to prove that a
zero *exists*, never to count zeros, and existence of a zero is a fixed-point statement:

`Σ_k d_k w^k = 0`  ⟺  `w = -(d_0 + Σ_{k≥2} d_k w^k) / d_1`,

and the very bounds the certificates supply say exactly that the right-hand side maps the closed
disk `‖w‖ ≤ r` into itself and is a contraction there.  Banach's fixed-point theorem
(`ContractingWith.exists_fixedPoint'`) then produces the root, with an ordinary axiom footprint
and in exact rational arithmetic.

The main theorem is `exists_root_of_contraction`.  A caller supplies, for its own polynomial:
rational upper bounds `U k` on `‖d k‖`, a rational lower bound `L` on `‖d 1‖`, and the two
inequalities

* `U 0 + Σ_{k=2}^n U k * r^k ≤ L * r`     (the disk maps into itself), and
* `Σ_{k=2}^n k * U k * r^(k-1) < L`       (the map is a contraction),

each of which is a `norm_num` computation on integers.

Checked in Python against the three witness certificates in the collaborator's write-ups before
formalizing (#323157: r = 1/4 about 1 + 22i, Lipschitz constant 0.1199; #323159: r = 1 in the
certificate's scaled variable, 0.0659; #328557: r = 1/100000, 0.000218) — all three satisfy both
inequalities in exact rational arithmetic.
-/

namespace Principia.MathDB.RootCert

/-- On a disk of radius `r`, the `k`-th power map is Lipschitz with constant `k * r^(k-1)`.
This is the one genuinely analytic ingredient; everything else is bookkeeping. -/
theorem norm_pow_sub_pow_le (r : ℝ) (x y : ℂ) (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (k : ℕ) :
    ‖x ^ k - y ^ k‖ ≤ (k : ℝ) * r ^ (k - 1) * ‖x - y‖ := by
  have hr : (0 : ℝ) ≤ r := le_trans (norm_nonneg x) hx
  have hsum : ‖∑ i ∈ Finset.range k, x ^ i * y ^ (k - 1 - i)‖ ≤ (k : ℝ) * r ^ (k - 1) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ i ∈ Finset.range k, ‖x ^ i * y ^ (k - 1 - i)‖ ≤ r ^ (k - 1) := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [norm_mul, norm_pow, norm_pow]
      have h1 : ‖x‖ ^ i ≤ r ^ i := by gcongr <;> assumption
      have h2 : ‖y‖ ^ (k - 1 - i) ≤ r ^ (k - 1 - i) := by gcongr <;> assumption
      have h3 : ‖x‖ ^ i * ‖y‖ ^ (k - 1 - i) ≤ r ^ i * r ^ (k - 1 - i) :=
        mul_le_mul h1 h2 (pow_nonneg (norm_nonneg y) _) (pow_nonneg hr i)
      refine h3.trans_eq ?_
      rw [← pow_add]
      congr 1
      omega
    refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc ‖x ^ k - y ^ k‖
      = ‖(∑ i ∈ Finset.range k, x ^ i * y ^ (k - 1 - i)) * (x - y)‖ := by
        rw [geom_sum₂_mul]
    _ = ‖∑ i ∈ Finset.range k, x ^ i * y ^ (k - 1 - i)‖ * ‖x - y‖ := norm_mul _ _
    _ ≤ (k : ℝ) * r ^ (k - 1) * ‖x - y‖ :=
        mul_le_mul_of_nonneg_right hsum (norm_nonneg _)

/-- The fixed-point map: `w ↦ -(d₀ + Σ_{k≥2} d_k w^k) / d₁`, whose fixed points are exactly the
roots of `d₀ + d₁ w + Σ_{k≥2} d_k w^k`. -/
noncomputable def tmap (d : ℕ → ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  -(d 0 + ∑ k ∈ Finset.Icc 2 n, d k * w ^ k) / d 1

/-- The tail `Σ_{k≥2} d_k w^k` is bounded by `Σ_{k≥2} U_k r^k` on the disk. -/
theorem norm_tail_le (d : ℕ → ℂ) (U : ℕ → ℝ) (n : ℕ) (r : ℝ) (w : ℂ) (hw : ‖w‖ ≤ r)
    (hU : ∀ k ∈ Finset.Icc 2 n, ‖d k‖ ≤ U k) :
    ‖∑ k ∈ Finset.Icc 2 n, d k * w ^ k‖ ≤ ∑ k ∈ Finset.Icc 2 n, U k * r ^ k := by
  have hr : (0 : ℝ) ≤ r := le_trans (norm_nonneg w) hw
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum ?_)
  intro k hk
  rw [norm_mul, norm_pow]
  have h1 : ‖w‖ ^ k ≤ r ^ k := by gcongr <;> assumption
  exact mul_le_mul (hU k hk) h1 (pow_nonneg (norm_nonneg w) k)
    (le_trans (norm_nonneg _) (hU k hk))

/-- The tail is Lipschitz with constant `Σ_{k≥2} k U_k r^(k-1)` on the disk. -/
theorem norm_tail_sub_le (d : ℕ → ℂ) (U : ℕ → ℝ) (n : ℕ) (r : ℝ) (w v : ℂ)
    (hw : ‖w‖ ≤ r) (hv : ‖v‖ ≤ r) (hU : ∀ k ∈ Finset.Icc 2 n, ‖d k‖ ≤ U k) :
    ‖(∑ k ∈ Finset.Icc 2 n, d k * w ^ k) - ∑ k ∈ Finset.Icc 2 n, d k * v ^ k‖
      ≤ (∑ k ∈ Finset.Icc 2 n, (k : ℝ) * U k * r ^ (k - 1)) * ‖w - v‖ := by
  have hdiff : (∑ k ∈ Finset.Icc 2 n, d k * w ^ k) - ∑ k ∈ Finset.Icc 2 n, d k * v ^ k
      = ∑ k ∈ Finset.Icc 2 n, d k * (w ^ k - v ^ k) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hdiff, Finset.sum_mul]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum ?_)
  intro k hk
  rw [norm_mul]
  have hUk : 0 ≤ U k := le_trans (norm_nonneg _) (hU k hk)
  have hpow := norm_pow_sub_pow_le r w v hw hv k
  calc ‖d k‖ * ‖w ^ k - v ^ k‖
      ≤ U k * ((k : ℝ) * r ^ (k - 1) * ‖w - v‖) :=
        mul_le_mul (hU k hk) hpow (norm_nonneg _) hUk
    _ = (k : ℝ) * U k * r ^ (k - 1) * ‖w - v‖ := by ring

/-- **Root existence from a contraction certificate.**  If the Taylor coefficients `d` of a
polynomial about some centre satisfy, for rational bounds `U k ≥ ‖d k‖` and `L ≤ ‖d 1‖`,

* `U 0 + Σ_{k=2}^n U k r^k ≤ L r`   (self-map), and
* `Σ_{k=2}^n k U k r^(k-1) < L`     (contraction),

then the polynomial has a root in the closed disk of radius `r` about that centre.  No zero
counting, hence no Rouché theorem, is involved. -/
theorem exists_root_of_contraction (d : ℕ → ℂ) (U : ℕ → ℝ) (L r : ℝ) (n : ℕ)
    (hr : 0 < r) (hL : 0 < L) (hLd : L ≤ ‖d 1‖) (hU : ∀ k ≤ n, ‖d k‖ ≤ U k)
    (hself : U 0 + ∑ k ∈ Finset.Icc 2 n, U k * r ^ k ≤ L * r)
    (hlip : ∑ k ∈ Finset.Icc 2 n, (k : ℝ) * U k * r ^ (k - 1) < L) :
    ∃ w : ℂ, ‖w‖ ≤ r ∧ d 0 + d 1 * w + ∑ k ∈ Finset.Icc 2 n, d k * w ^ k = 0 := by
  -- only indices `≤ n` are ever used, so the caller need not describe `d` past its last index
  have hU' : ∀ k ∈ Finset.Icc 2 n, ‖d k‖ ≤ U k := fun k hk => hU k (Finset.mem_Icc.mp hk).2
  have hd1 : d 1 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hLd
    linarith
  have hd1n : 0 < ‖d 1‖ := lt_of_lt_of_le hL hLd
  set S : ℝ := ∑ k ∈ Finset.Icc 2 n, (k : ℝ) * U k * r ^ (k - 1) with hS
  have hSnn : 0 ≤ S := by
    rw [hS]
    refine Finset.sum_nonneg fun k hk => ?_
    have hUk : 0 ≤ U k := le_trans (norm_nonneg _) (hU' k hk)
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hUk) (pow_nonneg hr.le _)
  set Kv : ℝ := S / L with hKv
  have hKvnn : 0 ≤ Kv := div_nonneg hSnn hL.le
  have hKv1 : Kv < 1 := by
    rw [hKv, div_lt_one hL]
    exact hlip
  -- the closed disk, as a complete set
  set s : Set ℂ := Metric.closedBall 0 r with hs
  have hsc : IsComplete s := (Metric.isClosed_closedBall).isComplete
  have hmem : ∀ z : ℂ, z ∈ s ↔ ‖z‖ ≤ r := by
    intro z
    rw [hs, Metric.mem_closedBall, dist_zero_right]
  -- the map sends the disk into itself
  have hmaps : Set.MapsTo (tmap d n) s s := by
    intro w hw
    rw [hmem] at hw ⊢
    have htail := norm_tail_le d U n r w hw hU'
    have hnum : ‖d 0 + ∑ k ∈ Finset.Icc 2 n, d k * w ^ k‖ ≤ L * r := by
      refine le_trans (norm_add_le _ _) ?_
      have h0 : ‖d 0‖ ≤ U 0 := hU 0 (by omega)
      linarith
    unfold tmap
    rw [norm_div, norm_neg, div_le_iff₀ hd1n]
    calc ‖d 0 + ∑ k ∈ Finset.Icc 2 n, d k * w ^ k‖ ≤ L * r := hnum
      _ = r * L := by ring
      _ ≤ r * ‖d 1‖ := by
          exact mul_le_mul_of_nonneg_left hLd hr.le
  -- and contracts on it
  have hcontract : ContractingWith ⟨Kv, hKvnn⟩ (hmaps.restrict (tmap d n) s s) := by
    constructor
    · -- `NNReal.coe_lt_coe` is `Iff.rfl` and `coe_mk` is `rfl`, so this is defeq; `simpa`
      -- normalises the goal away from the hypothesis and must not be used here
      exact hKv1
    · refine LipschitzWith.of_dist_le_mul fun a b => ?_
      have ha : ‖(a : ℂ)‖ ≤ r := (hmem a).1 a.2
      have hb : ‖(b : ℂ)‖ ≤ r := (hmem b).1 b.2
      -- the numerator difference, bounded by the tail Lipschitz constant
      have hrev : ‖(b : ℂ) - (a : ℂ)‖ = ‖(a : ℂ) - (b : ℂ)‖ := norm_sub_rev _ _
      have hnum : ‖(d 0 + ∑ k ∈ Finset.Icc 2 n, d k * (b : ℂ) ^ k)
            - (d 0 + ∑ k ∈ Finset.Icc 2 n, d k * (a : ℂ) ^ k)‖
          ≤ S * ‖(a : ℂ) - (b : ℂ)‖ := by
        rw [add_sub_add_left_eq_sub]
        refine (norm_tail_sub_le d U n r (b : ℂ) (a : ℂ) hb ha hU').trans_eq ?_
        rw [hrev]
      -- dividing by ‖d 1‖ ≥ L only helps
      have hstep : S * ‖(a : ℂ) - (b : ℂ)‖ ≤ Kv * ‖(a : ℂ) - (b : ℂ)‖ * ‖d 1‖ := by
        rw [hKv, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hL]
        exact mul_le_mul_of_nonneg_left hLd (mul_nonneg hSnn (norm_nonneg _))
      have heq : tmap d n (a : ℂ) - tmap d n (b : ℂ)
          = ((d 0 + ∑ k ∈ Finset.Icc 2 n, d k * (b : ℂ) ^ k)
              - (d 0 + ∑ k ∈ Finset.Icc 2 n, d k * (a : ℂ) ^ k)) / d 1 := by
        unfold tmap
        field_simp <;> ring
      have hd : dist (tmap d n (a : ℂ)) (tmap d n (b : ℂ)) ≤ Kv * dist (a : ℂ) (b : ℂ) := by
        rw [dist_eq_norm, dist_eq_norm, heq, norm_div, div_le_iff₀ hd1n]
        exact hnum.trans hstep
      -- `dist` on the subtype, `MapsTo.restrict`, and `↑⟨Kv, _⟩` are all `rfl`
      exact hd
  obtain ⟨w, hws, hwfix, -, -⟩ :=
    hcontract.exists_fixedPoint' hsc hmaps ((hmem 0).2 (by simpa using hr.le))
      (edist_ne_top _ _)
  refine ⟨w, (hmem w).1 hws, ?_⟩
  have hfix : tmap d n w = w := hwfix
  unfold tmap at hfix
  rw [div_eq_iff hd1] at hfix
  linear_combination -hfix

/-- The same conclusion with the polynomial written over `Finset.range (n+1)`, which is the shape
a caller has after expanding a polynomial about a point.  The split is done with `Finset.ext` and
`omega` rather than interval lemmas, so it depends on nothing fragile. -/
theorem exists_root_of_contraction' (d : ℕ → ℂ) (U : ℕ → ℝ) (L r : ℝ) (n : ℕ)
    (hn : 2 ≤ n) (hr : 0 < r) (hL : 0 < L) (hLd : L ≤ ‖d 1‖) (hU : ∀ k ≤ n, ‖d k‖ ≤ U k)
    (hself : U 0 + ∑ k ∈ Finset.Icc 2 n, U k * r ^ k ≤ L * r)
    (hlip : ∑ k ∈ Finset.Icc 2 n, (k : ℝ) * U k * r ^ (k - 1) < L) :
    ∃ w : ℂ, ‖w‖ ≤ r ∧ ∑ k ∈ Finset.range (n + 1), d k * w ^ k = 0 := by
  obtain ⟨w, hw, heq⟩ := exists_root_of_contraction d U L r n hr hL hLd hU hself hlip
  refine ⟨w, hw, ?_⟩
  have hset : Finset.range (n + 1) = insert 0 (insert 1 (Finset.Icc 2 n)) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h0 : (0 : ℕ) ∉ insert 1 (Finset.Icc 2 n) := by
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  have h1 : (1 : ℕ) ∉ Finset.Icc 2 n := by
    simp only [Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_insert h0, Finset.sum_insert h1]
  linear_combination heq

/-- Transport a disk root back to the original variable: if the disk has radius `r` and its
centre has real part greater than `r`, every point of the disk lies in the open right half-plane.
This is the step that turns a root certificate into a refutation of Hurwitz stability. -/
theorem re_pos_of_norm_le (c w : ℂ) (r : ℝ) (hw : ‖w‖ ≤ r) (hc : r < c.re) : 0 < (c + w).re := by
  have h1 : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
  have h2 : -‖w‖ ≤ w.re := (abs_le.mp h1).1
  rw [Complex.add_re]
  linarith

end Principia.MathDB.RootCert
