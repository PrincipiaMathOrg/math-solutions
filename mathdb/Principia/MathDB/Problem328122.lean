import Mathlib

/-!
# MathDB #328122 — common zeros of centrohermitian Toeplitz pencils satisfy `z_j = conj(z_{n−j})`

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/328122/solution.tex`, proving Conjecture 3.2 of Y. Xu (the reality
conjecture of Alexandersson–Shapiro): for `A ∈ ℂ^{m×(m+n)}` Toeplitz (`A_{ij} = a_{j−i}`) and
centrohermitian (`A_{ij} = conj(A_{m−1−i, m+n−1−j})`), every common zero `z ∈ ℂ^{n+1}` of the `m×m`
minors of `B(z) = A + ∑ z_k I_k` satisfies `z_j = conj(z_{n−j})`.

**What is proved.**  `reality`, with the source's hypotheses (all `m × m` minors of `B(z)` vanish),
for all `m, n`.

**Route (the write-up's).**  Vanishing minors give a nonzero `c` with `∑ᵢ cᵢ B_{ij} = 0`
(`exists_left_null`: otherwise the rows are independent, the rank is `m`, and `m` independent
columns give an invertible `m × m` submatrix).  With `v = conj c`, weighting the column equations
by `v` gives the linear system `b_j + ∑ₖ z_k H_{jk} = 0` (`system`), where `H_{jk} = ∑_{i,l}
conj(vᵢ) v_l [l + j = i + k]` and `b_j = ∑_{i,l} conj(vᵢ) a_{l+j−i} v_l`. Both have the
conjugate-reversal symmetry (`H_symm`, `b_symm`, the latter from centrohermitian symmetry `a_q =
conj(a_{n−q})`), so `J conj z` solves the same system.  The difference `d` satisfies `∑_{j,k}
conj(d_j) d_k H_{jk} = ∑_t |W_t|² = 0` with `W_t = ∑_{j+l=t} conj(d_j) v_l` (`quad_form`), and the
triangular structure at the first nonzero entry of `v` forces `d = 0` (`d_zero`).
-/

namespace Principia.MathDB.P328122

open Finset ComplexConjugate

/-! ### The core algebra, with `ℕ`-indexed data -/

section Core

variable (m n : ℕ) (a : ℤ → ℂ) (z v : ℕ → ℂ)

/-- `H_{jk} = ∑_{i,l < m} conj(vᵢ) v_l [l + j = i + k]`. -/
noncomputable def H (j k : ℕ) : ℂ :=
  ∑ i ∈ range m, ∑ l ∈ range m, conj (v i) * v l * (if l + j = i + k then 1 else 0)

/-- `b_j = ∑_{i,l < m} conj(vᵢ) a_{l+j−i} v_l`. -/
noncomputable def bb (j : ℕ) : ℂ :=
  ∑ i ∈ range m, ∑ l ∈ range m, conj (v i) * a ((l : ℤ) + j - i) * v l

/-- The column equations weighted by `v` give `b_j + ∑ₖ z_k H_{jk} = 0`. -/
theorem system
    (hcol : ∀ c, c < m + n → ∑ i ∈ range m, conj (v i) *
      (a ((c : ℤ) - i) + ∑ k ∈ range (n + 1), if c = i + k then z k else 0) = 0)
    (j : ℕ) (hj : j ≤ n) :
    bb m a v j + ∑ k ∈ range (n + 1), z k * H m v j k = 0 := by
  have hsum : ∑ l ∈ range m, v l * (∑ i ∈ range m, conj (v i) *
      (a (((l + j : ℕ) : ℤ) - i)
        + ∑ k ∈ range (n + 1), if l + j = i + k then z k else 0)) = 0 := by
    refine Finset.sum_eq_zero fun l hl => ?_
    rw [Finset.mem_range] at hl
    rw [hcol (l + j) (by omega), mul_zero]
  rw [← hsum]
  unfold bb H
  simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  congr 1
  · conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    push_cast
    ring
  · conv_rhs => rw [Finset.sum_comm]
    conv_rhs => enter [2, i]; rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> ring

/-- `H_{jk} = conj(H_{n−j, n−k})`. -/
theorem H_symm (j k : ℕ) (hj : j ≤ n) (hk : k ≤ n) :
    H m v j k = conj (H m v (n - j) (n - k)) := by
  unfold H
  simp only [map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  by_cases h1 : i + j = l + k <;> by_cases h2 : l + (n - j) = i + (n - k) <;>
    simp only [h1, h2, if_true, if_false, map_one, map_zero, mul_one, mul_zero] <;>
    first | ring1 | (exfalso; omega)

/-- `b_j = conj(b_{n−j})`, from `a_q = conj(a_{n−q})`. -/
theorem b_symm (ha : ∀ q : ℤ, -(m : ℤ) < q → q < m + n → a q = conj (a (n - q)))
    (j : ℕ) (hj : j ≤ n) : bb m a v j = conj (bb m a v (n - j)) := by
  unfold bb
  simp only [map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun l hl => ?_
  rw [Finset.mem_range] at hi hl
  have hq := ha ((i : ℤ) + j - l) (by omega) (by omega)
  rw [hq, show (n : ℤ) - ((i : ℤ) + j - l) = (l : ℤ) + ((n - j : ℕ) : ℤ) - i by
    rw [Nat.cast_sub hj]; ring]
  ring

/-- The conjugate-reversed vector solves the same system. -/
theorem system_conj
    (ha : ∀ q : ℤ, -(m : ℤ) < q → q < m + n → a q = conj (a (n - q)))
    (hsys : ∀ j, j ≤ n → bb m a v j + ∑ k ∈ range (n + 1), z k * H m v j k = 0)
    (j : ℕ) (hj : j ≤ n) :
    bb m a v j + ∑ k ∈ range (n + 1), conj (z (n - k)) * H m v j k = 0 := by
  have h := congrArg conj (hsys (n - j) (by omega))
  simp only [map_add, map_sum, map_mul, map_zero] at h
  rw [← b_symm m n a v ha j hj] at h
  rw [← h]
  congr 1
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  try dsimp only
  rw [show n + 1 - 1 - k = n - k by omega, H_symm m n v j (n - k) hj (by omega),
    show n - (n - k) = k by omega]

/-- The quadratic form of `H` is a sum of squared moduli. -/
theorem quad_form (d : ℕ → ℂ) (hv0 : ∀ l, m ≤ l → v l = 0) :
    ∑ j ∈ range (n + 1), conj (d j) * ∑ k ∈ range (n + 1), d k * H m v j k
      = ∑ t ∈ range (m + n), (∑ j ∈ range (n + 1), ∑ l ∈ range m,
          if l + j = t then conj (d j) * v l else 0)
        * conj (∑ j ∈ range (n + 1), ∑ l ∈ range m, if l + j = t then conj (d j) * v l else 0) := by
  unfold H
  simp only [Finset.mul_sum]
  have key : ∀ j ∈ range (n + 1), ∀ k ∈ range (n + 1), ∀ i ∈ range m, ∀ l ∈ range m,
      conj (d j) * (d k * (conj (v i) * v l * (if l + j = i + k then 1 else 0)))
        = ∑ t ∈ range (m + n), (if l + j = t then conj (d j) * v l else 0)
          * conj (if i + k = t then conj (d k) * v i else 0) := by
    intro j hj k hk i hi l hl
    rw [Finset.mem_range] at hj hk hi hl
    rw [Finset.sum_eq_single (l + j)]
    · by_cases h : l + j = i + k
      · rw [if_pos h, if_pos rfl, if_pos h.symm]
        simp only [map_mul, Complex.conj_conj]
        ring
      · rw [if_neg h, if_pos rfl, if_neg (fun h' => h h'.symm)]
        simp
    · intro t _ ht
      rw [if_neg (fun h => ht h.symm), zero_mul]
    · intro ht
      exact absurd (Finset.mem_range.2 (by omega)) ht
  rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk =>
    Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun l hl => key j hj k hk i hi l hl]
  -- move `t` to the front: `(j,k,i,l,t)` to `(t,j,k,i,l)`
  conv_lhs => enter [2, j, 2, k, 2, i]; rw [Finset.sum_comm]
  conv_lhs => enter [2, j, 2, k]; rw [Finset.sum_comm]
  conv_lhs => enter [2, j]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [map_sum]
  rw [Finset.sum_mul_sum]
  simp only [Finset.sum_mul_sum]
  conv_lhs => enter [2, j, 2, k]; rw [Finset.sum_comm]

/-- If `∑ₖ d_k H_{jk} = 0` for all `j ≤ n` and `v ≠ 0`, then `d_k = 0` for all `k ≤ n`. -/
theorem d_zero (d : ℕ → ℂ) (hv0 : ∀ l, m ≤ l → v l = 0) (hv : ∃ l, v l ≠ 0)
    (hd : ∀ j, j ≤ n → ∑ k ∈ range (n + 1), d k * H m v j k = 0) :
    ∀ s, s ≤ n → d s = 0 := by
  classical
  set W : ℕ → ℂ := fun t => ∑ j ∈ range (n + 1), ∑ l ∈ range m,
    if l + j = t then conj (d j) * v l else 0 with hW
  have hq := quad_form m n v d hv0
  have hzero : ∑ j ∈ range (n + 1), conj (d j) * ∑ k ∈ range (n + 1), d k * H m v j k = 0 :=
    Finset.sum_eq_zero fun j hj => by
      rw [Finset.mem_range] at hj
      rw [hd j (by omega), mul_zero]
  rw [hzero] at hq
  have hW0 : ∀ t, t < m + n → W t = 0 := by
    have hre : ∑ t ∈ range (m + n), Complex.normSq (W t) = 0 := by
      have := congrArg Complex.re hq
      simp only [Complex.zero_re, Complex.re_sum, Complex.mul_conj, Complex.ofReal_re] at this
      exact this.symm
    intro t ht
    have hnn : ∀ t ∈ range (m + n), 0 ≤ Complex.normSq (W t) := fun t _ => Complex.normSq_nonneg _
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hre t (Finset.mem_range.2 ht)
    exact Complex.normSq_eq_zero.1 this
  -- the first nonzero entry of `v`
  let r := Nat.find hv
  have hr : v r ≠ 0 := Nat.find_spec hv
  have hrlt : ∀ l, l < r → v l = 0 := fun l hl => by
    by_contra h
    exact Nat.find_min hv hl h
  have hrm : r < m := by
    by_contra h
    exact hr (hv0 r (by omega))
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro hs
    have hWs := hW0 (r + s) (by omega)
    have hexp : W (r + s) = conj (d s) * v r := by
      simp only [hW]
      rw [Finset.sum_eq_single s]
      · rw [Finset.sum_eq_single r]
        · rw [if_pos rfl]
        · intro l _ hl
          rw [if_neg (by omega)]
        · intro h
          exact absurd (Finset.mem_range.2 hrm) h
      · intro j hj hjs
        rw [Finset.mem_range] at hj
        refine Finset.sum_eq_zero fun l hl => ?_
        rw [Finset.mem_range] at hl
        split_ifs with h
        · rcases Nat.lt_or_ge j s with hlt | hge
          · rw [ih j hlt (by omega), map_zero, zero_mul]
          · rw [hrlt l (by omega), mul_zero]
        · rfl
      · intro h
        exact absurd (Finset.mem_range.2 (by omega)) h
    rw [hexp] at hWs
    have := (mul_eq_zero.1 hWs).resolve_right hr
    simpa using this

end Core

/-! ### The matrix statement -/

variable {m n : ℕ}

/-- The shift matrix `I_k`: `(I_k)_{ij} = 1` iff `j = i + k`. -/
def shiftMat (m n k : ℕ) : Matrix (Fin m) (Fin (m + n)) ℂ :=
  fun i j => if (j : ℕ) = (i : ℕ) + k then 1 else 0

/-- `B(z) = A + ∑_{k ≤ n} z_k I_k`. -/
noncomputable def pencil (A : Matrix (Fin m) (Fin (m + n)) ℂ) (z : Fin (n + 1) → ℂ) :
    Matrix (Fin m) (Fin (m + n)) ℂ :=
  A + ∑ k : Fin (n + 1), z k • shiftMat m n k

/-- Toeplitz: `A_{ij} = a_{j−i}`. -/
def IsToeplitz (A : Matrix (Fin m) (Fin (m + n)) ℂ) : Prop :=
  ∃ a : ℤ → ℂ, ∀ i j, A i j = a ((j : ℤ) - i)

/-- Centrohermitian: `A_{ij} = conj(A_{m−1−i, m+n−1−j})`. -/
def IsCentrohermitian (A : Matrix (Fin m) (Fin (m + n)) ℂ) : Prop :=
  ∀ i j, A i j = conj (A (Fin.rev i) (Fin.rev j))

/-- Vanishing maximal minors give a nonzero left null vector. -/
theorem exists_left_null (B : Matrix (Fin m) (Fin (m + n)) ℂ)
    (h : ∀ σ : Fin m → Fin (m + n), (B.submatrix id σ).det = 0) :
    ∃ c : Fin m → ℂ, c ≠ 0 ∧ ∀ j, ∑ i, c i * B i j = 0 := by
  by_contra hne
  push_neg at hne
  have hli : LinearIndependent ℂ B.row := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    by_contra hg0
    push_neg at hg0
    have hgne : g ≠ 0 := fun h0 => by
      obtain ⟨i, hi⟩ := hg0
      exact hi (congrFun h0 i)
    obtain ⟨j, hj⟩ := hne g hgne
    apply hj
    have := congrFun hg j
    simpa [Matrix.row, Finset.sum_apply, smul_eq_mul] using this
  have hrank : B.rank = m := by
    rw [hli.rank_matrix, Fintype.card_fin]
  obtain ⟨κ, f, hf, hspan, hind⟩ := exists_linearIndependent' ℂ B.col
  haveI : Finite κ := Finite.of_injective f hf
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = m := by
    have h1 := linearIndependent_iff_card_eq_finrank_span.1 hind
    rw [h1, Set.finrank, hspan, ← Matrix.rank_eq_finrank_span_cols, hrank]
  let e : κ ≃ Fin m := Fintype.equivFinOfCardEq hcard
  have hcols : LinearIndependent ℂ (B.submatrix id (f ∘ e.symm)).col :=
    hind.comp e.symm e.symm.injective
  have hunit := Matrix.linearIndependent_cols_iff_isUnit.1 hcols
  exact (Matrix.isUnit_iff_isUnit_det _).1 hunit |>.ne_zero (h (f ∘ e.symm))

/-- **MathDB #328122 (Xu's Conjecture 3.2).**  For a Toeplitz, centrohermitian `A`, every common
zero `z` of the `m × m` minors of `B(z)` satisfies `z_j = conj(z_{n−j})`. -/
theorem reality (A : Matrix (Fin m) (Fin (m + n)) ℂ) (hT : IsToeplitz A)
    (hC : IsCentrohermitian A) (z : Fin (n + 1) → ℂ)
    (hz : ∀ σ : Fin m → Fin (m + n), ((pencil A z).submatrix id σ).det = 0) :
    ∀ j : Fin (n + 1), z j = conj (z (Fin.rev j)) := by
  obtain ⟨a, ha⟩ := hT
  obtain ⟨c, hc0, hc⟩ := exists_left_null (pencil A z) hz
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      exact absurd (show c = 0 from funext fun i => Fin.elim0 i) hc0
    · exact h
  -- `ℕ`-indexed data
  let zN : ℕ → ℂ := fun k => if h : k < n + 1 then z ⟨k, h⟩ else 0
  let vN : ℕ → ℂ := fun l => if h : l < m then conj (c ⟨l, h⟩) else 0
  have hv0 : ∀ l, m ≤ l → vN l = 0 := fun l hl => by simp [vN, show ¬ l < m by omega]
  have hv : ∃ l, vN l ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hc0
    funext i
    have := hall i
    simpa [vN, i.isLt] using this
  -- centrohermitian symmetry of the coefficients
  have hsymm : ∀ q : ℤ, -(m : ℤ) < q → q < m + n → a q = conj (a (n - q)) := by
    intro q hq1 hq2
    -- realize `q = j − i` with `i < m`, `j < m + n`
    obtain ⟨i, j, hij⟩ : ∃ (i : Fin m) (j : Fin (m + n)), (j : ℤ) - i = q := by
      rcases le_or_gt 0 q with hq | hq
      · refine ⟨⟨0, by omega⟩, ⟨q.toNat, by omega⟩, ?_⟩
        simp only [Nat.cast_zero, sub_zero]
        omega
      · refine ⟨⟨(-q).toNat, by omega⟩, ⟨0, by omega⟩, ?_⟩
        simp only [Nat.cast_zero, zero_sub]
        omega
    have h1 := hC i j
    rw [ha, ha, Fin.val_rev, Fin.val_rev] at h1
    rw [← hij]
    convert h1 using 3
    push_cast [Nat.cast_sub (show (j : ℕ) + 1 ≤ m + n from j.isLt),
      Nat.cast_sub (show (i : ℕ) + 1 ≤ m from i.isLt)]
    ring
  -- the column equations in `ℕ`-indexed form
  have hcol : ∀ col, col < m + n → ∑ i ∈ range m, conj (vN i) *
      (a ((col : ℤ) - i) + ∑ k ∈ range (n + 1), if col = i + k then zN k else 0) = 0 := by
    intro col hcol
    have h := hc ⟨col, hcol⟩
    have e : ∀ i : Fin m, c i * pencil A z i ⟨col, hcol⟩ = conj (vN i) *
        (a ((col : ℤ) - i) + ∑ k ∈ range (n + 1), if col = (i : ℕ) + k then zN k else 0) := by
      intro i
      have hvi : conj (vN i) = c i := by simp [vN, i.isLt]
      have hs : ∑ k ∈ range (n + 1), (if col = (i : ℕ) + k then zN k else 0)
          = ∑ k : Fin (n + 1), z k * (if col = (i : ℕ) + k then 1 else 0) := by
        rw [← Fin.sum_univ_eq_sum_range (fun k => if col = (i : ℕ) + k then zN k else 0) (n + 1)]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [zN, k.isLt, dif_pos, Fin.eta]
        split_ifs <;> simp
      rw [hvi, hs]
      simp [pencil, Matrix.add_apply, Matrix.sum_apply, shiftMat, ha]
    calc ∑ i ∈ range m, conj (vN i) *
          (a ((col : ℤ) - i) + ∑ k ∈ range (n + 1), if col = i + k then zN k else 0)
        = ∑ i : Fin m, conj (vN i) *
          (a ((col : ℤ) - i) + ∑ k ∈ range (n + 1), if col = (i : ℕ) + k then zN k else 0) :=
          (Fin.sum_univ_eq_sum_range (fun i => conj (vN i) *
            (a ((col : ℤ) - i) + ∑ k ∈ range (n + 1), if col = i + k then zN k else 0)) m).symm
      _ = ∑ i : Fin m, c i * pencil A z i ⟨col, hcol⟩ := Finset.sum_congr rfl fun i _ => (e i).symm
      _ = 0 := h
  have hsys := system m n a zN vN hcol
  have hsys' := system_conj m n a zN vN hsymm hsys
  let d : ℕ → ℂ := fun k => zN k - conj (zN (n - k))
  have hd : ∀ j, j ≤ n → ∑ k ∈ range (n + 1), d k * H m vN j k = 0 := by
    intro j hj
    have e1 := hsys j hj
    have e2 := hsys' j hj
    simp only [d, sub_mul, Finset.sum_sub_distrib]
    linear_combination e1 - e2
  have hdz := d_zero m n vN d hv0 hv hd
  intro j
  have hj := j.isLt
  have hj2 : n - (j : ℕ) < n + 1 := by omega
  have := hdz j (by omega)
  simp only [d, zN, hj, hj2, dif_pos] at this
  rw [sub_eq_zero] at this
  have e1 : (⟨(j : ℕ), hj⟩ : Fin (n + 1)) = j := Fin.eta _ _
  have e2 : (⟨n - (j : ℕ), hj2⟩ : Fin (n + 1)) = Fin.rev j := by
    ext
    simp only [Fin.val_rev]
    omega
  rw [e1, e2] at this
  exact this

section Existence

/-! ### The hypothesis class of `reality` is inhabited

`reality` is this row's headline — Xu's Conjecture 3.2 — and it is an implication from
`IsToeplitz A` and `IsCentrohermitian A`.  Nothing exhibited a matrix satisfying both, so it
was at risk of being vacuous; a constant matrix with real entry satisfies both at once.

**What this does not settle.**  Inhabitation only.  A constant matrix is a degenerate instance,
and whether `reality` has instances in which its hypothesis `hz` — that every maximal minor of
the pencil vanishes — holds for an interesting `z` is a separate question, not answered here.
-/

theorem isToeplitz_const (c : ℂ) :
    IsToeplitz (Matrix.of fun _ _ => c : Matrix (Fin m) (Fin (m + n)) ℂ) :=
  ⟨fun _ => c, fun _ _ => rfl⟩

theorem isCentrohermitian_const {c : ℂ} (hc : conj c = c) :
    IsCentrohermitian (Matrix.of fun _ _ => c : Matrix (Fin m) (Fin (m + n)) ℂ) :=
  fun _ _ => hc.symm

/-- **A Toeplitz centrohermitian matrix exists**, so `reality` is not vacuous. -/
theorem exists_toeplitz_centrohermitian :
    ∃ A : Matrix (Fin m) (Fin (m + n)) ℂ, IsToeplitz A ∧ IsCentrohermitian A :=
  ⟨Matrix.of fun _ _ => 1, isToeplitz_const 1, isCentrohermitian_const (map_one _)⟩

end Existence

end Principia.MathDB.P328122
