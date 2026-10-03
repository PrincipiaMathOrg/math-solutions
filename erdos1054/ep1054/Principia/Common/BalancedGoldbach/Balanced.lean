/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.BalancedGoldbach.Variance
import Principia.Common.SW.Unconditional

/-!
# Balanced Goldbach: almost every even number is `p + q` with primes `3 < p < q < 3p`

`BalRep n` says `n = p + q` for primes `3 < p < q < 3p` (so both summands lie in `(n/4, 3n/4)`).
The headline is

* `balanced_goldbach : DensityZero notBalanced` — the even `n` with no such representation have
  density zero (the port's `GoldbachReduction.DensityZero`: rational `ε`, count over `0 ≤ n ≤ X`),
  **unconditionally**; `balanced_goldbach_of_mediumPNT` is the same from `MediumPNTBound`.

## How the restriction is obtained without a new circle method

For a window length `N`, every pair `(a, b) ∈ [0, N)²` with `a + b = n` has `a, b > n − N`. If
`4N ≤ 3n` (`InWindow`), then `a, b > n/4`, so the smaller is `> n/4` and the larger is `< 3n/4`,
which is `< 3 ×` the smaller: every off-diagonal prime pair counted by `R_N(n)` is balanced
(`balRep_of_pair`). If also `4n + 4 ≤ 7N`, the kernel count `r_N(n) ≥ 2N − 1 − n ≥ N/4`
(`kernel_ge`), so the main term `𝔖(n) r_N(n) ≥ N/16` for even `n` (`mainTermN_ge`, from
`𝔖(n) ≥ 1/4`). An `n` in the window with no balanced representation has `R_N(n)` supported on the
diagonal and on proper prime powers (`pairWeight_le_of_noPair`), hence `R_N(n) ≤ N/32`; the
variance `variance_upper` then bounds their number by `ε N` (`window_bad_card`, Chebyshev).
Four windows (`N = ⌊X/3⌋, ⌊2X/5⌋, ⌊X/2⌋, ⌊3X/5⌋`) cover the dyadic block `(X/2, X]`
(`window_cover`), and `GoldbachReduction.densityZero_of_block` sums the blocks.
-/

set_option autoImplicit false

open DirichletCharacter Complex PowerSeries ArithmeticFunction Finset Filter Metric MeasureTheory
open Principia.Common.SW (MediumPNTBound)

namespace Principia.Common.BalancedGoldbach

open Principia.Common.Goldbach
open Principia.Common.Goldbach.MajorArcMainTerm
open Principia.Common.Goldbach.GoldbachReduction
open scoped ArithmeticFunction

/-- `n = p + q` with primes `3 < p < q < 3p`: a **balanced** Goldbach representation (both
summands in `(n/4, 3n/4)`). -/
def BalRep (n : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 3 < p ∧ p < q ∧ q < 3 * p ∧ n = p + q

/-- `n` is even and has no balanced Goldbach representation. -/
def notBalanced (n : ℕ) : Prop := Even n ∧ ¬ BalRep n

/-- The balanced window of length `N`: `4N ≤ 3n` and `4n + 4 ≤ 7N`. -/
def InWindow (N n : ℕ) : Prop := 4 * N ≤ 3 * n ∧ 4 * n + 4 ≤ 7 * N

/-- **Every off-diagonal prime pair of the window count is balanced.** If `a, b < N`,
`a + b = n`, `4N ≤ 3n` and `N ≥ 9`, then the smaller of `a, b` exceeds `3` and the larger is less
than three times the smaller. -/
theorem balRep_of_pair {N n a b : ℕ} (hN : 9 ≤ N) (hw : InWindow N n) (ha : a < N) (hb : b < N)
    (hab : a + b = n) (hne : a ≠ b) (hpa : a.Prime) (hpb : b.Prime) : BalRep n := by
  obtain ⟨h1, -⟩ := hw
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨a, b, hpa, hpb, by omega, h, by omega, hab.symm⟩
  · exact ⟨b, a, hpb, hpa, by omega, h, by omega, by omega⟩

/-- **The kernel count on the upper half**: `r_N(n) ≥ 2N − 1 − n` for `n ≥ N` (the pairs
`(a, n − a)`, `n − N < a < N`). -/
theorem kernel_ge (N n : ℕ) (hn : N ≤ n) : ((2 * N - 1 - n : ℕ) : ℝ) ≤ kernel N n := by
  unfold kernel
  have h : (Finset.Ioo (n - N) N).card
      ≤ ((Finset.range N ×ˢ Finset.range N).filter (fun pr => pr.1 + pr.2 = n)).card := by
    apply Finset.card_le_card_of_injOn (fun a => (a, n - a))
    · intro a ha
      simp only [Finset.coe_Ioo, Set.mem_Ioo] at ha
      simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_setOf_eq]
      omega
    · intro a _ b _ hab
      simp only [Prod.mk.injEq] at hab
      exact hab.1
  rw [Nat.card_Ioo] at h
  have h2 : 2 * N - 1 - n ≤ N - (n - N) - 1 := by omega
  exact_mod_cast h2.trans h

/-- **The main term on the window**: `𝔖(n) r_N(n) ≥ N/16` for even `n` in the window
(`𝔖(n) ≥ 1/4` by `singSeries_ge`, `r_N(n) ≥ N/4` by `kernel_ge`). -/
theorem mainTermN_ge {N n : ℕ} (hw : InWindow N n) (he : Even n) (hn1 : 1 ≤ n) :
    (N : ℝ) / 16 ≤ mainTermN N n := by
  obtain ⟨h1, h2⟩ := hw
  have hS : (1 : ℝ) / 4 ≤ ∑' q, Tarithv n q := singSeries_ge n hn1 he
  have hK : (N : ℝ) / 4 ≤ kernel N n := by
    have hk := kernel_ge N n (by omega)
    have h4 : N ≤ 4 * (2 * N - 1 - n) := by omega
    have h4' : (N : ℝ) ≤ 4 * ((2 * N - 1 - n : ℕ) : ℝ) := by exact_mod_cast h4
    linarith
  rw [mainTermN]
  have hN0 : (0 : ℝ) ≤ (N : ℝ) / 4 := by positivity
  calc (N : ℝ) / 16 = (1 / 4) * ((N : ℝ) / 4) := by ring
    _ ≤ (∑' q, Tarithv n q) * kernel N n := mul_le_mul hS hK hN0 (by linarith)

/-- `Λ(m) ≤ log n` for `m ≤ n`, `n ≥ 1`. -/
theorem vonMangoldt_le_log_of_le {m n : ℕ} (hmn : m ≤ n) (hn : 1 ≤ n) : Λ m ≤ Real.log n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [ArithmeticFunction.map_zero]
    exact Real.log_nonneg (by exact_mod_cast hn)
  · exact le_trans ArithmeticFunction.vonMangoldt_le_log
      (Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast hmn))

/-- **The window count of an `n` with no off-diagonal prime pair is negligible.** If no
`a ≠ b < N` with `a + b = n` are both prime, `R_N(n)` is carried by the diagonal `a = b = n/2`
(one term, `≤ log² n`) and by pairs containing a proper prime power (`GoldbachReduction.badRep_le`'s
argument): `R_N(n) ≤ 2 log² n · √n (log₂ n + 1) + log² n`. -/
theorem pairWeight_le_of_noPair (N n : ℕ) (hn : 1 ≤ n)
    (hno : ∀ a b : ℕ, a < N → b < N → a + b = n → a ≠ b → a.Prime → b.Prime → False) :
    pairWeight N n
      ≤ 2 * Real.log n ^ 2 * ((Nat.sqrt n : ℝ) * (Nat.log 2 n + 1)) + Real.log n ^ 2 := by
  classical
  set F := (Finset.range N ×ˢ Finset.range N).filter (fun pr => pr.1 + pr.2 = n) with hF
  set PP := (Finset.Ioc 0 n).filter (fun m => ¬ m.Prime ∧ Λ m ≠ 0) with hPP
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hmemF : ∀ pr ∈ F, pr.1 < N ∧ pr.2 < N ∧ pr.1 + pr.2 = n := by
    intro pr hpr
    rw [hF, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hpr
    exact ⟨hpr.1.1, hpr.1.2, hpr.2⟩
  have hterm : ∀ pr ∈ F, Λ pr.1 * Λ pr.2 ≤ Real.log n ^ 2 := by
    intro pr hpr
    obtain ⟨-, -, hs⟩ := hmemF pr hpr
    have h1 : Λ pr.1 ≤ Real.log n := vonMangoldt_le_log_of_le (by omega) hn
    have h2 : Λ pr.2 ≤ Real.log n := vonMangoldt_le_log_of_le (by omega) hn
    calc Λ pr.1 * Λ pr.2 ≤ Real.log n * Real.log n :=
          mul_le_mul h1 h2 ArithmeticFunction.vonMangoldt_nonneg hlogn
      _ = Real.log n ^ 2 := (sq (Real.log n)).symm
  set D := F.filter (fun pr => pr.1 = pr.2) with hD
  set G := F.filter (fun pr => ¬ pr.1 = pr.2) with hG
  have hsplit : pairWeight N n = ∑ pr ∈ D, Λ pr.1 * Λ pr.2 + ∑ pr ∈ G, Λ pr.1 * Λ pr.2 := by
    rw [hD, hG, Finset.sum_filter_add_sum_filter_not]
    rfl
  -- the diagonal: at most the one pair `(n/2, n/2)`
  have hDcard : D.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    rw [hD, Finset.mem_filter] at hx hy
    obtain ⟨-, -, hsx⟩ := hmemF x hx.1
    obtain ⟨-, -, hsy⟩ := hmemF y hy.1
    have hx2 := hx.2
    have hy2 := hy.2
    ext <;> omega
  have hDsum : ∑ pr ∈ D, Λ pr.1 * Λ pr.2 ≤ Real.log n ^ 2 := by
    calc ∑ pr ∈ D, Λ pr.1 * Λ pr.2 ≤ ∑ _pr ∈ D, Real.log n ^ 2 :=
          Finset.sum_le_sum fun pr hpr => hterm pr (Finset.mem_of_mem_filter pr hpr)
      _ = (D.card : ℝ) * Real.log n ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * Real.log n ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hDcard
      _ = Real.log n ^ 2 := one_mul _
  -- the off-diagonal: every nonzero term contains a proper prime power
  set G' := G.filter (fun pr => Λ pr.1 * Λ pr.2 ≠ 0) with hG'
  have hmem : ∀ pr ∈ G', pr.1 < N ∧ pr.2 < N ∧ pr.1 + pr.2 = n ∧ pr.1 ≠ pr.2 ∧
      Λ pr.1 ≠ 0 ∧ Λ pr.2 ≠ 0 := by
    intro pr hpr
    rw [hG', Finset.mem_filter] at hpr
    obtain ⟨hprG, hne⟩ := hpr
    rw [hG, Finset.mem_filter] at hprG
    obtain ⟨h1, h2, h3⟩ := hmemF pr hprG.1
    exact ⟨h1, h2, h3, hprG.2, fun h => hne (by rw [h, zero_mul]),
      fun h => hne (by rw [h, mul_zero])⟩
  have hsplitG : ∑ pr ∈ G', Λ pr.1 * Λ pr.2
      = (∑ pr ∈ G'.filter (fun pr => pr.1.Prime), Λ pr.1 * Λ pr.2)
        + ∑ pr ∈ G'.filter (fun pr => ¬ pr.1.Prime), Λ pr.1 * Λ pr.2 :=
    (Finset.sum_filter_add_sum_filter_not G' _ _).symm
  have hcardA : (G'.filter (fun pr => ¬ pr.1.Prime)).card ≤ PP.card := by
    apply Finset.card_le_card_of_injOn (fun pr => pr.1)
    · intro pr hpr
      simp only [Finset.mem_coe, Finset.mem_filter] at hpr
      obtain ⟨hprG', hnp⟩ := hpr
      obtain ⟨-, -, hsum, -, h1, -⟩ := hmem pr hprG'
      have h1le : 2 ≤ pr.1 := (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h1).two_le
      simp only [Finset.mem_coe, hPP, Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨by omega, by omega⟩, hnp, h1⟩
    · intro p1 hp1 p2 hp2 heq
      simp only [Finset.mem_coe, Finset.mem_filter] at hp1 hp2
      obtain ⟨-, -, hs1, -⟩ := hmem p1 hp1.1
      obtain ⟨-, -, hs2, -⟩ := hmem p2 hp2.1
      dsimp only at heq
      have : p1.2 = p2.2 := by omega
      exact Prod.ext heq this
  have hcardB : (G'.filter (fun pr => pr.1.Prime)).card ≤ PP.card := by
    apply Finset.card_le_card_of_injOn (fun pr => pr.2)
    · intro pr hpr
      simp only [Finset.mem_coe, Finset.mem_filter] at hpr
      obtain ⟨hprG', hp1⟩ := hpr
      obtain ⟨hlt1, hlt2, hsum, hne, -, h2⟩ := hmem pr hprG'
      have h2le : 2 ≤ pr.2 := (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h2).two_le
      have hnp2 : ¬ pr.2.Prime := fun hp2 => hno pr.1 pr.2 hlt1 hlt2 hsum hne hp1 hp2
      simp only [Finset.mem_coe, hPP, Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨by omega, by omega⟩, hnp2, h2⟩
    · intro p1 hp1 p2 hp2 heq
      simp only [Finset.mem_coe, Finset.mem_filter] at hp1 hp2
      obtain ⟨-, -, hs1, -⟩ := hmem p1 hp1.1
      obtain ⟨-, -, hs2, -⟩ := hmem p2 hp2.1
      dsimp only at heq
      have : p1.1 = p2.1 := by omega
      exact Prod.ext this heq
  have hG'F : ∀ pr ∈ G', pr ∈ F := fun pr hpr =>
    Finset.mem_of_mem_filter pr (Finset.mem_of_mem_filter pr hpr)
  have hboundA : ∑ pr ∈ G'.filter (fun pr => ¬ pr.1.Prime), Λ pr.1 * Λ pr.2
      ≤ (PP.card : ℝ) * Real.log n ^ 2 := by
    calc ∑ pr ∈ G'.filter (fun pr => ¬ pr.1.Prime), Λ pr.1 * Λ pr.2
        ≤ ∑ _pr ∈ G'.filter (fun pr => ¬ pr.1.Prime), Real.log n ^ 2 :=
          Finset.sum_le_sum fun pr hpr => hterm pr (hG'F pr (Finset.mem_of_mem_filter pr hpr))
      _ = ((G'.filter (fun pr => ¬ pr.1.Prime)).card : ℝ) * Real.log n ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (PP.card : ℝ) * Real.log n ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hcardA
  have hboundB : ∑ pr ∈ G'.filter (fun pr => pr.1.Prime), Λ pr.1 * Λ pr.2
      ≤ (PP.card : ℝ) * Real.log n ^ 2 := by
    calc ∑ pr ∈ G'.filter (fun pr => pr.1.Prime), Λ pr.1 * Λ pr.2
        ≤ ∑ _pr ∈ G'.filter (fun pr => pr.1.Prime), Real.log n ^ 2 :=
          Finset.sum_le_sum fun pr hpr => hterm pr (hG'F pr (Finset.mem_of_mem_filter pr hpr))
      _ = ((G'.filter (fun pr => pr.1.Prime)).card : ℝ) * Real.log n ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (PP.card : ℝ) * Real.log n ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hcardB
  have hPPbound := card_properPrimePow_le n
  rw [← hPP] at hPPbound
  have hGsum : ∑ pr ∈ G, Λ pr.1 * Λ pr.2
      ≤ 2 * Real.log n ^ 2 * ((Nat.sqrt n : ℝ) * (Nat.log 2 n + 1)) := by
    calc ∑ pr ∈ G, Λ pr.1 * Λ pr.2
        = ∑ pr ∈ G', Λ pr.1 * Λ pr.2 := (Finset.sum_filter_ne_zero G).symm
      _ = (∑ pr ∈ G'.filter (fun pr => pr.1.Prime), Λ pr.1 * Λ pr.2)
          + ∑ pr ∈ G'.filter (fun pr => ¬ pr.1.Prime), Λ pr.1 * Λ pr.2 := hsplitG
      _ ≤ (PP.card : ℝ) * Real.log n ^ 2 + (PP.card : ℝ) * Real.log n ^ 2 :=
          add_le_add hboundB hboundA
      _ = 2 * Real.log n ^ 2 * (PP.card : ℝ) := by ring
      _ ≤ 2 * Real.log n ^ 2 * ((Nat.sqrt n : ℝ) * (Nat.log 2 n + 1)) :=
          mul_le_mul_of_nonneg_left hPPbound (by positivity)
  rw [hsplit]
  linarith

open Classical in
/-- **The balanced exceptions in one window are few.** For every `ε > 0` and all large `N`, at
most `ε N` even `n` in the window of length `N` have no balanced representation. -/
theorem window_bad_card (hPNT : MediumPNTBound) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (((Finset.Ioo N (2 * N)).filter
        (fun n => InWindow N n ∧ Even n ∧ ¬ BalRep n)).card : ℝ) ≤ ε * N := by
  classical
  obtain ⟨N₁, hvar⟩ := variance_upper hPNT (ε / 1024) (by positivity)
  obtain ⟨X₁, hnegl⟩ := negl_bound (1 / 64) (by norm_num)
  refine ⟨max 9 (max N₁ X₁), fun N hN => ?_⟩
  have hN9 : 9 ≤ N := le_trans (le_max_left _ _) hN
  have hNv : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNX : X₁ ≤ 2 * N := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
    omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set B := (Finset.Ioo N (2 * N)).filter (fun n => InWindow N n ∧ Even n ∧ ¬ BalRep n) with hBdef
  have hB : ∀ n ∈ B, (N : ℝ) / 32 ≤ |pairWeight N n - mainTermN N n| := by
    intro n hn
    rw [hBdef, Finset.mem_filter, Finset.mem_Ioo] at hn
    obtain ⟨⟨hn1, hn2⟩, hw, he, hnb⟩ := hn
    have hn1' : 1 ≤ n := by omega
    have hno : ∀ a b : ℕ, a < N → b < N → a + b = n → a ≠ b → a.Prime → b.Prime → False :=
      fun a b ha hb hab hne hpa hpb => hnb (balRep_of_pair hN9 hw ha hb hab hne hpa hpb)
    have hpw := pairWeight_le_of_noPair N n hn1' hno
    have hng := hnegl (2 * N) hNX n (by omega) (by omega)
    have hcast : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
    rw [hcast] at hng
    have hs : (1 : ℝ) ≤ (Nat.sqrt n : ℝ) := by exact_mod_cast Nat.sqrt_pos.mpr (by omega)
    have hl : (1 : ℝ) ≤ (Nat.log 2 n : ℝ) + 1 := by
      have := (Nat.cast_nonneg (Nat.log 2 n) : (0 : ℝ) ≤ _)
      linarith
    have hprod : (1 : ℝ) ≤ (Nat.sqrt n : ℝ) * ((Nat.log 2 n : ℝ) + 1) := by nlinarith
    have hlog2 : Real.log n ^ 2
        ≤ 2 * Real.log n ^ 2 * ((Nat.sqrt n : ℝ) * ((Nat.log 2 n : ℝ) + 1)) := by
      nlinarith [sq_nonneg (Real.log n)]
    have hpwle : pairWeight N n ≤ (N : ℝ) / 32 := by linarith
    have hmain := mainTermN_ge hw he hn1'
    rw [abs_sub_comm]
    calc (N : ℝ) / 32 ≤ mainTermN N n - pairWeight N n := by linarith
      _ ≤ |mainTermN N n - pairWeight N n| := le_abs_self _
  have hcard := card_bad_le_of_sq_sum (Finset.Ioo N (2 * N))
    (fun n => pairWeight N n - mainTermN N n) ((N : ℝ) / 32) (ε / 1024 * (N : ℝ) ^ 3)
    (by positivity) B (Finset.filter_subset _ _) hB (hvar N hNv)
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have h' : (B.card : ℝ) * (N : ℝ) ^ 2 ≤ (ε * N) * (N : ℝ) ^ 2 := by nlinarith
  exact le_of_mul_le_mul_right h' hN2

/-- **Four windows cover a dyadic block.** For `X ≥ 200`, every `n ∈ (X/2, X]` lies in the window
of one of `N = ⌊X/3⌋, ⌊2X/5⌋, ⌊X/2⌋, ⌊3X/5⌋`, and then `N < n < 2N`. -/
theorem window_cover {X n : ℕ} (hX : 200 ≤ X) (h1 : X / 2 < n) (h2 : n ≤ X) :
    (X / 3 < n ∧ n < 2 * (X / 3) ∧ InWindow (X / 3) n) ∨
    (2 * X / 5 < n ∧ n < 2 * (2 * X / 5) ∧ InWindow (2 * X / 5) n) ∨
    (X / 2 < n ∧ n < 2 * (X / 2) ∧ InWindow (X / 2) n) ∨
    (3 * X / 5 < n ∧ n < 2 * (3 * X / 5) ∧ InWindow (3 * X / 5) n) := by
  unfold InWindow
  omega

open Classical in
/-- **The dyadic-block bound.** For every `ε > 0`, eventually
`#{n ∈ (X/2, X] : n even, no balanced representation} ≤ ε X`. -/
theorem block_bad_card (hPNT : MediumPNTBound) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (((Finset.Ioc (X / 2) X).filter notBalanced).card : ℝ) ≤ ε * X := by
  obtain ⟨N₀, hN₀⟩ := window_bad_card hPNT (ε / 4) (by positivity)
  refine ⟨max 200 (3 * N₀ + 3), fun X hX => ?_⟩
  have hX200 : 200 ≤ X := le_trans (le_max_left _ _) hX
  have hXN : 3 * N₀ + 3 ≤ X := le_trans (le_max_right _ _) hX
  set W : ℕ → Finset ℕ := fun N =>
    (Finset.Ioo N (2 * N)).filter (fun n => InWindow N n ∧ Even n ∧ ¬ BalRep n) with hW
  have hWb : ∀ N : ℕ, N₀ ≤ N → N ≤ X → ((W N).card : ℝ) ≤ ε / 4 * X := by
    intro N hN hNX
    have h := hN₀ N hN
    have hNX' : (N : ℝ) ≤ X := by exact_mod_cast hNX
    have : ε / 4 * (N : ℝ) ≤ ε / 4 * X := mul_le_mul_of_nonneg_left hNX' (by positivity)
    exact le_trans h this
  have hsub : (Finset.Ioc (X / 2) X).filter notBalanced
      ⊆ ((W (X / 3) ∪ W (2 * X / 5)) ∪ W (X / 2)) ∪ W (3 * X / 5) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨h1, h2⟩, hb⟩ := hn
    simp only [hW, Finset.mem_union, Finset.mem_filter, Finset.mem_Ioo]
    rcases window_cover hX200 h1 h2 with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl ⟨⟨h.1, h.2.1⟩, h.2.2, hb⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨⟨h.1, h.2.1⟩, h.2.2, hb⟩))
    · exact Or.inl (Or.inr ⟨⟨h.1, h.2.1⟩, h.2.2, hb⟩)
    · exact Or.inr ⟨⟨h.1, h.2.1⟩, h.2.2, hb⟩
  have hc := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le ((W (X / 3) ∪ W (2 * X / 5)) ∪ W (X / 2)) (W (3 * X / 5))
  have hu2 := Finset.card_union_le (W (X / 3) ∪ W (2 * X / 5)) (W (X / 2))
  have hu3 := Finset.card_union_le (W (X / 3)) (W (2 * X / 5))
  have b1 := hWb (X / 3) (by omega) (by omega)
  have b2 := hWb (2 * X / 5) (by omega) (by omega)
  have b3 := hWb (X / 2) (by omega) (by omega)
  have b4 := hWb (3 * X / 5) (by omega) (by omega)
  have htot : ((Finset.Ioc (X / 2) X).filter notBalanced).card
      ≤ (W (X / 3)).card + (W (2 * X / 5)).card + (W (X / 2)).card + (W (3 * X / 5)).card := by
    omega
  have htot' : (((Finset.Ioc (X / 2) X).filter notBalanced).card : ℝ)
      ≤ ((W (X / 3)).card : ℝ) + ((W (2 * X / 5)).card : ℝ) + ((W (X / 2)).card : ℝ)
        + ((W (3 * X / 5)).card : ℝ) := by exact_mod_cast htot
  linarith

/-- **Almost-all balanced Goldbach, from the explicit prime number theorem.** -/
theorem balanced_goldbach_of_mediumPNT (hPNT : MediumPNTBound) : DensityZero notBalanced := by
  classical
  have hR := densityZero_of_block notBalanced (block_bad_card hPNT)
  intro ε hε
  obtain ⟨X₀, hX₀⟩ := hR (ε : ℝ) (by exact_mod_cast hε)
  refine ⟨X₀, fun X hX => ?_⟩
  have hb := hX₀ X hX
  rw [countUpTo]
  have hcast : ((((Finset.range (X + 1)).filter notBalanced).card : ℚ) : ℝ) ≤ (ε : ℝ) * X := by
    push_cast
    exact hb
  have hq : (((Finset.range (X + 1)).filter notBalanced).card : ℚ) ≤ ε * X := by
    exact_mod_cast hcast
  simpa using hq

/-- **Almost-all balanced Goldbach, unconditionally.** The even numbers `n` that are not `p + q`
with primes `3 < p < q < 3p` have density zero. `MediumPNTBound` is discharged by the ported
explicit prime number theorem (`Principia.Common.SW.mediumPNTBound`). -/
theorem balanced_goldbach : DensityZero notBalanced :=
  balanced_goldbach_of_mediumPNT Principia.Common.SW.mediumPNTBound

end Principia.Common.BalancedGoldbach
