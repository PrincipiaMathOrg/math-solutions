import Mathlib

/-!
# MathDB #357503 — Yuster's Conjecture 3.9 is FALSE

Write-up `mathdb-open-problems/problems/357503/solution.tex`,
*Four roots of Yuster's entropy polynomial at k = 50*, 18 September 2026.

Conjecture 3.9 asserts that every `p_k` has at most two roots in `(0,1)`, counting
multiplicity.  At `k = 50` it has at least four.  With

`S(x) = (1 − x⁵⁰)/(1 − x)`,  `B(x) = (1 − (1−x)⁵⁰)/x`,  `H(y) = ∑_{j<50} a_j yʲ`,

the write-up's Lemma gives `p₅₀(x) = B(x)S(x)⁵⁰ − α·2500·H(x⁵⁰)` (the sign `(−1)ᵏ` is `+1`
since `k` is even), where `α` is the unique positive root of `α(1+α)⁴⁹ = 1`.

`alpha_lower`/`alpha_upper` bracket `α ∈ (59/1000, 3/50)` from the two integer inequalities
`59·1059⁴⁹ < 1000⁵⁰` and `3·53⁴⁹ > 50⁵⁰`, using only that `t ↦ t(1+t)⁴⁹` is increasing.
Those bounds turn each sign question into an exact rational inequality: `p > 0` needs
`B S⁵⁰ > 150 H`, and `p < 0` needs `2 B S⁵⁰ < 295 H`.

The signs at `1/100, 1/4, 1/2, 3/5, 99/100` are `− + − + −`, and the
intermediate value theorem then gives a root in each of four disjoint intervals.

## Scope

This refutes the ROOT-COUNT conjecture.  The write-up notes the associated entropy
inequality was already proved by Ho and is untouched here.  `S` and `B` are used in their
closed forms, valid on `(0,1)` where the denominators `1−x` and `x` are nonzero — which is
also why the sign points avoid the endpoints.

Checked in Python before formalizing: all fifty `a_j > 0`; both integer inequalities; and
each of the five bound-form inequalities in exactly the shape proved below.
-/

namespace Principia.MathDB.P357503

open Set

/-- `S(x) = (1 − x⁵⁰)/(1 − x)`, the closed form valid off `x = 1`. -/
noncomputable def Sv (x : ℝ) : ℝ := (1 - x ^ 50) / (1 - x)

/-- `B(x) = (1 − (1−x)⁵⁰)/x`, valid off `x = 0`. -/
noncomputable def Bv (x : ℝ) : ℝ := (1 - (1 - x) ^ 50) / x

/-- `H(y) = ∑_{j<50} a_j yʲ` with `a_j = ∑_v (−1)ᵛ C(50,v) C(50(j−v)+49, 49)`, all positive. -/
noncomputable def Hv (y : ℝ) : ℝ :=
  1 + 50445672272782096667406248578 * y
    + 6709553634055027151107639960272792819205 * y ^ 2
    + 113464259003129748197270644391045776107891745832 * y ^ 3
    + 26950167319672027846257698322267403737237089219357909 * y ^ 4
    + 517441067907091253614907072185595679322784061911586816026 * y ^ 5
    + 1870791904592276373484210165929090311852015911013126758541583 * y ^ 6
    + 2035287605618206859728976594436702259236269859798011202504524940 * y ^ 7
    + 884754905815048416617974323253493165845600779229983368404690725672 * y ^ 8
    + 184568049704508750179187521442187527344249022198221791848957048706729 * y ^ 9
    + 20929071120397909959277654126077337426250863147060140733024220596764256 * y ^ 10
    + 1409379778173090809261538143997723018814216996371114194146775024012415403 * y ^ 11
    + 60148189685283959226122041210983149817673412911148043053657497243337977850 * y ^ 12
    + 1708659784108364575413066612203342608643304603296079298397666176221547816547 * y ^ 13
    + 33557241520162399005513514431973384739203452319893075503045146579449398456444 * y ^ 14
    + 469392916345143913887615236520944899271705811914105998232793403859448131254521 * y ^ 15
    + 4788273334941702705707178738875636929046694888229435686824364170372521569691053 * y ^ 16
    + 36303412958309564763740165984760454326105895102137914597526755906004784218224760 * y ^ 17
    + 207715053539434627175404984629611362297506067476793698858003710245919688658049842 * y ^ 18
    + 907960543849998511637023088173195604952196323797529473806764150542396768960352124 * y ^ 19
    + 3061934827530413535240661522682054288834474610584204684420149071741196050130750916 * y ^ 20
    + 8027779447052971525605852990301778686720980884148769743508793646503611545426196368 * y ^ 21
    + 16459433042115358383181961606410184213329513137126290720168677961231889037624968870 * y ^ 22
    + 26503217964265732520699240844451604194581872709540610341502241880483463925339350372 * y ^ 23
    + 33608204684969029458784255339943725297821316349792862290799253008947860331148244199 * y ^ 24
    + 33608204684969029458784255339943725297821316349792862290799253008947860331148244199 * y ^ 25
    + 26503217964265732520699240844451604194581872709540610341502241880483463925339350372 * y ^ 26
    + 16459433042115358383181961606410184213329513137126290720168677961231889037624968870 * y ^ 27
    + 8027779447052971525605852990301778686720980884148769743508793646503611545426196368 * y ^ 28
    + 3061934827530413535240661522682054288834474610584204684420149071741196050130750916 * y ^ 29
    + 907960543849998511637023088173195604952196323797529473806764150542396768960352124 * y ^ 30
    + 207715053539434627175404984629611362297506067476793698858003710245919688658049842 * y ^ 31
    + 36303412958309564763740165984760454326105895102137914597526755906004784218224760 * y ^ 32
    + 4788273334941702705707178738875636929046694888229435686824364170372521569691053 * y ^ 33
    + 469392916345143913887615236520944899271705811914105998232793403859448131254521 * y ^ 34
    + 33557241520162399005513514431973384739203452319893075503045146579449398456444 * y ^ 35
    + 1708659784108364575413066612203342608643304603296079298397666176221547816547 * y ^ 36
    + 60148189685283959226122041210983149817673412911148043053657497243337977850 * y ^ 37
    + 1409379778173090809261538143997723018814216996371114194146775024012415403 * y ^ 38
    + 20929071120397909959277654126077337426250863147060140733024220596764256 * y ^ 39
    + 184568049704508750179187521442187527344249022198221791848957048706729 * y ^ 40
    + 884754905815048416617974323253493165845600779229983368404690725672 * y ^ 41
    + 2035287605618206859728976594436702259236269859798011202504524940 * y ^ 42
    + 1870791904592276373484210165929090311852015911013126758541583 * y ^ 43
    + 517441067907091253614907072185595679322784061911586816026 * y ^ 44
    + 26950167319672027846257698322267403737237089219357909 * y ^ 45
    + 113464259003129748197270644391045776107891745832 * y ^ 46
    + 6709553634055027151107639960272792819205 * y ^ 47
    + 50445672272782096667406248578 * y ^ 48 + 1 * y ^ 49

/-- `p₅₀` in the write-up's normalization, as a function of `α`. -/
noncomputable def Pv (a x : ℝ) : ℝ := Bv x * Sv x ^ 50 - a * 2500 * Hv (x ^ 50)

/-- The five sign points, all interior to `(0,1)`. -/
noncomputable def pta : ℝ := (1 / 100 : ℝ)
noncomputable def ptb : ℝ := (1 / 4 : ℝ)
noncomputable def ptc : ℝ := (1 / 2 : ℝ)
noncomputable def ptd : ℝ := (3 / 5 : ℝ)
noncomputable def pte : ℝ := (99 / 100 : ℝ)

theorem Hpos_a : 0 < Hv (pta ^ 50) := by norm_num [Hv, pta]

theorem Hpos_b : 0 < Hv (ptb ^ 50) := by norm_num [Hv, ptb]

theorem Hpos_c : 0 < Hv (ptc ^ 50) := by norm_num [Hv, ptc]

theorem Hpos_d : 0 < Hv (ptd ^ 50) := by norm_num [Hv, ptd]

theorem Hpos_e : 0 < Hv (pte ^ 50) := by norm_num [Hv, pte]

theorem key_a : 2 * (Bv pta * Sv pta ^ 50) < 295 * Hv (pta ^ 50) := by
  norm_num [Bv, Sv, Hv, pta]

theorem key_b : 150 * Hv (ptb ^ 50) < Bv ptb * Sv ptb ^ 50 := by
  norm_num [Bv, Sv, Hv, ptb]

theorem key_c : 2 * (Bv ptc * Sv ptc ^ 50) < 295 * Hv (ptc ^ 50) := by
  norm_num [Bv, Sv, Hv, ptc]

theorem key_d : 150 * Hv (ptd ^ 50) < Bv ptd * Sv ptd ^ 50 := by
  norm_num [Bv, Sv, Hv, ptd]

theorem key_e : 2 * (Bv pte * Sv pte ^ 50) < 295 * Hv (pte ^ 50) := by
  norm_num [Bv, Sv, Hv, pte]

/-- `α > 59/1000`, since `t(1+t)⁴⁹` is increasing and `59·1059⁴⁹ < 1000⁵⁰`. -/
theorem alpha_lower (a : ℝ) (ha : 0 < a) (heq : a * (1 + a) ^ 49 = 1) : 59 / 1000 < a := by
  by_contra hc
  push_neg at hc
  have h1 : a * (1 + a) ^ 49 ≤ (59 / 1000) * (1 + 59 / 1000 : ℝ) ^ 49 := by
    have : (1 + a) ^ 49 ≤ (1 + 59 / 1000 : ℝ) ^ 49 := by gcongr <;> linarith
    nlinarith [pow_nonneg (by linarith : (0:ℝ) ≤ 1 + a) 49]
  rw [heq] at h1
  have hnum : (59 / 1000 : ℝ) * (1 + 59 / 1000) ^ 49 < 1 := by norm_num
  linarith

/-- `α < 3/50`, since `3·53⁴⁹ > 50⁵⁰`. -/
theorem alpha_upper (a : ℝ) (ha : 0 < a) (heq : a * (1 + a) ^ 49 = 1) : a < 3 / 50 := by
  by_contra hc
  push_neg at hc
  have h1 : (3 / 50 : ℝ) * (1 + 3 / 50) ^ 49 ≤ a * (1 + a) ^ 49 := by
    have : (1 + 3 / 50 : ℝ) ^ 49 ≤ (1 + a) ^ 49 := by gcongr <;> linarith
    nlinarith [pow_nonneg (by linarith : (0:ℝ) ≤ 1 + 3/50) 49]
  rw [heq] at h1
  have hnum : (1 : ℝ) < 3 / 50 * (1 + 3 / 50) ^ 49 := by norm_num
  linarith

/-- `p₅₀(1 / 100) < 0`: `B S⁵⁰ < 147.5 H ≤ α·2500·H`, as `α > 59/1000`. -/
theorem P_a (a : ℝ) (hlo : 59 / 1000 < a) : Pv a (1 / 100) < 0 := by
  have hk := key_a
  have hp := Hpos_a
  simp only [pta] at hk hp
  unfold Pv
  nlinarith [hk, hp, hlo]

/-- `p₅₀(1 / 4) > 0`: `α·2500·H < 150 H < B S⁵⁰`, as `α < 3/50`. -/
theorem P_b (a : ℝ) (hhi : a < 3 / 50) : 0 < Pv a (1 / 4) := by
  have hk := key_b
  have hp := Hpos_b
  simp only [ptb] at hk hp
  unfold Pv
  nlinarith [hk, hp, hhi]

/-- `p₅₀(1 / 2) < 0`: `B S⁵⁰ < 147.5 H ≤ α·2500·H`, as `α > 59/1000`. -/
theorem P_c (a : ℝ) (hlo : 59 / 1000 < a) : Pv a (1 / 2) < 0 := by
  have hk := key_c
  have hp := Hpos_c
  simp only [ptc] at hk hp
  unfold Pv
  nlinarith [hk, hp, hlo]

/-- `p₅₀(3 / 5) > 0`: `α·2500·H < 150 H < B S⁵⁰`, as `α < 3/50`. -/
theorem P_d (a : ℝ) (hhi : a < 3 / 50) : 0 < Pv a (3 / 5) := by
  have hk := key_d
  have hp := Hpos_d
  simp only [ptd] at hk hp
  unfold Pv
  nlinarith [hk, hp, hhi]

/-- `p₅₀(99 / 100) < 0`: `B S⁵⁰ < 147.5 H ≤ α·2500·H`, as `α > 59/1000`. -/
theorem P_e (a : ℝ) (hlo : 59 / 1000 < a) : Pv a (99 / 100) < 0 := by
  have hk := key_e
  have hp := Hpos_e
  simp only [pte] at hk hp
  unfold Pv
  nlinarith [hk, hp, hlo]

/-- `Pv a` is continuous on `[1/100, 99/100]`: the closed forms divide by `1 − x` and `x`,
both nonzero there — which is also why the sign points avoid `0` and `1`. -/
theorem Pv_cont (a : ℝ) : ContinuousOn (Pv a) (Set.Icc (1 / 100 : ℝ) (99 / 100)) := by
  unfold Pv Bv Sv Hv
  apply ContinuousOn.sub
  · apply ContinuousOn.mul
    · exact ContinuousOn.div (by fun_prop) (by fun_prop)
        (fun x hx => by simp only [Set.mem_Icc] at hx; linarith [hx.1])
    · exact ContinuousOn.pow (ContinuousOn.div (by fun_prop) (by fun_prop)
        (fun x hx => by simp only [Set.mem_Icc] at hx; linarith [hx.2])) 50
  · exact ContinuousOn.mul (by fun_prop) (by fun_prop)

/-- **MathDB #357503 — Yuster's Conjecture 3.9 is FALSE.**  For the unique positive `α` with
`α(1+α)⁴⁹ = 1`, `p₅₀` has a root in each of four disjoint subintervals of `(0,1)` — so at least
four roots there, not at most two. -/
theorem main (a : ℝ) (ha : 0 < a) (heq : a * (1 + a) ^ 49 = 1) :
    (∃ x ∈ Set.Ioo (1 / 100 : ℝ) (1 / 4), Pv a x = 0) ∧
      (∃ x ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2), Pv a x = 0) ∧
      (∃ x ∈ Set.Ioo (1 / 2 : ℝ) (3 / 5), Pv a x = 0) ∧
      (∃ x ∈ Set.Ioo (3 / 5 : ℝ) (99 / 100), Pv a x = 0) := by
  have hlo := alpha_lower a ha heq
  have hhi := alpha_upper a ha heq
  have hc := Pv_cont a
  have h1 := P_a a hlo
  have h2 := P_b a hhi
  have h3 := P_c a hlo
  have h4 := P_d a hhi
  have h5 := P_e a hlo
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hs : Set.Icc (1 / 100 : ℝ) (1 / 4) ⊆ Set.Icc (1 / 100 : ℝ) (99 / 100) :=
      Set.Icc_subset_Icc le_rfl (by norm_num)
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo (by norm_num : (1 / 100 : ℝ) ≤ 1 / 4)
      (hc.mono hs) (Set.mem_Ioo.mpr ⟨h1, h2⟩)
    exact ⟨x, hx, hfx⟩
  · have hs : Set.Icc (1 / 4 : ℝ) (1 / 2) ⊆ Set.Icc (1 / 100 : ℝ) (99 / 100) :=
      Set.Icc_subset_Icc (by norm_num) (by norm_num)
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo' (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)
      (hc.mono hs) (Set.mem_Ioo.mpr ⟨h3, h2⟩)
    exact ⟨x, hx, hfx⟩
  · have hs : Set.Icc (1 / 2 : ℝ) (3 / 5) ⊆ Set.Icc (1 / 100 : ℝ) (99 / 100) :=
      Set.Icc_subset_Icc (by norm_num) (by norm_num)
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo (by norm_num : (1 / 2 : ℝ) ≤ 3 / 5)
      (hc.mono hs) (Set.mem_Ioo.mpr ⟨h3, h4⟩)
    exact ⟨x, hx, hfx⟩
  · have hs : Set.Icc (3 / 5 : ℝ) (99 / 100) ⊆ Set.Icc (1 / 100 : ℝ) (99 / 100) :=
      Set.Icc_subset_Icc (by norm_num) le_rfl
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo' (by norm_num : (3 / 5 : ℝ) ≤ 99 / 100)
      (hc.mono hs) (Set.mem_Ioo.mpr ⟨h5, h4⟩)
    exact ⟨x, hx, hfx⟩

end Principia.MathDB.P357503
