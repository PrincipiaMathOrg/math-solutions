/-
Lean formalization by Hyunsik Chae, Apache License 2.0 (text: Chae/Pntpp/LICENSE).
Original: https://github.com/hs-chae/erdos1054_hyunsik (commit c065f37), file `Pntpp/DivisorPrefix/GoldbachTail.lean`,
written by Hyunsik Chae for Lean v4.35.0-rc2.
The Lean statements and proofs are his; the mathematical argument they formalize is the
divisor-prefix argument of Jimmy Fraiture (JIF), github.com/jif-perso/erdos_1054 (see CREDITS.md).
Ported to Principia (Lean v4.31.0, Mathlib v4.31.0) by Claude, 2026-10-05.
Changes: import paths `Pntpp.*` -> `Principia.Erdos1054.Chae.Pntpp.*`; `set_option autoImplicit false` and `set_option maxRecDepth 100000` added at file level (his lakefile set both globally)
-/
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.PrimeWindow
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.KernelNumerics

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Pntpp.DivisorPrefix

open Real

private theorem takeWhile_le_eq_filter
    (l : List ℕ) (X : ℕ) (hsorted : l.SortedLT) :
    l.takeWhile (fun d => d ≤ X) = l.filter (fun d => d ≤ X) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have hpair : (a :: l).Pairwise (· < ·) :=
        List.sortedLT_iff_pairwise.mp hsorted
      have htail : l.SortedLT :=
        List.sortedLT_iff_pairwise.mpr (List.pairwise_cons.mp hpair).2
      by_cases ha : a ≤ X
      · simp [ha, ih htail]
      · have hnone : ∀ b ∈ l, X < b := by
          intro b hb
          have hab : a < b := (List.pairwise_cons.mp hpair).1 b hb
          omega
        have hfilterNil : l.filter (fun b => b ≤ X) = [] :=
          List.filter_eq_nil_iff.mpr (by
            intro b hb
            simp [hnone b hb])
        simp [ha, hfilterNil]

private theorem prime_sq_not_dvd_prod
    {p : ℕ} (ps : List ℕ)
    (hp : p.Prime)
    (hprime : ∀ q ∈ ps, q.Prime)
    (hnodup : ps.Nodup)
    (hpMem : p ∈ ps) :
    ¬ p * p ∣ ps.prod := by
  induction ps with
  | nil => simp at hpMem
  | cons a ps ih =>
      rw [List.nodup_cons] at hnodup
      simp only [List.mem_cons] at hpMem
      rcases hpMem with rfl | hpMem
      · intro hsq
        have hpDvd : p ∣ ps.prod :=
          (Nat.mul_dvd_mul_iff_left hp.pos).mp hsq
        exact hnodup.1
          (mem_list_primes_of_dvd_prod hp.prime
            (fun q hq => (hprime q (by simp [hq])).prime) hpDvd)
      · intro hsq
        have haPrime : a.Prime := hprime a (by simp)
        have hpa : p ≠ a := by
          intro hpa
          subst a
          exact hnodup.1 hpMem
        have hpNotDvd : ¬ p ∣ a := by
          simpa [Nat.prime_dvd_prime_iff_eq hp haPrime] using hpa
        have hcop : (p * p).Coprime a := by
          simpa [pow_two] using (hp.coprime_iff_not_dvd.mpr hpNotDvd).pow_left 2
        have htail : p * p ∣ ps.prod := hcop.dvd_of_dvd_mul_left hsq
        exact ih (fun q hq => hprime q (by simp [hq])) hnodup.2 hpMem htail

theorem small_divisor_of_pairwise_large_prime_product
    (ps : List ℕ) (X d : ℕ)
    (hnodup : ps.Nodup)
    (hprime : ∀ p ∈ ps, p.Prime)
    (hpair : ∀ a ∈ ps, ∀ b ∈ ps, a ≠ b → X < a * b)
    (hdvd : d ∣ ps.prod)
    (hdX : d ≤ X) :
    d = 1 ∨ d ∈ ps := by
  have hprod : 0 < ps.prod := List.prod_pos fun p hp => (hprime p hp).pos
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hprod
  by_cases hdOne : d = 1
  · exact Or.inl hdOne
  let p := d.minFac
  have hpPrime : p.Prime := Nat.minFac_prime hdOne
  have hpDvdD : p ∣ d := Nat.minFac_dvd d
  have hpMem : p ∈ ps :=
    mem_list_primes_of_dvd_prod hpPrime.prime
      (fun q hq => (hprime q hq).prime) (hpDvdD.trans hdvd)
  by_cases hdPrime : d = p
  · exact Or.inr (hdPrime ▸ hpMem)
  let e := d / p
  have hpe : p * e = d := Nat.mul_div_cancel' hpDvdD
  have hpLeD : p ≤ d := Nat.le_of_dvd hdpos hpDvdD
  have hePos : 0 < e := Nat.div_pos hpLeD hpPrime.pos
  have heOne : e ≠ 1 := by
    intro he
    apply hdPrime
    simpa [he] using hpe.symm
  let q := e.minFac
  have hqPrime : q.Prime := Nat.minFac_prime heOne
  have hqDvdE : q ∣ e := Nat.minFac_dvd e
  have hpqDvdD : p * q ∣ d := by
    rw [← hpe]
    exact Nat.mul_dvd_mul_left p hqDvdE
  have hqDvdD : q ∣ d := by
    rw [← hpe]
    exact dvd_mul_of_dvd_right hqDvdE p
  have hqMem : q ∈ ps :=
    mem_list_primes_of_dvd_prod hqPrime.prime
      (fun r hr => (hprime r hr).prime) (hqDvdD.trans hdvd)
  have hpqNe : p ≠ q := by
    intro hpq
    exact prime_sq_not_dvd_prod ps hpPrime hprime hnodup hpMem
      (by simpa [hpq] using hpqDvdD.trans hdvd)
  have hpqLeD : p * q ≤ d := Nat.le_of_dvd hdpos hpqDvdD
  have hlarge := hpair p hpMem q hqMem hpqNe
  omega

theorem pairwise_large_prime_prefix
    (ps : List ℕ) (X : ℕ)
    (hsorted : ps.SortedLT)
    (hprime : ∀ p ∈ ps, p.Prime)
    (hupper : ∀ p ∈ ps, p ≤ X)
    (hpair : ∀ a ∈ ps, ∀ b ∈ ps, a ≠ b → X < a * b) :
    (divisorList ps.prod).take (ps.length + 1) = 1 :: ps := by
  by_cases hps : ps = []
  · subst ps
    simp [divisorList]
  have hprod : 0 < ps.prod := List.prod_pos fun p hp => (hprime p hp).pos
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil ps hps
  have hX : 1 ≤ X := (hprime a ha).one_lt.le.trans (hupper a ha)
  let l := divisorList ps.prod
  have hlSorted : l.SortedLT := divisorList_sorted ps.prod
  have htargetSorted : (1 :: ps).SortedLT := by
    rw [List.sortedLT_iff_pairwise]
    exact List.pairwise_cons.mpr
      ⟨fun p hp => (hprime p hp).one_lt, List.sortedLT_iff_pairwise.mp hsorted⟩
  have hfilterSorted : (l.filter (fun d => d ≤ X)).SortedLT :=
    List.sortedLT_iff_pairwise.mpr
      ((List.sortedLT_iff_pairwise.mp hlSorted).filter (fun d => d ≤ X))
  have hfilterNodup : (l.filter (fun d => d ≤ X)).Nodup :=
    (divisorList_nodup ps.prod).filter _
  have htargetNodup : (1 :: ps).Nodup := htargetSorted.nodup
  have hfilterMem :
      ∀ d, d ∈ l.filter (fun e => e ≤ X) ↔ d ∈ 1 :: ps := by
    intro d
    simp only [List.mem_filter, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro ⟨hdl, hdX⟩
      have hdvd : d ∣ ps.prod := (mem_divisorList.mp hdl).1
      exact small_divisor_of_pairwise_large_prime_product ps X d hsorted.nodup
        hprime hpair hdvd hdX
    · rintro (rfl | hdps)
      · exact ⟨mem_divisorList.mpr ⟨one_dvd _, hprod.ne'⟩, hX⟩
      · exact ⟨mem_divisorList.mpr ⟨List.dvd_prod hdps, hprod.ne'⟩,
          hupper d hdps⟩
  have hfilterPerm : List.Perm (l.filter (fun d => d ≤ X)) (1 :: ps) :=
    (List.perm_ext_iff_of_nodup hfilterNodup htargetNodup).2 hfilterMem
  have hfilter : l.filter (fun d => d ≤ X) = 1 :: ps :=
    hfilterPerm.eq_of_pairwise'
      (List.sortedLT_iff_pairwise.mp hfilterSorted)
      (List.sortedLT_iff_pairwise.mp htargetSorted)
  have htakeWhile : l.takeWhile (fun d => d ≤ X) = 1 :: ps := by
    rw [takeWhile_le_eq_filter l X hlSorted, hfilter]
  have hprefix : 1 :: ps <+: l := by
    rw [← htakeWhile]
    exact List.takeWhile_prefix _
  have htake := List.prefix_iff_eq_take.mp hprefix
  simpa [l] using htake.symm

theorem represents_one_add_sum_of_pairwise_large_prime_finset
    (s : Finset ℕ) (X : ℕ)
    (hprime : ∀ p ∈ s, p.Prime)
    (hupper : ∀ p ∈ s, p ≤ X)
    (hpair : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → X < a * b) :
    Represents (1 + ∑ p ∈ s, p) := by
  let ps := s.sort (· ≤ ·)
  have hpsSorted : ps.SortedLT := s.sortedLT_sort
  have hpsPrime : ∀ p ∈ ps, p.Prime := by
    intro p hp
    exact hprime p (by simpa [ps] using hp)
  have hpsUpper : ∀ p ∈ ps, p ≤ X := by
    intro p hp
    exact hupper p (by simpa [ps] using hp)
  have hpsPair : ∀ a ∈ ps, ∀ b ∈ ps, a ≠ b → X < a * b := by
    intro a ha b hb hab
    exact hpair a (by simpa [ps] using ha) b (by simpa [ps] using hb) hab
  have hpsProd : 0 < ps.prod := List.prod_pos fun p hp => (hpsPrime p hp).pos
  have hprefix := pairwise_large_prime_prefix ps X hpsSorted hpsPrime hpsUpper hpsPair
  have hrep := represents_one_add_sum_of_prefix ps hpsProd hprefix
  have hsum : ps.sum = ∑ p ∈ s, p := by
    calc
      ps.sum = s.toList.sum := (Finset.sort_perm_toList s (· ≤ ·)).sum_eq
      _ = ∑ p ∈ s, p := Finset.sum_toList s
  rw [← hsum]
  exact hrep

/-- The lower bound on each prime in the explicit ternary Goldbach input. -/
noncomputable def helfgottPrimeLowerBound (N : ℕ) : ℝ :=
  (N : ℝ) / (30000 * Real.log N)

private lemma monotone_log_ratio_six :
    MonotoneOn (fun y : ℝ => y - 6 * log y) (Set.Ici 6) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 6) ?_ ?_ ?_
  · exact continuousOn_id.sub (continuousOn_const.mul
      (continuousOn_log.mono (by
        intro y hy
        exact ne_of_gt (lt_of_lt_of_le (by norm_num) (Set.mem_Ici.mp hy)))))
  · intro y hy
    rw [interior_Ici] at hy
    refine DifferentiableAt.differentiableWithinAt ?_
    exact ((hasDerivAt_id y).sub
      ((Real.hasDerivAt_log
        (show y ≠ 0 by linarith [Set.mem_Ioi.mp hy])).const_mul 6)).differentiableAt
  · intro y hy
    rw [interior_Ici] at hy
    have hypos : 0 < y := by linarith [Set.mem_Ioi.mp hy]
    have hderiv : deriv (fun y : ℝ => y - 6 * log y) y = 1 - 6 * y⁻¹ :=
      ((hasDerivAt_id y).sub
        ((Real.hasDerivAt_log (show y ≠ 0 by linarith [hypos])).const_mul 6)).deriv
    rw [hderiv]
    have hyge6 : 6 ≤ y := le_of_lt (Set.mem_Ioi.mp hy)
    have hyinv : 6 * y⁻¹ ≤ 1 := by
      have hdiv : 6 / y ≤ 1 := (div_le_iff₀ hypos).2 (by simpa using hyge6)
      simpa [div_eq_mul_inv] using hdiv
    nlinarith

private lemma ratio_six_bound_exp31 (x : ℝ) (h31x : exp 31 ≤ x) :
    exp 31 / (31 : ℝ) ^ 6 ≤ x / log x ^ 6 := by
  have hbase_pos : 0 < exp (31 : ℝ) := exp_pos _
  have hxpos : 0 < x := lt_of_lt_of_le hbase_pos h31x
  have h1x : 1 < x :=
    lt_of_lt_of_le (one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 31)) h31x
  have hlogpos : 0 < log x := log_pos h1x
  have hlogbase_le : (31 : ℝ) ≤ log x := by
    have h := log_le_log hbase_pos h31x
    simpa [log_exp] using h
  have hlogx_ge6 : 6 ≤ log x := by linarith
  have hh : (31 : ℝ) - 6 * log (31 : ℝ) ≤ log x - 6 * log (log x) :=
    monotone_log_ratio_six (Set.mem_Ici.mpr (by norm_num : (6 : ℝ) ≤ 31))
      (Set.mem_Ici.mpr hlogx_ge6) hlogbase_le
  rw [← log_le_log_iff (by positivity) (by positivity)]
  have hleft : log (exp 31 / (31 : ℝ) ^ 6) = (31 : ℝ) - 6 * log (31 : ℝ) := by
    rw [log_div (exp_pos _).ne' (pow_ne_zero _ (by norm_num : (31 : ℝ) ≠ 0)),
      log_exp, log_pow]
    ring
  have hright : log (x / log x ^ 6) = log x - 6 * log (log x) := by
    rw [log_div hxpos.ne' (pow_ne_zero _ hlogpos.ne'), log_pow]
    ring
  linarith

private theorem exp31_ratio_six_ge_30000 :
    (30000 : ℝ) ≤ exp 31 / (31 : ℝ) ^ 6 := by
  exact KernelNumerics.exp31_ratio

private theorem exp31_le_ten_pow_27 :
    exp 31 ≤ (10 ^ 27 : ℝ) := by
  exact KernelNumerics.exp31_upper

private lemma ratio_six_ge_30000 (x : ℝ) (hx : (10 ^ 27 : ℝ) ≤ x) :
    (30000 : ℝ) ≤ x / log x ^ 6 := by
  exact exp31_ratio_six_ge_30000.trans
    (ratio_six_bound_exp31 x (exp31_le_ten_pow_27.trans hx))

private lemma sixty_thousand_log_le_sqrt (x : ℝ) (hx : (10 ^ 27 : ℝ) ≤ x) :
    60000 * log x ≤ sqrt x := by
  have hxExp : exp 31 ≤ x := exp31_le_ten_pow_27.trans hx
  have hxpos : 0 < x := (exp_pos 31).trans_le hxExp
  have hlog31 : (31 : ℝ) ≤ log x := by
    have h := log_le_log (exp_pos 31) hxExp
    simpa using h
  have hlogpos : 0 < log x := by linarith
  have hratio := ratio_six_ge_30000 x hx
  have hscale : 30000 * log x ^ 6 ≤ x :=
    (le_div_iff₀ (pow_pos hlogpos 6)).mp hratio
  have hlog4base : (31 : ℝ) ^ 4 ≤ log x ^ 4 := by
    exact pow_le_pow_left₀ (by norm_num) hlog31 4
  have hlog4 : (120000 : ℝ) ≤ log x ^ 4 := by
    norm_num at hlog4base ⊢
    linarith
  have hlog2nonneg : 0 ≤ log x ^ 2 := sq_nonneg _
  have hmult : 120000 * log x ^ 2 ≤ log x ^ 6 := by
    calc
      120000 * log x ^ 2 ≤ log x ^ 4 * log x ^ 2 :=
        mul_le_mul_of_nonneg_right hlog4 hlog2nonneg
      _ = log x ^ 6 := by ring
  have hsquare : (60000 * log x) ^ 2 ≤ x := by
    calc
      (60000 * log x) ^ 2 = 30000 * (120000 * log x ^ 2) := by ring
      _ ≤ 30000 * log x ^ 6 := by gcongr
      _ ≤ x := hscale
  rw [Real.le_sqrt (by positivity) hxpos.le]
  exact hsquare

private lemma sqrt_add_one_le_helfgott_bound
    (x : ℝ) (hx : (10 ^ 27 : ℝ) ≤ x) :
    sqrt x + 1 ≤ x / (30000 * log x) := by
  have hxpos : 0 < x := by positivity
  have hlogpos : 0 < log x := by
    apply log_pos
    nlinarith [hx]
  have hsqrtOne : 1 ≤ sqrt x := by
    rw [Real.le_sqrt (by norm_num) hxpos.le]
    nlinarith [hx]
  have hsqrtNonneg : 0 ≤ sqrt x := sqrt_nonneg x
  have hsqrtSum : sqrt x + 1 ≤ 2 * sqrt x := by linarith
  have hsixty := sixty_thousand_log_le_sqrt x hx
  apply (le_div_iff₀ (mul_pos (by norm_num) hlogpos)).2
  calc
    (sqrt x + 1) * (30000 * log x)
        ≤ (2 * sqrt x) * (30000 * log x) := by
          gcongr
    _ = (60000 * log x) * sqrt x := by ring
    _ ≤ sqrt x * sqrt x := by gcongr
    _ = x := by simpa [pow_two] using sq_sqrt hxpos.le

private lemma cast_sqrt_succ_le_real_sqrt_add_one (N : ℕ) :
    ((N.sqrt + 1 : ℕ) : ℝ) ≤ sqrt (N : ℝ) + 1 := by
  have hsqrt : (N.sqrt : ℝ) ≤ sqrt (N : ℝ) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    norm_cast
    simpa [pow_two] using Nat.sqrt_le N
  simpa using add_le_add_right hsqrt 1

/-- The exact numerical inequality needed by the even-tail prime-window gadget. -/
def EvenTailWindowMargin : Prop :=
  ∀ N : ℕ,
    10 ^ 27 ≤ N →
    ∃ M : ℕ,
      (M : ℝ) ≤ helfgottPrimeLowerBound N ∧
      N < M * M

theorem evenTailWindowMargin : EvenTailWindowMargin := by
  intro N hN
  refine ⟨N.sqrt + 1, ?_, Nat.lt_succ_sqrt N⟩
  change ((N.sqrt + 1 : ℕ) : ℝ) ≤ (N : ℝ) / (30000 * log (N : ℝ))
  exact (cast_sqrt_succ_le_real_sqrt_add_one N).trans
    (sqrt_add_one_le_helfgott_bound N (by exact_mod_cast hN))

theorem represents_even_tail_of_windowMargin
    (hgoldbach : HelfgottTailHypothesis)
    (hmargin : EvenTailWindowMargin) :
    ∀ n : ℕ, 10 ^ 27 + 1 ≤ n → Even n → Represents n := by
  intro n hn hnEven
  let N := n - 1
  have hN : 10 ^ 27 ≤ N := by
    dsimp [N]
    omega
  have hNOdd : Odd N := by
    exact Nat.Even.sub_odd (by omega) hnEven (by decide)
  obtain ⟨p, q, r, hp, hq, hr, hpOdd, hqOdd, hrOdd,
      hpq, hpr, hqr, hsum, hpLower, hqLower, hrLower⟩ :=
    hgoldbach N hN hNOdd
  obtain ⟨M, hMLower, hMM⟩ := hmargin N hN
  have hMp : M < p := by
    exact_mod_cast hMLower.trans_lt hpLower
  have hMq : M < q := by
    exact_mod_cast hMLower.trans_lt hqLower
  have hMr : M < r := by
    exact_mod_cast hMLower.trans_lt hrLower
  let s : Finset ℕ := {p, q, r}
  have hsPrime : ∀ a ∈ s, a.Prime := by
    intro a ha
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact hp
    · exact hq
    · exact hr
  have hsLower : ∀ a ∈ s, M < a := by
    intro a ha
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact hMp
    · exact hMq
    · exact hMr
  have hsUpper : ∀ a ∈ s, a ≤ N := by
    intro a ha
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;>
      have := hp.pos <;> have := hq.pos <;> have := hr.pos <;> omega
  have hrep :=
    represents_one_add_sum_of_prime_finset s M N hsPrime hsLower hsUpper hMM
  have hsSum : ∑ a ∈ s, a = N := by
    simp [s, hpq, hpr, hqr]
    omega
  rw [hsSum] at hrep
  have htarget : 1 + N = n := by
    dsimp [N]
    omega
  rw [htarget] at hrep
  exact hrep

def ShortLogPrimeHypothesis : Prop :=
  ∀ n : ℕ,
    10 ^ 27 + 10 ^ 8 ≤ n →
    ∃ ell : ℕ,
      ell.Prime ∧
      Odd ell ∧
      60000 * Real.log n < (ell : ℝ) ∧
      (ell : ℝ) < 120000 * Real.log n

theorem shortLogPrimeHypothesis : ShortLogPrimeHypothesis := by
  intro n hn
  let x : ℝ := 60000 * Real.log n
  let k : ℕ := ⌊x⌋₊
  have hnTwo : (2 : ℝ) ≤ n := by
    norm_cast
    omega
  have hlog : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) hnTwo
  have hxTwo : 2 < x := by
    dsimp [x]
    nlinarith [Real.log_two_gt_d9]
  have hxNonneg : 0 ≤ x := hxTwo.le.trans' (by norm_num)
  have hkTwo : 2 ≤ k := by
    apply Nat.le_floor
    exact_mod_cast hxTwo.le
  obtain ⟨ell, hellPrime, hkell, hellUpper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul k (by omega)
  have hellTwo : ell ≠ 2 := by omega
  have hellOdd : Odd ell := hellPrime.odd_of_ne_two hellTwo
  have hellStrictUpper : ell < 2 * k := by
    rcases hellOdd with ⟨j, hj⟩
    omega
  have hxFloor : x < (k : ℝ) + 1 := by
    simpa [k] using Nat.lt_floor_add_one x
  have hkOneEll : k + 1 ≤ ell := by omega
  have hellLower : x < (ell : ℝ) := by
    exact hxFloor.trans_le (by exact_mod_cast hkOneEll)
  have hkLeX : (k : ℝ) ≤ x := by
    simpa [k] using Nat.floor_le hxNonneg
  have hellUpperReal : (ell : ℝ) < 2 * x := by
    have hellCast : (ell : ℝ) < 2 * k := by
      exact_mod_cast hellStrictUpper
    nlinarith
  refine ⟨ell, hellPrime, hellPrime.odd_of_ne_two hellTwo, ?_, ?_⟩
  · simpa [x] using hellLower
  · dsimp [x] at hellUpperReal
    nlinarith

private lemma monotone_sub_120000_log :
    MonotoneOn (fun y : ℝ => y - 120000 * log y) (Set.Ici 120000) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 120000) ?_ ?_ ?_
  · exact continuousOn_id.sub (continuousOn_const.mul
      (continuousOn_log.mono (by
        intro y hy
        exact ne_of_gt (lt_of_lt_of_le (by norm_num) (Set.mem_Ici.mp hy)))))
  · intro y hy
    rw [interior_Ici] at hy
    refine DifferentiableAt.differentiableWithinAt ?_
    exact ((hasDerivAt_id y).sub
      ((Real.hasDerivAt_log
        (show y ≠ 0 by linarith [Set.mem_Ioi.mp hy])).const_mul 120000)).differentiableAt
  · intro y hy
    rw [interior_Ici] at hy
    have hypos : 0 < y := by linarith [Set.mem_Ioi.mp hy]
    have hderiv : deriv (fun y : ℝ => y - 120000 * log y) y =
        1 - 120000 * y⁻¹ :=
      ((hasDerivAt_id y).sub
        ((Real.hasDerivAt_log (show y ≠ 0 by linarith [hypos])).const_mul 120000)).deriv
    rw [hderiv]
    have hyge : (120000 : ℝ) ≤ y := le_of_lt (Set.mem_Ioi.mp hy)
    have hyinv : 120000 * y⁻¹ ≤ 1 := by
      have hdiv : (120000 : ℝ) / y ≤ 1 := (div_le_iff₀ hypos).2 (by simpa using hyge)
      simpa [div_eq_mul_inv] using hdiv
    nlinarith

private theorem track_a_threshold_lt_exp63 :
    (((10 ^ 27 + 10 ^ 8 : ℕ) : ℝ)) < exp 63 := by
  exact_mod_cast KernelNumerics.exp63_lower

private lemma log_linear_gap_at_track_a_threshold
    (x : ℝ) (hx : (((10 ^ 27 + 10 ^ 8 : ℕ) : ℝ)) ≤ x) :
    120000 * log x < x - (10 ^ 27 : ℝ) := by
  let x₀ : ℝ := ((10 ^ 27 + 10 ^ 8 : ℕ) : ℝ)
  have hx₀eq : x₀ = (1000000000000000000100000000 : ℝ) := by
    norm_num [x₀]
  have hx₀pos : 0 < x₀ := by positivity
  have hlogx₀ : log x₀ < 63 :=
    (Real.log_lt_iff_lt_exp hx₀pos).2 (by
      rw [hx₀eq]
      exact track_a_threshold_lt_exp63)
  have hx₀large : (120000 : ℝ) ≤ x₀ := by
    dsimp [x₀]
    norm_num
  have hx₀x : x₀ ≤ x := by
    rw [hx₀eq]
    exact hx
  have hxlarge : (120000 : ℝ) ≤ x := hx₀large.trans hx₀x
  have hmono := monotone_sub_120000_log
    (Set.mem_Ici.mpr hx₀large) (Set.mem_Ici.mpr hxlarge) hx₀x
  dsimp [x₀] at hmono hlogx₀
  norm_num at hmono hlogx₀ ⊢
  nlinarith

private theorem exp60_le_ten_pow_27 :
    exp 60 ≤ (10 ^ 27 : ℝ) := by
  exact KernelNumerics.exp60_upper

private lemma twice_log_window_sq_add_one_lt
    (x : ℝ) (hx : (10 ^ 27 : ℝ) ≤ x) :
    2 * (120000 * log x) ^ 2 + 1 < x := by
  have hxExp : exp 60 ≤ x := exp60_le_ten_pow_27.trans hx
  have hxpos : 0 < x := (exp_pos 60).trans_le hxExp
  have hlog60 : (60 : ℝ) ≤ log x := by
    have h := log_le_log (exp_pos 60) hxExp
    simpa using h
  have hlogpos : 0 < log x := by linarith
  have hscale : 30000 * log x ^ 6 ≤ x :=
    (le_div_iff₀ (pow_pos hlogpos 6)).mp (ratio_six_ge_30000 x hx)
  have hlog4base : (60 : ℝ) ^ 4 ≤ log x ^ 4 :=
    pow_le_pow_left₀ (by norm_num) hlog60 4
  have hlog4 : (960001 : ℝ) ≤ log x ^ 4 := by
    norm_num at hlog4base ⊢
    linarith
  have hlog2one : (1 : ℝ) ≤ log x ^ 2 := by nlinarith
  have hlog2nonneg : 0 ≤ log x ^ 2 := sq_nonneg _
  have hmult : 960001 * log x ^ 2 ≤ log x ^ 6 := by
    calc
      960001 * log x ^ 2 ≤ log x ^ 4 * log x ^ 2 :=
        mul_le_mul_of_nonneg_right hlog4 hlog2nonneg
      _ = log x ^ 6 := by ring
  calc
    2 * (120000 * log x) ^ 2 + 1
        < 28800000001 * log x ^ 2 := by nlinarith
    _ ≤ 30000 * (960001 * log x ^ 2) := by nlinarith
    _ ≤ 30000 * log x ^ 6 := by gcongr
    _ ≤ x := hscale

/-- The exact collection of numerical inequalities needed by the odd-tail divisor-prefix gadget. -/
def OddTailWindowMargin : Prop :=
  ∀ n ell : ℕ,
    10 ^ 27 + 10 ^ 8 ≤ n →
    60000 * Real.log n < (ell : ℝ) →
    (ell : ℝ) < 120000 * Real.log n →
    let N := n - 1 - ell
    10 ^ 27 ≤ N ∧
    ell ≤ N ∧
    ∃ M : ℕ,
      (M : ℝ) ≤ helfgottPrimeLowerBound N ∧
      (ell : ℝ) < helfgottPrimeLowerBound N ∧
      N < M * M ∧
      N < ell * M

theorem oddTailWindowMargin : OddTailWindowMargin := by
  intro n ell hn hellLower hellUpper
  let N := n - 1 - ell
  have hnReal : (((10 ^ 27 + 10 ^ 8 : ℕ) : ℝ)) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hgap := log_linear_gap_at_track_a_threshold n hnReal
  have hellPlus : ell + 10 ^ 27 < n := by
    exact_mod_cast (show (ell : ℝ) + (10 ^ 27 : ℝ) < n by
      nlinarith [hellUpper, hgap])
  have hN : 10 ^ 27 ≤ N := by
    dsimp [N]
    omega
  have hNpos : 0 < N := by omega
  have hnAtLeast : (10 ^ 27 : ℝ) ≤ n := by
    exact_mod_cast (show 10 ^ 27 ≤ n by omega)
  have hlogSquare := twice_log_window_sq_add_one_lt n hnAtLeast
  have hnPos : 0 < (n : ℝ) := by positivity
  have hlognPos : 0 < log (n : ℝ) := log_pos (by exact_mod_cast (show 1 < n by omega))
  have hellPosReal : 0 < (ell : ℝ) := by nlinarith [hellLower]
  have hellSqReal : 2 * (ell : ℝ) ^ 2 + 1 < n := by
    have hellSq : (ell : ℝ) ^ 2 < (120000 * log (n : ℝ)) ^ 2 := by
      nlinarith [sq_nonneg ((ell : ℝ) - 120000 * log (n : ℝ))]
    nlinarith
  have hellSqNat : 2 * (ell * ell) + 1 < n := by
    have hcast : ((2 * (ell * ell) + 1 : ℕ) : ℝ) < (n : ℝ) := by
      norm_num
      simpa [pow_two] using hellSqReal
    exact_mod_cast hcast
  have hellPos : 0 < ell := by exact_mod_cast hellPosReal
  have hellLeSq : ell ≤ ell * ell := by
    calc
      ell = ell * 1 := by simp
      _ ≤ ell * ell := Nat.mul_le_mul_left ell hellPos
  have hellSqN : ell * ell < N := by
    dsimp [N]
    omega
  have hellN : ell ≤ N := by omega
  have hNleN : N ≤ n := by
    dsimp [N]
    omega
  have hlogNn : log (N : ℝ) ≤ log (n : ℝ) := by
    apply log_le_log
    · positivity
    · exact_mod_cast hNleN
  have hlogNPos : 0 < log (N : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsmallDenPos : 0 < 60000 * log (N : ℝ) := mul_pos (by norm_num) hlogNPos
  have hdenPos : 0 < 30000 * log (N : ℝ) := mul_pos (by norm_num) hlogNPos
  have hsmallDenEll : 60000 * log (N : ℝ) < (ell : ℝ) := by
    nlinarith [hellLower]
  let M := N / ell + 1
  have hellMprod : N < ell * M := by
    dsimp [M]
    exact Nat.lt_mul_div_succ N hellPos
  have hellLeDiv : ell ≤ N / ell := by
    apply (Nat.le_div_iff_mul_le hellPos).2
    omega
  have hellM : ell < M := by
    dsimp [M]
    omega
  have hMpos : 0 < M := by
    dsimp [M]
    omega
  have hMM : N < M * M := by
    exact hellMprod.trans ((Nat.mul_lt_mul_right hMpos).2 hellM)
  have hNRealPos : 0 < (N : ℝ) := by positivity
  have hdivCompare :
      (N : ℝ) / ell < (N : ℝ) / (60000 * log (N : ℝ)) := by
    apply (div_lt_div_iff₀ hellPosReal hsmallDenPos).2
    nlinarith
  have hsqrtNLeN : sqrt (N : ℝ) ≤ N := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [show (1 : ℝ) ≤ N by exact_mod_cast (show 1 ≤ N by omega)]
  have hhalfAtLeastOne :
      (1 : ℝ) ≤ (N : ℝ) / (60000 * log (N : ℝ)) := by
    apply (le_div_iff₀ hsmallDenPos).2
    simpa using (sixty_thousand_log_le_sqrt N (by exact_mod_cast hN)).trans hsqrtNLeN
  have hMbound : (M : ℝ) ≤ (N : ℝ) / (30000 * log (N : ℝ)) := by
    calc
      (M : ℝ) = (N / ell : ℕ) + 1 := by simp [M]
      _ ≤ (N : ℝ) / ell + 1 := by
        gcongr
        exact Nat.cast_div_le
      _ ≤ (N : ℝ) / (60000 * log (N : ℝ)) + 1 := by linarith
      _ ≤ 2 * ((N : ℝ) / (60000 * log (N : ℝ))) := by linarith
      _ = (N : ℝ) / (30000 * log (N : ℝ)) := by
        field_simp
        ring
  have hellBound : (ell : ℝ) < (N : ℝ) / (30000 * log (N : ℝ)) := by
    apply (lt_div_iff₀ hdenPos).2
    have hdenEll : 30000 * log (N : ℝ) < (ell : ℝ) := by nlinarith
    have hellSqCast : (ell : ℝ) ^ 2 < N := by
      exact_mod_cast (by simpa [pow_two] using hellSqN)
    nlinarith [mul_lt_mul_of_pos_left hdenEll hellPosReal]
  refine ⟨hN, hellN, M, ?_, ?_, hMM, hellMprod⟩
  · exact hMbound
  · exact hellBound

theorem represents_odd_tail_of_windowMargins
    (hgoldbach : HelfgottTailHypothesis)
    (hshort : ShortLogPrimeHypothesis)
    (hmargin : OddTailWindowMargin) :
    ∀ n : ℕ, 10 ^ 27 + 10 ^ 8 ≤ n → Odd n → Represents n := by
  intro n hn hnOdd
  obtain ⟨ell, hellPrime, hellOdd, hellLower, hellUpper⟩ := hshort n hn
  let N := n - 1 - ell
  obtain ⟨hN, hellN, M, hMLower, hellBound, hMM, hellM⟩ :=
    hmargin n ell hn hellLower hellUpper
  change 10 ^ 27 ≤ N at hN
  change ell ≤ N at hellN
  change (M : ℝ) ≤ helfgottPrimeLowerBound N at hMLower
  change (ell : ℝ) < helfgottPrimeLowerBound N at hellBound
  change N < M * M at hMM
  change N < ell * M at hellM
  have hellPred : ell ≤ n - 1 := by
    dsimp [N] at hellN ⊢
    omega
  have hNOdd : Odd N := by
    have hnPredEven : Even (n - 1) :=
      Nat.Odd.sub_odd hnOdd (show Odd 1 by decide)
    exact Nat.Even.sub_odd hellPred hnPredEven hellOdd
  obtain ⟨p, q, r, hp, hq, hr, hpOdd, hqOdd, hrOdd,
      hpq, hpr, hqr, hsum, hpLower, hqLower, hrLower⟩ :=
    hgoldbach N hN hNOdd
  change helfgottPrimeLowerBound N < (p : ℝ) at hpLower
  change helfgottPrimeLowerBound N < (q : ℝ) at hqLower
  change helfgottPrimeLowerBound N < (r : ℝ) at hrLower
  have hMp : M < p := by
    exact_mod_cast hMLower.trans_lt hpLower
  have hMq : M < q := by
    exact_mod_cast hMLower.trans_lt hqLower
  have hMr : M < r := by
    exact_mod_cast hMLower.trans_lt hrLower
  have hellp : ell < p := by
    exact_mod_cast hellBound.trans hpLower
  have hellq : ell < q := by
    exact_mod_cast hellBound.trans hqLower
  have hellr : ell < r := by
    exact_mod_cast hellBound.trans hrLower
  let s : Finset ℕ := {ell, p, q, r}
  have hsPrime : ∀ a ∈ s, a.Prime := by
    intro a ha
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact hellPrime
    · exact hp
    · exact hq
    · exact hr
  have hsUpper : ∀ a ∈ s, a ≤ N := by
    intro a ha
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact hellN
    · have := hp.pos
      have := hq.pos
      have := hr.pos
      omega
    · have := hp.pos
      have := hq.pos
      have := hr.pos
      omega
    · have := hp.pos
      have := hq.pos
      have := hr.pos
      omega
  have hEllP : N < ell * p := by
    exact hellM.trans ((Nat.mul_lt_mul_left hellPrime.pos).2 hMp)
  have hEllQ : N < ell * q := by
    exact hellM.trans ((Nat.mul_lt_mul_left hellPrime.pos).2 hMq)
  have hEllR : N < ell * r := by
    exact hellM.trans ((Nat.mul_lt_mul_left hellPrime.pos).2 hMr)
  have hMPos : 0 < M := by
    by_contra hM
    have hMZero : M = 0 := Nat.eq_zero_of_not_pos hM
    simp [hMZero] at hMM
  have hPQ : N < p * q := by
    have h1 : M * M < M * p := (Nat.mul_lt_mul_left hMPos).2 hMp
    have h2 : M * p < q * p := (Nat.mul_lt_mul_right hp.pos).2 hMq
    exact hMM.trans (h1.trans (by simpa [Nat.mul_comm] using h2))
  have hPR : N < p * r := by
    have h1 : M * M < M * p := (Nat.mul_lt_mul_left hMPos).2 hMp
    have h2 : M * p < r * p := (Nat.mul_lt_mul_right hp.pos).2 hMr
    exact hMM.trans (h1.trans (by simpa [Nat.mul_comm] using h2))
  have hQR : N < q * r := by
    have h1 : M * M < M * q := (Nat.mul_lt_mul_left hMPos).2 hMq
    have h2 : M * q < r * q := (Nat.mul_lt_mul_right hq.pos).2 hMr
    exact hMM.trans (h1.trans (by simpa [Nat.mul_comm] using h2))
  have hsPair : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → N < a * b := by
    intro a ha b hb hab
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl | rfl
    · rcases hb with rfl | rfl | rfl | rfl
      · exact (hab rfl).elim
      · exact hEllP
      · exact hEllQ
      · exact hEllR
    · rcases hb with rfl | rfl | rfl | rfl
      · simpa [Nat.mul_comm] using hEllP
      · exact (hab rfl).elim
      · exact hPQ
      · exact hPR
    · rcases hb with rfl | rfl | rfl | rfl
      · simpa [Nat.mul_comm] using hEllQ
      · simpa [Nat.mul_comm] using hPQ
      · exact (hab rfl).elim
      · exact hQR
    · rcases hb with rfl | rfl | rfl | rfl
      · simpa [Nat.mul_comm] using hEllR
      · simpa [Nat.mul_comm] using hPR
      · simpa [Nat.mul_comm] using hQR
      · exact (hab rfl).elim
  have hrep :=
    represents_one_add_sum_of_pairwise_large_prime_finset s N hsPrime hsUpper hsPair
  have hsSum : ∑ a ∈ s, a = ell + N := by
    simp [s, hpq, hpr, hqr, hellp.ne, hellq.ne, hellr.ne]
    omega
  rw [hsSum] at hrep
  have htarget : 1 + (ell + N) = n := by
    dsimp [N]
    omega
  rw [htarget] at hrep
  exact hrep

theorem represents_odd_tail_of_windowMargin
    (hgoldbach : HelfgottTailHypothesis)
    (hmargin : OddTailWindowMargin) :
    ∀ n : ℕ, 10 ^ 27 + 10 ^ 8 ≤ n → Odd n → Represents n :=
  represents_odd_tail_of_windowMargins hgoldbach shortLogPrimeHypothesis hmargin

theorem represents_goldbach_tail_of_windowMargins
    (hgoldbach : HelfgottTailHypothesis)
    (hevenMargin : EvenTailWindowMargin)
    (hoddMargin : OddTailWindowMargin) :
    ∀ n : ℕ, 10 ^ 27 + 10 ^ 8 ≤ n → Represents n := by
  intro n hn
  rcases Nat.even_or_odd n with hnEven | hnOdd
  · exact represents_even_tail_of_windowMargin hgoldbach hevenMargin n (by omega) hnEven
  · exact represents_odd_tail_of_windowMargin hgoldbach hoddMargin n hn hnOdd

theorem represents_goldbach_tail
    (hgoldbach : HelfgottTailHypothesis) :
    ∀ n : ℕ, 10 ^ 27 + 10 ^ 8 ≤ n → Represents n :=
  represents_goldbach_tail_of_windowMargins hgoldbach
    evenTailWindowMargin oddTailWindowMargin

end Pntpp.DivisorPrefix
