/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIIOwedSplit

set_option autoImplicit false

/-!
# Three of the five `prop:kraken` bounds PROVED from the large sieve; `Procida2` split

`T2X.kraken_of` splits `T2S.Kraken` into `Garn1b`, `Garn1a`, `Gargamel`, `Procida2`, `Procida3`.
The book's proofs of `eq:garn1b`, `eq:gargamel`, `eq:procida3` and of the `1`-branch of
`eq:procida2` (`typeII.tex` 1251-1323, through `lem:ogor`/`lem:kastor2`) use ONE analytic input:
the large sieve in its sharp `N − 1 + δ⁻¹` form. With it named (`LargeSieve`, a published
theorem), they are proved here.

```
 LargeSieve    NAMED literature: Montgomery–Vaughan 1974 Cor. 1 (= Selberg; IK Thm 7.7)
 ls_sep        any ν-spaced set, 0 < ν ≤ 1 (one point: Cauchy–Schwarz)          PROVED
 block_bd      ∑_{m∈t} |∑_{W'<p≤W} log p e(mpα)|² ≤ (W − W' + ν⁻¹)∑(log p)²    PROVED
 sep_core      ‖j(a/q + d)‖ ≥ ν  (q ∤ ja ⇒ ≥ 1/q − |jd|; q ∣ j ⇒ = |jd|)        PROVED
 sum_blocks    blocks of length B: (L/B + 1)·(per-block bound)                  PROVED
 gargamel_holds   Gargamel   one block, ν = (1 − x/4Wq)/q                        PROVED
 garn1b_holds     Garn1b     blocks of 2K, K = min(q, ⌈Q/2⌉), ν = 1/2q          PROVED
 procida3_holds   Procida3   blocks of 2(Q' − q), Q' = x/|δ|q, ν = q|δ|/x         PROVED
 procida2_ls      Procida2's large-sieve half (one block)                        PROVED
 Procida2Mont     Procida2's Montgomery half (the log branch of the min)         OPEN
 procida2_of      Procida2 ← LargeSieve + Procida2Mont                           PROVED
 kraken_of_ls     Kraken ← LargeSieve + Garn1a + Procida2Mont                    PROVED
```

So `T2S.Kraken` now owes exactly `Garn1a` (Montgomery's inequality + MV's weighted large sieve +
MV Lemma 8) and `Procida2Mont` (Montgomery's inequality), beside the literature `LargeSieve`.

**Notes.**
* The m-points are `α_m = mα`, `m ∈ T2S.mSet` (odd); two of them differ by `j(2α) = j(a/q + δ/x)`
  with `m − m' = 2j`, which is where `sep_core` is applied. `eq:garn1b`'s `max(1, 2ρ)` comes from
  `q ≤ K·max(1, 2ρ)` (`K = q`, or `K = ⌈Q/2⌉ ≥ Q/2 ≥ q/2ρ`).
* `Procida2Mont` is stated with `eq:procida2`'s hypotheses exactly. The book's proof of that branch
  (`lem:ogor`) applies Montgomery's inequality at `R = (q(ν + υ))^{-1/2}`, which needs `p ∤ r` for
  squarefree `r ≤ R` against primes `p > W'`, i.e. `R ≤ W'`; nothing forces this when `|δ|` is
  small. On `R > W'` the branch's right side exceeds `2cW²/(4 log(W/2))·∑(log p)²`
  (`c = q + x/4W`), above the trivial Cauchy–Schwarz bound `#m·(W/2 + 1)·∑(log p)²`; so the link
  is believed TRUE, but its proof needs that case split.
-/

namespace Principia.Common.TernaryGoldbach.T2K

open Principia.Common.Goldbach
open Principia.Common.TernaryGoldbach.T2S Principia.Common.TernaryGoldbach.T2X

/-- **NAMED (literature) — the large sieve, sharp form** (Montgomery–Vaughan, *Hilbert's
inequality*, J. London Math. Soc. (2) 8 (1974), 73-82, Corollary 1; also Selberg; Iwaniec–Kowalski,
*Analytic Number Theory*, Theorem 7.7; cited by the book as `[MV74]`/`\cite{MR0337775}` in
`lem:ogor`): for `δ`-spaced points `‖β_r − β_s‖ ≥ δ` (`r ≠ s`) and any complex `b_n`,
`∑_r |∑_{M<n≤M+N} b_n e(nβ_r)|² ≤ (N − 1 + δ⁻¹)∑|b_n|²`. Stated here WEAKER: `0 < δ ≤ 1/2`,
`M ≥ 0`, points indexed by a finite set of naturals. -/
def LargeSieve : Prop :=
  ∀ (R : Finset ℕ) (β : ℕ → ℝ) (δ : ℝ), 0 < δ → δ ≤ 1 / 2 →
    (∀ r ∈ R, ∀ s ∈ R, r ≠ s → ∀ n : ℤ, δ ≤ |β r - β s - n|) →
    ∀ (M N : ℕ) (b : ℕ → ℂ),
      ∑ r ∈ R, ‖∑ n ∈ Finset.Ioc M (M + N), b n * e (n * β r)‖ ^ 2 ≤
        ((N : ℝ) - 1 + δ⁻¹) * ∑ n ∈ Finset.Ioc M (M + N), ‖b n‖ ^ 2

/-- The prime weight `b_n = 1_{n prime} log n`. -/
noncomputable def bP (n : ℕ) : ℂ := if n.Prime then ((Real.log n : ℝ) : ℂ) else 0

/-- The prime range of `pS`/`pSq` as an `Ioc` of naturals. -/
theorem filter_eq (W' W : ℝ) (hW' : 0 ≤ W') :
    (Finset.Icc 1 ⌊W⌋₊).filter (fun p : ℕ => p.Prime ∧ W' < (p : ℝ)) =
      (Finset.Ioc ⌊W'⌋₊ (⌊W'⌋₊ + (⌊W⌋₊ - ⌊W'⌋₊))).filter Nat.Prime := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  rw [← Nat.floor_lt hW']
  constructor
  · rintro ⟨⟨_, h2⟩, hp, h3⟩
    exact ⟨⟨h3, by omega⟩, hp⟩
  · rintro ⟨⟨h3, h2⟩, hp⟩
    exact ⟨⟨by omega, by omega⟩, hp, h3⟩

/-- `pS` as a sum of `bP n · e(n·mα)` over that `Ioc`. -/
theorem pS_eq (α W' W : ℝ) (hW' : 0 ≤ W') (m : ℕ) :
    pS α W' W m = ∑ n ∈ Finset.Ioc ⌊W'⌋₊ (⌊W'⌋₊ + (⌊W⌋₊ - ⌊W'⌋₊)),
      bP n * e (n * ((m : ℝ) * α)) := by
  unfold pS bP
  rw [filter_eq W' W hW', Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs
  · congr 2
    push_cast
    ring
  · simp

/-- `pSq` as `∑ ‖bP n‖²` over that `Ioc`. -/
theorem pSq_eq (W' W : ℝ) (hW' : 0 ≤ W') :
    pSq W' W = ∑ n ∈ Finset.Ioc ⌊W'⌋₊ (⌊W'⌋₊ + (⌊W⌋₊ - ⌊W'⌋₊)), ‖bP n‖ ^ 2 := by
  unfold pSq bP
  rw [filter_eq W' W hW', Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  · simp

/-- Cauchy–Schwarz for one frequency. -/
theorem one_bd (M N : ℕ) (b : ℕ → ℂ) (β : ℝ) :
    ‖∑ n ∈ Finset.Ioc M (M + N), b n * e (n * β)‖ ^ 2 ≤
      (N : ℝ) * ∑ n ∈ Finset.Ioc M (M + N), ‖b n‖ ^ 2 := by
  have h1 : ‖∑ n ∈ Finset.Ioc M (M + N), b n * e (n * β)‖ ≤
      ∑ n ∈ Finset.Ioc M (M + N), ‖b n‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_))
    rw [norm_mul, e_norm, mul_one]
  have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.Ioc M (M + N)) (f := fun n => ‖b n‖)
  simp only [Nat.card_Ioc, add_tsub_cancel_left] at h2
  calc ‖∑ n ∈ Finset.Ioc M (M + N), b n * e (n * β)‖ ^ 2
      ≤ (∑ n ∈ Finset.Ioc M (M + N), ‖b n‖) ^ 2 := by gcongr
    _ ≤ _ := h2

/-- **The large sieve on any `ν`-spaced set, `0 < ν ≤ 1`** (a single point by Cauchy–Schwarz,
two or more force `ν ≤ 1/2`). -/
theorem ls_sep (ls : LargeSieve) (R : Finset ℕ) (β : ℕ → ℝ) (ν : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → ∀ n : ℤ, ν ≤ |β r - β s - n|)
    (M N : ℕ) (b : ℕ → ℂ) :
    ∑ r ∈ R, ‖∑ n ∈ Finset.Ioc M (M + N), b n * e (n * β r)‖ ^ 2 ≤
      ((N : ℝ) - 1 + ν⁻¹) * ∑ n ∈ Finset.Ioc M (M + N), ‖b n‖ ^ 2 := by
  rcases le_or_gt R.card 1 with hc | hc
  · have hinv : 1 ≤ ν⁻¹ := one_le_inv₀ hν |>.mpr hν1
    have hS : 0 ≤ ∑ n ∈ Finset.Ioc M (M + N), ‖b n‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    rcases Finset.card_le_one_iff_subset_singleton.mp hc with ⟨r, hr⟩
    calc ∑ r ∈ R, ‖∑ n ∈ Finset.Ioc M (M + N), b n * e (n * β r)‖ ^ 2
        ≤ ∑ r ∈ {r}, ‖∑ n ∈ Finset.Ioc M (M + N), b n * e (n * β r)‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hr fun _ _ _ => sq_nonneg _
      _ ≤ (N : ℝ) * ∑ n ∈ Finset.Ioc M (M + N), ‖b n‖ ^ 2 := by
          rw [Finset.sum_singleton]; exact one_bd M N b (β r)
      _ ≤ _ := by gcongr; linarith
  · obtain ⟨r, hr, s, hs, hrs⟩ := Finset.one_lt_card.mp hc
    have h := hsep r hr s hs hrs (round (β r - β s))
    have h12 : ν ≤ 1 / 2 := h.trans (abs_sub_round _)
    exact ls R β ν hν h12 hsep M N b

/-- **One block**: on a set of `m` whose frequencies `mα` are `ν`-spaced (`0 < ν ≤ 1`),
`∑_m S(mα)² ≤ (W − W' + ν⁻¹)·∑(log p)²`. -/
theorem block_bd (ls : LargeSieve) (α W' W ν : ℝ) (hW' : 0 ≤ W') (hν : 0 < ν) (hν1 : ν ≤ 1)
    (t : Finset ℕ)
    (hsep : ∀ m ∈ t, ∀ m' ∈ t, m ≠ m' → ∀ n : ℤ, ν ≤ |((m : ℝ) - m') * α - n|) :
    ∑ m ∈ t, ‖pS α W' W m‖ ^ 2 ≤ (W - W' + ν⁻¹) * pSq W' W := by
  set M := ⌊W'⌋₊ with hM
  set N := ⌊W⌋₊ - ⌊W'⌋₊ with hN
  have hls := ls_sep ls t (fun m => (m : ℝ) * α) ν hν hν1
    (fun r hr s hs hrs n => by
      have := hsep r hr s hs hrs n
      simpa only [sub_mul] using this) M N bP
  have hP : 0 ≤ pSq W' W := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [← pSq_eq W' W hW'] at hls
  have hL : ∑ m ∈ t, ‖pS α W' W m‖ ^ 2 ≤ ((N : ℝ) - 1 + ν⁻¹) * pSq W' W := by
    refine le_of_eq_of_le (Finset.sum_congr rfl fun m _ => ?_) hls
    rw [pS_eq α W' W hW' m]
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · have hz : pSq W' W = 0 := by
      rw [pSq_eq W' W hW', ← hN, h0, add_zero, Finset.Ioc_self, Finset.sum_empty]
    rw [hz, mul_zero] at hL ⊢
    exact hL
  · refine hL.trans (mul_le_mul_of_nonneg_right ?_ hP)
    have hlt : ⌊W'⌋₊ < ⌊W⌋₊ := by omega
    have hW0 : 0 ≤ W := by
      by_contra hneg
      have h0 : ⌊W⌋₊ = 0 := Nat.floor_of_nonpos (by linarith)
      omega
    have hNr : (N : ℝ) = (⌊W⌋₊ : ℝ) - ⌊W'⌋₊ := by
      rw [hN, Nat.cast_sub hlt.le]
    have h1 := Nat.floor_le hW0
    have h2 := Nat.lt_floor_add_one W'
    rw [hNr]
    linarith


/-! ## Spacing -/

/-- `‖j(a/q + d)‖ ≥ ν`: from `q ∤ ja` the fraction part is `≥ 1/q` away from integers, and
`|jd| ≤ 1/q − ν`; when `q ∣ j` the fraction part vanishes and `|jd| ≥ ν` is assumed. -/
theorem sep_core (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hg : Int.gcd a q = 1) (j : ℤ) (d ν : ℝ)
    (hsmall : |(j : ℝ) * d| ≤ 1 / q - ν) (hdiv : (q : ℤ) ∣ j → ν ≤ |(j : ℝ) * d|) (n : ℤ) :
    ν ≤ |(j : ℝ) * ((a : ℝ) / q + d) - n| := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  by_cases h : j * a = n * q
  · have hd : (q : ℤ) ∣ j := by
      have h1 : (q : ℤ) ∣ j * a := ⟨n, by rw [h]; ring⟩
      exact Int.dvd_of_dvd_mul_left_of_gcd_one h1 (by rw [Int.gcd_comm]; exact hg)
    have hr : (j : ℝ) * a = n * q := by exact_mod_cast h
    have : (j : ℝ) * ((a : ℝ) / q + d) - n = j * d := by
      field_simp
      linear_combination hr
    rw [this]
    exact hdiv hd
  · have h1 : (1 : ℝ) ≤ |((j * a - n * q : ℤ) : ℝ)| := by
      have : (j * a - n * q : ℤ) ≠ 0 := sub_ne_zero.mpr h
      have h' := Int.one_le_abs this
      rw [← Int.cast_abs]
      exact_mod_cast h'
    have h2 : (j : ℝ) * ((a : ℝ) / q + d) - n = ((j * a - n * q : ℤ) : ℝ) / q + j * d := by
      push_cast
      field_simp
      ring
    rw [h2]
    have h3 : 1 / (q : ℝ) ≤ |((j * a - n * q : ℤ) : ℝ) / q| := by
      rw [abs_div, abs_of_pos hq0]
      exact div_le_div_of_nonneg_right h1 hq0.le
    have h4 : |((j * a - n * q : ℤ) : ℝ) / q| ≤
        |((j * a - n * q : ℤ) : ℝ) / q + j * d| + |(j : ℝ) * d| := by
      have := abs_add_le (((j * a - n * q : ℤ) : ℝ) / q + j * d) (-((j : ℝ) * d))
      rwa [add_neg_cancel_right, abs_neg] at this
    linarith

/-- Two odd `m ≠ m'` differ by `2j`, and `(m − m')α = j(a/q + d)` when `2α = a/q + d`. -/
theorem sep_odd (α : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hg : Int.gcd a q = 1) (d ν : ℝ)
    (h2a : 2 * α = a / q + d) (m m' : ℕ) (hm : m % 2 = 1) (hm' : m' % 2 = 1)
    (hsmall : ∀ j : ℤ, (m : ℝ) - m' = 2 * j → |(j : ℝ) * d| ≤ 1 / q - ν)
    (hdiv : ∀ j : ℤ, (m : ℝ) - m' = 2 * j → (q : ℤ) ∣ j → ν ≤ |(j : ℝ) * d|) (n : ℤ) :
    ν ≤ |((m : ℝ) - m') * α - n| := by
  obtain ⟨j, hj⟩ : ∃ j : ℤ, (m : ℤ) - m' = 2 * j := ⟨((m : ℤ) - m') / 2, by omega⟩
  have hjr : (m : ℝ) - m' = 2 * j := by exact_mod_cast hj
  have : ((m : ℝ) - m') * α = j * ((a : ℝ) / q + d) := by rw [hjr, ← h2a]; ring
  rw [this]
  exact sep_core a q hq hg j d ν (hsmall j hjr) (hdiv j hjr) n

/-- A nonzero multiple of `q` has absolute value `≥ q`. -/
theorem q_le_abs (q : ℕ) (j : ℤ) (hj : j ≠ 0) (hd : (q : ℤ) ∣ j) : (q : ℝ) ≤ |(j : ℝ)| := by
  have h := Int.le_of_dvd (abs_pos.mpr hj) ((dvd_abs _ _).mpr hd)
  rw [← Int.cast_abs]
  exact_mod_cast h

/-! ## Blocks -/

/-- **Splitting into blocks of length `B`**: if every subset of diameter `< B` contributes at
most `C`, a set inside `(A₀, A₀ + L]` contributes at most `(L/B + 1)·C`. -/
theorem sum_blocks (s : Finset ℕ) (f : ℕ → ℝ) (A0 L B C : ℝ) (hB : 0 < B)
    (hL : 0 ≤ L) (hC : 0 ≤ C) (hs : ∀ m ∈ s, A0 < (m : ℝ) ∧ (m : ℝ) ≤ A0 + L)
    (hblk : ∀ t ⊆ s, (∀ m ∈ t, ∀ m' ∈ t, |(m : ℝ) - m'| < B) → ∑ m ∈ t, f m ≤ C) :
    ∑ m ∈ s, f m ≤ (L / B + 1) * C := by
  have hmaps : ∀ m ∈ s, ⌊((m : ℝ) - A0) / B⌋₊ ∈ Finset.range (⌊L / B⌋₊ + 1) := by
    intro m hm
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith [(hs m hm).2]) hB.le)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ i ∈ Finset.range (⌊L / B⌋₊ + 1),
      ∑ m ∈ s.filter (fun m : ℕ => ⌊((m : ℝ) - A0) / B⌋₊ = i), f m ≤ C := by
    intro i _
    refine hblk _ (Finset.filter_subset _ _) ?_
    have hb : ∀ m ∈ s.filter (fun m : ℕ => ⌊((m : ℝ) - A0) / B⌋₊ = i),
        (i : ℝ) * B ≤ (m : ℝ) - A0 ∧ (m : ℝ) - A0 < (i + 1) * B := by
      intro m hm
      rw [Finset.mem_filter] at hm
      have h0 : 0 ≤ ((m : ℝ) - A0) / B := div_nonneg (by linarith [(hs m hm.1).1]) hB.le
      have h1 := Nat.floor_le h0
      have h2 := Nat.lt_floor_add_one (((m : ℝ) - A0) / B)
      rw [hm.2] at h1 h2
      exact ⟨(le_div_iff₀ hB).mp h1, (div_lt_iff₀ hB).mp h2⟩
    intro m hm m' hm'
    obtain ⟨a1, a2⟩ := hb m hm
    obtain ⟨b1, b2⟩ := hb m' hm'
    rw [abs_sub_lt_iff]
    constructor <;> nlinarith
  calc ∑ i ∈ Finset.range (⌊L / B⌋₊ + 1),
        ∑ m ∈ s.filter (fun m : ℕ => ⌊((m : ℝ) - A0) / B⌋₊ = i), f m
      ≤ ∑ _i ∈ Finset.range (⌊L / B⌋₊ + 1), C := Finset.sum_le_sum hfib
    _ = ((⌊L / B⌋₊ : ℝ) + 1) * C := by simp
    _ ≤ (L / B + 1) * C := by
        gcongr
        exact Nat.floor_le (div_nonneg hL hB.le)

/-- Membership in `T2S.mSet`. -/
theorem mem_mSet {x A W : ℝ} {m : ℕ} (h : m ∈ mSet x A W) :
    m % 2 = 1 ∧ x / (2 * W) < m ∧ A < m ∧ (m : ℝ) ≤ x / W := by
  unfold mSet at h
  rw [Finset.mem_filter, Finset.mem_Icc, max_lt_iff] at h
  obtain ⟨⟨h1, h2⟩, h3, h4, h5⟩ := h
  exact ⟨h3, h4, h5, (Nat.le_floor_iff' (by omega)).mp h2⟩

/-- Two elements of `mSet x A W` are `< x/2W` apart. -/
theorem mSet_close {x A W : ℝ} {m m' : ℕ} (h : m ∈ mSet x A W) (h' : m' ∈ mSet x A W)
    (hW : 0 < W) : |(m : ℝ) - m'| < x / (2 * W) := by
  obtain ⟨-, a1, -, a2⟩ := mem_mSet h
  obtain ⟨-, b1, -, b2⟩ := mem_mSet h'
  have : x / W = 2 * (x / (2 * W)) := by field_simp
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/-! ## `eq:gargamel` -/

/-- **`T2X.Gargamel`, PROVED from the large sieve**: one block, the `< x/4W` steps `j` of the
odd `m` give `‖j·2α‖ ≥ (1 − x/4Wq)/q`. -/
theorem gargamel_holds (ls : LargeSieve) : Gargamel := by
  intro x W W' U' Q α δ a q hW hWx hW' hU' hq hg h2a hδ hqQ hxW
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hW0 : 0 < W := by linarith
  have hx0 : 0 < x := by linarith
  have ht1 : x / (4 * W * q) < 1 := by
    rw [div_lt_one (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hxW
    linarith
  have ht0 : 0 ≤ x / (4 * W * q) := by positivity
  have hν : 0 < (1 - x / (4 * W * q)) / q := div_pos (by linarith) hq0
  have hν1 : (1 - x / (4 * W * q)) / q ≤ 1 := by
    rw [div_le_one hq0]
    linarith
  have hP : 0 ≤ pSq W' W := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have key := block_bd ls α W' W ((1 - x / (4 * W * q)) / q) (by linarith) hν hν1 (mSet x U' W)
    (fun m hm m' hm' hne n => by
      obtain ⟨hmo, -⟩ := mem_mSet hm
      obtain ⟨hmo', -⟩ := mem_mSet hm'
      have hcl := mSet_close hm hm' hW0
      have hjb : ∀ j : ℤ, (m : ℝ) - m' = 2 * j → |(j : ℝ)| < x / (4 * W) := by
        intro j hj
        rw [hj, abs_mul, abs_two] at hcl
        have : x / (2 * W) = 2 * (x / (4 * W)) := by field_simp; ring
        linarith
      have hj0 : ∀ j : ℤ, (m : ℝ) - m' = 2 * j → j ≠ 0 := by
        intro j hj h0
        rw [h0, Int.cast_zero, mul_zero, sub_eq_zero] at hj
        exact hne (by exact_mod_cast hj)
      have hxq : x / (4 * W) < q := by
        have : x / (4 * W) = x / (4 * W * q) * q := by field_simp
        rw [this]
        nlinarith
      refine sep_odd α a q hq hg (δ / x) _ h2a m m' hmo hmo' (fun j hj => ?_)
        (fun j hj hd => absurd (q_le_abs q j (hj0 j hj) hd) (not_le.mpr ((hjb j hj).trans hxq)))
        n
      have hQq : 1 / ((q : ℝ) * Q) ≤ 1 / ((q : ℝ) * q) :=
        one_div_le_one_div_of_le (by positivity) (by nlinarith)
      have e1 : 1 / (q : ℝ) - (1 - x / (4 * W * q)) / q = x / (4 * W) * (1 / ((q : ℝ) * q)) := by
        field_simp
        ring
      rw [e1, abs_mul]
      exact mul_le_mul (hjb j hj).le (hδ.trans hQq) (abs_nonneg _) (by positivity))
  calc s2 x α U' W' W = ∑ m ∈ mSet x U' W, ‖pS α W' W m‖ ^ 2 := rfl
    _ ≤ (W - W' + ((1 - x / (4 * W * q)) / q)⁻¹) * pSq W' W := key
    _ ≤ (W / 2 + q / (1 - x / (4 * W * q))) * pSq W' W := by
        rw [inv_div]
        gcongr
        linarith


/-- Every element of `mSet x U' W` lies in `(A₀, A₀ + x/2W]`, `A₀ = max(x/2W, U')`. -/
theorem mSet_range {x U' W : ℝ} (hW : 0 < W) (m : ℕ) (hm : m ∈ mSet x U' W) :
    max (x / (2 * W)) U' < (m : ℝ) ∧ (m : ℝ) ≤ max (x / (2 * W)) U' + x / (2 * W) := by
  obtain ⟨-, h1, h2, h3⟩ := mem_mSet hm
  have : x / W = x / (2 * W) + x / (2 * W) := by field_simp; ring
  exact ⟨max_lt h1 h2, by linarith [le_max_left (x / (2 * W)) U']⟩

/-! ## `eq:procida2` (large-sieve half) and `eq:procida3` -/

/-- **One `δ`-block** (`lem:ogor` with `ν = q|δ|/x`, `ν⁻¹ = Q' = x/|δ|q`): odd `m` at mutual
distance `< 2(Q' − q)` give `∑ S(mα)² ≤ (W/2 + Q')·∑(log p)²`. -/
theorem procida_block (ls : LargeSieve) (x W W' Q α δ : ℝ) (a : ℤ) (q : ℕ) (hW : 117 ≤ W)
    (hWx : W ≤ x) (hW' : W / 2 ≤ W') (hq : 1 ≤ q) (hg : Int.gcd a q = 1)
    (h2a : 2 * α = a / q + δ / x) (hδ : |δ / x| ≤ 1 / (q * Q)) (hqQ : (q : ℝ) ≤ Q)
    (hδ0 : δ ≠ 0) (t : Finset ℕ) (ht : ∀ m ∈ t, m % 2 = 1)
    (hdiam : ∀ m ∈ t, ∀ m' ∈ t, |(m : ℝ) - m'| < 2 * (x / (|δ| * q) - q)) :
    ∑ m ∈ t, ‖pS α W' W m‖ ^ 2 ≤ (W / 2 + x / (|δ| * q)) * pSq W' W := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hx0 : 0 < x := by linarith
  have hA : 0 < |δ| := abs_pos.mpr hδ0
  have hδx : |δ / x| = |δ| / x := by rw [abs_div, abs_of_pos hx0]
  rw [hδx] at hδ
  have hQ0 : 0 < Q := by linarith
  have hν : 0 < (q : ℝ) * |δ| / x := by positivity
  have hν1 : (q : ℝ) * |δ| / x ≤ 1 := by
    have h1 : (q : ℝ) * (|δ| / x) ≤ q * (1 / (q * Q)) := mul_le_mul_of_nonneg_left hδ hq0.le
    have h2 : (q : ℝ) * (1 / (q * Q)) = 1 / Q := by field_simp
    have h3 : 1 / Q ≤ 1 := by rw [div_le_one hQ0]; linarith
    calc (q : ℝ) * |δ| / x = q * (|δ| / x) := by ring
      _ ≤ 1 := by linarith
  have hP : 0 ≤ pSq W' W := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have key := block_bd ls α W' W ((q : ℝ) * |δ| / x) (by linarith) hν hν1 t
    (fun m hm m' hm' hne n => by
      have hcl := hdiam m hm m' hm'
      refine sep_odd α a q hq hg (δ / x) _ h2a m m' (ht m hm) (ht m' hm') (fun j hj => ?_)
        (fun j hj hd => ?_) n
      · rw [hj, abs_mul, abs_two] at hcl
        have hjb : |(j : ℝ)| ≤ x / (|δ| * q) - q := by linarith
        have e1 : 1 / (q : ℝ) - q * |δ| / x = (x / (|δ| * q) - q) * (|δ| / x) := by
          field_simp
        rw [e1, abs_mul, hδx]
        exact mul_le_mul_of_nonneg_right hjb (by positivity)
      · have hj0 : j ≠ 0 := by
          intro h0
          rw [h0, Int.cast_zero, mul_zero, sub_eq_zero] at hj
          exact hne (by exact_mod_cast hj)
        have hqj := q_le_abs q j hj0 hd
        rw [abs_mul, hδx]
        calc (q : ℝ) * |δ| / x = q * (|δ| / x) := by ring
          _ ≤ |(j : ℝ)| * (|δ| / x) := mul_le_mul_of_nonneg_right hqj (by positivity))
  refine key.trans (mul_le_mul_of_nonneg_right ?_ hP)
  rw [inv_div, mul_comm (q : ℝ)]
  linarith

/-- **`eq:procida2`, its large-sieve half (the `1` of the `min`), PROVED**: one block. -/
theorem procida2_ls (ls : LargeSieve) :
    ∀ x W W' U' Q α δ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 117 ≤ W → W ≤ x → W / 2 ≤ W' →
      x / (2 * W) ≤ U' → 1 ≤ q → Int.gcd a q = 1 → 2 * α = a / q + δ / x →
        |δ / x| ≤ 1 / (q * Q) → (q : ℝ) ≤ Q → δ ≠ 0 → x / (4 * W) + q < x / (|δ| * q) →
          s2 x α U' W' W ≤ (x / (|δ| * q) + W / 2) * pSq W' W := by
  intro x W W' U' Q α δ a q hW hWx hW' _ hq hg h2a hδ hqQ hδ0 hst
  have hW0 : 0 < W := by linarith
  have h := procida_block ls x W W' Q α δ a q hW hWx hW' hq hg h2a hδ hqQ hδ0 (mSet x U' W)
    (fun m hm => (mem_mSet hm).1) (fun m hm m' hm' => by
      have hcl := mSet_close hm hm' hW0
      have : x / (2 * W) = 2 * (x / (4 * W)) := by field_simp; ring
      linarith)
  calc s2 x α U' W' W = ∑ m ∈ mSet x U' W, ‖pS α W' W m‖ ^ 2 := rfl
    _ ≤ (W / 2 + x / (|δ| * q)) * pSq W' W := h
    _ = (x / (|δ| * q) + W / 2) * pSq W' W := by ring

/-- **NAMED (open) — the Montgomery half of `eq:procida2`**: the second branch of its `min`,
`S₂ ≤ (2q/φ(q))/log((x/|δq|)/(q + x/4W)) · (x/|δq| + W/2)·∑(log p)²`, under `eq:procida2`'s
hypotheses exactly (`lem:ogor` via Montgomery's inequality, IK Lemma 7.15). OPEN. -/
def Procida2Mont : Prop :=
  ∀ x W W' U' Q α δ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 117 ≤ W → W ≤ x → W / 2 ≤ W' → x / (2 * W) ≤ U' →
    1 ≤ q → Int.gcd a q = 1 → 2 * α = a / q + δ / x → |δ / x| ≤ 1 / (q * Q) → (q : ℝ) ≤ Q →
      δ ≠ 0 → x / (4 * W) + q < x / (|δ| * q) →
        s2 x α U' W' W ≤ 2 * ((q : ℝ) / Nat.totient q) /
          Real.log (x / (|δ| * q) / (q + x / (4 * W))) * (x / (|δ| * q) + W / 2) * pSq W' W

/-- **`T2X.Procida2` from the large sieve and its Montgomery half, PROVED.** -/
theorem procida2_of (ls : LargeSieve) (hm : Procida2Mont) : Procida2 := by
  intro x W W' U' Q α δ a q hW hWx hW' hU' hq hg h2a hδ hqQ hδ0 hst
  rcases le_total 1 (2 * ((q : ℝ) / Nat.totient q) /
      Real.log (x / (|δ| * q) / (q + x / (4 * W)))) with h1 | h1
  · rw [min_eq_left h1, one_mul]
    exact procida2_ls ls x W W' U' Q α δ a q hW hWx hW' hU' hq hg h2a hδ hqQ hδ0 hst
  · rw [min_eq_right h1]
    exact hm x W W' U' Q α δ a q hW hWx hW' hU' hq hg h2a hδ hqQ hδ0 hst

/-- **`T2X.Procida3`, PROVED from the large sieve**: blocks of length `2(Q' − q)`. -/
theorem procida3_holds (ls : LargeSieve) : Procida3 := by
  intro x W W' U' Q α δ a q hW hWx hW' hU' hq hg h2a hδ hqQ hδ0 ρ hρ0 hρ1 hqρ
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hW0 : 0 < W := by linarith
  have hx0 : 0 < x := by linarith
  have hA : 0 < |δ| := abs_pos.mpr hδ0
  have hQ0 : 0 < Q := by linarith
  have hδx : |δ / x| = |δ| / x := by rw [abs_div, abs_of_pos hx0]
  have hQQ : Q ≤ x / (|δ| * q) := by
    rw [hδx, div_le_div_iff₀ hx0 (by positivity), one_mul] at hδ
    rw [le_div_iff₀ (by positivity)]
    linarith
  set Q' := x / (|δ| * q) with hQ'
  have hD : (1 - ρ) * Q ≤ Q' - q := by nlinarith
  have hD' : Q' * (1 - ρ) ≤ Q' - q := by nlinarith
  have hD0 : 0 < Q' - q := lt_of_lt_of_le (by nlinarith) hD
  have hP : 0 ≤ pSq W' W := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hblk := sum_blocks (mSet x U' W) (fun m => ‖pS α W' W m‖ ^ 2) (max (x / (2 * W)) U')
    (x / (2 * W)) (2 * (Q' - q)) ((W / 2 + Q') * pSq W' W) (by linarith) (by positivity)
    (by positivity) (mSet_range hW0)
    (fun t hts hdiam => procida_block ls x W W' Q α δ a q hW hWx hW' hq hg h2a hδ hqQ hδ0 t
      (fun m hm => (mem_mSet (hts hm)).1) hdiam)
  have e : (x / (2 * W) / (2 * (Q' - q)) + 1) * (W / 2 + Q') =
      W / 2 + Q' + x / (8 * (Q' - q)) + x * Q' / (4 * W * (Q' - q)) := by
    field_simp
    ring
  have hco : (x / (2 * W) / (2 * (Q' - q)) + 1) * (W / 2 + Q') ≤
      Q' + W / 2 + x / (8 * (1 - ρ) * Q) + x / (4 * (1 - ρ) * W) := by
    rw [e]
    have i1 : x / (8 * (Q' - q)) ≤ x / (8 * (1 - ρ) * Q) :=
      div_le_div_of_nonneg_left hx0.le (by nlinarith) (by linarith)
    have i2 : x * Q' / (4 * W * (Q' - q)) ≤ x / (4 * (1 - ρ) * W) := by
      rw [div_le_div_iff₀ (by positivity) (by nlinarith)]
      calc x * Q' * (4 * (1 - ρ) * W) = (4 * x * W) * (Q' * (1 - ρ)) := by ring
        _ ≤ (4 * x * W) * (Q' - q) := by gcongr
        _ = x * (4 * W * (Q' - q)) := by ring
    linarith
  calc s2 x α U' W' W = ∑ m ∈ mSet x U' W, ‖pS α W' W m‖ ^ 2 := rfl
    _ ≤ (x / (2 * W) / (2 * (Q' - q)) + 1) * ((W / 2 + Q') * pSq W' W) := hblk
    _ = ((x / (2 * W) / (2 * (Q' - q)) + 1) * (W / 2 + Q')) * pSq W' W := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hco hP

/-! ## `eq:garn1b` -/

/-- **`T2X.Garn1b`, PROVED from the large sieve**: blocks of `2K`, `K = min(q, ⌈Q/2⌉)`, inside
which the odd `m` are `1/2q`-spaced. -/
theorem garn1b_holds (ls : LargeSieve) : Garn1b := by
  intro x W W' U' Q α δ a q hW hWx hW' hU' hq hg h2a hδ hqQ ρ hρ0 hρ1 hqρ
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hW0 : 0 < W := by linarith
  have hx0 : 0 < x := by linarith
  have hQ0 : 0 < Q := by linarith
  set c := ⌈Q / 2⌉₊ with hc
  set K := min q c with hK
  have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by linarith)).ne'
  have hK1 : 1 ≤ K := le_min hq hc1
  have hKq : K ≤ q := min_le_left _ _
  have hKc : K ≤ c := min_le_right _ _
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hcQ : (c : ℝ) < Q / 2 + 1 := Nat.ceil_lt_add_one (by linarith)
  have hKr : (K : ℝ) ≤ c := by exact_mod_cast hKc
  have hKqr : (K : ℝ) ≤ q := by exact_mod_cast hKq
  have hP : 0 ≤ pSq W' W := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hblock : ∀ t ⊆ mSet x U' W, (∀ m ∈ t, ∀ m' ∈ t, |(m : ℝ) - m'| < 2 * K) →
      ∑ m ∈ t, ‖pS α W' W m‖ ^ 2 ≤ (W / 2 + 2 * q) * pSq W' W := by
    intro t hts hdiam
    have hν : (0 : ℝ) < 1 / (2 * q) := by positivity
    have hν1 : 1 / (2 * (q : ℝ)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have key := block_bd ls α W' W (1 / (2 * q)) (by linarith) hν hν1 t
      (fun m hm m' hm' hne n => by
        have hcl := hdiam m hm m' hm'
        have hjK : ∀ j : ℤ, (m : ℝ) - m' = 2 * j → |(j : ℝ)| + 1 ≤ K := by
          intro j hj
          rw [hj, abs_mul, abs_two] at hcl
          have h1 : |(j : ℝ)| < K := by linarith
          rw [← Int.cast_abs] at h1
          have h2 : |j| < (K : ℤ) := by exact_mod_cast h1
          have h3 : |j| + 1 ≤ (K : ℤ) := h2
          rw [← Int.cast_abs]
          exact_mod_cast h3
        have hj0 : ∀ j : ℤ, (m : ℝ) - m' = 2 * j → j ≠ 0 := by
          intro j hj h0
          rw [h0, Int.cast_zero, mul_zero, sub_eq_zero] at hj
          exact hne (by exact_mod_cast hj)
        refine sep_odd α a q hq hg (δ / x) _ h2a m m' (mem_mSet (hts hm)).1
          (mem_mSet (hts hm')).1 (fun j hj => ?_) (fun j hj hd => ?_) n
        · have hjQ : |(j : ℝ)| ≤ Q / 2 := by linarith [hjK j hj]
          have e1 : 1 / (q : ℝ) - 1 / (2 * q) = Q / 2 * (1 / (q * Q)) := by
            field_simp
            ring
          rw [e1, abs_mul]
          exact mul_le_mul hjQ hδ (abs_nonneg _) (by positivity)
        · have := q_le_abs q j (hj0 j hj) hd
          linarith [hjK j hj])
    refine key.trans (mul_le_mul_of_nonneg_right ?_ hP)
    rw [one_div, inv_inv]
    linarith
  have hsum := sum_blocks (mSet x U' W) (fun m => ‖pS α W' W m‖ ^ 2) (max (x / (2 * W)) U')
    (x / (2 * W)) (2 * K) ((W / 2 + 2 * q) * pSq W' W) (by linarith) (by positivity)
    (by positivity) (mSet_range hW0) hblock
  have hM1 : (1 : ℝ) ≤ max 1 (2 * ρ) := le_max_left _ _
  have hKM : (q : ℝ) ≤ K * max 1 (2 * ρ) := by
    rcases min_choice q c with h | h
    · rw [hK, h]
      nlinarith
    · rw [hK, h]
      have h1 : Q / 2 ≤ (c : ℝ) := by
        have := Nat.le_ceil (Q / 2)
        rw [hc]
        exact this
      have h2 : 2 * ρ ≤ max 1 (2 * ρ) := le_max_right _ _
      nlinarith
  have hqK : (q : ℝ) / K ≤ max 1 (2 * ρ) := by
    rw [div_le_iff₀ hK0]
    linarith
  have e : (x / (2 * W) / (2 * K) + 1) * (W / 2 + 2 * q) =
      (x / (8 * q) + x / (2 * W)) * (q / K) + W / 2 + 2 * q := by
    field_simp
    ring
  calc s2 x α U' W' W = ∑ m ∈ mSet x U' W, ‖pS α W' W m‖ ^ 2 := rfl
    _ ≤ (x / (2 * W) / (2 * K) + 1) * ((W / 2 + 2 * q) * pSq W' W) := hsum
    _ = ((x / (8 * q) + x / (2 * W)) * (q / K) + W / 2 + 2 * q) * pSq W' W := by
        rw [← e]
        ring
    _ ≤ (max 1 (2 * ρ) * (x / (8 * q) + x / (2 * W)) + W / 2 + 2 * q) * pSq W' W := by
        have h : (x / (8 * q) + x / (2 * W)) * (q / K) ≤
            max 1 (2 * ρ) * (x / (8 * q) + x / (2 * W)) := by
          rw [mul_comm (max 1 (2 * ρ))]
          exact mul_le_mul_of_nonneg_left hqK (by positivity)
        exact mul_le_mul_of_nonneg_right (by linarith) hP

/-! ## `T2S.Kraken` -/

/-- **`T2S.Kraken` from the large sieve, `eq:garn1a` and the Montgomery half of `eq:procida2`,
PROVED.** -/
theorem kraken_of_ls (ls : LargeSieve) (g2 : Garn1a) (hm : Procida2Mont) : Kraken :=
  kraken_of (garn1b_holds ls) g2 (gargamel_holds ls) (procida2_of ls hm) (procida3_holds ls)

end Principia.Common.TernaryGoldbach.T2K
