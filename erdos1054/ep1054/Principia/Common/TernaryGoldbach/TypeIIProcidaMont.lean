/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIIKrakenLS
import Principia.Common.TernaryGoldbach.TypeIICrustoCudo
import Principia.Common.Sieve.BrunTitchmarshAP

set_option autoImplicit false

/-!
# `T2K.Procida2Mont` PROVED from Montgomery's inequality and the large sieve

`T2K.Procida2Mont` (`TypeIIKrakenLS`) is the log branch of `eq:procida2`:
`S₂ ≤ 2(q/φ(q))/log T · (x/|δ|q + W/2)·∑(log p)²`, `T = (x/|δ|q)/(q + x/4W)`, under the
hypotheses of `eq:procida2`. The book proves it through `lem:ogor` (`minarcs.tex` 3348-3398):
Montgomery's inequality at `R = (q(ν + υ))^{−1/2} = √T` (`ν = q|δ|/x`, `υ = |δ|/4W`), then the
large sieve over the points `mα + c/r`, `r ≤ R` square-free coprime to `q`, `(c, r) = 1`, which
are `ν`-spaced because distinct fractions `a/q + c/r` are `1/qR² = ν + υ` apart.

**Finding (confirmed and repaired).** Montgomery's inequality needs every prime `p > W'` coprime
to every `r ≤ R`, i.e. `R ≤ W'`; nothing in `eq:procida2` forces this. The proof here splits:

* `√T ≤ W'` — the book's argument (`mont_case`), with the sum `∑_{r ≤ √T} μ²(r)/φ(r)` over
  `(r, q) = 1` bounded below by `(φ(q)/q)·log √T` (`eq:werst`) through the Selberg-sum bound
  already proved in `Principia.Common.Sieve.BrunTitchmarshAP.boundingSum_ge`;
* `√T > W'` — the trivial bound `S₂ ≤ (x/4W + 1)(W/2 + 1)·∑(log p)²` (`triv_bd`) is below the
  target, because `(W/2 + 1)·log T ≤ (√T + 1)√T ≤ 2T` (`log T ≤ √T`) and
  `x/4W + 1 ≤ q + x/4W`, so `(x/4W + 1)(W/2 + 1) ≤ 2(x/|δ|q)/log T`. The task brief's claim
  ("on `R > W'` the trivial Cauchy–Schwarz bound wins") is CORRECT.

```
 MontgomeryIneq   NAMED literature: Montgomery 1968; IK Lemma 7.15 (case ω(p) = 1)
 block_gen        the large sieve on any ν-spaced frequencies                   PROVED
 block_triples    ... indexed by triples (Nat.pair)                             PROVED
 sep_triple       distinct (m, r, c) give ν-spaced mα + c/r                     PROVED
 rSet_ge          ∑_{r ∈ rSet} 1/φ(r) ≥ (φ(q)/q)·log √T   (eq:werst)          PROVED
 mont_one         Montgomery for one m, summed over r                           PROVED
 mont_case        √T ≤ W' : S₂ ≤ (q/φ(q))/log √T·(x/|δ|q + W/2)·∑(log p)²      PROVED
 triv_bd          S₂ ≤ (x/4W + 1)(W/2 + 1)·∑(log p)²                            PROVED
 procida2Mont_holds : MontgomeryIneq → LargeSieve → Procida2Mont               PROVED
 kraken_of_mont     : LargeSieve → MontgomeryIneq → Garn1a → Kraken            PROVED
```

So `T2S.Kraken` now owes exactly `Garn1a`, beside the literature `LargeSieve` and
`MontgomeryIneq`.
-/

namespace Principia.Common.TernaryGoldbach.T2M

open Principia.Common.Goldbach
open Principia.Common.TernaryGoldbach.T2S Principia.Common.TernaryGoldbach.T2X
open Principia.Common.TernaryGoldbach.T2K

/-! ## (0) Montgomery's inequality (named literature) -/

/-- **NAMED (literature) — Montgomery's inequality, the case `ω(p) = 1`** (H. L. Montgomery,
*A note on the large sieve*, J. London Math. Soc. 43 (1968), 93-98; Iwaniec–Kowalski, *Analytic
Number Theory*, §7.4, Lemma 7.15; Montgomery, *Topics in Multiplicative Number Theory*, LNM 227,
pp. 27-29; cited by the book in `lem:ogor` as `\cite{MR0224585}`, `\cite[§7.4]{MR2061214}`):
for square-free `r` and `b_n` vanishing on the `n` not coprime to `r` (the residue class `0`
sifted mod every `p ∣ r`, so `h(r) = ∏_{p ∣ r} 1/(p − 1) = 1/φ(r)`),
`|S(β)|² ≤ φ(r)·∑_{c mod r, (c, r) = 1} |S(β + c/r)|²`, `S(β) = ∑_{M<n≤M+N} b_n e(nβ)`. -/
def MontgomeryIneq : Prop :=
  ∀ r : ℕ, Squarefree r → ∀ (M N : ℕ) (b : ℕ → ℂ) (β : ℝ),
    (∀ n ∈ Finset.Ioc M (M + N), ¬ Nat.Coprime n r → b n = 0) →
      ‖∑ n ∈ Finset.Ioc M (M + N), b n * e (n * β)‖ ^ 2 ≤
        (Nat.totient r : ℝ) * ∑ c ∈ (Finset.range r).filter (fun c => Nat.Coprime c r),
          ‖∑ n ∈ Finset.Ioc M (M + N), b n * e (n * (β + c / r))‖ ^ 2

/-! ## (1) The prime exponential sum at an arbitrary frequency -/

/-- `S(β) = ∑_{W'<p≤W} (log p) e(pβ)`, written over the `Ioc` of `T2K.pS_eq`. -/
noncomputable def sB (W' W β : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊W'⌋₊ (⌊W'⌋₊ + (⌊W⌋₊ - ⌊W'⌋₊)), bP n * e (n * β)

theorem pS_eq_sB (α W' W : ℝ) (hW' : 0 ≤ W') (m : ℕ) :
    pS α W' W m = sB W' W ((m : ℝ) * α) :=
  pS_eq α W' W hW' m

/-- **One block, arbitrary frequencies**: `ν`-spaced `β_i` (`0 < ν ≤ 1`) give
`∑_i |S(β_i)|² ≤ (W − W' + ν⁻¹)·∑(log p)²` (`T2K.block_bd` with general points). -/
theorem block_gen (ls : LargeSieve) (W' W ν : ℝ) (hW' : 0 ≤ W') (hν : 0 < ν) (hν1 : ν ≤ 1)
    (t : Finset ℕ) (β : ℕ → ℝ)
    (hsep : ∀ i ∈ t, ∀ k ∈ t, i ≠ k → ∀ n : ℤ, ν ≤ |β i - β k - n|) :
    ∑ i ∈ t, ‖sB W' W (β i)‖ ^ 2 ≤ (W - W' + ν⁻¹) * pSq W' W := by
  set M := ⌊W'⌋₊ with hM
  set N := ⌊W⌋₊ - ⌊W'⌋₊ with hN
  have hls := ls_sep ls t β ν hν hν1 hsep M N bP
  have hP : 0 ≤ pSq W' W := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [← pSq_eq W' W hW'] at hls
  have hL : ∑ i ∈ t, ‖sB W' W (β i)‖ ^ 2 ≤ ((N : ℝ) - 1 + ν⁻¹) * pSq W' W := hls
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

/-- The pairing code of a triple. -/
def enc (w : ℕ × ℕ × ℕ) : ℕ := Nat.pair w.1 (Nat.pair w.2.1 w.2.2)

/-- Its inverse. -/
def dec (k : ℕ) : ℕ × ℕ × ℕ := (k.unpair.1, k.unpair.2.unpair.1, k.unpair.2.unpair.2)

theorem dec_enc (w : ℕ × ℕ × ℕ) : dec (enc w) = w := by
  simp only [dec, enc, Nat.unpair_pair]

/-- **One block over triples**: `ν`-spaced frequencies indexed by a finset of triples. -/
theorem block_triples (ls : LargeSieve) (W' W ν : ℝ) (hW' : 0 ≤ W') (hν : 0 < ν)
    (hν1 : ν ≤ 1) (D : Finset (ℕ × ℕ × ℕ)) (β : ℕ × ℕ × ℕ → ℝ)
    (hsep : ∀ w ∈ D, ∀ w' ∈ D, w ≠ w' → ∀ n : ℤ, ν ≤ |β w - β w' - n|) :
    ∑ w ∈ D, ‖sB W' W (β w)‖ ^ 2 ≤ (W - W' + ν⁻¹) * pSq W' W := by
  have hinj : Set.InjOn enc D := fun w _ w' _ h => by
    have := congrArg dec h
    rwa [dec_enc, dec_enc] at this
  have h := block_gen ls W' W ν hW' hν hν1 (D.image enc) (fun k => β (dec k)) (by
    intro i hi k hk hik n
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hk
    rw [dec_enc, dec_enc]
    exact hsep w hw w' hw' (fun h => hik (by rw [h])) n)
  rw [Finset.sum_image hinj] at h
  simpa only [dec_enc] using h

/-! ## (2) Spacing of the shifted frequencies `mα + c/r` -/

theorem isCop_nat {a b : ℕ} (h : Nat.Coprime a b) : IsCoprime (a : ℤ) (b : ℤ) :=
  Nat.isCoprime_iff_coprime.mpr h

/-- **Spacing of `mα + c/r`** (`lem:ogor`'s second paragraph): for `2α = A/q + d`, odd
`m, m'`, positive `r, r' ≤ R` coprime to `q`, `c, c'` reduced residues, two distinct
triples give frequencies `≥ ν` apart mod 1, provided `ν + υ ≤ 1/(qR²)`, `|jd| ≤ υ` for the step
`j = (m − m')/2`, and `|jd| ≥ ν` when `q ∣ j ≠ 0`. -/
theorem sep_triple (α : ℝ) (A : ℤ) (q : ℕ) (hq : 1 ≤ q) (hg : Int.gcd A q = 1) (d ν υ R : ℝ)
    (h2a : 2 * α = A / q + d) (m m' r r' c c' : ℕ) (hm : m % 2 = 1) (hm' : m' % 2 = 1)
    (hr : 0 < r) (hr' : 0 < r') (hrR : (r : ℝ) ≤ R) (hr'R : (r' : ℝ) ≤ R) (hcr : c < r)
    (hc'r : c' < r') (hcop : Nat.Coprime c r) (hcop' : Nat.Coprime c' r')
    (hrq : Nat.Coprime r q) (hr'q : Nat.Coprime r' q) (hgap : ν + υ ≤ 1 / (q * R ^ 2))
    (hsmall : ∀ j : ℤ, (m : ℝ) - m' = 2 * j → |(j : ℝ) * d| ≤ υ)
    (hdiv : ∀ j : ℤ, (m : ℝ) - m' = 2 * j → (q : ℤ) ∣ j → j ≠ 0 → ν ≤ |(j : ℝ) * d|)
    (hne : (m, r, c) ≠ (m', r', c')) (n : ℤ) :
    ν ≤ |((m : ℝ) * α + c / r) - ((m' : ℝ) * α + c' / r') - n| := by
  obtain ⟨j, hj⟩ : ∃ j : ℤ, (m : ℤ) - m' = 2 * j := ⟨((m : ℤ) - m') / 2, by omega⟩
  have hjr : (m : ℝ) - m' = 2 * j := by exact_mod_cast hj
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hr'0 : (0 : ℝ) < r' := by exact_mod_cast hr'
  set Num : ℤ := j * A * r * r' + c * q * r' - c' * q * r - n * q * r * r' with hNum
  have key : ((m : ℝ) * α + c / r) - ((m' : ℝ) * α + c' / r') - n =
      (Num : ℝ) / (q * r * r') + j * d := by
    have hma : (m : ℝ) * α - m' * α = j * (A / q + d) := by
      rw [← h2a, ← sub_mul, hjr]
      ring
    rw [show ((m : ℝ) * α + c / r) - ((m' : ℝ) * α + c' / r') - n =
      ((m : ℝ) * α - m' * α) + c / r - c' / r' - n by ring, hma, hNum]
    push_cast
    field_simp
    ring
  rw [key]
  by_cases hN : Num = 0
  · have heq : j * A * r * r' + c * q * r' = c' * q * r + n * q * r * r' := by
      have : Num = 0 := hN
      rw [hNum] at this
      linarith
    have hqj : (q : ℤ) ∣ j := by
      have h1 : (q : ℤ) ∣ j * (A * r * r') :=
        ⟨c' * r + n * r * r' - c * r', by linear_combination heq⟩
      have hcA : IsCoprime (q : ℤ) A := (Int.isCoprime_iff_gcd_eq_one.mpr hg).symm
      have hc : IsCoprime (q : ℤ) (A * r * r') :=
        (hcA.mul_right (isCop_nat hrq).symm).mul_right (isCop_nat hr'q).symm
      exact hc.dvd_of_dvd_mul_right h1
    have hrr : r ∣ r' := by
      have h1 : (r : ℤ) ∣ r' * (c * q) :=
        ⟨c' * q + n * q * r' - j * A * r', by linear_combination heq⟩
      have hc : IsCoprime (r : ℤ) (c * q) := (isCop_nat hcop).symm.mul_right (isCop_nat hrq)
      exact Int.natCast_dvd_natCast.mp (hc.dvd_of_dvd_mul_right h1)
    have hr'r : r' ∣ r := by
      have h1 : (r' : ℤ) ∣ r * (c' * q) :=
        ⟨j * A * r + c * q - n * q * r, by linear_combination (-1 : ℤ) * heq⟩
      have hc : IsCoprime (r' : ℤ) (c' * q) := (isCop_nat hcop').symm.mul_right (isCop_nat hr'q)
      exact Int.natCast_dvd_natCast.mp (hc.dvd_of_dvd_mul_right h1)
    have hrr' : r = r' := Nat.dvd_antisymm hrr hr'r
    subst hrr'
    have heq2 : j * A * r + c * q = c' * q + n * q * r := by
      have hr0' : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne'
      apply mul_right_cancel₀ hr0'
      linear_combination heq
    have hcc : c = c' := by
      have h1 : (r : ℤ) ∣ q * ((c : ℤ) - c') := ⟨n * q - j * A, by linear_combination heq2⟩
      have h2 := (isCop_nat hrq).dvd_of_dvd_mul_left h1
      have h3 : |(c : ℤ) - c'| < r := by
        rw [abs_lt]
        constructor <;> omega
      have := Int.eq_zero_of_abs_lt_dvd h2 h3
      omega
    subst hcc
    have hj0 : j ≠ 0 := by
      rintro rfl
      apply hne
      have : m = m' := by omega
      rw [this]
    rw [hN, Int.cast_zero, zero_div, zero_add]
    exact hdiv j hjr hqj hj0
  · have h1 : (1 : ℝ) ≤ |(Num : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hN
    have hR0 : 0 < R := by linarith
    have hrr : (r : ℝ) * r' ≤ R ^ 2 := by nlinarith
    have hden : 0 < (q : ℝ) * r * r' := by positivity
    have hqR : 0 < (q : ℝ) * R ^ 2 := mul_pos hq0 (pow_pos hR0 2)
    have h2 : 1 / ((q : ℝ) * R ^ 2) ≤ |(Num : ℝ) / (q * r * r')| := by
      rw [abs_div, abs_of_pos hden, le_div_iff₀ hden]
      calc 1 / ((q : ℝ) * R ^ 2) * (q * r * r') ≤ 1 := by
            rw [div_mul_eq_mul_div, one_mul, div_le_one hqR]
            nlinarith
        _ ≤ _ := h1
    have h3 : |(Num : ℝ) / (q * r * r')| ≤ |(Num : ℝ) / (q * r * r') + j * d| + |(j : ℝ) * d| := by
      have := abs_add_le ((Num : ℝ) / (q * r * r') + j * d) (-((j : ℝ) * d))
      rwa [add_neg_cancel_right, abs_neg] at this
    have h4 := hsmall j hjr
    linarith

/-! ## (3) The moduli `r ≤ √T`, `r` square-free coprime to `q`, and `∑ 1/φ(r) ≥ (φ(q)/q)log √T` -/

open Principia.Common.BrunTitchmarshAP
open scoped ArithmeticFunction.zeta

/-- The divisors `l` of the sieve's `P = ∏_{p ≤ T, p ∤ q} p` with `l² ≤ T`: square-free, coprime
to `q`, at most `√T`. -/
noncomputable def rSet (q : ℕ) (T : ℝ) (hT : 1 ≤ T) : Finset ℕ :=
  (apSieve q 0 0 T hT).prodPrimes.divisors.filter (fun l : ℕ => (l : ℝ) ^ 2 ≤ T)

/-- The reduced residues mod `r`. -/
def cSet (r : ℕ) : Finset ℕ := (Finset.range r).filter (fun c => Nat.Coprime c r)

theorem gT_eq (q : ℕ) (T : ℝ) (hT : 1 ≤ T) (l : ℕ) (hl : l ≠ 0) :
    SelbergSieve.selbergTerms (apSieve q 0 0 T hT).toBoundingSieve l =
      1 / (Nat.totient l : ℝ) := by
  rw [SelbergSieve.selbergTerms_apply]
  have hnu : ∀ n : ℕ, n ≠ 0 → (apSieve q 0 0 T hT).nu n = 1 / n := by
    intro n hn
    change ((ζ : ArithmeticFunction ℝ).pdiv .id) n = _
    simp [ArithmeticFunction.pdiv_apply, hn]
  rw [hnu l hl]
  have hp : ∏ p ∈ l.primeFactors, 1 / (1 - (apSieve q 0 0 T hT).nu p) =
      ∏ p ∈ l.primeFactors, 1 / (1 - 1 / (p : ℝ)) :=
    Finset.prod_congr rfl fun p hp => by rw [hnu p (Nat.prime_of_mem_primeFactors hp).ne_zero]
  rw [hp, Finset.prod_div_distrib, Finset.prod_const_one,
    ← totient_div_eq_prod l (Nat.pos_of_ne_zero hl)]
  have h1 : (Nat.totient l : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hl)).ne'
  have h2 : (l : ℝ) ≠ 0 := by exact_mod_cast hl
  field_simp

theorem bsum_eq (q : ℕ) (T : ℝ) (hT : 1 ≤ T) :
    (apSieve q 0 0 T hT).selbergBoundingSum = ∑ l ∈ rSet q T hT, 1 / (Nat.totient l : ℝ) := by
  unfold SelbergSieve.selbergBoundingSum rSet
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl0 : l ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hl)
  have hlev : (apSieve q 0 0 T hT).level = T := rfl
  rw [hlev, gT_eq q T hT l hl0]

/-- **`eq:werst`**: `∑_{r ∈ rSet} 1/φ(r) ≥ (φ(q)/q)·log √T` (the Selberg-sum lower bound of
`BrunTitchmarshAP.boundingSum_ge`). -/
theorem rSet_ge (q : ℕ) (hq : 0 < q) (T : ℝ) (hT : 1 ≤ T) :
    (Nat.totient q : ℝ) / q * Real.log (Real.sqrt T) ≤
      ∑ l ∈ rSet q T hT, 1 / (Nat.totient l : ℝ) := by
  rw [← bsum_eq]
  exact boundingSum_ge q 0 0 T hT hq

theorem mem_rSet {q : ℕ} {T : ℝ} {hT : 1 ≤ T} {l : ℕ} (h : l ∈ rSet q T hT) :
    0 < l ∧ Squarefree l ∧ Nat.Coprime l q ∧ (l : ℝ) ≤ Real.sqrt T := by
  unfold rSet at h
  rw [Finset.mem_filter, Nat.mem_divisors] at h
  obtain ⟨⟨hd, hP⟩, hl2⟩ := h
  exact ⟨Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hP),
    Squarefree.squarefree_of_dvd hd
      (BoundingSieve.prodPrimes_squarefree (apSieve q 0 0 T hT).toBoundingSieve),
    (coprime_of_dvd_prodPrimes q 0 0 T hT hd).symm,
    (Real.le_sqrt (Nat.cast_nonneg l) (by linarith)).mpr hl2⟩

/-! ## (4) `√T ≤ W'`: Montgomery's inequality, then the large sieve over the points `mα + c/r` -/

/-- **Montgomery for one frequency, summed over `r ∈ rSet`**: `G·|S(β)|² ≤ ∑_r ∑_c |S(β + c/r)|²`,
`G = ∑_{r ∈ rSet} 1/φ(r)`; the primes `p > W' ≥ √T ≥ r` are coprime to every `r`. -/
theorem mont_one (mi : MontgomeryIneq) (q : ℕ) (T : ℝ) (hT : 1 ≤ T) (W' W β : ℝ)
    (hRW : Real.sqrt T ≤ W') :
    (∑ l ∈ rSet q T hT, 1 / (Nat.totient l : ℝ)) * ‖sB W' W β‖ ^ 2 ≤
      ∑ r ∈ rSet q T hT, ∑ c ∈ cSet r, ‖sB W' W (β + c / r)‖ ^ 2 := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun r hr => ?_
  obtain ⟨hr0, hsq, -, hrT⟩ := mem_rSet hr
  have hphi : (0 : ℝ) < Nat.totient r := by exact_mod_cast Nat.totient_pos.mpr hr0
  have h : ‖sB W' W β‖ ^ 2 ≤
      (Nat.totient r : ℝ) * ∑ c ∈ cSet r, ‖sB W' W (β + c / r)‖ ^ 2 :=
    mi r hsq ⌊W'⌋₊ (⌊W⌋₊ - ⌊W'⌋₊) bP β (fun n hn hnc => by
      unfold bP
      rw [if_neg]
      intro hp
      apply hnc
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro hdvd
      have h1 : n ≤ r := Nat.le_of_dvd hr0 hdvd
      have h2 : ⌊W'⌋₊ < n := (Finset.mem_Ioc.mp hn).1
      have h3 : W' < n := by
        have := Nat.lt_floor_add_one W'
        have : (⌊W'⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast h2
        linarith
      have h4 : (n : ℝ) ≤ r := by exact_mod_cast h1
      linarith)
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hphi]
  linarith

/-- **`lem:ogor`'s Montgomery branch, on `√T ≤ W'`** (`T = (x/|δ|q)/(q + x/4W)`, so that
`1/(qT) = ν + υ`, `ν = q|δ|/x`, `υ = |δ|/4W`): `S₂ ≤ (q/φ(q))/log √T·(x/|δ|q + W/2)·∑(log p)²`. -/
theorem mont_case (mi : MontgomeryIneq) (ls : LargeSieve) (x W W' U' Q α δ : ℝ) (A : ℤ)
    (q : ℕ) (hW : 117 ≤ W) (hWx : W ≤ x) (hW' : W / 2 ≤ W') (hq : 1 ≤ q)
    (hg : Int.gcd A q = 1) (h2a : 2 * α = A / q + δ / x) (hδ : |δ / x| ≤ 1 / (q * Q))
    (hqQ : (q : ℝ) ≤ Q) (hδ0 : δ ≠ 0) (hst : x / (4 * W) + q < x / (|δ| * q))
    (hRW : Real.sqrt (x / (|δ| * q) / (q + x / (4 * W))) ≤ W') :
    s2 x α U' W' W ≤ (q : ℝ) / Nat.totient q /
      Real.log (Real.sqrt (x / (|δ| * q) / (q + x / (4 * W)))) *
        (x / (|δ| * q) + W / 2) * pSq W' W := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hW0 : 0 < W := by linarith
  have hx0 : 0 < x := by linarith
  have hA : 0 < |δ| := abs_pos.mpr hδ0
  have hδx : |δ / x| = |δ| / x := by rw [abs_div, abs_of_pos hx0]
  have hc0p : 0 < (q : ℝ) + x / (4 * W) := by positivity
  set T := x / (|δ| * q) / (q + x / (4 * W)) with hTdef
  have hT1 : 1 < T := by
    rw [hTdef, lt_div_iff₀ hc0p, one_mul]
    linarith
  have hT1' : (1 : ℝ) ≤ T := hT1.le
  set R := Real.sqrt T with hRdef
  have hR1 : 1 < R := by
    rw [hRdef]
    exact (Real.lt_sqrt zero_le_one).mpr (by rw [one_pow]; exact hT1)
  have hlogR : 0 < Real.log R := Real.log_pos hR1
  have hν : 0 < (q : ℝ) * |δ| / x := by positivity
  have hν1 : (q : ℝ) * |δ| / x ≤ 1 := by
    have hQ0 : 0 < Q := by linarith
    have h1 : (q : ℝ) * (|δ| / x) ≤ q * (1 / (q * Q)) :=
      mul_le_mul_of_nonneg_left (hδx ▸ hδ) hq0.le
    have h2 : (q : ℝ) * (1 / (q * Q)) = 1 / Q := by field_simp
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have h3 : 1 / Q ≤ 1 := by rw [div_le_one hQ0]; linarith
    calc (q : ℝ) * |δ| / x = q * (|δ| / x) := by ring
      _ ≤ 1 := by linarith
  have hgap : (q : ℝ) * |δ| / x + |δ| / (4 * W) ≤ 1 / (q * R ^ 2) := by
    rw [hRdef, Real.sq_sqrt (by linarith), hTdef]
    refine le_of_eq ?_
    field_simp
  have hphiq : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  set G := ∑ l ∈ rSet q T hT1', 1 / (Nat.totient l : ℝ) with hGdef
  have hG : (Nat.totient q : ℝ) / q * Real.log R ≤ G := rSet_ge q hq T hT1'
  have hW'0 : 0 ≤ W' := by linarith
  set D := M2C.dep (mSet x U' W) (fun _ => M2C.dep (rSet q T hT1') cSet) with hD
  have hstep : G * s2 x α U' W' W ≤
      ∑ w ∈ D, ‖sB W' W ((w.1 : ℝ) * α + (w.2.2 : ℝ) / (w.2.1 : ℝ))‖ ^ 2 := by
    unfold s2
    rw [Finset.mul_sum]
    calc ∑ m ∈ mSet x U' W, G * ‖pS α W' W m‖ ^ 2
        ≤ ∑ m ∈ mSet x U' W, ∑ r ∈ rSet q T hT1', ∑ c ∈ cSet r,
            ‖sB W' W ((m : ℝ) * α + c / r)‖ ^ 2 :=
          Finset.sum_le_sum fun m _ => by
            rw [pS_eq_sB α W' W hW'0 m]
            exact mont_one mi q T hT1' W' W _ hRW
      _ = _ := by
          rw [hD, ← M2C.sum_dep]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [← M2C.sum_dep]
  have hls := block_triples ls W' W ((q : ℝ) * |δ| / x) hW'0 hν hν1 D
    (fun w => (w.1 : ℝ) * α + (w.2.2 : ℝ) / (w.2.1 : ℝ)) (by
      rintro ⟨m, r, c⟩ hw ⟨m', r', c'⟩ hw' hne n
      simp only [hD, M2C.mem_dep] at hw hw'
      obtain ⟨hm, hr, hc⟩ := hw
      obtain ⟨hm', hr', hc'⟩ := hw'
      obtain ⟨hr0, -, hrq, hrR⟩ := mem_rSet hr
      obtain ⟨hr0', -, hr'q, hr'R⟩ := mem_rSet hr'
      unfold cSet at hc hc'
      rw [Finset.mem_filter, Finset.mem_range] at hc hc'
      have hcl := mSet_close hm hm' hW0
      refine sep_triple α A q hq hg (δ / x) ((q : ℝ) * |δ| / x) (|δ| / (4 * W)) R h2a m m' r r'
        c c' (mem_mSet hm).1 (mem_mSet hm').1 hr0 hr0' hrR hr'R hc.1 hc'.1 hc.2 hc'.2 hrq hr'q
        hgap (fun j hj => ?_) (fun j hj hd hj0 => ?_) hne n
      · rw [hj, abs_mul, abs_two] at hcl
        have hjb : |(j : ℝ)| ≤ x / (4 * W) := by
          have : x / (2 * W) = 2 * (x / (4 * W)) := by field_simp; ring
          linarith
        rw [abs_mul, hδx]
        calc |(j : ℝ)| * (|δ| / x) ≤ x / (4 * W) * (|δ| / x) :=
              mul_le_mul_of_nonneg_right hjb (by positivity)
          _ = |δ| / (4 * W) := by field_simp
      · have hqj := q_le_abs q j hj0 hd
        rw [abs_mul, hδx]
        calc (q : ℝ) * |δ| / x = q * (|δ| / x) := by ring
          _ ≤ |(j : ℝ)| * (|δ| / x) := mul_le_mul_of_nonneg_right hqj (by positivity))
  have hP : 0 ≤ pSq W' W := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hinv : ((q : ℝ) * |δ| / x)⁻¹ = x / (|δ| * q) := by
    rw [inv_div, mul_comm]
  rw [hinv] at hls
  have hbig : G * s2 x α U' W' W ≤ (x / (|δ| * q) + W / 2) * pSq W' W := by
    refine (hstep.trans hls).trans (mul_le_mul_of_nonneg_right ?_ hP)
    linarith
  have hS0 : 0 ≤ s2 x α U' W' W := s2_nonneg _ _ _ _ _
  have hkey : (Nat.totient q : ℝ) / q * Real.log R * s2 x α U' W' W ≤
      (x / (|δ| * q) + W / 2) * pSq W' W :=
    (mul_le_mul_of_nonneg_right hG hS0).trans hbig
  have hpos : 0 < (Nat.totient q : ℝ) / q * Real.log R := by positivity
  have e1 : (q : ℝ) / Nat.totient q / Real.log R * (x / (|δ| * q) + W / 2) * pSq W' W =
      (x / (|δ| * q) + W / 2) * pSq W' W / ((Nat.totient q : ℝ) / q * Real.log R) := by
    field_simp
  rw [e1, le_div_iff₀ hpos]
  linarith

/-! ## (5) `√T > W'`: the trivial bound wins -/

/-- **The trivial bound**: `S₂ ≤ (x/4W + 1)(W/2 + 1)·∑(log p)²` (at most `x/4W + 1` odd `m`,
Cauchy–Schwarz over at most `W/2 + 1` integers `n`). -/
theorem triv_bd (x W W' U' α : ℝ) (hW : 117 ≤ W) (hWx : W ≤ x) (hW' : W / 2 ≤ W') :
    s2 x α U' W' W ≤ (x / (4 * W) + 1) * (W / 2 + 1) * pSq W' W := by
  have hW0 : 0 < W := by linarith
  have hx0 : 0 < x := by linarith
  have hW'0 : 0 ≤ W' := by linarith
  set N := ⌊W⌋₊ - ⌊W'⌋₊ with hNdef
  have hP : 0 ≤ pSq W' W := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hf : ∀ m : ℕ, ‖pS α W' W m‖ ^ 2 ≤ (N : ℝ) * pSq W' W := by
    intro m
    rw [pS_eq α W' W hW'0 m, pSq_eq W' W hW'0]
    exact one_bd _ _ bP _
  have hN : (N : ℝ) ≤ W / 2 + 1 := by
    rcases le_total ⌊W'⌋₊ ⌊W⌋₊ with h | h
    · rw [hNdef, Nat.cast_sub h]
      have := Nat.floor_le hW0.le
      have := Nat.lt_floor_add_one W'
      linarith
    · rw [hNdef, Nat.sub_eq_zero_of_le h, Nat.cast_zero]
      linarith
  have hNP : 0 ≤ (N : ℝ) * pSq W' W := mul_nonneg (Nat.cast_nonneg N) hP
  have h := sum_blocks (mSet x U' W) (fun m => ‖pS α W' W m‖ ^ 2) (max (x / (2 * W)) U')
    (x / (2 * W)) 2 ((N : ℝ) * pSq W' W) two_pos (by positivity) hNP
    (fun m hm => mSet_range hW0 m hm) (by
      intro t ht hdiam
      have hcard : t.card ≤ 1 := by
        refine Finset.card_le_one.mpr fun m hm m' hm' => ?_
        have h1 := (mem_mSet (ht hm)).1
        have h2 := (mem_mSet (ht hm')).1
        have hd := hdiam m hm m' hm'
        rw [abs_sub_lt_iff] at hd
        have e1 : m < m' + 2 := by
          have : (m : ℝ) < m' + 2 := by linarith [hd.1]
          exact_mod_cast this
        have e2 : m' < m + 2 := by
          have : (m' : ℝ) < m + 2 := by linarith [hd.2]
          exact_mod_cast this
        omega
      obtain ⟨m0, hm0⟩ := Finset.card_le_one_iff_subset_singleton.mp hcard
      calc ∑ m ∈ t, ‖pS α W' W m‖ ^ 2 ≤ ∑ m ∈ {m0}, ‖pS α W' W m‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hm0 fun _ _ _ => sq_nonneg _
        _ ≤ (N : ℝ) * pSq W' W := by rw [Finset.sum_singleton]; exact hf m0)
  calc s2 x α U' W' W = ∑ m ∈ mSet x U' W, ‖pS α W' W m‖ ^ 2 := rfl
    _ ≤ (x / (2 * W) / 2 + 1) * ((N : ℝ) * pSq W' W) := h
    _ = (x / (4 * W) + 1) * ((N : ℝ) * pSq W' W) := by
        congr 2
        field_simp
        ring
    _ ≤ (x / (4 * W) + 1) * ((W / 2 + 1) * pSq W' W) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hN hP) (by positivity)
    _ = _ := by ring

/-- `log T ≤ √T` (from `log(√T/2) ≤ √T/2 − 1` and `log 2 < 1`). -/
theorem log_le_sqrt (T : ℝ) (hT : 0 < T) : Real.log T ≤ Real.sqrt T := by
  have hR : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have h1 := Real.log_le_sub_one_of_pos (half_pos hR)
  rw [Real.log_div hR.ne' two_ne_zero] at h1
  have h2 : Real.log T = 2 * Real.log (Real.sqrt T) := by
    rw [Real.log_sqrt hT.le]
    ring
  have h3 := Real.log_two_lt_d9
  linarith

/-- **`T2K.Procida2Mont`, PROVED** from Montgomery's inequality and the large sieve, with the
case split the book omits: on `√T ≤ W'` (`T = (x/|δ|q)/(q + x/4W)`) `lem:ogor`'s argument
(`mont_case`); on `√T > W'` the trivial bound (`triv_bd`), since then
`(W/2 + 1)·log T ≤ 2T` and `x/4W + 1 ≤ q + x/4W`. -/
theorem procida2Mont_holds (mi : MontgomeryIneq) (ls : LargeSieve) : Procida2Mont := by
  intro x W W' U' Q α δ a q hW hWx hW' hU' hq hg h2a hδ hqQ hδ0 hst
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hW0 : 0 < W := by linarith
  have hx0 : 0 < x := by linarith
  have hA : 0 < |δ| := abs_pos.mpr hδ0
  have hc0p : 0 < (q : ℝ) + x / (4 * W) := by positivity
  set Q' := x / (|δ| * q) with hQ'
  set c0 := (q : ℝ) + x / (4 * W) with hc0
  set T := Q' / c0 with hTdef
  have hT1 : 1 < T := by
    rw [hTdef, lt_div_iff₀ hc0p, one_mul]
    linarith
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT1
  have hP : 0 ≤ pSq W' W := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hphiq : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hqphi : (1 : ℝ) ≤ (q : ℝ) / Nat.totient q := by
    rw [le_div_iff₀ hphiq, one_mul]
    exact_mod_cast Nat.totient_le q
  by_cases hR : Real.sqrt T ≤ W'
  · have h : s2 x α U' W' W ≤ (q : ℝ) / Nat.totient q / Real.log (Real.sqrt T) *
        (Q' + W / 2) * pSq W' W :=
      mont_case mi ls x W W' U' Q α δ a q hW hWx hW' hq hg h2a hδ hqQ hδ0 hst hR
    refine h.trans (le_of_eq ?_)
    rw [Real.log_sqrt hT0.le]
    field_simp
  · replace hR := not_le.mp hR
    refine (triv_bd x W W' U' α hW hWx hW').trans (mul_le_mul_of_nonneg_right ?_ hP)
    set R := Real.sqrt T with hRdef
    have hR0 : 0 < R := Real.sqrt_pos.mpr hT0
    have hRR : R ^ 2 = T := Real.sq_sqrt hT0.le
    have hlog := log_le_sqrt T hT0
    have hQT : Q' = c0 * T := by
      rw [hTdef]
      field_simp
    have h1 : (W / 2 + 1) * Real.log T ≤ 2 * T := by
      have hR1 : 1 ≤ R := by nlinarith
      nlinarith
    have h2 : x / (4 * W) + 1 ≤ c0 := by
      have : (1 : ℝ) ≤ q := by exact_mod_cast hq
      linarith
    have h4 : (x / (4 * W) + 1) * (W / 2 + 1) * Real.log T ≤ 2 * Q' := by
      rw [hQT]
      have hx4 : 0 ≤ x / (4 * W) + 1 := by positivity
      calc (x / (4 * W) + 1) * (W / 2 + 1) * Real.log T
          = (x / (4 * W) + 1) * ((W / 2 + 1) * Real.log T) := by ring
        _ ≤ c0 * (2 * T) :=
            mul_le_mul h2 h1 (by positivity) hc0p.le
        _ = 2 * (c0 * T) := by ring
    have h5 : (x / (4 * W) + 1) * (W / 2 + 1) ≤ 2 * Q' / Real.log T := by
      rw [le_div_iff₀ hL]
      exact h4
    refine h5.trans ?_
    have hQ'0 : 0 ≤ Q' := by positivity
    rw [div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hL.le
    nlinarith

/-- **`T2S.Kraken` from the large sieve, Montgomery's inequality and `Garn1a`, PROVED**
(`T2K.kraken_of_ls` with `procida2Mont_holds`). -/
theorem kraken_of_mont (ls : LargeSieve) (mi : MontgomeryIneq) (g2 : Garn1a) : Kraken :=
  kraken_of_ls ls g2 (procida2Mont_holds mi ls)

end Principia.Common.TernaryGoldbach.T2M
