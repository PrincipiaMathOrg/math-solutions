/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIIProcidaMont

set_option autoImplicit false

/-!
# `T2X.Garn1a` spined: one block, then Montgomery + the weighted large sieve + ONE weight sum

`T2X.Garn1a` (`eq:garn1a`, `q < W/2`, `Q ≥ 3.5W`) is proved in the book (`prop:kraken`,
`minarcs.tex` 3655-3700) from `eq:pokor2b` on blocks of `q` consecutive odd `m`, and `eq:pokor2b`
(`lem:kastor2` ← `lem:kastor1`, 3401-3627) from Montgomery's inequality, the Montgomery–Vaughan
weighted large sieve, and a lower bound for `∑_{r ≤ R} (N + (3/2)(1/qrR − 1/Q)⁻¹)⁻¹μ²(r)/φ(r)`.

```
 Pokor2B          one block: ∑_{m ∈ t}|S(mα)|² ≤ (q/φ(q))·W/log(W/2q)·∑(log p)²       LINK
 garn1a_of_pokor  : Pokor2B → T2X.Garn1a   (blocks of 2q, T2K.sum_blocks)           PROVED
 MVWeighted       NAMED literature: Montgomery–Vaughan 1973, Theorem 1, eq. (1.6)
 WeightLB         the weight sum of eq:malheur ≥ (φ(q)/q)·log(W/2q)/W              LINK
 sep_w            distinct (m, r, c) in a block: ‖Δ(mα + c/r)‖ ≥ 1/qrR − 1/Q         PROVED
 wblock_triples   the weighted large sieve over triples                           PROVED
 pokor2B_of_links : MontgomeryIneq → MVWeighted → WeightLB → Pokor2B              PROVED
 kraken_of_weight : LargeSieve → MontgomeryIneq → MVWeighted → WeightLB → Kraken  PROVED
```

**Finding (the book's `eq:pokor2` derivation, `minarcs.tex` 3489-3580).** It applies the weighted
large sieve with the interval length `W − W' ≤ W/2` in place of `N`, the number of integers in
`(W', W]`, which is `⌊W⌋ − ⌊W'⌋` and can be `(W + 1)/2` (e.g. `W = 119`, `W' = 59.5`: `N = 60`).
Its chain has ZERO slack at its choice `R = (0.30285·W/q)^{1/2}` (`3σ/(1 − σ/3.5) = 0.9946`, MV
Lemma 8's `0.25068` with margin `1.1·10⁻⁶` at `R = 5`), so the `+1/2` is not absorbed as printed.
`WeightLB` states the needed bound with the TRUE `N` and an existential `R`; at the best `R` it
holds on every point checked (`scratchpad/weight_test.py`, `weight_test2.py`: worst margin
`5.9%` at `W = 2.8·10⁶`, `q = 1`, decaying like `1/log W` but positive: asymptotically
`∑_{r ≤ R} μ²/φ ≈ log R + 1.3325`, not MV Lemma 8's `log R + 0.25068`). `eq:pokor2b` itself has
margin `≥ 2×` numerically (`scratchpad/pokor_test.py`: worst ratio `0.48`).
-/

namespace Principia.Common.TernaryGoldbach.T2G

open Principia.Common.Goldbach
open Principia.Common.TernaryGoldbach.T2S Principia.Common.TernaryGoldbach.T2X
open Principia.Common.TernaryGoldbach.T2K

/-- **Link [Pokor2B] — `eq:pokor2b`, one block** (`minarcs.tex` 3587-3627 via `lem:kastor1`
3401-3584): `q < W/2`, `Q ≥ 3.5W`; any set `t` of odd `m` at mutual distance `< 2q` (so inside
one block of `q` consecutive odd numbers) has
`∑_{m ∈ t} |∑_{W'<p≤W} (log p) e(αmp)|² ≤ (q/φ(q))·W/log(W/2q)·∑(log p)²`. OPEN. -/
def Pokor2B : Prop :=
  ∀ x W W' Q α δ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 117 ≤ W → W ≤ x → W / 2 ≤ W' → 1 ≤ q →
    Int.gcd a q = 1 → 2 * α = a / q + δ / x → |δ / x| ≤ 1 / (q * Q) → (q : ℝ) ≤ Q →
      (q : ℝ) < W / 2 → 3.5 * W ≤ Q →
        ∀ t : Finset ℕ, (∀ m ∈ t, m % 2 = 1) → (∀ m ∈ t, ∀ m' ∈ t, |(m : ℝ) - m'| < 2 * q) →
          ∑ m ∈ t, ‖pS α W' W m‖ ^ 2 ≤
            (q : ℝ) / Nat.totient q * W / Real.log (W / (2 * q)) * pSq W' W

/-- **`T2X.Garn1a` from `Pokor2B`, PROVED** (`prop:kraken`'s proof of `eq:garn1a`: blocks of
length `2q`, `(x/2W)/(2q) + 1` of them, `T2K.sum_blocks`). -/
theorem garn1a_of_pokor (pk : Pokor2B) : Garn1a := by
  intro x W W' U' Q α δ a q hW hWx hW' hU' hq hg h2a hδ hqQ hqW hQW
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hW0 : 0 < W := by linarith
  have hx0 : 0 < x := by linarith
  have hphi : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hL : 0 < Real.log (W / (2 * q)) := Real.log_pos (by
    rw [lt_div_iff₀ (by positivity)]
    linarith)
  have hP : 0 ≤ pSq W' W := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hC : 0 ≤ (q : ℝ) / Nat.totient q * W / Real.log (W / (2 * q)) * pSq W' W := by
    positivity
  have hsum := sum_blocks (mSet x U' W) (fun m => ‖pS α W' W m‖ ^ 2) (max (x / (2 * W)) U')
    (x / (2 * W)) (2 * q) _ (by positivity) (by positivity) hC (mSet_range hW0)
    (fun t hts hdiam => pk x W W' Q α δ a q hW hWx hW' hq hg h2a hδ hqQ hqW hQW t
      (fun m hm => (mem_mSet (hts hm)).1) hdiam)
  refine hsum.trans (le_of_eq ?_)
  field_simp
  ring

/-- **`T2S.Kraken` from the large sieve, Montgomery's inequality and `Pokor2B`, PROVED**. -/
theorem kraken_of_pokor (ls : LargeSieve) (mi : T2M.MontgomeryIneq) (pk : Pokor2B) : Kraken :=
  T2M.kraken_of_mont ls mi (garn1a_of_pokor pk)

/-! ## `Pokor2B` from Montgomery's inequality, the weighted large sieve and one weight sum -/

/-- **NAMED (literature) — the large sieve with weights** (H. L. Montgomery and R. C. Vaughan,
*The large sieve*, Mathematika 20 (1973), 119-134, Theorem 1, eq. (1.6); cited by the book in
`lem:kastor1` as `\cite[(1.6)]{MR0374060}`): for points `β_r` and `δ_r > 0` with
`‖β_r − β_s‖ ≥ δ_r` (`s ≠ r`), `∑_r (N + (3/2)δ_r⁻¹)⁻¹·|∑_{M<n≤M+N} b_n e(nβ_r)|² ≤ ∑|b_n|²`.
Stated WEAKER than (1.6): `δ_r` any positive lower bound for the distance from `β_r` to the
other points (MV take the minimum), points indexed by a finite set of naturals. -/
def MVWeighted : Prop :=
  ∀ (R : Finset ℕ) (β δ : ℕ → ℝ), (∀ r ∈ R, 0 < δ r) →
    (∀ r ∈ R, ∀ s ∈ R, r ≠ s → ∀ n : ℤ, δ r ≤ |β r - β s - n|) →
    ∀ (M N : ℕ) (b : ℕ → ℂ),
      ∑ r ∈ R, ((N : ℝ) + 3 / 2 * (δ r)⁻¹)⁻¹ *
          ‖∑ n ∈ Finset.Ioc M (M + N), b n * e (n * β r)‖ ^ 2 ≤
        ∑ n ∈ Finset.Ioc M (M + N), ‖b n‖ ^ 2

/-- The moduli of `lem:kastor1`: square-free `r ≤ R` coprime to `q`. -/
noncomputable def rS (q : ℕ) (R : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊R⌋₊).filter (fun r => Squarefree r ∧ Nat.Coprime r q)

/-- **Link [WeightLB] — the weight sum of `eq:malheur`** (`minarcs.tex` 3489-3580): with
`N = ⌊W⌋ − ⌊W'⌋` (the length of the prime range as an `Ioc`), some `R ≤ W'` with `qR² < Q` gives
`∑_{r ≤ R sq-free, (r,q)=1} (N + (3/2)(1/qrR − 1/Q)⁻¹)⁻¹/φ(r) ≥ (φ(q)/q)·log(W/2q)/W`.
OPEN. The book proves it with `N` replaced by `W/2` (false by up to `1/2`: `⌊W⌋ − ⌊W/2⌋` can be
`(W + 1)/2`), MV Lemma 8 above `R = 100` and `HC.MV8SmallCited` below, with ZERO slack at its
choice `R = (0.30285W/q)^{1/2}`; with the true `N` and the best `R` it holds with margin `≥ 8.6%`
on the grid checked (`scratchpad/weight_test.py`). -/
def WeightLB : Prop :=
  ∀ W W' Q : ℝ, ∀ q : ℕ, 117 ≤ W → W / 2 ≤ W' → W' < W → 1 ≤ q → (q : ℝ) < W / 2 →
    3.5 * W ≤ Q →
      ∃ R : ℝ, 1 ≤ R ∧ R ≤ W' ∧ (q : ℝ) * R ^ 2 < Q ∧
        (Nat.totient q : ℝ) / q * Real.log (W / (2 * q)) / W ≤
          ∑ r ∈ rS q R, ((((⌊W⌋₊ - ⌊W'⌋₊ : ℕ)) : ℝ) +
            3 / 2 * (1 / ((q : ℝ) * r * R) - 1 / Q)⁻¹)⁻¹ / Nat.totient r

/-- **Spacing for `lem:kastor1`**: two distinct `(m, r, c)` in one block (`|m − m'| < 2q`) give
`‖(mα + c/r) − (m'α + c'/r')‖ ≥ 1/(qrR) − 1/Q` (`r' ≤ R`, `|jd| ≤ 1/Q`; `q ∣ j` forces
`j = 0`). -/
theorem sep_w (α : ℝ) (A : ℤ) (q : ℕ) (hq : 1 ≤ q) (hg : Int.gcd A q = 1) (d Qv R : ℝ)
    (h2a : 2 * α = A / q + d) (m m' r r' c c' : ℕ) (hm : m % 2 = 1) (hm' : m' % 2 = 1)
    (hr : 0 < r) (hr' : 0 < r') (hr'R : (r' : ℝ) ≤ R) (hcr : c < r)
    (hc'r : c' < r') (hcop : Nat.Coprime c r) (hcop' : Nat.Coprime c' r')
    (hrq : Nat.Coprime r q) (hr'q : Nat.Coprime r' q)
    (hsmall : ∀ j : ℤ, (m : ℝ) - m' = 2 * j → |(j : ℝ) * d| ≤ 1 / Qv)
    (hdiv : ∀ j : ℤ, (m : ℝ) - m' = 2 * j → (q : ℤ) ∣ j → j = 0)
    (hne : (m, r, c) ≠ (m', r', c')) (n : ℤ) :
    1 / ((q : ℝ) * r * R) - 1 / Qv ≤ |((m : ℝ) * α + c / r) - ((m' : ℝ) * α + c' / r') - n| := by
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
  · exfalso
    have heq : j * A * r * r' + c * q * r' = c' * q * r + n * q * r * r' := by
      have : Num = 0 := hN
      rw [hNum] at this
      linarith
    have hqj : (q : ℤ) ∣ j := by
      have h1 : (q : ℤ) ∣ j * (A * r * r') :=
        ⟨c' * r + n * r * r' - c * r', by linear_combination heq⟩
      have hcA : IsCoprime (q : ℤ) A := (Int.isCoprime_iff_gcd_eq_one.mpr hg).symm
      have hc : IsCoprime (q : ℤ) (A * r * r') :=
        (hcA.mul_right (T2M.isCop_nat hrq).symm).mul_right (T2M.isCop_nat hr'q).symm
      exact hc.dvd_of_dvd_mul_right h1
    have hj0 := hdiv j hjr hqj
    have hrr : r ∣ r' := by
      have h1 : (r : ℤ) ∣ r' * (c * q) :=
        ⟨c' * q + n * q * r' - j * A * r', by linear_combination heq⟩
      have hc : IsCoprime (r : ℤ) (c * q) :=
        (T2M.isCop_nat hcop).symm.mul_right (T2M.isCop_nat hrq)
      exact Int.natCast_dvd_natCast.mp (hc.dvd_of_dvd_mul_right h1)
    have hr'r : r' ∣ r := by
      have h1 : (r' : ℤ) ∣ r * (c' * q) :=
        ⟨j * A * r + c * q - n * q * r, by linear_combination (-1 : ℤ) * heq⟩
      have hc : IsCoprime (r' : ℤ) (c' * q) :=
        (T2M.isCop_nat hcop').symm.mul_right (T2M.isCop_nat hr'q)
      exact Int.natCast_dvd_natCast.mp (hc.dvd_of_dvd_mul_right h1)
    have hrr' : r = r' := Nat.dvd_antisymm hrr hr'r
    subst hrr'
    have heq2 : j * A * r + c * q = c' * q + n * q * r := by
      have hr0' : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne'
      apply mul_right_cancel₀ hr0'
      linear_combination heq
    have hcc : c = c' := by
      have h1 : (r : ℤ) ∣ q * ((c : ℤ) - c') := ⟨n * q - j * A, by linear_combination heq2⟩
      have h2 := (T2M.isCop_nat hrq).dvd_of_dvd_mul_left h1
      have h3 : |(c : ℤ) - c'| < r := by
        rw [abs_lt]
        constructor <;> omega
      have := Int.eq_zero_of_abs_lt_dvd h2 h3
      omega
    subst hcc
    apply hne
    have : m = m' := by omega
    rw [this]
  · have h1 : (1 : ℝ) ≤ |(Num : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hN
    have hden : 0 < (q : ℝ) * r * r' := by positivity
    have hR0 : 0 < R := by linarith
    have hqrR : 0 < (q : ℝ) * r * R := by positivity
    have h2 : 1 / ((q : ℝ) * r * R) ≤ |(Num : ℝ) / (q * r * r')| := by
      rw [abs_div, abs_of_pos hden, le_div_iff₀ hden]
      calc 1 / ((q : ℝ) * r * R) * (q * r * r') ≤ 1 := by
            rw [div_mul_eq_mul_div, one_mul, div_le_one hqrR]
            exact mul_le_mul_of_nonneg_left hr'R (by positivity)
        _ ≤ _ := h1
    have h3 : |(Num : ℝ) / (q * r * r')| ≤
        |(Num : ℝ) / (q * r * r') + j * d| + |(j : ℝ) * d| := by
      have := abs_add_le ((Num : ℝ) / (q * r * r') + j * d) (-((j : ℝ) * d))
      rwa [add_neg_cancel_right, abs_neg] at this
    have h4 := hsmall j hjr
    linarith

/-- **The weighted large sieve over triples** (`Nat.pair` encoding, as `T2M.block_triples`). -/
theorem wblock_triples (mv : MVWeighted) (W' W : ℝ) (hW' : 0 ≤ W') (D : Finset (ℕ × ℕ × ℕ))
    (β δ : ℕ × ℕ × ℕ → ℝ) (hδ : ∀ w ∈ D, 0 < δ w)
    (hsep : ∀ w ∈ D, ∀ w' ∈ D, w ≠ w' → ∀ n : ℤ, δ w ≤ |β w - β w' - n|) :
    ∑ w ∈ D, ((((⌊W⌋₊ - ⌊W'⌋₊ : ℕ)) : ℝ) + 3 / 2 * (δ w)⁻¹)⁻¹ * ‖T2M.sB W' W (β w)‖ ^ 2 ≤
      pSq W' W := by
  have hinj : Set.InjOn T2M.enc D := fun w _ w' _ h => by
    have := congrArg T2M.dec h
    rwa [T2M.dec_enc, T2M.dec_enc] at this
  have h := mv (D.image T2M.enc) (fun k => β (T2M.dec k)) (fun k => δ (T2M.dec k))
    (by
      intro k hk
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hk
      rw [T2M.dec_enc]
      exact hδ w hw)
    (by
      intro i hi k hk hik n
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hk
      simp only [T2M.dec_enc]
      exact hsep w hw w' hw' (fun h => hik (by rw [h])) n)
    ⌊W'⌋₊ (⌊W⌋₊ - ⌊W'⌋₊) bP
  rw [Finset.sum_image hinj] at h
  rw [pSq_eq W' W hW']
  simp only [T2M.dec_enc] at h
  exact h

/-- `pS` and `pSq` vanish when `W' ≥ W` (no prime in `(W', W]`). -/
theorem pS_empty (α W' W : ℝ) (h : W ≤ W') (hW : 0 ≤ W) (m : ℕ) :
    pS α W' W m = 0 ∧ pSq W' W = 0 := by
  have hE : (Finset.Icc 1 ⌊W⌋₊).filter (fun p : ℕ => p.Prime ∧ W' < (p : ℝ)) = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    have h1 : (p : ℝ) ≤ W := le_trans (Nat.cast_le.mpr hp.1.2) (Nat.floor_le hW)
    linarith [hp.2.2]
  unfold pS pSq
  rw [hE]
  simp

/-- **`Pokor2B` from Montgomery's inequality, the weighted large sieve and `WeightLB`,
PROVED** (`lem:kastor1`'s argument with the true `N = ⌊W⌋ − ⌊W'⌋`): `G·∑_{m ∈ t}|S(mα)|² ≤
∑_{(m,r,c)} ω_r|S(mα + c/r)|² ≤ ∑(log p)²`, `ω_r = (N + (3/2)(1/qrR − 1/Q)⁻¹)⁻¹`,
`G = ∑_r ω_r/φ(r) ≥ (φ(q)/q)log(W/2q)/W`. -/
theorem pokor2B_of_links (mi : T2M.MontgomeryIneq) (mv : MVWeighted) (wl : WeightLB) :
    Pokor2B := by
  intro x W W' Q α δ a q hW hWx hW' hq hg h2a hδ hqQ hqW hQW t hodd hdiam
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hW0 : 0 < W := by linarith
  have hx0 : 0 < x := by linarith
  have hQ0 : 0 < Q := by linarith
  have hW'0 : 0 ≤ W' := by linarith
  have hphi : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hL : 0 < Real.log (W / (2 * q)) := Real.log_pos (by
    rw [lt_div_iff₀ (by positivity)]
    linarith)
  have hP : 0 ≤ pSq W' W := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rcases lt_or_ge W' W with hWW | hWW
  · obtain ⟨R, hR1, hRW, hqR, hG⟩ := wl W W' Q q hW hW' hWW hq hqW hQW
    set N : ℕ := ⌊W⌋₊ - ⌊W'⌋₊ with hN
    set ω : ℕ → ℝ := fun r => ((N : ℝ) + 3 / 2 * (1 / ((q : ℝ) * r * R) - 1 / Q)⁻¹)⁻¹ with hω
    have hR0 : 0 < R := by linarith
    have hδr : ∀ r ∈ rS q R, 0 < 1 / ((q : ℝ) * r * R) - 1 / Q := by
      intro r hr
      have hr' := (Finset.mem_filter.mp hr).1
      rw [Finset.mem_Icc] at hr'
      have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr'.1
      have hrR : (r : ℝ) ≤ R := le_trans (Nat.cast_le.mpr hr'.2) (Nat.floor_le hR0.le)
      have : (q : ℝ) * r * R < Q := by nlinarith
      rw [sub_pos]
      exact one_div_lt_one_div_of_lt (by positivity) this
    have hω0 : ∀ r ∈ rS q R, 0 ≤ ω r := by
      intro r hr
      have := hδr r hr
      simp only [hω]
      positivity
    set G := ∑ r ∈ rS q R, ω r / Nat.totient r with hGdef
    have hT0 : 0 < (Nat.totient q : ℝ) / q * Real.log (W / (2 * q)) / W := by positivity
    have hG0 : 0 < G := lt_of_lt_of_le hT0 hG
    have hmont : ∀ m : ℕ, G * ‖pS α W' W m‖ ^ 2 ≤
        ∑ r ∈ rS q R, ∑ c ∈ T2M.cSet r, ω r * ‖T2M.sB W' W ((m : ℝ) * α + c / r)‖ ^ 2 := by
      intro m
      rw [T2M.pS_eq_sB α W' W hW'0 m, hGdef, Finset.sum_mul]
      refine Finset.sum_le_sum fun r hr => ?_
      have hrm := Finset.mem_filter.mp hr
      have hr' := Finset.mem_Icc.mp hrm.1
      have hr0 : 0 < r := hr'.1
      have hrR : (r : ℝ) ≤ R := le_trans (Nat.cast_le.mpr hr'.2) (Nat.floor_le hR0.le)
      have hphr : (0 : ℝ) < Nat.totient r := by exact_mod_cast Nat.totient_pos.mpr hr0
      have h : ‖T2M.sB W' W ((m : ℝ) * α)‖ ^ 2 ≤ (Nat.totient r : ℝ) *
          ∑ c ∈ T2M.cSet r, ‖T2M.sB W' W ((m : ℝ) * α + c / r)‖ ^ 2 :=
        mi r hrm.2.1 ⌊W'⌋₊ (⌊W⌋₊ - ⌊W'⌋₊) bP ((m : ℝ) * α) (fun n hn hnc => by
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
      rw [← Finset.mul_sum]
      have hw := hω0 r hr
      calc ω r / Nat.totient r * ‖T2M.sB W' W ((m : ℝ) * α)‖ ^ 2
          = ω r * (‖T2M.sB W' W ((m : ℝ) * α)‖ ^ 2 / Nat.totient r) := by ring
        _ ≤ ω r * ∑ c ∈ T2M.cSet r, ‖T2M.sB W' W ((m : ℝ) * α + c / r)‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ hw
          rw [div_le_iff₀ hphr]
          linarith
    set D := M2C.dep t (fun _ => M2C.dep (rS q R) T2M.cSet) with hD
    have hflat : ∑ m ∈ t, ∑ r ∈ rS q R, ∑ c ∈ T2M.cSet r,
        ω r * ‖T2M.sB W' W ((m : ℝ) * α + c / r)‖ ^ 2 =
        ∑ w ∈ D, ω w.2.1 * ‖T2M.sB W' W ((w.1 : ℝ) * α + (w.2.2 : ℝ) / (w.2.1 : ℝ))‖ ^ 2 := by
      rw [hD, ← M2C.sum_dep]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← M2C.sum_dep]
    have hls := wblock_triples mv W' W hW'0 D
      (fun w => (w.1 : ℝ) * α + (w.2.2 : ℝ) / (w.2.1 : ℝ))
      (fun w => 1 / ((q : ℝ) * w.2.1 * R) - 1 / Q)
      (by
        intro w hw
        simp only [hD, M2C.mem_dep] at hw
        exact hδr w.2.1 hw.2.1)
      (by
        rintro ⟨m, r, c⟩ hw ⟨m', r', c'⟩ hw' hne n
        simp only [hD, M2C.mem_dep] at hw hw'
        obtain ⟨hm, hr, hc⟩ := hw
        obtain ⟨hm', hr', hc'⟩ := hw'
        have hrm := Finset.mem_filter.mp hr
        have hrm' := Finset.mem_filter.mp hr'
        have hrI := Finset.mem_Icc.mp hrm.1
        have hrI' := Finset.mem_Icc.mp hrm'.1
        have hr'R : (r' : ℝ) ≤ R := le_trans (Nat.cast_le.mpr hrI'.2) (Nat.floor_le hR0.le)
        unfold T2M.cSet at hc hc'
        rw [Finset.mem_filter, Finset.mem_range] at hc hc'
        have hcl := hdiam m hm m' hm'
        refine sep_w α a q hq hg (δ / x) Q R h2a m m' r r' c c' (hodd m hm) (hodd m' hm')
          hrI.1 hrI'.1 hr'R hc.1 hc'.1 hc.2 hc'.2 hrm.2.2 hrm'.2.2 (fun j hj => ?_)
          (fun j hj hd => ?_) hne n
        · rw [hj, abs_mul, abs_two] at hcl
          have hjq : |(j : ℝ)| < q := by linarith
          have hjq' : |(j : ℝ)| ≤ q - 1 := by
            rw [← Int.cast_abs] at hjq ⊢
            have : |j| < (q : ℤ) := by exact_mod_cast hjq
            have : |j| ≤ (q : ℤ) - 1 := by omega
            exact_mod_cast this
          rw [abs_mul]
          calc |(j : ℝ)| * |δ / x| ≤ (q - 1) * (1 / (q * Q)) :=
                mul_le_mul hjq' hδ (abs_nonneg _) (by linarith)
            _ ≤ 1 / Q := by
                rw [show ((q : ℝ) - 1) * (1 / (q * Q)) = (1 - 1 / q) * (1 / Q) by
                  field_simp]
                have : 0 ≤ 1 / (q : ℝ) := by positivity
                have : 0 < 1 / Q := by positivity
                nlinarith
        · rw [hj, abs_mul, abs_two] at hcl
          have hjq : |(j : ℝ)| < q := by linarith
          rw [← Int.cast_abs] at hjq
          have : |j| < (q : ℤ) := by exact_mod_cast hjq
          exact Int.eq_zero_of_abs_lt_dvd hd this)
    have hbig : G * ∑ m ∈ t, ‖pS α W' W m‖ ^ 2 ≤ pSq W' W := by
      rw [Finset.mul_sum]
      refine (Finset.sum_le_sum fun m _ => hmont m).trans ?_
      rw [hflat]
      exact hls
    have hS0 : 0 ≤ ∑ m ∈ t, ‖pS α W' W m‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hkey : (Nat.totient q : ℝ) / q * Real.log (W / (2 * q)) / W *
        ∑ m ∈ t, ‖pS α W' W m‖ ^ 2 ≤ pSq W' W :=
      (mul_le_mul_of_nonneg_right hG hS0).trans hbig
    have e1 : (q : ℝ) / Nat.totient q * W / Real.log (W / (2 * q)) * pSq W' W =
        pSq W' W / ((Nat.totient q : ℝ) / q * Real.log (W / (2 * q)) / W) := by
      field_simp
    rw [e1, le_div_iff₀ hT0]
    linarith
  · have h0 : ∀ m, pS α W' W m = 0 := fun m => (pS_empty α W' W hWW hW0.le m).1
    rw [(pS_empty α W' W hWW hW0.le 0).2]
    simp [h0]

/-- **`T2X.Garn1a` from Montgomery's inequality, the weighted large sieve and `WeightLB`**. -/
theorem garn1a_of_links (mi : T2M.MontgomeryIneq) (mv : MVWeighted) (wl : WeightLB) : Garn1a :=
  garn1a_of_pokor (pokor2B_of_links mi mv wl)

/-- **`T2S.Kraken` from the literature (`LargeSieve`, `MontgomeryIneq`, `MVWeighted`) and the
one open link `WeightLB`, PROVED**. -/
theorem kraken_of_weight (ls : LargeSieve) (mi : T2M.MontgomeryIneq) (mv : MVWeighted)
    (wl : WeightLB) : Kraken :=
  T2M.kraken_of_mont ls mi (garn1a_of_links mi mv wl)

end Principia.Common.TernaryGoldbach.T2G
