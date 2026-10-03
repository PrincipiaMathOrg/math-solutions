/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.LargeQNum

set_option autoImplicit false

/-!
# `HX.EspagnLargeQ` PROVED from Rosser–Schoenfeld 1962 (3.16), (3.24), (3.30), (3.32)

The two tails of the spine (`LargeQSpine.lean`) and the final composition.

* **`tailGen`** (`ternvin.tex` 3152-3175): for `q ≥ Π_{p≤31} p`, bracket
  `Π_{p≤p₁} p ≤ q < Π_{p≤p₀} p` (`p₁ < p₀` consecutive primes, `p₁ ≥ 31`); then
  `λ(q) ≤ victo(p₁, q) ≤ 190.272(log p₁)³e^{2.24742p₁^{1/3}}/(log q − log p₁ + 0.07354)³`,
  `log q ≥ θ(p₁) ≥ 0.8009p₁`, `eq:mutuso`, `e^{0.224p₁} ≤ q^{0.2797} ≤ ϖ₀(q)` (`eq:drolo`).
* **`tailWo`** (3203-3208): for `210 ∤ q`, `q ≥ Π_{p≤37,p≠7} p`, the same with `eq:hipowo`,
  `log q ≥ θ(p₁) − log 7`, and the CORRECTED `LQ.mutusoWo`.
* **`espagnLargeQ_of_rs62`**: `HX.EspagnLargeQ` from RS62 (3.16), (3.24), (3.30), (3.32) alone
  (with the cited small runs it already receives from `HC.EspagnSmallCited`).
-/

namespace Principia.Common.TernaryGoldbach.LQ

open Principia.Common.TernaryGoldbach.HC (lambdaE varpi0 varpiE victoFirst hipowoFirst)

/-! ## (1) The second lines of `eq:victo`, `eq:hipowo` -/

/-- **`eq:victo`, second line** (`ternvin.tex` 3125-3126):
`victo(p₁,q) ≤ 190.272(log p₁)³e^{2.24742p₁^{1/3}}/(log q − log p₁ + 0.07354)³`. -/
theorem victo_second (p1 q : ℝ) (hp1 : 1 ≤ p1) (hq : p1 ≤ q) :
    victoFirst p1 q ≤ 190.272 * Real.log p1 ^ 3 * Real.exp (2.24742 * p1 ^ ((1 : ℝ) / 3)) /
      (Real.log q - Real.log p1 + 0.07354) ^ 3 := by
  unfold victoFirst
  have hp0 : 0 < p1 := by linarith
  have hX : 0 ≤ Real.log q - Real.log p1 := by
    have := Real.log_le_log hp0 hq
    linarith
  have ha : 0 ≤ Real.log p1 := Real.log_nonneg hp1
  set X := Real.log q - Real.log p1 with hXdef
  set a := Real.log p1 with hadef
  set e := Real.exp (0.74914 * p1 ^ ((1 : ℝ) / 3)) with hedef
  have he0 : 0 < e := Real.exp_pos _
  have he3 : Real.exp (2.24742 * p1 ^ ((1 : ℝ) / 3)) = e ^ 3 := by
    rw [hedef, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he3]
  have hX0 : 0 < X + 0.07354 := by linarith
  have hD : 0.37268 * (X + 0.07354) ≤ 0.37268 * X + 0.02741 := by nlinarith
  have hD0 : 0 < 0.37268 * (X + 0.07354) := by nlinarith
  have hN0 : 0 ≤ 1.90516 * a * (7.45235 * (e / 6.62365)) := by positivity
  have hb : 1.90516 * a * (7.45235 * (e / 6.62365)) / (0.37268 * X + 0.02741) ≤
      1.90516 * a * (7.45235 * (e / 6.62365)) / (0.37268 * (X + 0.07354)) :=
    div_le_div_of_nonneg_left hN0 hD0 hD
  have hb0 : 0 ≤ 1.90516 * a * (7.45235 * (e / 6.62365)) / (0.37268 * X + 0.02741) :=
    div_nonneg hN0 (by linarith)
  have hQ0 : 0 ≤ a ^ 3 * e ^ 3 / (X + 0.07354) ^ 3 := by positivity
  calc (1.90516 * a * (7.45235 * (e / 6.62365)) / (0.37268 * X + 0.02741)) ^ 3
      ≤ (1.90516 * a * (7.45235 * (e / 6.62365)) / (0.37268 * (X + 0.07354))) ^ 3 :=
        pow_le_pow_left₀ hb0 hb 3
    _ = (1.90516 * 7.45235 / 6.62365 / 0.37268) ^ 3 * (a ^ 3 * e ^ 3 / (X + 0.07354) ^ 3) := by
        field_simp
    _ ≤ 190.272 * (a ^ 3 * e ^ 3 / (X + 0.07354) ^ 3) :=
        mul_le_mul_of_nonneg_right (by norm_num) hQ0
    _ = 190.272 * a ^ 3 * e ^ 3 / (X + 0.07354) ^ 3 := by ring

/-- **`eq:hipowo`, second line** (`ternvin.tex` 3196-3197):
`hipowo(p₁,q) ≤ 84.351(log p₁)³e^{2.24742p₁^{1/3}}/(log q − log p₁ + 0.35152)³`. -/
theorem hipowo_second (p1 q : ℝ) (hp1 : 1 ≤ p1) (hq : p1 ≤ q) :
    hipowoFirst p1 q ≤ 84.351 * Real.log p1 ^ 3 * Real.exp (2.24742 * p1 ^ ((1 : ℝ) / 3)) /
      (Real.log q - Real.log p1 + 0.35152) ^ 3 := by
  unfold hipowoFirst
  have hp0 : 0 < p1 := by linarith
  have hX : 0 ≤ Real.log q - Real.log p1 := by
    have := Real.log_le_log hp0 hq
    linarith
  have ha : 0 ≤ Real.log p1 := Real.log_nonneg hp1
  have h7 := log7_bounds.1
  set X := Real.log q - Real.log p1 with hXdef
  set a := Real.log p1 with hadef
  set e := Real.exp (0.74914 * p1 ^ ((1 : ℝ) / 3)) with hedef
  have he0 : 0 < e := Real.exp_pos _
  have he3 : Real.exp (2.24742 * p1 ^ ((1 : ℝ) / 3)) = e ^ 3 := by
    rw [hedef, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he3]
  have hD : 0.37268 * (X + 0.35152) ≤ 0.37268 * (X + Real.log 7 / 7) + 0.02741 := by nlinarith
  have hD0 : 0 < 0.37268 * (X + 0.35152) := by nlinarith
  have hN0 : 0 ≤ 1.633 * a * (7.45235 * (e / 7.44586)) := by positivity
  have hb : 1.633 * a * (7.45235 * (e / 7.44586)) / (0.37268 * (X + Real.log 7 / 7) + 0.02741) ≤
      1.633 * a * (7.45235 * (e / 7.44586)) / (0.37268 * (X + 0.35152)) :=
    div_le_div_of_nonneg_left hN0 hD0 hD
  have hb0 : 0 ≤ 1.633 * a * (7.45235 * (e / 7.44586)) /
      (0.37268 * (X + Real.log 7 / 7) + 0.02741) := div_nonneg hN0 (by linarith)
  have hX0 : 0 < X + 0.35152 := by linarith
  have hQ0 : 0 ≤ a ^ 3 * e ^ 3 / (X + 0.35152) ^ 3 := by positivity
  calc (1.633 * a * (7.45235 * (e / 7.44586)) / (0.37268 * (X + Real.log 7 / 7) + 0.02741)) ^ 3
      ≤ (1.633 * a * (7.45235 * (e / 7.44586)) / (0.37268 * (X + 0.35152))) ^ 3 :=
        pow_le_pow_left₀ hb0 hb 3
    _ = (1.633 * 7.45235 / 7.44586 / 0.37268) ^ 3 * (a ^ 3 * e ^ 3 / (X + 0.35152) ^ 3) := by
        field_simp
    _ ≤ 84.351 * (a ^ 3 * e ^ 3 / (X + 0.35152) ^ 3) :=
        mul_le_mul_of_nonneg_right (by norm_num) hQ0
    _ = 84.351 * a ^ 3 * e ^ 3 / (X + 0.35152) ^ 3 := by ring

/-! ## (2) The general tail -/

/-- `e^{0.224t} ≤ q^{0.2797}` once `log q ≥ 0.8009t` (`0.2797·0.8009 ≥ 0.224`). -/
theorem exp_le_qpow (q t : ℝ) (hq : 0 < q) (ht : 0 ≤ t) (hl : 0.8009 * t ≤ Real.log q) :
    Real.exp (0.224 * t) ≤ q ^ (0.2797 : ℝ) := by
  rw [Real.rpow_def_of_pos hq]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- **`LQ.TailGen`, PROVED** (`ternvin.tex` 3152-3175). -/
theorem tailGen (h316 : RS62_316) (h324 : RS62_324) (h330 : RS62_330) (h332 : RS62_332)
    (hps : HC.ProdSmallCited) (hls : HC.LogSumCited) (hlt : HC.LogSumTenKCited)
    (hts : HC.ThetaSmallCited) (hf1 : HC.F1ProdCited) : TailGen := by
  intro cer q hq
  have hex : ∃ m, q < primorial (m + 1) :=
    ⟨q, lt_trans (Nat.lt_succ_self q) (lt_primorial_self (by omega))⟩
  obtain ⟨n, hndef⟩ : ∃ n, n = Nat.find hex := ⟨_, rfl⟩
  have hn : q < primorial (n + 1) := by rw [hndef]; exact Nat.find_spec hex
  have h31 : primorial 31 = 200560490130 := by decide
  have hn31 : 31 ≤ n := by
    by_contra h
    have := primorial_mono (show n + 1 ≤ 31 by omega)
    omega
  have hnq : primorial n ≤ q := by
    have hmin : ¬q < primorial (n - 1 + 1) :=
      Nat.find_min hex (show n - 1 < Nat.find hex by rw [← hndef]; omega)
    rw [show n - 1 + 1 = n by omega] at hmin
    omega
  obtain ⟨p1, hp1def⟩ : ∃ p1, p1 = Nat.findGreatest Nat.Prime n := ⟨_, rfl⟩
  have hp1 : p1.Prime := by rw [hp1def]; exact Nat.findGreatest_spec hn31 (by norm_num)
  have hp31 : 31 ≤ p1 := by rw [hp1def]; exact Nat.le_findGreatest hn31 (by norm_num)
  have hp1n : p1 ≤ n := by rw [hp1def]; exact Nat.findGreatest_le n
  have hgap : ∀ m < n + 1, p1 < m → ¬m.Prime := fun m hm h => by
    rw [hp1def] at h
    exact Nat.findGreatest_is_greatest h (by omega)
  have hprim : primorial p1 = primorial n := by
    unfold primorial
    rw [filter_prime_eq hp1n hgap]
  have hpq' : primorial p1 ≤ q := hprim ▸ hnq
  have hpq : p1 ≤ q := le_trans le_primorial_self hpq'
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  -- `log q ≥ θ(p₁) ≥ 0.8009p₁`
  have hθ : Chebyshev.theta p1 ≤ Real.log q := by
    rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]
    exact Real.log_le_log (by exact_mod_cast primorial_pos p1) (by exact_mod_cast hpq')
  have hlq : 0.8009 * (p1 : ℝ) ≤ Real.log q := le_trans (thetaLower h316 hts p1 hp1 hp31) hθ
  -- `λ(q) ≤ victo(p₁, q)`
  have hv := lam_le_victo cer hf1 hipo q n p1 (by omega) (by omega) hp1n hgap hn hpq
    (mertBound h330 hps p1 hp1 (by omega)) (logSumBound h332 hls hlt p1 hp1 (by omega))
    (h324 p1 (by omega)).le
  have hp1r : (31 : ℝ) ≤ p1 := by exact_mod_cast hp31
  have hpqr : (p1 : ℝ) ≤ q := by exact_mod_cast hpq
  have h2 := victo_second p1 q (by linarith) hpqr
  -- `eq:mutuso` at `t = p₁`, then the denominator grows to `log q − log p₁ + 0.07354`
  have hmu := mutuso p1 hp1r
  have hLu : Real.log p1 ≤ 3.434 + ((p1 : ℝ) / 31 - 1) := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < p1)
      (by norm_num : (0 : ℝ) < 31))
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    linarith [log31_le]
  have hW0 : 0 < 0.8009 * (p1 : ℝ) - Real.log p1 + 0.07354 := by linarith
  have hWD : 0.8009 * (p1 : ℝ) - Real.log p1 + 0.07354 ≤ Real.log q - Real.log p1 + 0.07354 := by
    linarith
  have hlp : 0 ≤ Real.log p1 := Real.log_nonneg (by linarith)
  have hnum0 : 0 ≤ 190.272 * Real.log p1 ^ 3 * Real.exp (2.24742 * (p1 : ℝ) ^ ((1 : ℝ) / 3)) :=
    by positivity
  have h3 : 190.272 * Real.log p1 ^ 3 * Real.exp (2.24742 * (p1 : ℝ) ^ ((1 : ℝ) / 3)) /
      (Real.log q - Real.log p1 + 0.07354) ^ 3 ≤ Real.exp (0.224 * p1) := by
    rw [div_le_iff₀ (pow_pos (by linarith) 3)]
    have hc : (0.8009 * (p1 : ℝ) - Real.log p1 + 0.07354) ^ 3 ≤
        (Real.log q - Real.log p1 + 0.07354) ^ 3 := pow_le_pow_left₀ hW0.le hWD 3
    have := mul_le_mul_of_nonneg_left hc (Real.exp_pos (0.224 * (p1 : ℝ))).le
    linarith
  have h4 := exp_le_qpow q p1 hq0 (by linarith) hlq
  have h5 := drolo q (by exact_mod_cast hq)
  have h6 : varpi0 (q : ℝ) ≤ varpiE q := le_max_left _ _
  linarith

/-! ## (3) The `210 ∤ q` tail -/

/-- **`LQ.TailWo`, PROVED** (`ternvin.tex` 3203-3208, with the corrected `mutusoWo`). -/
theorem tailWo (h316 : RS62_316) (h324 : RS62_324) (h330 : RS62_330) (h332 : RS62_332)
    (hps : HC.ProdSmallCited) (hls : HC.LogSumCited) (hlt : HC.LogSumTenKCited)
    (hts : HC.ThetaSmallCited) (hf1 : HC.F1ProdCited) : TailWo := by
  intro cer q hq h210
  have hex : ∃ m, q < primorial (m + 1) / 7 := by
    refine ⟨7 * q + 13, ?_⟩
    have h := lt_primorial_self (show 2 < 7 * q + 13 + 1 by omega)
    omega
  obtain ⟨n, hndef⟩ : ∃ n, n = Nat.find hex := ⟨_, rfl⟩
  have hn : q < primorial (n + 1) / 7 := by rw [hndef]; exact Nat.find_spec hex
  have h37 : primorial 37 / 7 = 1060105447830 := by decide
  have hn37 : 37 ≤ n := by
    by_contra h
    have := Nat.div_le_div_right (c := 7) (primorial_mono (show n + 1 ≤ 37 by omega))
    omega
  have hnq : primorial n / 7 ≤ q := by
    have hmin : ¬q < primorial (n - 1 + 1) / 7 :=
      Nat.find_min hex (show n - 1 < Nat.find hex by rw [← hndef]; omega)
    rw [show n - 1 + 1 = n by omega] at hmin
    omega
  obtain ⟨p1, hp1def⟩ : ∃ p1, p1 = Nat.findGreatest Nat.Prime n := ⟨_, rfl⟩
  have hp1 : p1.Prime := by rw [hp1def]; exact Nat.findGreatest_spec hn37 (by norm_num)
  have hp37 : 37 ≤ p1 := by rw [hp1def]; exact Nat.le_findGreatest hn37 (by norm_num)
  have hp1n : p1 ≤ n := by rw [hp1def]; exact Nat.findGreatest_le n
  have hgap : ∀ m < n + 1, p1 < m → ¬m.Prime := fun m hm h => by
    rw [hp1def] at h
    exact Nat.findGreatest_is_greatest h (by omega)
  have hprim : primorial p1 = primorial n := by
    unfold primorial
    rw [filter_prime_eq hp1n hgap]
  have h7d : 7 ∣ primorial p1 := (Nat.prime_seven.dvd_primorial_iff).mpr (by omega)
  have hpq' : primorial p1 / 7 ≤ q := hprim ▸ hnq
  have hP7 : primorial p1 = 7 * (primorial p1 / 7) := (Nat.mul_div_cancel' h7d).symm
  have hpq : p1 ≤ q := by
    have h1 : p1 ∣ primorial p1 := hp1.dvd_primorial
    have h2 : 7 * p1 ∣ primorial p1 :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd
        ((Nat.coprime_primes Nat.prime_seven hp1).mpr (by omega)) h7d h1
    have h3 : 7 * p1 ≤ primorial p1 := Nat.le_of_dvd (primorial_pos _) h2
    omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  -- `log q ≥ θ(p₁) − log 7 ≥ 0.8009p₁ − log 7`
  have hθ : Chebyshev.theta p1 - Real.log 7 ≤ Real.log q := by
    rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]
    have hpos : (0 : ℝ) < ((primorial p1 / 7 : ℕ) : ℝ) := by
      exact_mod_cast Nat.div_pos (le_trans (by norm_num) (Nat.le_of_dvd (primorial_pos _) h7d))
        (by norm_num)
    have hcast : ((primorial p1 : ℕ) : ℝ) = 7 * ((primorial p1 / 7 : ℕ) : ℝ) := by
      exact_mod_cast hP7
    have e : Real.log (primorial p1 : ℝ) = Real.log 7 + Real.log ((primorial p1 / 7 : ℕ) : ℝ) := by
      rw [hcast, Real.log_mul (by norm_num) hpos.ne']
    rw [e]
    have hq7 : ((primorial p1 / 7 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq'
    have := Real.log_le_log hpos hq7
    linarith
  have hlq : 0.8009 * (p1 : ℝ) - Real.log 7 ≤ Real.log q := by
    have := thetaLower h316 hts p1 hp1 (by omega)
    linarith
  have hv := lam_le_hipowo cer hf1 hipoWo f1Seven q n p1 (by omega) (by omega) hp1n hgap h210 hn
    hpq (mertBound h330 hps p1 hp1 (by omega)) (logSumBound h332 hls hlt p1 hp1 (by omega))
    (h324 p1 (by omega)).le
  have hp1r : (37 : ℝ) ≤ p1 := by exact_mod_cast hp37
  have hpqr : (p1 : ℝ) ≤ q := by exact_mod_cast hpq
  have h2 := hipowo_second p1 q (by linarith) hpqr
  have hmu := mutusoWo p1 hp1r
  obtain ⟨h7l, h7u⟩ := log7_bounds
  have hLu : Real.log p1 ≤ 3.611 + ((p1 : ℝ) / 37 - 1) := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < p1)
      (by norm_num : (0 : ℝ) < 37))
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    linarith [log37_le]
  have hW0 : 0 < 0.8009 * (p1 : ℝ) - Real.log 7 - Real.log p1 + 0.35152 := by linarith
  have hWD : 0.8009 * (p1 : ℝ) - Real.log 7 - Real.log p1 + 0.35152 ≤
      Real.log q - Real.log p1 + 0.35152 := by linarith
  have hlp : 0 ≤ Real.log p1 := Real.log_nonneg (by linarith)
  have h3 : 84.351 * Real.log p1 ^ 3 * Real.exp (2.24742 * (p1 : ℝ) ^ ((1 : ℝ) / 3)) /
      (Real.log q - Real.log p1 + 0.35152) ^ 3 ≤ Real.exp (0.224 * p1) / 1.73 := by
    rw [div_le_div_iff₀ (pow_pos (by linarith) 3) (by norm_num)]
    have hc : (0.8009 * (p1 : ℝ) - Real.log 7 - Real.log p1 + 0.35152) ^ 3 ≤
        (Real.log q - Real.log p1 + 0.35152) ^ 3 := pow_le_pow_left₀ hW0.le hWD 3
    have := mul_le_mul_of_nonneg_left hc (Real.exp_pos (0.224 * (p1 : ℝ))).le
    nlinarith
  -- `e^{0.224p₁}/1.73 ≤ e^{0.224p₁}/7^{0.2797} ≤ q^{0.2797}`
  have h4 : Real.exp (0.224 * p1) / 1.73 ≤ q ^ (0.2797 : ℝ) := by
    have h7p := seven_pow_le
    have h7p0 : 0 < (7 : ℝ) ^ (0.2797 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    have hA : Real.exp (0.224 * p1) / 1.73 ≤ Real.exp (0.224 * p1) / (7 : ℝ) ^ (0.2797 : ℝ) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le h7p0 h7p
    refine le_trans hA ?_
    rw [div_le_iff₀ h7p0, Real.rpow_def_of_pos hq0,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 7), ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have h5 := drolo q (by
    have : 200560490130 ≤ q := le_trans (by norm_num) hq
    exact_mod_cast this)
  have h6 : varpi0 (q : ℝ) ≤ varpiE q := le_max_left _ _
  linarith

/-! ## (4) The composition -/

/-- **`HX.EspagnLargeQ`, PROVED from Rosser–Schoenfeld 1962 (3.16), (3.24), (3.30), (3.32)**
(`ternvin.tex` 3025-3211), with Helfgott's cited small runs from `HC.EspagnSmallCited`. -/
theorem espagnLargeQ_of_rs62 (h316 : RS62_316) (h324 : RS62_324) (h330 : RS62_330)
    (h332 : RS62_332) : HX.EspagnLargeQ := fun cer sm =>
  espagnLargeQ_of_links h324 hipo hipoWo varpi0Mono f1Seven
    (tailGen h316 h324 h330 h332 sm.2.1 sm.2.2.1 sm.2.2.2.1 sm.2.2.2.2.2.1 sm.2.2.2.2.1)
    (tailWo h316 h324 h330 h332 sm.2.1 sm.2.2.1 sm.2.2.2.1 sm.2.2.2.2.2.1 sm.2.2.2.2.1) cer sm

end Principia.Common.TernaryGoldbach.LQ
