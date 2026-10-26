/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.

# MathDB #351036 — the literal record is FALSE; the repaired sum is integral

MathDB open problem #351036.  For positive integers `n, a, d` put

  `M_i(a,d) = ∑_{r<d} a^{r i}`,   `E_k(n,a,d) = (1/φ(n)) ∑_{i=1}^{φ(n)} gcd(n, M_i(a,d)) ζ_k^i`

with `ζ_k` a primitive `k`-th root of unity.  The MathDB record asserts `E_k(n,a,d) ∈ ℤ` with **no
condition on `k`**.

Two results, both proved here.

1. **The literal record is false** (`literal_statement_false`).  At `(n,a,d,k) = (2,2,1,3)` we have
   `φ(2) = 1` and `M_1(2,1) = 1`, so the sum is `ζ_3`, which is not a rational integer.  The
   source's own context supplies the omitted hypothesis `k ∣ φ(n)`, which fails here (`3 ∤ 1`).
2. **The repaired statement is true** (`integrality`): `k ∣ φ(n)` implies `E_k(n,a,d) ∈ ℤ` for all
   positive `n, a, d`.

## What is assumed

Exactly one thing: **Theorem 3.1 of the source, for a prime base** (`SourceThm31Prime`), the
integer exponent of a cyclotomic factor in the rational partial zeta function of a function
field.  The source states it for prime *powers*; only the prime case is assumed here, because
Dirichlet supplies a prime.  Formalizing it is a separate project, so it enters as a named
hypothesis and never as an `axiom`.

Everything else is proved, including the two steps the write-up delegates to the literature:

* the **transfer to a general coprime base** (`coprime_case`), which needs a prime `q ≡ a (mod n)`
  — that is Dirichlet's theorem on primes in arithmetic progressions, and Mathlib has it
  (`Nat.forall_exists_prime_gt_and_modEq`), so this is a theorem here rather than an assumption;
* the **reduction of the general case to the coprime case** (`integrality`), via the coprime-part
  splitting `n = n₀ n₁` (`exists_coprime_part`, proved by peeling one prime at a time), the
  observation that `p ∣ a` forces `M_i ≡ 1 (mod p)` so `n₁` contributes nothing to the gcd, and
  the vanishing of the inner geometric sum when `k ∤ φ(n₀)`.

## The reusable half

`sum_split` and `geom_vanish` are campaign-agnostic: a Fourier sum of a weight that is periodic
with period `h₀`, taken over `L` full periods, factors as (geometric sum in `w = ζ^{h₀}`) × (sum
over one period), and that geometric factor vanishes unless `w = 1`.  Neither mentions gcds,
totients or roots of unity, and both belong in `Common/` on promotion.

## Statement shape

`E` sums over `Icc 1 (φ n)`, matching the source's `∑_{i=1}^{φ(n)}` literally;
`sum_Icc_one_eq_range` is the bridge to the `range`-indexed form the proofs use.

`integrality` carries no `0 < a` hypothesis.  The source states its result for positive `a`; the
proof never uses positivity, so the formal statement covers `a = 0` too.  That is a broadening,
not a narrowing -- the claimed domain is a strict subset of the proved one.
-/
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Field.GeomSum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Totient

namespace Principia.MathDB.P351036

open Finset

/-! ### The objects -/

/-- `M_i(a,d) = ∑_{r<d} a^{r i}`.  Written as a geometric *sum* rather than as
`(a^{di} - 1)/(a^i - 1)`, which is exactly how the source avoids a `0/0` at `a = 1`. -/
def M (a d i : ℕ) : ℕ := ∑ r ∈ range d, a ^ (r * i)

/-- The gcd weight `f(i) = gcd(n, M_i(a,d))`. -/
def gcdM (n a d i : ℕ) : ℕ := Nat.gcd n (M a d i)

/-- `E_k(n,a,d) = (1/φ(n)) ∑_{i=1}^{φ(n)} gcd(n, M_i(a,d)) ζ^i`. -/
noncomputable def E (n a d : ℕ) (ζ : ℂ) : ℂ :=
  (1 / (Nat.totient n : ℂ)) * ∑ i ∈ Icc 1 (Nat.totient n), (gcdM n a d i : ℂ) * ζ ^ i

/-- `z` is a rational integer. -/
def IsInt (z : ℂ) : Prop := ∃ m : ℤ, z = (m : ℂ)

theorem isInt_zero : IsInt 0 := ⟨0, by norm_num⟩

/-! ### The literal MathDB statement is false -/

theorem M_one (a i : ℕ) : M a 1 i = 1 := by
  simp [M]

theorem gcdM_two_one (i : ℕ) : gcdM 2 2 1 i = 1 := by
  simp [gcdM, M_one]

theorem E_counterexample (ζ : ℂ) : E 2 2 1 ζ = ζ := by
  have h2 : Nat.totient 2 = 1 := Nat.totient_two
  unfold E
  rw [h2, Finset.Icc_self, Finset.sum_singleton, gcdM_two_one]
  norm_num

/-- A primitive cube root of unity is not a rational integer: if it were `m`, then `m ∣ 1`, so
`m = ±1`; `m = -1` fails `m³ = 1`, and `m = 1` contradicts primitivity. -/
theorem not_isInt_of_isPrimitiveRoot_three {ζ : ℂ} (h : IsPrimitiveRoot ζ 3) : ¬ IsInt ζ := by
  rintro ⟨m, rfl⟩
  have h3 : ((m : ℂ)) ^ 3 = 1 := h.pow_eq_one
  have hm : (m : ℤ) ^ 3 = 1 := by exact_mod_cast h3
  have hdvd : m ∣ 1 := ⟨m ^ 2, by rw [← hm]; ring⟩
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with rfl | rfl
  · have hone : ((1 : ℤ) : ℂ) ^ 1 = 1 := by norm_num
    have := (h.pow_eq_one_iff_dvd 1).mp hone
    omega
  · norm_num at hm

/-- **MathDB #351036, part one: the record as stated is false.**  The witness is
`(n,a,d,k) = (2,2,1,3)`, where the omitted hypothesis `k ∣ φ(n)` also fails. -/
theorem literal_statement_false :
    ∃ (n a d k : ℕ) (ζ : ℂ), 0 < n ∧ 0 < a ∧ 0 < d ∧ 0 < k ∧ IsPrimitiveRoot ζ k ∧
      ¬ (k ∣ Nat.totient n) ∧ ¬ IsInt (E n a d ζ) := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 3 :=
    ⟨_, Complex.isPrimitiveRoot_exp 3 (by norm_num)⟩
  refine ⟨2, 2, 1, 3, ζ, by norm_num, by norm_num, by norm_num, by norm_num, hζ, ?_, ?_⟩
  · rw [Nat.totient_two]
    omega
  · rw [E_counterexample]
    exact not_isInt_of_isPrimitiveRoot_three hζ

/-! ### The reusable half: periodic Fourier sums

Neither lemma mentions gcds, totients or roots of unity. -/

/-- Iterating the quasi-periodicity `F (j + h₀) = F j * w`. -/
theorem quasi_periodic_mul {F : ℕ → ℂ} {w : ℂ} {h₀ : ℕ} (hF : ∀ j, F (j + h₀) = F j * w) :
    ∀ (t s : ℕ), F (s + t * h₀) = F s * w ^ t := by
  intro t
  induction t with
  | zero => intro s; simp
  | succ t ih =>
    intro s
    have hidx : s + (t + 1) * h₀ = (s + t * h₀) + h₀ := by ring
    rw [hidx, hF, ih s]
    ring

/-- **The split.**  A quasi-periodic sum over `L` full periods factors as the geometric sum in `w`
times the sum over a single period. -/
theorem sum_split {F : ℕ → ℂ} {w : ℂ} {h₀ : ℕ} (hF : ∀ j, F (j + h₀) = F j * w) :
    ∀ L : ℕ, ∑ j ∈ range (L * h₀), F j = (∑ t ∈ range L, w ^ t) * ∑ s ∈ range h₀, F s := by
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
    have hidx : (L + 1) * h₀ = L * h₀ + h₀ := by ring
    rw [hidx, Finset.sum_range_add, ih, Finset.sum_range_succ]
    have hblock : ∑ s ∈ range h₀, F (L * h₀ + s) = w ^ L * ∑ s ∈ range h₀, F s := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      have hcomm : L * h₀ + s = s + L * h₀ := by ring
      rw [hcomm, quasi_periodic_mul hF L s]
      ring
    rw [hblock]
    ring

/-- **The vanishing.**  A full geometric sum with `w ≠ 1` and `w ^ L = 1` is zero. -/
theorem geom_vanish {w : ℂ} (hw : w ≠ 1) {L : ℕ} (hL : w ^ L = 1) :
    ∑ t ∈ range L, w ^ t = 0 := by
  rw [geom_sum_eq hw L, hL]
  simp

/-- `∑_{i=1}^{N}` re-indexed over `range N`. -/
theorem sum_Icc_one_eq_range (N : ℕ) (F : ℕ → ℂ) :
    ∑ i ∈ Icc 1 N, F i = ∑ j ∈ range N, F (j + 1) := by
  have hset : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range]
  have hN : N + 1 - 1 = N := by omega
  rw [hN]
  exact Finset.sum_congr rfl fun j _ => by rw [Nat.add_comm]

/-! ### Elementary arithmetic of `M` and the gcd weight -/

theorem M_succ (a d i : ℕ) : M a (d + 1) i = (∑ r ∈ range d, a ^ ((r + 1) * i)) + 1 := by
  unfold M
  rw [Finset.sum_range_succ']
  simp

/-- If `p ∣ a` then `M_i(a,d) ≡ 1 (mod p)` for `i ≥ 1`, so `p ∤ M_i`.  This is what makes the
part of `n` sharing factors with `a` invisible to the gcd. -/
theorem not_dvd_M {p a d i : ℕ} (hp : p.Prime) (hpa : p ∣ a) (hd : 0 < d) (hi : 0 < i) :
    ¬ p ∣ M a d i := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  rw [M_succ]
  intro hdvd
  have htail : p ∣ ∑ r ∈ range d', a ^ ((r + 1) * i) :=
    Finset.dvd_sum fun r _ => dvd_pow hpa (Nat.mul_ne_zero (Nat.succ_ne_zero r) (by omega))
  have hone : p ∣ 1 := (Nat.dvd_add_right htail).mp hdvd
  have h1 := Nat.le_of_dvd Nat.one_pos hone
  have h2 := hp.two_le
  omega

theorem coprime_of_primes_dvd {n₁ a d i : ℕ} (hprimes : ∀ p, p.Prime → p ∣ n₁ → p ∣ a)
    (hd : 0 < d) (hi : 0 < i) : Nat.Coprime n₁ (M a d i) := by
  by_contra hcon
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hcon
  exact not_dvd_M hp (hprimes p hp (hpg.trans (Nat.gcd_dvd_left _ _))) hd hi
    (hpg.trans (Nat.gcd_dvd_right _ _))

/-- A factor coprime to `m` does not change the gcd with `m`. -/
theorem gcd_mul_of_coprime {n₀ n₁ m : ℕ} (h : Nat.Coprime n₁ m) :
    Nat.gcd (n₀ * n₁) m = Nat.gcd n₀ m := by
  refine Nat.dvd_antisymm ?_ ?_
  · have hg1 : Nat.gcd (n₀ * n₁) m ∣ n₀ * n₁ := Nat.gcd_dvd_left _ _
    have hg2 : Nat.gcd (n₀ * n₁) m ∣ m := Nat.gcd_dvd_right _ _
    have hcop : Nat.Coprime (Nat.gcd (n₀ * n₁) m) n₁ := Nat.Coprime.coprime_dvd_left hg2 h.symm
    exact Nat.dvd_gcd (hcop.dvd_of_dvd_mul_right hg1) hg2
  · exact Nat.dvd_gcd ((Nat.gcd_dvd_left n₀ m).trans (dvd_mul_right n₀ n₁))
      (Nat.gcd_dvd_right n₀ m)

/-- Congruent arguments give equal gcds. -/
theorem gcd_congr_of_modEq {n x y : ℕ} (h : x ≡ y [MOD n]) : Nat.gcd n x = Nat.gcd n y := by
  have h' : x % n = y % n := h
  rw [Nat.gcd_rec n x, Nat.gcd_rec n y, h']

/-- `M` respects congruence of the base. -/
theorem M_modEq_base {n a b : ℕ} (h : a ≡ b [MOD n]) (d i : ℕ) :
    M a d i ≡ M b d i [MOD n] := by
  rw [← ZMod.natCast_eq_natCast_iff] at h ⊢
  unfold M
  push_cast at h ⊢
  exact Finset.sum_congr rfl fun r _ => by rw [h]

/-- `M` is periodic in the exponent index with period `φ(n₀)`, when the base is a unit. -/
theorem M_modEq_shift {n₀ a : ℕ} (hcop : Nat.Coprime a n₀) (d i : ℕ) :
    M a d (i + Nat.totient n₀) ≡ M a d i [MOD n₀] := by
  have hh : a ^ Nat.totient n₀ ≡ 1 [MOD n₀] := Nat.ModEq.pow_totient hcop
  rw [← ZMod.natCast_eq_natCast_iff] at hh ⊢
  unfold M
  push_cast at hh ⊢
  refine Finset.sum_congr rfl fun r _ => ?_
  have hsplit : ((a : ZMod n₀)) ^ (r * (i + Nat.totient n₀))
      = (a : ZMod n₀) ^ (r * i) * ((a : ZMod n₀) ^ Nat.totient n₀) ^ r := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  rw [hsplit, hh, one_pow, mul_one]

theorem gcdM_periodic {n₀ a : ℕ} (hcop : Nat.Coprime a n₀) (d i : ℕ) :
    gcdM n₀ a d (i + Nat.totient n₀) = gcdM n₀ a d i :=
  gcd_congr_of_modEq (M_modEq_shift hcop d i)

theorem gcdM_congr_base {n a b : ℕ} (h : a ≡ b [MOD n]) (d i : ℕ) :
    gcdM n a d i = gcdM n b d i :=
  gcd_congr_of_modEq (M_modEq_base h d i)

theorem E_congr_base {n a b : ℕ} (h : a ≡ b [MOD n]) (d : ℕ) (ζ : ℂ) :
    E n a d ζ = E n b d ζ := by
  unfold E
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [gcdM_congr_base h d i]

/-! ### The coprime-part splitting -/

/-- Peeling one prime of `gcd(n,a)` at a time: `n = n₀ n₁` with `n₀` coprime to `a` and every
prime factor of `n₁` dividing `a`.  The fuel is a proof device — each peel divides `n` by a prime
at least `2`, so `n` steps always suffice. -/
theorem exists_coprime_part_aux (a : ℕ) : ∀ (fuel n : ℕ), n ≤ fuel → 0 < n →
    ∃ n₀ n₁ : ℕ, 0 < n₀ ∧ 0 < n₁ ∧ n = n₀ * n₁ ∧ Nat.Coprime n₀ a ∧
      ∀ p, p.Prime → p ∣ n₁ → p ∣ a := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hle hn
    omega
  | succ fuel ih =>
    intro n hle hn
    by_cases hcop : Nat.Coprime n a
    · refine ⟨n, 1, hn, Nat.one_pos, (Nat.mul_one n).symm, hcop, ?_⟩
      intro p hp hdvd
      have h1 := Nat.le_of_dvd Nat.one_pos hdvd
      have h2 := hp.two_le
      omega
    · obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd (show Nat.gcd n a ≠ 1 from hcop)
      have hpn : p ∣ n := hpg.trans (Nat.gcd_dvd_left n a)
      have hpa : p ∣ a := hpg.trans (Nat.gcd_dvd_right n a)
      have hnp : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
      have hlt : n / p < n := Nat.div_lt_self hn hp.one_lt
      obtain ⟨m₀, m₁, hm₀, hm₁, hmul, hcop₀, hprimes⟩ := ih (n / p) (by omega) hnp
      refine ⟨m₀, p * m₁, hm₀, Nat.mul_pos hp.pos hm₁, ?_, hcop₀, ?_⟩
      · have hback : n / p * p = n := Nat.div_mul_cancel hpn
        rw [← hback, hmul]
        ring
      · intro q hq hqd
        rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
        · have : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp h
          rw [this]
          exact hpa
        · exact hprimes q hq h

theorem exists_coprime_part (a n : ℕ) (hn : 0 < n) :
    ∃ n₀ n₁ : ℕ, 0 < n₀ ∧ 0 < n₁ ∧ n = n₀ * n₁ ∧ Nat.Coprime n₀ a ∧
      ∀ p, p.Prime → p ∣ n₁ → p ∣ a :=
  exists_coprime_part_aux a n n le_rfl hn

/-! ### The source's Theorem 3.1, and the coprime case -/

/-- **Theorem 3.1 of the source, restricted to a PRIME base** -- which is all the argument needs,
because Dirichlet hands it a prime.  The source states it for prime *powers*, so this hypothesis
is strictly weaker than the source theorem, and the name says so: assuming less makes
`integrality` stronger.  It is the integer exponent of a cyclotomic factor in a rational partial
zeta function.  This is the one input this file does not prove; a hypothesis, never an `axiom`. -/
-- SPEC-CARRY-CHECKED: SourceThm31Prime -- 2026-09-26, against the row's two claims.  Consumed by
-- `coprime_case` and `integrality` only; `literal_statement_false` carries NO hypothesis, so the
-- row's refutation half is unconditional while its repaired half rests on this published source
-- theorem.  So this was never a vacuity risk -- the source proves it, for prime powers, and this
-- is the weaker prime case -- it was a DISCLOSURE gap: the table row read as unconditional and
-- now states the split.  Found only because the auditor's counted-row parser was fixed the same
-- day; an escaped pipe in this row's statement cell had hidden it.
def SourceThm31Prime : Prop :=
  ∀ (n q d k : ℕ) (ζ : ℂ), 0 < n → 0 < d → q.Prime → Nat.Coprime q n →
    IsPrimitiveRoot ζ k → k ∣ Nat.totient n → IsInt (E n q d ζ)

/-- **The coprime case.**  Dirichlet's theorem supplies a prime `q ≡ a (mod n)`; congruent bases
give the same gcd weights, so `E` is unchanged and Theorem 3.1 applies.  This step is a *theorem*
rather than an assumption because Mathlib has Dirichlet. -/
theorem coprime_case (hthm : SourceThm31Prime) {n a d k : ℕ} {ζ : ℂ}
    (hn : 0 < n) (hd : 0 < d) (hζ : IsPrimitiveRoot ζ k) (hk : k ∣ Nat.totient n)
    (hcop : Nat.Coprime a n) : IsInt (E n a d ζ) := by
  obtain ⟨q, -, hq, hqa⟩ :=
    Nat.forall_exists_prime_gt_and_modEq 0 (q := n) (a := a) (by omega) hcop
  have hqcop : Nat.Coprime q n := by
    have hg : Nat.gcd n q = Nat.gcd n a := gcd_congr_of_modEq hqa
    have hna : Nat.gcd n a = 1 := by
      rw [Nat.gcd_comm]
      exact hcop
    unfold Nat.Coprime
    rw [Nat.gcd_comm]
    rw [hg, hna]
  rw [← E_congr_base hqa d ζ]
  exact hthm n q d k ζ hn hd hq hqcop hζ hk

/-! ### The repaired statement -/

/-- **MathDB #351036, part two: the repaired statement is true.**  For all positive `n, a, d` and
every primitive `k`-th root of unity with `k ∣ φ(n)`, `E_k(n,a,d)` is a rational integer.

The proof splits `n = n₀ n₁` with `n₀` coprime to `a`; the factor `n₁` is invisible to every gcd
because `p ∣ a` forces `M_i ≡ 1 (mod p)`.  The weight is then periodic with period `φ(n₀)`, and
the Fourier sum over `φ(n) = φ(n₀) φ(n₁)` terms factors.  Either `ζ^{φ(n₀)} ≠ 1`, and the
geometric factor kills the whole sum, or `ζ^{φ(n₀)} = 1`, and what survives is exactly
`E_k(n₀,a,d)` — the coprime case. -/
theorem integrality (hthm : SourceThm31Prime) {n a d k : ℕ} {ζ : ℂ}
    (hn : 0 < n) (hd : 0 < d) (hζ : IsPrimitiveRoot ζ k) (hk : k ∣ Nat.totient n) :
    IsInt (E n a d ζ) := by
  obtain ⟨n₀, n₁, hn₀, hn₁, hnmul, hcop₀, hprimes⟩ := exists_coprime_part a n hn
  -- the two factors are coprime to each other
  have hcop01 : Nat.Coprime n₀ n₁ := by
    by_contra hcon
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hcon
    have hpn₀ : p ∣ n₀ := hpg.trans (Nat.gcd_dvd_left _ _)
    have hpn₁ : p ∣ n₁ := hpg.trans (Nat.gcd_dvd_right _ _)
    have hpa : p ∣ a := hprimes p hp hpn₁
    have : p ∣ Nat.gcd n₀ a := Nat.dvd_gcd hpn₀ hpa
    rw [hcop₀] at this
    have h1 := Nat.le_of_dvd Nat.one_pos this
    have h2 := hp.two_le
    omega
  set h₀ := Nat.totient n₀ with hh₀
  set L := Nat.totient n₁ with hL
  have hh₀pos : 0 < h₀ := by
    rw [hh₀]
    first
    | exact Nat.totient_pos.mpr hn₀
    | exact Nat.totient_pos hn₀
  have hLpos : 0 < L := by
    rw [hL]
    first
    | exact Nat.totient_pos.mpr hn₁
    | exact Nat.totient_pos hn₁
  have hphi : Nat.totient n = L * h₀ := by
    rw [hnmul, Nat.totient_mul hcop01, ← hh₀, ← hL]
    ring
  -- the weight only sees `n₀`
  have hweight : ∀ j : ℕ, gcdM n a d (j + 1) = gcdM n₀ a d (j + 1) := by
    intro j
    unfold gcdM
    rw [hnmul]
    exact gcd_mul_of_coprime (coprime_of_primes_dvd hprimes hd (by omega))
  -- the quasi-periodic summand
  set F : ℕ → ℂ := fun j => (gcdM n₀ a d (j + 1) : ℂ) * ζ ^ (j + 1) with hF
  have hFper : ∀ j, F (j + h₀) = F j * ζ ^ h₀ := by
    intro j
    have hidx : j + h₀ + 1 = (j + 1) + h₀ := by ring
    have hg : gcdM n₀ a d (j + h₀ + 1) = gcdM n₀ a d (j + 1) := by
      rw [hidx, hh₀]
      exact gcdM_periodic hcop₀.symm d (j + 1)
    have hidx2 : j + h₀ + 1 = (j + 1) + h₀ := by omega
    have hz : ζ ^ (j + h₀ + 1) = ζ ^ (j + 1) * ζ ^ h₀ := by
      rw [hidx2, pow_add]
    simp only [hF]
    rw [hg, hz]
    ring
  -- rewrite `E` as the split sum
  have hEsplit : E n a d ζ
      = (1 / (Nat.totient n : ℂ)) * ((∑ t ∈ range L, (ζ ^ h₀) ^ t) * ∑ s ∈ range h₀, F s) := by
    unfold E
    rw [sum_Icc_one_eq_range]
    congr 1
    have hterm : ∀ j ∈ range (Nat.totient n),
        ((gcdM n a d (j + 1) : ℂ)) * ζ ^ (j + 1) = F j := by
      intro j _
      simp only [hF]
      rw [hweight j]
    rw [Finset.sum_congr rfl hterm, hphi]
    exact sum_split hFper L
  by_cases hone : ζ ^ h₀ = 1
  · -- the surviving case: what is left is `E_k(n₀,a,d)`
    have hkdvd : k ∣ h₀ := (hζ.pow_eq_one_iff_dvd h₀).mp hone
    have hE₀ : E n₀ a d ζ = (1 / (h₀ : ℂ)) * ∑ s ∈ range h₀, F s := by
      unfold E
      rw [← hh₀, sum_Icc_one_eq_range]
    have hgeom : (∑ t ∈ range L, (ζ ^ h₀) ^ t) = (L : ℂ) := by
      rw [hone]
      simp
    have hcastL : ((L : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hcasth : ((h₀ : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hcastphi : ((Nat.totient n : ℂ)) = (L : ℂ) * (h₀ : ℂ) := by
      rw [hphi]
      push_cast
      ring
    have hfinal : E n a d ζ = E n₀ a d ζ := by
      rw [hEsplit, hgeom, hE₀, hcastphi]
      field_simp
    rw [hfinal]
    exact coprime_case hthm hn₀ hd hζ (by rw [← hh₀]; exact hkdvd) hcop₀.symm
  · -- the vanishing case
    have hpow : (ζ ^ h₀) ^ L = 1 := by
      rw [← pow_mul]
      have : h₀ * L = Nat.totient n := by rw [hphi]; ring
      rw [this]
      exact (hζ.pow_eq_one_iff_dvd (Nat.totient n)).mpr hk
    have hzero : (∑ t ∈ range L, (ζ ^ h₀) ^ t) = 0 := geom_vanish hone hpow
    rw [hEsplit, hzero]
    simpa using isInt_zero

end Principia.MathDB.P351036
