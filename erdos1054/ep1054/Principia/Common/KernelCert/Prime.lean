/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-!
# Kernel certificates: primality by one `gcd`

`n` is prime as soon as `2 ≤ n < (k + 1)²` and `gcd(n, P) = 1` for a `P` divisible by every
`d ∈ [2, k]`: the least prime factor of a composite `n` is `≤ √n ≤ k` and would divide the gcd
(`primeWith_sound`). `Nat.gcd` is kernel-native, so with one shared `P = 2·3⋯k`
(`sieveProd k`, a balanced product tree) a whole list is certified at the cost of one bignum
product plus one small `gcd` per element.

## API

* `primeWith k P n` and `primeWith_sound` — the test for any certified `P`.
* `primeUpTo k n := primeWith k (sieveProd k) n`, `primeUpTo_sound`. **Batch use:**
  `l.all (primeUpTo k) = true` by `decide +kernel`, with `(k + 1)² > max l`; the kernel computes
  `sieveProd k` once (its whnf is cached) and one `gcd` per element.
* `primeB n` — a single-number test, sound **and complete** (`primeB_sound`, `primeB_complete`,
  `primeB_iff`). It builds its own product up to `min(2^⌈log₂ √n⌉, n − 1)`, so each call costs a
  product of `~√n` numbers; for many numbers use `primeUpTo`.
* `coprimeScan P s c x` — the numbers `x, x + s, …, x + (c − 1)s` coprime to `P`, in order;
  `coprimeScan_prime`: with `P = sieveProd k` its elements are primes. With `s = 2` and odd `x`
  this lists **all** primes of a band (every odd prime of the band is coprime to `P` when the band
  lies above `k`).

## Measured (kernel, v4.31.0; wall-clock on a shared 16 GB machine, ±3 s noise)

* `sieveProd 6325` (a 70 000-bit number): ~2 s.
* `l.all (primeUpTo 6325)` for the 1164 primes `primes(2·10^7, 4·10^7)[::1000]`: 2.95 s of kernel
  type checking (profiler), +0.26 GB over the import baseline.
* `primeB n` for one `n` (`n = 39 999 299`, `1 000 003`, `1 000 001`): 5.4–6.0 s each.
* A scan of all odd numbers of `[2·10^7, 2·10^7 + 3·10^4)` against `gcd(·, 6325!)` (the list of
  its 1799 primes): 6.5 s and 0.63 GB peak for the whole file, product included, when the step
  is written `Nat.add x 2`; written `x + 2` the same scan took 97 s (see `Bits.lean`).
-/

namespace Principia.Common.KernelCert

/-- `a · (a + 1) ⋯ (a + n − 1)`, linearly. -/
def prodLin (a : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => prodLin a n * (a + n)

/-- `a · (a + 1) ⋯ (a + n − 1)` as a balanced product tree of depth `≤ fuel` (falling back to
`prodLin` when the fuel runs out, so the value never depends on the fuel). -/
def prodTree : ℕ → ℕ → ℕ → ℕ
  | 0, a, n => prodLin a n
  | f + 1, a, n =>
    if n ≤ 1 then prodLin a n else prodTree f a (n / 2) * prodTree f (a + n / 2) (n - n / 2)

/-- `sieveProd k = 2 · 3 ⋯ k`. -/
def sieveProd (k : ℕ) : ℕ := prodTree 64 2 (k - 1)

theorem dvd_prodLin (a : ℕ) : ∀ n d, a ≤ d → d < a + n → d ∣ prodLin a n
  | 0, d, h1, h2 => by omega
  | n + 1, d, h1, h2 => by
      simp only [prodLin]
      rcases Nat.lt_or_ge d (a + n) with h | h
      · exact Dvd.dvd.mul_right (dvd_prodLin a n d h1 h) _
      · have : d = a + n := by omega
        rw [this]
        exact Dvd.intro_left _ rfl

theorem dvd_prodTree : ∀ f a n d, a ≤ d → d < a + n → d ∣ prodTree f a n
  | 0, a, n, d, h1, h2 => dvd_prodLin a n d h1 h2
  | f + 1, a, n, d, h1, h2 => by
      simp only [prodTree]
      split_ifs with hn
      · exact dvd_prodLin a n d h1 h2
      · rcases Nat.lt_or_ge d (a + n / 2) with h | h
        · exact Dvd.dvd.mul_right (dvd_prodTree f a (n / 2) d h1 h) _
        · exact Dvd.dvd.mul_left (dvd_prodTree f (a + n / 2) (n - n / 2) d h (by omega)) _

theorem dvd_sieveProd {k d : ℕ} (h2 : 2 ≤ d) (hk : d ≤ k) : d ∣ sieveProd k :=
  dvd_prodTree 64 2 (k - 1) d h2 (by omega)

theorem coprime_prodLin {p a : ℕ} :
    ∀ n, (∀ d, a ≤ d → d < a + n → Nat.Coprime p d) → Nat.Coprime p (prodLin a n)
  | 0, _ => Nat.coprime_one_right p
  | n + 1, h => by
      simp only [prodLin]
      exact Nat.Coprime.mul_right (coprime_prodLin n (fun d h1 h2 => h d h1 (by omega)))
        (h (a + n) (by omega) (by omega))

theorem coprime_prodTree {p : ℕ} :
    ∀ f a n, (∀ d, a ≤ d → d < a + n → Nat.Coprime p d) → Nat.Coprime p (prodTree f a n)
  | 0, a, n, h => coprime_prodLin n h
  | f + 1, a, n, h => by
      simp only [prodTree]
      split_ifs with hn
      · exact coprime_prodLin n h
      · exact Nat.Coprime.mul_right
          (coprime_prodTree f a (n / 2) (fun d h1 h2 => h d h1 (by omega)))
          (coprime_prodTree f (a + n / 2) (n - n / 2) (fun d h1 h2 => h d (by omega) (by omega)))

/-- **The primality test against a certified product `P`.** -/
def primeWith (k P n : ℕ) : Bool :=
  decide (2 ≤ n) && decide (n < (k + 1) * (k + 1)) && Nat.gcd n P == 1

/-- **Soundness of `primeWith`**, for any `P` divisible by `2, …, k`. -/
theorem primeWith_sound {k P n : ℕ} (hP : ∀ d, 2 ≤ d → d ≤ k → d ∣ P)
    (h : primeWith k P n = true) : n.Prime := by
  simp only [primeWith, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h2, hk⟩, hg⟩ := h
  by_contra hnp
  have hmf : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hsq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
  have hmk : n.minFac ≤ k := by
    by_contra hc
    have : (k + 1) * (k + 1) ≤ n.minFac ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul (by omega) (by omega)
    omega
  have hdvd : n.minFac ∣ Nat.gcd n P := Nat.dvd_gcd (Nat.minFac_dvd n) (hP _ hmf.two_le hmk)
  rw [hg] at hdvd
  exact hmf.one_lt.ne' (Nat.dvd_one.1 hdvd)

/-- **Batch primality test**: `primeUpTo k n` certifies `n` prime when `n < (k + 1)²`. -/
def primeUpTo (k n : ℕ) : Bool := primeWith k (sieveProd k) n

theorem primeUpTo_sound {k n : ℕ} (h : primeUpTo k n = true) : n.Prime :=
  primeWith_sound (fun _ h2 hk => dvd_sieveProd h2 hk) h

/-- **A whole list at once**: `l.all (primeUpTo k) = true` (one `decide +kernel`) makes every
element prime. -/
theorem all_primeUpTo_sound {k : ℕ} {l : List ℕ} (h : l.all (primeUpTo k) = true) :
    ∀ p ∈ l, p.Prime := fun p hp => primeUpTo_sound (List.all_eq_true.1 h p hp)

/-- `sqrtBound n x f`: double `x` (at most `f` times) until `n < x²`. -/
def sqrtBound (n : ℕ) : ℕ → ℕ → ℕ
  | x, 0 => x
  | x, f + 1 => if n < x * x then x else sqrtBound n (x + x) f

theorem lt_sqrtBound (n : ℕ) :
    ∀ f x, n < (x * 2 ^ f) * (x * 2 ^ f) → n < sqrtBound n x f * sqrtBound n x f
  | 0, x, h => by simpa [sqrtBound] using h
  | f + 1, x, h => by
      simp only [sqrtBound]
      split_ifs with hx
      · exact hx
      · apply lt_sqrtBound n f (x + x)
        have e : (x + x) * 2 ^ f = x * 2 ^ (f + 1) := by rw [pow_succ]; ring
        rw [e]
        exact h

/-- **The single-number primality test** (trial division by the product `2 ⋯ k`,
`k = min(2^j, n − 1)` with `n < 4^j`). -/
def primeB (n : ℕ) : Bool :=
  primeWith (min (sqrtBound n 1 n) (n - 1)) (sieveProd (min (sqrtBound n 1 n) (n - 1))) n

theorem primeB_sound {n : ℕ} (h : primeB n = true) : n.Prime :=
  primeWith_sound (fun _ h2 hk => dvd_sieveProd h2 hk) h

theorem primeB_complete {n : ℕ} (hn : n.Prime) : primeB n = true := by
  have h2 := hn.two_le
  set s := sqrtBound n 1 n with hs
  have hsq : n < s * s := by
    apply lt_sqrtBound n n 1
    have h1 : n < 2 ^ n := Nat.lt_two_pow_self
    have h2' : 2 ^ n ≤ 2 ^ n * 2 ^ n := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos n)
    simp only [one_mul]
    exact h1.trans_le h2'
  unfold primeB
  rw [← hs]
  simp only [primeWith, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨h2, ?_⟩, ?_⟩
  · rcases le_total s (n - 1) with hle | hle
    · rw [min_eq_left hle]
      nlinarith
    · rw [min_eq_right hle]
      have : n - 1 + 1 = n := by omega
      rw [this]
      nlinarith
  · have := coprime_prodTree (p := n) 64 2 (min s (n - 1) - 1) (fun d h1 h3 => by
      rw [hn.coprime_iff_not_dvd]
      intro hd
      have := Nat.le_of_dvd (by omega) hd
      have : min s (n - 1) ≤ n - 1 := min_le_right _ _
      omega)
    exact this

theorem primeB_iff (n : ℕ) : primeB n = true ↔ n.Prime :=
  ⟨primeB_sound, primeB_complete⟩

/-- The first `y ∈ [x, x + f)` coprime to `P` (`0` if there is none). A generator only: nothing
is proved about it, and a list built from it is certified afterwards (e.g. by `primeUpTo`). -/
def nextCoprime (P : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, x => if Nat.gcd x P == 1 then x else nextCoprime P f (x + 1)

/-- The numbers `x, x + s, …, x + (c − 1)s` that are coprime to `P`, in increasing order. -/
def coprimeScan (P s : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | c + 1, x =>
    if Nat.gcd x P == 1 then x :: coprimeScan P s c (Nat.add x s)
    else coprimeScan P s c (Nat.add x s)

theorem mem_coprimeScan {P s : ℕ} :
    ∀ c x y, y ∈ coprimeScan P s c x →
      Nat.gcd y P = 1 ∧ x ≤ y ∧ y < x + c * s + 1 ∧ ∃ i, i < c ∧ y = x + i * s
  | 0, x, y, h => by simp [coprimeScan] at h
  | c + 1, x, y, h => by
      simp only [coprimeScan] at h
      have hrec : y ∈ coprimeScan P s c (Nat.add x s) →
          Nat.gcd y P = 1 ∧ x ≤ y ∧ y < x + (c + 1) * s + 1 ∧
            ∃ i, i < c + 1 ∧ y = x + i * s := by
        intro hy
        obtain ⟨hg, h1, h2, i, hic, hi⟩ := mem_coprimeScan c (Nat.add x s) y hy
        refine ⟨hg, by simp only [Nat.add_eq] at h1; omega, ?_, i + 1, by omega, ?_⟩
        · simp only [Nat.add_eq] at h2
          have : (c + 1) * s = c * s + s := by ring
          omega
        · simp only [Nat.add_eq] at hi
          rw [hi]
          ring
      split_ifs at h with hg
      · rcases List.mem_cons.1 h with rfl | hy
        · exact ⟨by simpa using hg, le_rfl, by omega, 0, by omega, by simp⟩
        · exact hrec hy
      · exact hrec h

/-- `coprimeScan` lists are strictly increasing for `s > 0`, so duplicate-free. -/
theorem coprimeScan_nodup {P s : ℕ} (hs : 0 < s) :
    ∀ c x, (coprimeScan P s c x).Nodup
  | 0, x => by simp [coprimeScan]
  | c + 1, x => by
      simp only [coprimeScan]
      split_ifs
      · refine List.nodup_cons.2 ⟨fun hx => ?_, coprimeScan_nodup hs c _⟩
        have := (mem_coprimeScan c (Nat.add x s) x hx).2.1
        simp only [Nat.add_eq] at this
        omega
      · exact coprimeScan_nodup hs c _

/-- **The elements of `coprimeScan (sieveProd k) s c x` are prime** when `2 ≤ x` and the scan
stays below `(k + 1)²`. -/
theorem coprimeScan_prime {k s c x y : ℕ} (hx : 2 ≤ x) (hk : x + c * s < (k + 1) * (k + 1))
    (hy : y ∈ coprimeScan (sieveProd k) s c x) : y.Prime := by
  obtain ⟨hg, h1, h2, -⟩ := mem_coprimeScan c x y hy
  refine primeWith_sound (k := k) (P := sieveProd k) (fun _ h2 hk => dvd_sieveProd h2 hk) ?_
  simp only [primeWith, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨by omega, by omega⟩, hg⟩

end Principia.Common.KernelCert
