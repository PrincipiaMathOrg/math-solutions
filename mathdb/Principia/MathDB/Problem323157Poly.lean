import Mathlib

/-!
# MathDB #323157 — the polynomial reduction (Part 1 of the refutation)

Karp's Conjecture 2 (write-up `mathdb-open-problems/problems/323157/solution.tex`,
*A counterexample to rising-factorial Toeplitz stability*, 11 September 2026) asserts that for
`α, β > 0` and `n ≥ 3`, strict log-concavity `f k ^ 2 > f (k-1) * f (k+1)` for `1 ≤ k < n`
forces every zero of

`Q n α β x = Σ_{k≤n} f k * f (n-k) * C(n,k) * ((x+α)_k (x+β)_{n-k} − (x+α+β)_k (x)_{n-k})`

to have negative real part.  The witness is `n = 12`, `α = 1`, `β = 40` and the `f` below.

This module carries the part of the refutation that never mentions `Complex.I`: that the
witness **satisfies the conjecture's hypotheses** (`fpos`, `flogconcave`), and that `Q`
collapses to `5280 * P` with `P` of degree 10 (`Q_eq`).  The root of `P` in the open right
half-plane is supplied separately, through `Principia.MathDB.RootCert`.

The 215 check: the conjecture requires strictness at **every** `k` with `1 ≤ k < n`, i.e. all
eleven, and requires the `f k` positive — `flogconcave` and `fpos` assert exactly those, no
weaker.  Refuting the conjecture needs a zero with `¬ (re < 0)`; the witness gives `re > 3/4`,
which is stronger than required and therefore safe.

Checked in Python against the write-up before formalizing: `Q − 5280 P = 0` identically
(SymPy, exact integers), `deg Q = 10` — the degree-11 and 12 terms cancel — all eleven
log-concavity gaps `(1979,1,1,1,1,99,1,1,1,1,1979)` strictly positive, every `f k > 0`, and
the write-up's `U_k` table and `L` reproduced exactly.
-/

namespace Principia.MathDB.P323157

/-- The witness coefficient sequence, over `ℤ` so the hypothesis checks are decidable. -/
def fz : ℕ → ℤ
  | 0 => 1
  | 1 => 45
  | 2 => 46
  | 3 => 47
  | 4 => 48
  | 5 => 49
  | 6 => 50
  | 7 => 49
  | 8 => 48
  | 9 => 47
  | 10 => 46
  | 11 => 45
  | 12 => 1
  | _ => 0

/-- The same sequence in `ℂ`, which is where `Q` lives. -/
noncomputable def fv (k : ℕ) : ℂ := ((fz k : ℤ) : ℂ)

/-- The rising factorial `(y)_k = y (y+1) ⋯ (y+k-1)`, with `(y)_0 = 1`. -/
noncomputable def rise (y : ℂ) (k : ℕ) : ℂ := ∏ i ∈ Finset.range k, (y + (i : ℂ))

/-- Karp's `Q_n^{α,β}`, stated exactly as the conjecture does. -/
noncomputable def Qgen (f : ℕ → ℂ) (al be : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), f k * f (n - k) * ((n.choose k : ℕ) : ℂ) *
    (rise (x + al) k * rise (x + be) (n - k) - rise (x + al + be) k * rise x (n - k))

/-- The reduced polynomial `P`, of degree 10. -/
noncomputable def Pw (x : ℂ) : ℂ :=
  8850973475178928800 + 2242108441860414480 * x + 269652359703530916 * x ^ 2
    + 20855984967227000 * x ^ 3 + 1180285415416015 * x ^ 4 + 51443738871420 * x ^ 5
    + 1706782696773 * x ^ 6 + 40875054000 * x ^ 7 + 653614185 * x ^ 8 + 6181900 * x ^ 9
    + 26111 * x ^ 10

/-- **The reduction.**  `Q_{12}^{1,40} = 5280 · P`, so `Q` and `P` have the same zeros.
The binomial coefficients are supplied as kernel-checked `ℕ` facts rather than left to
`simp`, which does not reduce `Nat.choose` on numerals. -/
theorem Q_eq (x : ℂ) : Qgen fv 1 40 12 x = 5280 * Pw x := by
  simp only [Qgen, rise, fv, fz, Pw, Finset.sum_range_succ, Finset.sum_range_zero,
    Finset.prod_range_succ, Finset.prod_range_zero,
    show Nat.choose 12 0 = 1 from by decide,
    show Nat.choose 12 1 = 12 from by decide,
    show Nat.choose 12 2 = 66 from by decide,
    show Nat.choose 12 3 = 220 from by decide,
    show Nat.choose 12 4 = 495 from by decide,
    show Nat.choose 12 5 = 792 from by decide,
    show Nat.choose 12 6 = 924 from by decide,
    show Nat.choose 12 7 = 792 from by decide,
    show Nat.choose 12 8 = 495 from by decide,
    show Nat.choose 12 9 = 220 from by decide,
    show Nat.choose 12 10 = 66 from by decide,
    show Nat.choose 12 11 = 12 from by decide,
    show Nat.choose 12 12 = 1 from by decide]
  norm_num <;> ring

/-- The witness is positive at every index the conjecture ranges over. -/
theorem fpos : ∀ k ≤ 12, 0 < fz k := by decide

/-- Strict log-concavity at every `k` with `1 ≤ k < 12` — all eleven, as required. -/
theorem flogconcave : ∀ k < 12, 1 ≤ k → fz (k - 1) * fz (k + 1) < fz k ^ 2 := by decide


/-- The Taylor coefficients of `P` about `c = 1 + 22i`, Gaussian integers, exactly as the
write-up's table gives them. -/
noncomputable def dc : ℕ → ℂ
  | 0 => 189742720030323200 - 793700276134708800 * Complex.I
  | 1 => 4623392455279316640 + 918762031531300000 * Complex.I
  | 2 => 964738491164890776 - 503623553473212480 * Complex.I
  | 3 => 41731284639119040 - 102319762071198320 * Complex.I
  | 4 => -2112789934659650 - 6198494048526780 * Complex.I
  | 5 => -218140822818450 - 124159018788420 * Complex.I
  | 6 => -6331464644337 + 1371931656480 * Complex.I
  | 7 => -65933357040 + 91671433920 * Complex.I
  | 8 => 141728700 + 1275715980 * Complex.I
  | 9 => 6443010 + 5744420 * Complex.I
  | 10 => 26111
  | _ => 0

/-- **The Taylor expansion of `P` about `c = 1 + 22i`.**  `ring` knows nothing about `I`, so
the identity is closed by `linear_combination` against `Complex.I_sq`; the multiplier is the
exact quotient of `LHS − RHS` by `I² + 1`, computed in SymPy (the division is exact). -/
theorem P_taylor (w : ℂ) :
    Pw (1 + 22 * Complex.I + w) = ∑ k ∈ Finset.range 11, dc k * w ^ k := by
  simp only [Pw, dc, Finset.sum_range_succ, Finset.sum_range_zero]
  linear_combination
    (693506144006872064*Complex.I^8 + 315230065457669120*Complex.I^7*w
      + 7778447642926033920*Complex.I^7 + 64478877025432320*Complex.I^6*w^2
      + 3182092217560650240*Complex.I^6*w + 38291756553924054016*Complex.I^6
      + 7815621457628160*Complex.I^5*w^3 + 578562221374663680*Complex.I^5*w^2
      + 13861229097426304000*Complex.I^5*w + 107784278287366855680*Complex.I^5
      + 621697161402240*Complex.I^4*w^4 + 61362659842767360*Complex.I^4*w^3
      + 2190866898887927040*Complex.I^4*w^2 + 33587866032987087360*Complex.I^4*w
      + 189798455192375539136*Complex.I^4 + 33910754258304*Complex.I^3*w^5
      + 4183817716552320*Complex.I^3*w^4 + 197215812716313600*Complex.I^3*w^3
      + 4435522994609118720*Complex.I^3*w^2 + 48345192287928130496*Complex.I^3*w
      + 214731038256609441600*Complex.I^3 + 1284498267360*Complex.I^2*w^6
      + 190173532570560*Complex.I^2*w^5 + 11027816143935360*Complex.I^2*w^4
      + 318492280762064640*Complex.I^2*w^3 + 4878044622175076880*Complex.I^2*w^2
      + 39711069545189343840*Complex.I^2*w + 153288903454765695584*Complex.I^2
      + 33363591360*Complex.I*w^7 + 5762834320320*Complex.I*w^6 + 389707911390336*Complex.I*w^5
      + 13082315947303680*Complex.I*w^4 + 231203067348110880*Complex.I*w^3
      + 2228016603406920480*Complex.I*w^2 + 14034327466097548544*Complex.I*w
      + 63471040466028782400*Complex.I + 568697580*w^8 + 112263006240*w^7 + 8343198679200*w^6
      + 280721021898240*w^5 + 3577372949170020*w^4 - 15604117215881040*w^3
      - 624895548036962400*w^2 - 1774422446647767840*w + 11195081019151638400) * Complex.I_sq

end Principia.MathDB.P323157
