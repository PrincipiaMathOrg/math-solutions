import Mathlib

set_option autoImplicit false

/-!
# MathDB #342271 — divisibility of an elliptic Dedekind sum (SPINE)

Write-up `mathdb-open-problems/problems/342271/solution.tex` on the `mathdb-results` branch
of `antoshashakov/Principia-Math-In-Progress`.
Source: G. Shibukawa, *Some arithmetic properties of an elliptic Dedekind sum*, JP J.
Algebra Number Theory Appl. **46**(1) (2020) 35–54 (arXiv:1903.12200v2), **Conjecture 13**.

## The elliptic content is a DICTIONARY, not an engine

The conjecture is about Shibukawa's elliptic sum `s_τ(a;b)`, but the theorem the write-up
actually proves has nothing elliptic in it.  With `((x))` the sawtooth and

    s(h;b) = ∑_{j<b} ((j/b))·((hj/b))

the CLASSICAL Dedekind sum, the real theorem is: for `gcd(ht,b) = 1`,

    D_b(h,t) = 6b·(s(h;b) + s(ht²;b) − 2·s(ht;b)) ∈ 4ℤ,   and ∈ 12ℤ when 3 ∤ b.

The only thing connecting this to the elliptic world is Shibukawa's equation (4.3),
`Q(a;b) = 6(s(a;2b) + s(2a;b) − 2s(a;b))`, which the write-up itself labels an established
input.  Taken as the *definition* of `Q`, the entire elliptic apparatus — Eisenstein series,
the modular `λ`, the evaluation at `τ = i` — never appears.  (Sitaramachandra Rao's
Hardy-sum identity is cited as provenance for (4.3) and is **never used in the proof**.)

## The engine, and what this module proves

Two moves, both elementary.  **Meyer's inversion formula** (reproved in the write-up, not
imported) relates the inversion number `I(h,b)` of `j ↦ hj mod b` to the Dedekind sum:
`I(h,b) = (b−1)(b−2)/4 − 3b·s(h;b)`.  And **permutation signs are multiplicative**: since
`σ_{ht²} = σ_t ∘ σ_t ∘ σ_h` and a square has positive sign, `I(h,b) + I(ht²,b)` is even.

Substituting Meyer three times makes the `(b−1)(b−2)` constants cancel EXACTLY, leaving the
write-up's equation (10), which is proved here as `Dsum_eq_inv`:

    D_b(h,t) = 4·I(ht,b) − 2·(I(h,b) + I(ht²,b)).

`Dsum_four` then reads off `D ∈ 4ℤ` from the parity.  The factor 3 is separate and purely
arithmetic, and that part is **proved outright**: `six_sum_sq` gives
`6∑_{j<b} j² = b(b−1)(2b−1)`, `three_dvd_of_not` gives `3 ∣ (b−1)(2b−1)` when `3 ∤ b`, and
together `two_sum_sq_dvd` gives `b ∣ 2∑_{j<b} j²` — which is exactly what the write-up's
step (11) consumes to make `2b·s(u;b)` an integer.  `Dsum_twelve` combines the two with
`gcd(3,4) = 1`.

## What is carried

Three named hypotheses, each the write-up's own step: `Meyer` (the inversion formula),
`SignParity` (the permutation-sign argument), and `Den3Of` (that `b ∣ 2∑j²` transfers to
`2b·s(u;b) ∈ ℤ` through the residues `r_j ≡ uj`).  So this row is a SPINE and is NOT counted
as fully verified.

**None of the three is out of reach.**  The decisive Mathlib fact exists and is in exactly
the right shape: `Equiv.Perm.sign_eq_prod_prod_Iio` (`GroupTheory/Perm/Fin.lean:489`) is
literally the inversion-number-to-sign bridge `SignParity` needs, with the correct order.
Meyer is finite-sum algebra over `ℚ` on `Finset.range b`.  Absent from Mathlib (grepped,
zero hits): Dedekind sums, the sawtooth, inversion number as a named quantity, Hardy sums —
all one-liners to define, as they are here.

**215 check.**  The source states Conjecture 13 for `a` even, `b` positive odd,
`gcd(a,b) = 1` — i.e. `a + b` odd.  The theorem stated here is the write-up's Theorem 2,
which is STRICTLY MORE GENERAL: every modulus `b` including even ones, and arbitrary `h,t`
subject only to `gcd(ht,b) = 1`.  That is the safe direction, since the guards sit on the
hypothesis side.  Conjecture 13 follows by taking `a = 2c` and using the sawtooth folding
identity `s(2c;2b) = s(c;b)`, which is NOT formalised here — so the row proves the general
engine, not the specialisation.

Values checked first, in exact rational arithmetic: Meyer for every coprime `(h,b)` with
`b ≤ 25`; `D ∈ 4ℤ` and (for `3 ∤ b`) `D ∈ 12ℤ` for all coprime `(h,t,b)` with `b ≤ 20`;
equation (10) itself; the parity; the `Den3` integrality for `b ≤ 30`; and the write-up's
three sharpness values `3Q(2;3) = 4`, `5Q(4;5) = 12`, `7Q(2;7) = 12`.
-/

namespace Principia.MathDB.P342271

open Finset

/-- The sawtooth `((x)) = x − ⌊x⌋ − 1/2`, and `0` at integers. -/
noncomputable def saw (x : ℚ) : ℚ := if x = (⌊x⌋ : ℚ) then 0 else x - (⌊x⌋ : ℚ) - 1 / 2

/-- The **classical** Dedekind sum `s(h;b) = ∑_{j<b} ((j/b))·((hj/b))`. -/
noncomputable def ded (h b : ℕ) : ℚ :=
  ∑ j ∈ range b, saw ((j : ℚ) / b) * saw ((h : ℚ) * j / b)

/-- The inversion number of `j ↦ hj mod b` on `{0,…,b−1}`: the number of pairs `i < j`
whose images are out of order.  Written as a sum over `j` of a count on `Iio j`, which is
exactly the shape `Equiv.Perm.sign_eq_prod_prod_Iio` produces. -/
def invNum (h b : ℕ) : ℕ :=
  ∑ j : Fin b, ((Finset.Iio j).filter
    (fun i => (h * j.val) % b < (h * i.val) % b)).card

/-- The write-up's `D_b(h,t)`. -/
noncomputable def Dsum (h t b : ℕ) : ℚ :=
  6 * b * (ded h b + ded (h * t ^ 2) b - 2 * ded (h * t) b)

/-! ### The three carried links -/

/-- **Meyer's inversion formula.**  Finite-sum algebra over `ℚ`; the write-up reproves it
rather than importing it. -/
def Meyer : Prop := ∀ h b : ℕ, 0 < b → Nat.Coprime h b →
  (invNum h b : ℚ) = ((b : ℚ) - 1) * ((b : ℚ) - 2) / 4 - 3 * b * ded h b

/-- **The permutation-sign step.**  `σ_{ht²} = σ_t ∘ σ_t ∘ σ_h` and a square has positive
sign, so the two inversion numbers agree mod 2.  `Equiv.Perm.sign_eq_prod_prod_Iio` is the
bridge. -/
def SignParity : Prop := ∀ h t b : ℕ, 0 < b → Nat.Coprime (h * t) b →
  Even (invNum h b + invNum (h * t ^ 2) b)

/-! #### The sign-to-parity bridge — proved

The ARGUMENT behind `SignParity` is generic, and it is proved here: a product of `±1`
collapses to `(-1)^(number of -1 factors)`, `Equiv.Perm.sign_eq_prod_prod_Iio` IS that
product, and two permutations of equal sign therefore have inversion numbers of equal
parity.  What stays carried is only the IDENTIFICATION — that `j ↦ hj mod b` is a
permutation whose inversion number is `invNum h b`, and that the two relevant permutations
have the same sign because `σ_{ht²} = σ_t ∘ σ_t ∘ σ_h` and a square has positive sign.

These four declarations mention nothing about this campaign and are `Common/` candidates. -/

/-- A product of `±1` collapses to `(-1)^(number of `-1` factors)`. -/
theorem prod_pm {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (∏ x ∈ s, (if p x then (1 : ℤˣ) else -1))
      = (-1) ^ ((s.filter (fun x => ¬ p x)).card) := by
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  rfl

/-- The inversion number of a permutation of `Fin n`, in exactly the shape
`Equiv.Perm.sign_eq_prod_prod_Iio` produces. -/
def invOf {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  ∑ j : Fin n, ((Finset.Iio j).filter (fun i => σ j < σ i)).card

/-- **`sign σ = (-1)^(inversions of σ)`.**  Mathlib has the product form but not this. -/
theorem sign_eq_pow_invOf {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    σ.sign = (-1 : ℤˣ) ^ (invOf σ) := by
  classical
  have hfil : ∀ j : Fin n,
      (Finset.Iio j).filter (fun i => ¬ (σ i < σ j))
        = (Finset.Iio j).filter (fun i => σ j < σ i) := by
    intro j
    refine Finset.filter_congr (fun i hi => ?_)
    have hij : i ≠ j := ne_of_lt (Finset.mem_Iio.mp hi)
    have hne : σ i ≠ σ j := fun h => hij (σ.injective h)
    constructor
    · intro h; exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm hne)
    · intro h; exact not_lt.mpr (le_of_lt h)
  rw [Equiv.Perm.sign_eq_prod_prod_Iio]
  calc ∏ j : Fin n, ∏ i ∈ Finset.Iio j, (if σ i < σ j then (1 : ℤˣ) else -1)
      = ∏ j : Fin n, (-1 : ℤˣ) ^ (((Finset.Iio j).filter (fun i => σ j < σ i)).card) := by
        refine Finset.prod_congr rfl (fun j _ => ?_)
        rw [prod_pm, hfil j]
    _ = (-1 : ℤˣ) ^ (invOf σ) := Finset.prod_pow_eq_pow_sum _ _ _

/-- **Equal sign forces equal parity of inversion numbers.** -/
theorem even_add_invOf {n : ℕ} {σ τ : Equiv.Perm (Fin n)} (h : σ.sign = τ.sign) :
    Even (invOf σ + invOf τ) := by
  have hp : (-1 : ℤˣ) ^ (invOf σ) = (-1 : ℤˣ) ^ (invOf τ) := by
    rw [← sign_eq_pow_invOf, ← sign_eq_pow_invOf, h]
  have hchar : ∀ m : ℕ, ((-1 : ℤˣ) ^ m = 1 ↔ Even m) := fun m =>
    neg_one_pow_eq_one_iff_even (by decide)
  rw [Nat.even_add]
  exact ⟨fun hs => (hchar _).mp (by rw [← hp, (hchar _).mpr hs]),
    fun ht => (hchar _).mp (by rw [hp, (hchar _).mpr ht])⟩

/-- What actually remains of the sign step: the multiplication maps are permutations whose
inversion numbers are `invNum`, and the two relevant ones have equal sign. -/
def SignsAgree : Prop := ∀ h t b : ℕ, 0 < b → Nat.Coprime (h * t) b →
  ∃ σ τ : Equiv.Perm (Fin b), σ.sign = τ.sign ∧
    invOf σ = invNum h b ∧ invOf τ = invNum (h * t ^ 2) b

/-- **`SignParity` is now a THEOREM.**  The parity argument is discharged; only the
identification of the permutations is carried. -/
theorem signParity_of (hs : SignsAgree) : SignParity := by
  intro h t b hb hc
  obtain ⟨σ, τ, hsign, h1, h2⟩ := hs h t b hb hc
  rw [← h1, ← h2]
  exact even_add_invOf hsign

/-! #### The multiplication permutation — `SignParity` is DISCHARGED

`j ↦ hj mod b` is injective on `Fin b` when `gcd(h,b) = 1`, hence a permutation, and
`σ_{ht²} = σ_t ∘ σ_t ∘ σ_h`, so its sign is `(sign σ_t)² · sign σ_h = sign σ_h`.  With
`invNum` written in the shape above, `invOf (σ_h) = invNum h b` holds definitionally. -/

def mulMap (h : ℕ) {b : ℕ} (j : Fin b) : Fin b :=
  ⟨(h * j.val) % b, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le j.val) j.isLt)⟩

theorem mulMap_inj {b : ℕ} (h : ℕ) (hc : Nat.Coprime h b) :
    Function.Injective (mulMap h (b := b)) := by
  intro i j hij
  have hv : h * i.val ≡ h * j.val [MOD b] := congrArg Fin.val hij
  have hmod : i.val ≡ j.val [MOD b] := Nat.ModEq.cancel_left_of_coprime hc.symm hv
  have hi := Nat.mod_eq_of_lt i.isLt
  have hj := Nat.mod_eq_of_lt j.isLt
  refine Fin.ext ?_
  unfold Nat.ModEq at hmod
  omega

noncomputable def mulPerm {b : ℕ} (h : ℕ) (hc : Nat.Coprime h b) : Equiv.Perm (Fin b) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (mulMap_inj h hc))

theorem mulPerm_val {b : ℕ} (h : ℕ) (hc : Nat.Coprime h b) (j : Fin b) :
    ((mulPerm h hc) j).val = (h * j.val) % b := rfl

/-- `σ_{h t²} = σ_t ∘ σ_t ∘ σ_h`. -/
theorem mulPerm_comp {b : ℕ} (h t : ℕ) (hh : Nat.Coprime h b) (ht : Nat.Coprime t b)
    (hht : Nat.Coprime (h * t ^ 2) b) :
    mulPerm (h * t ^ 2) hht = mulPerm t ht * (mulPerm t ht * mulPerm h hh) := by
  refine Equiv.ext (fun j => Fin.ext ?_)
  show (h * t ^ 2 * j.val) % b = (t * ((t * ((h * j.val) % b)) % b)) % b
  have key : (t * ((t * ((h * j.val) % b)) % b)) ≡ (h * t ^ 2 * j.val) [MOD b] := by
    calc t * ((t * ((h * j.val) % b)) % b)
        ≡ t * (t * ((h * j.val) % b)) [MOD b] := Nat.ModEq.mul_left t (Nat.mod_modEq _ _)
      _ ≡ t * (t * (h * j.val)) [MOD b] :=
          Nat.ModEq.mul_left t (Nat.ModEq.mul_left t (Nat.mod_modEq _ _))
      _ = h * t ^ 2 * j.val := by ring
  exact key.symm

/-- **A square has positive sign**, so the two permutations agree. -/
theorem sign_mulPerm_eq {b : ℕ} (h t : ℕ) (hh : Nat.Coprime h b) (ht : Nat.Coprime t b)
    (hht : Nat.Coprime (h * t ^ 2) b) :
    Equiv.Perm.sign (mulPerm (h * t ^ 2) hht) = Equiv.Perm.sign (mulPerm h hh) := by
  rw [mulPerm_comp h t hh ht hht, map_mul, map_mul, ← mul_assoc, Int.units_mul_self, one_mul]

theorem invOf_mulPerm {b : ℕ} (h : ℕ) (hc : Nat.Coprime h b) :
    invOf (mulPerm h hc) = invNum h b := rfl

/-- **`SignsAgree` is a theorem.** -/
theorem signsAgree : SignsAgree := by
  intro h t b _ hc
  have c1 : Nat.Coprime h b := Nat.Coprime.coprime_dvd_left (dvd_mul_right h t) hc
  have ht : Nat.Coprime t b := Nat.Coprime.coprime_dvd_left (dvd_mul_left t h) hc
  have c3 : Nat.Coprime (h * t ^ 2) b := Nat.Coprime.mul_left c1 (ht.pow_left 2)
  exact ⟨mulPerm h c1, mulPerm (h * t ^ 2) c3,
    (sign_mulPerm_eq h t c1 ht c3).symm, invOf_mulPerm h c1, invOf_mulPerm _ c3⟩

/-- **The permutation-sign step is fully discharged.** -/
theorem signParity : SignParity := signParity_of signsAgree

/-! #### Toward `Den3Of`: the sawtooth evaluated, and the residues summed

The write-up's identity (8) is `s(h;b) = (1/b²)∑_j j·r_j - (b-1)/4` with `r_j = hj mod b`.
Its two ingredients are proved here.  **What the sawtooth actually is** at a rational `n/b`
is `saw_nat_div`; **that the residues are a permutation** — so they sum to `b(b-1)/2` — is
`sum_residues`, which reuses `mulPerm`.  The remaining step is the summation bookkeeping,
carried as `DedSumOf`. -/

theorem div_split {n b : ℕ} (hb : 0 < b) :
    (n : ℚ) / b = ((n / b : ℕ) : ℚ) + ((n % b : ℕ) : ℚ) / b := by
  have hbq : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  have h : (b : ℚ) * ((n / b : ℕ) : ℚ) + ((n % b : ℕ) : ℚ) = (n : ℚ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) (Nat.div_add_mod n b)
  field_simp
  linarith [h]

theorem floor_nat_div {n b : ℕ} (hb : 0 < b) :
    ⌊(n : ℚ) / (b : ℚ)⌋ = ((n / b : ℕ) : ℤ) := by
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  have hs := div_split (n := n) hb
  have h0 : (0 : ℚ) ≤ ((n % b : ℕ) : ℚ) / b := by positivity
  have h1 : ((n % b : ℕ) : ℚ) / b < 1 := by
    rw [div_lt_one hbq]
    exact_mod_cast Nat.mod_lt n hb
  rw [Int.floor_eq_iff, Int.cast_natCast]
  exact ⟨by linarith, by linarith⟩

/-- **What the sawtooth is at `n/b`.**  `((n/b)) = (n mod b)/b - 1/2` whenever `b ∤ n`. -/
theorem saw_nat_div {n b : ℕ} (hb : 0 < b) (hnz : n % b ≠ 0) :
    saw ((n : ℚ) / b) = ((n % b : ℕ) : ℚ) / b - 1 / 2 := by
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  have hs := div_split (n := n) hb
  have hfl := floor_nat_div (n := n) hb
  have hpos : (0 : ℚ) < ((n % b : ℕ) : ℚ) / b := by
    refine div_pos ?_ hbq
    exact_mod_cast Nat.pos_of_ne_zero hnz
  have hne : ((n : ℚ) / b) ≠ ((⌊(n : ℚ) / b⌋ : ℤ) : ℚ) := by
    rw [hfl, Int.cast_natCast, hs]
    intro h
    linarith
  unfold saw
  rw [if_neg hne, hfl, Int.cast_natCast, hs]
  ring

/-- `b ∤ hj` for `0 < j < b` when `gcd(h,b) = 1`. -/
theorem mul_mod_ne_zero {h b j : ℕ} (hc : Nat.Coprime h b) (hj0 : 0 < j) (hjb : j < b) :
    (h * j) % b ≠ 0 := by
  intro hz
  have hdvd : b ∣ h * j := Nat.dvd_of_mod_eq_zero hz
  have : b ∣ j := (Nat.Coprime.dvd_of_dvd_mul_left hc.symm hdvd)
  exact absurd (Nat.le_of_dvd hj0 this) (by omega)

/-- **The summand of `ded`, evaluated.**  This is where `saw_nat_div` is consumed. -/
theorem ded_term {h b j : ℕ} (hb : 0 < b) (hc : Nat.Coprime h b) (hj0 : 0 < j)
    (hjb : j < b) :
    saw ((j : ℚ) / b) * saw ((h : ℚ) * j / b)
      = ((j : ℚ) / b - 1 / 2) * ((((h * j) % b : ℕ) : ℚ) / b - 1 / 2) := by
  have hjmod : j % b ≠ 0 := by rw [Nat.mod_eq_of_lt hjb]; omega
  have h1 : saw ((j : ℚ) / b) = ((j : ℚ) / b - 1 / 2) := by
    rw [saw_nat_div hb hjmod, Nat.mod_eq_of_lt hjb]
  have hcast : (h : ℚ) * j / b = ((h * j : ℕ) : ℚ) / b := by push_cast; ring
  rw [h1, hcast, saw_nat_div hb (mul_mod_ne_zero hc hj0 hjb)]

/-- **The residues are a permutation**, so they sum to `∑ j`.  `mulPerm` supplies it. -/
theorem sum_residues {h b : ℕ} (hc : Nat.Coprime h b) :
    ∑ j : Fin b, ((h * j.val) % b) = ∑ j : Fin b, j.val := by
  have := Equiv.sum_comp (mulPerm h hc) (fun j : Fin b => j.val)
  simpa [mulPerm_val] using this

/-- The remaining summation bookkeeping of identity (8), carried. -/
def DedSumOf : Prop := ∀ h b : ℕ, 0 < b → Nat.Coprime h b →
  (∀ j : ℕ, 0 < j → j < b →
    saw ((j : ℚ) / b) * saw ((h : ℚ) * j / b)
      = ((j : ℚ) / b - 1 / 2) * ((((h * j) % b : ℕ) : ℚ) / b - 1 / 2)) →
  (∑ j : Fin b, ((h * j.val) % b) = ∑ j : Fin b, j.val) →
  ded h b
    = (∑ j ∈ range b, (j : ℚ) * (((h * j) % b : ℕ) : ℚ)) / (b : ℚ) ^ 2
      - ((b : ℚ) - 1) / 4

/-- **Identity (8), from the carried summation.**  Both of its inputs are proved above. -/
theorem saw_zero : saw 0 = 0 := by
  unfold saw
  simp

/-- **The summation step — proved.**  Every summand is expanded, the `j = 0` term is
absorbed by an `if`, and the three resulting sums are evaluated: Gauss for `∑ j`, the
permutation fact for `∑ r_j`, and a card count for the constant `1/4`. -/
theorem dedSum (h b : ℕ) (hb : 0 < b) (T : ℕ → ℚ) (hT0 : T 0 = 0)
    (hterm : ∀ j : ℕ, 0 < j → j < b →
      T j = ((j : ℚ) / (b : ℚ) - 1 / 2) * ((((h * j) % b : ℕ) : ℚ) / (b : ℚ) - 1 / 2))
    (hres : ∑ j ∈ range b, ((h * j) % b) = ∑ j ∈ range b, j) :
    ∑ j ∈ range b, T j
      = (∑ j ∈ range b, (j : ℚ) * ((((h * j) % b : ℕ)) : ℚ)) / (b : ℚ) ^ 2
        - ((b : ℚ) - 1) / 4 := by
  have hBq : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
  have hB : ((b : ℚ)) ≠ 0 := ne_of_gt hBq
  have hexp : ∀ j ∈ range b, T j
      = (j : ℚ) * ((((h * j) % b : ℕ)) : ℚ) / (b : ℚ) ^ 2
        - (j : ℚ) / (2 * (b : ℚ)) - ((((h * j) % b : ℕ)) : ℚ) / (2 * (b : ℚ))
        + (if j = 0 then 0 else 1 / 4) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [hT0]
    · rw [hterm j hj0 (Finset.mem_range.mp hj), if_neg (by omega)]
      field_simp
      ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div, ← Finset.sum_div]
  have e4 : ∑ j ∈ range b, (if j = 0 then (0 : ℚ) else 1 / 4) = ((b : ℚ) - 1) / 4 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
    have hset : (range b).filter (fun j => ¬ j = 0) = (range b).erase 0 := by
      ext x
      simp [Finset.mem_erase, and_comm]
    rw [hset, Finset.card_erase_of_mem (Finset.mem_range.mpr hb), Finset.card_range]
    have : ((b - 1 : ℕ) : ℚ) = (b : ℚ) - 1 := by
      have := Nat.cast_sub (R := ℚ) hb
      simpa using this
    rw [this]
    ring
  have e5 : (∑ j ∈ range b, ((((h * j) % b : ℕ)) : ℚ)) = ∑ j ∈ range b, (j : ℚ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum, hres]
  have e6 : (∑ j ∈ range b, (j : ℚ)) = ((b : ℚ) - 1) * (b : ℚ) / 2 := by
    have hn := Finset.sum_range_id_mul_two b
    have hq : ((∑ j ∈ range b, j : ℕ) : ℚ) * 2 = ((b * (b - 1) : ℕ) : ℚ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) hn
    rw [Nat.cast_mul, Nat.cast_sub hb, Nat.cast_sum] at hq
    push_cast at hq ⊢
    linarith
  rw [e4, e5, e6]
  field_simp
  ring

/-- **`DedSumOf` is now a theorem.** -/
theorem dedSumOf : DedSumOf := by
  intro h b hb hc hterm hres
  have hres' : ∑ j ∈ range b, ((h * j) % b) = ∑ j ∈ range b, j := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => (h * j) % b) b,
      ← Fin.sum_univ_eq_sum_range (fun j : ℕ => j) b]
    exact hres
  refine dedSum h b hb _ ?_ (fun j hj0 hjb => hterm j hj0 hjb) hres'
  simp [saw_zero]

theorem ded_eq {h b : ℕ} (hb : 0 < b) (hc : Nat.Coprime h b) :
    ded h b
      = (∑ j ∈ range b, (j : ℚ) * (((h * j) % b : ℕ) : ℚ)) / (b : ℚ) ^ 2
        - ((b : ℚ) - 1) / 4 :=
  dedSumOf h b hb hc (fun _ hj0 hjb => ded_term hb hc hj0 hjb) (sum_residues hc)

/-- **The denominator step (11).**  Given `b ∣ 2∑_{j<b} j²`, the residues `r_j ≡ uj (mod b)`
transfer the divisibility to `2∑ j·r_j`, making `2b·s(u;b)` an integer. -/
def Den3Of : Prop := ∀ u b : ℕ, 0 < b → Nat.Coprime u b →
  ((b : ℤ) ∣ 2 * ∑ j ∈ range b, (j : ℤ) ^ 2) →
  ∃ n : ℤ, 2 * (b : ℚ) * ded u b = (n : ℚ)

/-! ### The arithmetic behind the factor 3 — proved -/

/-- `6·∑_{j<b} j² = b(b−1)(2b−1)`, over `ℤ` so that `b = 0` needs no special case. -/
theorem six_sum_sq (b : ℕ) :
    6 * ∑ j ∈ range b, (j : ℤ) ^ 2 = (b : ℤ) * ((b : ℤ) - 1) * (2 * (b : ℤ) - 1) := by
  induction b with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      push_cast
      ring

/-- If `3 ∤ b` then `3 ∣ (b−1)(2b−1)`: one of the two factors is `≡ 0 (mod 3)`. -/
theorem three_dvd_of_not {b : ℕ} (h3 : ¬ (3 ∣ b)) :
    (3 : ℤ) ∣ ((b : ℤ) - 1) * (2 * (b : ℤ) - 1) := by
  have hb : b % 3 = 1 ∨ b % 3 = 2 := by omega
  have hz : (b : ℤ) % 3 = 1 ∨ (b : ℤ) % 3 = 2 := by omega
  rcases hz with h | h
  · exact Dvd.dvd.mul_right (by omega) _
  · exact Dvd.dvd.mul_left (by omega) _

/-- **`b ∣ 2∑_{j<b} j²` when `3 ∤ b`.**  `6∑ = b(b−1)(2b−1) = 3bk`, so `2∑ = bk`. -/
theorem two_sum_sq_dvd {b : ℕ} (h3 : ¬ (3 ∣ b)) :
    (b : ℤ) ∣ 2 * ∑ j ∈ range b, (j : ℤ) ^ 2 := by
  obtain ⟨k, hk⟩ := three_dvd_of_not h3
  refine ⟨k, ?_⟩
  have h6 : 6 * ∑ j ∈ range b, (j : ℤ) ^ 2
      = (b : ℤ) * (((b : ℤ) - 1) * (2 * (b : ℤ) - 1)) := by
    rw [six_sum_sq b]; ring
  rw [hk] at h6
  linarith

/-! #### `Den3Of` — proved

With identity (8) available, the denominator step is arithmetic: `2b·s(u;b) = 2S/b -
b(b-1)/2` where `S = ∑ j·r_j`, and both pieces are integers — the first because
`r_j ≡ uj (mod b)` transfers `b ∣ 2∑j²` to `b ∣ 2S`, the second because `b` and `b-1` are
consecutive. -/

/-- `n - (n mod b) = b·(n / b)` over `ℤ`, written without any `%`-cast lemma: the `ℕ`
identity `Nat.mod_add_div` is cast INWARD, so nothing can be reinterpreted. -/
theorem nat_mod_sub (n b : ℕ) :
    (n : ℤ) - ((n % b : ℕ) : ℤ) = (b : ℤ) * ((n / b : ℕ) : ℤ) := by
  have h := Nat.mod_add_div n b
  have hc : ((n % b : ℕ) : ℤ) + (b : ℤ) * ((n / b : ℕ) : ℤ) = (n : ℤ) := by
    rw [← Nat.cast_mul, ← Nat.cast_add, h]
  linarith

/-- `uj - (uj mod b) = b·(uj / b)`. -/
theorem mod_sub_eq {u b : ℕ} (j : ℕ) :
    (u : ℤ) * (j : ℤ) - ((((u * j) % b : ℕ)) : ℤ)
      = (b : ℤ) * ((((u * j) / b : ℕ)) : ℤ) := by
  have h := nat_mod_sub (u * j) b
  rw [Nat.cast_mul] at h
  exact h

theorem den3Of : Den3Of := by
  intro u b hb hc hdvd
  set S : ℤ := ∑ j ∈ range b, (j : ℤ) * ((((u * j) % b : ℕ)) : ℤ) with hSdef
  set Q : ℤ := ∑ j ∈ range b, (j : ℤ) ^ 2 with hQdef
  have hbq : ((b : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  -- `b ∣ S - u·Q`, termwise
  have hstep : (b : ℤ) ∣ (S - (u : ℤ) * Q) := by
    rw [hSdef, hQdef, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum (fun j _ => ?_)
    refine ⟨-((j : ℤ) * ((((u * j) / b : ℕ)) : ℤ)), ?_⟩
    have hm := mod_sub_eq (u := u) (b := b) j
    linear_combination (-(j : ℤ)) * hm
  -- hence `b ∣ 2S`
  obtain ⟨k, hk⟩ : (b : ℤ) ∣ 2 * S := by
    have h2 : 2 * S = 2 * (S - (u : ℤ) * Q) + (u : ℤ) * (2 * Q) := by ring
    rw [h2]
    exact dvd_add (Dvd.dvd.mul_left hstep 2) (Dvd.dvd.mul_left hdvd _)
  -- and `2 ∣ b(b-1)`
  obtain ⟨l, hl⟩ : (2 : ℤ) ∣ (b : ℤ) * ((b : ℤ) - 1) := by
    have he := Int.even_mul_succ_self ((b : ℤ) - 1)
    have : ((b : ℤ) - 1) * ((b : ℤ) - 1 + 1) = (b : ℤ) * ((b : ℤ) - 1) := by ring
    rw [this] at he
    exact he.two_dvd
  refine ⟨k - l, ?_⟩
  rw [ded_eq hb hc]
  have hSq : (∑ j ∈ range b, (j : ℚ) * (((u * j) % b : ℕ) : ℚ)) = (S : ℚ) := by
    rw [hSdef]
    push_cast
    rfl
  rw [hSq]
  have hkq : ((b : ℚ)) * (k : ℚ) = 2 * (S : ℚ) := by exact_mod_cast hk.symm
  have hlq : ((b : ℚ)) * ((b : ℚ) - 1) = 2 * (l : ℚ) := by exact_mod_cast hl
  have hS' : (S : ℚ) = (b : ℚ) * (k : ℚ) / 2 := by linarith
  have hl' : (l : ℚ) = (b : ℚ) * ((b : ℚ) - 1) / 2 := by linarith
  push_cast
  rw [hS', hl']
  field_simp
  ring

/-- The write-up's `Den3`, now a theorem rather than a hypothesis. -/
theorem den3 {u b : ℕ} (hb : 0 < b) (h3 : ¬ (3 ∣ b))
    (hc : Nat.Coprime u b) : ∃ n : ℤ, 2 * (b : ℚ) * ded u b = (n : ℚ) :=
  den3Of u b hb hc (two_sum_sq_dvd h3)

/-! #### Toward `Meyer`: the pointwise residue identity — proved

Meyer's formula comes from summing, over all pairs `0 ≤ i < j < b`, the identity

    r_{j-i} = r_j - r_i + b·[r_i > r_j].

That pointwise identity is `residue_diff`, proved here and **needing no coprimality at
all**: `r_{j-i}` and `r_j - r_i + b·[…]` both lie in `[0,b)` and are congruent mod `b`, so
they are equal.  What remains carried is the SUMMATION — reindexing the triangular pair set
by the difference `j - i` — which is `MeyerPairSum`. -/

/-- **The pointwise residue identity.**  No coprimality is needed. -/
theorem residue_diff (h b i j : ℕ) (hb : 0 < b) (hij : i < j) :
    (((h * (j - i)) % b : ℕ) : ℤ) + ((h * i % b : ℕ) : ℤ)
      = ((h * j % b : ℕ) : ℤ)
        + (b : ℤ) * (if (h * j) % b < (h * i) % b then 1 else 0) := by
  have e1 := nat_mod_sub (h * (j - i)) b
  have e2 := nat_mod_sub (h * j) b
  have e3 := nat_mod_sub (h * i) b
  have hsub : ((h * (j - i) : ℕ) : ℤ) = ((h * j : ℕ) : ℤ) - ((h * i : ℕ) : ℤ) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hij.le]
    ring
  set V : ℤ := (((h * (j - i)) % b : ℕ) : ℤ) with hVd
  set A : ℤ := ((h * j % b : ℕ) : ℤ) with hAd
  set C : ℤ := ((h * i % b : ℕ) : ℤ) with hCd
  set m : ℤ := (((h * j) / b : ℕ) : ℤ) - (((h * i) / b : ℕ) : ℤ)
    - (((h * (j - i)) / b : ℕ) : ℤ) with hmd
  have hkey : V - A + C = (b : ℤ) * m := by rw [hmd]; linarith
  have hbz : (0 : ℤ) < (b : ℤ) := by exact_mod_cast hb
  have hAz : A < (b : ℤ) := by rw [hAd]; exact_mod_cast Nat.mod_lt _ hb
  have hCz : C < (b : ℤ) := by rw [hCd]; exact_mod_cast Nat.mod_lt _ hb
  have hVz : V < (b : ℤ) := by rw [hVd]; exact_mod_cast Nat.mod_lt _ hb
  have hA0 : (0 : ℤ) ≤ A := by rw [hAd]; exact Int.natCast_nonneg _
  have hC0 : (0 : ℤ) ≤ C := by rw [hCd]; exact Int.natCast_nonneg _
  have hV0 : (0 : ℤ) ≤ V := by rw [hVd]; exact Int.natCast_nonneg _
  split_ifs with hlt
  · have hltz : A < C := by rw [hAd, hCd]; exact_mod_cast hlt
    have h1 : (0 : ℤ) < (b : ℤ) * m := by linarith
    have h2 : (b : ℤ) * m < 2 * (b : ℤ) := by linarith
    have hm1 : m = 1 := by nlinarith
    rw [hm1] at hkey
    linarith
  · have hgez : C ≤ A := by
      rw [hAd, hCd]
      exact_mod_cast Nat.le_of_not_lt hlt
    have h1 : -(b : ℤ) < (b : ℤ) * m := by linarith
    have h2 : (b : ℤ) * m < (b : ℤ) := by linarith
    have hm0 : m = 0 := by nlinarith
    rw [hm0] at hkey
    linarith

/-- The rational form of `residue_diff`, which is what the summation consumes. -/
theorem residue_diff_rat (h b i j : ℕ) (hb : 0 < b) (hij : i < j) :
    (((h * (j - i)) % b : ℕ) : ℚ)
      = ((h * j % b : ℕ) : ℚ) - ((h * i % b : ℕ) : ℚ)
        + (b : ℚ) * (if (h * j) % b < (h * i) % b then 1 else 0) := by
  have h1 := residue_diff h b i j hb hij
  have h2 : (((h * (j - i)) % b : ℕ) : ℚ) + ((h * i % b : ℕ) : ℚ)
      = ((h * j % b : ℕ) : ℚ)
        + (b : ℚ) * (if (h * j) % b < (h * i) % b then 1 else 0) := by
    split_ifs at h1 ⊢ with hlt
    · exact_mod_cast h1
    · exact_mod_cast h1
  linarith

/-! #### The triangular toolkit

Three `Finset` facts, all campaign-agnostic: counting below `j` is the same in `Fin b` as
in `ℕ`; the inner reindex `i ↦ j - i`; and the triangular swap, which turns an inner
summand independent of `j` into a multiplicity. -/

theorem card_Iio_filter {b : ℕ} (j : Fin b) (Q : ℕ → Prop) [DecidablePred Q] :
    ((Finset.Iio j).filter (fun i : Fin b => Q i.val)).card
      = ((Finset.range j.val).filter (fun i => Q i)).card := by
  classical
  apply Finset.card_bij (fun (i : Fin b) _ => i.val)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Iio] at ha
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨ha.1, ha.2⟩
  · intro a _ a' _ hEq
    exact Fin.ext hEq
  · intro c hcm
    simp only [Finset.mem_filter, Finset.mem_range] at hcm
    refine ⟨⟨c, lt_trans hcm.1 j.isLt⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_Iio]
    exact ⟨hcm.1, hcm.2⟩

/-- **`invNum` as a nested `ℕ`-sum.** -/
theorem invNum_range (h b : ℕ) :
    (invNum h b)
      = ∑ j ∈ range b, ∑ i ∈ range j,
          (if (h * j) % b < (h * i) % b then 1 else 0) := by
  classical
  rw [invNum, ← Fin.sum_univ_eq_sum_range
    (fun j => ∑ i ∈ range j, (if (h * j) % b < (h * i) % b then 1 else 0)) b]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [card_Iio_filter j (fun i => (h * j.val) % b < (h * i) % b), Finset.card_filter]

theorem inner_reflect (j : ℕ) (f : ℕ → ℚ) :
    ∑ i ∈ range j, f (j - i) = ∑ i ∈ range j, f (i + 1) := by
  rw [← Finset.sum_range_reflect (fun i => f (j - i)) j]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hEq : j - (j - 1 - i) = i + 1 := by
    have := Finset.mem_range.mp hi
    omega
  rw [hEq]

theorem tri_swap (b : ℕ) (g : ℕ → ℚ) :
    (∑ j ∈ range b, ∑ i ∈ range j, g i)
      = ∑ i ∈ range b, ((b - (i + 1) : ℕ) : ℚ) * g i := by
  simp only [Finset.range_eq_Ico]
  rw [← Finset.sum_Ico_Ico_comm' 0 b (fun i _ => g i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]

theorem tri_diff (b : ℕ) (f : ℕ → ℚ) :
    (∑ j ∈ range b, ∑ i ∈ range j, f (j - i))
      = ∑ i ∈ range b, ((b - (i + 1) : ℕ) : ℚ) * f (i + 1) := by
  rw [Finset.sum_congr rfl (fun j _ => inner_reflect j f)]
  exact tri_swap b (fun i => f (i + 1))

/-- Gauss, over `ℚ`. -/
theorem sum_range_cast (b : ℕ) : ∑ j ∈ range b, (j : ℚ) = (b : ℚ) * ((b : ℚ) - 1) / 2 := by
  induction b with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- The remaining half of Meyer: summing `residue_diff` over the triangular pair set and
reindexing by the difference `j - i`.  Carried. -/
def MeyerPairSum : Prop := ∀ h b : ℕ, 0 < b → Nat.Coprime h b →
  (∀ i j : ℕ, i < j → j < b →
    (((h * (j - i)) % b : ℕ) : ℚ) = ((h * j % b : ℕ) : ℚ) - ((h * i % b : ℕ) : ℚ)
      + (b : ℚ) * (if (h * j) % b < (h * i) % b then 1 else 0)) →
  (b : ℚ) * (invNum h b : ℚ)
    = (2 * (b : ℚ) - 1) * (b : ℚ) * ((b : ℚ) - 1) / 2
      - 3 * ∑ j ∈ range b, (j : ℚ) * (((h * j) % b : ℕ) : ℚ)

/-- **`MeyerPairSum` is a theorem.**  The triangular sum `∑_{j<b} ∑_{i<j} r_{j-i}` is
computed two ways: by `tri_diff` (reindexing by the difference) and by `residue_diff`
(expanding each term).  Equating them, and using that the residues sum to `∑ j`, gives the
pair-sum identity. -/
theorem meyerPairSum : MeyerPairSum := by
  intro h b hb hc hrd
  classical
  set R : ℕ → ℚ := fun n => (((h * n) % b : ℕ) : ℚ) with hRd
  -- the residues sum to `∑ j`
  have hres : ∑ j ∈ range b, ((h * j) % b) = ∑ j ∈ range b, j := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => (h * j) % b) b,
      ← Fin.sum_univ_eq_sum_range (fun j : ℕ => j) b]
    exact sum_residues hc
  have hRsum : ∑ d ∈ range b, R d = (b : ℚ) * ((b : ℚ) - 1) / 2 := by
    have : ∑ d ∈ range b, R d = ∑ d ∈ range b, (d : ℚ) := by
      rw [hRd]
      rw [← Nat.cast_sum, ← Nat.cast_sum, hres]
    rw [this, sum_range_cast]
  -- the inversion count, as a rational double sum
  have hind : ((invNum h b : ℕ) : ℚ)
      = ∑ j ∈ range b, ∑ i ∈ range j,
          (if (h * j) % b < (h * i) % b then (1 : ℚ) else 0) := by
    rw [invNum_range h b]
    push_cast
    rfl
  -- the triangular sum, expanded termwise
  have hT2 : (∑ j ∈ range b, ∑ i ∈ range j, R (j - i))
      = (∑ j ∈ range b, (j : ℚ) * R j)
        - (∑ j ∈ range b, ∑ i ∈ range j, R i)
        + (b : ℚ) * ((invNum h b : ℕ) : ℚ) := by
    rw [hind, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j hjm => ?_)
    have hjb := Finset.mem_range.mp hjm
    have hterm : ∀ i ∈ range j, R (j - i)
        = R j - R i + (b : ℚ) * (if (h * j) % b < (h * i) % b then (1 : ℚ) else 0) :=
      fun i him => hrd i j (Finset.mem_range.mp him) hjb
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
  -- the shift `i ↦ i+1`
  have hshift : (∑ i ∈ range b, ((b - (i + 1) : ℕ) : ℚ) * R (i + 1))
      = ∑ d ∈ range b, ((b - d : ℕ) : ℚ) * R d := by
    have hA := Finset.sum_range_succ' (fun d => ((b - d : ℕ) : ℚ) * R d) b
    have hB := Finset.sum_range_succ (fun d => ((b - d : ℕ) : ℚ) * R d) b
    have h0 : ((b - 0 : ℕ) : ℚ) * R 0 = 0 := by simp [hRd]
    have hbb : ((b - b : ℕ) : ℚ) * R b = 0 := by simp
    rw [h0, add_zero] at hA
    rw [hbb, add_zero] at hB
    rw [← hA, hB]
  -- equate the two computations and finish
  have hkey := (tri_diff b R).symm.trans hT2
  rw [hshift, tri_swap b R] at hkey
  -- turn the ℕ-subtractions into ℚ-subtractions
  have hc1 : (∑ d ∈ range b, ((b - d : ℕ) : ℚ) * R d)
      = ∑ d ∈ range b, ((b : ℚ) - (d : ℚ)) * R d :=
    Finset.sum_congr rfl (fun d hd => by
      rw [Nat.cast_sub (le_of_lt (Finset.mem_range.mp hd))])
  have hc2 : (∑ i ∈ range b, ((b - (i + 1) : ℕ) : ℚ) * R i)
      = ∑ i ∈ range b, ((b : ℚ) - (i : ℚ) - 1) * R i :=
    Finset.sum_congr rfl (fun i hi => by
      rw [Nat.cast_sub (Finset.mem_range.mp hi)]
      push_cast
      ring)
  rw [hc1, hc2] at hkey
  -- collect: `∑ (2b - 2d - 1) R d = ∑ d R d + b I`
  have hcollect : (∑ d ∈ range b, ((b : ℚ) - (d : ℚ)) * R d)
      + (∑ d ∈ range b, ((b : ℚ) - (d : ℚ) - 1) * R d)
      = (2 * (b : ℚ) - 1) * (∑ d ∈ range b, R d)
        - 2 * (∑ d ∈ range b, (d : ℚ) * R d) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun d _ => by ring)
  rw [hRsum] at hcollect
  linarith [hkey, hcollect]

/-- **`Meyer` from the pair sum**, using the proved identity (8).  The algebraic content is
`(b-1)(b-2)/4 + 3b(b-1)/4 = (b-1)(2b-1)/2`. -/
theorem meyerOf (hP : MeyerPairSum) : Meyer := by
  intro h b hb hc
  have hbq : ((b : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  have hps := hP h b hb hc (fun i j hij _ => residue_diff_rat h b i j hb hij)
  rw [ded_eq hb hc]
  refine mul_left_cancel₀ hbq ?_
  rw [hps]
  field_simp
  ring

/-- **The inversion formula is a theorem.**  Nothing is carried on this row any more. -/
theorem meyer : Meyer := meyerOf meyerPairSum

/-! #### The folding identity `s(2c;2b) = s(c;b)`

This is what specialises the general Theorem 2 to Conjecture 13.  Pair `j` with `j + b` in
`range (2b)`: the SECOND factor is unchanged, because
`(2c(b+i)) mod 2b = 2·((ci) mod b)` scales exactly; and the two FIRST factors add to
`((i/b))`, because `((i/2b)) + (((b+i)/2b)) = ((i/b))`.  No periodicity or duplication lemma
for the sawtooth is needed — everything routes through `saw_nat_div`. -/

/-- `(2c(b+i)) mod 2b = 2·((ci) mod b)`; no coprimality needed. -/
theorem mod_scale_shift (c b i : ℕ) : (2 * c * (b + i)) % (2 * b) = 2 * ((c * i) % b) := by
  have h1 : 2 * c * (b + i) = 2 * c * i + 2 * b * c := by ring
  rw [h1, Nat.add_mul_mod_self_left, show 2 * c * i = 2 * (c * i) from by ring,
    Nat.mul_mod_mul_left]

/-- The same without the shift. -/
theorem mod_scale (c b i : ℕ) : (2 * c * i) % (2 * b) = 2 * ((c * i) % b) := by
  rw [show 2 * c * i = 2 * (c * i) from by ring, Nat.mul_mod_mul_left]

/-- **The two first factors add.**  `((i/2b)) + (((b+i)/2b)) = ((i/b))` for `i < b`. -/
theorem saw_fold {b i : ℕ} (hb : 0 < b) (hi : i < b) :
    saw ((i : ℚ) / ((2 * b : ℕ) : ℚ)) + saw (((b + i : ℕ) : ℚ) / ((2 * b : ℕ) : ℚ))
      = saw ((i : ℚ) / ((b : ℕ) : ℚ)) := by
  have h2b : 0 < 2 * b := by omega
  have hbq : (0 : ℚ) < ((b : ℕ) : ℚ) := by exact_mod_cast hb
  have hmod2 : (b + i) % (2 * b) = b + i := Nat.mod_eq_of_lt (by omega)
  have hne2 : (b + i) % (2 * b) ≠ 0 := by rw [hmod2]; omega
  have hsecond := saw_nat_div (n := b + i) (b := 2 * b) h2b hne2
  rw [hmod2] at hsecond
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · have hbne : ((b : ℕ) : ℚ) ≠ 0 := ne_of_gt hbq
    simp only [Nat.cast_zero, zero_div, saw_zero, add_zero] at hsecond ⊢
    rw [hsecond]
    push_cast
    field_simp
    ring
  · have hmod1 : i % (2 * b) = i := Nat.mod_eq_of_lt (by omega)
    have hne1 : i % (2 * b) ≠ 0 := by rw [hmod1]; omega
    have hfirst := saw_nat_div (n := i) (b := 2 * b) h2b hne1
    rw [hmod1] at hfirst
    have hmod3 : i % b = i := Nat.mod_eq_of_lt hi
    have hne3 : i % b ≠ 0 := by rw [hmod3]; omega
    have hthird := saw_nat_div (n := i) (b := b) hb hne3
    rw [hmod3] at hthird
    rw [hfirst, hsecond, hthird]
    push_cast
    field_simp
    ring

/-- `((b/2b)) = 0`: the half-integer is a zero of the sawtooth. -/
theorem saw_half {b : ℕ} (hb : 0 < b) : saw (((b : ℕ) : ℚ) / ((2 * b : ℕ) : ℚ)) = 0 := by
  have h2b : 0 < 2 * b := by omega
  have hbq : (0 : ℚ) < ((b : ℕ) : ℚ) := by exact_mod_cast hb
  have hbne : ((b : ℕ) : ℚ) ≠ 0 := ne_of_gt hbq
  have hmod : b % (2 * b) = b := Nat.mod_eq_of_lt (by omega)
  have hne : b % (2 * b) ≠ 0 := by rw [hmod]; omega
  have hs := saw_nat_div (n := b) (b := 2 * b) h2b hne
  rw [hmod] at hs
  rw [hs]
  push_cast
  field_simp
  ring

/-- **The second factor is unchanged by the fold and by the scaling.** -/
theorem saw_scaled {c b i : ℕ} (hb : 0 < b) (hc : Nat.Coprime c b) (hi0 : 0 < i)
    (hib : i < b) (k : ℕ) (hk : (2 * c * k) % (2 * b) = 2 * ((c * i) % b)) :
    saw (((2 * c : ℕ) : ℚ) * (k : ℚ) / ((2 * b : ℕ) : ℚ))
      = saw ((c : ℚ) * (i : ℚ) / ((b : ℕ) : ℚ)) := by
  have h2b : 0 < 2 * b := by omega
  have hbq : (0 : ℚ) < ((b : ℕ) : ℚ) := by exact_mod_cast hb
  have hbne : ((b : ℕ) : ℚ) ≠ 0 := ne_of_gt hbq
  have hres : (c * i) % b ≠ 0 := mul_mod_ne_zero hc hi0 hib
  have hcast1 : ((2 * c : ℕ) : ℚ) * (k : ℚ) / ((2 * b : ℕ) : ℚ)
      = (((2 * c * k : ℕ)) : ℚ) / ((2 * b : ℕ) : ℚ) := by push_cast; ring
  have hcast2 : (c : ℚ) * (i : ℚ) / ((b : ℕ) : ℚ)
      = (((c * i : ℕ)) : ℚ) / ((b : ℕ) : ℚ) := by push_cast; ring
  rw [hcast1, hcast2,
    saw_nat_div (n := 2 * c * k) (b := 2 * b) h2b (by rw [hk]; omega),
    saw_nat_div (n := c * i) (b := b) hb hres, hk]
  push_cast
  field_simp

/-- **The folding identity.**  `s(2c; 2b) = s(c; b)`. -/
theorem ded_fold (c b : ℕ) (hb : 0 < b) (hc : Nat.Coprime c b) :
    ded (2 * c) (2 * b) = ded c b := by
  have h2b : 0 < 2 * b := by omega
  rw [ded, ded]
  rw [show 2 * b = b + b from by ring] at *
  rw [Finset.sum_range_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hib := Finset.mem_range.mp hi
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · have hz : ((0 : ℕ) : ℚ) / ((b + b : ℕ) : ℚ) = 0 := by simp
    have hz2 : ((0 : ℕ) : ℚ) / ((b : ℕ) : ℚ) = 0 := by simp
    have hh := saw_half (b := b) hb
    rw [show 2 * b = b + b from by ring] at hh
    simp only [Nat.cast_zero, zero_div, saw_zero, add_zero, mul_zero] at *
    rw [hh]
    ring
  · have hfold := saw_fold (b := b) (i := i) hb hib
    rw [show 2 * b = b + b from by ring] at hfold
    have hs1 := saw_scaled (c := c) (b := b) (i := i) hb hc hi0 hib i (mod_scale c b i)
    have hs2 := saw_scaled (c := c) (b := b) (i := i) hb hc hi0 hib (b + i)
      (mod_scale_shift c b i)
    rw [show 2 * b = b + b from by ring] at hs1 hs2
    rw [hs1, hs2, ← add_mul, hfold]

/-! ### The composition -/

theorem coprime_pieces {h t b : ℕ} (hc : Nat.Coprime (h * t) b) :
    Nat.Coprime h b ∧ Nat.Coprime (h * t) b ∧ Nat.Coprime (h * t ^ 2) b := by
  have h1 : Nat.Coprime h b := Nat.Coprime.coprime_dvd_left (dvd_mul_right h t) hc
  have h2 : Nat.Coprime t b := Nat.Coprime.coprime_dvd_left (dvd_mul_left t h) hc
  exact ⟨h1, hc, Nat.Coprime.mul_left h1 (h2.pow_left 2)⟩

/-- **The write-up's equation (10).**  Substituting Meyer three times makes the
`(b−1)(b−2)` constants cancel exactly. -/
theorem Dsum_eq_inv {h t b : ℕ} (hb : 0 < b) (hc : Nat.Coprime (h * t) b) :
    Dsum h t b
      = 4 * (invNum (h * t) b : ℚ) - 2 * ((invNum h b : ℚ) + (invNum (h * t ^ 2) b : ℚ)) := by
  obtain ⟨c1, c2, c3⟩ := coprime_pieces hc
  have e1 := meyer h b hb c1
  have e2 := meyer (h * t) b hb c2
  have e3 := meyer (h * t ^ 2) b hb c3
  simp only [Dsum]
  linarith

/-- **`D_b(h,t) ∈ 4ℤ`.** -/
theorem Dsum_four {h t b : ℕ} (hb : 0 < b)
    (hc : Nat.Coprime (h * t) b) : ∃ m : ℤ, Dsum h t b = 4 * (m : ℚ) := by
  obtain ⟨k, hk⟩ := signParity h t b hb hc
  refine ⟨(invNum (h * t) b : ℤ) - (k : ℤ), ?_⟩
  rw [Dsum_eq_inv hb hc]
  have hk' : ((invNum h b : ℚ) + (invNum (h * t ^ 2) b : ℚ)) = (k : ℚ) + (k : ℚ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) hk
  rw [hk']
  push_cast
  ring

/-- **`D_b(h,t) ∈ 12ℤ` when `3 ∤ b`.**  `6b·s(u;b) = 3·(2b·s(u;b))` is a multiple of 3
termwise by `den3`, and `gcd(3,4) = 1`. -/
theorem Dsum_twelve {h t b : ℕ} (hb : 0 < b)
    (h3 : ¬ (3 ∣ b)) (hc : Nat.Coprime (h * t) b) : ∃ m : ℤ, Dsum h t b = 12 * (m : ℚ) := by
  obtain ⟨c1, c2, c3⟩ := coprime_pieces hc
  obtain ⟨n1, hn1⟩ := den3 hb h3 c1
  obtain ⟨n2, hn2⟩ := den3 hb h3 c3
  obtain ⟨n3, hn3⟩ := den3 hb h3 c2
  obtain ⟨m4, hm4⟩ := Dsum_four hb hc
  -- `D = 3·(n₁ + n₂ − 2n₃)`, so `3 ∣ D`; with `4 ∣ D` and `gcd(3,4) = 1`, `12 ∣ D`
  have h3D : Dsum h t b = 3 * ((n1 : ℚ) + (n2 : ℚ) - 2 * (n3 : ℚ)) := by
    simp only [Dsum]
    linarith
  set N : ℤ := n1 + n2 - 2 * n3 with hN
  have hcast : Dsum h t b = 3 * (N : ℚ) := by rw [h3D, hN]; push_cast; ring
  have heq : (3 : ℚ) * (N : ℚ) = 4 * (m4 : ℚ) := by rw [← hcast, hm4]
  have hZ : (3 : ℤ) * N = 4 * m4 := by exact_mod_cast heq
  have h4N : (4 : ℤ) ∣ N := by
    have ha : (4 : ℤ) ∣ 3 * N := ⟨m4, hZ⟩
    have hb4 : (4 : ℤ) ∣ 4 * N := dvd_mul_right 4 N
    have hd := dvd_sub hb4 ha
    have hsub : (4 : ℤ) * N - 3 * N = N := by ring
    rwa [hsub] at hd
  obtain ⟨m, hm⟩ := h4N
  refine ⟨m, ?_⟩
  rw [hcast, hm]
  push_cast
  ring

/-! ### Conjecture 13 itself

The write-up's Theorem 1.  Shibukawa's rational part is
`Q(a;b) = 6·(s(a;2b) + s(2a;b) − 2·s(a;b))` (equation (3)), and the conjecture asserts that
for even `a` coprime to a positive odd `b` the integer `b·Q(a;b)` lies in `4ℤ`, and in `12ℤ`
when `3 ∤ b`.  Writing `a = 2c`, the folding identity `s(2c;2b) = s(c;b)` turns `b·Q(2c;b)`
into `D_b(c,2)`, and Theorem 2 — proved above with no hypothesis beyond coprimality —
delivers both divisibilities. -/

/-- Shibukawa's rational part, equation (3) of the write-up. -/
noncomputable def Qsum (a b : ℕ) : ℚ :=
  6 * (ded a (2 * b) + ded (2 * a) b - 2 * ded a b)

/-- **The specialisation.**  `b·Q(2c;b) = D_b(c,2)`.  The only content is `ded_fold`: the
first term of `Q` is `s(2c;2b)`, and folding turns it into the `s(c;b)` that `D_b(c,2)`
wants. -/
theorem Qsum_eq_Dsum {c b : ℕ} (hb : 0 < b) (hc : Nat.Coprime c b) :
    (b : ℚ) * Qsum (2 * c) b = Dsum c 2 b := by
  have hfold : ded (2 * c) (2 * b) = ded c b := ded_fold c b hb hc
  simp only [Qsum, Dsum]
  rw [hfold, show (2 : ℕ) * (2 * c) = c * 2 ^ 2 from by ring,
    show (2 : ℕ) * c = c * 2 from by ring]
  ring

/-- **CONJECTURE 13 (Shibukawa), the `4ℤ` half.**  For even `a` coprime to a positive odd
`b`, `b·Q(a;b) ∈ 4ℤ`.  (`Odd b` is the source's hypothesis and supplies `0 < b`; it is in
fact redundant, since `gcd(a,b) = 1` with `a` even already forces `b` odd.) -/
theorem conjecture13 {a b : ℕ} (hodd : Odd b) (ha : Even a) (hab : Nat.Coprime a b) :
    ∃ m : ℤ, (b : ℚ) * Qsum a b = 4 * (m : ℚ) := by
  obtain ⟨c, rfl⟩ : ∃ c, a = 2 * c := by
    obtain ⟨r, hr⟩ := ha
    exact ⟨r, by omega⟩
  obtain ⟨k, hk⟩ := hodd
  have hb : 0 < b := by omega
  have hc : Nat.Coprime c b := Nat.Coprime.coprime_dvd_left (dvd_mul_left c 2) hab
  rw [Qsum_eq_Dsum hb hc]
  exact Dsum_four hb (by rwa [Nat.mul_comm c 2])

/-- **CONJECTURE 13 (Shibukawa), the `12ℤ` half.**  If in addition `3 ∤ b`, then
`b·Q(a;b) ∈ 12ℤ`. -/
theorem conjecture13_twelve {a b : ℕ} (hodd : Odd b) (h3 : ¬ (3 ∣ b)) (ha : Even a)
    (hab : Nat.Coprime a b) : ∃ m : ℤ, (b : ℚ) * Qsum a b = 12 * (m : ℚ) := by
  obtain ⟨c, rfl⟩ : ∃ c, a = 2 * c := by
    obtain ⟨r, hr⟩ := ha
    exact ⟨r, by omega⟩
  obtain ⟨k, hk⟩ := hodd
  have hb : 0 < b := by omega
  have hc : Nat.Coprime c b := Nat.Coprime.coprime_dvd_left (dvd_mul_left c 2) hab
  rw [Qsum_eq_Dsum hb hc]
  exact Dsum_twelve hb h3 (by rwa [Nat.mul_comm c 2])

end Principia.MathDB.P342271
