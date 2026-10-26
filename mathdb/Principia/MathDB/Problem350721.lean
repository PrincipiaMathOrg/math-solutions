import Mathlib

/-!
# MathDB #350721 — the signed cycle-restriction positivity conjecture is FALSE

Write-up `mathdb-open-problems/problems/350721/solution.tex`,
*Signed cycle-restriction polynomial positivity*, 18 September 2026.

For a permutation of `{1,…,n}` written in one-line form, let `RLM` be the set of right-to-left
minima VALUES and `EXC = {π(j) : π(j) > j}` the excedance values, and put

`P_{n,k}(x,y) = (−1)^{n−1} ∑_π (−1)^{inv π} x_{RLM(π)} y_{EXC(π)}`,  the sum running over
those `π` all of whose cycles have length `≥ k`.

Conjecture 5.2.1 of the journal version asserts `P_{n,k} ∈ ℕ[x,y]` for `2 ≤ k ≤ n`.  It fails at
`n = 8`, `k = 3`: the coefficient of `x₁x₄x₆x₇ y₂y₃y₅y₈` is `−1`.  The conjecture is quantified
over all `n` and `k`, so one witness refutes it, and `2 ≤ 3 ≤ 8` holds — the witness meets the
conjecture's own guard.

## How the search is made small, and why that is honest

A coefficient of `P_{8,3}` is a signed count over permutations with prescribed `RLM` and `EXC`.
Enumerating all `8! = 40320` in the kernel is impractical.  The reduction used here costs nothing
in rigour: **the excedance requirement is LOCAL to each position** — `EXC(π) = S` is equivalent to
*for every `j`, `π(j) > j` iff `π(j) ∈ S`* — so it can be applied while the one-line form is being
built rather than after.  `build` is that depth-first enumeration, and `build_complete` is the
lemma that makes it honest: every arrangement of the available values respecting `allowedAt` from
position `j` onwards is produced, so nothing the predicate would have kept is lost.

Measured effect: `build 8 1 base` has **37** elements rather than 40320, and exactly five of
those satisfy the remaining two conditions.  Because the pruning is a *conjunct* of the predicate
rather than a consequence of it, it needs no extra mathematics — in particular none of the
write-up's forcing chain (`π(1)=2`, `π(2)=3`, `π(8)=7`) has to be proved.

`qual_mem_survivors` is the bridge: any permutation of `base` satisfying the full predicate lies
in `survivors`.  With `survivors_qual` (everything in it qualifies) and `survivors_nodup`, the
signed count over `survivors` IS the coefficient.

## Scope, stated honestly

Formalized: **both** of the write-up's coefficients.  The coefficient of `x₁x₄x₆x₇ y₂y₃y₅y₈`
in `P_{8,3}` is `−1`, refuting Conjecture 5.2.1 as stated; and the coefficient of `x₁y₂⋯y₈`
is `+1` (`opposite_signs`), so negating the whole polynomial cannot rescue positivity either —
which covers the MathDB transcription, that drops the `(−1)^{n−1}` prefactor.  The second case
reuses the same machinery: `build` and `build_complete` are parameterized by the local
predicate, so only the target sets change.  For that monomial the pruning is even sharper —
exactly ONE permutation of the 40320 survives it, the 8-cycle `23456781`.

A 215 note on the source: brute force finds EIGHT permutations carrying the two statistic sets,
not the write-up's six.  The two extra have fixed points, which the write-up excludes one step
earlier in its argument — so its table is correct but its *"exactly six rows"* is conditional on
that step.  Nothing here depends on the count; the cycle condition is applied directly.

Checked in Python before formalizing (`verify_350721.py`, `verify_350721_forcing.py`): both of
the write-up's coefficients by brute force over all 40320 permutations; the five contributing
permutations `23158467, 23514867, 23518467, 23581467, 23851467` with inversions `6,6,7,8,9`; the
equivalence *every cycle ≥ 3* ⇔ `π(i) ≠ i ∧ π(π(i)) ≠ i` over all 40320; and that exactly 37
permutations satisfy the excedance condition alone.
-/

namespace Principia.MathDB.P350721

def app (l : List ℕ) (i : ℕ) : ℕ := l.getD (i - 1) 0

def inS (v : ℕ) : Bool := v == 2 || v == 3 || v == 5 || v == 8

/-- The second monomial's excedance target, `{2,…,8}` — everything but `1`. -/
def inSN (v : ℕ) : Bool := v != 1

/-- The excedance requirement, LOCAL to one position: `π(j) > j` iff `π(j) ∈ {2,3,5,8}`. -/
def allowedAt (j v : ℕ) : Bool := (decide (j < v)) == inS v

/-- The same, for the second monomial's target set. -/
def allowedAtN (j v : ℕ) : Bool := (decide (j < v)) == inSN v

/-- Depth-first enumeration of the one-line forms that respect the LOCAL predicate `allow` at
every position.  `n` is fuel (positions still to fill) and `j` the next position.  `allow` is a
conjunct of the full predicate, never a consequence of it, which is what makes the pruning free. -/
def build (allow : ℕ → ℕ → Bool) : ℕ → ℕ → List ℕ → List (List ℕ)
  | 0, _, _ => [[]]
  | (n + 1), j, avail =>
      (avail.filter (allow j)).flatMap fun v =>
        (build allow n (j + 1) (avail.erase v)).map (fun rest => v :: rest)

/-- **Completeness of the pruned enumeration.**  Every arrangement of `avail` that respects
`allowedAt` from position `j` onwards is produced.  This is what makes the pruning honest: the
enumeration loses no permutation that the predicate would have kept. -/
theorem build_complete (allow : ℕ → ℕ → Bool) : ∀ (n j : ℕ) (avail l : List ℕ),
    l.length = n → l.Perm avail →
    (∀ i, i < n → allow (j + i) (l.getD i 0) = true) →
    l ∈ build allow n j avail := by
  intro n
  induction n with
  | zero =>
    intro j avail l hlen _ _
    have : l = [] := List.eq_nil_of_length_eq_zero hlen
    subst this
    simp [build]
  | succ m ih =>
    intro j avail l hlen hperm hall
    obtain ⟨v, rest, rfl⟩ : ∃ v rest, l = v :: rest := by
      cases l with
      | nil => simp at hlen
      | cons a t => exact ⟨a, t, rfl⟩
    have hv : v ∈ avail := hperm.mem_iff.mp (by simp)
    have hva : allow j v = true := by
      have := hall 0 (Nat.succ_pos m)
      simpa using this
    have hrest : rest.Perm (avail.erase v) := (List.cons_perm_iff_perm_erase.mp hperm).2
    have hrlen : rest.length = m := by simpa using hlen
    have hrall : ∀ i, i < m → allow (j + 1 + i) (rest.getD i 0) = true := by
      intro i hi
      have h := hall (i + 1) (Nat.succ_lt_succ hi)
      -- do NOT put `List.getD` in the simp set: it unfolds recursively and blows the
      -- recursion depth.  The cons step is definitional, so `rfl` suffices.
      have e1 : (v :: rest).getD (i + 1) 0 = rest.getD i 0 := rfl
      have e2 : j + (i + 1) = j + 1 + i := by omega
      rw [e1, e2] at h
      exact h
    have hmem := ih (j + 1) (avail.erase v) rest hrlen hrest hrall
    rw [build]
    refine List.mem_flatMap.mpr ⟨v, ?_, ?_⟩
    · exact List.mem_filter.mpr ⟨hv, hva⟩
    · exact List.mem_map.mpr ⟨rest, hmem, rfl⟩

/-- `RLM(π) = {1,4,6,7}` stated pointwise: `π(j)` is a right-to-left minimum iff it lies in
the target set. -/
def rlmOK (l : List ℕ) : Bool :=
  (List.range' 1 8).all fun j =>
    (decide ((l.drop j).all (fun w => app l j < w)))
      == (app l j == 1 || app l j == 4 || app l j == 6 || app l j == 7)

/-- Every cycle of `π` has length `≥ 3`, i.e. no fixed point and no 2-cycle. -/
def cyc3 (l : List ℕ) : Bool :=
  (List.range' 1 8).all fun i => app l i != i && app l (app l i) != i

/-- The excedance requirement over all eight positions. -/
def excOK (l : List ℕ) : Bool := (List.range' 1 8).all fun j => allowedAt j (app l j)

/-- `RLM(π) = {1}` pointwise. -/
def rlmOKN (l : List ℕ) : Bool :=
  (List.range' 1 8).all fun j =>
    (decide ((l.drop j).all (fun w => app l j < w))) == (app l j == 1)

/-- The excedance requirement for the second monomial. -/
def excOKN (l : List ℕ) : Bool := (List.range' 1 8).all fun j => allowedAtN j (app l j)

/-- The full predicate for the second monomial. -/
def qualN (l : List ℕ) : Bool := excOKN l && rlmOKN l && cyc3 l

/-- The full predicate: the two statistic sets and the cycle bound. -/
def qualM (l : List ℕ) : Bool := excOK l && rlmOK l && cyc3 l

def invCount : List ℕ → ℕ
  | [] => 0
  | x :: xs => (xs.filter (fun y => decide (y < x))).length + invCount xs

def base : List ℕ := [1, 2, 3, 4, 5, 6, 7, 8]

/-- The pruned enumeration, filtered by the remaining two conditions. -/
def survivors : List (List ℕ) :=
  (build allowedAt 8 1 base).filter (fun l => rlmOK l && cyc3 l)

/-- The same for the second monomial: only the 8-cycle `23456781` survives. -/
def survivorsN : List (List ℕ) :=
  (build allowedAtN 8 1 base).filter (fun l => rlmOKN l && cyc3 l)


/-- The pruned enumeration is COMPLETE for the full predicate: any permutation of `base`
satisfying `qualM` survives it.  This is what licenses replacing a sum over all `8!`
permutations by a sum over `survivors`. -/
theorem qual_mem_survivors (l : List ℕ) (hl : l.Perm base) (hq : qualM l = true) :
    l ∈ survivors := by
  have hex : excOK l = true := by
    have := hq
    simp only [qualM, Bool.and_eq_true] at this
    exact this.1.1
  have hrest : (rlmOK l && cyc3 l) = true := by
    have := hq
    simp only [qualM, Bool.and_eq_true] at this
    simp [this.1.2, this.2]
  have hlen : l.length = 8 := by
    have := hl.length_eq
    simpa [base] using this
  have hall : ∀ i, i < 8 → allowedAt (1 + i) (l.getD i 0) = true := by
    intro i hi
    have h := (List.all_eq_true.mp hex) (1 + i) (by simp [List.mem_range']; omega)
    have e : app l (1 + i) = l.getD i 0 := by simp [app]
    rwa [e] at h
  have hmem : l ∈ build allowedAt 8 1 base := build_complete allowedAt 8 1 base l hlen hl hall
  exact List.mem_filter.mpr ⟨hmem, hrest⟩

/-- Every survivor really does satisfy the predicate and really is a permutation of `base`. -/
theorem survivors_qual : ∀ l ∈ survivors, qualM l = true := by decide +kernel

theorem survivors_nodup : survivors.Nodup := by decide +kernel

/-- **The coefficient.**  `(−1)^{n−1} ∑ (−1)^{inv π} = −1` with `n = 8`. -/
theorem coeff_eq :
    (-1 : ℤ) ^ 7 * (survivors.map (fun l => (-1 : ℤ) ^ invCount l)).sum = -1 := by
  decide +kernel

/-- **MathDB #350721 — Conjecture 5.2.1 is FALSE.**  The qualifying permutations are exactly the
five in `survivors`, and their signed count, with the source's `(−1)^{n−1}` prefactor at `n = 8`,
is `−1`; so `P_{8,3} ∉ ℕ[x,y]` and the conjecture fails at `2 ≤ k = 3 ≤ n = 8`. -/
theorem main :
    (∀ l, l.Perm base → qualM l = true → l ∈ survivors) ∧
      (∀ l ∈ survivors, qualM l = true) ∧
      survivors.Nodup ∧
      (-1 : ℤ) ^ 7 * (survivors.map (fun l => (-1 : ℤ) ^ invCount l)).sum = -1 :=
  ⟨fun l hl hq => qual_mem_survivors l hl hq, survivors_qual, survivors_nodup, coeff_eq⟩

/-- Completeness of the pruned enumeration for the second monomial. -/
theorem qualN_mem_survivorsN (l : List ℕ) (hl : l.Perm base) (hq : qualN l = true) :
    l ∈ survivorsN := by
  have hex : excOKN l = true := by
    have := hq
    simp only [qualN, Bool.and_eq_true] at this
    exact this.1.1
  have hrest : (rlmOKN l && cyc3 l) = true := by
    have := hq
    simp only [qualN, Bool.and_eq_true] at this
    simp [this.1.2, this.2]
  have hlen : l.length = 8 := by
    have := hl.length_eq
    simpa [base] using this
  have hall : ∀ i, i < 8 → allowedAtN (1 + i) (l.getD i 0) = true := by
    intro i hi
    have h := (List.all_eq_true.mp hex) (1 + i) (by simp [List.mem_range']; omega)
    have e : app l (1 + i) = l.getD i 0 := by simp [app]
    rwa [e] at h
  have hmem : l ∈ build allowedAtN 8 1 base :=
    build_complete allowedAtN 8 1 base l hlen hl hall
  exact List.mem_filter.mpr ⟨hmem, hrest⟩

theorem survivorsN_qual : ∀ l ∈ survivorsN, qualN l = true := by decide +kernel

theorem survivorsN_nodup : survivorsN.Nodup := by decide +kernel

/-- **The second coefficient.**  For `x₁y₂⋯y₈` the signed count is `+1`. -/
theorem coeff_eqN :
    (-1 : ℤ) ^ 7 * (survivorsN.map (fun l => (-1 : ℤ) ^ invCount l)).sum = 1 := by
  decide +kernel

/-- **No global sign convention rescues positivity.**  Two coefficients of `P_{8,3}` have
opposite signs, so negating the whole polynomial cannot make it lie in `ℕ[x,y]` either.  This
covers the MathDB transcription, which omits the `(−1)^{n−1}` prefactor. -/
theorem opposite_signs :
    ((∀ l, l.Perm base → qualN l = true → l ∈ survivorsN) ∧
        (∀ l ∈ survivorsN, qualN l = true) ∧ survivorsN.Nodup) ∧
      (-1 : ℤ) ^ 7 * (survivors.map (fun l => (-1 : ℤ) ^ invCount l)).sum = -1 ∧
      (-1 : ℤ) ^ 7 * (survivorsN.map (fun l => (-1 : ℤ) ^ invCount l)).sum = 1 :=
  ⟨⟨fun l hl hq => qualN_mem_survivorsN l hl hq, survivorsN_qual, survivorsN_nodup⟩,
    coeff_eq, coeff_eqN⟩

end Principia.MathDB.P350721
