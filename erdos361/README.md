# Erdős Problem 361 — irregularity of forbidden-subset-sum extremal sets

> For fixed `c > 0` let `f_c(n) = max { |A| : A ⊆ {1, …, ⌊cn⌋}, n ∉ Σ(A) }`, where `Σ(A)`
> is the set of nonempty subset sums. **Does `f_c(n)/n` converge?**
> **Answer: it converges iff `c ≥ 1`.** For `c ≥ 1`, `f_c(n) = ⌊cn⌋ − ⌈n/2⌉`, so
> `f_c(n)/n → c − 1/2`. For every `c ∈ (0,1)`, `f_c(n)/n` does **not** converge — the
> affirmative answer to the Erdős–Graham irregularity question.

## Results

| Paper result | Statement | Lean name | Module |
| --- | --- | --- | --- |
| Regular range (`c ≥ 1`) | `F M n = M − ⌈n/2⌉` for `1 ≤ n ≤ M` | `Erdos361.Statement.erdos361_cge1` | `Erdos361/Core.lean` |
| **Theorem 4 (irregularity)** | `∀ c ∈ (0,1)`, `f_c(n)/n` has no limit | `Erdos361.Statement.erdos361_irregular` | `Erdos361/Core.lean` |
| **Part 1 (size) — Basile 7.1** | dense `A ⊆ [1,E]` represents every even `t ∈ (2E,3E)`, `3∤t` | `Erdos361.Statement.basile71_unconditional` | `Erdos361/BasileMain.lean` |

### Part 1 — Basile's Problem 7.1 (the *size* question, linear regime `c ∈ (1/3,1/2)`)

`basile71_unconditional`: for every `ε > 0` there is an `E₀` such that for all `E ≥ E₀`, every
`A ⊆ [1,E]` with `|A| ≥ (1/3+ε)E` has `n ∈ Σ(A)` for every even `n ∈ (2E,3E)` with `3 ∤ n` — i.e.
such a dense set *cannot* avoid those `n`. This answers the located inverse question posed on the
forum by **Basile Beyer de Ryke as Problem 7.1** (equivalently **Alon's Conjecture 4.3** in the
linear regime). It is **axiom-free and fully unconditional**: Freiman's `3k-3` theorem — which
earlier revisions carried as the hypothesis `hFreiman` — is now **proved from scratch in-project**
(`Erdos361/BasileFreiman.lean`, `Erdos361Freiman.freiman_3k3`; Nathanson's Kneser-free
large-diameter induction, no Mathlib port exists). Alon's Prop 2.5 good core and the located
covering are likewise *proved* in-development (`good_core_exists`, `hLev_covering`), the latter by an
elementary route that **avoids Lev 1997 entirely**. No cited hypothesis remains.

**Status:** a machine-checked *candidate*, **pending expert referee**. It answers Basile 7.1 / the
`c ∈ (1/3,1/2)` size question; it does **not** claim to resolve the full erdosproblems.com #361 as
stated.

`f_c(n)` is modelled by `Fc c n = F ⌊c·n⌋ n`, where `F M n` is the max cardinality of an
avoider of `n` in `[1,M]` (`Erdos361/Statement.lean`).

## How the statements are kept honest

`Erdos361/Statement.lean` (definitions only, Mathlib-only import) and `Challenge.lean`
(the two statements, `sorry`) are the **entire audit surface**. `Solution.lean` proves the
same two statements by direct term assignment from the development, so Lean checks the
development's statements are definitionally the trusted ones.
[Comparator](https://github.com/leanprover/comparator) verifies this mechanically on CI
(`comparator/`), and checks the axiom footprints.

## Axiom-free

**Both** `erdos361_cge1` and `erdos361_irregular` are **axiom-free** — `[propext, Quot.sound,
Classical.choice]` only. The paper's sole external input, **Alon 1987** *(Subset Sums, J.
Number Theory 27 (1987) 196–205, Theorem 1.1)* — formerly postulated as an axiom — is now
**proved from scratch** in `Erdos361/Core.lean`: the general-`h` **Dias da Silva–Hamidoune**
restricted-sumset bound (built from Mathlib's Combinatorial Nullstellensatz) gives Alon's
theorem over a prime modulus, and the irregularity is assembled on the subsequence `n = 2p`
(`p` prime). See `VERIFICATION.md` §4.

## Verify it yourself

```bash
cd erdos361
lake exe cache get
lake build                 # the development (Erdos361)
lake build Challenge Solution
```

Comparator (Linux-only; runs on CI):
```bash
lake env /path/to/comparator comparator/erdos361_cge1.json        # expect: Your solution is okay!
lake env /path/to/comparator comparator/erdos361_irregular.json   # expect: Your solution is okay!
```

## Layout

```
erdos361/
├── Erdos361/
│   ├── Statement.lean       trusted defs (Avoids/Avoiders/F/Fc) — no axioms
│   ├── Core.lean            c≥1 formula + irregularity: modular dichotomy, DSH, avoider bounds
│   ├── BasileGlue.lean      Part 1: distinctification + Represents ↔ ¬Avoids
│   ├── BasileGreedy.lean    Part 1: Alon Prop 2.5 good core (good_core_exists)
│   ├── BasileCovering.lean  Part 1: the located covering (hLev_covering), avoids Lev 1997
│   ├── BasileFreiman.lean   Part 1: Freiman 3k-3 from scratch (freiman_3k3) — the former hFreiman
│   └── BasileMain.lean      Part 1: assembly → basile71_(fully_)unconditional
├── Erdos361.lean        build root (imports Core + BasileMain)
├── Challenge.lean       the three statements, `sorry`  (audit surface)
├── Solution.lean        the three statements, proved by term assignment + #print axioms
├── comparator/          all.json + one config per result
├── paper/erdos361.pdf   the manuscript (Theorem 4), sha256-pinned in VERIFICATION.md
├── formalization.yaml   mathlib-initiative metadata + alignment
└── VERIFICATION.md      the honest ledger
```
