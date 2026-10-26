# Principia Math Solutions

Principia's shared repository for mathematical papers, Lean formalizations, and supporting computations. Ongoing and completed work are kept together, with each project in its own directory.

## Latest Erdős 1054 manuscript

The current paper is the [October 16 collaboration manuscript (PDF)](erdos1054/ep1054/paper/revisions/2026-10-16/EP1054.pdf),
supplied by Christian Kudeba with the formalization link updated to this organization repository.
See its [revision record](erdos1054/ep1054/paper/revisions/2026-10-16/README.md).
The [current editable LaTeX source](erdos1054/ep1054/paper/revisions/2026-10-16/EP1054.tex)
and [bibliography](erdos1054/ep1054/paper/revisions/2026-10-16/EP1054.bib) are derived from the
previous source with only its formalization URL and displayed date updated to match the new PDF.
The [previous October 15 PDF and Overleaf export](erdos1054/ep1054/paper/revisions/2026-10-15/README.md)
remain preserved, including all contributor drafts. No replacement Overleaf export was supplied.
Receipt/publication dates are not claims about when each collaborator last edited the manuscript.

The earlier [September 25 manuscript snapshot](erdos1054/ep1054/paper/) and its checksums remain
unchanged. The passing Comparator evidence checks the existing Lean statements and proofs;
publishing revised prose does not automatically certify its correspondence to those statements.
The verification scope remains **33 unconditional results and four conditional results**.

## Projects

| Project | Files | Verification record |
| --- | --- | --- |
| Erdős 1054 — Sums of initial segments of divisors | [Project directory](erdos1054/) · [EP1054 formalization and manuscript](erdos1054/ep1054/) | [EP1054 verification details](erdos1054/ep1054/VERIFICATION.md) |
| MathDB — Lean formalizations of 143 open problems | [Project directory](mathdb/) · [index of the modules](mathdb/README.md) | [MathDB verification details](mathdb/VERIFICATION.md) |

The MathDB directory holds one Lake project with 178 modules: 143 of them formalize a MathDB
open problem and were gated locally, and the rest are supporting modules they import. Those
gates were run on the authors' machine, not in this repository's CI, and **no Comparator
contract exists for them yet** — there is no `Challenge.lean`/`Solution.lean` pair and no
`comparator.json` under `mathdb/`, so nothing there has been or can yet be checked by the
Comparator. Many of the modules formalize a *refutation* of the problem as stated rather than a
proof of it; the index says which, and each module's header says what it still owes. Treat
`mathdb/VERIFICATION.md` as the scope statement for the whole directory.

The EP1054 Comparator contract covers 33 unconditional results. Four further results remain conditional on explicitly stated inputs; this repository does not present the entire manuscript as unconditionally formalized. The complete supporting Lean library and pinned build metadata are included.

## Checking a project

Each project records its Lean toolchain, dependencies, comparison contract, and verification scope alongside its source files. Keep those files together; a proof file alone is not a complete reproducible environment.

For EP1054, run **erdos1054-ep1054-build** in the [Actions tab](https://github.com/PrincipiaMathOrg/math-solutions/actions) first, then **erdos1054-ep1054-comparator**. The build caches supporting dependencies; the Comparator compiles and checks the named targets itself. Use the run's recorded commit and logs as the verification evidence. Historical runs linked in imported documents belong to the original repository, not this destination.

## Contributing

Open a pull request for changes, keep all of a project's mathematical and supporting files in its project directory, and preserve the existing author and license notices. Changes to proof statements, allowed axioms, dependencies, or checking workflows require explicit review and fresh checks.

## Authorship and rights

Unless a file or accompanying notice states otherwise, the formalization source code is distributed under Apache License 2.0; see [LICENSE](LICENSE). The EP1054 manuscript and its TeX, bibliography, and PDF retain the rights of their named authors and are not relicensed under the source-code license.

Imported third-party work retains its original authorship, license, and attribution notices, including Hyunsik Chae's development and the mathematical sources credited in the project. Principia's stewardship of this repository does not imply sole authorship or a transfer of copyright.

## Repository provenance

Erdős 1054 was copied from its existing public repository without changing its mathematical files. See [the migration record](MIGRATION.md) for the source snapshot, integrity checks, and history mapping.
