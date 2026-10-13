# Erdős 1054 repository migration

On 13 October 2026, the existing public Erdős 1054 project was copied into `PrincipiaMathOrg/math-solutions`, with permission to retain its manuscript, source files, author credits, and rights notices. The source repository and Principia's project records, uploaded drafts, and historical reports were not changed by this copy.

## Source snapshot

- Original repository: [antoshashakov/Principia-Math-Solutions](https://github.com/antoshashakov/Principia-Math-Solutions).
- Original main commit: `30d7e5327cdf5cda55137d70abec8f4d3b7ff2b3`.
- Original project: [erdos1054 at the copied commit](https://github.com/antoshashakov/Principia-Math-Solutions/tree/30d7e5327cdf5cda55137d70abec8f4d3b7ff2b3/erdos1054).
- Filtered history head, before adding this repository's documentation: `cc5edb8c2f86a3667520644f9828e794487c3267`.

The full `erdos1054/` directory was retained: the EP1054 development and manuscript, the earlier work, Hyunsik Chae's original development, all supporting sources, and their provenance and rights notices. The current EP1054 snapshot includes 502 supporting Lean modules; it is not the earlier 461-module snapshot.

## Imported paths and integrity

The initial import contains 638 original tracked files totaling 22,974,633 bytes:

- `erdos1054/` — 632 files, with the existing directory structure unchanged.
- Root `LICENSE` and `.gitignore`.
- `.github/workflows/erdos1054-comparator.yml`.
- `.github/workflows/erdos1054-ep1054-build.yml`.
- `.github/workflows/erdos1054-ep1054-comparator.yml`.
- `.github/workflows/erdos1054-hyunsik-build.yml`.

The Git tree hashes below are identical in the source snapshot and the filtered destination. A Git tree records file names, modes, and content object hashes recursively, so these checks cover the entire mathematical directory, including paper assets, locks, and licenses:

| Directory | Unchanged Git tree hash |
| --- | --- |
| `erdos1054/` | `fe6435c05ce6addf8d090e562a4c3fed217ba5fb` |
| `erdos1054/ep1054/` | `8ac05759ebe2f902e45108e70710f8647efd8290` |

The new root README and this migration record are repository documentation, not changes to the imported proofs. No compiled Lean objects or dependency caches were imported.

## Preserved history

The source main history was filtered in an isolated fresh clone using `git-filter-repo` 2.47.0, retaining only the imported paths. The 21 relevant commits retain their author and committer metadata and timestamps. Parent histories changed when unrelated projects were removed, so commit IDs changed. References to original commit IDs in historical messages and project documents remain intact.

The [retained commit mapping](migration/erdos1054-20261013-commit-map.txt) links original commits to the corresponding destination commits. Unrelated source commits, branches, tags, issues, settings, and workflow runs were not imported or represented as destination records.

## Verification evidence

The source's [Comparator run 37503885024](https://github.com/antoshashakov/Principia-Math-Solutions/actions/runs/37503885024) is historical evidence for the copied source commit and its 33 configured unconditional targets. It is not a destination-repository pass and does not establish an unconditional verification of the four conditional results.

Fresh destination build and Comparator runs are required before Principia's connection is switched. The initial documentation commit uses `[skip ci]` only to avoid launching three long build jobs simultaneously during import; checking workflows themselves are unchanged and remain available for explicit runs.

## Rights and provenance

All original license files, `SOURCE.txt`, `SHA256SUMS`, credits, and manuscript-rights declarations remain unchanged. The manuscript retains the rights of its named authors, as recorded in `erdos1054/ep1054/formalization.yaml`; the source-code license does not relicense the manuscript. Historical source repository and dependency references retain their original meaning.
