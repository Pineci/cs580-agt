---
type: map
created: 2026-01-01
updated: 2026-10-20
origin: claude
---
# Log

Append-only record of changes made to the vault. Newest at the bottom.
Format: `## [YYYY-MM-DD] operation | subject`, then bullets of notes created (+), updated (~), archived (−).

## [2026-10-19] ingest | Filos-Ratsikas 2026 - The Distortion of Stable Matching
- + [[Filos-Ratsikas 2026 - The Distortion of Stable Matching]] (raw: `sources/_raw/filosratsikas2026distortion.pdf`, from arXiv:2602.14961v1)
- + [[Stable Matching]]
- + [[Deferred Acceptance]]
- + [[Distortion]]
- + [[Query-Enhanced Algorithms]]
- + [[Rotation Poset]]

## [2026-10-19] ingest | Rios 2026 - The Dating Heuristic
- + [[Rios 2026 - The Dating Heuristic]] (raw: `sources/_raw/rios2026dating.pdf`, from arXiv:2308.02584v5)
- + [[Two-Sided Assortment Optimization]]
- + [[Dating Heuristic]]
- + [[Correlation Gap]]
- + [[Submodular Maximization]]
- + [[History-Dependent Like Probabilities]]
- ~ [[Stable Matching]] (added contrast link to Two-Sided Assortment Optimization)
- ~ [[Query-Enhanced Algorithms]] (added link: displays and likes as elicitation)
- ~ [[Filos-Ratsikas 2026 - The Distortion of Stable Matching]] (added cross-reference to Rios 2026)

## [2026-10-19] query | Match Quality in the Dating Heuristic Framework
- + [[Match Quality in the Dating Heuristic Framework]] (research-direction framework and preliminary results)
- ~ [[Dating Heuristic]] (linked the synthesis)
- ~ [[Correlation Gap]] (linked the synthesis; noted the uniform-matroid constant)
- ~ [[Rios 2026 - The Dating Heuristic]] (recorded the project direction)

## [2026-10-20] update | Match Quality in the Dating Heuristic Framework
- ~ [[Match Quality in the Dating Heuristic Framework]] (linked the new Lean formalization in `lean/`)

## [2026-10-20] update | Lean formalization of Rios 2026 and the match-quality results
- ~ [[Rios 2026 - The Dating Heuristic]] (warning: Theorems 5.3 and 5.4 appear false as stated; counterexamples, the 5.4 one machine-checked)
- ~ [[Match Quality in the Dating Heuristic Framework]] (updated the Lean status: R2–R4 proved, R1 conditional on one open lemma)
- + [[Counterexamples to the Multi-Period Dating Heuristic Guarantees]] (counterexamples to Theorems 5.3 and 5.4 moved out of the source note)
- ~ [[Dating Heuristic]] (flagged DHT's T-period guarantee as disputed)

## [2026-10-20] update | R1 key lemma proved in Lean
- ~ [[Match Quality in the Dating Heuristic Framework]] (R1 now fully machine-checked; sketched the finite Poisson-comparison proof)
