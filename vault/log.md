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

## [2026-10-20] update | Theorem 5.3 counterexample in Lean; timing-aware repairs tested
- ~ [[Counterexamples to the Multi-Period Dating Heuristic Guarantees]] (5.3 counterexample now machine-checked; second flaw in DHT's schedule; decoy family with ratio → 1/(T-1); aggregated repair R1 fails, per-period repair R2 holds with proof sketch)
- ~ [[Rios 2026 - The Dating Heuristic]] (warning updated: both counterexamples machine-checked; repair)
- ~ [[Dating Heuristic]] (DHT flag updated)
- ~ [[Match Quality in the Dating Heuristic Framework]] (link to the counterexamples note)

## [2026-10-20] update | Theorem 5.3 repair (R2, DHT-τ) machine-checked in Lean
- ~ [[Counterexamples to the Multi-Period Dating Heuristic Guarantees]] (R2 repair now machine-checked; the Lean proof route; the two benchmark rules R2 needs; Gaps updated)
- ~ [[Rios 2026 - The Dating Heuristic]] (warning: the repair is machine-checked)
- ~ [[Dating Heuristic]] (DHT flag: the repair is machine-checked)

## [2026-10-20] update | Renamed the Theorem 5.3 repair relaxations
- ~ [[Counterexamples to the Multi-Period Dating Heuristic Guarantees]] (repairs "R1"/"R2" renamed to $\mathrm{Rel}_{\text{agg}}$/$\mathrm{Rel}_\tau$ to avoid clashing with the match-quality R1–R4; Lean names `FeasibleR2` etc. renamed to `FeasibleTau` etc.)

## [2026-10-20] update | Lean sanity check: corrected claims
- ~ [[Counterexamples to the Multi-Period Dating Heuristic Guarantees]] (Theorem 5.4 is existential: only its proof is refuted, the claim is open; rounding step is prose; Lean's DHT predicate assumes no mutual-view interference)
- ~ [[Rios 2026 - The Dating Heuristic]] (warning: Theorem 5.4's proof is wrong, not the theorem)
- ~ [[Match Quality in the Dating Heuristic Framework]] (R1 now for unequal caps, R2 with $c_K$; what is not machine-checked in R1, R3, R4)

## [2026-10-20] query | Match Quality with Queried Values
- + [[Match Quality with Queried Values]] (phase 2 of the match-quality direction: distortion-style warm-up; Bayesian model results B1 and B2; sketch of a tractable query strategy; brute force in `data/scripts/bayes_query_check.py`)
- ~ [[Match Quality in the Dating Heuristic Framework]] (linked the new note from the phase 2 preview)
- ~ [[Query-Enhanced Algorithms]] (linked the warm-up)

## [2026-10-20] update | Budgeted backlog screening (B3)
- ~ [[Match Quality with Queried Values]] (B3: screening-aware DH-int gets $c_K\rho\ge c_K/2$ when responders can screen only part of the backlog; example where a budget-blind program fails; brute force in `data/scripts/screening_budget_check.py`)

## [2026-10-21] query | Top-k Match Quality
- + [[Top-k Match Quality]] (T1: credit-DH gets $\rho c_k$ for top-k with known qualities; T2: Bayesian priors; queries before period 1; T3: budgeted screening; weighted DH-int is $\Theta(k/K)$; brute force in `data/scripts/topk_check.py` and `data/scripts/topk_screening_check.py`)
- ~ [[Match Quality in the Dating Heuristic Framework]] (R5 marked as worked out)
- ~ [[Match Quality with Queried Values]] (top-1 gap points to the new note)

## [2026-10-21] ingest | Coles 2013 - Preference Signaling in Matching Markets
- + [[Coles 2013 - Preference Signaling in Matching Markets]] (url, NBER WP 16185; no raw file)
- + [[Preference Signaling]]
- + [[Congestion in Matching Markets]]

## [2026-10-21] ingest | Lee 2015 - Propose with a Rose
- + [[Lee 2015 - Propose with a Rose]] (url, published version; no raw file)
- ~ [[Preference Signaling]] (field evidence)
- ~ [[Rios 2026 - The Dating Heuristic]] (conflict callout: the cited +0.2 signaling effect is not what Lee & Niederle measure; 2014 is the online-first year)
- ~ [[History-Dependent Like Probabilities]] (what the rose experiment measures; strategic history effects)

## [2026-10-21] ingest | Arnosti 2021 - Managing Congestion in Matching Markets
- + [[Arnosti 2021 - Managing Congestion in Matching Markets]] (url, NSF PAR; no raw file)
- ~ [[Congestion in Matching Markets]] (two regimes, application limits)

## [2026-10-21] ingest | Kanoria 2021 - Facilitating the Search for Partners on Matching Platforms
- + [[Kanoria 2021 - Facilitating the Search for Partners on Matching Platforms]] (url, SSRN version; no raw file)
- ~ [[Congestion in Matching Markets]] (costly screening, effective cost c/p)
- ~ [[Two-Sided Assortment Optimization]] (who should initiate when users are strategic)

## [2026-10-21] query | Strategic Users in the Dating Heuristic Framework
- + [[Strategic Users in the Dating Heuristic Framework]] (strategic likes and agent reports: Theorems 1–2, Lemmas 1–2, Propositions 1–5; brute force in `data/scripts/strategic_check.py`)

## [2026-10-21] query | From DH-int to Credit-DH
- + [[From DH-int to Credit-DH]] (walkthrough: model, notation, the three programs side by side, why credit-DH works for top-k, unknown-value counterparts; no new results)
- ~ [[Dating Heuristic]] (related link)
- ~ [[Top-k Match Quality]] (evidence link)

## [2026-10-22] query | Truthful Swiping with an LLM Oracle
- + [[Truthful Swiping with an LLM Oracle]] (truthful oracle, sincere-threshold swiping, full-information benchmark: Theorems 1–4, Propositions 4–5; brute force in `data/scripts/truthful_swipe_check.py`)
- ~ [[Strategic Users in the Dating Heuristic Framework]] (follow-up link in Gaps)

## [2026-10-26] query | Truthful Swiping with an LLM Oracle (DSIC and glossary)
- ~ [[Truthful Swiping with an LLM Oracle]] ("ex-post dominant" corrected to dominant/DSIC; new T5 (Theorem 5, Proposition 6, ex post vs DSIC, report manipulation); worked example; plain-language readings; glossary; Evidence rerun with exhaustive DSIC checks)
- ~ [[Strategic Users in the Dating Heuristic Framework]] (same terminology fix in Summary, Theorem 1, Theorem 2(i))

## [2026-10-26] query | Truthful Swiping with an LLM Oracle (continuous values)
- ~ [[Truthful Swiping with an LLM Oracle]] (T3: value combination $s$ defined as a vector, $w_s$ → $w_{e,s}$; new "Continuous values" remark: one bar per pair, welfare unchanged, the query trade-off with a uniform example; Gaps: query-aware plan)

## [2026-10-26] query | Truthful Swiping with an LLM Oracle (Lean verification of SDH)
- ~ [[Truthful Swiping with an LLM Oracle]] (Theorem 1, SDH's DSIC and IR, Theorem 3(b)–(d) for size caps machine-checked in `lean/`; Theorem 3(c) corrected: bar-shaped plans split a tied bar proportionally, and $\hat p_e$ is defined precisely; Gaps, Evidence and Glossary updated)

## [2026-10-26] query | Truthful Swiping with an LLM Oracle (Lean verification of the remaining results)
- ~ [[Truthful Swiping with an LLM Oracle]] (every result now machine-checked in `lean/` except Theorem 3(b) for continuous priors; Theorem 2(b) sharpened to $k/b$ via König's edge-coloring theorem; Theorem 4 and Proposition 6(b) need only $np\to\infty$, with a Chebyshev-and-König benchmark; Bayes–Nash example clarified; Preliminary, Evidence, Gaps and Glossary updated)
