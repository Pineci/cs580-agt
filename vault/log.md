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

## [2026-10-30] query | Max-Min Match Quality and Egalitarian Matching (correction, Lean)
- ~ [[Max-Min Match Quality and Egalitarian Matching]] (new Correction section and a pointer callout; Eeshan's text unchanged: the per-user $c_K^2$ claim fails for SDH's max-weight selection, with a machine-checked counterexample at $\theta^*/3$; Theorem MM machine-checked in `lean/`: $\mathrm{OPT}_{\min} \le \theta^*$, balanced two-stage selection gives $\gamma_1\gamma_2$ per user, random order $1/4$, $c_K$-balanced rules (via Sion) give the note's $c_K^2$; price of fairness 1.61, not 4.32, after a tie-break)
- ~ index (the note was not indexed)

## [2026-10-30] query | Truthful Swiping with an LLM Oracle (query budgets on the speed-dating data)
- ~ [[Truthful Swiping with an LLM Oracle]] (T3 gets a test of query budgets with `data/scripts/query_budget_check.py`: the unbudgeted plan queries 96–100% of pairs; a query-aware plan, with $\tau_e$ as an LP variable, keeps 77–79% of SDH's welfare on a quarter of the calls and restores MM-SDH's worst-off user on about a third, well ahead of Theorem 3(d)'s scaling; Evidence, Gaps and the Preliminary callout updated)

## [2026-10-30] query | Query Budgets in Screened DH
- + [[Query Budgets in Screened DH]] (Theorem Q: query-aware plan with per-user call budgets; truthfulness, calls, per-user 1/4 and c_K², SDH's welfare c_K², benchmark against every budgeted policy including adaptive ones, monotone homogeneous objectives including max-min; for priors with finite means; machine-checked in `lean/DatingAlgo/BudgetedSDH.lean` and `ContinuousSDH.lean`, 973 theorems all proved)
- ~ [[Truthful Swiping with an LLM Oracle]] (Theorem 3(b) for continuous priors and the query-aware plan now proved; Preliminary, T3 and Gaps updated)
- ~ index

## [2026-10-30] query | Q-SDH Proof Guide
- + `attachments/Q-SDH Proof Guide.html` (a long explainer of Theorem Q for readers: symbols, a worked one-pair example, each result with its Lean names, how the proofs work, a proof map, the 14 assumptions and what each one costs)
- ~ [[Query Budgets in Screened DH]] (a callout linking the guide)
## [2026-10-27] query | Max-Min Match Quality and Egalitarian Matching
- + [[Max-Min Match Quality and Egalitarian Matching]] (Rawlsian egalitarian objective, LP formulation, price of fairness, truthful swiping, Leximin refinement)

## [2026-11-05] query | Position-Aware Reciprocal Re-Ranking and Dual Pacing
- + [[Position-Aware Reciprocal Re-Ranking and Dual Pacing]] (Regret and error bounds vs global fluid optimum, comparative analysis against Hinge pLMC, DH-int, and Gale-Shapley, four theoretical improvements: AdaGrad dual pacing, Doubly Robust IPS debiasing, dynamic OCRS, safe budget pacing)

## [2026-11-06] query | Next-Generation Continuous Reciprocal Re-Ranking
- + [[Next-Generation Continuous Reciprocal Re-Ranking]] (Bounded O(1) regret via periodic fluid LP re-solving, stochastic competitive ratios beyond 1-1/e via Top-k Poisson scaling and Dynamic OCRS, computational complexity reduction from O(M log M) to O(M + K log K) via QuickSelect, smooth continuous softmax re-ranking with Nesterov accelerated dual prox O(1/t^2), closed-loop stability via industrial PID feedback dual pacing)

## [2026-11-06] query | Gender-Skewed Reciprocal Matching and Asymmetric Pacing
- + [[Gender-Skewed Reciprocal Matching and Asymmetric Pacing]] (Empirical data for 3:1 male-to-female ratio, mathematical behavior of female shadow price surge lambda_w* and slack male shadow prices lambda_m*=0, theoretical modifications: asymmetric like budgets B_m << B_w, inverted proposal flow, and asymmetric Dynamic OCRS; simulation results on 75M x 25W market)

## [2026-11-06] query | Truthful Top-k Swiping in Like-Aware Feeds
- + [[Truthful Top-k Swiping in Like-Aware Feeds]] (incentives for top-k users when the ranking uses likes: why the re-ranker's DSIC claim fails, Claims A–C, the feedback rule, a one-directional design; informal proofs; records a conflict with the re-ranking and gender-skew notes)
- + `attachments/Top-k Swiping Incentives Guide.html` (explains every result in short and in detail)

## [2026-11-09] query | The Live-Set Theorem for Truthful Swiping
- + [[The Live-Set Theorem for Truthful Swiping]] (Theorem A: sincere swiping is dominant iff matches are the acceptable profiles in a live set fixed without the user's swipes; Theorem A' for platform coins; valuation classes; Theorem B and the two-cost model; Proposition P: others' likes give sqrt(p) on the random market; brute force in `data/scripts/live_set_check.py`)
- ~ [[Truthful Top-k Swiping in Like-Aware Feeds]] (Claim A points to the new note)
- + `inbox/lu2026conversations.pdf` (Lu, Turkel, Chen & Afghahi, SIGIR 2026; copied in, not ingested yet)
- ~ index

## [2026-11-09] query | Welfare of Truthful Feeds in the Two-Cost Model
- + [[Welfare of Truthful Feeds in the Two-Cost Model]] (adopted model: costs c and d, a match counts only if both users keep it; Proposition 1: Theorems A and B for conversations and the fallback counterexample; Theorem C: capped initiators and a responder queue; Proposition T: long feeds on the random market)
- ~ [[The Live-Set Theorem for Truthful Swiping]] (two-cost model marked adopted; new section on other cost functions with Theorem B'; evidence and gaps updated)
- ~ `data/scripts/live_set_check.py` (checks E, F, G)
- ~ index

## [2026-11-09] query | Responder queue: partial scrolling and pair welfare
- ~ [[Welfare of Truthful Feeds in the Two-Cost Model]] (Theorem C': responders who look at the first m admirers, two-cap lemma, factor c_k c_m; Theorem D: thinned queue gets 1/4 of the pair LP, best of two gets 1/(4 + 1/c_k); net-of-drop-cost remark; gaps updated)
- ~ `data/scripts/live_set_check.py` (check H)
- ~ index

## [2026-11-09] lean | Theorems A and B formalized
- ~ [[The Live-Set Theorem for Truthful Swiping]] (records the Lean status: Theorems A and B for top-k and additive users are proved in `lean/DatingAlgo/LiveSet.lean`; gaps list what is not formalized)
