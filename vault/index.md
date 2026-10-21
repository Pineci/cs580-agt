---
type: map
created: 2026-01-01
updated: 2026-10-21
origin: claude
---
# Index

Catalog of the vault. Every note in `notes/`, `sources/`, and `maps/` gets one line here: `- [[Title]] — one-line summary`. Grouped by map; notes without a map go under **Unsorted**. Maintained by the vault skills.

## Maps

## Sources
- [[Filos-Ratsikas 2026 - The Distortion of Stable Matching]] — welfare loss of ordinal/query-limited stable matching: DA unbounded, randomized 2, $\Theta(\log n)$ queries for $1+\varepsilon$

- [[Rios 2026 - The Dating Heuristic]] — which profiles a dating app should show whom; DH-int is a $(1-1/e)$-approximation for every design; ~19% more matches than Greedy on real-app data
- [[Coles 2013 - Preference Signaling in Matching Markets]] — one scarce, costless signal per worker: in informative equilibria workers signal their top firm and firms use cutoffs; signals raise matches and worker welfare, effect on firms ambiguous
- [[Lee 2015 - Propose with a Rose]] — field experiment on a dating site: a scarce rose raises acceptance by about 3.3 points (about 20%); 8 roses instead of 2 means 44–86% more dates
- [[Arnosti 2021 - Managing Congestion in Matching Markets]] — mean-field market with application and screening costs: two regimes and a tragedy of the commons; application limits help and costs hurt applicants
- [[Kanoria 2021 - Facilitating the Search for Partners on Matching Platforms]] — strategic search with costly screening: recipients are too selective, and blocking the long side from proposing (plus hiding quality) raises welfare

## Unsorted
- [[Stable Matching]] — no blocking pair; side-optimal matchings, stable pairs, welfare cost of stability
- [[Deferred Acceptance]] — Gale–Shapley proposal algorithm; proposer-optimal; unbounded welfare distortion, Rand-MoWo/1-MoWo fixes
- [[Distortion]] — worst-case welfare ratio from limited (ordinal) information; summary table for stable matching
- [[Query-Enhanced Algorithms]] — ordinal input plus a few cardinal value queries; threshold-step-function technique and query lower bounds
- [[Rotation Poset]] — poset of rotations whose closed subsets are the stable matchings; path-shaped posets enable faster search
- [[Two-Sided Assortment Optimization]] — choosing what each side sees when a match needs mutual interest; backlogs, one/two-directional and (non-)sequential designs
- [[Dating Heuristic]] — DH / DH-int / DHT one-lookahead programs for dating-app displays; $(1-1/e)$ guarantees and simulation results
- [[Correlation Gap]] — independent vs. correlated distributions with the same marginals lose at most $1-1/e$ for monotone submodular functions
- [[Submodular Maximization]] — diminishing returns; greedy/local-search/continuous-greedy guarantees under matroid constraints
- [[History-Dependent Like Probabilities]] — like probability as a function of a user's matches, backlog, and time on the app; five simulated forms
- [[Match Quality in the Dating Heuristic Framework]] — project synthesis: quality objectives (additive, top-k), sharper $c_K$ for DH-int, weighted DH-int keeps it, top-1 needs a new algorithm (preliminary)
- [[Match Quality with Queried Values]] — unknown quality, queried through each user's agent: distortion-style warm-up ($c_K/\lambda$); Bayesian model where value-indexed DH-int keeps $c_K$ with backlog screening and with the best pre-period query strategy, and screening-aware DH-int gets $c_K/2$ under screening budgets (preliminary)
- [[Top-k Match Quality]] — top-k/top-1 quality: credit-DH gets $\rho c_k \ge c_k/2$ with known qualities (weighted DH-int only $\Theta(k/K)$); carries over to free rankings, Bayesian priors, queries before period 1, and budgeted screening ($c_k/6$) (preliminary)
- [[Preference Signaling]] — scarce, free signals of special interest (roses): credible because rationed; theory and dating-site evidence
- [[Congestion in Matching Markets]] — wasted applications and screening; limits, costs, restricting who initiates, signals and curation as levers
- [[Counterexamples to the Multi-Period Dating Heuristic Guarantees]] — Theorem 5.3 of Rios & Torrico is false and Theorem 5.4's proof is wrong: the T-period relaxations ignore timing (ratios 0.52 and 0.50, both machine-checked); for T ≥ 3 DHT's schedule loses up to 1/(T-1); a per-period relaxation repairs 5.3 (machine-checked)
