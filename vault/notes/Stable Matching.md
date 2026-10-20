---
type: concept
created: 2026-10-19
updated: 2026-10-19
tags: [matching/stable]
aliases: [stable marriage, stable marriage problem, blocking pair, stable pair, stable partner, man-optimal stable matching, woman-optimal stable matching, optimal stable matching]
sources: ["[[Filos-Ratsikas 2026 - The Distortion of Stable Matching]]", "[[Rios 2026 - The Dating Heuristic]]"]
origin: claude
status: seed
---
# Stable Matching

A *blocking pair* is a man and a woman who would both rather be with each other than with their assigned partners. A one-to-one matching between the two sides is *stable* if it has no blocking pair.

## Details
- **Model.** Two disjoint sides $M$ and $W$. Each agent has a strict ranking over the other side.
- **Depends only on rankings.** Stability depends only on the rankings, never on cardinal utilities. So every valuation profile consistent with the same rankings has the same stable set $\mathcal M_s(\succ)$ ([[Filos-Ratsikas 2026 - The Distortion of Stable Matching]]).
- **Existence.** With strict preferences a stable matching always exists. Gale & Shapley (1962) proved this constructively with [[Deferred Acceptance]].
- **Side-optimal matchings.**
  - The *man-optimal* stable matching $\mu^*_M$ gives every man, simultaneously, his best partner among all stable matchings.
  - $\mu^*_M$ is also the worst stable matching for every woman.
  - The *woman-optimal* matching $\mu^*_W$ is the mirror image.
  - Consequently, $\mu^*_M$ maximizes the men's welfare over stable matchings and $\mu^*_W$ maximizes the women's.
- **Stable pairs and partners.**
  - A pair is a *stable pair* if it appears in at least one stable matching. Each member is then a *stable partner* of the other.
  - All stable pairs can be found in $O(n^2)$ (Gusfield 1987).
  - An agent's best stable partner is its partner in its own side's optimal matching.
- **Structure.** Stable matchings correspond one-to-one with the closed subsets of the [[Rotation Poset]] (Irving & Leather 1986). That poset encodes all of them and how to move between them.
- **Optimal (maximum-welfare) stable matching.** Given full cardinal utilities, the stable matching that maximizes $\sum_a v_a(\mu(a))$ can be computed in polynomial time (Irving, Leather & Gusfield 1987).
- **Randomized stability.**
  - *Ex-post* stable: a lottery over stable matchings.
  - *Ex-ante* or *stable fractional* (Caragiannis et al. 2021): a weaker notion where blocking is judged against expected utilities.

## Welfare and stability
- **Stability can wipe out welfare.** In some instances every stable matching has welfare 0 while some unstable matching has positive welfare. This is Observation 2.1 of [[Filos-Ratsikas 2026 - The Distortion of Stable Matching]], built on Gale–Shapley's Example 2. Anshelevich, Das & Naamad (2013) study this ratio as a price of anarchy/stability.
  - This is why welfare guarantees for stable-matching algorithms are measured against the best *stable* matching; see [[Distortion]].
- **Randomizing between the two extremes guarantees half.** For every stable $\mu$, $\mathrm{SW}_M(\mu^*_M)+\mathrm{SW}_W(\mu^*_W)\ge\mathrm{SW}(\mu)$. So picking $\mu^*_M$ or $\mu^*_W$ at random, which needs only the rankings, guarantees half the optimal stable welfare in expectation. Knowing which of the two is better guarantees half deterministically ([[Filos-Ratsikas 2026 - The Distortion of Stable Matching]]).

## Examples
- **Gale–Shapley Example 2 (4×4).** It has a unique stable matching, and in it no agent gets their top choice.
- **Cyclic shift profile.**
  - Man $m_i$ ranks $w_i, w_{i+1}, \dots$ (indices wrap around). Woman $w_i$ ranks $m_{i+1}, m_{i+2}, \dots, m_i$.
  - There are exactly $n$ stable matchings, the "cyclic diagonals", and every pair is a stable pair.
  - Knuth identified it as the worst case for the running time of Deferred Acceptance.
  - [[Filos-Ratsikas 2026 - The Distortion of Stable Matching]] uses it for its query lower bounds.

## Related
- [[Deferred Acceptance]]
- [[Rotation Poset]]
- [[Distortion]]
- [[Two-Sided Assortment Optimization]]: the dating-app alternative to a central clearinghouse. A platform repeatedly shows profiles, and a match is any mutual like, so users can match many times and there is no stability requirement ([[Rios 2026 - The Dating Heuristic]]).
