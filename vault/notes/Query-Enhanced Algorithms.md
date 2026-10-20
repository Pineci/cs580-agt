---
type: concept
created: 2026-10-19
updated: 2026-10-19
tags: [social-choice/distortion, elicitation]
aliases: [value queries, value query, cardinal queries, query-enhanced distortion, threshold step function, Stable-TSF, HassePath]
sources: ["[[Filos-Ratsikas 2026 - The Distortion of Stable Matching]]"]
origin: claude
status: seed
---
# Query-Enhanced Algorithms

These algorithms get every agent's ranking for free and may also ask a limited number of *value queries*: "what is your cardinal value for $b$?" They trade the cost of eliciting values against [[Distortion]]. The model comes from Amanatidis, Birmpas, Filos-Ratsikas & Voudouris (2021).

## Details
- **Cost** is the number of queries per agent, not the total.
- **Adaptive vs. non-adaptive.** Adaptive queries may depend on earlier answers. Non-adaptive queries are fixed in advance from the rankings alone. Every answer must be consistent with the agent's ranking.
- **Standard upper-bound technique: threshold step function.**
  1. Query the agent's top choice to learn $v^*_a$.
  2. For each of $\lambda$ thresholds, binary-search the ranking for the point where value drops below $\delta^\ell v^*_a$. Each threshold costs $\log_2 n$ queries.
  3. Replace each value with its bucket's lower bound.
  4. Optimize the resulting simulated welfare.
- **Motivation in matching markets.** Interviews reveal how strongly people prefer each other, but they are costly, so there should be few of them ([[Filos-Ratsikas 2026 - The Distortion of Stable Matching]]). Earlier interview models elicit only ordinal information: Rastegari et al. (2013, 2016), Drummond & Boutilier (2014), Ashlagi et al. (2025).

## In stable matching
From [[Filos-Ratsikas 2026 - The Distortion of Stable Matching]]:
- **1 query per agent gets distortion 2.** Ask each agent its value for its partner in its own side's optimal matching, then pick whichever of the two side-optimal matchings has higher revealed welfare.
- **Beating 2 needs $\Omega(\log n)$ adaptive or $\Omega(n)$ non-adaptive queries per agent.**
  - The instance is the cyclic shift profile.
  - The adversary answers so that each query at most halves the set of still-unqueried stable partners.
- **$O(\log n/\varepsilon^2)$ queries get $1+\varepsilon$ (Stable-TSF).** Two changes to the standard technique make this work:
  - The binary search runs only over each agent's *stable partners*, so the simulated optimum is a stable matching.
  - The loss from the bottom bucket is charged to $\mathrm{SW}_M(\mu^*_M)+\mathrm{SW}_W(\mu^*_W)$, which is at most $2\,\mathrm{SW}(\text{output})$.
  - Together these improve on the $O(\log^2 n/\varepsilon)$ bound known for non-stable matching.
- **Matching-level queries.** A query can instead return $\mathrm{SW}_M(\mu)$ for a whole matching, counted as one query per agent. HassePath uses these to binary-search a chain-shaped [[Rotation Poset]] with $O(\log n/\varepsilon)$ queries.
- **Open questions.**
  - Does $O(\log n/\varepsilon)$ suffice on every instance (Conjecture 1)?
  - How do the bounds change with noisy, unreliable, or strategic answers?

## Related
- [[Distortion]]
- [[Stable Matching]]
- [[Deferred Acceptance]]
- [[Rotation Poset]]
- [[Two-Sided Assortment Optimization]]: showing someone a profile and observing a like or dislike is another kind of elicitation. Each display answers a noisy binary question rather than returning an exact value. *(This is my reading, not a claim made by either source.)*
