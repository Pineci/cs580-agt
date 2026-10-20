---
type: concept
created: 2026-10-19
updated: 2026-10-19
tags: [matching/stable, algorithms]
aliases: [Gale-Shapley algorithm, Gale–Shapley algorithm, DA, deferred acceptance algorithm, Rand-MoWo, 1-MoWo]
sources: ["[[Filos-Ratsikas 2026 - The Distortion of Stable Matching]]"]
origin: claude
status: seed
---
# Deferred Acceptance

The Gale–Shapley (1962) proposal algorithm. One side proposes in order of preference. The other side holds on to the best offer it has received so far and rejects the rest. The algorithm ends with a [[Stable Matching]] that is the best possible stable matching for the proposing side and the worst for the receiving side.

## Details
- **Procedure (men proposing).**
  - While some man is unmatched and still has women he hasn't proposed to, he proposes to his favorite among them.
  - The woman he proposes to keeps whichever of him and her current partner she ranks higher, and rejects the other.
  - The output is the man-optimal matching $\mu^*_M$. With women proposing, the output is $\mu^*_W$.
- **Ordinal.** It uses only the agents' rankings, never the strength of their preferences.
- **Running time.** The cyclic shift profile is a worst case (Knuth 1997, as noted in [[Filos-Ratsikas 2026 - The Distortion of Stable Matching]]).
- **Incentives** *(background from outside the ingested sources):* DA is strategy-proof for the proposing side but not for the receiving side (Dubins & Freedman 1981; Roth 1982).

## Welfare guarantees
From [[Filos-Ratsikas 2026 - The Distortion of Stable Matching]]:
- **Unbounded worst case.** DA, with either side proposing, has unbounded [[Distortion]] relative to the best stable matching. So does every deterministic algorithm that uses only rankings.
  - The counterexample is a 4×4 instance with exactly two stable matchings.
  - Utilities can be chosen so that whichever matching the algorithm picks has welfare 0 and the other has welfare 1.
- **Rand-MoWo.** Run both versions and output each with probability 1/2. Distortion is at most 2, and no randomized ordinal algorithm does better.
- **1-MoWo.** Run both versions. Ask each man his value for his $\mu^*_M$ partner, and each woman her value for her $\mu^*_W$ partner, which is one query per agent. Output the matching with the higher revealed welfare.
  - This is deterministic, with distortion at most 2.
  - Doing better than 2 takes $\Omega(\log n)$ queries per agent; see [[Query-Enhanced Algorithms]].
- **Average case.** When all values are i.i.d., $\mu^*_M$ and $\mu^*_W$ have the same expected welfare, so DA's average-case distortion is at most 2.
  - In simulations on standard synthetic preference models it is about 1.00–1.05.
  - On adversarial "spiked" values it is at most about 1.5, except in very small markets.
  - Rand-MoWo did no better than plain DA in these experiments.

## Related
- [[Stable Matching]]
- [[Distortion]]
- [[Query-Enhanced Algorithms]]
- [[Rotation Poset]]: the two DA outputs are the poset's extremes, with no rotations eliminated ($\mu^*_M$) or all of them eliminated ($\mu^*_W$).
