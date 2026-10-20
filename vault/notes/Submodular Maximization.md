---
type: concept
created: 2026-10-19
updated: 2026-10-19
tags: [optimization/submodular]
aliases: [submodular function, submodularity, multilinear extension, matroid constraint, partition matroid, laminar matroid, continuous greedy, dependent rounding]
sources: ["[[Rios 2026 - The Dating Heuristic]]"]
origin: claude
status: seed
---
# Submodular Maximization

Maximizing a set function with *diminishing returns*, meaning an element adds less to a larger set than to a smaller one. The constraints are typically a cardinality limit or a matroid. Greedy-type algorithms give constant-factor guarantees.

## Details
- **Definitions,** as stated in Appendices C and E of [[Rios 2026 - The Dating Heuristic]]:
  - $g$ is *monotone* if $g(x+1_e)\ge g(x)$.
  - $g$ is *submodular* if $g(x+1_e+1_{e'})-g(x+1_{e'})\le g(x+1_e)-g(x)$.
  - The *multilinear extension* is $G(x)=\sum_S g(S)\prod_{e\in S}x_e\prod_{e\notin S}(1-x_e)$: the expected value of $g$ when each element is included independently with probability $x_e$.
  - A *laminar matroid* caps $|A\cap X|\le c(X)$ for every set $X$ in a laminar family, one where any two sets are either disjoint or nested.
- **Standard results** used in [[Rios 2026 - The Dating Heuristic]]:
  - **Weighted rank.** The maximum of a linear function over a matroid, viewed as a function of the ground set, is monotone submodular (Fisher, Nemhauser & Wolsey 1978).
  - **Greedy.** Gets $1/(1+r)$ over an intersection of $r$ matroids (Fisher, Nemhauser & Wolsey 1978).
  - **Local search.** Gets $1/(r+\epsilon)$ over an intersection of $r$ matroids (Lee, Sviridenko & Vondrák 2009).
  - **Single matroid.** Continuous greedy on the multilinear extension gets $1-1/e$ (Vondrák 2008).
  - **Rounding.** Dependent randomized rounding (Gandhi, Khuller, Parthasarathy & Srinivasan 2006) turns the fractional solution into an integral one while keeping the marginals and degree limits.

## In dating-platform assortment
From [[Rios 2026 - The Dating Heuristic]]:
- **When submodularity holds.**
  - If next period has no same-period ("non-sequential") matches, the expected number of next-period matches $\mathsf M^2(\mathbf x^1)$ is monotone submodular in this period's displays.
  - If next period allows them, it is *not* submodular (Prop 3.4).
- **Platform designs become matroid intersections:**

  | Design | Constraint structure | Guarantee |
  | --- | --- | --- |
  | One-directional, sequential | one partition matroid | $1-1/e$ |
  | Two-directional, sequential | two matroids | $1/(2+\epsilon)$ |
  | One-directional, non-sequential | partition ∩ laminar | $1/(2+\epsilon)$ |
  | Two-directional, non-sequential | three partition matroids | $1/(3+\epsilon)$ |

## Related
- [[Correlation Gap]]
- [[Dating Heuristic]]
- [[Two-Sided Assortment Optimization]]
