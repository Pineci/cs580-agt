---
type: concept
created: 2026-10-19
updated: 2026-10-19
tags: [matching/stable]
aliases: [rotation, rotations, rotation digraph, rotation elimination, Hasse diagram of the rotation poset]
sources: ["[[Filos-Ratsikas 2026 - The Distortion of Stable Matching]]"]
origin: claude
status: seed
---
# Rotation Poset

A rotation is a cyclic swap of partners among some men and women in a stable matching. The rotation poset is a partial order on an instance's rotations. Its closed (downward-closed) subsets correspond one-to-one with the instance's stable matchings (Irving & Leather 1986). It therefore encodes every stable matching compactly, together with how to move between them.

## Details
Definitions follow Appendix A of [[Filos-Ratsikas 2026 - The Distortion of Stable Matching]].
- **Rotation exposed in a stable matching $\mu$.** An ordered list $\rho=((m_0,w_0),\dots,(m_{k-1},w_{k-1}))$ of pairs in $\mu$, with $k\ge2$, such that:
  - for each $i$, $w_{i+1}$ is the highest-ranked woman below $w_i$ on $m_i$'s list who prefers $m_i$ to her current partner $m_{i+1}$;
  - indices are taken mod $k$.
- **Eliminating $\rho$.** Each $m_i$ moves to $w_{i+1}$.
  - The result is again stable.
  - Every man in $\rho$ ends up worse off, and every woman in $\rho$ better off.
- **From $\mu^*_M$ to everything.** Every stable matching is reached from the man-optimal $\mu^*_M$ by eliminating a unique set of rotations.
  - $\mu^*_M$ corresponds to the empty set.
  - The woman-optimal $\mu^*_W$ corresponds to the set of all rotations.
- **At most $n^2$ rotations.** A pair can appear in at most one rotation.
- **Precedence.** $\rho\prec\rho'$ if $\rho$ has already been eliminated in every stable matching where $\rho'$ is exposed.
- **Computation.**
  - A DAG whose transitive closure is this order (the *rotation digraph*) can be computed in $O(n^2)$ (Gusfield 1987).
  - The Hasse diagram is its transitive reduction.
  - Irving, Leather & Gusfield (1987) use this structure to find a maximum-welfare stable matching in polynomial time.
- **Shape follows preference structure.**
  - A path corresponds to 1-attribute preference models (Chebolu et al. 2012).
  - A star corresponds to 2-attribute models (Bhatnagar et al. 2008).
  - $k$-range models give Hasse diagrams of pathwidth $O(k^2)$ (Cheng & Rosenbaum 2023).

## Use in distortion bounds
From [[Filos-Ratsikas 2026 - The Distortion of Stable Matching]]:
- **Lower-bound instances.**
  - A 4×4 instance with a single rotation, and therefore exactly two stable matchings.
  - The cyclic shift profile, whose poset is a chain of $n-1$ rotations. Each rotation consists of all $n$ pairs of the current matching. This gives exactly $n$ stable matchings.
- **Upper bound for path-shaped posets.**
  - When the Hasse diagram is a path, men's welfare never increases and women's never decreases along the chain.
  - Binary search over the matchings therefore gets $1+\varepsilon$ distortion with $O(\log n/\varepsilon)$ queries per agent.
  - The authors expect a branch-by-branch search on general posets to prove their $O(\log n/\varepsilon)$ conjecture.

## Related
- [[Stable Matching]]
- [[Deferred Acceptance]]
- [[Query-Enhanced Algorithms]]
