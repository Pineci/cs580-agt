---
type: concept
created: 2026-10-19
updated: 2026-10-19
tags: [optimization/submodular, probability]
aliases: [correlation robust stochastic optimization, distribution problem]
sources: ["[[Rios 2026 - The Dating Heuristic]]"]
origin: claude
status: seed
---
# Correlation Gap

Take a monotone submodular set function $f$ and fixed marginal probabilities for each element. The expected value of $f$ when elements are included *independently* is at least $1-1/e$ times the largest expected value achievable by *any* distribution with those marginals, including correlated ones (Agrawal, Ding, Saberi & Ye 2010).

## Details
- **Statement.** Fix marginals $p\in[0,1]^U$. Let $\lambda^{\text{ind}}$ include each element $e$ independently with probability $p_e$. Then
  $$\mathbb E_{\lambda^{\text{ind}}}[f(S)]\;\ge\;(1-1/e)\,\max\{\mathbb E_\lambda[f(S)]:\ \lambda\text{ has marginals }p\}.$$
- **In terms of extensions** *(background)*:
  - The left side is the multilinear extension $F(p)$.
  - The right side is the concave closure $f^+(p)$.
  - So the statement is $F(p)\ge(1-1/e)f^+(p)$. See [[Submodular Maximization]].
- **Why it's useful.** In stochastic optimization the real randomness is often independent, for example separate users deciding separately. An LP relaxation, though, implicitly allows arbitrary correlation. The correlation gap bounds how much is lost.

## How [[Rios 2026 - The Dating Heuristic]] uses it
- **Setup.**
  - Each user's next-period backlog $B$ is a random set: the people who liked them.
  - Senders decide independently, with marginals $\phi_{\ell'\ell}x_{\ell'\ell}$.
  - The per-user value $f_\ell(B)$ is the maximum expected matches from showing at most $K_\ell$ backlog profiles. It is monotone submodular.
- **The distribution problem $G$** maximizes $\mathbb E f_\ell$ over *all* backlog distributions with those marginals.
  - LP duality shows $G$ upper-bounds the fractional second-period part $F$ of the DH-int relaxation.
  - The actual, independent backlog distribution achieves at least $(1-1/e)G$.
- **Result.** Chaining these gives the $(1-1/e)$ guarantees for DH-int (two periods) and DHT ($T$ periods); see [[Dating Heuristic]].

## Related
- [[Submodular Maximization]]
- [[Dating Heuristic]]
- [[Match Quality in the Dating Heuristic Framework]]: for weighted top-$K$ functions (the rank functions of $K$-uniform matroids), the gap improves from $1-1/e$ to $1-e^{-K}K^K/K!$. The project uses this to sharpen DH-int's guarantee. *(Yan 2011; not from an ingested source, citation to verify.)*
