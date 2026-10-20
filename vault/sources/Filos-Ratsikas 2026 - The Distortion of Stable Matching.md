---
type: source
source_type: paper
title: "The Distortion of Stable Matching"
authors: [Aris Filos-Ratsikas, Georgios Kalantzis]
year: 2026
venue: "arXiv preprint (cs.GT), arXiv:2602.14961v1"
citekey: "filosratsikas2026distortion"
url: "https://arxiv.org/abs/2602.14961"
raw: "[[filosratsikas2026distortion.pdf]]"
created: 2026-10-19
updated: 2026-10-19
tags: [matching/stable, social-choice/distortion]
aliases: ["The Distortion of Stable Matching"]
origin: claude
status: seed
---
# The Distortion of Stable Matching

> [!summary]
> First study of [[Distortion]] for [[Stable Matching]]. The question is how much social welfare (the sum of both sides' cardinal utilities) an algorithm loses when it sees only the agents' ordinal rankings, or the rankings plus a few [[Query-Enhanced Algorithms|value queries]]. The benchmark is the best *stable* matching, because the best unrestricted matching can be infinitely better even with full information. Every deterministic ordinal algorithm, [[Deferred Acceptance]] included, has unbounded distortion. Running men-proposing or women-proposing DA with probability 1/2 each gets distortion 2, and no randomized ordinal algorithm does better. With queries, one query per agent also gets 2. Beating 2 needs $\Omega(\log n)$ adaptive queries per agent, and $O(\log n/\varepsilon^2)$ queries are enough for $1+\varepsilon$. With values drawn i.i.d., DA's average-case distortion is at most 2 in theory and close to 1 in experiments.

## Setting and model
- Balanced one-to-one market: men $M$, women $W$, $|M|=|W|=n$. Every agent finds everyone on the other side acceptable.
- Agent $a$ has a non-negative valuation $v_a$ over the other side. No normalization is assumed in general. The ordinal ranking $\succ_a$ is induced by $v_a$, with ties broken arbitrarily. Positive results hold for any tie-breaking. Lower bounds use ties only for convenience and can be made strict.
- Social welfare: $\mathrm{SW}(\mu\mid\mathbf v)=\mathrm{SW}_M+\mathrm{SW}_W=\sum_a v_a(\mu(a))$. A randomized matching gives agent $a$ expected utility $\sum_b p_{a,b}\,v_a(b)$.
- Stability depends only on the rankings, so the stable set $\mathcal M_s(\succ)$ is the same for every valuation profile consistent with $\succ$.
- A pair is a *stable pair* if it appears in some stable matching. $S_a$ is $a$'s set of stable partners, and $f^s(a)$ is $a$'s *stable favorite* (its top stable partner). All stable pairs can be computed in $O(n^2)$ (Gusfield 1987).
- Randomized stable means *ex-post* stable: a lottery over stable matchings (via Birkhoff–von Neumann, with support of at most $n^2$ matchings). The welfare-optimal stable matching is therefore deterministic. Given full cardinal information, it can be computed in polynomial time (Irving, Leather & Gusfield 1987; the paper calls this algorithm $\mathcal A_{ilg}$).
- Distortion of algorithm $\mathcal A$:
  $$\mathrm{dist}(\mathcal A)=\sup_{\mathbf v,n}\frac{\max_{\mu\in\mathcal M_s(\succ_{\mathbf v})}\mathrm{SW}(\mu\mid\mathbf v)}{\mathbb E\big[\mathrm{SW}(\mathcal A(\succ_{\mathbf v})\mid\mathbf v)\big]}$$
- **Why the benchmark is the best stable matching (Observation 2.1).** Take Gale–Shapley's Example 2, a 4×4 instance whose unique stable matching gives nobody their top choice. Give every agent value 1 for their favorite and 0 for everyone else. Then every stable matching has welfare 0, while some unstable matching has positive welfare. The ratio studied by Anshelevich, Das & Naamad (2013), which they call the price of anarchy/stability, is therefore unbounded.
- **Query model (Section 4),** following Amanatidis et al. (2021). A value query to agent $a$ about $b$ returns $v_a(b)$. An *adaptive* query may depend on earlier answers. A *non-adaptive* query depends only on $\succ$. Cost is measured as queries per agent.
- **Average-case distortion (Section 5),** following Caragiannis & Fehrs (2024). All values are drawn i.i.d. from $F$, and the measure is a ratio of expectations:
  $$\mathrm{avdist}(\mathcal A)=\sup_{n,F}\frac{\mathbb E[\max_{\mu\in\mathcal M_s}\mathrm{SW}(\mu)]}{\mathbb E[\mathrm{SW}(\mathcal A)]}$$

## Assumptions
- Balanced market, complete lists, strict rankings. Footnote 4 says all results extend to ties with weak stability.
- The ordinal lower bounds use unit-sum valuations (Remark 2), so they hold under the standard normalization. The query lower bounds use unnormalized 0/1 ("dichotomous") valuations.
- Query answers are exact and truthful.
- Incentives (strategic misreporting) are not considered anywhere in the paper.

## Main results
**Ordinal algorithms (Section 3)**
- **Thm 3.1.** Every deterministic ordinal stable algorithm, including DA with either side proposing, has unbounded distortion.
  - The instance (Fig. 2) is a 4×4 profile with exactly two stable matchings, $\mu^*_M$ and $\mu^*_W$. They differ by a single rotation that swaps $m_2$ and $m_4$ (Appendix B).
  - Valuations are then set so that whichever matching the algorithm picks has welfare 0 and the other has welfare 1.
- **Thm 3.2.** *Rand-MoWo* outputs $\mu^*_M$ or $\mu^*_W$ with probability 1/2 each and has distortion at most 2. Every man weakly prefers $\mu^*_M$, and every woman $\mu^*_W$, to any stable matching. So $\tfrac12(\mathrm{SW}(\mu^*_M)+\mathrm{SW}(\mu^*_W))\ge\tfrac12(\mathrm{SW}_M(\mu^*)+\mathrm{SW}_W(\mu^*))$.
- **Thm 3.3.** Every randomized ordinal stable algorithm has distortion at least 2; the ratio is at least $2-\frac{3}{n/2+2}$.
  - The instance is the *reverse cyclic shift* profile: every agent has a distinct favorite, every man ranks his suitor second, and every woman ranks her suitor last.
  - A man is *selective* (value 1 for his favorite, 0 for everyone else) if the algorithm matches him to his favorite with probability at most 1/2. Otherwise he is *indifferent* (value $1/n$ for everyone). His suitor gets the opposite type.
  - The algorithm earns at most $n/2+2$. The stable matching that pairs every selective agent with its favorite earns $n+1$.
- **Remark 3.** The proof of Thm 3.3 never uses the stability of the output. So no ordinal randomized algorithm can beat 2 against the best-stable benchmark, even one that outputs unstable or ex-ante stable (fractional) matchings.

**Query-enhanced algorithms (Section 4)**
- **Thm 4.1.** *1-MoWo* gets distortion at most 2 with 1 query per agent. It runs DA both ways, queries each man about his $\mu^*_M$ partner and each woman about her $\mu^*_W$ partner, and returns whichever matching has the higher revealed welfare.
- **Thm 4.2.** A deterministic stable algorithm with fewer than $n/2$ non-adaptive queries per agent has distortion at least 2.
- **Thm 4.3.** A deterministic stable algorithm with fewer than $(\log_2 n)/2$ adaptive queries per agent has distortion at least 2.
  - Both bounds use the *cyclic shift* profile (Def. 4.2). Its stable matchings are exactly the $n$ "cyclic diagonals" $\mu_k=\{(m_i,w_{(i-1+k)\bmod n+1})\}$ (Lemma 4.1).
  - Its [[Rotation Poset]] is a chain of $n-1$ rotations (Appendix C). Every pair is a stable pair.
  - The valuations are dichotomous, and only $m_1$ and $w_1$ have any non-zero values.
- **Thm 4.4.** *Stable-TSF* achieves distortion at most $1+\varepsilon$ with $\min\{n,\,4\log_2 n/\varepsilon^2\}$ queries per agent, for $\varepsilon\in(0,1]$. Together with Thm 4.3, $\Theta(\log n)$ queries per agent are necessary and sufficient for any constant distortion below 2.
- **Thm D.1 (Informal Thm 4).** If the Hasse diagram of the rotation poset is a path, *HassePath* achieves $1+\varepsilon$ with at most $8\log_2 n/\varepsilon$ queries per agent.
- **Conjecture 1.** $O(\log n/\varepsilon)$ queries per agent are enough for $1+\varepsilon$ on every instance.

**Average case (Section 5)**
- **Thm 5.1.** If all values are i.i.d. from any $F$, DA (either side proposing) has average-case distortion at most 2. Swapping the roles of men and women leaves the value distribution unchanged, so $\mathbb E[\mathrm{SW}(\mu^*_M)]=\mathbb E[\mathrm{SW}(\mu^*_W)]$. The bound then follows as in Thm 3.2.

## Technique
- **Lower bounds** use instances whose stable set is tiny (two matchings) or perfectly structured (a chain of $n$ matchings). The adversary can then put all the welfare on whichever matching the algorithm avoids.
- **Adaptive query lower bound.**
  - On the cyclic shift profile, $m_1$'s and $w_1$'s stable partners are each in bijection with the $n$ stable matchings, in opposite orders.
  - The adversary answers 1 in the top half of the "uninformed region" and 0 in the bottom half, so each query at most halves it.
  - Queries to $m_1$ and to $w_1$ shrink the same set of stable matchings, so the proof treats both agents as one proxy agent. After fewer than $\log_2 n$ halvings in total, some stable matching $\tilde\mu$ still leaves both $m_1$'s and $w_1$'s partners unqueried.
  - The adversary then sets the 0/1 transition points. If the algorithm outputs $\tilde\mu$, it gets 0 while $\mu^*_M$ gets 1. Otherwise $\tilde\mu$ gets 2 and the algorithm's output gets 1.
- **Stable-TSF** adapts the threshold-step-function method of Amanatidis et al. (2021, 2022).
  - Each agent's ranking is restricted to its stable partners. This is needed so the simulated optimum is a stable matching.
  - Query $f^s(a)$ to learn $v^*_a$.
  - Use $\lambda=4\ln(1/\varepsilon)/\varepsilon$ thresholds $t_\ell=\varepsilon^{\ell/\lambda}/4$. Binary search the ranking to sort stable partners into buckets by value relative to $v^*_a$, at $\log_2 n$ queries per threshold.
  - Set each simulated value to its bucket's lower bound, with 0 for the last bucket. Return the stable matching with the highest simulated welfare, computed by $\mathcal A_{ilg}$.
  - Agents whose optimal partner falls in the last bucket lose at most $t_\lambda(\mathrm{SW}_M(\mu^*_M)+\mathrm{SW}_W(\mu^*_W))\le 2t_\lambda\,\mathrm{SW}(\text{output})=\tfrac{\varepsilon}{2}\mathrm{SW}(\text{output})$. This uses the fact that each agent's stable favorite is its partner in its own side's optimal matching. This is what improves on the $O(\log^2 n/\varepsilon)$ bound of the non-stable setting.
  - All other agents lose at most a factor $\varepsilon^{-1/\lambda}$. In total, $\mathrm{dist}\le\varepsilon/2+e^{\varepsilon/4}\le1+\varepsilon$.
- **HassePath.**
  - When the rotation poset is a chain, the stable matchings form a sequence $\mu_0=\mu^*_M,\dots,\mu_z=\mu^*_W$. Along it, $\mathrm{SW}_M$ never increases and $\mathrm{SW}_W$ never decreases.
  - The algorithm uses "matching-level" queries that return $\mathrm{SW}_M(\mu)$ or $\mathrm{SW}_W(\mu)$, each counted as one query per agent.
  - It binary-searches the sequence for $k=2/\log_2(1+\varepsilon)-2$ target matchings, each about a $(1+\varepsilon)$ factor apart in side welfare, and outputs the best one.
  - The sequence has at most $n^2$ matchings, because each pair appears in at most one rotation.

## Experiments
- **Preference generation** follows the stable-matching instance map of Boehmer, Heeger & Szufa (2024). Four statistical cultures are used:
  - Attributes (Bhatnagar et al. 2008)
  - Impartial Culture
  - IC2 (two blocks)
  - Mallows (normalized dispersion)
- Euclidean cultures are excluded because they have a unique stable matching.
- **Values consistent with the rankings** are drawn from Uniform[0,1], Beta(1/2,1/2), or an exponential distribution.
- **Table 1:** 100 profiles per cell, $n\in\{5,10,15,20,40\}$. DA's empirical average-case distortion is at most about 1.047 everywhere; the worst cell is IC with exponential values at $n=5$. Under Attributes it is about 1.001–1.007.
- **Fig. 6:** "spiked uniform" values (probability 0.98 uniform on $[0,0.2]$, probability 0.02 near 1), $n$ from 3 to 15.
  - DA stays at or below 1.5 except Mallows at $n=3$ (about 1.55), and falls toward 1 as $n$ grows.
  - 1-MoWo stays at about 1.00–1.07.
  - Rand-MoWo is generally no better than deterministic DA. This matches Filos-Ratsikas & Voudouris (2024) on randomized voting rules in practice.
- **What the evidence supports:** DA does well on random instances of these types. Theory gives only the bound of 2, and $n\le40$ is small.

## Limitations and gaps
- The model is the balanced, complete-list, one-to-one marriage problem.
- Incentives are not studied: rankings and query answers are assumed truthful. (This observation is mine; the paper doesn't discuss it.)
- The query bounds have a gap in their $\varepsilon$-dependence: $O(\log n/\varepsilon^2)$ upper bound versus Conjecture 1.
- There is no tight average-case result.
- Future work proposed by the authors:
  - popular matchings and stable fractional matchings (both have stronger benchmarks, so the factor-2 arguments break);
  - noisy or unreliable query answers (consistency/robustness with predictions; compare McCauley et al. 2026 on stable matching with ordinal predictions);
  - roommates, hospitals/residents, many-to-many, and 3D stable matching.
- v1 has small typos in the proofs, which matter if checking them:
  - Thm 4.2 Case 2 sets $\mathrm{tr}(v_{m_1})$ twice where the second should be $\mathrm{tr}(v_{w_1})$.
  - The Thm 4.3 proof writes $U_{m_2}$ where $U_{w_1}$ is meant.
  - The Fig. 4 caption says "Theorem 3.3" for the cyclic shift profile.
  - The query count in the Thm 4.4 proof says "$\varepsilon<\log_2 n$" where Algorithm 4 uses $\varepsilon<(\log_2 n)/n$.

## Relevance to my work
- *Provisional until the project direction is set.*
- Dating apps mostly collect ordinal or binary signals (rankings, likes). This paper measures what ordinal-only stable matching costs in welfare, and how much a few "intensity" queries buy back. Examples of such queries might be super-likes, ratings, or interviews or first dates.
- The factor-2 results reduce to one structural fact: each side's optimal stable matching dominates every stable matching for that side. So any mechanism that can tell which side's welfare matters more gets a 2-approximation.
- Possible extension angles the paper leaves open:
  - many-to-one or roommates versions
  - strategic query answers
  - realistic (non-i.i.d.) value models for the average case
- Contrast with [[Rios 2026 - The Dating Heuristic]]: real dating apps don't output one stable matching. They repeatedly show profiles and count mutual likes. See that note's "Relevance" section for a possible bridge.

## Follow-up reading
- Amanatidis, Birmpas, Filos-Ratsikas & Voudouris (2021, AIJ; 2022, JAIR; 2024, SIDMA): query-enhanced distortion
- Anshelevich, Filos-Ratsikas, Shah & Voudouris (2021): distortion survey
- Anshelevich, Das & Naamad (2013): welfare vs. stability in matching
- Caragiannis & Fehrs (2024): average-case distortion
- Caragiannis, Filos-Ratsikas, Kanellopoulos & Vaish (2021): stable fractional matchings
- Irving, Leather & Gusfield (1987); Gusfield & Irving (1989): optimal stable matching and the structure of stable matchings
- Boehmer, Heeger & Szufa (2024): synthetic stable matching instances
- Ashlagi, Chen, Roghani & Saberi (2025): stable matching with interviews

## Concepts
- [[Stable Matching]]
- [[Deferred Acceptance]]
- [[Distortion]]
- [[Query-Enhanced Algorithms]]
- [[Rotation Poset]]
