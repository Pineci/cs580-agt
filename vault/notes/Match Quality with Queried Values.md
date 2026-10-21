---
type: synthesis
question: "Can quality-weighted DH-int keep its additive-quality guarantee when the platform does not know match qualities and must query them, for example through an LLM agent for each user?"
created: 2026-10-20
updated: 2026-10-20
tags: [dating/platforms, matching/quality, elicitation, research/project]
aliases: [queried match quality, Bayesian query model, backlog screening, value-indexed DH-int, unknown match quality]
sources: ["[[Rios 2026 - The Dating Heuristic]]", "[[Filos-Ratsikas 2026 - The Distortion of Stable Matching]]"]
origin: claude
status: seed
---
# Match Quality with Queried Values

> [!question] Can quality-weighted DH-int keep its additive-quality guarantee when the platform does not know match qualities and must query them, for example through an LLM agent for each user?

> [!note] Preliminary
> These are informal proofs from 2026-10-20 and are not in Lean. B1, B2 and the examples were checked by brute force (see Evidence). This is phase 2 of [[Match Quality in the Dating Heuristic Framework]]: unknown quality, additive objective. The project chose the Bayesian model as its main model, with the distortion-style model as a warm-up.

## Answer

**Summary**
- **Warm-up (distortion-style model).** Rankings are free and value queries are exact.
  - Weighted DH-int on threshold-step estimates gets $c_K(1-\varepsilon)/\lambda$ of the full-information optimum.
  - It needs $O(\log n\cdot\log_\lambda(Kn/\varepsilon p))$ queries per user.
  - The same reduction turns any known-quality top-$k$ guarantee into one with queries.
- **Bayesian model (main model).**
  - **B1.** If responders can screen their backlogs between periods, a *value-indexed* DH-int keeps $c_K$. The program has to see each pair's value distribution, not just its mean: mean-weighted DH-int can be arbitrarily bad.
  - **B2.** With budgeted queries before period 1, $c_K$ still holds if the platform picks the query strategy that maximizes the expected optimum of the value-indexed program. That step is a stochastic dynamic program, much harder than DH-int's MIP. So B2 shows that all the loss beyond $c_K$ comes from choosing what to query.
  - **Open:** a tractable query strategy for period 1 (sketch below), and backlogs larger than the screening budget.

The setting is the two-period model of [[Rios 2026 - The Dating Heuristic]], with its assumptions: empty initial backlog, history-independent like probabilities, no mutual views in period 2. As in R1, $c_K=1-e^{-K}K^K/K!$, where $K$ is at most every display cap.

### Shared setup
- **Directional quality.** $q_{\ell\ell'}\ge0$ is $\ell$'s value for $\ell'$. A match $e=\{\ell,\ell'\}$ earns $w_e=q_{\ell\ell'}+q_{\ell'\ell}$, and additive quality is $Q=\mathbb E\sum_{e\in\mathcal M}w_e$. The earlier note's symmetric $q_e$ is the case $q_{\ell\ell'}=q_{\ell'\ell}=q_e/2$.
- **Queries.** A query $(\ell,\ell')$ is answered by $\ell$'s agent and reveals $q_{\ell\ell'}$.
- **R2 for any weights.** R2 holds for any non-negative pair weights. So with known $q$, DH-int weighted by $w_e$ is $c_K$-approximate.

### Warm-up: distortion-style model
This is the model of [[Query-Enhanced Algorithms]] and [[Distortion]].
- $\ell$'s agent reports $\ell$'s ranking of its potentials $\mathcal P_\ell$ by $q_{\ell\ell'}$ for free. A value query returns the exact value, and cost is counted per agent. Values are worst case among those consistent with the rankings.
- The benchmark $\mathrm{OPT}(q)$ is the best adaptive policy that knows $q$.
- Notation: $n=\max_\ell|\mathcal P_\ell|$. $t_\ell$ is $\ell$'s top-ranked potential, with value $v^*_\ell=q_{\ell t_\ell}$. $p_\ell$ is the largest probability that $\ell$ and $t_\ell$ match when the platform shows only that pair ($\phi\phi$ in every design).

**Lemma A (sandwich).** If $\tilde q\le q\le\lambda\tilde q+b$ for every pair, then weighted DH-int run on $\tilde q$ earns $Q_q\ge c_K\big(\mathrm{OPT}(q)-\mathrm{OPT}(b)\big)/\lambda$.
- For a fixed policy $\pi$, $Q_q(\pi)=\sum_e\Pr[e\in\mathcal M]\,w_e(q)$ is linear and increasing in $q$. The policy's choices depend on $\tilde q$, but its match distribution does not depend on $q$.
- So $Q_q(\mathrm{ALG})\ge Q_{\tilde q}(\mathrm{ALG})\ge c_K\,\mathrm{OPT}(\tilde q)$, using R2 with weights $\tilde q$.
- If $\pi^*$ is optimal for $q$, then $\mathrm{OPT}(q)=Q_q(\pi^*)\le\lambda Q_{\tilde q}(\pi^*)+Q_b(\pi^*)\le\lambda\,\mathrm{OPT}(\tilde q)+\mathrm{OPT}(b)$.

**Theorem A (threshold step function).** For each user $\ell$:
- query $v^*_\ell$;
- for $j=1,\dots,J_\ell$, binary-search the ranking for the last potential with value at least $v^*_\ell\lambda^{-j}$;
- set $\tilde q$ to the largest threshold not above $q$, or to 0 below the last threshold.

With $J_\ell=\lceil\log_\lambda(2K_\ell n/(\varepsilon p_\ell))\rceil$, weighted DH-int on $\tilde q$ gets $c_K(1-\varepsilon)\,\mathrm{OPT}(q)/\lambda$, using $1+J_\ell\lceil\log_2n\rceil$ adaptive queries per user.
- Above the last threshold, $\tilde q\le q<\lambda\tilde q$. Below it, $\tilde q=0$ and $q<v^*_\ell\lambda^{-J_\ell}$, which is the $b$ part.
- Every match needs $\ell$ to see the partner, and $\ell$ sees at most $K_\ell$ profiles per period, so $\ell$ has at most $2K_\ell$ matches. Hence $\mathrm{OPT}(b)\le\sum_\ell 2K_\ell v^*_\ell\lambda^{-J_\ell}\le(\varepsilon/n)\sum_\ell p_\ell v^*_\ell\le\varepsilon\max_\ell p_\ell v^*_\ell$.
- Showing only the pair $(\ell,t_\ell)$ earns at least $p_\ell v^*_\ell$, so $\mathrm{OPT}(q)\ge\max_\ell p_\ell v^*_\ell$ and therefore $\mathrm{OPT}(b)\le\varepsilon\,\mathrm{OPT}(q)$.
- Lemma A finishes the proof.

With $\lambda=1+\delta$ this is $O\big(\log n\,(\log n+\log(K/\varepsilon p))/\delta\big)$ queries per user, in line with the $O(\log^2n/\varepsilon)$ that [[Filos-Ratsikas 2026 - The Distortion of Stable Matching]] cites for non-stable matching.

**Corollaries and limits.**
- **Top-$k$.** Suppose an algorithm gets $\alpha$ of the top-$k$ optimum for every $q\ge0$, which is R5's goal. Run on $\tilde q$, it gets $\alpha(1-\varepsilon)/\lambda$, with $2K_\ell$ replaced by $k$ in $J_\ell$. The reason is that the sum of a user's $k$ best values is increasing, positively homogeneous and subadditive in the values.
- **Noisy LLM scores.** Suppose the agent scores every pair to within a factor $\lambda$, so that after rescaling $\tilde q\le q\le\lambda\tilde q$. Then weighted DH-int on the scores gets $c_K/\lambda$ with no queries at all.
- **Limits.** The query count depends on $p_\ell$. Free rankings are also a weak assumption for an LLM agent, which can score a profile about as cheaply as rank it. This is why the project uses the Bayesian model.

### Bayesian model
- **Priors.** $q_{\ell\ell'}\sim D_{\ell\ell'}$, known, with finite support. Values are independent across ordered pairs and independent of likes.
- **Query windows.**
  - *Before period 1:* agent $\ell$ may make up to $b_\ell$ queries, adaptively.
  - *Between periods ("screening"):* after period-1 likes are seen and before period-2 displays.
- **Benchmark.** OPT is the best adaptive policy, choosing both displays and queries, in the same design with the same budgets.
- **Why not compare with full information.** Take one slot and $n$ candidates who all match for sure, each worth 1 with probability $1/n$ and 0 otherwise. With $b$ queries the best policy gets $1-(1-1/n)^b(1-1/n)$, about $(b+1)/n$. Full information gets $1-(1-1/n)^n\approx0.63$.
- **Posterior means.** For any policy, $Q=\mathbb E\sum_{e\in\mathcal M}\hat w_e$, where $\hat w_e$ replaces each unqueried component by its prior mean. This holds because an unqueried component is independent of every like, query answer and decision.

#### B1. Screening backlogs keeps $c_K$
**Setting.**
- There are no queries before period 1.
- Between periods, every agent can afford $|B_\ell|+K_\ell$ queries. That is enough to learn $w$ for each backlog member: $\ell$'s own value for each of them, and each sender's value for the profile it initiated toward.
- OPT may screen without limit.

**Algorithm: value-indexed DH-int.**
- Solve program (16), weighting mutual views by $\beta_e\,\mathbb E[w_e]$. Replace the period-2 part with
  $$F^v_\ell(x)=\max\sum_{\ell',v}\phi^2_{\ell\ell'}\,v\,y_{\ell\ell'v}\quad\text{s.t. }0\le y_{\ell\ell'v}\le\phi^1_{\ell'\ell}\,x_{\ell'\ell}\Pr[w_{\ell\ell'}=v],\ \ \sum_{\ell',v}y_{\ell\ell'v}\le K_\ell.$$
  This is a MIP of the same shape as (16), with one $y$ for each value of $w$.
- In period 2, each responder screens its backlog and shows the $K_\ell$ members with the highest $\phi^2w$.

**Theorem B1.** Value-indexed DH-int earns at least $c_K\,\mathrm{OPT}$. The bound is tight, because deterministic values are a special case and R1's tight example applies.
1. **OPT's form.** $\mathrm{OPT}=\max_x[\mathrm{imm}(x)+\sum_\ell\mathbb E f_\ell(B_\ell)]$. Here $\mathrm{imm}(x)$ is the expected reward from period-1 mutual views, and $f_\ell(B)$ is the sum of the $K_\ell$ largest values of $\phi^2w$ over $B$.
   - Period-1 decisions come before any information, so deterministic ones are without loss of generality.
   - With known $w$, showing the top $K_\ell$ is the best response. Responders don't interact in period 2.
   - This is the form of `value` in `lean/DatingAlgo/TwoPeriod.lean`.
2. **Layer cake.** $f_\ell=\int_0^\infty\min(N_\theta,K_\ell)\,d\theta$, where $N_\theta=\#\{\ell'\in B_\ell:\phi^2w\ge\theta\}$.
   - The indicators in $N_\theta$ are independent across senders, because each sender's arrival and its pair's value are independent of the other senders'.
   - Write $\mu_\theta=\sum_{\ell'}\phi^1x\Pr[\phi^2w\ge\theta]$ for the mean of $N_\theta$.
3. **The program in the same form.** $F^v_\ell(x)=\int_0^\infty\min(\mu_\theta,K_\ell)\,d\theta$, because the fractional program fills the highest values first.
4. **Upper bound.** By Jensen, $\mathbb E\min(N_\theta,K)\le\min(\mu_\theta,K)$. So $\mathbb Ef_\ell\le F^v_\ell$, and OPT is at most the program's optimum.
5. **Lower bound.** R1's key lemma gives $\mathbb E\min(N_\theta,K)\ge c_K\min(\mu_\theta,K)$. Integrating, $\mathbb Ef_\ell\ge c_KF^v_\ell$.
6. **Conclusion.** At the program's optimum $x^*$, the algorithm earns $\mathrm{imm}(x^*)+\sum_\ell\mathbb Ef_\ell\ge c_K\cdot(\text{program optimum})\ge c_K\,\mathrm{OPT}$.

The only new point is that R1's argument never needed fixed weights: independent random weights pass straight through the layer cake.

**Example: mean-weighted DH-int fails.**
- $n$ initiators each have one slot, and every like is certain.
- *Pooled:* every initiator initiates toward $r$, who has one slot. $r$'s value for each is $n$ with probability $1/n$, and 0 otherwise.
- *Split:* each initiator initiates toward its own responder, for a sure value of $2/n$.
- The mean-weighted program scores pooled at 1 and split at 2, so it splits and earns 2.
- Pooled with screening earns $n(1-(1-1/n)^n)\approx0.63n$.
- So the ratio tends to 0: it is 0.307 at $n=10$ and 0.032 at $n=100$. The value-indexed program scores pooled at $n$ and picks it.

#### B2. Queries before period 1: $c_K$ with the best query strategy
**Setting.**
- Each agent $\ell$ has a budget of $b_\ell$ queries before period 1, used adaptively. Screening between periods works as in B1.
- $H$ is the history before period 1: the queries and their answers. Under the posterior, queried components are fixed and the rest keep their priors, still independent.
- $\Phi(H)$ is the optimum of the value-indexed program for the posterior.

**Algorithm.** Pick a query strategy $\sigma^*$ that maximizes $\mathbb E\,\Phi(H)$. Then run value-indexed DH-int on the posterior.

**Theorem B2.** This algorithm earns at least $c_K\,\mathrm{OPT}$.
- *Upper bound.* Given $H$, any benchmark policy continues as a B1-type policy on the posterior instance. So its conditional value is at most $\Phi(H)$, by step 4 of B1. Hence $\mathrm{OPT}\le\max_\sigma\mathbb E\,\Phi(H_\sigma)=\mathbb E\,\Phi(H_{\sigma^*})$.
- *Lower bound.* Given $H$, the algorithm earns at least $c_K\Phi(H)$, by steps 5–6 of B1 on the posterior. Taking expectations finishes the proof.
- *Restricted strategies.* The argument works for any family of allowed query strategies, provided the algorithm and OPT share it. Examples: only initiators query, or each agent queries only its own values.
- *Caveat.* Computing $\sigma^*$ is a dynamic program over query histories. Rios & Torrico assume their MIP is solved exactly; this step is much harder than that.

#### Toward a tractable query strategy (sketch, not proved)
**Obstacle: the value of information is not submodular.**
- Take one slot. The choice is between a sure alternative worth 3 and a pair with $w=q_1+q_2$, where each $q$ is 0 or 2 with probability 1/2.
- Learning one component alone is worth nothing: the posterior mean is 1 or 3, and the alternative still wins.
- Learning both is worth $0.25$.
- So greedy query selection has no standard guarantee.

**Restriction: "screen when acting".**
- Each agent queries only its own values, and only when its user is about to act:
  - an initiator before period 1, up to $b_\ell$ queries;
  - a responder between periods, on its backlog.
- The two components of a pair are then never queried at the same time, which removes the complementarity above. It is not shown that this removes every such effect.

**Proposed LP.** This is for one-directional, sequential-only designs, with initiators $I$ and responders $J$.
- $s_{ij}$ is the probability that $i$ screens $j$, with $\sum_js_{ij}\le b_i$.
- $x_{ij}(v)\le s_{ij}\Pr[q_{ij}=v]$ is the probability that $i$ screened $j$, saw value $v$, and initiated. $x_{ij}(\circ)\le1-s_{ij}$ is the probability that $i$ initiated without screening. Together, $\sum_j\big(\sum_vx_{ij}(v)+x_{ij}(\circ)\big)\le K_i$.
- The responder part is $F^v_j$ over items $(i,a,u)$, where $a$ is the initiator's known or mean value. Each item has mass $\phi^1_{ij}x_{ij}(a)\Pr[q_{ji}=u]$ and weight $\phi^2_{ji}(a+u)$.
- Each constraint holds in expectation for every policy of this kind, because a screening decision is made before the value it reveals. The fractional top-$K$ bounds the responder's value even when OPT correlates initiators.

**Proposed rounding.**
- Each initiator rounds its own screening and initiation, using only its own values and coins. It needs a scheme that keeps each $x_{ij}(a)$ up to a constant factor $\gamma$ while respecting $b_i$ and $K_i$ on every sample path.
- Contention resolution schemes for uniform matroids (Chekuri, Vondrák & Zenklusen 2014) should give $\gamma$ as a product of two constants. That is unverified.
- Arrivals at each responder then stay independent across initiators, and B1's layer-cake step gives $c_K$ on masses scaled by $\gamma$.
- **Conjecture:** ratio $c_K\gamma$.

## Evidence
- [[Match Quality in the Dating Heuristic Framework]]: the objectives, R1 (the constant $c_K$ and its key lemma), and R2 (any non-negative weights), which A and B1 reuse.
- [[Rios 2026 - The Dating Heuristic]]: the model, program (16), and the decomposition of OPT used in step 1 of B1.
- [[Query-Enhanced Algorithms]], [[Distortion]], [[Filos-Ratsikas 2026 - The Distortion of Stable Matching]]: the free-rankings model with value queries, and the threshold step function.
- [[Correlation Gap]]: the role of independence in B1's lower bound.
- **Lean.** A and B1 rest on `poissonBinomial_min_ge` and `dhInt_quality_approx_cK` in `lean/DatingAlgo/PoissonGap.lean`. The new results themselves are not formalized.
- **Brute force, 2026-10-20.** `data/scripts/bayes_query_check.py` does exact enumeration on small markets, with two- and three-point priors, over three seeds. Every check passed.
  - *B1:* $c_KF^v_\ell\le\mathbb Ef_\ell\le F^v_\ell$ held for every responder and every period-1 decision, on 9,000 random instances across one-directional, two-directional, and two-directional-with-mutual-views designs.
    - The worst ALG/OPT was $0.88$. Hill-climbing got down to $0.83$.
    - Random search doesn't approach $c_K$, but R1's tight example shows the bound is tight.
  - *B2:* OPT and the best $\mathbb E\,\Phi$ strategy were computed by dynamic programming over query histories. $\mathrm{ALG}\ge c_K\,\mathrm{OPT}$ held on 1,200 instances, with worst ratio $0.93$.
  - *Examples:* the needle, mean-weighted DH-int, and non-submodular value-of-information numbers above all come from the script.
- *Not from an ingested source; to verify or ingest:*
  - Weitzman (1979), Pandora's box;
  - Singla (2018), "The Price of Information in Combinatorial Optimization";
  - Gupta, Nagarajan & Singla (2017), adaptivity gaps for stochastic probing;
  - Chekuri, Vondrák & Zenklusen (2014), contention resolution schemes.

## Gaps
- **Nothing here is in Lean.** B1 should be a small extension of `PoissonGap.lean` to random weights; B2 is a conditioning argument.
- **Tractable queries before period 1.** This is only a sketch.
  - The rounding constant $\gamma$ is unverified.
  - It covers one-directional, sequential-only designs. With two directions, independent rounding can show a pair both ways, and mutual views couple two users' capacity.
  - It is also open whether simple rules, such as screening the $b$ best by prior, lose only a constant.
- **Binding screening budgets.** When a backlog is larger than the screening budget, the responder faces a budgeted probing problem. This is open.
- **Warm-up.** The query count depends on $p_\ell$, and there are no lower bounds on the number of queries.
- **Top-1 with queries.** Not started. B1 relies on the additive objective splitting across responders, so top-1 inherits R4's obstruction. Pandora's box is the natural tool when one user inspects candidates at a cost.
