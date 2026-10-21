---
type: synthesis
question: "Can quality-weighted DH-int keep its additive-quality guarantee when the platform does not know match qualities and must query them, for example through an LLM agent for each user?"
created: 2026-10-20
updated: 2026-10-21
tags: [dating/platforms, matching/quality, elicitation, research/project]
aliases: [queried match quality, Bayesian query model, backlog screening, value-indexed DH-int, unknown match quality, budgeted screening, screening-aware DH-int]
sources: ["[[Rios 2026 - The Dating Heuristic]]", "[[Filos-Ratsikas 2026 - The Distortion of Stable Matching]]"]
origin: claude
status: seed
---
# Match Quality with Queried Values

> [!question] Can quality-weighted DH-int keep its additive-quality guarantee when the platform does not know match qualities and must query them, for example through an LLM agent for each user?

> [!note] Preliminary
> These are informal proofs from 2026-10-20 and are not in Lean. B1–B3 and the examples were checked by brute force (see Evidence). This is phase 2 of [[Match Quality in the Dating Heuristic Framework]]: unknown quality, additive objective. The project chose the Bayesian model as its main model, with the distortion-style model as a warm-up.

## Answer

**Summary**
- **Warm-up (distortion-style model).** Rankings are free and value queries are exact.
  - Weighted DH-int on threshold-step estimates gets $c_K(1-\varepsilon)/\lambda$ of the full-information optimum.
  - It needs $O(\log n\cdot\log_\lambda(Kn/\varepsilon p))$ queries per user.
  - The same reduction turns any known-quality top-$k$ guarantee into one with queries.
- **Bayesian model (main model).**
  - **B1.** If responders can screen their backlogs between periods, a *value-indexed* DH-int keeps $c_K$. The program has to see each pair's value distribution, not just its mean: mean-weighted DH-int can be arbitrarily bad.
  - **B2.** With budgeted queries before period 1, $c_K$ still holds if the platform picks the query strategy that maximizes the expected optimum of the value-indexed program. That step is a stochastic dynamic program, much harder than DH-int's MIP. So B2 shows that all the loss beyond $c_K$ comes from choosing what to query.
  - **B3.** When a responder can screen only $b_\ell$ members of its backlog, *screening-aware* DH-int gets $c_K\rho\ge c_K/2$. Its program accounts for the budget, and each responder marks backlog members at random, then screens them in random order. A program that ignores the budget can be arbitrarily bad.
  - **Open:** a tractable query strategy for period 1 (sketch below), and whether B3's factor $\rho$ is needed.

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

#### B3. Budgeted screening: $c_K\rho$, with $\rho\ge1/2$
**Setting.**
- As in B1, except that responder $\ell$ can screen at most $b_\ell$ backlog members between periods, possibly fewer than its backlog holds. OPT has the same budgets.
- A screen reveals the member's pair weight.
- If the sender's own value comes free (its agent answers at most $K$ queries), split each sender by that value as separate items. Nothing below changes, since each sender still contributes at most one item.

**Single responder.**
- *Notation.* Let $\pi_i=\phi^1_{i\ell}x_{i\ell}$ be the probability that sender $i$ is in the backlog. Let $W_i=\phi^2_{\ell i}w_{\ell i}$ be its random weight, with mean $\mu_i$.
- *Program.* $G_\ell(x)$ uses three kinds of variables:
  - $z_i$: $i$ arrives and is screened;
  - $y_{iv}$: $i$ is screened, has weight $v$, and is shown;
  - $u_i$: $i$ arrives, is not screened, and is shown.

  $$G_\ell(x)=\max\sum_{i,v}v\,y_{iv}+\sum_i\mu_iu_i\quad\text{s.t. }y_{iv}\le z_i\Pr[W_i=v],\ \ z_i+u_i\le\pi_i,\ \ \sum_iz_i\le b_\ell,\ \ \sum_{i,v}y_{iv}+\sum_iu_i\le K_\ell.$$
- *Every policy satisfies these constraints in expectation.* The key one is $y_{iv}\le z_i\Pr[W_i=v]$. It holds because the decision to screen $i$ is made before $W_i$ is seen, and $W_i$ is independent of everything else the platform sees.
- *Policy ("mark, then screen in random order").*
  1. Mark each backlog member $i$ independently with probability $z_i/\pi_i$, using the program's $z$.
  2. Screen the marked members in uniformly random order until the budget is spent.
  3. Show the $K_\ell$ best, ranking screened members by $W$ and the rest by $\mu$.

**Lemma B3.** The policy earns at least $c_{K_\ell}\,\rho\,G_\ell(x)$, where $\rho=\min_i\mathbb E\big[\min(1,b_\ell/(1+|M_{-i}|))\big]$ and $M_{-i}$ is the set of other marked members. $\rho\ge1/2$ always, and $\rho\ge b/(b+1)$ for $b_\ell\le2$.
1. **Layer cake.** The shown value is $\int_0^\infty\min(N_\theta,K)\,d\theta$, where $N_\theta$ counts the candidates whose weight is at least $\theta$.
   - Let $\mu_\theta=\sum_i[z_i\Pr(W_i\ge\theta)+(\pi_i-z_i)\mathbb 1(\mu_i\ge\theta)]$. At the program's $z$, $\int\min(\mu_\theta,K)\,d\theta=G_\ell(x)$, because the fractional program fills the highest weights first.
   - So it suffices to show $\mathbb E\min(N_\theta,K)\ge\rho\,c_K\min(\mu_\theta,K)$.
   - Drop marked members that were not screened from the candidates. This only lowers the policy's value.
2. **Comparison with no budget.** Let $N'_\theta$ count as if every marked member were screened: marked members with $W\ge\theta$ plus unmarked members with $\mu\ge\theta$.
   - Its indicators are independent across senders, one per sender, with total mean $\mu_\theta$. So R1's lemma gives $\mathbb E\min(N'_\theta,K)\ge c_K\min(\mu_\theta,K)$.
   - What remains is $\mathbb E\min(N_\theta,K)\ge\rho\,\mathbb E\min(N'_\theta,K)$.
3. **Count in a fixed order.** Give each member an independent uniform priority $U$. Order the members with marked ones first, by $U$, then unmarked ones. Then $\min(N,K)$ is the number of good candidates with fewer than $K$ good candidates before them, and likewise for $N'$.
   - *Unmarked good member.* Whenever it counts in $N'$ it also counts in $N$, because screened-and-good members are a subset of marked-and-good ones.
   - *Marked good member $i$ with priority $u$.* It counts in $N'$ if $E_2$ holds: fewer than $K$ marked-good members come before $u$. It counts in $N$ if $E_1$ also holds: fewer than $b$ marked members come before $u$, so $i$ is screened.
4. **Harris.** For fixed $u$, $E_1$ and $E_2$ are both decreasing events in the other members' independent coordinates. Each member's state is ordered unmarked < marked-bad < marked-good, together with whether its priority is below $u$. So $\Pr[E_1\cap E_2]\ge\Pr[E_1]\Pr[E_2]$.
   - Putting marked members first matters. With mixed orders, an unmarked-good member and a marked-bad member compete for different resources: one takes a display slot, the other a screen. Then $E_1$ and $E_2$ can be negatively correlated.
5. **Chebyshev.** $\Pr[E_1(u)]$ and $\Pr[E_2(u)]$ both decrease in $u$. So $\int_0^1\Pr[E_1]\Pr[E_2]\,du\ge\int_0^1\Pr[E_1]\,du\cdot\int_0^1\Pr[E_2]\,du$.
   - The first factor is the probability that $i$ is among the first $b$ marked members, $\mathbb E[\min(1,b/(1+|M_{-i}|))]\ge\rho$.
   - The second factor is $i$'s count in $N'$.
6. **Bounding $\rho$.** We have $\mathbb E|M_{-i}|\le\sum_jz_j\le b$.
   - By Markov's inequality, $E_1(u)$ fails with probability at most $u$, which gives $\rho\ge\int_0^1(1-u)\,du=1/2$.
   - For $b\le2$, $\min(1,b/(1+d))$ lies above the line through its values at $d=b$ and $d=b+1$ at every integer $d\ge0$. That line decreases in $d$, so $\rho\ge b/(b+1)$.

**Theorem B3 (two periods).** Screening-aware DH-int earns at least $c_K\rho\,\mathrm{OPT}\ge(c_K/2)\,\mathrm{OPT}$, where $\rho$ is the smallest over responders.
- *Algorithm.* Use program (16), with mutual views at $\beta_e\mathbb E[w_e]$ and period-2 part $\sum_\ell G_\ell(x)$. Since $\pi_i=\phi^1x$ enters linearly, this is still a MIP of DH-int's shape. In period 2, run the policy above.
- *Proof.* This is B1's chain.
  - Every policy satisfies $G_\ell$'s constraints, so OPT is at most the program's optimum.
  - Lemma B3 bounds each responder from below.
- *Consistency with B1.* If every budget covers the whole backlog, the program sets $z=\pi$, $\rho=1$, and this is B1.
- *Queries before period 1.* B2's conditioning argument goes through unchanged with $c_K\rho$ in place of $c_K$.

**Example: the program must see the budget.**
- $n$ initiators each have one slot, and every like is certain.
- *Pooled:* every initiator initiates toward $r$, with $K=b=1$. $r$'s value for each is $n$ with probability $1/n$, and 0 otherwise.
- *Split:* each initiator initiates toward its own responder, for a sure value of $1/2$.
- B1's program assumes $r$ screens everyone. It scores pooled at $n>n/2$, so it pools. But one screen earns only $2-1/n$, so it gets about $4/n$ of OPT: 0.611 at $n=6$ and 0.380 at $n=10$.
- $G_r$ scores pooled at $2-1/n$, so screening-aware DH-int splits.

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
- **Brute force for B3, 2026-10-20.** `data/scripts/screening_budget_check.py` solves $G_\ell$ with scipy. It computes the policy exactly and the optimal adaptive screening policy by dynamic programming, over three seeds. Every check passed.
  - *Single responder:* 9,000 random instances with 2–6 senders and binding $b$ and $K$, plus hill-climbing.
    - OPT $\le G$ and $\mathrm{ALG}\ge c_K\rho\,G$ always held.
    - The worst ALG/$(c_KG)$ was $1.09$. The worst ALG/OPT was $0.83$.
    - $\rho$ went as low as $0.501$ in individual instances.
  - *$\rho\ge b/(b+1)$* held exactly on 60,000 random Poisson-binomials, for $b=1..4$.
  - *Two-period lift:* 600 random one-directional markets. The worst ALG/OPT was $0.93$.
  - *Budget-blind example:* the numbers above come from the script.
- *Not from an ingested source; to verify or ingest:*
  - Weitzman (1979), Pandora's box;
  - Singla (2018), "The Price of Information in Combinatorial Optimization";
  - Gupta, Nagarajan & Singla (2017), adaptivity gaps for stochastic probing;
  - Chekuri, Vondrák & Zenklusen (2014), contention resolution schemes.

## Gaps
- **Nothing here is in Lean.**
  - B1 should be a small extension of `PoissonGap.lean` to random weights.
  - B2 is a conditioning argument.
  - B3 adds Harris's inequality for product measures, which Mathlib may not have in this form.
- **Tractable queries before period 1.** This is only a sketch.
  - The rounding constant $\gamma$ is unverified.
  - It covers one-directional, sequential-only designs. With two directions, independent rounding can show a pair both ways, and mutual views couple two users' capacity.
  - It is also open whether simple rules, such as screening the $b$ best by prior, lose only a constant.
- **B3's factor $\rho$.**
  - *Is it needed?* No tested instance came near $c_K\rho$. But instances with at most 6 senders cannot reach the Poisson worst case behind $c_K$ even without a budget, so this does not show that $\rho$ is unnecessary. A test with many small senders (Monte Carlo) would.
  - *Is $\rho\ge b/(b+1)$ for every $b$?* It is proved for $b\le2$ and holds numerically for Poisson-binomials. A general proof needs their concentration, since arbitrary distributions can go lower for $b\ge3$.
  - *Smarter screening orders* (for example, by each member's value of screening) are not analyzed.
  - *The two-period check* covered only one-directional markets.
- **Warm-up.** The query count depends on $p_\ell$, and there are no lower bounds on the number of queries.
- **Top-1 with queries.** Worked out in [[Top-k Match Quality]]: free rankings, Bayesian priors, queries before period 1 and budgeted screening all carry over to credit-DH. Pandora's-box models, where one user inspects candidates at a cost, are still unexplored.
