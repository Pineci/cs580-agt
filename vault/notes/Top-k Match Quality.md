---
type: synthesis
question: "Is there a dating-heuristic algorithm with a constant-factor guarantee for top-k (and top-1) match quality, first with known qualities and then when qualities must be queried?"
created: 2026-10-21
updated: 2026-10-21
tags: [dating/platforms, matching/quality, research/project]
aliases: [top-1 match quality, best-match quality, credit-DH, credit program, top-k quality]
sources: ["[[Rios 2026 - The Dating Heuristic]]"]
origin: claude
status: seed
---
# Top-k Match Quality

> [!question] Is there a dating-heuristic algorithm with a constant-factor guarantee for top-k (and top-1) match quality, first with known qualities and then when qualities must be queried?

> [!note] Preliminary
> These are informal proofs from 2026-10-21 and are not in Lean. The results were checked by brute force on small markets (see Evidence). This note works out R5 of [[Match Quality in the Dating Heuristic Framework]], the project's end goal ($k=1$), and carries it into the query models of [[Match Quality with Queried Values]].

## Answer

**Summary**
- **Known qualities (T1).** *Credit-DH* gets $\rho\,c_k\ge c_k/2$ of the best adaptive policy. It is DH-int's program with credit variables, plus a random period-2 rule.
  - For top-1 that is at least $0.316$, whatever the display caps.
  - Quality-weighted DH-int is only $\Theta(k/K)$ here.
- **Queried qualities.**
  - *Free rankings:* $\rho\,c_k(1-\varepsilon)/\lambda$, by the sandwich lemma.
  - *Bayesian priors, no queries (T2):* the same $\rho\,c_k$, with credits indexed by value. A user picks their best match after the fact, so uncertain values help even without queries.
  - *Queries before period 1:* $\rho\,c_k$, given the best query strategy (B2's argument).
  - *Budgeted screening between periods (T3):* $c_k\rho_b\rho_K/(1+\rho_b)\ge c_k/6$, using a random priority between screened and unscreened candidates.
- **Caveat.** Credit-DH's period-2 rule is random. On small random markets it often loses to weighted DH-int. Its value is the worst-case guarantee.

**Setting.** This is the two-period model of [[Rios 2026 - The Dating Heuristic]], with its assumptions: empty initial backlog, history-independent likes, no mutual views in period 2.
- **Directional values.** $q_{\ell\ell'}$ is $\ell$'s value for $\ell'$.
- **Objective.** $U_k=\mathbb E\sum_\ell\mathrm{top}_k\{q_{\ell\ell'}:\ell'\text{ matched with }\ell\}$.
- **Constant.** $c_k=1-e^{-k}k^k/k!$, so $c_1=0.632$ and $c_2=0.729$.
- **Factor $\rho$.** $\rho=\min\mathbb E[\min(1,K_\ell/(1+D))]$, where $D$ is the number of *other* marked members in the same backlog. It is at least $1/2$, and at least $K/(K+1)$ when $K\le2$, by the argument in B3 of [[Match Quality with Queried Values]].
- **Benchmark.** The best adaptive policy for the same design.

### Weighted DH-int is $\Theta(k/K)$
- **Upper bound.** R4 shows at most $2k/(K+k)$, which is $2/(K+1)$ for top-1.
- **New lower bound.** For $k\le2K$, weighted DH-int gets at least $c_K\,k/(2K)$.
  - Each user has at most $2K$ matches, so $\mathrm{top}_k\ge\frac{k}{2K}\cdot$(sum of that user's match values).
  - For every policy, $U_k$ is at most additive quality.
  - R2 gives weighted DH-int $c_K$ of the additive optimum.
- **Why it fails.** A user's period-2 matches come from several responders. The additive program values them as if each added in full.

### T1. Known qualities: credit-DH
**Program.** This makes the R5 linear program precise.
- Keep DH-int's constraints (16) on $(x,w,y)$.
- Pair $e=\{\ell,\ell'\}$ matches with probability $p_e=\beta_ew_e+\phi^2_{\ell\ell'}y_{\ell\ell'}+\phi^2_{\ell'\ell}y_{\ell'\ell}$. At most one term is nonzero, because a pair is shown at most one way.
- Add credits $c_{\ell\ell'}\le p_e$ with $\sum_{\ell'}c_{\ell\ell'}\le k$, and maximize $\sum q_{\ell\ell'}c_{\ell\ell'}$.
- This is still a MIP of DH-int's shape. When $k\ge2K$ the credit constraints never bind, and it becomes weighted DH-int's program.

**Upper bound.** Given any policy, set:
- $y_{\ell\ell'}$ to the probability that $\ell$ shows $\ell'$ in period 2;
- $c_{\ell\ell'}$ to the probability that $\ell'$ is matched with $\ell$ *and* is among $\ell$'s $k$ best matches.

Every constraint holds, and the objective equals $U_k$. So OPT is at most the program's optimum.

**Policy.**
- Period 1 follows the program.
- In period 2, responder $\ell$ marks each backlog member $\ell'$ independently with probability $y^*_{\ell\ell'}/\phi^1_{\ell'\ell}$. It shows the marked ones in uniformly random order, up to $K_\ell$.
- Spare slots can be filled freely. Filling only adds matches, and top-$k$ can only grow.

**Theorem T1.** $U_k(\text{credit-DH})\ge\rho\,c_k\,\mathrm{OPT}\ge(c_k/2)\,\mathrm{OPT}$.

*Proof, for each user $u$, using a layer cake over $u$'s values.*
1. **Sources.** $u$'s matches come from three sources, and each partner appears in at most one:
   - (a) mutual views in period 1;
   - (b) $u$'s initiations, answered by responders;
   - (c) $u$'s own period-2 responses.
2. **Independence.**
   - Source (a) is independent coins.
   - In (b), different responders' backlogs are built from different like coins, and each responder uses its own coins. So (b) is independent across responders.
   - (c) is independent of (a) and (b). But its items are correlated with each other, through $u$'s own capacity.
3. **Marginals.** In each case, compare with the program's match probability.
   - (a) matches it exactly.
   - (b) gets at least $\rho$ times it, because the responder keeps a marked member with probability at least $\rho$.
   - (c), *before* $u$'s capacity cuts its marked set down to $K_u$, matches it exactly.
4. **Ordering.** Count $u$'s first $k$ good matches (value at least $\theta$) in this order: (c) by priority, then (a) and (b).
   - *Items in (c).* For such an item, "$u$ keeps it" (fewer than $K_u$ marked before it) and "it is among the first $k$ good" (fewer than $k$ marked, liked, good (c) items before it) are both decreasing events. So Harris and Chebyshev give a factor of $\rho$, as in B3.
   - *Items in (a) and (b).* They lose at most their marginal factor $\rho$, and they face fewer competitors than in the comparison without capacity limits.
5. **Conclusion.** Let $N'_\theta$ count independent indicators whose probabilities are exactly the program's match probabilities. Then $\mathbb E\min(N_\theta,k)\ge\rho\,\mathbb E\min(N'_\theta,k)\ge\rho\,c_k\min(\mu_\theta,k)$, by R1's lemma with cap $k$.
   - Integrating over $\theta$ gives $\rho\,c_k$ times the fractional top-$k$ of $u$'s match probabilities. That is at least $\rho\,c_k\sum_{\ell'}q_{u\ell'}c^*_{u\ell'}$.
   - Sum over users.

*Compared with R5's conjecture.*
- R5 guessed $c_Kc_k$. The proof gives $\rho\,c_k$: a responder's random truncation costs $\rho$, and there is no separate $c_K$.
- R5 missed that a user's own responses are correlated with each other. The ordering in step 4 handles this.

### Queried qualities
**Free rankings (the warm-up model).** T1 holds for any non-negative values. $U_k$ is increasing, positively homogeneous and subadditive in the values. So Lemma A of the queried-values note gives $\rho\,c_k(1-\varepsilon)/\lambda$, with threshold-step queries and $k$ in place of $2K$.

**T2. Bayesian, no queries.**
- *Program.* Index credits by value: $c_{\ell\ell'}(t)\le p_e\Pr[q_{\ell\ell'}=t]$ and $\sum_{\ell',t}c_{\ell\ell'}(t)\le k$. This bound is valid because, without queries, matches are independent of values.
- *Guarantee.* The policy is the same and gets the same $\rho\,c_k$. In the Harris step, "good" is now an independent random coordinate.
- *Point.* A user picks their best match after the fact, so uncertain values help even without queries. For top-1, a high-variance candidate can be worth more than a safe one with the same mean.

**Queries before period 1.** This is B2's conditioning argument. Given the history, values remain independent under the posterior, so T2 applies to the posterior instance. With the best query strategy the result is $\rho\,c_k\,\mathrm{OPT}$. Choosing that strategy remains intractable, as in the additive case.

**T3. Budgeted screening between periods.**
- *Model.* A responder screens its own values, at most $b_\ell$ of its backlog, between periods. Initiators' values are not screened.
- *Program.* B3's screening variables $z$, $y(t)$, $o$ feed the credits:
  - the responder's credit at value $t$ is at most $\phi^2(y(t)+o\Pr[t])$;
  - the initiator's credit at value $s$ is at most $\phi^2(\sum_ty(t)+o)\Pr[q=s]$.
- *Policy.*
  1. Mark each arrival for screening with probability $z/\pi$, or make it a blind candidate with probability $o/\pi$.
  2. Screen marked arrivals in priority order until the budget $b_\ell$ is spent.
  3. A screened arrival with value $t$ becomes a candidate with probability $y(t)/(z\Pr[t])$.
  4. With probability $\alpha=1/(1+\rho_b)$ screened candidates go first, and otherwise blind candidates go first. Show the first $K_\ell$.
- **Theorem T3.** $U_k\ge c_k\,\rho_b\rho_K/(1+\rho_b)\cdot\mathrm{OPT}\ge(c_k/6)\,\mathrm{OPT}$. Here $\rho_b$ and $\rho_K$ are the survival factors for screening and for display within a group; each is at least $1/2$.
- *Why the random group order.* A blind candidate takes a display slot but no screen. A marked member that turns out bad takes a screen but no slot.
  - In a mixed order, these push the "screened" and "displayed" events in opposite directions, and Harris's inequality fails.
  - With one group first, that group's items get the Harris bound. Randomizing gives each group its share, and $\min(N_s,k)+\min(N_b,k)\ge\min(N_s+N_b,k)$ recombines them.
  - B3's additive analysis avoided this because its display rule ranks by weight. Here the display order decides other users' matches, so the order is part of the policy.

### Example: R4's instance
Take $K=2$ and $k=1$. Credit-DH's program picks the top-1 optimum, a perfect matching plus the admirers, so credit-DH is optimal. Weighted DH-int earns $0.676$ of OPT, which tends to $2/3$.

## Evidence
- [[From DH-int to Credit-DH]]: a walkthrough that puts DH-int, weighted DH-int and credit-DH side by side, for readers new to the project.
- [[Match Quality in the Dating Heuristic Framework]]: the objectives; R1 (constant and lemma); R2; R4 (instance and upper bound); R5 (the conjecture worked out here).
- [[Match Quality with Queried Values]]: Lemma A (sandwich), B2 (conditioning), B3 (marked-first ordering, the bound on $\rho$, screening variables).
- [[Rios 2026 - The Dating Heuristic]]: the model and program (16). [[Correlation Gap]]: the role of independence.
- **Brute force, 2026-10-21.** Exact enumeration over three seeds. Every check passed.
  - `data/scripts/topk_check.py` covers T1 (known values) and T2 (random values, no queries) on 3,600 markets across one-directional, two-directional, and two-directional-with-mutual-views designs.
    - OPT was computed exactly, with period-2 shows allowed to depend on every period-1 outcome.
    - OPT $\le$ program and credit-DH $\ge\rho\,c_k\cdot$program always held.
    - The worst credit-DH/OPT was $0.70$, or $0.73$ with spare slots filled. Credit-DH/$(c_k\,\text{program})$ went as low as $0.977$, so on a few markets $\rho$ or the program's gap shows.
    - Weighted DH-int's worst was $0.69$ on random markets and $0.676$ on R4. On most random markets it beat credit-DH.
  - `data/scripts/topk_screening_check.py` covers T3 on 900 one-directional markets.
    - OPT screens adaptively across all responders and chooses shows jointly.
    - OPT $\le$ program and ALG $\ge c_k\cdot\text{factor}\cdot$program always held.
    - The worst ALG/OPT was $0.715$. The proven factor was never below $0.182$ (the guarantee is $1/6$).
- *Standard tools, not from an ingested source:* Harris's (FKG) inequality for product measures, and Chebyshev's integral inequality.

## Gaps
- **Nothing is in Lean.**
- **Constants.**
  - Whether $\rho$ is needed is open. The markets tested are too small to reach $c_k$'s worst case.
  - There is no hardness or lower bound for top-1 beyond R4.
  - T3's $c_k/6$ is surely loose.
- **The period-2 rule ignores realized period-1 matches and values.** A practical variant would take period 1 from the credit program and respond greedily by marginal top-$k$ gain. It has no guarantee yet and should be tested in simulation.
- **T3 checks covered only one-directional markets.** The random group priority is an analysis device.
- **Not covered:** a tractable query strategy before period 1 (as in the additive case), more than two periods, and strategic users.
