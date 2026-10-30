---
type: synthesis
question: "If the platform can spend only a limited number of oracle calls per user, can a screened-DH mechanism stay truthful and still guarantee a constant fraction of the best budgeted policy — for continuous priors, and for the max-min objective as well as total welfare?"
created: 2026-10-30
updated: 2026-10-30
tags: [dating/platforms, matching/quality, game-theory/incentives, elicitation, fairness, research/project]
aliases: [query budgets, query-aware plan, budgeted SDH, Q-SDH, query-budgeted screened DH]
sources: ["[[Rios 2026 - The Dating Heuristic]]"]
origin: claude
status: seed
---
# Query Budgets in Screened DH

> [!question] If the platform can spend only a limited number of oracle calls per user, can a screened-DH mechanism stay truthful and still guarantee a constant fraction of the best budgeted policy — for continuous priors, and for the max-min objective as well as total welfare?

> [!note] Preliminary
> Written 2026-10-30. This extends [[Truthful Swiping with an LLM Oracle]] (SDH, Theorem 3) and [[Max-Min Match Quality and Egalitarian Matching]] (MM-SDH, Theorem MM) with a per-user call budget. The numbers on the speed-dating data are in the truthful-swiping note (T3, query budgets). Every part of Theorem Q is machine-checked in Lean, for discrete priors and for priors with finite means (see Evidence); the exceptions are listed there.

## Answer

**Summary.** Yes, with one change to SDH: the query probabilities become variables of the plan.
- **Plan (Q-LP).** Choose, for each pair $e$, a query probability $\tau_e$ and a use rule $y_e(s)\le\tau_e$, subject to each user's cap and each user's call budget. Q-SDH queries $e$ with probability $\tau_e$, keeps a found pair with probability $y_e(s)/\tau_e$, selects, and shows. Nothing else changes.
- **Truthful.** Sincere swiping stays dominant: the shown set is still a capped set of acceptable pairs chosen from oracle answers and coins.
- **Calls.** Each user's expected calls are at most its budget.
- **Every user.** With random-order selection, every user gets at least $1/4$ of its planned surplus; with balanced rules, $c_K^2$.
- **Benchmark.** Every budgeted policy, adaptive ones included, induces a feasible Q-LP plan that gives every user exactly its expected utility under the policy.
- **Any objective that is monotone and scales.** For an objective $W$ of the users' expected utilities that is monotone and positively homogeneous, Q-SDH run on a $W$-optimal plan gets at least $\gamma\,W(\text{best budgeted policy})$, with $\gamma=1/4$ or $c_K^2$. This covers max-min ($W=\min$), max-min over the users who can match at all, max-min of normalized utilities, total welfare, and Nash welfare.
- **Continuous priors.** All of the above holds for any priors on the values with finite means, discrete or continuous. Total welfare with SDH's max-weight selection keeps $c_K^2$ of the plan, which closes the truthful-swiping note's gap "Theorem 3(b) for continuous priors".

### Model
- Two sides $I,J$. Pair $e=(i,j)$ has a random value pair $s=(q_{ij},q_{ji})\in\mathbb R^2$ with prior $\mu_e$, independent across pairs. The priors can be discrete or continuous; the values need finite means.
- Costs $c_i,c_j$. Net values $w_I(s)=s_1-c_i$, $w_J(s)=s_2-c_j$. $e$ is *acceptable* at $s$ when both are positive; $A_e$ is that set.
- Caps $K_\ell$: user $\ell$ keeps at most $K_\ell$ matches. Utility is additive within the cap (additive users, or top-$k$ users with $K_\ell\le k$).
- **Calls.** Querying pair $e$ asks first the side less likely to accept, and the other side only if the first says yes. With $\phi^I_e=\mu_e(s_1>c_i)$ and $\phi^J_e=\mu_e(s_2>c_j)$, a query of $e$ charges $i$ an expected $a^I_e=1$ if $\phi^I_e\le\phi^J_e$ and $\phi^J_e$ otherwise, and $j$ an expected $a^J_e=\phi^I_e$ or $1$.
- **Budget.** Each user $\ell$ may be charged at most $Q_\ell$ calls in expectation.

### The plan (Q-LP)
Variables $\tau_e\in[0,1]$ and measurable $y_e:\mathbb R^2\to[0,1]$:
$$y_e(s)\le\tau_e,\qquad y_e=0\text{ off }A_e,\qquad \sum_{j}\int y_{ij}\,d\mu_{ij}\le K_i,\qquad \sum_j a^I_{ij}\tau_{ij}\le Q_i$$
and the same for each $j$. User $i$'s *planned surplus* is $\mathrm{lp}_i(y)=\sum_j\int w_I\,y_{ij}\,d\mu_{ij}$, and similarly for $j$.
- *In words:* $\tau_e$ is how often the platform pays to look at $e$; $y_e(s)$ is how often it then uses $e$ when $e$'s values are $s$. It can't use a pair more often than it looks at it.
- For a discrete prior, $x_{e,s}=y_e(s)\pi_{e,s}$ recovers the truthful-swiping note's $x_{e,s}\le\tau_e\pi_{e,s}$. With $\tau_e$ forced to $\max_s x_{e,s}/\pi_{e,s}$ and no budget, it is SDH's plan.
- For a continuous prior and a fixed total use, the best $y_e$ is $\tau_e$ on the pair's best outcomes, so the value of a pair is the perspective $\tau_eF_e(x_e/\tau_e)$ (truthful-swiping note, T3). Solving the plan this way, or on quantile slices, gives a feasible plan; the guarantees below hold for whatever feasible plan is run, relative to its own value.

### Q-SDH
1. **Plan:** a feasible $(\tau,y)$.
2. **Screen:** query each pair independently with probability $\tau_e$.
3. **Thin:** keep a found pair with values $s$ with probability $y_e(s)/\tau_e$. A pair is then a *candidate* with probability exactly $y_e(s)$ given $s$, independently across pairs.
4. **Select:** each responder keeps a set of its candidates drawn by a rule, then each initiator keeps a set of what it was passed (two stages, as in MM-SDH). Or, for total welfare: the best capped set of found pairs (SDH's max-weight step).
5. **Show:** as in SDH.

### Theorem Q
Let $(\tau,y)$ be feasible.
- **(a) Truthful.** For every realization, each user is shown a capped set of acceptable partners chosen from oracle answers and coins, so sincere swiping is dominant (truthful-swiping note, Theorems 3(a) and 5).
- **(b) Calls.** User $\ell$'s expected calls are $\sum_{e\ni\ell}a^\ell_e\tau_e\le Q_\ell$.
- **(c) Every user.** If every stage-1 rule is $\gamma_1$-balanced and every stage-2 rule $\gamma_2$-balanced, then $\mathbb E[u_\ell]\ge\gamma_1\gamma_2\,\mathrm{lp}_\ell(y)$ for every user. Random order gives $1/4$; balanced rules exist with $\gamma_1=\gamma_2=c_K$ for $K$ at most every cap.
- **(d) Total welfare.** The best capped set of found pairs earns at least $c_K^2\sum_\ell\mathrm{lp}_\ell(y)$.
- **(e) Benchmark.** Every budgeted screened policy $P$ induces a feasible plan $(\tau^P,y^P)$ with $\mathrm{lp}_\ell(y^P)=\mathbb E_P[u_\ell]$ for every user.
- **(f) Objectives.** Let $W:\mathbb R^{I\cup J}\to\mathbb R$ be monotone ($u\le v\Rightarrow W(u)\le W(v)$) and positively homogeneous ($W(\gamma u)=\gamma W(u)$ for $\gamma\ge0$). If $W(\mathrm{lp}(y))\ge W(\mathrm{lp}(y'))-\varepsilon$ for every feasible $y'$, then for every budgeted screened policy $P$,
$$W\big(\mathbb E[u(\text{Q-SDH})]\big)\ \ge\ \gamma_1\gamma_2\big(W(\mathbb E_P[u])-\varepsilon\big).$$

**Budgeted screened policies.** A policy may choose its queries adaptively, one at a time, using coins and every answer so far, and finally picks a capped set of pairs it found acceptable. Its expected calls must respect the budgets. The one property the proof uses is *non-anticipation*: the event "$e$ is queried" is decided before $e$'s values are seen, so given all values, the probability $q_e$ that $e$ is queried does not depend on $e$'s own values. The theorem is stated for every policy with that property, a class that contains all adaptive ones (for discrete priors, Lean proves that every random mixture of adaptive query trees has it).
- *How Lean describes a policy.* For discrete priors, by the law of its (queried, matched) sets given all values. For general priors, by its marginals given all values: $q_e(\omega)$ and $m_e(\omega)$, with $m_e\le q_e$, caps holding for $\sum_{e\ni\ell}m_e$, and non-anticipating $q_e$. Every randomized policy has such marginals, so the bound covers more than real policies.

### Proofs
**(b)** The query coin of $e$ is independent of $e$'s values, and the second side is asked only after a yes, so $e$'s expected charge to $\ell$ is $\tau_ea^\ell_e$. Sum over $e\ni\ell$.

**(c) The coarsening lemma.** The rules see only *which* pairs are candidates, never values. Given the candidate pattern $\eta$, user $i$'s utility is $\sum_j w_I(s_{ij})\,\kappa_{ij}(\eta)$, where $\kappa_{ij}(\eta)$ is the chance the two stages keep $(i,j)$; $\kappa_{ij}(\eta)=0$ unless $(i,j)$ is a candidate. Pairs are independent, so
$$\mathbb E\big[w_I(s_{ij})\,\kappa_{ij}(\eta)\big]=\sum_{\eta}\kappa_{ij}(\eta)\prod_{e}\int f^{\eta}_e\,d\mu_e,$$
with $f^\eta_{ij}=w_I\,y_{ij}$ if $\eta_{ij}$ is "candidate" (else $0$), and $f^\eta_e=y_e$ or $1-y_e$ for the other pairs (Fubini for a product of one-coordinate functions). Only three numbers per pair appear: $X_e=\int y_e\,d\mu_e$, $\int w_Iy_e\,d\mu_e$ and $\int w_Jy_e\,d\mu_e$. So the expectation equals the same expression in a **discrete surrogate market** with one value combination per pair, used with probability $X_e$, worth $\bar w_I=\int w_Iy_e/X_e$ to $i$ and $\bar w_J$ to $j$. The surrogate plan is feasible (caps carry over), its planned surplus is $\mathrm{lp}_\ell(y)$, and MM-SDH's per-user theorem (`mmUtilI_ge`) applies to it. Since $y_e=0$ off $A_e$, $\bar w>0$ whenever $X_e>0$, so the surrogate pairs are acceptable.

**(d)** The best capped set of found pairs is at least the weight of any capped subset of them, in particular of what $c_K$-balanced rules select from the candidates, which are found pairs. Summing (c) over all users gives $c_K^2\sum_\ell\mathrm{lp}_\ell(y)$.

**(e) Resampling.** Write $m_e(\omega)$ for the probability that $P$ matches $e$ given all values $\omega$, and $q_e(\omega)$ for the probability that it queries $e$; $m_e\le q_e$, $m_e=0$ unless $\omega_e\in A_e$, and $\sum_{e\ni\ell}m_e\le K_\ell$. Set $\tau^P_e=\mathbb E[q_e]$ and $y^P_e(s)=\mathbb E\big[m_e(\omega\text{ with }\omega_e:=s)\big]$.
- Replacing $\omega_e$ by an independent copy $s\sim\mu_e$ does not change the law of $\omega$. So for any $f$, $\mathbb E[m_e(\omega)f(\omega_e)]=\int f\,y^P_e\,d\mu_e$. With $f=w_I$ this gives $\mathrm{lp}_i(y^P)=\mathbb E_P[u_i]$; with $f=1$, the caps.
- Non-anticipation: $q_e(\omega\text{ with }\omega_e:=s)=q_e(\omega)$, so $y^P_e(s)\le\mathbb E[q_e]=\tau^P_e$, and $\mathbb E[q_e(\omega)a(\omega_e)]=\tau^P_e\int a\,d\mu_e$, which is the call formula of (b). So the budget carries over.

**(f)** By (c), $\mathbb E[u_\ell]\ge\gamma_1\gamma_2\,\mathrm{lp}_\ell(y)$ for every $\ell$. Monotonicity and homogeneity give $W(\mathbb E[u])\ge\gamma_1\gamma_2W(\mathrm{lp}(y))$. By (e), $W(\mathbb E_P[u])=W(\mathrm{lp}(y^P))\le W(\mathrm{lp}(y))+\varepsilon$. $\square$

### Which objectives (f) covers
- **Max-min:** $W(u)=\min_\ell u_\ell$. Q-SDH's worst-off user gets at least $\theta^*_Q/4\ge\mathrm{OPT}_{\min,Q}/4$ with random order, $c_K^2$ with balanced rules.
- **Isolated users.** A user with no acceptable partner forces $\min_\ell u_\ell=0$ for every policy (max-min note, §5). Taking the min over the users who can match, $W(u)=\min_{\ell\in U'}u_\ell$, or normalizing, $W(u)=\min_\ell u_\ell/M_\ell$ over users with best-case surplus $M_\ell>0$, is still monotone and homogeneous.
- **Total and weighted welfare, Nash welfare** (the geometric mean), and $p$-means with $p\le1$.
- **Not covered:** leximin, which is not a real-valued objective. Still, (c) holds user by user, so every user keeps $\gamma_1\gamma_2$ of whatever a leximin-optimal plan gives it.

## Evidence
- **Vault.** [[Truthful Swiping with an LLM Oracle]] (SDH, Theorem 3, the call model, T3 query budgets on data); [[Max-Min Match Quality and Egalitarian Matching]] (Theorem MM, balanced rules); [[Match Quality with Queried Values]] (B2: with budgeted queries and *unscreened* DH-int, choosing the queries is a hard dynamic program; here screening before display makes it an LP).
- **Data.** `data/scripts/query_budget_check.py`: the query-aware plan keeps 77–79% of SDH's welfare on a quarter of the calls, and the worst-off user's MM-SDH value on about a third (truthful-swiping note, T3).
- **Lean, 2026-10-30.** `lean/check.sh`: 973 theorems, all fully proved, only the standard axioms. Files `lean/DatingAlgo/BudgetedSDH.lean` (finitely many value combinations) and `lean/DatingAlgo/ContinuousSDH.lean` (any priors with finite means); `lean/README.md` maps each result to its Lean name.
  - *(a)* `sdh_dsic` already holds for every planned set of acceptable pairs.
  - *(b)* `qsdh_callsI`, `qsdh_callsJ`; `contCallsI_eq`, `contCallsJ_eq`.
  - *(c)* `qsdh_quarter`, `qsdh_cK`; `contUtil_ge`, `contUtil_quarter`, `contUtil_cK`. For general priors through the surrogate market: `contUtilI_eq` shows Q-SDH's expected utility *equals* MM-SDH's in the surrogate, using the coarsening lemma `integral_prodExp_bern`.
  - *(d)* `qsdh_welfare`; `contSDH_welfare`, with SDH's own max-weight selection, via `rules_le_bestMatch`.
  - *(e)* `exists_qplan_of_policy` with `isBudgetedPolicy_of_trees` (adaptive query trees are non-anticipating, `QTree.mem_run_update`); `exists_contPlan_of_policy`, via resampling (`measurePreserving_update`, `integral_mul_coord_eq`).
  - *(f)* `objective_of_perUser`, `qsdh_objective_quarter`, `qsdh_objective_cK`; `cont_objective_of_perUser`, `cont_objective_quarter`, `cont_objective_cK`. Instances: `isMonoHom_inf'` (max-min over any nonempty set of users), `isMonoHom_weightedInf` (normalized max-min), `isMonoHom_weightedSum`.
  - *Never worse than scaling:* `qfeasible_scaled`.
  - *Not in Lean:* Nash welfare and $p$-means are covered by (f)'s hypotheses but not instantiated; the perspective form $\tau_eF_e(x_e/\tau_e)$ of the continuous plan; the Chernoff remark under Gaps.

## Gaps
- **Hard caps.** The budget holds in expectation. Calls charged to a user are a sum of independent 0/1 terms, so Chernoff bounds the overshoot, but a hard cap needs dependent rounding or truncation, which breaks the independence the proofs use.
- **Constants.** $c_K^2$ and $1/4$ are what the analysis gives; the data suggest much more (0.63–0.92 of planned surplus per user).
- **Asking order.** Policies ask within a pair in the fixed order (less likely side first). Letting the benchmark choose the order per pair needs one $\tau$ per order.
- **Solving the continuous plan.** The guarantee is relative to whatever plan is run. An optimal continuous plan need not be computed exactly: (f) holds for $\varepsilon$-optimal plans, such as quantile discretizations.
- **Strategic oracle answers** are out of scope, as in the truthful-swiping note.
