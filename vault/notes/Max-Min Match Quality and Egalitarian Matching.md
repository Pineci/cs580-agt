---
type: synthesis
question: "Can the dating heuristic framework be formulated to maximize the minimum user's expected welfare (max-min / Rawlsian egalitarianism), how does it differ from utilitarian welfare, and does it guarantee truthful swiping?"
created: 2026-10-27
updated: 2026-10-30
tags: [dating/platforms, matching/quality, fairness, game-theory/incentives, research/project]
aliases: [max-min welfare, egalitarian matching, price of fairness, Rawlsian matching, max-min SDH, leximin dating]
sources: ["[[Rios 2026 - The Dating Heuristic]]", "[[Truthful Swiping with an LLM Oracle]]", "[[From DH-int to Credit-DH]]"]
origin: claude
status: seed
---
# Max-Min Match Quality and Egalitarian Matching

> [!question] Can the dating heuristic framework be formulated to maximize the minimum user's expected welfare (max-min / Rawlsian egalitarianism), how does it differ from utilitarian welfare, and does it guarantee truthful swiping?

> [!warning] Corrected 2026-10-30
> The $c_K^2$ guarantee below is false for SDH's own selection step, and the price of fairness in §4 is an artifact of an untied LP. See [[#Correction (2026-10-30)]] for the corrected, machine-checked statements.

## Answer

**Summary**
- **The Max-Min Objective.** Rather than maximizing total utilitarian surplus $\sum_{\ell \in U} \mathbb{E}[u_\ell]$, the platform maximizes the expected welfare of the worst-off agent:
  $$\max_\pi \min_{\ell \in U} \mathbb{E}[u_\ell(\pi)], \quad \text{or equivalently} \quad \max \theta \quad \text{s.t.} \quad \mathbb{E}[u_\ell(\pi)] \ge \theta \; \forall \ell \in U.$$
- **Max-Min Screened DH (MM-SDH).** The planning LP introduces a scalar variable $\theta$ and enforces linear constraints $\mathbb{E}_{\text{LP}}[u_\ell(x)] \ge \theta$ for every user $\ell \in I \cup J$. Because contention resolution and correlation gap bounds hold *user-by-user*, MM-SDH achieves the **exact same constant-factor approximation** as utilitarian SDH:
  $$\min_{\ell \in U} \mathbb{E}[u_\ell(\text{MM-SDH})] \ge c_K^2 \cdot \mathrm{OPT}_{\min} \quad (\text{or } \rho c_k \cdot \mathrm{OPT}_{\min} \text{ for top-}k).$$
- **Truthful Swiping (DSIC) is Preserved.** MM-SDH remains a *swipe-local* policy and displays at most $k$ acceptable profiles per user. By Theorem 1 (Cost-Separability), sincere swiping remains a universal Dominant Strategy (DSIC) against any behavior of other users.
- **How It Differs from Utilitarian (The Price of Fairness).**
  - *Utilitarian matching* herds display capacity toward high-reciprocity, popular pairs, starving disadvantaged or niche users (who may receive near-zero utility).
  - *Max-Min matching* forces the platform to lift the bottom users, shifting displays toward the least fortunate agents.
  - *The Price of Fairness (PoF)*: Total welfare $\sum u_\ell$ can drop significantly (numerical simulation in `data/scripts/maxmin_check.py` reveals a $4.3\times$ reduction in total welfare to achieve a $+241.8\%$ increase in the minimum user's welfare).
- **The Bottleneck & Leximin Refinement.** If even one user has no compatible partners in the market, the global max-min value is $\theta^* = 0$. In practice, the platform should use a **Leximin refinement**: maximize the worst-off user, then subject to that floor, maximize the second-worst-off, and so on.

---

### 1. Mathematical Formulation

#### Market and Utilities
- Bipartite market $U = I \cup J$, two periods, display capacities $K_\ell$.
- Each pair $e = (i, j)$ has compatibility values $q_{ij}, q_{ji} \ge 0$ and match costs $c_i, c_j > 0$.
- Net surplus: $w_{ij} = q_{ij} - c_i$ and $w_{ji} = q_{ji} - c_j$.
- Sincere swiping means swiping right if and only if $q > c$ (i.e., $w > 0$).
- Under Screened DH (SDH), the platform uses an LLM oracle to identify acceptable pairs ($w > 0$ for both), and ensures that no top-$k$ user is ever shown more than $k$ acceptable profiles.

#### Utilitarian vs. Max-Min Objectives
1. **Utilitarian**:
   $$\max_\pi \sum_{\ell \in U} \mathbb{E}[u_\ell(\pi)].$$
2. **Max-Min (Rawlsian Egalitarian)**:
   $$\max_\pi \min_{\ell \in U} \mathbb{E}[u_\ell(\pi)].$$

---

### 2. The Max-Min Screened Dating Heuristic (MM-SDH)

#### The Planning LP
In `ScreenedDH.lean`, an allocation plan is $x_{ij}(c) \in [0, \pi_{ij}(c)]$, representing the probability pair $(i, j)$ is matched under value combination $c$.
For each initiator $i \in I$, their expected LP surplus is:
$$\mathrm{lpSurplus}_I(i, x) = \sum_{j \in J} \sum_{c \in C} (v_I(i, j, c) - c_I(i)) \cdot x_{ij}(c).$$
For each responder $j \in J$, their expected LP surplus is:
$$\mathrm{lpSurplus}_J(j, x) = \sum_{i \in I} \sum_{c \in C} (v_J(i, j, c) - c_J(j)) \cdot x_{ij}(c).$$

The **Max-Min LP** is:
$$\max_{x, \theta} \quad \theta$$
$$\text{subject to} \quad \mathrm{lpSurplus}_I(i, x) \ge \theta, \quad \forall i \in I$$
$$\mathrm{lpSurplus}_J(j, x) \ge \theta, \quad \forall j \in J$$
$$\sum_{j, c} x_{ij}(c) \le K_i, \quad \forall i \in I$$
$$\sum_{i, c} x_{ij}(c) \le K_j, \quad \forall j \in J$$
$$0 \le x_{ij}(c) \le \pi_{ij}(c), \quad x_{ij}(c) = 0 \text{ if unacceptable}.$$

This is a standard Linear Program with $|I \times J \times C| + 1$ variables and $|I| + |J|$ additional linear constraints.

#### Rounding & Approximation Guarantee
The platform executes the exact same SDH contention-resolution scheme:
1. Period 1: Initiations and mutual views from plan $x^*$.
2. Period 2: Responders mark backlog arrivals with probability $x_{ij}^* / \phi^1$ and display marked candidates in random order.

**Theorem (Max-Min Approximation Ratio)**:
In `ScreenedDH.lean`, the contention-resolution lower bound is established *user-by-user*:
$$\mathbb{E}[u_i(\text{SDH})] \ge c_K^2 \cdot \mathrm{lpSurplus}_I(i, x^*), \quad \forall i \in I$$
$$\mathbb{E}[u_j(\text{SDH})] \ge c_K^2 \cdot \mathrm{lpSurplus}_J(j, x^*), \quad \forall j \in J.$$
Taking the minimum over all users $\ell \in I \cup J$:
$$\min_{\ell \in U} \mathbb{E}[u_\ell(\text{MM-SDH})] \ge c_K^2 \cdot \min_{\ell \in U} \mathrm{lpSurplus}_\ell(x^*) = c_K^2 \cdot \theta^* \ge c_K^2 \cdot \mathrm{OPT}_{\min}.$$

*Conclusion*: MM-SDH achieves at least $c_K^2$ (or $\rho c_k \ge c_k/2$ for Credit-DH) of the optimal Max-Min benchmark!

---

### 3. Incentive Compatibility & Truthful Swiping

Does maximizing the minimum user's utility harm truthful swiping? **No!**
- **Swipe-Local Policy**: MM-SDH computes the display plan $(x^*, \theta^*)$ using only prior distributions and oracle queries, not user swipes. Period 2 displays depend only on a responder's own backlog and independent coins.
- **Cost-Separability**: By construction, MM-SDH enforces the IR cap: each user sees at most $k$ acceptable profiles (or at most $K_\ell$ for additive).
- **Dominant Strategy (DSIC)**: By Theorem 1 (`TruthfulSwiping.lean`), sincere swiping ($q > c$) is a **universal Dominant Strategy (DSIC)** against any behavior of other users.

---

### 4. Comparison: Utilitarian vs. Max-Min

We implemented and solved both models in `data/scripts/maxmin_check.py` on a heterogeneous market:
- Initiator $i_0$ has high reciprocity ($\phi = 0.8$) and high quality.
- Initiator $i_2$ is disadvantaged/niche ($\phi = 0.15$).

| Metric | Utilitarian Optimization ($\max \sum u_\ell$) | Max-Min Optimization ($\max \min u_\ell$) | Comparison |
|---|---|---|---|
| **Worst-Off User $\min u_\ell$** | **$0.0266$** | **$0.0909$** | **$+241.8\%$ improvement for the bottom user!** |
| **Best-Off User $\max u_\ell$** | $1.6573$ | $0.1327$ | Inequality drops drastically |
| **Total Welfare $\sum u_\ell$** | **$2.5709$** | **$0.5954$** | Total welfare decreases by $76.8\%$ |
| **Price of Fairness (PoF)** | Baseline ($1.0$) | **$4.3177$** | Ratio of Utilitarian to Max-Min sum |
| **Strategyproofness (DSIC)** | Preserved | Preserved | Sincere swiping dominant in both |

#### The Fundamental Trade-off
1. **Under Utilitarian**: The platform acts as an unconstrained profit-maximizer. It ignores user $i_2$ because spending a display on $i_2$ generates low expected return. $i_0$ and $j_0$ receive all the matches.
2. **Under Max-Min**: The platform acts as a Rawlsian social planner. It is forced to allocate display capacity to user $i_2$ to lift their expected welfare. This cannibalizes capacity from $i_0$ and $j_0$, drastically lowering the aggregate sum of utilities.

---

### 5. Practical Implementation: The Leximin Refinement

A known theoretical edge case of pure max-min is the **isolated user trap**:
If user $i_{\text{iso}}$ has zero acceptable potentials in the entire market ($|\mathcal{P}_{i_{\text{iso}}} \cap G| = 0$), then $\mathbb{E}[u_{i_{\text{iso}}}] = 0$ for *every* policy!
Under a naive max-min solver:
$$\theta^* = 0,$$
and the objective provides no guidance on how to allocate displays among the remaining $n-1$ users.

**Solution: The Leximin Algorithm**:
1. Solve the Max-Min LP to find $\theta_1^* = \max \min_{\ell \in U} \mathbb{E}[u_\ell]$.
2. Identify the bottleneck user(s) whose surplus equals $\theta_1^*$, and fix their welfare constraint $\mathbb{E}[u_\ell] \ge \theta_1^*$.
3. Maximize the second minimum $\theta_2$ over the remaining users, and repeat.
This produces a **Pareto-optimal egalitarian matching** that lifts disadvantaged users without needlessly discarding surplus for easier-to-match users.

---

## Correction (2026-10-30)

§2 claims every user keeps $c_K^2$ of its planned surplus "because contention resolution holds user by user", and that `ScreenedDH.lean` shows this. It doesn't: `ScreenedDH.lean` bounds only *total* weight (`lpValue_le_sdhValue`). And SDH's selection step, the best capped set of found pairs ([[Truthful Swiping with an LLM Oracle|SDH]] step 3), maximizes total weight, which can starve a user. Everything below is machine-checked in `lean/` (`MaxMinSDH.lean`, `MaxMinCounterexample.lean`, `UniformRule.lean`, `BalancedCRS.lean`).

### What fails: SDH's own selection

**Counterexample** (`maxMin_sdh_counterexample`). Initiators $i_0, i_1$, one responder $j$, values known, all caps and costs 1.
- $(i_0, j)$: $i_0$ gains 1 and $j$ gains 10, so the net weight is 11.
- $(i_1, j)$: $i_1$ gains 2 and $j$ gains 1, so the net weight is 3.

The max-min plan is forced: $x_0 \ge \theta$, $2x_1 \ge \theta$ and $x_0 + x_1 \le 1$ give $\theta^* = 2/3$, with $x_0 = 2/3$ and $x_1 = 1/3$. SDH queries each pair with probability $x$, and when it finds both it keeps $(i_0, j)$. So, for any tie-breaking,
$$\mathbb E[u_{i_1}] = 2\cdot\tfrac13\cdot\tfrac13 = \tfrac29 = \tfrac{\theta^*}{3} < c_1^2\,\theta^* \approx 0.40\,\theta^*.$$

### What holds: selection that protects every pair

**MM-SDH**, as formalized:
1. **Plan:** solve the max-min LP of §2.
2. **Screen and thin** as SDH's analysis does. A found pair in combination $c$ is kept with probability $x_{e,c}/(\tau_e\pi_{e,c})$, so it becomes a *candidate* with probability exactly $x_{e,c}$.
3. **Select in two stages with rules.** Each responder keeps a random capped subset of its candidates, then each initiator does the same with what reaches it. A rule sees only its user's candidate set and its own coins.

Utilities are additive within caps, which covers additive users and top-$k$ users with cap $\le k$.

A rule is **$\gamma$-balanced** if, when candidates arrive independently, it keeps each candidate with probability at least $\gamma$ times that candidate's arrival probability.

**Theorem MM.**
- **(a) The LP bounds the benchmark:** $\mathrm{OPT}_{\min} \le \theta^*$. Here $\mathrm{OPT}_{\min}$ is the best floor $\min_\ell \mathbb E[u_\ell]$ of any full-information policy, randomized or not, that picks capped sets of acceptable pairs. (`floor_le_maxMin`)
- **(b) Composition:** if every stage-1 rule is $\gamma_1$-balanced and every stage-2 rule is $\gamma_2$-balanced, then every user gets $\mathbb E[u_\ell] \ge \gamma_1\gamma_2\,\mathrm{lpSurplus}_\ell(x)$. (`mmUtilI_ge`, `mmUtilJ_ge`)
- **(c) Random order:** keeping a uniformly random $\min(K_\ell, |A|)$ of the candidates is $\tfrac12$-balanced. So $\min_\ell \mathbb E[u_\ell] \ge \theta^*/4 \ge \mathrm{OPT}_{\min}/4$. (`mmsdh_quarter_maxMin`)
- **(d) The note's constant:** $c_K$-balanced rules exist. With them, $\min_\ell \mathbb E[u_\ell] \ge c_K^2\,\theta^* \ge c_K^2\,\mathrm{OPT}_{\min}$ for $K$ at most every cap. (`mmsdh_cK_maxMin`)
- **(e) Truthfulness:** sincere swiping stays DSIC. Each user sees only a capped set of acceptable partners, and `sdh_dsic` covers every such set.

**Proof sketch.**
- **(a)** Set $x_{e,c} = \Pr[\text{the policy matches } e \text{ in combination } c]$. Then $x \le \pi$, $x$ vanishes on unacceptable combinations, and every cap holds in expectation. By linearity, $\mathrm{lpSurplus}_\ell(x) = \mathbb E[u_\ell]$ for every user.
- **(b)** Fix a pair $e = (i, j)$. Rules see only candidate sets, and different responders use disjoint candidates and coins. So the chance that $e$ is selected in combination $c$ factors exactly as $x_{e,c}\,\kappa_1\kappa_2$:
  - $\kappa_1$ is the chance $j$'s rule keeps $i$, given that $i$ is a candidate;
  - $\kappa_2$ is the chance $i$'s rule keeps $j$, given that stage 1 passed $j$ on. What reaches $i$ comes from different responders, so it arrives independently.
  
  Balance gives $\kappa_1 \ge \gamma_1$ and $\kappa_2 \ge \gamma_2$. Multiply by $\ell$'s surplus, which is $\ge 0$ on acceptable combinations, and sum over $\ell$'s pairs.
- **(c)** A candidate competing with $D$ others is kept with probability $\min(1, K/(1+D))$. For natural $d$ and $K \ge 1$, $\min(1, K/(1+d)) \ge 1 - d/(2K)$. Since $\mathbb E[D] \le K$, the keep probability is at least $\tfrac12$.
- **(d)** Chekuri–Vondrák–Zenklusen. A designer picks a rule, and an adversary picks weights $w \ge 0$.
  - The payoff $\sum_e w_e(\Pr[e \text{ kept}] - c_K y_e)$ is linear in $w$ and affine in the rule, so Sion's minimax theorem gives a saddle point.
  - Against any fixed $w$, keeping the $K$ heaviest candidates earns $\mathbb E[\mathrm{top}_K\,w(A)] \ge c_K\sum_e w_e y_e$. This is the $c_K$ correlation gap, R1's lemma in [[Match Quality in the Dating Heuristic Framework]].
  - So the saddle point's rule is $c_K$-balanced.

**Constants.** The $\tfrac14$ for random order is a lower bound, not tight. For comparison, $c_2^2 \approx 0.53$. The $c_K$-balanced rules exist but are not explicit; they depend on the plan's candidate probabilities, never on values or swipes.

### Price of fairness, redone

The table in §4 maximizes only $\theta$, so the solver returns an arbitrary plan among those that reach $\theta^*$. `data/scripts/maxmin_check_v2.py` breaks the tie by total welfare:
- $\theta^* = 0.0909$ is kept, with total welfare $1.596$ instead of $0.595$.
- The price of fairness is $1.61$, not $4.32$.
- A floor of $0.75\,\theta^*$ costs under 5% of utilitarian welfare.

On the speed-dating data, `data/scripts/run_algorithm_benchmark_v2.py` gives:
- **Plans:** the tie-broken max-min plan gives up only 0.6–1.8% of planned total welfare.
- **Max-weight selection:** it undoes the max-min plan. In wave 2, one user got 0.22 of their plan.
- **Random order, then filling spare slots:** the worst-off user is better off than under SDH in every wave, at a cost of 5–7% of total welfare.
