---
type: synthesis
question: "Can the dating heuristic framework be formulated to maximize the minimum user's expected welfare (max-min / Rawlsian egalitarianism), how does it differ from utilitarian welfare, and does it guarantee truthful swiping?"
created: 2026-10-27
updated: 2026-10-27
tags: [dating/platforms, matching/quality, fairness, game-theory/incentives, research/project]
aliases: [max-min welfare, egalitarian matching, price of fairness, Rawlsian matching, max-min SDH, leximin dating]
sources: ["[[Rios 2026 - The Dating Heuristic]]", "[[Truthful Swiping with an LLM Oracle]]", "[[From DH-int to Credit-DH]]"]
origin: claude
status: seed
---
# Max-Min Match Quality and Egalitarian Matching

> [!question] Can the dating heuristic framework be formulated to maximize the minimum user's expected welfare (max-min / Rawlsian egalitarianism), how does it differ from utilitarian welfare, and does it guarantee truthful swiping?

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
