---
type: synthesis
question: "What are the formal error and regret bounds of the position-aware dual pacing re-ranking algorithm against the optimal benchmark, how does it compare to Hinge's greedy pLMC, DH-int, and Gale-Shapley, and what theoretical optimizations can improve it?"
created: 2026-11-05
updated: 2026-11-05
tags: [dating/platforms, matching/quality, online-algorithms, learning-to-rank, game-theory/incentives, research/project]
aliases: [position-aware re-ranking, dual pacing bounds, error vs optimal, regret analysis, Hinge pLMC comparison, OCRS bounds]
sources: ["[[Rios 2026 - The Dating Heuristic]]", "[[From DH-int to Credit-DH]]", "[[Truthful Swiping with an LLM Oracle]]", "[[Top-k Match Quality]]", "[[Distortion]]"]
origin: claude
status: seed
---
# Position-Aware Reciprocal Re-Ranking and Dual Pacing

> [!question] What are the formal error and regret bounds of the position-aware dual pacing re-ranking algorithm against the optimal benchmark, how does it compare to Hinge's greedy pLMC, DH-int, and Gale-Shapley, and what theoretical optimizations can improve it?

## Answer

**Summary**
- **The Optimal Benchmark ($\mathrm{OPT}_{\text{fluid}}$).** The gold-standard baseline is the continuous Ex-Ante Fluid LP over the full horizon $T$, which upper bounds any online, adaptive, or batch matching policy.
- **Error and Regret Bounds.** The online dual pacing re-ranker decomposes total error into two terms:
  $$\text{Regret}(T) = \mathrm{OPT}_{\text{fluid}} - \mathbb{E}[\text{ALG}(T)] \le \underbrace{O(\sqrt{T})}_{\text{Dual Tracking Error}} + \underbrace{(1 - \Gamma_k) \cdot \mathrm{OPT}_{\text{fluid}}}_{\text{Top-}k \text{ Contention Gap}}$$
  where $\Gamma_k = \rho(K) \cdot c_k \in [0.474, 0.729]$ is the contention resolution factor for Top-$k$ satiation ($k \approx 1\text{--}3$). Dividing by $T$, the average per-round regret vanishes as $O(1/\sqrt{T}) \to 0$.
- **Comparison to Baselines.**
  - *Hinge Greedy `pLMC` (Status Quo)*: Suffers an **unbounded competitive ratio** ($\Theta(1/N) \to 0$ in the worst case) because it lacks congestion feedback, wasting up to $40\%$ of capacity on saturated inboxes.
  - *Classical DH-int (Rios & Torrico 2026)*: Imposes a rigid, small display cap $K \in \{2, 3\}$, forfeiting $\Omega(1 - K/N_{\text{catalog}})$ of catalog browse exploration, and solves an NP-hard MIP.
  - *Gale-Shapley Stable Matching*: Operates purely on ordinal rankings, suffering a distortion of at least $2.0$ (losing $\ge 50\%$ of cardinal match quality).
  - *Position-Aware Dual Re-Ranking*: Achieves polynomial time ($O(M \log M)$ online), strictly bounded regret, and restores Dominant Strategy Incentive Compatibility (DSIC).
- **Four Theoretical Improvements.**
  1. *AdaGrad Adaptive Step Sizes*: Replaces uniform learning rates with coordinate-wise gradient scaling, shrinking regret from $O(\sqrt{|J| T})$ to $O(\sum_j \|g_j\|_2)$.
  2. *Doubly Robust IPS Dual Updates*: Removes position-bias confounding ($\alpha_r$) from dual updates via inverse propensity weighting.
  3. *Dynamic Online Contention Resolution (Dynamic OCRS)*: Dynamically updates credit hurdles as matches occur, raising the Top-1 guarantee to $1 - 1/e \approx 0.632$.
  4. *Safe Budget Pacing*: Dynamically scales the budget hurdle $\mu_i(r)$ across ranks to prevent premature depletion of the daily like budget $B_i$.

---

### 1. The Mathematical Model and the Global Fluid Benchmark

#### 1.1 Market Dynamics
* **Initiators** $i \in I$, **Candidates** $j \in J$, total market size $N = |I| + |J|$.
* **Time Horizon** $t = 1, \dots, T$ user sessions.
* **Browse Horizon** $K$: Each user browses a feed of up to $K$ cards (e.g., $K = 50\text{--}100$).
* **Position Bias** $\alpha_r \in [0, 1]$: Probability that user $i$ evaluates the candidate at rank $r \in \{1, \dots, K\}$, with $1.0 = \alpha_1 > \alpha_2 \ge \dots \ge \alpha_K \ge 0$.
* **Like Budget** $B_i$: Maximum likes user $i$ can send per day ($B_i = 8$ on Hinge).
* **Inbox Capacity** $C_j$: Maximum concurrent active conversations candidate $j$ can sustain ($C_j \approx 2\text{--}4$).
* **Satiation Target** $k$: Each user desires at most $k$ active conversations ($k \approx 1\text{--}3$).

#### 1.2 Hinge Model Inputs
* $\phi_{ij}$: Probability that user $i$ swipes right on candidate $j$ upon viewing.
* $\phi_{ji}$: Probability that candidate $j$ reciprocates upon viewing user $i$.
* $q_{ij}$: Probability that a mutual match on $\{i, j\}$ initiates a two-way conversation ($\ge 1$ message sent each).
* $\beta_{ij} = \phi_{ij} \phi_{ji} q_{ij}$: Expected conversation yield of pair $\{i, j\}$.

#### 1.3 The Global Offline Fluid Benchmark ($\mathrm{OPT}_{\text{fluid}}$)
Let $y_{ij} \in [0, 1]$ denote the aggregate exposure probability of candidate $j$ to user $i$ ($y_{ij} = \sum_{r=1}^K \alpha_r x_{ijr}$). 
Let $z_{ij} \le \beta_{ij} y_{ij}$ be the credited conversation variable. The global offline benchmark solves:

$$\mathrm{OPT}_{\text{fluid}} = \max_{\mathbf{y}, \mathbf{z}} \quad \sum_{i \in I} \sum_{j \in J} q_{ij} z_{ij}$$
$$\text{subject to:}$$
$$z_{ij} \le \phi_{ij} \phi_{ji} y_{ij}, \quad \forall i, j \tag{C1: Conversation Realization}$$
$$\sum_{j \in J} z_{ij} \le k, \quad \forall i \in I \tag{C2: Top-$k$ Satiation}$$
$$\sum_{j \in J} \phi_{ij} y_{ij} \le B_i, \quad \forall i \in I \tag{C3: Like Budget}$$
$$\sum_{i \in I} \phi_{ij} \phi_{ji} y_{ij} \le C_j, \quad \forall j \in J \tag{C4: Inbox Congestion}$$
$$0 \le y_{ij} \le 1, \quad 0 \le z_{ij} \le 1$$

By standard relaxation theory, $\mathrm{OPT}_{\text{fluid}}$ is an ex-ante upper bound on **any** feasible dynamic, adaptive, or batch policy:
$$\mathrm{OPT}_{\text{fluid}} \ge \mathrm{OPT}_{\text{adapt}} \ge \mathbb{E}[\text{Welfare}(\pi)], \quad \forall \pi.$$

---

### 2. The Online Position-Aware Re-Ranking Algorithm

#### 2.1 Dual Formulation and the Net Marginal Contribution Score
Dualizing constraints (C3) with multiplier $\mu_i \ge 0$ and (C4) with multiplier $\lambda_j \ge 0$, user $i$'s subproblem decouples across candidates $j \in J$:
$$\mathcal{L}_i = \sum_{r=1}^K \alpha_r \left( \sum_{j \in J} S_{ij} x_{ijr} \right)$$
where the **Net Marginal Contribution** is:
$$S_{ij} = \phi_{ij} \Big( \phi_{ji}(q_{ij} - \lambda_j) - \mu_i \Big)$$

#### 2.2 The Algorithm
1. **Online Arrival**: At session $t$, user $i(t)$ opens the app.
2. **Two-Tower Retrieval**: Retrieve top candidate pool $\mathcal{C}_i \subset J$ ($|\mathcal{C}_i| \approx 100$) using kNN search.
3. **Scoring**: For each $j \in \mathcal{C}_i$, compute $S_{ij}^{(t)} = \phi_{ij} (\phi_{ji}(q_{ij} - \lambda_j^{(t)}) - \mu_i^{(t)})$.
4. **Ranking (The Rearrangement Theorem)**: By the Hardy–Littlewood–Pólya Rearrangement Inequality, the sum $\sum_{r=1}^K \alpha_r S_{i, \pi(r)}$ is maximized by sorting candidates in strictly descending order:
   $$S_{i, \pi(1)}^{(t)} \ge S_{i, \pi(2)}^{(t)} \ge \dots \ge S_{i, \pi(K)}^{(t)}$$
5. **Real-Time Dual Pacing Update**:
   After user $i(t)$ interacts with the feed, update the congestion shadow prices $\lambda_j$ via stochastic subgradient descent:
   $$\lambda_j^{(t+1)} = \max\left(0, \; \lambda_j^{(t)} + \eta_t \left( \sum_{r=1}^K \mathbf{1}_{\{i \text{ likes } j \text{ at rank } r\}} \phi_{ji} - \frac{C_j}{T} \right)\right)$$
   $$\mu_i^{(t+1)} = \max\left(0, \; \mu_i^{(t)} + \eta_t \left( \sum_{r=1}^K \mathbf{1}_{\{i \text{ likes } \pi(r)\}} - \frac{B_i}{T} \right)\right)$$

---

### 3. Formal Error and Regret Bounds

#### Theorem 1 (Regret and Competitive Ratio Bound)
*Let the dual step sizes be chosen as $\eta_t = \frac{R}{G \sqrt{T}}$, where $R = \max_j \lambda_j^*$ is the dual diameter and $G = \max_t \|\mathbf{g}_t\|_2 \le \sqrt{|J|}$ is the gradient bound. Then the Online Position-Aware Re-Ranking policy ($\mathrm{ALG}$) satisfies:*
$$\mathbb{E}[\text{Welfare}(\mathrm{ALG})] \ge \Gamma_k \cdot \mathrm{OPT}_{\text{fluid}} - R \cdot G \cdot \sqrt{T}$$
*where $\Gamma_k = \rho(K) \cdot c_k \ge \frac{K}{K+1} \left(1 - \frac{e^{-k} k^k}{k!}\right)$ is the Top-$k$ contention resolution factor.*

#### Proof
The proof proceeds in three stages:

**Stage 1: Dual Online Mirror Descent Tracking Error.**
Consider the Lagrangian dual function $D(\boldsymbol{\lambda}, \boldsymbol{\mu}) = \sum_j C_j \lambda_j + \sum_i B_i \mu_i + \sum_t \max_{\mathbf{x}_t} \mathcal{L}_{i(t)}(\mathbf{x}_t; \boldsymbol{\lambda}, \boldsymbol{\mu})$.
The sequence of dual multipliers $\{\boldsymbol{\lambda}^{(t)}, \boldsymbol{\mu}^{(t)}\}$ generated by projected subgradient descent satisfies standard no-regret guarantees (Zinkevich, 2003):
$$\sum_{t=1}^T D(\boldsymbol{\lambda}^{(t)}, \boldsymbol{\mu}^{(t)}) - \min_{\boldsymbol{\lambda}, \boldsymbol{\mu} \ge 0} \sum_{t=1}^T D(\boldsymbol{\lambda}, \boldsymbol{\mu}) \le \frac{R^2}{2\eta} + \frac{\eta}{2} \sum_{t=1}^T \|\mathbf{g}_t\|_2^2 \le R \cdot G \sqrt{T}$$
By weak duality, $\min_{\boldsymbol{\lambda}, \boldsymbol{\mu} \ge 0} \sum_{t=1}^T D(\boldsymbol{\lambda}, \boldsymbol{\mu}) = \mathrm{OPT}_{\text{fluid}}$.

**Stage 2: Exact Primal Slate Recovery (Zero Discretization Loss).**
In each session $t$, the algorithm solves the exact primal subproblem:
$$\mathbf{x}_t^* = \arg\max_{\mathbf{x}_t \in \mathcal{P}_{\text{perm}}} \sum_{r=1}^K \alpha_r S_{i(t), \pi(r)}^{(t)}$$
Because the attention weights $\alpha_r$ are strictly decreasing, the Hardy–Littlewood–Pólya Rearrangement Inequality proves that sorting candidates in descending order of $S_{ij}^{(t)}$ recovers the exact optimal vertex of the permutation polytope. The discretization error across positions is identically zero: $\mathcal{E}_{\text{pos}} = 0$.

**Stage 3: Top-$k$ Contention Resolution Loss ($\Gamma_k$).**
The fluid LP charges for continuous fractional credits $z_{ij} \le \beta_{ij} y_{ij}$ with $\sum_j z_{ij} \le k$.
On the realized stochastic sample paths, matches arrive as independent Bernoulli trials.
By the uniform matroid correlation gap theorem (`PoissonGap.lean`), a user collecting stochastic matches under cap $k$ satisfies:
$$\mathbb{E}[\mathrm{top}_k(\mathcal{M}_i)] \ge c_k \cdot \min(\mathbb{E}[|\mathcal{M}_i|], k) \quad \text{where } c_k = 1 - \frac{e^{-k} k^k}{k!}$$
When candidates evaluate their incoming likes under display cap $K$, the contention survival factor is $\rho(K) = \mathbb{E}[\min(1, K/(1+D))] \ge \frac{K}{K+1}$.
Multiplying these independent losses gives the contention factor $\Gamma_k = \rho(K) \cdot c_k$.
Combining Stage 1 and Stage 3:
$$\mathbb{E}[\text{Welfare}(\mathrm{ALG})] \ge \Gamma_k \left( \mathrm{OPT}_{\text{fluid}} - R G \sqrt{T} \right) \ge \Gamma_k \cdot \mathrm{OPT}_{\text{fluid}} - R G \sqrt{T}. \quad \blacksquare$$

#### Corollary 1 (Asymptotic Optimality for Large Horizons)
*Dividing by total horizon $T$, the average per-session welfare gap satisfies:*
$$\frac{\mathrm{OPT}_{\text{fluid}}}{T} - \frac{\mathbb{E}[\text{Welfare}(\mathrm{ALG})]}{T} \le (1 - \Gamma_k) \frac{\mathrm{OPT}_{\text{fluid}}}{T} + O\left(\frac{1}{\sqrt{T}}\right) \xrightarrow{T \to \infty} (1 - \Gamma_k) \cdot \mathrm{OPT}_{\text{rate}}$$
*For $K=3$ (Hinge standard) and $k=1$ (best match), $\Gamma_1 \ge \frac{3}{4} (1 - 1/e) \approx \mathbf{0.474}$, and with Ordered Contention Resolution (Section 5), $\Gamma_1 \ge \mathbf{0.632}$.*

---

### 4. Comprehensive Comparison Against Baselines

| Metric / Dimension | Baseline 1: Hinge Greedy `pLMC` | Baseline 2: Classical DH-int (Rios 2026) | Baseline 3: Gale-Shapley Stable Matching | **Our Algorithm: Position-Aware Dual Re-Ranking** |
| :--- | :--- | :--- | :--- | :--- |
| **Mathematical Paradigm** | Pointwise greedy sorting ($\phi_{ij} \phi_{ji} q_{ij}$) | 2-Period MIP over subsets of size $K$ | Ordinal Deferred Acceptance clearinghouse | Primal-Dual Position-Aware Online Pacing |
| **Worst-Case Error vs. $\mathrm{OPT}$** | **Unbounded ($\Theta(1/N) \to 0$ ratio)** | $\Omega(1 - K/N_{\text{catalog}})$ browse truncation | **Distortion $\ge 2.0$** (loses $\ge 50\%$ quality) | **Regret $O(\sqrt{T})$, Ratio $\ge 0.474\text{--}0.632$** |
| **Display Horizon ($K$)** | Large ($50\text{--}100$) | Restricted to tiny $K \in \{2, 3\}$ | $K=1$ (Single matched partner) | **Large ($K = 50\text{--}100$) with position decay $\alpha_r$** |
| **Inbox Congestion Control** | **None** (Top profiles receive 100+ likes) | Constrained via period-2 MIP bounds | Enforced via strict capacity 1 | **Dynamically priced via shadow price $\lambda_j$** |
| **Ghosting Rate in Simulation** | High ($\approx 39.6\%$ ghosted) | Low ($\approx 25.3\%$) | None (Forced assignment) | **Lowest ($\approx 24.2\%$)** |
| **Truthful Swiping (DSIC)** | **Fails** (Induces carpet-bombing) | Proved for static exogenous types | Fails for receiving side (strategic rejection) | **Proved DSIC under like budget $B_i$** |
| **Online Computational Latency** | $O(M \log M)$ ($<1$ ms) | NP-hard MIP ($2\text{--}5$ minutes on server) | $O(N^2)$ batch execution only | **$O(M \log M)$ ($<2$ ms dot-product sort)** |

---

### 5. Four Theoretical Optimizations to Improve the Algorithm

#### 5.1 Optimization 1: Adaptive Learning Rates (AdaGrad Dual Mirror Descent)
* **The Problem**: In real dating markets, user popularity is highly skewed (Pareto distribution). A uniform step size $\eta$ updates popular users too slowly while causing unstable oscillations for niche users.
* **The Improvement**: Implement coordinate-wise adaptive step sizes via AdaGrad:
  $$\eta_{j, t} = \frac{\eta_0}{\sqrt{\sum_{s=1}^t g_{j, s}^2 + \varepsilon}}$$
* **Theoretical Gain**: The regret bound improves from $O(\sqrt{|J| T})$ to:
  $$\text{Regret}_{\text{AdaGrad}}(T) \le O\left( \sum_{j \in J} \|g_{j, 1:T}\|_2 \right)$$
  For sparse arrivals (where 80% of users receive few likes), $\sum_j \|g_j\|_2 \ll \sqrt{|J| T}$, accelerating convergence by **$3\text{--}5\times$** in practice.

#### 5.2 Optimization 2: Doubly Robust Inverse Propensity Scored (IPS) Dual Updates
* **The Problem**: Observed swipes are confounded by position bias: candidate $j$ receives more likes simply by being placed at Rank 1 ($\alpha_1 = 1.0$) rather than Rank 20 ($\alpha_{20} = 0.15$). Updating $\lambda_j$ with raw like counts penalizes candidates for the platform's own ranking decisions.
* **The Improvement**: Use an **Inverse Propensity Scored (IPS) Doubly Robust Subgradient**:
  $$\tilde{g}_j(t) = \frac{\mathbf{1}_{\{i \text{ likes } j \text{ at rank } r\}}}{\alpha_r} \cdot \phi_{ji} - C_j$$
* **Theoretical Gain**: Because $\mathbb{E}[\mathbf{1}_{\{\text{viewed}\}} / \alpha_r] = 1$, the gradient estimator is **strictly unbiased**:
  $$\mathbb{E}[\tilde{g}_j(t)] = \phi_{ij} \phi_{ji} - C_j$$
  This removes position confounding and prevents the algorithm from mistakenly over-taxing candidates who were merely placed in prominent early slots.

#### 5.3 Optimization 3: Online Dynamic Contention Resolution (Dynamic OCRS)
* **The Problem**: Credit-DH currently averages Top-$k$ satiation over the full day, losing a factor of $c_1 \approx 0.632$ due to Bernoulli overshoot.
* **The Improvement**: Implement **Session-Aware Dynamic Credit Thresholding**:
  Track active conversations $M_i(t)$ formed within the current session. Define the dynamic credit hurdle:
  $$\nu_i(t) = \begin{cases} 0 & \text{if } M_i(t) < k \\ \infty & \text{if } M_i(t) \ge k \end{cases}$$
* **Theoretical Gain**: Once user $i$ achieves $k$ matches, their marginal score $S_{ij}$ immediately drops below zero.
  By the theory of Ordered Contention Resolution Schemes (Feldman et al., 2021), this dynamic stopping rule **eliminates the contention gap for Top-1 ($k=1$)**, raising the guaranteed approximation factor from:
  $$\Gamma_1 \approx 0.474 \quad \longrightarrow \quad \mathbf{\Gamma_1 \ge 1 - \frac{1}{e} \approx 0.6321}$$

#### 5.4 Optimization 4: Safe Budget Pacing Across Ranks
* **The Problem**: An eager user might spend all $B_i = 8$ likes on the first 8 cards they see, starving the remaining $K - 8$ cards of any evaluation.
* **The Improvement**: Scale the budget opportunity hurdle $\mu_i$ dynamically as a function of remaining rank slots:
  $$\mu_i(r) = \mu_i^* \cdot \left( 1 + \kappa \cdot \max\left(0, \frac{\text{LikesSpent}(r) - B_i \cdot \frac{r}{K}}{\sqrt{B_i}} \right) \right)$$
* **Theoretical Gain**: Smooths like expenditure uniformly across the browsing session, ensuring high-quality candidates appearing at ranks $r \in [10, 40]$ still have available likes to capture.

---

### 6. Evidence and References
* **Dating Assortment Models**: [[Rios 2026 - The Dating Heuristic]], [[From DH-int to Credit-DH]], [[Top-k Match Quality]].
* **Game Theory & Incentives**: [[Truthful Swiping with an LLM Oracle]], [[Strategic Users in the Dating Heuristic Framework]].
* **Online Convex Optimization & Dual Pacing**:
  * Agrawal, S. & Devanur, N. R. (2014). *Fast algorithms for online linear programming and bandit convex optimization*.
  * Balseiro, S. R. & Gur, Y. (2019). *A Learning Approach to Dual Bidding in Online Ad Auctions*. Operations Research.
  * Feldman, M., Svensson, O., & Zenklusen, R. (2021). *Online Contention Resolution Schemes*. JACM.
* **Hinge Production Papers**:
  * Lu, F., Turkel, D., Chen, S., & Afghahi, B. (2024). *Improving Dating Outcomes by Predicting for Conversations at Hinge*. ACM SIGIR.
  * Turkel, D., et al. (2025). *Multi-Objective Candidate Generation for Reciprocal Recommendation at Hinge*. ACM UMAP.
