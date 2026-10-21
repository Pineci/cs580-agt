---
type: synthesis
question: "How do DH-int, quality-weighted DH-int and credit-DH differ, and why does credit-DH keep a constant-factor guarantee for top-k match quality?"
created: 2026-10-21
updated: 2026-10-21
tags: [dating/platforms, matching/quality, research/project]
aliases: [DH variants compared, DH-int vs credit-DH, credit-DH walkthrough]
sources: ["[[Rios 2026 - The Dating Heuristic]]"]
origin: claude
status: seed
---
# From DH-int to Credit-DH

> [!question] How do DH-int, quality-weighted DH-int and credit-DH differ, and why does credit-DH keep a constant-factor guarantee for top-k match quality?

> [!note] Walkthrough, no new results
> Written 2026-10-21 for readers new to the project. It puts the programs from [[Dating Heuristic]], [[Match Quality in the Dating Heuristic Framework]] and [[Top-k Match Quality]] side by side. Proofs and evidence live in those notes. Credit-DH's guarantees are informal and not in Lean.

## Answer

**Summary**
- All three versions solve a MIP with the same decisions and constraints, show its period-1 part, then play period 2. They differ in what the objective pays for and in the period-2 rule.
- **DH-int** counts matches. It gets $c_K\ge1-1/e$ of the best adaptive policy ([[Rios 2026 - The Dating Heuristic]], sharpened to $c_K$ by R1).
- **Quality-weighted DH-int** pays each user their value for every match. It gets $c_K$ for additive quality (R2), but only $\Theta(k/K)$ for top-$k$.
- **Credit-DH** pays each user only for their $k$ best planned matches, and responders follow the plan by random marking. It gets $\rho\,c_k\ge c_k/2$ for top-$k$ (T1), so at least $0.316$ for top-1 whatever the display caps.

### The model in brief
From [[Rios 2026 - The Dating Heuristic]], Section 4:
- **Displays.** Two sides $I,J$. Each period the platform shows user $\ell$ at most $K_\ell$ profiles from $\ell$'s potentials.
- **Likes.** Shown $\ell'$ in period $t$, $\ell$ likes $\ell'$ with probability $\phi^t_{\ell\ell'}$, independently. The platform knows $\phi$.
- **Backlog and matches.** A like waits in the receiver's backlog. A pair matches once both have liked each other:
  - *sequential:* $\ell$ initiates in period 1 and likes $\ell'$; $\ell'$ is shown $\ell$ from the backlog in period 2 and likes back;
  - *mutual view:* both see each other in period 1 and both like, with probability $\beta_e=\phi^1_{\ell\ell'}\phi^1_{\ell'\ell}$.
- **Two periods.** Backlogs start empty. Period 2 has only backlog responses, with no mutual views.
- **Designs.** One- or two-directional, with mutual views in period 1 allowed or not. Every result holds for each design.
- **Benchmark.** The best adaptive policy for the same design. It sees period-1 outcomes before acting in period 2, but does not know likes in advance.

The project adds values $q_{\ell\ell'}\ge0$ ($\ell$'s value for $\ell'$) and three objectives ([[Match Quality in the Dating Heuristic Framework]]):
- *count* $C=\mathbb E\,\lvert\mathcal M\rvert$;
- *additive quality* $Q=\mathbb E\sum_{e\in\mathcal M}(q_{\ell\ell'}+q_{\ell'\ell})$;
- *top-$k$ quality* $U_k=\mathbb E\sum_\ell\mathrm{top}_k\{q_{\ell\ell'}:\ell'\in M_\ell\}$.

A user whose matches are worth 0.9, 0.5 and 0.2 to them contributes 1.6 to $Q$, 1.4 to $U_2$ and 0.9 to $U_1$. A user has at most $2K_\ell$ matches, so $U_k=Q$ once $k\ge2K_\ell$ for every user.

### Notation
| Symbol | Meaning |
| --- | --- |
| $K_\ell$, $K$ | display cap per period; $K=\min_\ell K_\ell$ |
| $\phi^1_{\ell\ell'}$, $\phi^2_{\ell\ell'}$ | probability $\ell$ likes $\ell'$ when shown in period 1, 2 |
| $\beta_e$ | $\phi^1_{\ell\ell'}\phi^1_{\ell'\ell}$, match probability of a mutual view |
| $x_{\ell\ell'}\in\{0,1\}$ | $\ell$ initiates toward $\ell'$ in period 1 (paper's $x^1$) |
| $w_e\in\{0,1\}$ | mutual view of pair $e$ in period 1 (paper's $w^1$) |
| $y_{\ell\ell'}\in[0,1]$ | planned probability $\ell$ shows $\ell'$ from its backlog in period 2 (paper's $x^2$) |
| $p_e$ | planned match probability, $\beta_ew_e+\phi^2_{\ell\ell'}y_{\ell\ell'}+\phi^2_{\ell'\ell}y_{\ell'\ell}$ |
| $\bar q_e$ | $q_{\ell\ell'}+q_{\ell'\ell}$ ([[Match Quality with Queried Values]] calls it $w_e$) |
| $z_{\ell\ell'}$ | credit: planned probability that $\ell'$ matches $\ell$ and is among $\ell$'s $k$ best ([[Top-k Match Quality]] writes $c_{\ell\ell'}$) |
| $c_K$ | $1-e^{-K}K^K/K!$: $c_1=0.632$, $c_2=0.729$, $c_3=0.776$ |
| $\rho$ | $\min\mathbb E[\min(1,K_\ell/(1+D))]$, $D$ = other marked members of the backlog; $\ge1/2$, and $\ge K/(K+1)$ for $K\le2$ |

### The three programs
**DH-int** (count), the two-period form of the paper's program:
$$
\begin{array}{llll}
\max & \sum_e\beta_e\,w_e+\sum_\ell\sum_{\ell'}\phi^2_{\ell\ell'}\,y_{\ell\ell'} & & \\
\text{s.t.} & \sum_{\ell'}x_{\ell\ell'}+\sum_{e\ni\ell}w_e\le K_\ell & \forall\ell & \text{(P1) period-1 cap}\\
& x_{\ell\ell'}+x_{\ell'\ell}+w_e\le1 & \forall e & \text{(P2) one way per pair}\\
& 0\le y_{\ell\ell'}\le\phi^1_{\ell'\ell}\,x_{\ell'\ell} & \forall\ell,\ell' & \text{(P3) respond only to a like}\\
& \sum_{\ell'}y_{\ell\ell'}\le K_\ell & \forall\ell & \text{(P4) period-2 cap}\\
& x,w\in\{0,1\}\text{, allowed by the design} & & \text{(P5)}
\end{array}
$$
Period 2: each responder shows the $K_\ell$ backlog members with the largest $\phi^2_{\ell\ell'}$.

**Quality-weighted DH-int** (R2). Same constraints (P1)–(P5); the objective weights each planned match by $\bar q$:
$$\max\ \sum_e\beta_e\,\bar q_e\,w_e+\sum_\ell\sum_{\ell'}\phi^2_{\ell\ell'}\,\bar q_{\ell\ell'}\,y_{\ell\ell'}.$$
Period 2: show the $K_\ell$ largest $\phi^2_{\ell\ell'}\bar q_{\ell\ell'}$.

**Credit-DH** (T1). Same constraints (P1)–(P5), plus credits:
$$
\begin{array}{llll}
\max & \sum_\ell\sum_{\ell'}q_{\ell\ell'}\,z_{\ell\ell'} & & \\
\text{s.t.} & \text{(P1)–(P5)} & & \\
& p_e=\beta_ew_e+\phi^2_{\ell\ell'}y_{\ell\ell'}+\phi^2_{\ell'\ell}y_{\ell'\ell} & \forall e & \text{(C1) match probability}\\
& 0\le z_{\ell\ell'}\le p_e & \forall\ell,\ e\ni\ell & \text{(C2) credit}\le\text{match probability}\\
& \sum_{\ell'}z_{\ell\ell'}\le k & \forall\ell & \text{(C3) }k\text{ credits per user}
\end{array}
$$
Credits are directional: $z_{\ell\ell'}$ and $z_{\ell'\ell}$ share the cap $p_e$. Period 2, for each responder $\ell$:
1. Mark each backlog member $\ell'$ independently with probability $y^*_{\ell\ell'}/\phi^1_{\ell'\ell}$, so it ends up marked with probability exactly $y^*_{\ell\ell'}$.
2. Show the first $K_\ell$ marked members in uniformly random order.
3. Optionally fill spare slots with unmarked members; extra matches never lower a top-$k$.

**The ladder.** The objectives are, in order,
$$\sum_ep_e\ \longrightarrow\ \sum_\ell\sum_{\ell'}q_{\ell\ell'}\,p_{\ell\ell'}\ \longrightarrow\ \max_{0\le z\le p,\ \sum_{\ell'}z_{\ell\ell'}\le k}\ \sum_\ell\sum_{\ell'}q_{\ell\ell'}\,z_{\ell\ell'}.$$
That is: count every match; pay each user for every match; pay each user only for their $k$ best. When $k\ge2K_\ell$ for every user, credits never bind and credit-DH's program is weighted DH-int's.

**What credits compute.** For a fixed plan, the best credits fill each user's highest values first: the *fractional top-$k$* of their match probabilities. Example, $k=1$: partner A (value 1) with probability 0.6, partner B (value 0.8) with probability 0.7.
- Credit-DH counts $0.6+0.4\cdot0.8=0.92$.
- Weighted DH-int counts $0.6+0.7\cdot0.8=1.16$.
- With independent matches the true expected best is $0.6+0.4\cdot0.7\cdot0.8=0.824$.

Both overcount. With independent matches the true value is always at least $c_1=0.632$ of credit-DH's count (here 0.896). Weighted DH-int's overcount has no such bound: it grows with the number of matches a user can collect.

### Side by side
| | DH-int | Weighted DH-int | Credit-DH |
| --- | --- | --- | --- |
| Pays for | $\sum_ep_e$ | $\sum q\,p$ | $\sum q\,z$, $z\le p$, $k$ credits |
| Period 2 | top $K_\ell$ by $\phi^2$ | top $K_\ell$ by $\phi^2\bar q$ | random marking, random order |
| On $C$ | $c_K$, tight | none in general | not analyzed |
| On $Q$ | none (R3) | $c_K$ (R2) | not analyzed |
| On $U_k$ | none | $\Theta(k/K)$ | $\rho\,c_k\ge c_k/2$ |
| Loss in proof | responder overflow, $c_K$ | responder overflow, $c_K$ | random cut $\rho$; user's top-$k$, $c_k$ |
| Status | in Lean | in Lean | informal; brute force |

Weighted DH-int's $\Theta(k/K)$ (all caps equal $K$): at most $2k/(K+k)$ by R4, at least $c_Kk/(2K)$ for $k\le2K$. For top-1 its ceiling falls from 0.667 at $K=2$ to 0.182 at $K=10$, while credit-DH's floor stays at 0.316 (0.421 at $K=2$).

### Why credit-DH works for top-k
**Why weighting fails.** Additive value splits by responder: each period-2 match belongs to the responder who shows it, so the proof bounds each responder separately. Top-$k$ value does not split that way. A user's matches come from several sources, and at $k=1$ a second good match adds nothing. R4's instance with $K=2$ shows it:
- Four block users value each other at 1, and each has one admirer, valued just under ½ both ways. Likes are certain.
- The full block and "perfect matching plus admirers" both have additive value about 8, and weighted DH-int picks the full block.
- Top-1 is 4 for the full block and about 6 for the other plan, which credit-DH picks. The ratio is $2/(K+1)$.

**The proof** ([[Top-k Match Quality]], T1) in four steps:
1. **Upper bound.** For any policy, let $y$ be its period-2 show probabilities and $z_{\ell\ell'}$ the probability that $\ell'$ matches $\ell$ and is among $\ell$'s $k$ best. This is feasible with objective $U_k$, so OPT $\le$ the program.
2. **Layer cake.** $\mathrm{top}_k=\int_0^\infty\min(N_u(\theta),k)\,d\theta$, where $N_u(\theta)$ counts $u$'s matches worth at least $\theta$. The program's credited value is $\int_0^\infty\min(\mu_u(\theta),k)\,d\theta$, where $\mu_u(\theta)$ is the planned expectation of $N_u(\theta)$.
3. **Following the plan.** Random marking is a contention-resolution scheme: each planned response survives with probability at least $\rho$. Each responder uses only its own backlog and coins, so a user's matches from different responders are independent. A greedy responder would not keep the plan's marginals.
4. **Poisson bound with cap $k$.** For independent coins, $\mathbb E\min(N,k)\ge c_k\min(\mathbb EN,k)$ (R1's lemma). A user's matches come from three sources: mutual views, responses to their initiations, and their own responses. The first two are independent. The third competes for the user's own $K_u$ slots, and an ordering argument with Harris's inequality and Chebyshev's integral inequality charges $\rho$ only once. So $\mathbb E\min(N_u(\theta),k)\ge\rho\,c_k\min(\mu_u(\theta),k)$; integrate over $\theta$ and sum over users.

**Where the constants come from.**
- $c_k$ is lost at each user: independent coins overshoot $k$ good matches (the extras are wasted) or fall short.
- $\rho$ is lost at each responder's random cut; Markov gives $\rho\ge1/2$.
- There is no $c_K$, unlike R5's guess of $c_Kc_k$: the responder no longer picks by value, so overflow costs $\rho$ instead.

### Unknown values
Counterparts from [[Match Quality with Queried Values]] and [[Top-k Match Quality]]:

| Information | Additive $Q$ | Top-$k$ $U_k$ |
| --- | --- | --- |
| Free rankings, value queries | weighted DH-int on estimates, $c_K(1-\varepsilon)/\lambda$ | credit-DH on estimates, $\rho c_k(1-\varepsilon)/\lambda$ |
| Priors, no queries | mean-weighted DH-int, $c_K$ | value-indexed credits (T2), $\rho c_k$ |
| Free backlog screening | value-indexed DH-int (B1), $c_K$ | special case of T3 |
| Screening budget | screening-aware DH-int (B3), $c_K\rho$ | T3, $c_k\rho_b\rho_K/(1+\rho_b)\ge c_k/6$ |
| Queries before period 1 | B2, $c_K$ with the best strategy | $\rho c_k$ with the best strategy |

## Evidence
- [[Rios 2026 - The Dating Heuristic]] and [[Dating Heuristic]]: the model, DH-int's program and its proof.
- [[Match Quality in the Dating Heuristic Framework]]: the objectives, R1 ($c_K$), R2, R3, R4 and R5.
- [[Top-k Match Quality]]: credit-DH, T1–T3, the $\Theta(k/K)$ bounds for weighted DH-int, and the brute-force checks in `data/scripts/topk_check.py` and `data/scripts/topk_screening_check.py`.
- [[Match Quality with Queried Values]]: B1–B3 and the bound on $\rho$.
- A rendered version with figures and every program written in full is a claude.ai artifact, "From DH-int to Credit-DH" (https://claude.ai/artifact/DjJfvCHbHPwArMwtcadbVF). It is private until its owner shares it.

## Gaps
- Inherits the gaps of [[Top-k Match Quality]]: credit-DH is not in Lean, whether $\rho$ is needed is open, and there is no top-1 lower bound beyond R4.
- Credit-DH's behavior on count and additive quality is not analyzed.
- On small random markets weighted DH-int usually beats credit-DH. A practical variant (credit program for period 1, greedy marginal top-$k$ responses) is untested.
- The original DH and DHT ([[Dating Heuristic]]) and strategic users ([[Strategic Users in the Dating Heuristic Framework]]) are out of scope here.
