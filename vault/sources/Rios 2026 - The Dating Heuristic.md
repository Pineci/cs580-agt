---
type: source
source_type: paper
title: "The Dating Heuristic: A Provably Strong Matching Algorithm for Dating Platforms"
authors: [Ignacio Rios, Alfredo Torrico]
year: 2026
venue: "arXiv preprint (math.OC), arXiv:2308.02584v5 (first posted Aug 2023)"
citekey: "rios2026dating"
url: "https://arxiv.org/abs/2308.02584"
raw: "[[rios2026dating.pdf]]"
created: 2026-10-19
updated: 2026-10-19
tags: [dating/platforms, matching/assortment, optimization/submodular]
aliases: ["The Dating Heuristic: A Provably Strong Matching Algorithm for Dating Platforms"]
origin: claude
status: seed
---
# The Dating Heuristic: A Provably Strong Matching Algorithm for Dating Platforms

> [!summary]
> Models a curated dating app that chooses, each period, up to $K_\ell$ profiles to show each user. A match forms when two users see and like each other, possibly in different periods: pending likes wait in the receiver's "backlog". Users' like probabilities may depend on their own history. The platform maximizes expected matches over $T$ periods, which is an exponentially large dynamic program. The paper analyzes the Integral Dating Heuristic (DH-int), a one-period-lookahead mixed-integer program. In a two-period model DH-int is a $(1-1/e)$-approximation for every platform design: one- or two-directional, sequential-only or not. A precomputed $T$-period variant (DHT) is $(1-1/e)$ against semi-adaptive policies. Natural baselines (per-user greedy, per-period maximum matching) can be off by a factor of $n$. Simulations calibrated on data from a major U.S. dating app show DH-int producing about 19% more matches than Greedy and about 30% more than the app's own algorithm, close to an upper bound.

## Setting and model
- **Market.**
  - Two fixed sides $I$ and $J$ over a horizon $[T]$, with no arrivals or departures (bipartite and heterosexual for exposition).
  - Initial *potentials* $\mathcal P^1_\ell$ are the users mutually acceptable to $\ell$ by stated preferences (age, height, and so on).
- **Displays and likes.**
  - Each period the platform shows $S^t_\ell\subseteq\mathcal P^t_\ell$ with $|S^t_\ell|\le K_\ell$.
  - User $\ell$ likes $\ell'$ with probability $\phi^t_{\ell\ell'}(\sigma^t_\ell)$, independently across users.
  - A like does not depend on the other profiles shown alongside, because there is no substitution effect. This is justified empirically by Rios, Saban & Zheng (2023).
- **Dynamics (eq. 1).**
  - Each period, the profiles shown to $\ell$ and the users who disliked $\ell$ are removed from $\ell$'s potentials.
  - The *backlog* $\mathcal B^t_\ell$ holds potentials who have already liked $\ell$ but haven't yet been shown to $\ell$.
- **Matches come in two kinds.**
  - *Sequential:* $\ell'$ liked $\ell$ earlier, $\ell'$ is later shown to $\ell$ from the backlog, and $\ell$ likes back.
  - *Non-sequential:* both see each other in the same period and both like.
  - The match probability given mutual exposure is $\beta^t_{\ell\ell'}=\phi^t_{\ell\ell'}\phi^t_{\ell'\ell}$.
- **History** $\sigma^t_\ell=(L^{<t}_{\ell\to},D^{<t}_{\ell\to},B^t_\ell,M^{<t}_\ell)$: likes given, dislikes given, backlog, and matches so far. The platform knows $\phi$ as a function of history.
- **Objective (Problem 3.2).** $\max_{\pi\in\Pi}\mathbb E\big[\sum_t\sum_{(i,j)}\mu^{t,\pi}_{ij}\big]$.
  - The benchmark is the optimal adaptive dynamic program.
  - An omniscient benchmark that knows all likes in advance is too strong for any policy (Remark 3.3).
- **Platform design** is encoded in the admissible policy set $\Pi$:
  - *One-directional:* only one side initiates. Coffee Meets Bagel's "Ladies Choice" lets men initiate and shows women only men who liked them.
  - *Two-directional:* either side initiates.
  - Non-sequential matches can be allowed or forbidden. Examples where they're allowed: Tinder "Hot Takes", video speed dating.
- **Decision variables.**
  - $x^t_{\ell\ell'}\in\{0,1\}$ on arcs: $\ell$ sees $\ell'$, either initiating or from the backlog.
  - $w^t_e\in\{0,1\}$ on edges: both see each other in the same period.
  - Constraint: $x_{\ell\ell'}+x_{\ell'\ell}+w_e\le1$, so each pair is shown at most one way.

## Assumptions
- No entry or exit. Likes are independent, unaffected by the rest of the display, and $\phi(\cdot)$ is known.
- **Two-period analysis (Section 4).**
  - The initial backlog is empty.
  - Period-2 probabilities may differ from period 1 but don't depend on the realized period-1 history.
  - No non-sequential matches in period 2 ($w^2=0$). The authors argue this is mild because most matches are sequential.
- **$T$-period analysis (Section 5).** Like probabilities don't change over time, and there are no non-sequential matches in the last period.
- **Proxy for next period.** The lookahead plugs in a history-free proxy $\hat\phi^{t+1}$, typically $\phi^t$. This is optimistic when like probabilities fall with history.

## Main results
**Structure of the second-period problem**
- **Prop 3.4.** The next-period value $f^{t+1}(R)$, with non-sequential matches allowed, is *not* submodular in the realized like set $R$.
  - It can still be evaluated by an LP, because the constraint matrix is totally unimodular (Prop B.2).
- **Lemma 4.1, C.2.** Without non-sequential matches in period 2, things are better behaved:
  - $f(R)$ is a weighted rank function over a partition matroid, so it is monotone submodular.
  - So is $\mathsf M^2(\mathbf x^1)=\mathbb E_{R\sim\phi^1\cdot\mathbf x^1}f(R)$.

**Guarantees**
- **Thm 4.3.** DH-int (Algorithm 2) is a $(1-1/e)$-approximation for the two-period problem (Problem 4.2), for every platform design.
- **Thm 4.4 and Appendix E.** Polynomial-time alternatives do submodular maximization over a matroid intersection that depends on the design (Algorithm 5). Guarantees by design:

  | Design | Constraint structure | Guarantee |
  | --- | --- | --- |
  | One-directional, sequential | one partition matroid | $1-1/e$ (continuous greedy + dependent rounding) |
  | Two-directional, sequential | two matroids | $1/(2+\epsilon)$; greedy gets $1/3$ |
  | One-directional, non-sequential in period 1 | partition ∩ laminar matroid | $1/(2+\epsilon)$ |
  | Two-directional, non-sequential in period 1 | three partition matroids | $1/(3+\epsilon)$ |

- **Thm E.13.** Allowing non-sequential matches in period 2 adds at most a constant factor in large, "picky" markets.
  - Setting: one-directional, time-invariant probabilities, and initiators' like probabilities at most $1/n$.
  - Bound: $\mathrm{OPT}_1\ge(\tfrac1{2e}-o(1))\,\mathrm{OPT}_2$.
- **Props D.1, D.2.** Two natural baselines can be only $O(1/n)$-approximate.
  - *Local Greedy* shows each user the $K$ profiles with the best match probability for that user. It ignores congestion on popular profiles.
  - Per-period maximum-weight *Perfect Matching* ignores the information in realized likes.
- **Thm 5.3.** DHT (Algorithm 3) is $(1-1/e)$ against the best *semi-adaptive* policy, for any design and any $T$.
  - DHT solves one $T$-period relaxation (eq. 19) up front.
  - It shows the selected initiating profiles without adapting.
  - It fills each user's spare slots from their backlog, in order of like probability.
  - A semi-adaptive policy chooses initiations non-adaptively and backlog responses adaptively. The upper bound comes from Lemma 5.2.
- **Thm 5.4.** For one-directional, sequential-only designs, a semi-adaptive policy is $(1-1/e)$ against the best fully *adaptive* policy. It uses the LP relaxation of (19), dependent rounding (Gandhi et al. 2006), and then DHT.

## Technique
- **DH-int program (eq. 11).**
  - First-period decisions $(\mathbf x^t,\mathbf w^t)$ are binary. Next-period variables are continuous "expected" quantities: $x^{t+1}_{\ell\ell'}\in[0,1]$ is roughly the probability that $\ell$ sees $\ell'$ from the backlog.
  - The coupling constraint $x^{t+1}_{\ell\ell'}\le\phi^t_{\ell'\ell}\,x^t_{\ell'\ell}$ says $\ell'$ can reach $\ell$'s backlog only if $\ell'$ was shown $\ell$ and liked them.
  - Each period has its own cardinality limit $K_\ell$, and each backlog profile can be shown at most once over the two periods.
  - It differs from the original DH (Rios, Saban & Zheng 2023) only in requiring integral first-period variables. That removes DH's rounding step. Lemma B.1 shows the two feasible regions are otherwise equivalent.
- **Proof of Thm 4.3.**
  1. The MIP value upper-bounds OPT (Lemma C.5).
  2. Its period-2 part $F(\mathbf x^{1*})$ is a fractional LP with marginal constraints. Lemma C.4 shows $F$ is at most the *distribution problem* $G$, using LP duality and the structure of $G$'s dual (Lemma C.3).
  3. $G$ maximizes expected period-2 matches over *any*, possibly correlated, backlog distribution whose marginals are $\phi^1_{\ell'\ell}x^1_{\ell'\ell}$.
  4. The real backlog is independent across senders. By the [[Correlation Gap]] of the monotone submodular per-user value $f_\ell$ (Agrawal et al. 2010), it achieves $\mathsf M^2\ge(1-1/e)G$.
  5. So $\mathsf M^2\ge(1-1/e)G\ge(1-1/e)F$.
- **DHT proof.** The same correlation-gap argument on the $T$-period relaxation with per-user budget $K_\ell T$. The key step (Claim F.1) is that greedily filling backlog slots by like probability reproduces the optimal set for the total set of likes received.

## Experiments
- **Data.** Proprietary data from an anonymous industry partner (a major U.S. app, under NDA).
  - Sample: all heterosexual users in Houston, TX active 14 Feb–14 Aug 2020. That is 1,682 women and 1,193 men.
  - Average potentials: about 110 for women, 133 for men.
  - Mean like probability: about 0.30 for women, 0.53 for men (Table 3).
- **Like-probability model.**
  - A logit with user and date fixed effects, estimated on 396k evaluations (pseudo-$R^2$ 0.386, Table 2).
  - Covariates: the evaluated profile's attractiveness score, age, height, and education; positive and negative differences from the evaluator on each; shared race; shared religion.
  - Women's like probabilities pile up near 0; men's are spread out with a mode near 1 (Fig. 5).
- **Simulation setup.** $T=7$ days, $K_\ell=3$, 100 runs, starting from users' real backlogs on 14 Feb 2020. History effects enter the logit utility in five ways:
  - none;
  - linear in number of matches, $\gamma=-0.170$, from Rios, Saban & Zheng (2023);
  - threshold: stop liking after more than 5 matches;
  - disengagement: $-0.2\,t$;
  - signaling: $+0.2$ when the user knows the profile is from their backlog (cf. Lee & Niederle 2014).
- **Results, two-directional with linear history (Table 4):**

  | Algorithm | Matches |
  | --- | --- |
  | DH-int | 4691 |
  | DH | 4634 |
  | DHT | 4442 |
  | Greedy | 3948 |
  | Perfect Matching | 3676 |
  | Partner's algorithm | 3597 |

  - The DH variants come close to the upper bound.
  - The ranking is the same under every history effect (Fig. 1).
  - The gap to the upper bound is largest under disengagement.
  - DH-int's lead grows with the strength of the history effect, from about 20% to 25% as the multiplier $\psi$ goes from 0 to 5 (Fig. 3).
- **Why DH wins (Fig. 2).** The DH variants deliberately show initial profiles with *lower* like rates, except in the last period. In exchange, their backlog interactions convert at higher and steadier rates. They balance getting an initial like against getting it reciprocated.
- **One-directional designs.**
  - DH-int gets 4246 matches with men initiating and 4250 with women initiating, versus 4691 two-directional. The paper calls this "very close"; it is about 9% fewer.
  - Women initiating does better for every algorithm, and much better for DHT, Greedy, and the partner's algorithm.

## Limitations and gaps
- **Objective.** The objective is the number of matches. It ignores utilities, fairness across users, and stability, and a user can match many times. (These observations are mine.)
- **Behavior.**
  - Users are stochastic but not strategic.
  - The platform knows $\phi$ exactly; in the simulations, $\phi$ comes from the estimated logit.
- **Computation.** DH-int solves a MIP every period, so it has no polynomial-time guarantee. The polynomial alternatives have weaker guarantees that depend on the design.
- **Restrictive assumptions behind the guarantees.**
  - Two-period guarantee: no history-dependence in period-2 probabilities and no non-sequential matches in the last period.
  - $T$-period guarantee: time-invariant probabilities and a semi-adaptive benchmark.
  - The guarantee against fully adaptive policies covers only one-directional, sequential-only designs.
- **Evidence.** The simulated matches come from model-estimated probabilities, not field outcomes. The original DH was field-tested in Rios, Saban & Zheng (2023).
- **Market.** The market is static, with no arrivals or departures.

## Relevance to my work
- *Provisional until the project direction is set.*
- This is the most operational source so far for a "dating algorithm". It formalizes what an app actually decides (whom to show to whom) and gives a benchmark algorithm with guarantees.
- Table 2's logit coefficients and Table 3's summary statistics could calibrate our own simulations in `data/`.
- Contrast with [[Filos-Ratsikas 2026 - The Distortion of Stable Matching]] *(my reading)*:
  - There, a central clearinghouse outputs one stable matching from rankings plus a few queries, and quality is measured as welfare.
  - Here, a platform probes pairs over time. Each display works like a noisy binary query answered with a like or dislike. The objective is mutual likes, with no stability requirement.
  - A model that elicits preferences through displays and likes but targets welfare or stability could bridge the two.
- **Project direction (set 2026-10-19):** extend this framework from match count to match quality. Analysis so far: [[Match Quality in the Dating Heuristic Framework]].

## Follow-up reading
- Rios, Saban & Zheng (2023, MSOM), "Improving match rates in dating markets through assortment optimization": the original DH, history-effect estimates, and a field experiment.
- Two-sided assortment optimization:
  - Ashlagi, Krishnaswamy, Makhijani, Saban & Shiragur (2022, OR)
  - Torrico, Carvalho & Lodi (2021)
  - Aouad & Saban (2022, MS)
- Matching platform design:
  - Kanoria & Saban (2021): facilitating search
  - Immorlica, Lucier, Manshadi & Wei (2022)
  - Celdir, Cho & Hwang (2024): popularity bias in dating
  - Halaburda, Piskorski & Yildirim (2018)
- Lee & Niederle (2014): signaling in online dating
- Agrawal, Ding, Saberi & Ye (2010): correlation gap
- Stochastic matching / query-commit: Chen, Immorlica, Karlin, Mahdian & Rudra (2009); Jeloudar, Lo, Pollner & Saberi (2021)

## Concepts
- [[Two-Sided Assortment Optimization]]
- [[Dating Heuristic]]
- [[Correlation Gap]]
- [[Submodular Maximization]]
- [[History-Dependent Like Probabilities]]
