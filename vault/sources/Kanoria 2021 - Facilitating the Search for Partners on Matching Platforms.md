---
type: source
source_type: paper
title: "Facilitating the Search for Partners on Matching Platforms"
authors: [Yash Kanoria, Daniela Saban]
year: 2021
venue: "Management Science 67(10):5990–6029 (2021), doi:10.1287/mnsc.2020.3794"
citekey: "kanoria2021facilitating"
url: "https://business.columbia.edu/sites/default/files-efs/citation_file_upload/ssrn_id3667353_code2067838.pdf"
raw: ""
created: 2026-10-21
updated: 2026-10-21
tags: [dating/platforms, matching/search, market-design, game-theory/incentives]
aliases: ["Facilitating the Search for Partners on Matching Platforms", "Kanoria & Saban 2021", "Restricting Agent Actions"]
origin: claude
status: seed
---
# Facilitating the Search for Partners on Matching Platforms

> [!summary]
> A dynamic two-sided search model with a continuum of agents and no prices. Agents are shown random candidates and may pay $c$ to learn their idiosyncratic value for one before proposing or before answering a proposal. The paper characterizes evolutionarily stable stationary equilibria and compares them with a constrained planner. Two inefficiencies recur. Recipients are too selective, because they ignore the screening that proposers waste on rejections. In an unbalanced market, the long side does the proposing and can't afford to screen. Blocking the long side from proposing creates a better equilibrium. With vertical differentiation, also hiding quality stops short-side agents from holding out for top partners, which gives a Pareto improvement as $c\to0$.

> [!info] Version read
> I read the SSRN version (abstract 3004814, dated 2020-08-04, accepted at Management Science) in full: 71 pages, with the main text on pp. 1–36 and Appendices A–E on pp. 37–71.
> - **Not read:** the separate online supplementary appendix (`supp-KS-Aug2020.pdf`). It holds the proofs of Props. 1, 2 and 7, Theorems 4, 5 and 9 (detailed as 14, 15 and 18), Theorem 17, Corollaries 6 and 10, and Lemmas C.1 and D.6–D.8.
> - Numbering may differ in the journal version.

## Setting and model
- **Market.**
  - The two sides are called workers and employers, with a continuum of each in continuous time. Employers arrive at rate $\lambda_e$ and tier-$t$ workers at rate $\lambda_w^t$.
  - A matched pair leaves at once. Unmatched agents leave at hazard rate $\mu$. The analysis takes $\mu\to0$, so every agent gets many opportunities.
- **Values.** Agent $i$'s value for $j$ is $v_{ij}=q_j+u_{ij}$.
  - Quality $q_j$ is public. Employers and L-workers have $q=0$; H-workers have $q>0$.
  - $u_{ij}\sim U(0,1)$ is i.i.d. over *ordered* pairs. Nobody, the platform included, knows it until $i$ pays a screening cost $c$ to learn it privately.
  - Utility is the value of the match, if any, minus total screening costs. There are no transfers.
- **Protocol.** Each agent has a rate-1 Poisson opportunity clock. When it rings:
  1. The agent may request a candidate, and the platform shows a uniformly random agent from the other side. With two worker tiers, an employer can ask for a tier.
  2. The agent may screen the candidate, then decides whether to propose.
  3. The recipient sees the proposer's tier for free, may screen, and accepts or rejects.
  - Everything happens instantaneously.
- **Strategies (Defs. 1–2).** Each agent fixes a deterministic strategy on arrival:
  - for opportunities, $a^o\in\{$do nothing, propose without screening, screen then propose$\}$;
  - for proposals, $a^i\in\{$ignore, accept without screening, screen then accept or reject$\}$;
  - thresholds $(\theta^o,\theta^i)$ used after screening.
- **Interventions** restrict the allowed actions:
  - *Block a side from proposing.*
  - *Hide quality from employers:* each employer uses one action and one threshold for all workers, and candidates are drawn from both tiers. Screening still reveals the total value $v$.
- **Objective.** Steady-state average welfare, weighted by arrival rates (eq. 4). Because every type's utility is characterized, other objectives would also work.

## Equilibrium concept
- **The agent's problem is a stationary MDP.** The agent waits for a candidate, a proposal, or exit, and returns to waiting after any failed attempt. The exit risk acts as a per-epoch discount factor.
- **Prop. 1: the threshold equals the continuation value.** Any best response uses one threshold, on total value, for candidates and proposals alike. It equals the agent's best-response expected utility, $\theta^*=\max_sU(s)$.
- **Robust best response (Def. 6).** A best response must also stay optimal after a hypothetical "bonus" proposal or "bonus" opportunity. This kills spurious equilibria, such as everyone ignoring everyone.
- **Stationary equilibrium (Def. 4).** It follows Hopenhayn (1992) and is akin to a mean-field equilibrium. Thresholds equal best-response utilities, arriving agents play only best responses, and the agent mix is an attractive fixed point of the flow ODEs.
- **Evolutionary stability (Def. 7).** After a perturbation, newcomers who best-respond to the current mix must push the system back to the equilibrium. Thresholds are held fixed.
- **Conventions.** "Equilibrium" means an evolutionarily stable stationary equilibrium. Results hold for $\mu<\mu_0(c)$, with utilities stated as $\mu\to0$.

## Assumptions
- **Continuum.** A continuous-time exact law of large numbers, which the authors note is rigorous only in discrete time.
- **Values and costs.** Uniform values, independent across pairs and directions, and one screening cost $c$ for everyone.
- **No curation.** Candidates are uniformly random; the platform can't see $u_{ij}$.
- **No congestion.** With instantaneous actions there are no coordination failures. Those failures are the friction behind the opposite conclusion, that the long side should propose, in Herreiner (1999) and Shi & Delacroix (2018).
- **Matching.** Matches are one-to-one and final.
- **Section 3.** Its full characterization also imposes Restriction 4: agents handle proposals and opportunities independently.
- **Section 4.**
  - Only workers are vertically differentiated, with $q\in(0,1)$.
  - Employers outnumber H-workers but not all workers: $\lambda_e\in(\lambda_w^H(1+q/2),\lambda_w^H+\lambda_w^L)$.
  - Screening costs are small.

## Main results
**Planner benchmark, one tier on each side**
- **Prop. 2.** For any strategies,
  $$\text{Avg-welf}\le\frac{\min(\lambda_w,\lambda_e)}{\lambda_w+\lambda_e}\,W(c).$$
  The bound is attained as $\mu\to0$. The per-match value $W(c)$ is:

  | $c$ | Who screens | $W(c)$ |
  | --- | --- | --- |
  | $\ge1/8$ | nobody | $1$ |
  | $[\tilde c,1/8)$ | recipients, with $\theta^i=1-\sqrt{2c}$ | $\tfrac32-\sqrt{2c}$ |
  | $(0,\tilde c)$ | both sides | $g(c)$ |

  - **When both screen,**
    $$g(c)=\sup_{\theta^o,\theta^i}\Big[\tfrac{1+\theta^o}{2}-\tfrac{c}{(1-\theta^o)(1-\theta^i)}+\tfrac{1+\theta^i}{2}-\tfrac{c}{1-\theta^i}\Big].$$
    These terms are the proposer's value and screening cost per match, then the recipient's.
  - **Optimal thresholds.** With $x=1-\theta^o$ and $y=1-\theta^i$, the first-order conditions (eq. 7) are $x^2y=2c$ and $y=x(1+x)$.
  - **Cutoff.** $\tilde c\approx0.060$.
- **Remark 1: recipients should be the lenient side.** The planner sets $\theta^o>\theta^i$. The total value of a match depends only on the two thresholds, but every proposal the recipient rejects wastes the proposer's screening.

**Symmetric markets: one side proposes, and recipients are too selective**
- **Thm. 3** ($\lambda_w=\lambda_e$). The stable equilibria are exactly these, each with its mirror image:

  | $c$ | Equilibrium | Limiting utilities = thresholds |
  | --- | --- | --- |
  | $(0,1/32)$ | one side screens and proposes; the other never proposes and screens proposals | proposers $1-(2c)^{1/4}$; recipients $1-\sqrt{2c}$ |
  | $(1/32,1/8)$ | one side proposes without screening; the other screens proposals | proposers $1/2$; recipients $1-\sqrt{2c}$ |
  | $\ge1/8$ | nobody screens | $1/2$ |

  - **Symmetry breaks.** Although both sides may propose, only one does: a recipient faces no rejection and has no reason to risk it.
  - **The recipient's threshold** is $1-\sqrt{2c}$, the classical optimal-stopping threshold. It comes from the Bellman equation $V=\frac1{1+\mu}[-c+(1-\theta)\frac{1+\theta}2+\theta V]$.
  - **Mixed equilibria are unstable** (Lemma D.2). If more workers propose, waiting becomes better for employers, which in turn makes proposing better for workers.
- **Inefficiency 1: recipients are too selective.**
  - A proposer facing a recipient threshold $\theta_r$ pays an *effective screening cost* $c/(1-\theta_r)$ per useful candidate (Lemma C.1). Here that is $\sqrt{c/2}$.
  - So proposers stop screening at $c=1/32$, below the planner's cutoff $\tilde c$.
  - Welfare is strictly below the planner's for small $c$.
- In a symmetric market, blocking one side just selects the mirror equilibrium, with the same welfare.

**Unbalanced markets: the long side proposes and can't be selective**
- **Thm. 4 (no intervention).** Workers are the long side, with $R=\lambda_w/\lambda_e\ge1.25$. Define $\xi(R,c)=\frac{R-\sqrt{(R-1)^2+2c(2R-1)}}{2R-1}$ and $\underline c=1/(8R^2)$; eq. 38 defines a cutoff $\bar c(R)>\underline c$.
  1. **$c<2\bar c^2$:** workers screen and propose with $\theta_w=\xi(R,\sqrt{c/2})$.
  2. **$c\in(2\underline c^2,1/8)$:** workers propose without screening, for utility $1/(2R)$.
  3. **$c>1/8$:** nobody screens.
  - In equilibria 1 and 2, employers screen proposals with $1-\sqrt{2c}$.
  - Equilibria 1 and 2 coexist on $(2\underline c^2,2\bar c^2)$; elsewhere the equilibrium is unique.
  - For $c<1/8$ the long side proposes in *every* equilibrium. Facing exit risk, a worker always uses its opportunities, and employers then prefer to wait.
- **Thm. 5 (workers blocked from proposing).** Let $\hat c=\frac{8R-7}{32(2R-1)}$.
  - For $c<\min(\bar c,\hat c)$ there is an equilibrium where:
    - employers screen and propose with $\theta_e\to1-\sqrt{2c/(1-\xi(R,c))}$;
    - workers screen proposals with $\theta_w\to\xi(R,c)$.
  - It is unique for $c<\min(\underline c,\hat c)$.
  - Workers now pay $c$ per screening instead of $\sqrt{c/2}$, so they become more selective. Employers lose a little and workers gain a lot.
- **Remark 2: same-side spillover.** A worker who rejects an employer frees her for other workers. A worker's chance of receiving a proposal before exit rises from $1/R$ to $1/(\theta_w+R(1-\theta_w))$.
- **Cor. 6.** For any $R>1.25$ and small enough $c$, blocking the long side strictly raises average welfare. The equilibrium is unique in both cases.
- **Gap to the planner (Fig. 3, $R=2$).** The intervention comes close to the planner for intermediate $c$. For small $c$ the gap stays large, because the long side still uses a low threshold against exit risk.

**Vertical differentiation (H- and L-workers)**
- **Prop. 7 (planner).** For $c<c_0(q)\le1/32$,
  $$\text{Avg-welf}\le\frac{\lambda_w^Hq+\lambda_e\,g(c)}{\lambda_w^H+\lambda_w^L+\lambda_e}.$$
  At the optimum all employers and all H-workers match, only L-workers go unmatched, and L-workers never propose.
- **Thm. 8 (no intervention: reachers and settlers).** For small $c$ and $\mu$ there is a stable equilibrium:
  - **Employers.**
    - They propose only to H-workers, screening with $\theta_e\to1-\sqrt{2c}$.
    - *Reachers* also ignore L-workers' proposals. Their share is $\to(\lambda_w^H+\delta^H)/\lambda_e$, where $\delta^H\approx\lambda_w^Hq/2$.
    - *Settlers* screen L-workers' proposals.
    - Both earn the same utility.
  - **H-workers** never propose, screen proposals with $1-\sqrt{2c}$, and match instantly.
  - **L-workers** propose without screening, for utility $\to\frac{\lambda_e-\lambda_w^H-\delta^H}{2\lambda_w^L}$.
  - **Inspection paradox.** A flow $\delta^H$ of reachers leaves unmatched. Reachers therefore linger, with steady-state mass $\Theta(1/\mu)$, and swamp the settlers.
  - **Inefficiencies:**
    1. Short-side agents (employers) leave unmatched, even as $c\to0$.
    2. L-workers can't screen at all, even as $c\to0$. Almost every employer they reach ignores them, so their effective screening cost diverges.
    3. Thresholds are off. Employers' threshold for H-workers is $\le1$, where the planner's tends to $1+q$, and proposal-screening thresholds are too high. Neither intervention fixes this.
- **Thm. 17 (block workers from proposing).** L-workers become recipients and screen, with $\theta_w^L\to\frac1{2R_\delta^L-1}$, where $R_\delta^L=\lambda_w^L/(\lambda_e-\lambda_w^H(1+q/2))$. Reachers persist and still leave unmatched.
- **Thm. 9 (block workers and hide quality).** Assume $\lambda_e\in(\lambda_w^H,\lambda_w^H+\lambda_w^L)$ and write $R^L=\lambda_w^L/(\lambda_e-\lambda_w^H)$. The equilibrium is then unique:
  - employers screen and propose to random workers, with $\theta_e\to1-K_ec$;
  - H-workers screen proposals, with $\theta_w^H\to1-K_H\sqrt c$;
  - L-workers screen proposals, with $\theta_w^L\to\frac1{2R^L-1}$.

  The constants $K_e$ and $K_H$ are explicit.
  - **Why it works.** Without tiers, nobody can be a reacher. Since $\theta_e\le1$, every employer eventually matches, so Inefficiency 1 is gone.
  - **What remains.** One threshold for both tiers is too lax for H-workers and too strict for L-workers.
- **Table 1** (limits $\mu\to0$, then $c\to0$).
  - Employers and H-workers get 1 in every case.
  - L-workers get:

    | Intervention | L-worker utility |
    | --- | --- |
    | none | $\frac1{2R_\delta^L}$ |
    | block workers from proposing | $\frac1{2R_\delta^L-1}$ |
    | block and hide quality | $\frac1{2R^L-1}$ |

  - Each step raises L-workers' utility and leaves the others unchanged: a Pareto improvement *in the limit*.
  - *My computation:* at positive $c$ it isn't quite Pareto. Since $K_H>\sqrt2$, H-workers get $1-K_H\sqrt c<1-\sqrt{2c}$. An $O(\sqrt c)$ flow of them also leaves unmatched (Thm. 18).
- **Section 5.**
  - **Raising screening costs on purpose** gives at most a minimal gain in numerical experiments.
  - **Admission control (Cor. 10).** For $R\ge1.28$ and $c<1/32$, block workers and admit them only at rate $R^*\lambda_e$, where $\xi(R^*,c)=\theta^i(c)$. This reaches the planner's welfare as $\mu\to0$. Workers' over-selectivity as recipients exactly offsets their exit risk.

## Technique
- **Effective screening cost (Lemma C.1).** Screening options that arrive at rate $\eta$, each succeeding with probability $p$, at cost $c$, is worth the same as screening options that arrive at rate $\eta p$ at cost $c/p$. Rejection risk inflates a proposer's cost, and that drives most of the results.
- **Utopian bound (Lemma C.2).** No agent earns more than $q_{\max}+\max(1/2,1-\sqrt{2c})$. It earns strictly less if it can be rejected after screening or can leave unmatched.
- **Existence (Thm. 3).**
  1. Write each side's Bellman equation to get best-response threshold maps.
  2. The recipient's map is $O(\mu/c^{3/2})$-Lipschitz: recipients feel the proposers' threshold only through exit risk.
  3. So the composition of the two maps is a contraction for small $\mu$.
  4. The resulting best responses are strict, which gives evolutionary stability.
- **Uniqueness.**
  - Lemma D.1: everyone answers proposals.
  - Lemma D.2: there is no stable mixing on both sides.
  - The rest is case analysis.
- **Thm. 8.**
  - The fixed point is found perturbatively in $\mu$.
  - The share of reachers is pinned down by reachers and settlers being indifferent.
  - Stability comes from eigenvalues on two time scales, $-\mu$ and $-\gamma$.

## Experiments
- **No data.** Fig. 3 plots welfare against $c$ for $R=1$ and $R=2$. Section 5 reports some numerics.
- **Motivation:**
  - the TaskRabbit redesign;
  - search frictions on Airbnb and Upwork;
  - Tinder surveys (Tyson et al. 2016): 59% of women but 9% of men like fewer than 10% of profiles;
  - Bumble (only women write first; more male users) and Coffee Meets Bagel (more female users);
  - Tinder's hidden Elo score.

## Limitations and gaps
- **Stylized.** Values are uniform, $c$ is common, and candidates are random. There is no curation, which is exactly the lever [[Rios 2026 - The Dating Heuristic]] studies. *(my observation)*
- **One match per agent**, and matches are final.
- **Scope.**
  - The results hold as $\mu\to0$, and in Section 4 for small $c$.
  - The boundaries between regimes are not characterized.
  - Thm. 8 proves existence only.
- **Weak stability.** Evolutionary stability holds thresholds fixed, which the authors call a "weak" notion.
- **Pareto only in the limit.** Inefficiency 3 survives both interventions, and the Pareto improvement needs $c\to0$.

## Relevance to my work
- **What it offers.** This is the closest *strategic* model to ours.
  - Agents decide whether to pay to learn a value, and whether to initiate.
  - Platform design means restricting their actions, and it is evaluated in equilibrium.
  - It lacks the curation and multiple matches that our setting has. Ours is [[Rios 2026 - The Dating Heuristic]] with strategic users ([[Strategic Users in the Dating Heuristic Framework]]).
- **Screening cost ↔ our screening budgets.**
  - The screening cost $c$ is a per-profile evaluation cost, like B3's responder budgets in [[Match Quality with Queried Values]] or the cost of an LLM evaluation.
  - Lemma C.1 carries over directly to our period 1. Suppose an initiator must pay to evaluate $r$, and $p_r$ is the probability that $r$ is shown the initiator and likes back. The initiator then faces cost $c/p_r$.
  - DH-int's display plan sets $p_r$. So the platform sets users' effective screening costs, and with them whether period-1 likes are informed.
  - Our S1 dominance argument assumes values are free to learn. With a cost, strategy enters through the choice to *screen*.
  - Proposing without screening is the costly-screening version of our S3 finding that likes stop carrying information.
  - *My reading:* LLM agents push $c\to0$, but the two-tier inefficiencies survive that, because $c/p$ blows up when a user is almost always ignored. Cheap screening alone doesn't make unpopular users' likes informative.
- **Restricting actions helps only when users are strategic.**
  - In Rios & Torrico, two-directional policies include the one-directional ones. With non-strategic users a restriction can only lower the optimum: about 9% fewer matches for DH-int.
  - Here, blocking a side gives a better equilibrium (Thms. 5 and 9, Cor. 6).
  - A target result for us: in equilibrium, a one-directional DH-int could beat a two-directional one once screening or likes are costly or budgeted.
- **Which side should initiate.** *(my reading)*
  - Remark 1 says the less selective side should receive. In equilibrium that is the long side, hence "the short side proposes".
  - In Rios & Torrico's Houston data, women outnumber men (1,682 vs 1,193) but like far less often (0.30 vs 0.53).
  - Women initiating did best for every algorithm there. That fits Remark 1, not "the short side proposes", so the two criteria can disagree.
- **Our responder is the paper's recipient.** In our model a period-2 like-back is a sure match, just as a recipient here faces no rejection. So Inefficiency 1 (responders ignoring senders' wasted effort) should reappear once likes or screening cost something, for example under S4's like budgets.
- **Hiding information is the other half of our cheap-talk question.**
  - Hiding quality stops reaching. Our analogue is which signals the platform displays, such as popularity or "already liked you" badges.
  - An LLM agent that estimates popularity would undo the hiding.
  - S5 covers information flowing from agents to the platform; this paper covers information flowing from the platform to agents.
- **Equilibrium toolkit.**
  - Prop. 1 (threshold = continuation value) is the stationary analogue of the rising thresholds of our top-$k$ users in S7 and [[Top-k Match Quality]].
  - Stationary equilibrium with evolutionary stability is a ready-made concept if we move to many periods with arrivals.
  - The bonus-proposal refinement handles zero-probability events, such as a user who never receives a backlog like.

## Follow-up reading
- **Who should search:** Herreiner (1999); Shi & Delacroix (2018, QJE).
- **Congestion:** [[Arnosti 2021 - Managing Congestion in Matching Markets]].
- **Signaling:** [[Coles 2013 - Preference Signaling in Matching Markets]]; [[Lee 2015 - Propose with a Rose]].
- **Restricted choice:** Halaburda, Piskorski & Yıldırım (2018).
- **Cream skimming and information design:** Romanyuk & Smolin (2019).
- **Survey:** Chade, Eeckhout & Smith (2017).

## Concepts
- [[Two-Sided Assortment Optimization]]: its one- vs. two-directional lever is this paper's "block a side from proposing".
- [[Match Quality with Queried Values]]: costly screening of values, as in B3's budgets.
- [[Match Quality in the Dating Heuristic Framework]]: this paper's objective is welfare, not match count.
- Covered in [[Congestion in Matching Markets]]: costly screening. Agents pay to learn values, with effective cost $c/p$ under rejection risk. Overlaps [[Query-Enhanced Algorithms]], where the platform queries values instead.
- Covered in [[Two-Sided Assortment Optimization]] (section added 2026-10-21): initiating-side design. Which side should propose, and why restricting it helps in equilibrium. Overlaps the "one-directional" alias of [[Two-Sided Assortment Optimization]].
- Not a separate note yet: hiding quality information. Withholding vertical scores, such as a hidden Elo, to widen search.
- Not a separate note yet: stationary equilibrium. A mean-field steady state in which thresholds equal continuation values, refined by evolutionary stability.
- Covered in [[Congestion in Matching Markets]]: search frictions. Decentralized two-sided search, including reachers vs. settlers.
