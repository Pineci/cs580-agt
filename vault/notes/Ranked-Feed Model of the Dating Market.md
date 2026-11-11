---
type: concept
created: 2026-11-11
updated: 2026-11-11
tags: [dating/platforms, game-theory/incentives, matching/quality, research/project]
aliases: [ranked-feed model, ranking model, ranking policy, patience, exposure, reach, ranked feed, clock, feed protocol, timing of the dating model]
sources: ["[[Rios 2026 - The Dating Heuristic]]"]
origin: claude
status: seed
---
# Ranked-Feed Model of the Dating Market

A dating market in which the platform gives each user a ranking over all candidates and the user examines a prefix of it and swipes, under an explicit *clock* that says in what order users act. It is the common setting of [[The Live-Set Theorem for Truthful Swiping]], [[Welfare of Truthful Feeds in the Two-Cost Model]] and [[Queries and the Live-Set Theorem]].

> [!note] Preliminary
> Written 2026-11-11 and corrected the same day: the first version had no clock and called the round-based model a special case, which is true only of what a user sees in one sitting. Propositions 1 and 2 below are checked in Lean (`lean/DatingAlgo/Timing.lean`). Proposition 3, on the Dating Heuristic's setting, is an informal argument plus a simulation.

## Details

### The model
- **Market.** Two sides $I$ and $J$. User $\ell$'s candidates $C_\ell$ are the other side. $\ell$ has private values $v_\ell(x)\ge0$, wants at most $k_\ell$ partners, and pays $c$ per kept match and $d\le c$ per dropped one. Profile $x$ is *acceptable* if $v_\ell(x)>c$.
- **Prior.** Values are independent across ordered pairs. The platform knows their distributions and never sees a value unless it queries an oracle.
- **Events.** The market runs as a sequence of events. At each event the platform either closes the market or picks one user and shows them one profile they have not seen; that user swipes like or pass. Who acts next, and which profile they see, may depend on the platform's coins, the prior and the history of all swipes.
- **Sittings.** A user's events come in sittings. In a sitting the platform holds a ranking of $\ell$'s unseen candidates, $\ell$ examines the top entry, the platform may re-rank the rest, and the sitting ends after $R_\ell$ profiles. The *patience* $R_\ell$ has $\Pr[R_\ell\ge r]=\alpha^\ell_r$ and is independent of values, swipes and what is shown.
- **Matches and payoffs.** A pair matches if each examined and liked the other, unless the platform declines the mutual like. Each user then keeps or drops each match, and a conversation is a match both keep. $\ell$'s payoff is the value of its conversations, minus $c$ per conversation and $d$ per match it drops.
- **Truthful.** *Sincere* swiping likes exactly the acceptable profiles examined. A policy is *exactly truthful* if sincere swiping is a best strategy for every realization of the coins, the patience draws and the others' strategies.

### Two separate choices
A model fixes two things, and they are independent.
- **The format of a sitting.** A *set*: patience is a fixed number $K$, so order is irrelevant. Or a *ranked prefix*: patience is random, so higher positions are seen more often.
- **The clock**, a restriction on the order of events.
  - *Synchronized rounds:* in each round every user has one sitting, and the platform uses a round's swipes only from the next round on.
  - *Two stages:* all initiators have their sittings, then all responders.
  - *Continuous:* no restriction.

| | Synchronized rounds or stages | Continuous |
| --- | --- | --- |
| **Set per sitting** | [[Dating Heuristic]], screened DH, Q-SDH | daily batches at arbitrary times |
| **Ranked prefix per sitting** | the queue theorems C, C′, D, F, G (two stages) | a scrolling feed |

### Proposition 1: one user's view is a swipe tree, for every clock
Fix the platform's coins, the patience draws and the strategies of all users other than $\ell$. For every clock there is a swipe tree $t$ such that the match sets $\ell$ can obtain, by any way of swiping, are exactly the leaves of $t$, and liking exactly the shown profiles in $X$ leads to the leaf $t(X)$.

*Proof.* With everything else fixed, the market is a deterministic machine whose only input is $\ell$'s swipes. Run it. It performs events that do not involve $\ell$ (other users' swipes, re-rankings, ends of rounds) until it either shows $\ell$ a profile or closes. Closing gives a leaf. Showing a profile gives a node whose two subtrees are built the same way from the states after a like and after a pass. This ends because every event shows some user a profile they have not seen, and there are finitely many such pairs. $\square$

- The clock may itself depend on $\ell$'s swipes.
- **Scrolling at will.** If examining is free and the user chooses when to stop, stopping is the same as passing on the rest.

**Corollary (clock-free results).** Theorems A and A′, Theorem B and Theorem E are statements about a swipe tree and the match sets at its leaves. By Proposition 1 they hold under every clock, with or without rounds.

### Proposition 2: the queue results depend on the clock
The queue theorems assume two stages. Each of the following fails under another clock.
- **(a) The guarantee.** One initiator and one top-1 responder who are sure to like each other. The plan's objective is 1. With two stages the responder's queue holds the initiator and there is one conversation. If the responder's sitting comes first, its queue is empty and there is none, which is below $c_1\cdot1$. In general, if responder $j$ acts when only the initiators in $T_j$ have swiped, expected conversations are $\sum_j\mathbb E\min(k_j,|A_j\cap T_j|)$, which never falls when $T_j$ grows.
- **(b) The benchmark.** One initiator who likes everyone and may be shown one profile; two responders who each accept with probability $\tfrac12$. $\mathrm{LP}_1$ is at most $\tfrac12$. If the responders swipe first and the platform then shows the initiator a responder who accepted, expected conversations are $\tfrac34$. The LP's bound holds only when the decision to show $j$ to $i$ comes before both swipes.
- **(c) Truthfulness over rounds.** An initiator who wants one partner is shown one profile per round, and a second round happens only if the first left them unmatched. Both profiles would match. A user who values the first at 2 and the second at 5, with $c=1$, gets 1 by swiping sincerely and 4 by passing in round one. Each round alone satisfies Theorem A; the two together do not, because the second feed depends on the first swipe.

*Proofs.* (a) and (b) are the computations stated. (c) The outcome is the first profile if it is liked and otherwise the second if it is liked, which is not of the form $X\cap S$; the two utilities are $2-1$ and $5-1$. $\square$

- **What is clock-free in the queue.** An initiator is exactly truthful whenever it is shown at most $k_i$ profiles *in total* and whether a responder keeps it does not depend on its other swipes. Those are conditions on the swipe tree, so they can be checked under any clock.

### Proposition 3: the Dating Heuristic's setting as a special case
The setting of [[Rios 2026 - The Dating Heuristic]] has $T$ periods, at most $K_\ell$ unseen profiles shown to each user per period, backlogs, and likes that occur with probabilities $\phi^t_{\ell\ell'}(\sigma^t_\ell)$ depending on the user's own history.
- **(a) Who sees what, and when.** It is this model with synchronized rounds and a set per sitting. One- and two-directional designs, and same-period matches, are restrictions on the policy.
- **(b) Likes.** A like probability that depends on the user's own history is a randomized strategy: a rule from what the user has seen and done to a swipe. So every market of that paper is this model with every user's strategy fixed.
- **(c) When those likes are sincere.** If values are independent across pairs, sincere users like independently with probability $\Pr[v_\ell(\ell')>c]$, the same in every period and after every history. A probability that changes with the period needs a cost that changes with the period, which the theorems here do not cover. A probability that changes with the realized history is never sincere behavior.
- **(d) Objective.** With no limit on partners and the same surplus for every acceptable match, welfare is proportional to the number of matches.

*Proof.* (a) Let the platform show each user its period-$t$ set in any order and use the swipes only when building period $t+1$. (b) is the definition of a strategy. (c) A sincere user likes $x$ iff $v_\ell(x)>c$, an event that involves no other profile and no history. (d) Each match adds the same amount to both users' payoffs and nobody drops. $\square$

**Incentives inside the special case** (users with no partner limit).
- **Two rounds: truthful.** Under every two-round policy whose second round uses only a user's backlog, sincere swiping is dominant (Theorem 5(b) of [[Truthful Swiping with an LLM Oracle]], Lean-checked).
- **Three rounds: not truthful.** With one-period lookahead the second round's displays are re-optimized after the first round's swipes, and a user's own like changes what the program shows them next. In a three-round, one-directional market with three users per side and one profile per period, there are instances where passing on one profile gains a match with another *under every tie-breaking rule* (10 of 600 random instances). In one of them the initiator is shown $j_0$ in round 1. If it likes $j_0$ it is shown $j_2$ in round 2 and ends matched with $j_0$; if it passes it is shown $j_1$ and ends matched with $j_1$. By Theorem A, sincere swiping is then not dominant, even without a partner limit.
- This uses my reading of DH-int from the vault's source note, not the paper's code.

### The whole market
For a profile of strategies, one for each user, the market runs to a final state. `FeedMarket.final`, `realized` and `welfare` define the run, each user's matches and total welfare for any scheduler. Two facts tie this to the one-user view:
- whatever one user does, its realized matches are an outcome of the protocol it faces;
- if it likes exactly the shown profiles in $X$, they are the leaf $t(X)$.

So "sincere swiping is dominant" has its usual meaning: for every profile of the others' strategies, no deviation raises the user's realized utility (`market_sincere_dominant`).

### Which results hold, and under which clock
| Result | Clock it needs | With ranked sittings |
| --- | --- | --- |
| Theorems A, A′, B, E | none | as stated |
| Theorem C (responder queue) | two stages | exposures $e_{ij}$ replace display probabilities, and only the first $k_i$ positions of an initiator's feed can match |
| Theorem C′, two-cap lemma, Theorem F | two stages; the queue is complete before the responder looks | already ranking results |
| Theorem G (screened queue) | two stages; queries before displays | proved only when initiators examine all $k_i$ slots |
| Theorem D, Propositions P and T | fixed feed lengths and a fixed order of moves | deterministic patience |

### What ranking changes for the platform
- **Reach.** The profiles in the first $R_\ell$ positions of a sitting.
- **Exposure.** $e_\ell(x)=\sum_r\alpha^\ell_r\Pr[x\text{ at rank }r]$, the probability that $\ell$ examines $x$.
- **Constraint.** For a ranking drawn before the sitting, $e$ is achievable iff $\sum_{x\in T}e(x)\le\alpha_1+\dots+\alpha_{|T|}$ for every set $T$, with equality for $T=C_\ell$ *(not in vault, general knowledge: Rado's theorem on convex hulls of permutations)*. A set of $K$ is the case $\alpha=(1,\dots,1,0,\dots)$.

### Theorem A for a ranking over everyone
A policy is exactly truthful for $\ell$ iff, in every realization, at most $k_\ell$ of the profiles $\ell$ examines over all its sittings would match $\ell$, and which ones does not depend on $\ell$'s swipes.
- **A full ranking is a shortlist plus filler.** If $\ell$ may scroll through everyone, at most $k_\ell$ candidates in the whole pool can be live.
- **What makes a full ranking useful.** Theorem B: a policy that ignores $\ell$'s own swipes costs $d$ per match beyond $k_\ell$. Theorem E: with an oracle the cap disappears.

## Evidence
- **Lean, 2026-11-11.** `lean/DatingAlgo/Timing.lean`; `lean/check.sh` reports 1159 theorems, none open.
  - *The whole market:* `FeedMarket.final`, `realized`, `welfare`, `realized_outcome`, `realized_run`, `market_sincere_dominant`.
  - *Proposition 1:* `FeedProtocol` (a machine with arbitrary internal steps between the user's swipes), `FeedProtocol.outcome_iff_reach`; `FeedMarket.toProtocol` for a market with an arbitrary scheduler and arbitrary strategies of the others.
  - *Corollary:* `protocol_liveSet_iff` and `market_liveSet_iff` (Theorem A), `protocol_regret_le` (Theorem B), `protocol_keepBest` (Theorem E).
  - *Proposition 2:* `queue_guarantee_needs_order` and `queueConvAt_le` (a), `lp1_bound_needs_order` (b), `refill_not_truthful` (c).
- **Simulation, 2026-11-11.** `data/scripts/dh_multiround_own_swipe.py` solves DH-int exactly on small markets and quantifies over every tie-breaking rule. With two rounds a user's matches never depend on their own swipes (600 instances). With three rounds they do under every rule in 12 of 600 instances, and passing on one profile gains a match with another in 10 of them.
- [[Swipe Rounds versus Ranked Feeds]]: a plain-language comparison.

## Related
- [[The Live-Set Theorem for Truthful Swiping]]: swipe trees, Theorems A and B.
- [[Welfare of Truthful Feeds in the Two-Cost Model]]: the keep stage, Theorems C, C′ and D, Proposition T.
- [[Queries and the Live-Set Theorem]]: Theorems E, F and G.
- [[Counterexamples to the Multi-Period Dating Heuristic Guarantees]]: welfare guarantees are also delicate beyond two rounds in the set-per-sitting model.
- [[Position-Aware Reciprocal Re-Ranking and Dual Pacing]]: a position-aware model of the platform's optimization, with prices and budgets. It does not define users' strategies.

## Gaps
- **Welfare under a continuous clock.** Only the incentive theorems apply. No guarantee is known when users in both roles scroll and the platform re-ranks continuously.
- **More than two stages.** The queue theorems are not extended to further rounds, and (c) shows the natural extension breaks truthfulness.
- **Costly scrolling.** With a cost per profile examined, when to stop depends on beliefs about what lies below.
- **Re-shown profiles.** Each profile is shown to a user at most once and a swipe is final.
- **Position changing the swipe.** Position affects only whether a profile is examined.
- **History-dependent likes.** The Dating Heuristic's general setting is contained only as fixed strategies (Proposition 3(b)). No result here says when such strategies are best responses.
- **Period-dependent costs.** Needed to match like probabilities that change with the period; Theorems A, B and E are proved for one cost $c$.
- **The three-round finding** rests on a reconstruction of DH-int and on small markets with one profile per period. It has not been checked against the paper's formulation or on two-directional designs, where optima are always tied.
- **Lean.** The reduction and the whole-market run are formalized for an abstract scheduler. Sittings, patience, exposure, Proposition 3 and the three-round example are not.
