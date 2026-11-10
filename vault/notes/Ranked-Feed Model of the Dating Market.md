---
type: concept
created: 2026-11-11
updated: 2026-11-11
tags: [dating/platforms, game-theory/incentives, matching/quality, research/project]
aliases: [ranked-feed model, ranking model, ranking policy, patience, exposure, reach, ranked feed]
sources: ["[[Rios 2026 - The Dating Heuristic]]"]
origin: claude
status: seed
---
# Ranked-Feed Model of the Dating Market

A dating market in which the platform gives each user a ranking over all candidates, the user examines a prefix of it and swipes, and the platform may re-rank after every swipe. It is the common setting of [[The Live-Set Theorem for Truthful Swiping]], [[Welfare of Truthful Feeds in the Two-Cost Model]] and [[Queries and the Live-Set Theorem]].

> [!note] Preliminary
> Written 2026-11-11. It collects definitions those three notes use piecemeal and records which of their results hold when feeds are rankings over all participants. Nothing here is a new theorem, and the model as a whole is not in Lean.

## Details

### The model
- **Market.** Two sides $I$ and $J$. User $\ell$'s candidates $C_\ell$ are the other side. $\ell$ has private values $v_\ell(x)\ge0$, wants at most $k_\ell$ partners (a top-$k_\ell$ valuation), and pays $c$ per kept match and $d\le c$ per dropped one. Profile $x$ is *acceptable* if $v_\ell(x)>c$.
- **Prior.** Values are independent across ordered pairs. The platform knows their distributions, in particular $p_{\ell x}=\Pr[v_\ell(x)>c]$, and never sees a value unless it queries an oracle.
- **Patience.** $\ell$ examines $R_\ell$ profiles, with $\Pr[R_\ell\ge r]=\alpha^\ell_r$ non-increasing in $r$. Patience is independent of values, of swipes and of what is shown.
- **Ranking policy.** At every moment the platform holds, for each user $\ell$, a total order $\sigma_\ell$ over the candidates $\ell$ has not swiped on. $\ell$ examines the top entry and swipes like or pass; the platform may then re-rank the rest. This repeats until $R_\ell$ profiles are examined. $\sigma_\ell$ may depend on the platform's coins, the prior and the history of everyone's swipes.
- **Matches.** A pair matches if each examined and liked the other, unless the platform declines the mutual like by a rule that uses the same information as the ranking.
- **Conversations and payoffs.** Each user keeps or drops each match, and a conversation is a match both keep. $\ell$'s payoff is the value of its conversations, minus $c$ per conversation and $d$ per match it drops.
- **Truthful.** *Sincere* swiping likes exactly the acceptable profiles examined. A policy is *exactly truthful* if sincere swiping is a best strategy for every realization of the coins, the patience draws and the others' strategies.

### Special cases
- **Round-based displays** ([[Dating Heuristic]], screened DH). Patience is a fixed number $K_\ell$ per round, so order within a round is irrelevant and the policy is a choice of $K_\ell$ profiles.
- **Hinge's flow.** An initiator's feed ranks all responders. A responder's feed ranks only the initiators who liked them.
- **Both roles.** Every user's feed ranks every candidate, so a mutual like can form in either order.

### One user's view is a swipe tree
Fix the coins, the patience draws and the others' strategies. User $\ell$ then sees a first profile, a second one that depends on the first swipe, and so on for $R_\ell$ steps, and ends with a set of matches among the profiles it liked. That is a swipe tree in the sense of [[The Live-Set Theorem for Truthful Swiping]]. Conversely every swipe tree is the feed of some ranking policy with patience equal to the tree's depth.
- So a result proved for every swipe tree holds for every ranking policy.
- **Scrolling at will.** If examining is free and the user chooses when to stop, stopping is the same as passing on the rest. This is the case $R_\ell=|C_\ell|$.

### What ranking changes for the platform
- **Reach.** The profiles in the first $R_\ell$ positions of the realized feed.
- **Exposure.** $e_\ell(x)=\sum_r\alpha^\ell_r\Pr[x\text{ at rank }r]$, the probability that $\ell$ examines $x$.
- **Constraint.** For a ranking drawn before the session, a vector $e$ is achievable iff $\sum_{x\in T}e(x)\le\alpha_1+\dots+\alpha_{|T|}$ for every set $T$, with equality for $T=C_\ell$ *(not in vault, general knowledge: Rado's theorem on convex hulls of permutations)*. Round-based displays are the case $\alpha=(1,\dots,1,0,\dots)$, where this reads $\sum_xe(x)\le K$ and $e\le1$.

### Which results hold
| Result | In the ranked-feed model |
| --- | --- |
| Theorem A (live set) and Theorem A′ | As stated: they are about swipe trees |
| Theorem B ($d$ per extra match) | As stated, for any ranking policy under which the profiles that would match $\ell$ do not depend on $\ell$'s swipes |
| Theorem E (keep-best with an oracle) | As stated |
| Theorem C (responder queue) | With exposures $e_{ij}$ in place of display probabilities, and only the first $k_i$ positions of an initiator's feed able to match. The Lean statement is in terms of mutual-like probabilities and covers this |
| Theorem C′, the two-cap lemma, Theorem F | Already ranking results: the queue is ranked and the responder examines a prefix |
| Theorem G (screened queue) | Proved only when initiators examine all $k_i$ of their slots |
| Theorem D, Propositions P and T | Fixed feed lengths: the case of deterministic patience |

### Theorem A for a ranking over everyone
A ranking policy is exactly truthful for $\ell$ iff, in every realization, at most $k_\ell$ profiles in $\ell$'s reach would match $\ell$, and which ones does not depend on $\ell$'s swipes.
- **A full ranking is a shortlist plus filler.** If $\ell$ may scroll through everyone, at most $k_\ell$ candidates in the whole pool can be live. Re-ranking on $\ell$'s own swipes may only reorder the rest.
- **What makes a full ranking useful.** Theorem B: a ranking that ignores $\ell$'s own swipes costs $d$ per match beyond $k_\ell$. Theorem E: with an oracle the cap disappears.

## Related
- [[Swipe Rounds versus Ranked Feeds]]: a plain-language comparison of this model with the round-based one.
- [[The Live-Set Theorem for Truthful Swiping]]: swipe trees, Theorems A and B.
- [[Welfare of Truthful Feeds in the Two-Cost Model]]: the keep stage, Theorems C, C′ and D, Proposition T.
- [[Queries and the Live-Set Theorem]]: Theorems E, F and G.
- [[Position-Aware Reciprocal Re-Ranking and Dual Pacing]]: a position-aware model of the platform's optimization, with prices and budgets. It does not define users' strategies.

## Gaps
- **Both roles.** Only Theorems A, B and E apply. Swipes are truthful up to $d$ per extra match, the keep stage is a coordination game, and there is no welfare guarantee.
- **Costly scrolling.** With a cost per profile examined, when to stop depends on beliefs about what lies below. The theorems do not cover it.
- **Re-shown profiles.** Each profile is shown to a user at most once and a swipe is final.
- **Position changing the swipe.** Position affects only whether a profile is examined.
- **Theorem G with decaying attention** inside the initiator's $k_i$ slots.
