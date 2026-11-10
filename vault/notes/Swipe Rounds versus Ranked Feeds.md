---
type: synthesis
question: "How does the swipe version of the dating model (the platform picks a set of profiles each round) differ from the ranking version (the platform ranks all candidates), and what changes in the project's results?"
created: 2026-11-11
updated: 2026-11-11
tags: [dating/platforms, game-theory/incentives, research/project]
aliases: [swipe version, ranking version, swipe rounds, round-based display model, swipe model versus ranking model]
sources: ["[[Rios 2026 - The Dating Heuristic]]"]
origin: claude
status: seed
---
# Swipe Rounds versus Ranked Feeds

> [!question] How does the swipe version of the dating model (the platform picks a set of profiles each round) differ from the ranking version (the platform ranks all candidates), and what changes in the project's results?

## Answer

**Summary**
- **Same market, different control.** The two versions have the same users, values, likes and matches. They differ in what the platform chooses and how a user consumes it.
- **The swipe version is a special case.** It is the ranking version with patience fixed at $K$, where order stops mattering.
- **One user's view is the same in both.** Either way the user faces a sequence of profiles in which the next may depend on earlier swipes: a swipe tree. Theorems A, B and E are proved for any swipe tree.
- **What changes** is the meaning of "at most $k$", the platform's optimization, and the constant in the guarantee.

### The two versions
- **Swipe version (rounds).** Each round the platform hands the user a set of $K$ profiles, and the user swipes on every one. This is the model of [[Dating Heuristic]], and the project used it through [[Truthful Swiping with an LLM Oracle]] and [[Query Budgets in Screened DH]].
- **Ranking version (feed).** The platform orders every candidate into one list. The user starts at the top and swipes down until their patience runs out. The platform does not know how far they will scroll. [[Ranked-Feed Model of the Dating Market]] has the formal statement.

| | Swipe version | Ranking version |
| --- | --- | --- |
| What the platform chooses | a set of $K$ profiles per round | an order over all candidates |
| What the user examines | all $K$ | the top of the list, as far as patience goes |
| Does order matter | no | yes: higher is more likely to be seen |
| What limits the platform | $K$ slots per round | attention: the top spot is always seen, lower spots less often |
| When it can react to swipes | between rounds | after every swipe, by re-ranking the rest |
| Real-world analogue | a daily batch of suggestions | an endless scrolling feed |
| In the project | DH, screened DH, Q-SDH | the responder queue, Theorems C′, F, G |

### Example
Six candidates: Ana, Ben, Cal, Dee, Eli, Fay.
- **Swipe version, $K=2$.** The platform shows Ben and Eli. The user sees both for sure.
- **Ranking version.** The platform orders them Ben, Eli, Ana, Cal, Dee, Fay. Suppose the user looks at one profile with probability 0.5, three with probability 0.3 and all six with probability 0.2. Then Ben is seen always, Eli and Ana half the time, and the last three 20% of the time.

The swipe version buys certainty for two people. The ranking version spreads a fixed amount of attention down a list.

### What stays the same
- **Theorem A.** Exact truthfulness forces a fixed shortlist of at most $k$ people who can match the user.
- **Theorem B.** Going over $k$ costs $d$ per extra match.
- **Theorem E.** A truthful oracle removes the cap.

### What changes
- **What "at most $k$" restricts.** In the swipe version, $k$ of the profiles shown. In the ranking version, $k$ of the profiles the user could reach by scrolling, so a full ranking becomes a shortlist of $k$ plus filler.
- **The platform's optimization.** Slots become exposure. The linear programs keep their objective and change the constraint on what a feed can deliver.
- **The guarantee.** The swipe version loses one factor, $c_K$, for the cap on what is shown (R1 in [[Match Quality in the Dating Heuristic Framework]]). The ranking version with partial scrolling loses two, $c_kc_m$: one for how many the user keeps and one for how far they look (the two-cap lemma in [[Welfare of Truthful Feeds in the Two-Cost Model]]).

### Variants inside the ranking version
- **Hinge's flow.** Initiators get a ranking of everyone; responders get a ranking of only the people who liked them. The queue theorems (C, C′, D, F, G) are for this.
- **Both roles.** Everyone gets a ranking of everyone. Only Theorems A, B and E apply, and there is no welfare guarantee.

## Evidence
- [[Ranked-Feed Model of the Dating Market]]: the ranking model, the reduction to swipe trees, exposure, and the table of which results carry over.
- [[The Live-Set Theorem for Truthful Swiping]] (Theorems A, B), [[Queries and the Live-Set Theorem]] (Theorem E, Theorems F and G), [[Welfare of Truthful Feeds in the Two-Cost Model]] (Theorems C, C′, the two-cap lemma).
- [[Rios 2026 - The Dating Heuristic]] and [[Dating Heuristic]]: the round-based model with display caps.
- The example's exposures are arithmetic on the stated patience distribution: $1$, $0.5$, $0.5$, $0.2$, $0.2$, $0.2$.

## Gaps
- **No direct welfare comparison.** The vault has guarantees for each version against its own benchmark, not a statement of how much a platform gains or loses by ranking instead of batching.
- **The swipe version's guarantees were not re-derived in exposure form.** Screened DH and Q-SDH are stated with display caps only.
- The gaps of [[Ranked-Feed Model of the Dating Market]] apply: both roles, costly scrolling, re-shown profiles.
