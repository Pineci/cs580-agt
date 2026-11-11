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

> [!note] Corrected 2026-11-11
> The first version said the swipe version is a special case of the ranking version. That is true only of what a user sees in one sitting. The swipe version also has rounds, and the first version left the clock out.

## Answer

**Summary**
- **They differ in two ways.** In what a user gets in one sitting (a set or a ranked list), and in the clock (synchronized rounds or none).
- **The first difference is a special case.** A set of $K$ is a ranked list with patience fixed at $K$.
- **The second is not.** Rounds are extra structure. A scrolling feed with no rounds is a different model.
- **The incentive theorems ignore both differences.** Theorems A, B and E hold for sets or rankings, with or without rounds.
- **The welfare theorems do not.** Every welfare result in the project assumes rounds or stages.

### Difference 1: what a user gets in one sitting
| | Set | Ranked prefix |
| --- | --- | --- |
| What the platform chooses | $K$ profiles | an order over all unseen candidates |
| What the user examines | all $K$ | the top of the list, as far as patience goes |
| Does order matter | no | yes: higher is more likely to be seen |
| What limits the platform | $K$ slots | attention: the top spot is always seen, lower spots less often |

**Example.** Six candidates: Ana, Ben, Cal, Dee, Eli, Fay.
- *Set, $K=2$.* The platform shows Ben and Eli. The user sees both for sure.
- *Ranked prefix.* The platform orders them Ben, Eli, Ana, Cal, Dee, Fay. Suppose the user looks at one profile with probability 0.5, three with probability 0.3 and all six with probability 0.2. Then Ben is seen always, Eli and Ana half the time, and the last three 20% of the time.

### Difference 2: the clock
| | Synchronized rounds | No rounds |
| --- | --- | --- |
| Who acts when | everyone swipes in round 1, then everyone in round 2 | anyone, at any time |
| When the platform can react | between rounds | after every swipe |
| What a later feed can use | everything from earlier rounds | whatever has happened so far |

### The four combinations
| | Rounds or stages | No rounds |
| --- | --- | --- |
| **Set per sitting** | [[Dating Heuristic]], screened DH, Q-SDH | daily batches at arbitrary times |
| **Ranked prefix per sitting** | the queue theorems (two stages) | a scrolling feed |

The project's welfare results are all in the left column. The bottom-right cell is the ranking over everyone with no rounds.

### What holds everywhere
From one user's seat every cell looks the same: a sequence of profiles in which the next may depend on earlier swipes. That is a swipe tree, whatever the clock (Proposition 1 of [[Ranked-Feed Model of the Dating Market]]). So these hold in all four cells:
- **Theorem A.** Exact truthfulness forces a fixed shortlist of at most $k$ people who can match the user.
- **Theorem B.** Going over $k$ costs $d$ per extra match.
- **Theorem E.** A truthful oracle removes the cap.

### What depends on the cell
- **The meaning of "at most $k$".** With sets, $k$ of the profiles shown. With a ranking the user can scroll through, $k$ of everyone they could reach, so a full ranking is a shortlist of $k$ plus filler.
- **The platform's optimization.** Slots become exposure.
- **The guarantee's constant.** A set costs one factor, $c_K$ (R1 in [[Match Quality in the Dating Heuristic Framework]]). A ranked prefix costs two, $c_kc_m$ (the two-cap lemma in [[Welfare of Truthful Feeds in the Two-Cost Model]]).
- **Whether there is a guarantee at all.** The queue's guarantee, its benchmark and its truthfulness over several rounds each fail under a different clock (Proposition 2 of [[Ranked-Feed Model of the Dating Market]]).

### Variants of the ranked-prefix row
- **Hinge's flow, two stages.** Initiators get a ranking of everyone; then responders get a ranking of the people who liked them. The queue theorems are for this.
- **Both roles, no rounds.** Everyone scrolls a ranking of everyone. Only Theorems A, B and E apply.

## Evidence
- [[Ranked-Feed Model of the Dating Market]]: the model, Proposition 1 (clock-free) and Proposition 2 (clock-dependent), both checked in Lean.
- [[The Live-Set Theorem for Truthful Swiping]] (Theorems A, B), [[Queries and the Live-Set Theorem]] (Theorems E, F, G), [[Welfare of Truthful Feeds in the Two-Cost Model]] (Theorems C, C′, the two-cap lemma).
- [[Rios 2026 - The Dating Heuristic]] and [[Dating Heuristic]]: the round-based model with display caps.
- The example's exposures are arithmetic on the stated patience distribution: $1$, $0.5$, $0.5$, $0.2$, $0.2$, $0.2$.

## Gaps
- **No welfare result without rounds.**
- **No direct welfare comparison** between a set and a ranked prefix against a common benchmark.
- **Screened DH and Q-SDH are stated with display caps only**, not in exposure form.
- The gaps of [[Ranked-Feed Model of the Dating Market]] apply.
