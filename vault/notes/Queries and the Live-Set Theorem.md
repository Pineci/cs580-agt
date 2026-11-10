---
type: synthesis
question: "If the platform can query a truthful oracle for users' values, does the barrier of Theorem A go away, and is there a ranked-feed algorithm that uses queries, possibly under a budget?"
created: 2026-11-10
updated: 2026-11-11
tags: [dating/platforms, game-theory/incentives, matching/quality, research/project]
aliases: [Theorem E, Theorem F, Theorem G, keep-best rule, queried queue, screened queue, lazy queries, slot rule, query window]
sources: ["[[Rios 2026 - The Dating Heuristic]]"]
origin: claude
status: seed
---
# Queries and the Live-Set Theorem

> [!question] If the platform can query a truthful oracle for users' values, does the barrier of Theorem A go away, and is there a ranked-feed algorithm that uses queries, possibly under a budget?

> [!note] Preliminary
> Written 2026-11-10. It continues [[The Live-Set Theorem for Truthful Swiping]] (Theorems A, B) and [[Welfare of Truthful Feeds in the Two-Cost Model]] (Theorems C, C′), using the oracle of [[Truthful Swiping with an LLM Oracle]]. Theorem E and the guarantee of Theorem G are Lean-checked. Theorem F's truthfulness and its per-responder bound $c_kc_B$ (the two-cap lemma) are Lean-checked.

## Answer

**Summary**
- **Theorem E.** If the platform knows a user's values on the live set, it can keep the user's best $k$ mutual likes itself. Sincere swiping is then dominant for a live set of any size, and the user gets their full-information optimum. The cap of $k$ is gone.
- **Lazy queries.** The platform needs a query only when more than $k$ liked profiles would match, one per such profile.
- **Only where queried.** A live profile whose value the platform has not queried still holds one of the $k$ slots.
- **What queries do not fix.** The live set must still ignore the user's swipes, two users over their limit still collide, and the oracle's reports must be truthful.
- **Theorem F (queried queue).** In the responder queue of Theorem C′, querying on overshoot makes both sides exactly truthful with the same guarantees. A budget of $B$ queries per responder is a window of $B$ admirers, and the factor is $c_kc_B$.
- **Theorem G (screened queue).** Queries can also screen who an initiator is shown. Under per-user budgets the mechanism gets $c_k^2$ of an LP that bounds every such mechanism. On the random market each call buys about $p$ of the optimum.
- **Where queries raise welfare.** On the responder side, by widening that window. On the initiator side, by screening who is shown.

### Setting
One top-$k$ user with values $q$, costs $c\ge0$ to keep a match and $d\ge0$ to drop one, and acceptable set $A=\{x:q_x>c\}$. A set $R$ of profiles would match the user if liked; it does not depend on the user's swipes and may have any size. The platform can ask a truthful oracle for $q_x$.

### Theorem E: the keep-best rule
**Rule.** When the user likes $X$, the platform matches them with the $k$ most valuable acceptable members of $X\cap R$ (all of them if there are fewer) and declines the rest.

**Statement.**
- **(a) Dominant.** Sincere swiping is a best strategy for every $R$, of any size.
- **(b) Optimal.** A sincere user's outcome is at least as good as every subset of $R$. Its utility is the top-$k$ net value of $A\cap R$, and the user never drops a match.
- **(c) Lazy.** If at most $k$ liked profiles would match, match them all without a query. Otherwise query each liked member of $R$. A sincere user triggers queries only when $|A\cap R|>k$, and then $|A\cap R|$ of them.
- **(d) Slots.** Suppose only the profiles in $Q$ can be queried. Fix a set $S_U\subseteq R\setminus Q$ of at most $k$ unqueried live profiles without looking at the user's swipes. Match the user with the liked members of $S_U$ and with the $k-|S_U|$ most valuable acceptable liked members of $R\cap Q$. Sincere swiping is dominant.

*Proof.* (a), (b) Any set of matches inside $R$ is worth at most the top-$k$ net value of its acceptable members, which is at most the top-$k$ net value of $A\cap R$. A sincere user gets a best set of at most $k$ members of $A\cap R$ and keeps all of them, which is worth exactly that. (c) Every outcome of the lazy rule is a subset of $R$, and a sincere user's outcome is the same as under the rule. (d) The user never has more than $k$ matches, so utility is a sum over matches. The unqueried part is largest under sincere swiping by Theorem A, and the queried part by (a). $\square$

**Why Theorem A no longer binds.** Its proof holds one decision tree fixed while the user's values vary. A platform that sees values can use a different tree for each type. In shortlist terms, the live set becomes "your best $k$ among the people who like you back".

**What still binds.**
- **Unqueried profiles keep their slots.** Take $k=1$, Alice queried and worth 5, Bob unqueried and live. If a pass on Bob hands the slot to Alice, a user who values Bob at 1.1 passes on him. So (d) cannot reuse a slot the user leaves empty.
- **The live set must still ignore the user's swipes.** A window of "the first $B$ admirers the user likes" lets a user pass on an early admirer to bring a better one into the window.
- **No converse.** With known values the platform can also punish any departure from the swipes it expects, so rules of other shapes can be dominant too. I have no characterization like Theorem A for the queried case.
- **Reports.** Everything assumes a truthful oracle. If the user or their agent supplies the values, the incentive problem moves there (T5 in [[Truthful Swiping with an LLM Oracle]]).
- **Two sides.** If both users of a mutual like are over their limit, one keep-best rule can decline someone the other kept. Resolving that with second chances is [[Deferred Acceptance]], and no stable rule is truthful for both sides *(not in vault, general knowledge: Roth 1982)*.

### Theorem F: the queried queue
**Setting.** That of Theorem C′ in [[Welfare of Truthful Feeds in the Two-Cost Model]]: initiators browse, responder $j$ looks at the first $R_j$ admirers of a queue ranked by acceptance probability. Add an oracle for responders' values and a budget of $B_j$ queries per responder.

**Mechanism.** Queue-DH as in Theorem C′, with two changes.
1. **Window.** Responder $j$ is shown the first $E_j=\max(B_j,k_j)$ admirers of the queue.
2. **Keep-best, lazily.** If $j$ likes at most $k_j$ of them, all are matched. Otherwise the platform queries $j$'s value for each one $j$ liked and keeps the best $k_j$.

**Statement.**
- **(a) Truthful.** Sincere swiping is exactly dominant for initiators and for responders, and nobody drops a match.
- **(b) Conversations.** $\mathbb E[\text{conversations}]\ge\sum_j\sum_m w^j_m\,\gamma(k_j,m\wedge E_j)\,\min\big(k_j,V^j_{m\wedge E_j}(x)\big)$, with $\gamma$ and $V$ as in Theorem C′. With full attention that is $c_{k_j}c_{B_j}\min(k_j,V^j_{B_j})$ per responder. The sum without the factor $\gamma$ bounds every mechanism in which responder $j$ considers at most $E_j$ admirers.
- **(c) Queries.** None for initiators. Responder $j$ uses $L_j$ queries if $L_j>k_j$ and none otherwise, where $L_j\le E_j$ counts the acceptable admirers in the window.
- **(d) Against no queries.** Theorem C′ gives the same conversation bound with a window of the same size, but there a responder loses $d$ per drop. Queries remove that loss and make responders exactly truthful.

*Proof.* (a) Initiators are shown at most $k_i$ profiles, and whether $j$ keeps $i$ does not depend on $i$'s other swipes (Theorem C(a); being declined is free). The window is a set of admirers, fixed by the others' likes and by $R_j$, so it is a live set that $j$'s swipes cannot change; apply Theorem E(c). (b) The two-cap lemma with look limit $m\wedge E_j$. (c) By construction. $\square$

- **A budget of at most $k$ is the no-query case.** A window of $k$ admirers is exactly truthful by Theorem A.
- **One top-1 responder, 12 admirers, acceptance probability 0.3:**

| Budget $B$ | Conversation | Expected queries |
| --- | --- | --- |
| 1 | 0.30 | 0 |
| 2 | 0.51 | 0.18 |
| 4 | 0.76 | 0.79 |
| 8 | 0.94 | 2.20 |
| 12 | 0.99 | 3.53 |

### Theorem G: screening initiator feeds
**Setting.** That of Theorem C (responders look at their whole queue), with an oracle for both sides' values and budgets in expectation: at most $B_j$ calls of responder $j$'s oracle and $B_i$ of initiator $i$'s.

**Three kinds of display** of $j$ to $i$.
- *Unscreened:* no query. A mutual like with probability $p_{ij}p_{ji}$.
- *Screened:* the platform first asks whether $j$ would accept $i$ and shows $j$ only on a yes. A mutual like with probability $p_{ij}$.
- *Double-screened:* after that yes it also asks whether $i$ would like $j$, and shows $j$ only on a second yes. A mutual like for sure.

**Plan.** $\mathrm{LP}_Q=\max\sum_j\min(k_j,\mu_j)$ with $\mu_j=\sum_i\big(u_{ij}p_{ij}p_{ji}+s^1_{ij}p_{ij}+s^2_{ij}\big)$, subject to
$$u_{ij}+\tau_{ij}\le1,\quad s^1_{ij}+g_{ij}\le\tau_{ij}p_{ji},\quad s^2_{ij}\le g_{ij}p_{ij},\quad \sum_j\big(u_{ij}+s^1_{ij}+s^2_{ij}\big)\le k_i,\quad \sum_i\tau_{ij}\le B_j,\quad \sum_jg_{ij}\le B_i.$$
Here $\tau_{ij}$ and $g_{ij}$ are the probabilities of asking $j$'s and then $i$'s oracle about the pair, and $u,s^1,s^2$ those of proposing $j$ to $i$ by each kind.

**Mechanism (screened queue).**
1. Solve $\mathrm{LP}_Q$.
2. For each initiator and each responder independently, draw the pair's kind with the plan's probabilities and make its queries. If they pass, $j$ is *proposed* to $i$.
3. Show $i$ at most $k_i$ of the proposed profiles, chosen by a balanced selection rule (for example a random $k_i$ of them).
4. Responders see every admirer, and the platform keeps each responder's best $k_j$.

**Statement.**
- **(a) Truthful.** Initiators are exactly truthful. So are responders if the platform also queries their unscreened admirers on overshoot (at most one more call per liked unscreened admirer); otherwise they lose $d$ per drop.
- **(b) Conversations.** $\mathbb E[\text{conversations}]\ge\gamma\,c_{\min_jk_j}\,\mathrm{LP}_Q$, where $\gamma=\tfrac12$ for the random rule and $\gamma=c_{\min_ik_i}$ for a $c_k$-balanced rule.
- **(c) Bound.** $\mathrm{LP}_Q$ bounds every one-directional mechanism that shows each initiator at most $k_i$ profiles, meets the budgets in expectation, and asks the responder's oracle first on any pair it screens.
- **(d) Ends of the range.** With no budget this is $\mathrm{LP}_1$ of Theorem C. With unlimited budgets every display is double-screened, which is the regime of screened DH.

*Proof.*
- **(b)** The profiles proposed to $i$ are independent with probabilities summing to at most $k_i$. A $\gamma$-balanced rule shows each proposed profile with probability at least $\gamma$, looking only at which profiles are proposed ([[Max-Min Match Quality and Egalitarian Matching]]: the random rule is $\tfrac12$-balanced and $c_k$-balanced rules exist; both Lean-checked). So $i$ brings $j$ a mutual like with probability at least $\gamma$ times its term in $\mu_j$, independently across initiators. Then $\mathbb E\min(k_j,N_j)\ge c_{k_j}\min(k_j,\gamma\mu_j)\ge\gamma c_{k_j}\min(k_j,\mu_j)$.
- **(c)** For such a mechanism let $u,\tau,s^1,g,s^2$ be the probabilities of the corresponding events for each pair. An answer is independent of the decision to ask for it, which gives the three per-pair constraints. A conversation needs a display and a mutual like; apply Jensen as in Theorem C.
- **(a)** As in Theorems C and E. $\square$

**The random market, $p=0.01$** (every like has probability $\sqrt p$; the optimum matches almost everyone):

| Calls per responder | Calls per initiator | $\mathrm{LP}_Q$ share | Mechanism |
| --- | --- | --- | --- |
| 0 | 0 | 0.010 | 0.006 |
| 3 | 0 | 0.037 | 0.023 |
| $1/\sqrt p=10$ | 0 | 0.100 | 0.061 |
| 30 | 3 | 0.307 | 0.176 |
| $1/p=100$ | 10 | 1.000 | 0.469 |

- **Each call buys about $p$.** Screening by the responder's value alone tops out at $\sqrt p$. A constant share needs about $1/p$ calls per responder, in line with the query lower bound (Theorem 4 of [[Truthful Swiping with an LLM Oracle]]).
- **Here the random rule is $c_1$-balanced** by symmetry, so the guarantee is $c_1^2\approx0.40$ of $\mathrm{LP}_Q$.

### Where queries raise welfare
- **Responder side.** The exactly truthful window grows from $k$ to $B$ (the table).
- **Initiator side.** Initiators stay capped at $k_i$ shown profiles, because any shown profile may match. Queries can keep those slots from being wasted: screened DH shows only pairs that are acceptable both ways and earns $c_K^2$ of the full-information LP, and Q-SDH does so under a per-user budget ([[Truthful Swiping with an LLM Oracle]], [[Query Budgets in Screened DH]]; both Lean-checked).
- **Both, under budgets.** Theorem G screens initiator feeds inside the queue and keeps a factor $c_k^2$ of its LP bound.

## Evidence
- **Lean, 2026-11-10.** `lean/DatingAlgo/LiveSet.lean`: `keepBest_sincere_best` (E(a)), `keepBest_optimal` and `keepBest_util` (E(b)), `keepBest_of_card_le` (E(c): no query when at most $k$ acceptable profiles match), `exists_keepBest`. E(d) is not formalized.
- **Lean, 2026-11-10, queue algorithms.** `lean/DatingAlgo/QueueGuarantees.lean`; `lean/check.sh`: 1039 theorems, none open.
  - *Theorem G(b):* `screenedQueue_ge` (any $\gamma$-balanced rule), `screenedQueue_uniform_ge` ($\tfrac12c_K$), `screenedQueue_exists_ge` ($c_{K'}c_K$). The upper bound G(c) is `conv_le_fluidConv`, with the marginal bound as a hypothesis.
  - *Theorem F:* truthfulness is `keepBest_sincere_best` with the window as live set, and `queue_initiator_truthful`. The conversation bound for the whole queue as window is `queueConv_ge`. For a finite window the factor $c_kc_B$ is the two-cap lemma, `twoCap_ge` in `lean/DatingAlgo/TwoCap.lean` (1092 theorems, none open), stated for one responder's queue.
- **Brute force, 2026-11-10.** `data/scripts/live_set_check.py`, check I; every assertion held.
  - *Theorem E:* keep-best, lazy and slot rules on 3,000 random cases with five profiles and every set of likes. The lazy rule needed no query in 2,203 of them. The two counterexamples above.
  - *Theorem F:* the table, from the two-cap computation of check H.
  - *Theorem G (check J):* 200 random markets with random budgets and the random rule, conversations at least 0.63 of $\mathrm{LP}_Q$ (proved: 0.32); the random-market table, computed exactly.
- [[The Live-Set Theorem for Truthful Swiping]] (Theorems A, B), [[Welfare of Truthful Feeds in the Two-Cost Model]] (Theorems C, C′, the two-cap lemma).

## Gaps
- **A converse for the queried case.** Which rules are dominant when some values are known.
- **Theorem G's bound** covers mechanisms that ask the responder's oracle first. Asking the initiator first needs one more kind of display.
- **Theorem G with partial scrolling.** It assumes responders see their whole queue.
- **Budgets in expectation.** $B_j$ here is a hard cap per responder. Q-SDH's budgets are on expected calls.
- **A noisy or strategic oracle.** Theorem E needs exact, truthful values.
- **Both sides over their limit**, as in the welfare note.
