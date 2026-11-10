---
type: synthesis
question: "If a ranked dating feed may use likes beyond consent (feeds, prices and matches can react to them), can top-k users be made to swipe truthfully, and what should truthful mean for them?"
created: 2026-11-06
updated: 2026-11-09
tags: [dating/platforms, game-theory/incentives, matching/quality, online-algorithms, research/project]
aliases: [like-aware feeds, like-aware ranking, value-monotone swiping, likes are your favorites, Elo banding, reply-odds banding, Likes You queue, feedback rule]
sources: ["[[Rios 2026 - The Dating Heuristic]]", "[[Kanoria 2021 - Facilitating the Search for Partners on Matching Platforms]]"]
origin: claude
status: seed
---
# Truthful Top-k Swiping in Like-Aware Feeds

> [!question] If a ranked dating feed may use likes beyond consent (feeds, prices and matches can react to them), can top-k users be made to swipe truthfully, and what should truthful mean for them?

> [!note] Preliminary
> Written 2026-11-06 while reviewing the reciprocal re-ranking framework of [[Position-Aware Reciprocal Re-Ranking and Dual Pacing]] and [[Next-Generation Continuous Reciprocal Re-Ranking]]. It builds on [[Truthful Swiping with an LLM Oracle]] (Theorem 1, Propositions 4–6) and [[Strategic Users in the Dating Heuristic Framework]] (S4, S6, Proposition 1). Claims A–C and the feedback rule are informal proofs, not in Lean. As in those notes, a top-$k$ user's utility is the sum of their $k$ best match values minus $c$ per match, and a profile is *acceptable* if its value exceeds $c$.

> [!tip] Step-by-step guide
> [[Top-k Swiping Incentives Guide.html]] explains every result twice, in short and in detail, with examples. Obsidian doesn't display HTML, so the link opens it in your web browser.

## Answer

**Summary.**
- **Not as the re-ranker is written.** Three of its realistic features each break sincere swiping: top-$k$ satiation in a long feed, a binding like budget, and prices that react to the user's own likes.
- **Consent-only likes can't fix top-$k$ cheaply.** Under swipe-local policies, a top-$k$ user is truthful only if they see at most $k$ acceptable profiles. Without an oracle, that caps top-1 welfare near $2p\,\mathrm{OPT_{IR}}$ (Lean-checked). This is the reason to design rankings that use likes on purpose.
- **Using likes can't rescue the sincere threshold either (Claim A).** With yes/no likes, once $k+1$ acceptable profiles could match, no mechanism that caps matches at $k$, wastes none, and can't see values makes "like everyone acceptable" dominant. No later reward based on the like count fixes it.
- **Change the target.** For top-$k$ users, truthful should mean *value-monotone*: on each batch, like your top $m$ by value. The mechanism sets $m$.
- **What achieves it:**
  - *Claim B:* equal reply odds within a batch (Elo-style banding) make some best response value-monotone, on average.
  - *Feedback rule:* if reactions to likes depend only on the count and are penalties, nobody likes below cost.
  - *Claim C:* in a "Likes you" queue every like is a sure match, so picking your top $k$ is dominant within a round.
- **Design.** One side proposes from banded feeds with at most $k$ likes outstanding; the other side picks from its queue. [[Gender-Skewed Reciprocal Matching and Asymmetric Pacing]] proposes this structure for skewed markets (the short side picks), and Claim C is why it is truthful for the side that picks.

### The re-ranker as written
- **Model** ([[Position-Aware Reciprocal Re-Ranking and Dual Pacing]]). Score $S_{ij}=\phi_{ij}\big(\phi_{ji}(q_{ij}-\lambda_j)-\mu_i\big)$; feeds of 10–100 cards with position decay; a daily like budget $B_i$; satiation $k=1$–3; prices updated online from likes. There $q_{ij}$ is a conversation probability, so values are written $v_{ij}$ here.
- **Satiation.** By Theorem 1 of [[Truthful Swiping with an LLM Oracle]], under swipe-local displays sincere swiping is dominant for a top-$k$ user iff they see at most $k$ acceptable profiles. Long feeds show many more.
- **Budgets.** With more than $B$ acceptable cards, sincere swiping is infeasible (Proposition 5(c) there). Best responses save likes for later cards and shade toward profiles likely to like back ([[Strategic Users in the Dating Heuristic Framework|S4]]), so likes measure attainability as well as value.
- **Prices that react to your own likes.** The budget price updates as $\mu_i\leftarrow\max\{0,\mu_i+\eta(\text{likes}-B_i/T)\}$ and enters scores as $-\phi_{ij}\mu_i$, so it reorders the user's later feeds. In the counterexample below, $\eta=0.5$, $B_i/T=0.2$, and session 2 shows one card, $b$ or $c$, with $S_{ib}=0.9(0.5-\mu_i)$ and $S_{ic}=0.3(1-\mu_i)$. Liking card $a$ in session 1 sets $\mu_i=0.4$ and puts $c$ on top; passing keeps $\mu_i=0$ and $b$ on top. Everyone likes back.

| Net values $(a,b,c)$ | Sincere play | Earns | Deviation | Earns |
| --- | --- | --- | --- | --- |
| $(-0.5,\,-1,\,+5)$ | pass $a$, shown $b$, pass | 0 | like $a$, shown $c$, like | 4.5 |
| $(+0.5,\,+5,\,-1)$ | like $a$, shown $c$, pass | 0.5 | pass $a$, shown $b$, like | 5 |

- The others are sincere in this example, so it rules out ex-post IC, not just DSIC.
- **What survives.** With $\lambda$, $\mu$ and $\phi$ frozen over the horizon and no rule that depends on a user's own matches, every feed is exogenous.
  - Sincere swiping is then ex-post IC for additive users whose budgets don't bind.
  - For top-$k$ users it is an $\varepsilon$-Bayes–Nash equilibrium with $\varepsilon_i=c_i\,\mathbb E(|M_i|-k)^+$ (Proposition 4 of [[Truthful Swiping with an LLM Oracle]]).
  - Over three or more sessions it is not DSIC in the universal sense, because others' later likes can react to your earlier ones. [[Truthful Swiping with an LLM Oracle#T5. Dominant strategies (DSIC), not just ex post|T5]] relies on the two-period timing.

> [!warning] Conflict
> [[Position-Aware Reciprocal Re-Ranking and Dual Pacing]] (comparison table) and `reciprocal_reranking_monograph.tex` (its DSIC theorem) say sincere swiping is dominant under the like budget $B_i$. [[Truthful Swiping with an LLM Oracle]] (Theorem 1, Proposition 5(c)) implies it is not, for top-$k$ users or when the budget binds, and the reacting $\mu_i$ breaks it even for additive users (above). The monograph's proof treats each like as additive and independent of the others. Likewise, [[Gender-Skewed Reciprocal Matching and Asymmetric Pacing]] says scarcer likes force men to swipe truthfully; with a binding budget sincere swiping is infeasible, and likes shade toward attainable partners.

### Claim A: yes/no likes can't pick your best k
> [!tip] Superseded (2026-11-09)
> [[The Live-Set Theorem for Truthful Swiping]] turns this claim into a characterization. Conditions 2 and 3 are not needed, feeds may be adaptive, and the result covers matroid and general valuations and the two-cost model.

**Statement.** Suppose that on a batch:
1. a user's only input is the set $D$ they like;
2. they get at most $k$ matches, all from $D\cap R$, where $R$ is the set of shown profiles that would match them;
3. if at most $k$ of their likes would match, all of them do;
4. which matches are kept does not depend on their values beyond $D$.

If a batch can contain $k+1$ acceptable profiles that would all match, liking exactly the acceptable set $A$ is not dominant.

*Proof.* Let $M$ be the set kept when the user likes $A$; some acceptable would-match $y$ is not in $M$. By (4), choose values with $y$ the favorite and some $z\in M$ barely acceptable. Liking $M-z+y$ (or $M+y$ if $|M|<k$) matches all of them by (3), a gain of $v_y-v_z>0$. $\square$
- **Ways out.** Dropping (2) allows overshoot (Theorem 1(b)); dropping (3) wastes matches; dropping (4) needs an oracle; dropping (1) needs ranked likes or roses. Never showing $k+1$ would-matches is Proposition 6, at about $2p$ of the optimum.
- **Rewards based on the like count.** Take a later reward $F(n)$ for $n$ likes, and $k=1$. A batch of $n+1$ acceptable would-matches needs $F(n+1)-F(1)\ge v_y-v_z$. A batch with one profile worth $c+\varepsilon$ and $n$ worth $c-\varepsilon$, all would-matches, needs $F(n+1)-F(1)\le2\varepsilon$. No $F$ meets both.
- This extends Theorem 1(b) of [[Truthful Swiping with an LLM Oracle]] beyond swipe-local policies.

### The new target: value-monotone swiping
A strategy is *value-monotone* if, on every batch, it likes the top $m$ profiles by value, for some $m$ that may depend on the batch.
- It is what top-$k$ users do with sure matches ([[Strategic Users in the Dating Heuristic Framework]], Proposition 1(a)).
- It reveals the top of each user's ranking, and it leaves $m$ to the mechanism.
- It gives up learning exactly who clears the cost $c$.

### Claim B: equal reply odds give value-monotone best responses
**Statement.** Suppose:
- every profile in a batch would like the user back independently with the same probability $\varphi$;
- the user's matches from the batch are $D\cap R$, within their free like slots;
- the platform's later treatment depends on the batch only through how many the user liked and how many matched.

Then, for any utility that increases with match values and charges $c$ per match (top-$k$, additive), some expected-utility best response is value-monotone.

*Proof.* If $x\in D$, $y\notin D$ and $v_y>v_x$, swap them, and swap their reply coins, which have the same law. In every outcome the match set has $y$ in place of $x$ with the same counts, so the future is unchanged and utility weakly rises. Repeat. $\square$
- **Unequal odds break it.** With one like left and cost 1, a profile worth 10 that likes back 10% of the time is worth $0.9$ in expectation, and one worth 3 at 90% is worth $1.8$, so the user likes the one they value less (S4).
- **Elo-style banding supplies equal odds.** Show user $i$ only profiles whose $\phi_{ji}$ is close to a level set for $i$: a constraint on the fluid LP's exposures. Feeds of similar desirability are what Elo-style scores are used for ([[Kanoria 2021 - Facilitating the Search for Partners on Matching Platforms]] mentions Tinder's hidden Elo).
- **On average only.** Claim A rules out dominance.

### The feedback rule
**Statement.** In Claim B's setting, suppose the user's best future utility $F(n)$ depends only on the number $n$ of likes and never increases with $n$. Then some best response contains no unacceptable profile. With Claim B, the user likes their top $m$, all of them acceptable.

*Proof.* Dropping an unacceptable $w$ removes a match worth at most $v_w-c<0$, since adding $w$ raises the top-$k$ sum by at most $v_w$, and moves the future to $F(n-1)\ge F(n)$. $\square$
- $\mu_i$ fails the rule: it reorders feeds, and whether that helps depends on the user's values (the counterexample above).
- Penalties that hurt every user, such as fewer cards or lower placement after over-liking, satisfy it.
- What it prevents: likes on unwanted profiles to steer the feed, which become ghosted matches.

### Claim C: sure-match queues
**Statement.** A responder who picks at most $s$ (their free slots) from a queue of profiles that already liked them, at the end of a round, does best in every outcome by picking their top $\min(s,\#\text{acceptable})$ by value.

*Proof.* This is Claim B with $\varphi=1$, so the swap holds outcome by outcome; while below $k$, an acceptable pick adds $v-c>0$. It is the argument of Proposition 1(a) of [[Strategic Users in the Dating Heuristic Framework]]. $\square$
- It is dominant within a round. Across rounds a responder may wait for a better queue, which only changes $m$.
- Initiators can't get the same guarantee: the queue is certain only because they liked first, so Claim A applies to them.

### The design
- **Initiators** get a discovery feed ranked by the fluid LP and banded by reply odds, with at most $k$ likes outstanding, so no one gets more than $k$ matches. Value-monotone on average, by Claim B and the feedback rule.
- **Responders** see a "Likes you" queue decided at the end of each round. Picking the top $k$ is dominant (Claim C).
- **Prices.** $\lambda_j$ stays, since it aggregates many users' likes. $\mu_i$ becomes a penalty on the like count.
- **Given up.** A dominant strategy for initiators, and welfare lost to banding. *(Not in vault, general knowledge: Alcalde & Barberà 1994 show that no one-to-one matching mechanism is strategy-proof, individually rational and Pareto efficient, so some side has to give.)*
- **Relation to [[Truthful Swiping with an LLM Oracle|screened DH]].** SDH reaches DSIC for the sincere threshold by paying for oracle calls. This design needs no oracle and settles for value-monotone likes.

## Evidence
- [[Truthful Swiping with an LLM Oracle]]: Theorem 1 (`sincere_best`, `sincere_not_best`, `costSeparable_topK_iff`, `swipeLocal_dsic_topK`), Proposition 4 (`topK_regret_le`, `topK_regret_attained`, `excess_le`), Proposition 5(c), Proposition 6 (`zeroQuery_topK_dsic_iff`, `prop6b_asymp`). Lean names are from `lean/README.md`.
- [[Strategic Users in the Dating Heuristic Framework]]: S4 (budgets shade likes), S6 (selectivity-weighted displays break sincerity), Proposition 1(a) (sure-match responses).
- The re-ranking model and its claims: [[Position-Aware Reciprocal Re-Ranking and Dual Pacing]], [[Next-Generation Continuous Reciprocal Re-Ranking]], [[Gender-Skewed Reciprocal Matching and Asymmetric Pacing]].
- The $\mu_i$ counterexample is exact arithmetic; a short script reproduced it (not committed).
- Claims A–C and the feedback rule are informal proofs written 2026-11-06, not in Lean.
- *Not in vault (general knowledge):* Alcalde & Barberà 1994. Deferred acceptance is strategy-proof for proposers who want one match (Dubins & Freedman 1981; Roth 1982; see [[Deferred Acceptance]]). In large markets with short lists, receivers gain little from lying (Immorlica & Mahdian 2005; Kojima & Pathak 2009; Ashlagi, Kanoria & Leshno 2017).

## Gaps
- **Welfare of the design**, against the best policy facing value-monotone users. Users' thresholds depend on the feed, a fixed point already open as Proposition 4(d) of [[Truthful Swiping with an LLM Oracle]].
- **Approximate bands.** The loss from value-monotone play when reply odds within a batch vary by a factor $1\pm\delta$.
- **Attention decay.** In a feed, reaching a later card depends on not stopping earlier, so reply events are not independent; Claim B's swap needs adjusting.
- **The cost of banding**, measured on the speed-dating data with the re-ranking simulator.
- **Lean.** Claims A–C should fit beside `TruthfulSwiping.lean` and `SwipeLocal.lean`.
- **Richer messages.** Ranked likes or roses with deferred acceptance, and their incentives in large markets.
- **Learning from which profiles you like** (retraining $\phi$) is outside Claim B's count-only assumption.
