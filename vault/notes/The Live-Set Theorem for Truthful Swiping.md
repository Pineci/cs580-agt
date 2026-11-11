---
type: synthesis
question: "With yes/no swipes and a platform that cannot see values, which mechanisms make sincere swiping a dominant strategy? Does letting the feed react to likes, or charging less for dropped matches, lift the limit of k acceptable profiles for top-k users?"
created: 2026-11-09
updated: 2026-11-11
tags: [dating/platforms, game-theory/incentives, matching/quality, research/project]
aliases: [live-set theorem, Theorem A, Theorem B, top-k barrier, binary-swipe barrier, live set, own-swipe independence, two-cost model, drop cost, general cost functions, cyclic-priority mechanism]
sources: ["[[Rios 2026 - The Dating Heuristic]]"]
origin: claude
status: seed
---
# The Live-Set Theorem for Truthful Swiping

> [!question] With yes/no swipes and a platform that cannot see values, which mechanisms make sincere swiping a dominant strategy? Does letting the feed react to likes, or charging less for dropped matches, lift the limit of k acceptable profiles for top-k users?

> [!note] Preliminary
> Written 2026-11-09. It replaces Claim A of [[Truthful Top-k Swiping in Like-Aware Feeds]] with a characterization and extends Theorem 1 of [[Truthful Swiping with an LLM Oracle]] from swipe-local policies to every mechanism. Theorems A and B are Lean-checked for top-$k$ and additive users (`lean/DatingAlgo/LiveSet.lean`); the other proofs are informal. Theorem A was also checked exhaustively on three profiles (see Evidence).

## Answer

**Summary**
- **Theorem A.** Sincere swiping is dominant exactly when, in every realization, the user's matches are *the acceptable profiles inside a live set* $S$. The live set is fixed without looking at the user's swipes, and it must be a set on which the user's valuation is additive: at most $k$ profiles for top-$k$.
- **Your own swipes cannot matter.** No feed, price or match rule may react to a user's own likes in a way that changes who can match them. This holds even for additive users.
- **The cap of $k$ survives like-aware ranking.** A top-$k$ user can be shown more than $k$ profiles who would match only if the platform refuses all but $k$ of those mutual likes, and chooses which without the user's swipes.
- **Other valuations.** Matroid users: the live set is independent. Any class that contains top-1 users (submodular, XOS, subadditive): one live profile. Additive: any live set.
- **Two costs** ($c$ for a kept match, $d$ for a dropped one). For every $d>0$ the theorem is unchanged, so the barrier does not go away. What shrinks is the gain from deviating: exactly $d$ per dropped match (Theorem B). At $d=0$ the cap disappears, but liking everything is then as good as sincere swiping. The project adopted this model on 2026-11-09; welfare results are in [[Welfare of Truthful Feeds in the Two-Cost Model]].
- **Other cost functions.** A general cost changes two numbers and nothing else: the cap sits at the first rise in the marginal cost of a kept match, and breaking it costs the smaller of the drop cost and that rise (Theorem B′). Top-$k$ is itself such a cost.
- **What others' likes buy (Proposition P).** A live set may depend on who likes the user. On the random market that raises zero-query truthful welfare from about $2p$ of the optimum to between $\sqrt p/2$ and $\sqrt p$.

### Setting
- **Ranked feeds and the clock.** [[Ranked-Feed Model of the Dating Market]] states the model. Theorems A and B hold under every clock, with or without rounds (Proposition 1 there; `lean/DatingAlgo/Timing.lean`).
- **User and values.** One user $\ell$, a finite set $N$ of profiles, and a value $q_x$ for each. Any value vector with entries in an open interval around the cost $c>0$ can occur. Profile $x$ is *acceptable* if $q_x>c$; $X$ is the acceptable set.
- **Utility.** $u_q(S)=\max_{T\subseteq S}\big[v_q(T)-c|T|-d|S\setminus T|\big]$ for the match set $S$, with $0\le d\le c$: the user keeps $T$ and drops the rest. With $d=c$ this is the earlier model $v_q(S)-c|S|$.
- **Family $\mathcal F$.** A valuation class comes with a family $\mathcal F$ of sets, closed under subsets, such that:
  - (F1) on $S\in\mathcal F$ utility is additive, $u_q(S)=\sum_{x\in S}g(q_x)$ with $g(t)=\max(t-c,-d)$;
  - (F2) if $S\notin\mathcal F$ and every member of $S$ is worth $c+\varepsilon$, then $u_q(S)$ stays below a negative constant as $\varepsilon\to0$.
- **Swipe tree.** Fix the platform's coins and the others' strategies. What $\ell$ then faces is a tree: each node shows a profile not yet shown on that path, or stops; $\ell$ likes or passes; at the end $\ell$'s matches are a set of liked profiles. The tree cannot depend on $q$ (the platform is *value-blind*). It may depend on $\ell$'s earlier swipes, which is what like-aware means.
- **Sincere swiping.** Like iff acceptable. The outcome depends only on $X$; call it $M(X)$.
- **Dominant.** For every $q$, no path through the tree gives $\ell$ more than the sincere path. A mechanism is universally DSIC when this holds in every tree it can produce.

### Theorem A
**Statement.** Let the class satisfy (F1) and (F2), and let $0<d\le c$. In a swipe tree, sincere swiping is dominant if and only if there is a set $S\in\mathcal F$ with
$$M(X)=X\cap S\quad\text{for every }X\subseteq N.$$
With $d=0$ the same holds for every subadditive class, with no restriction on $S$.

*Proof, if.* Every path is the sincere path of the set $X'$ it likes, so every leaf is $X'\cap S$. For a user with acceptable set $X$, (F1) gives $u_q(X'\cap S)=\sum_{x\in X'\cap S}g(q_x)\le\sum_{x\in X\cap S}g(q_x)$, because $g(q_x)>0$ exactly on $X$.

*Proof, only if.*
1. **Every leaf is in $\mathcal F$.** Take a leaf $M'$ whose path likes $L$. Give $L$ the value $c+\varepsilon$ and everything else $c-\varepsilon$. This user's sincere path is that path, and passing on everything earns 0. So $u_q(M')\ge0$ for all small $\varepsilon$, which (F2) forbids unless $M'\in\mathcal F$.
2. **Every leaf lies inside $S:=M(N)$.** Suppose a leaf $M'$ contains $x\notin S$. Give $x$ the value $c+a$ and everyone else $c+\varepsilon$. Sincere swiping likes everything and earns $\varepsilon|S|$. The leaf $M'$ earns at least $a$, by (F1). Contradiction for small $\varepsilon$.
3. **$M(X)=X\cap S$.** $M(X)$ lies in $X$ and in $S$. Suppose $x\in X\cap S$ is missing from it. Give $x$ the value $c+a$, the rest of $X$ the value $c+\varepsilon$, and everything else $c-\varepsilon$. Sincere swiping earns at most $\varepsilon|S|$; liking everything reaches $S$ and earns at least $a-\varepsilon|S|$. Contradiction. $\square$
- *With $d=0$.* "If" holds because utility is monotone and unacceptable profiles add nothing. Steps 2 and 3 use only that utility is monotone, at least the best single net value, and at most the sum of the positive net values. Step 1 is the only step that needs $d>0$.

*In words.* The platform holds a shortlist for you that your swipes cannot change. You match with the shortlisted people you like, and with no one else. Everything else in the feed is inert.

**Corollaries.**
- **Own-swipe independence.** If liking or passing one profile changes whether another can match you, some user gains by swiping insincerely. The price $\mu_i$ in [[Position-Aware Reciprocal Re-Ranking and Dual Pacing]] is an example ([[Truthful Top-k Swiping in Like-Aware Feeds]] has the counterexample).
- **What the live set may use.** Coins, the other users' swipes, and predictions built from data other than this user's swipes. An oracle lifts value-blindness and is outside the theorem.
- **Top-$k$.** $|S|\le k$ in every realization, including the one where everyone shown likes back. So Theorem 1's limit holds for every value-blind mechanism, and Claim A's assumptions (a cap on matches, no wasted matches) are not needed: wasting is forced.

**Theorem A′ (platform coins).** Suppose sincere swiping is dominant only on average over the platform's coins. Then for every $X$: $M(X)\in\mathcal F$ almost surely, and the probability $m(x)$ that a liked profile $x$ converts is the same for every $X\ni x$. For top-$k$ users $\sum_x m(x)\le k$.
- *Proof sketch.* Step 1's user gives $\Pr[M(L)\notin\mathcal F]=O(\varepsilon)$ for every $\varepsilon$, so it is 0. Utility is then additive on outcomes. A user who values $x$ at $c+a$ and the rest of $X$ at $c+\varepsilon$ can play another set's sincere strategy, so $m_X(x)\ge m_{X'}(x)$ for all $X,X'\ni x$.
- This direction is only necessary: a strategy that reacts to what the feed reveals about the coins is not covered.

### Which valuations
| Class the platform knows | Possible live sets |
| --- | --- |
| Additive | any set |
| Top-$k$ | at most $k$ profiles |
| Weighted matroid rank, matroid known (one partner per city) | independent sets |
| Any class containing top-1: gross substitutes, submodular, XOS, subadditive, or top-$k$ with $k$ private | at most one profile |

- With one live profile, sincere swiping is dominant for every monotone valuation.
- **Not covered.** Valuations with complements in general (one case is in "Other cost functions"). Values that take a single acceptable level: there users don't care which acceptable partner they get, and priority rules that pick a largest matching are truthful *(not in vault, general knowledge: Bogomolnaia & Moulin 2004)*. Theorem A says that result fails as soon as acceptable partners differ in value.

### Two costs
**Theorem B.** Let matches be $X'\cap S$ for a live set $S$ of any size, for example a swipe-local policy. For a subadditive valuation, the best play in hindsight beats sincere swiping by at most $d$ times the number of matches the user would drop if dropping were free. It is exactly $d\,(|X\cap S|-k)^+$ for top-$k$ and $d\,(|X\cap S|-\mathrm{rank})$ for matroid users.
- *Proof.* Removing an unacceptable profile from the liked set never hurts: if it was kept it added at most $c$ in value and cost $c$; if it was dropped it cost $d$. So the best deviation likes a subset of $X\cap S$. The best such subset is $T_0$, the set a user keeps from $X\cap S$ when dropping is free. A sincere user can keep $T_0$ too and pay $d$ for each other match. For top-$k$ and matroid users that is the sincere user's best choice, which gives equality. $\square$
- With $d=c$ this is Proposition 4(a) of [[Truthful Swiping with an LLM Oracle]].

**Does the barrier go away?**
- **Exactly, no.** For any $d>0$, Theorem A still forces a live set of at most $k$.
- **Approximately, yes.** With many live profiles, deviating gains at most $d$ per dropped match, and a like on an unacceptable profile that converts costs $\min(d,c-q_x)$. So $d$ sets both how far sincere swiping is from dominant and how much an insincere like costs.
- **At $d=0$.** Sincere swiping is dominant under every swipe-local policy, for every subadditive valuation. So is liking everything, and likes then carry no information.

> [!tip] Adopted (2026-11-09)
> The project uses the two-cost model, with Theorems A and B as the headline pair. With $d<c$, welfare needs a rule for what a dropped match costs the *other* user; otherwise showing everyone to everyone is optimal as $d\to0$. The rule: a match counts only if both users keep it. [[Welfare of Truthful Feeds in the Two-Cost Model]] restates both theorems under it.

### Other cost functions
**General form.** $u_q(S)=\max_{T\subseteq S}\big[v_q(T)-(c_1+\dots+c_{|T|})-(d_1+\dots+d_{|S\setminus T|})\big]$: the $r$-th kept match costs $c_r$ and the $r$-th dropped match costs $d_r$. Sincere swiping is still "like iff the profile is worth having alone", $q_x>c_1$.

Theorem A's proof uses the costs only through (F1) and (F2). A cost function therefore changes the family $\mathcal F$ and leaves the live-set form alone.

| Cost model | Largest live set | Gain from deviating, per extra match |
| --- | --- | --- |
| Linear, $c$ and $d$ (above) | $k$ | $d$ |
| Additive values, convex keep cost $c_1\le c_2\le\dots$ | $k_1$, the number of matches at the lowest marginal cost | $\min(d,\ c_r-c_1)$ at most |
| The same with $c_r=c$ for $r\le k$ and $c_r=\infty$ after | $k$: this *is* top-$k$ | $d$ |
| Top-$k$, first $j$ drops free | $k+j$ | 0 for the first $j$ |
| A fixed cost shared by all kept matches (economies of scale) | 1 | not bounded by $d$ |

- *Convex keep cost.* (F1) holds on sets of at most $k_1$ profiles, where every kept match costs $c_1$. (F2) holds beyond: with all values at $c_1+\varepsilon$, an extra match either costs $c_r-c_1-\varepsilon$ to keep or $d$ to drop.
- *Last two rows.* Checked by brute force only. Free drops need (F1) weakened to "on $S\in\mathcal F$, the acceptable members are a best subset of $S$". With a shared fixed cost, two profiles that are each unacceptable alone can be worth liking together.

**Theorem B′.** Take additive values, convex keep costs, a constant drop cost $d$, and a live set of any size. Order the acceptable live profiles by value, $v_{(1)}\ge\dots\ge v_{(m)}$, and let $t^*$ be the number worth keeping, $t^*=\#\{r:v_{(r)}>c_r\}$. The best play in hindsight beats sincere swiping by exactly
$$\sum_{r>t^*}\min\big(d,\ c_r-v_{(r)}\big)\ \le\ \sum_{r=k_1+1}^{m}\min\big(d,\ c_r-c_1\big).$$
- *Proof.* As in Theorem B, the best deviation likes only the top $t^*$. A sincere user ends with $m$ matches and, for each $r>t^*$, either keeps it at a loss of $c_r-v_{(r)}$ or drops it for $d$. These losses rise with $r$, so the choices are consistent. For the bound, $v_{(r)}>c_1$ and $t^*\ge\min(m,k_1)$. $\square$

**What this says.**
- **The barrier is a kink.** Exact dominance fails at the first point where one more kept match costs more than the last. Top-$k$ is the sharpest kink.
- **Its size is the price.** If time gets scarce gradually ($c_r-c_1$ small), sincere swiping is nearly dominant even when dropping is as costly as keeping.
- **No cost function removes it.** Costs that make matches substitutes or complements only shrink $\mathcal F$. The exceptions are free drops, where likes stop carrying information.

### What others' likes buy
**Proposition P.** Take Proposition 6(b)'s market in [[Truthful Swiping with an LLM Oracle]]: $n$ top-1 users per side, each value is 2 with probability $\sqrt p$ and 0 otherwise, costs are 1, and $np\to\infty$.
- **(a) Upper bound.** Every value-blind, universally DSIC mechanism earns at most $\sqrt p\,(1+o(1))\,\mathrm{OPT_{IR}}$. By Theorem A a user's single live profile is chosen independently of the user's own values, so the user likes it with probability $\sqrt p$.
- **(b) Cyclic priority.** Show everyone to everyone. User $\ell$'s candidate is the first of $\ell,\ell+1,\dots$ on the other side who likes $\ell$; the other side counts downward. A pair matches iff each is the other's candidate. Each user's live set has at most one member and ignores the user's own swipes, so this is DSIC. A user is matched with probability $\sqrt p/(2-\sqrt p)\ge\sqrt p/2$.
- **(c) Comparison.** Swipe-local policies with display caps get at most $2p$ (Proposition 6(b)). The gain needs feeds of length about $1/\sqrt p$ and both sides to be selective: if one side accepts everyone, the bound in (a) is $p$.

### Ways around the theorem
- **An oracle or other outside information about values:** screened DH ([[Truthful Swiping with an LLM Oracle]]). With the user's values on the live set, the platform can keep the best $k$ mutual likes itself and the cap disappears ([[Queries and the Live-Set Theorem]], Theorem E).
- **Richer messages:** ranked likes or roses ([[Preference Signaling]]).
- **A different truthful action:** pick at most $k$ from a queue of sure matches (Claim C of [[Truthful Top-k Swiping in Like-Aware Feeds]]).
- **Approximate truthfulness:** Theorem B, or Bayesian best responses (Claim B there).

## Evidence
- [[Truthful Swiping with an LLM Oracle]]: Theorem 1 (the swipe-local case), Proposition 4(a), Proposition 6. [[Truthful Top-k Swiping in Like-Aware Feeds]]: Claim A, the $\mu_i$ counterexample, Claims B and C.
- **Lean, 2026-11-09.** `lean/DatingAlgo/LiveSet.lean`; `lean/check.sh` reports 1008 theorems, none open.
  - *Theorem A:* `liveSet_iff` (any outcome rule with $M(X)\subseteq X$) and `swipeTree_liveSet_iff` (swipe trees), for top-$k$ users, $d>0$, and types within $\delta\le c$ of the cost. `liveSet_iff_additive` for additive users, `liveSet_iff_zero_drop` for $d=0$, `own_swipe_independence`.
  - *Theorem B:* `twoCost_topK_regret_le`, `twoCost_topK_regret_attained` for top-$k$ users with $0\le d\le c$.
- **Brute force, 2026-11-09.** `data/scripts/live_set_check.py`; every assertion held.
  - *Theorem A:* every swipe tree on three profiles (244 display rules, 132,127 mechanisms), for additive, top-1, top-2 and a partition matroid, with $d=c$ and $d=0.3c$: dominant iff live-set form. With $d=0$ the dominant mechanisms are the 811 with an unrestricted live set, for every class.
  - *Theorem A′:* linear programs over all randomized rules on three profiles. With values within $\varepsilon$ of the cost, overshoot probability and the change in a profile's conversion probability are $O(\varepsilon)$ (0.0007 and 0.0015 at $\varepsilon=0.001$, $d=c$, top-1).
  - *Theorem B:* 3,000 random cases; exact for top-$k$ and matroid users, an upper bound for XOS.
  - *Proposition P(b):* dominance checked against every behavior of the others for 2 and 3 users per side; simulated match rates agree with the formula ($0.0528\pm0.0012$ against $0.0526$ at $p=0.01$).
  - *Other cost functions:* the same exhaustive test for a convex keep cost, top-2 written as a cost, a free first drop and a shared fixed cost; in each the dominant mechanisms are the live sets of the size in the table. Theorem B′'s formula on 3,000 random cases.
- *Not in vault yet:* Hinge's ranking paper is in `inbox/lu2026conversations.pdf`. Its flow is initiator likes, responder accepts, and behavioral features carry about half of its model's attribution.

## Gaps
- **Lean.** Not formalized: Theorem A for matroid users and for classes containing top-1, Theorem A′, Theorem B for matroid and subadditive users, Theorem B′, Proposition P.
- **A cost per like sent** (like budgets). Utility then depends on the swipes and not only on the matches, so the swipe-tree argument does not apply as written.
- **General cost functions.** The free-drop and fixed-cost rows are brute force on three profiles, with no proof.
- **Learning from a user's own likes.** Theorem A rules it out under exact dominance. A large-market or Bayesian version of own-swipe independence is open.
- **Best truthful welfare for general priors.** Proposition P is one market, and its bounds are a factor 2 apart.
- **Theorem A′ is only necessary.** A matching sufficient condition for randomized mechanisms is open.
- **Re-shown profiles.** The tree shows each profile once and treats a swipe as final.
