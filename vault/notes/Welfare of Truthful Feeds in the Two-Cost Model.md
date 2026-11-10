---
type: synthesis
question: "With the two-cost model adopted and a match counted only when both users keep it, what do Theorems A and B say about conversations, and how much welfare can an exactly or nearly truthful feed guarantee?"
created: 2026-11-09
updated: 2026-11-11
tags: [dating/platforms, game-theory/incentives, matching/quality, research/project]
aliases: [conversation rule, keep stage, responder queue, Queue-DH, Theorem C, Theorem D, two-cap lemma, thinned queue, Proposition T, one-sided overshoot]
sources: ["[[Rios 2026 - The Dating Heuristic]]"]
origin: claude
status: seed
---
# Welfare of Truthful Feeds in the Two-Cost Model

> [!question] With the two-cost model adopted and a match counted only when both users keep it, what do Theorems A and B say about conversations, and how much welfare can an exactly or nearly truthful feed guarantee?

> [!note] Preliminary
> Written 2026-11-09, after the project adopted the two-cost model of [[The Live-Set Theorem for Truthful Swiping]] and the rule that a match counts only if both users keep it. Proofs are informal and not in Lean. The numbers come from `data/scripts/live_set_check.py`.

## Answer

**Summary**
- **Model.** After the swipes, each user keeps or drops each match. A *conversation* is a match both users keep, and only conversations create value.
- **Theorems A and B carry over to conversations** when being dropped is free and the keep stage has no second chances. A sincere swiper then regrets at most $d$ per match they drop.
- **Second chances break truthfulness.** If a dropped user can fall back on another match, a user's own swipes change who keeps them, and Theorem A applies again with a full match at stake.
- **Theorem C (one side over the cap).** Cap initiators at $k$ profiles and show responders everyone who liked them. Initiators are exactly truthful, responders regret $d$ per drop, and conversations are at least $c_k$ times the best any mechanism with exactly truthful initiators can get.
- **Theorem C′ (partial scrolling).** If a responder looks only at the first $m$ admirers, rank the queue by acceptance probability. The factor becomes $c_kc_m$, never below 0.46.
- **Theorem D (pair welfare).** When the two users value the pair differently, a thinned queue gets $\tfrac14$ of the pair LP, and the better of the two queues gets at least 0.18 of the best in the class.
- **Proposition T (both sides over the cap).** On the random market, feeds of length $\lambda/p$ put a constant share of users in a conversation (0.47 at $\lambda=1$), where exact truthfulness allows at most $\sqrt p$. The price is $d$ times about one drop per user, and a keep stage that is a coordination game.

### Model
- **Ranked feeds.** [[Ranked-Feed Model of the Dating Market]] states the model in which feeds are rankings over all candidates and records which results hold there.
- **Sides and values.** Initiators $I$ and responders $J$. User $\ell$ has a top-$k_\ell$ valuation. Values are independent across pairs and across the two users of a pair. The platform knows the distributions and sees only swipes.
- **Timeline.** Swipes; a *match* is a mutual like; then each user keeps or drops each match; a *conversation* is a match both keep.
- **Payoff of $\ell$.** $v_\ell(\text{conversations})-c$ per conversation, $-d$ per match $\ell$ drops, $-h$ per match $\ell$ keeps and the partner drops. Here $0\le d\le c$, and $h=0$ unless stated.
- **One-shot keep stage.** A user's keep decisions cannot react to another user's drops.
- **Welfare.** The sum of payoffs.

### Theorems A and B for conversations
For user $\ell$, let $S$ be the live set of [[The Live-Set Theorem for Truthful Swiping]] (who matches $\ell$ if liked) and $S^{\mathrm{keep}}\subseteq S$ those who would also keep $\ell$. Assume neither depends on $\ell$'s swipes. The comparison below gives every swiping strategy its best keep choice in hindsight.

**Proposition 1.** For a top-$k$ user:
- **(a) Regret.** Sincere swiping loses exactly $d\,(|X\cap S^{\mathrm{keep}}|-k)^+ + h\,|X\cap(S\setminus S^{\mathrm{keep}})|$ against the best swipes in hindsight: $d$ per match the user drops and $h$ per match the partner drops.
- **(b) Exact.** With $h=0$ and $d>0$, sincere swiping is dominant iff $|S^{\mathrm{keep}}|\le k$ in every realization. This is Theorem A with "match" read as "match the partner keeps".
- **(c) Second chances.** If dropped users can fall back on another match, $S^{\mathrm{keep}}$ depends on $\ell$'s swipes and (a), (b) fail.

*Proof.* (a) The best swipes like the best $k$ members of $X\cap S^{\mathrm{keep}}$ and nothing else. Sincere swiping reaches the same conversations after dropping the other members of $X\cap S^{\mathrm{keep}}$, and pays $h$ for each liked profile in $S\setminus S^{\mathrm{keep}}$. (b) With $h=0$ a match the partner drops is the same as no match, so the outcome of liking $X'$ is $X'\cap S^{\mathrm{keep}}$, and Theorem A applies. (c) Example with top-1 users: $i$ prefers $j_1$ to $j_2$; $i'$ prefers $j_2$ to $j_1$; $j_1$ prefers $i'$ to $i$; $j_2$ prefers $i$ to $i'$; everyone finds everyone acceptable. Run [[Deferred Acceptance]] among the matches with responders proposing. Sincere $i$ ends with $j_2$. If $i$ passes on $j_2$, then $j_2$ proposes to $i'$, who drops $j_1$, who falls back on $i$. $\square$

**The keep stage.**
- **If $\ell$'s partners never have more than $k$ matches**, they never drop, $S^{\mathrm{keep}}=S$, and keeping one's best $k$ is dominant.
- **If both sides can exceed $k$**, a user may keep someone who drops them. No keep rule is dominant, and the loss is a whole match. This is the congestion of [[Congestion in Matching Markets]]. Swipes stay nearly truthful by (a), but welfare must count the loss.

### Theorem C: capped initiators and a responder queue
**Setting.** Hinge's flow: initiators browse, and a responder sees only initiators who liked them. $p_{ij}$ is the probability that $i$ likes $j$, and $p_{ji}$ that $j$ accepts $i$.

**Mechanism (Queue-DH).**
1. Solve $\mathrm{LP}_1=\max\sum_j\min\big(k_j,\ \sum_i x_{ij}p_{ij}p_{ji}\big)$ subject to $\sum_j x_{ij}\le k_i$ and $0\le x\le1$. Scale columns down so that $\mu_j:=\sum_i x_{ij}p_{ij}p_{ji}\le k_j$.
2. Show initiator $i$ a set $D_i$ of at most $k_i$ profiles with $\Pr[j\in D_i]=x_{ij}$, independently across initiators.
3. Show responder $j$ every initiator who liked $j$. The responder likes the acceptable ones, keeps the best $k_j$ and drops the rest.

**Statement.**
- **(a) Initiators.** Sincere swiping is exactly dominant, and initiators never drop.
- **(b) Responders.** Keeping the best $k_j$ is dominant. Sincere swiping loses exactly $d\,(N_j-k_j)^+$, where $N_j$ counts acceptable admirers; with sincere initiators its mean is at most $d\,(1-c_{k_j})\,k_j$.
- **(c) Conversations.** $\mathbb E[\text{conversations}]\ge\sum_j c_{k_j}\min(k_j,\mu_j)\ge c_{\min_j k_j}\mathrm{LP}_1$, with $c_k=1-e^{-k}k^k/k!$. And $\mathrm{LP}_1$ bounds the expected conversations of every one-directional value-blind mechanism that shows each initiator at most $k_i$ profiles.
- **(d) Responder surplus.** Choose $x$ to maximize the fluid bound $\sum_j\int_0^\infty\min\big(k_j,\ \sum_i x_{ij}p_{ij}\Pr[v_j(i)-c>\theta]\big)\,d\theta$, a concave program. Then $\mathbb E\big[\sum_j \text{top-}k_j\text{ surplus of }j\big]$ is at least $c_{\min_jk_j}$ times that bound, and the bound holds for the same class of mechanisms.

*Proof.*
- **(a)** $i$'s matches lie in $D_i$. Whether $j$ keeps $i$ depends on $j$'s values and $j$'s other admirers, not on $i$'s other swipes. So $S^{\mathrm{keep}}\subseteq D_i$ is fixed and has at most $k_i$ members; use Proposition 1(b).
- **(b)** Initiators never drop, so $S^{\mathrm{keep}}=S$ and Proposition 1(a) applies. $N_j$ is a sum of independent indicators with mean $\mu_j\le k_j$, and $\mathbb E(N_j-k_j)^+=\mu_j-\mathbb E\min(k_j,N_j)\le(1-c_{k_j})\mu_j$.
- **(c)** $j$ has $\min(k_j,N_j)$ conversations, and $\mathbb E\min(k,N)\ge c_k\min(k,\mathbb EN)$ for sums of independent indicators (the lemma behind DH's guarantee, [[Rios 2026 - The Dating Heuristic]]; see [[Correlation Gap]]). For the bound: in any such mechanism $j$ has at most $\min(k_j,\#\{i\text{ shown }j\text{, mutual like}\})$ conversations. The platform decides to show $j$ to $i$ before either has swiped on the other, so that event has probability $x_{ij}p_{ij}p_{ji}$ with $\sum_jx_{ij}\le k_i$. Then apply Jensen.
- **(d)** The sum of the $k$ largest of some nonnegative numbers is $\int_0^\infty\min(k,\#\{\text{numbers above }\theta\})\,d\theta$. Apply (c)'s lemma and bound at each $\theta$. $\square$

**Remarks.**
- **Gain over capped responders.** One top-1 responder, $m$ initiators who always like, acceptance probability $a$: a cap of one admirer gives $a$, the queue gives $1-(1-a)^m$.
- **Ranked initiator feeds.** If the initiator looks at position $r$ with probability $\alpha_r$, replace $x_{ij}$ by the exposure $\sum_r\alpha_r\Pr[j\text{ at position }r]$. Nothing else in (a) to (c) changes.
- **Where it is weak.** On the random market below, each initiator sees one profile, so only a share $p$ of users converse. The mechanism suits markets where initiators like most of what they see and responders are selective.

- **Net of drop costs.** The bounds above ignore the $d$ paid per drop. In (c), $\mu_j\le k_j$ keeps expected drops below $(1-c_{k_j})k_j$ per responder. In (d), subtract $d\sum_j(\mu_j-k_j)^+$ from the objective, which keeps it concave and still bounds every mechanism in the class; the mechanism then earns at least $c_k$ times that bound minus $d\,(1-c_k)\sum_j\mu_j$.

### Theorem C′: responders who look at part of the queue
**Setting.** Responder $j$ looks at the first $R_j$ admirers in the queue, with $\Pr[R_j=m]=w^j_m$ independent of everything else. Theorem C is $R_j=\infty$, and a display cap of $K$ is $R_j\equiv K$.

**Mechanism.** Queue-DH with two changes. Order each queue by decreasing acceptance probability $p_{ji}$. Choose $x$ to solve the linear program
$$\mathrm{LP}_\alpha=\max\sum_j\sum_m w^j_m\min\big(k_j,\ V^j_m(x)\big),\qquad V^j_m(x)=\max\Big\{\sum_i e_ip_{ji}:\ e_i\le x_{ij}p_{ij},\ \sum_ie_i\le m\Big\},$$
subject to $\sum_jx_{ij}\le k_i$. $V^j_m$ is the fluid count of acceptable admirers among the first $m$.

**Statement.** Incentives are as in Theorem C. Conversations satisfy
$$\mathbb E[\text{conversations}]\ \ge\ \sum_j\sum_m w^j_m\,\gamma(k_j,m)\,\min\big(k_j,V^j_m(x)\big),\qquad \gamma(k,m)=\begin{cases}c_m&m\le k\\ c_kc_m&m>k,\end{cases}$$
which is at least $c_1c_2\approx0.46$ of $\mathrm{LP}_\alpha$. And $\mathrm{LP}_\alpha$ bounds every mechanism in Theorem C's class, whatever order it uses.

**Lemma (two caps).** Admirers in queue order have independent presence probabilities $y_i$ and acceptance probabilities $p_1\ge p_2\ge\dots$. Let $Z_m$ count the accepted among the first $m$ present. Then $\mathbb E\min(k,Z_m)\ge\gamma(k,m)\min(k,V_m(y))$.

*Proof of the lemma.*
1. **One term per admirer.** Admirer $i$ adds a conversation iff $i$ is present and accepted, fewer than $m$ earlier admirers are present, and fewer than $k$ earlier ones are present and accepted. So $\mathbb E\min(k,Z_m)=\sum_iy_ip_i\pi_i$, with $\pi_i$ the probability of the last two events.
2. **The two events help each other.** Both are decreasing in the independent presence and acceptance indicators, so by Harris's inequality $\pi_i\ge a_ib_i$, where $a_i=\Pr[\text{fewer than }m\text{ earlier present}]$ and $b_i=\Pr[\text{fewer than }k\text{ earlier accepted}]$. Both fall with $i$.
3. **Fluid prefix.** Let $e\le y$ fill the queue from the top until $\sum e_i=m$ or $\sum e_ip_i=k$. Then $\sum e_ip_i=V:=\min(k,V_m(y))$. Lowering the last admirer's presence to $e_i$ changes no earlier $a_i,b_i$, so the one-cap lemma gives $\sum e_ip_ib_i\ge c_kV$ and (in its weighted form, Theorem C(d)) $\sum e_ip_ia_i\ge c_mV$.
4. **Combine.** $a$ and $b$ are ordered the same way, so Chebyshev's sum inequality with weights $e_ip_i$ gives $\sum e_ip_ia_ib_i\ge(c_mV)(c_kV)/V$. If $m\le k$ the second event never binds and step 3 alone gives $c_mV$. $\square$

*Proof of the theorem.* Apply the lemma to each $j$ and $m$ with $y_i=x_{ij}p_{ij}$. For the bound, fix a mechanism and condition on $R_j=m$: $j$ looks at no more than $m$ admirers, each is one with probability at most $x_{ij}p_{ij}$, and acceptance is independent of the order, so the expected number of acceptable admirers seen is at most $V^j_m$. Then apply Jensen. $\square$

- **Looser than it looks.** In 20,000 random queues the smallest ratio was 0.59, against a proved 0.46 for $k=1$, $m=2$.
- **Consistency.** With no keep limit and $R_j\equiv K$ the factor is $c_K$, the constant a display cap costs in [[Dating Heuristic]].

### Theorem D: pair welfare
**Setting.** A conversation between $i$ and $j$ is worth $(v_i(j)-c)+(v_j(i)-c)$. Let $\omega_{ij}$ be its mean given a mutual like. The responder keeps by $v_j(i)$ alone, so a full queue can crowd out pairs the initiator values highly.

**Mechanism (thinned queue).** Solve $\mathrm{LP_{pair}}=\max\sum_{ij}\omega_{ij}z_{ij}$ subject to $z_{ij}\le x_{ij}p_{ij}p_{ji}$, $\sum_iz_{ij}\le k_j$, $\sum_jx_{ij}\le k_i$. Show $j$ to $i$ with probability $z_{ij}/(2p_{ij}p_{ji})$, at most $k_i$ profiles per initiator. Responders see every admirer.

**Statement.**
- **(a)** Every acceptable admirer is kept with probability at least $\tfrac12$, whatever the responder prefers. So pair welfare is at least $\tfrac14\mathrm{LP_{pair}}$. Incentives are as in Theorem C.
- **(b)** Every mechanism in Theorem C's class has pair welfare at most $\Phi^*+\mathrm{LP_{pair}}$, where $\Phi^*$ is the largest fluid bound of Theorem C(d).
- **(c)** The better of Queue-DH (run for responder surplus) and the thinned queue therefore gets at least $\frac{1}{4+1/c_k}$ of the best in the class: 0.18 for $k=1$.

*Proof.* (a) $j$'s acceptable admirers other than $i$ number $N$ with mean at most $k_j/2$, so $\Pr[N\ge k_j]\le\tfrac12$ by Markov, and $i$ is kept whenever $N<k_j$. This holds for every value of $v_j(i)$, and $v_i(j)$ plays no part in who is kept. So each pair contributes at least $\tfrac12\cdot\tfrac{z_{ij}}2\cdot\omega_{ij}$. (b) Responder surplus is at most $\Phi^*$. The initiator's surplus in a conversation is independent of whether the conversation happens, given $i$'s like, so initiator surplus is at most $\max\sum\bar a_{ij}z_{ij}\le\mathrm{LP_{pair}}$ with $\bar a_{ij}$ the initiator's mean surplus. (c) $\max(c_kA,\tfrac14B)\ge(A+B)/(1/c_k+4)$. $\square$

- **The constant is loose for large $k$.** The $\tfrac12$ comes from Markov; a Chernoff bound brings it towards 1.
- **Seeing values is worth a factor 2.** One responder, $k=1$: admirer $A$ has initiator surplus 1 and responder surplus $\delta$; admirer $B$ has initiator surplus 0 and responder surplus $2\delta$, or a large $H$ with probability $1/H$. Showing either or both earns about 1. A planner who sees values earns about 2.

### Proposition T: long feeds on both sides
**Setting.** The market of Proposition P in [[The Live-Set Theorem for Truthful Swiping]]: $n$ top-1 users per side, every like has probability $\sqrt p$, all acceptable partners are worth the same.

**Mechanism.** Initiator $i$ is shown the $L$ responders $i,\dots,i+L-1$ (mod $n$). A responder sees every admirer, keeps one acceptable admirer at random and drops the others. An initiator then keeps one of the responders who kept them and drops the others.

**Statement.** For $n\ge L$:
- **(a)** The share of users in a conversation is $\rho=1-\big(1-\tfrac{1-(1-p)^L}{L}\big)^L$, which tends to $1-\exp(-(1-e^{-\lambda}))$ when $Lp=\lambda$ and $p\to0$.
- **(b)** Expected drops are $Lp-(1-(1-p)^L)$ per responder and $(1-(1-p)^L)-\rho$ per initiator. Sincere swiping loses $d$ per own drop (Proposition 1(a)).
- **(c)** Every exactly truthful value-blind mechanism gets at most $\sqrt p\,(1+o(1))$ (Proposition P).

*Proof.* The $L$ pairs of a user are mutual likes independently with probability $p$. A responder with $D$ other mutual admirers keeps $i$ with probability $1/(1+D)$, and $\mathbb E[1/(1+\mathrm{Bin}(L-1,p))]=\frac{1-(1-p)^L}{Lp}$. These events involve disjoint pairs for the $L$ responders in $i$'s feed, so each keeps $i$ independently with probability $q=\frac{1-(1-p)^L}{L}$, and $\rho=1-(1-q)^L$. $\square$

| $Lp$ | In a conversation | Drops per responder | Drops per initiator |
| --- | --- | --- | --- |
| 0.5 | 0.33 | 0.11 | 0.07 |
| 1 | 0.47 | 0.37 | 0.16 |
| 2 | 0.58 | 1.13 | 0.29 |
| 4 | 0.63 | 3.02 | 0.36 |

- At $p=0.01$ the exact-truthfulness bound is 0.10 and cyclic priority reaches 0.05.
- **Caveat.** A responder's keep choice is not dominant here: the initiator they keep may drop them. $\rho$ already counts that loss. For small $p$ the share stays below $1-1/e$ however long the feed.

### How the three regimes compare
| Who may exceed $k$ live profiles | Swipes | Keep stage | Welfare result |
| --- | --- | --- | --- |
| Nobody | exactly dominant | trivial | at most $\sqrt p$ of $\mathrm{OPT_{IR}}$ on the random market (Proposition P) |
| Responders only | initiators exact, responders lose $d$ per drop | dominant | $c_k$ of the best with exact initiators (Theorem C); $c_kc_m$ with partial scrolling (C′); 0.18 for pair welfare (D) |
| Both sides | everyone loses $d$ per drop | coordination game | constant share on the random market (Proposition T) |

## Evidence
- [[The Live-Set Theorem for Truthful Swiping]]: Theorems A and B, Proposition P. [[Rios 2026 - The Dating Heuristic]]: the two-period flow and the $c_k$ lemma.
- **Brute force, 2026-11-09.** `data/scripts/live_set_check.py`, checks F and G; every assertion held.
  - *Proposition 1:* the regret formula on 3,000 random cases; the fallback example.
  - *Proposition T:* simulation with $n=4000$ agrees with the formulas for $\rho$ and both drop counts at five settings.
  - *Theorem C:* 300 random markets, conversations at least 0.70 of $\mathrm{LP}_1$ (the bound allows $c_1=0.632$); 300 random queues, responder surplus at least 0.73 of the fluid bound.
  - *Theorem C′ (check H):* the two-cap lemma on 20,000 random queues, including many small identical admirers; 200 random markets with attention, conversations at least 0.73 of $\mathrm{LP}_\alpha$.
  - *Theorem D (check H):* 4,000 responders who keep the lowest-surplus pairs, pair welfare at least 0.29 of the pair LP.

## Gaps
- **Constants.** $c_kc_m$ in Theorem C′ and $\tfrac14$ in Theorem D are not tight; the checks sit well above both. Theorem D takes the better of two mechanisms, and a single one with a constant factor is open.
- **Theorem C′ covers conversations only.** Responder surplus and pair welfare with partial scrolling are open.
- **One role per user.** Every result here has initiators on one side and responders on the other. If a user both browses and receives likes, the two sources together can exceed $k$.
- **The keep stage when both sides exceed $k$.** No dominant rule exists. Open: a one-shot keep stage that loses less than Proposition T's, and what happens with $h>0$.
- **Benchmark.** Theorem C compares with mechanisms whose initiators are exactly truthful, not with $\mathrm{OPT_{IR}}$.
- **With an oracle.** [[Queries and the Live-Set Theorem]] makes the responder queue exactly truthful by querying on overshoot (Theorem F).
- **Lean.** Theorem C(a) and (c) are formalized (`lean/DatingAlgo/QueueGuarantees.lean`: `queueConv_ge`, `queue_approx`, `conv_le_fluidConv`, `queue_initiator_truthful`). The two-cap lemma is formalized with the factor $c_kc_m$ for all $m,k$ (`lean/DatingAlgo/TwoCap.lean`: `twoCap_ge`). Its Lean proof replaces Chebyshev's inequality by two summations by parts and proves the correlation step by induction on the queue. Not formalized: Proposition 1, C(d), the sharper factor $c_m$ for $m\le k$, the market-level statement of Theorem C′, Theorem D, Proposition T.
