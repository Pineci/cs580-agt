---
type: synthesis
question: "When users and their LLM agents act strategically, does a dating-heuristic platform make likes track match quality, and do agents report values truthfully?"
created: 2026-10-21
updated: 2026-10-22
tags: [dating/platforms, matching/quality, game-theory/incentives, research/project]
aliases: [strategic likes, sincere liking, consent-only policies, like budgets, cheap-talk reports, strategic agents]
sources: ["[[Rios 2026 - The Dating Heuristic]]", "[[Coles 2013 - Preference Signaling in Matching Markets]]", "[[Lee 2015 - Propose with a Rose]]", "[[Arnosti 2021 - Managing Congestion in Matching Markets]]", "[[Kanoria 2021 - Facilitating the Search for Partners on Matching Platforms]]"]
origin: claude
status: seed
---
# Strategic Users in the Dating Heuristic Framework

> [!question] When users and their LLM agents act strategically, does a dating-heuristic platform make likes track match quality, and do agents report values truthfully?

> [!note] Preliminary
> This was written on 2026-10-21: an informal summary first, then formal statements with written-out proofs, not machine-checked. It adds incentives to [[Match Quality in the Dating Heuristic Framework]], [[Match Quality with Queried Values]] and [[Top-k Match Quality]], whose users like at random with known probabilities.

## Answer

**Summary**
- **Likes as consent.**
  - Call a policy *consent-only* if each responder's period-2 display depends only on its own backlog and on independent coins.
  - DH-int, value-indexed DH-int and credit-DH are all consent-only.
  - Under such a policy, liking exactly when your value exceeds your match cost is weakly dominant *ex post*: it is at least as good on every realization, whatever others do (Theorem 1).
  - Like probabilities then equal $\Pr[q>c]$. A binary signal can't track quality any more closely than that.
- **No extra loss from incentives.** With additive utilities, weight DH-int by the expected welfare of a consented match. It then keeps $c_K$ against the best policy facing sincere users.
- **Costless matches make likes empty.** The threshold is 0, so everyone likes everyone. Likes are sincere but say nothing, and a match certifies nothing about quality.
- **Like budgets cut both ways.**
  - In period 2, a budget makes likes rank partners by value.
  - In period 1, it shades likes toward partners likely to reciprocate.
  - It also makes likes depend on what else is in the display, which [[Rios 2026 - The Dating Heuristic|Rios & Torrico]] rule out.
- **LLM value reports are cheap talk.**
  - In B1/B3's ranking and in credit-DH, an agent gains by inflating its values for the partners it prefers.
  - With bounded reports, each responder's ranking collapses to its own preference, and welfare can drop without bound.
  - Reports are safe only when they steer the reporter's own choices.
  - **Prop. 3′.** Any rule that makes truthful reporting dominant must ignore each sender's report when deciding whether to show that sender. It can use a responder's report only to let the responder choose from a menu of displays the platform fixes.
- **Using likes beyond consent breaks sincerity.** For example, ranking senders by how selective they are rewards hiding likes.
- **Top-k users are still monotone in value, but history-dependent.** Their thresholds rise with the matches they already have, which is the history dependence that Rios & Torrico's theory excludes. Guarantees for strategic top-k users are open.

### Model
This is the two-period model of [[Rios 2026 - The Dating Heuristic]], with these changes:
- **Private values.** $q_{\ell\ell'}\ge0$ is $\ell$'s value for $\ell'$. It is drawn from a prior $D_{\ell\ell'}$ that the platform knows, independently across ordered pairs. $\ell$ learns it on seeing $\ell'$, or $\ell$'s agent evaluates it.
- **Match cost.** $c_\ell\ge0$ per match: the time a conversation or date takes.
- **Utilities.**
  - *Additive:* $u_\ell=\sum_{\ell'\in M_\ell}(q_{\ell\ell'}-c_\ell)$.
  - *Top-k:* $u_\ell=\mathrm{top}_k\{q_{\ell\ell'}:\ell'\in M_\ell\}-c_\ell|M_\ell|$.
- **Actions.** Whenever $\ell$ is shown $\ell'$, $\ell$ (or its agent) likes or passes. A match forms when both have liked: in the same period for a mutual view, or one after the other through the backlog.
- **Platform.** It commits to a policy: period-1 displays, then period-2 displays as a function of what it observes.
  - Like probabilities are no longer data. $\phi_{\ell\ell'}$ is the probability that $\ell$'s *strategy* likes $\ell'$.
  - In the agent-report variant, agents also report values, which the platform may use.
- **Welfare.** $W=\sum_\ell u_\ell$, the total over both sides.

**Definitions.**
- **Consent-only policy.** Period-1 displays are fixed in advance. A responder's period-2 display is a function of its own backlog and of coins independent of everything else.
- **Sincere strategy** (additive utility): like exactly when $q_{\ell\ell'}>c_\ell$.
- **Value-monotone strategy:** each like decision, holding the rest fixed, is a threshold in the user's value for that profile.

### S1. Consent-only policies make sincere liking dominant
- **What a like does.** Under a consent-only policy, a like changes exactly one event: whether this pair matches.
  - When $s$ likes $r$ in period 1, $s$ enters $r$'s backlog. That changes $r$'s display, which can only affect *other* senders, never $s$.
  - $s$'s other matches depend on other backlogs, on $s$'s own backlog, and on mutual views. None of these change.
- **Additive utility.** Liking $r$ changes $s$'s payoff by $\Pr[\text{the match forms}\mid s\text{ likes}]\cdot(q_{sr}-c_s)$, whose sign is that of $q_{sr}-c_s$, whatever others do. So sincere liking is weakly dominant.
  - In period 2 the sender has already liked, so a responder's like back is a sure match. The same sign argument applies.
- **Top-k utility.** The marginal value of a match increases in its value, so every like decision is a threshold given the rest.
  - In period 2, matches are certain, and the best set of likes is the $j$ most valued shown members, for some $j$.
- **Consequence.** Under sincere play, $\phi_{\ell\ell'}=\Pr_{D}[q_{\ell\ell'}>c_\ell]$, in both periods. With additive utility this does not depend on history, so Rios & Torrico's model holds exactly.

### S2. Equilibrium guarantee for weighted DH-int
- **Weights.** Write $A_{\ell\ell'}=\mathbb E[q_{\ell\ell'}-c_\ell\mid q_{\ell\ell'}>c_\ell]\ge0$. A consented match $\{\ell,\ell'\}$ has expected welfare $A_{\ell\ell'}+A_{\ell'\ell}$.
- **Algorithm.** Run DH-int with mutual views weighted by $\beta_e(A_{\ell\ell'}+A_{\ell'\ell})$ and responses weighted by $\phi_{rs}(A_{sr}+A_{rs})$, where $\phi$ and $\beta$ are the sincere like probabilities.
- **Claim.** DH-int is consent-only, so sincere play is a dominant-strategy equilibrium. In it, DH-int earns at least $c_K$ times the best welfare any adaptive policy can reach against sincere users.
- **Why.** Given sincere play, this is exactly R2 with these non-negative weights. Every match has non-negative welfare, because both users liked.

### S3. Costless matches make likes uninformative
- **Threshold zero.** With $c_\ell=0$ and $q\ge0$, sincere means liking everyone, so $\phi\equiv1$.
- **Weak dominance needs no information.** In the two-period model, the platform's welfare guarantee survives, because S2 holds with $A=\mathbb E[q]$.
- **What is lost.**
  - Matches no longer certify anything about quality.
  - A platform that learns from likes over many periods learns nothing.
  - If matches really cost something but users don't bear that cost when liking (sending a like is free; the cost is paid later, on a bad date), likes overshoot.
- **What costs do.** Making likes or matches costly, even slightly, is what makes likes informative.
- **Literature.**
  - In [[Arnosti 2021 - Managing Congestion in Matching Markets]], free applications cause a tragedy of the commons. With more applicants than employers, applicants keep at most $\frac1r(1-(r-1)\log\frac{r}{r-1})$ of their benchmark, whatever the costs.
    - Their costs and limits help through *congestion*, not information: an application reveals nothing about fit.
    - Here the display cap $K$ already limits congestion, so the gain from costs is informational.
  - [[Coles 2013 - Preference Signaling in Matching Markets]]: *scarcity*, not cost, makes free signals informative.
  - In [[Kanoria 2021 - Facilitating the Search for Partners on Matching Platforms]], a user who pays $c$ to evaluate a profile effectively pays $c/p$, where $p$ is the chance it is accepted.
    - Applied here: if evaluating $r$ costs $c$, the initiator evaluates only when $\pi_{sr}$, the chance that $r$ is shown the initiator and likes back, is large enough.
    - The platform's display plan sets $\pi$, so it also decides whether period-1 likes are *informed*. Cheap LLM screening lowers $c$ but does not fix a small $\pi$.

### S4. Like budgets
- **Setup.** Each user can like at most $L$ of the profiles shown per period, with $L<K$.
- **Period 2.** Backlog members already liked the responder, so a like is a sure match. A budgeted responder likes its $L$ most valued positive matches. This is value-monotone, and in fact ranks by value.
- **Period 1.** A like on $r$ yields a match with probability $p_r=\Pr[r\text{ shows and likes }s\mid s\in B_r]$. A budgeted initiator likes the $L$ profiles with the largest $p_r(q_{sr}-c_s)$, so it shades toward attainable partners.
  - The platform knows its own $p_r$, so a like still reveals $q_{sr}\ge$ a known threshold.
  - The threshold now depends on which other profiles share the display. That *substitution effect* is ruled out by Rios & Torrico, who cite empirical support. So budgets void their analysis, and the guarantee would have to be redone.
- **Evidence.**
  - In [[Lee 2015 - Propose with a Rose]], scarce roses raise acceptance by about 3.3 points. But real users neither use all their roses nor aim them at attainable partners.
    - Naive users therefore shade less than the best response.
    - Optimizing LLM agents would shade fully.
  - [[Coles 2013 - Preference Signaling in Matching Markets]] gives the theory: workers signal their top firm, and signals raise matches and the welfare of the side that signals. Its tiered-preferences case is the analogue of shading.
  - See [[Preference Signaling]].

### S5. LLM value reports are cheap talk
- **B1/B3's period-2 rule.** It ranks $r$'s backlog by $\phi^2(\hat q_{rs}+\hat q_{sr})$. $r$'s agent wants its own top members shown.
  - *Example.* $K=1$, and $r$'s backlog is $\{s_1,s_2\}$ with $q_{rs_1}=1$, $q_{rs_2}=1/2$, $q_{s_1r}=0$, $q_{s_2r}=H$.
  - Truthful reports show $s_2$, with welfare about $H$.
  - Reporting $\hat q_{rs_1}>H+1/2$ gets $s_1$ shown, raising $r$'s own value from $1/2$ to $1$ while welfare falls to about $1$.
- **Equilibrium with bounded reports.** If reports lie in $[0,Q]$, each responder's agent reports $Q$ for its favorites and $0$ for the rest. The ranking becomes each responder's own preference, and the welfare loss is unbounded as $H\to\infty$.
- **Credit-DH's program and value-indexed DH-int's period-1 plan** allocate displays by reported values. Inflating your value for a popular profile raises your priority to be shown to them.
- **When reports are safe.** A report is safe when it only steers the reporter's own choice and the rule maximizes the reporter's own utility. An example is ranking $r$'s backlog by $\hat q_{rs}$ alone, a dictatorship over one's own display.
  - That gives up the sender's side of welfare.
  - The loss is zero when values are symmetric, and unbounded otherwise.
- **Design principle.** Elicit through actions with consequences (likes, roses), not numbers. Or let agents *act* (like or pass) on their users' behalf.

### S6. Using likes beyond consent breaks sincerity
- **The rule.** Suppose period 2 shows a responder's backlog in order of how *selective* each sender was, meaning how few profiles it liked. This is a natural heuristic for genuine interest.
- **The deviation.**
  - Sender $s$ is shown $r$ and $r'$ in period 1, and values both above cost.
  - Responder $r$ has one slot and a rival sender $t$ who liked exactly two profiles.
  - If $s$ likes both, the tie with $t$ is broken in $t$'s favor; if $s$ likes only $r$, $s$ is shown first.
  - When $q_{sr}$ is large, passing on $r'$ pays.
- **The general point.** Any dependence of one display on the user's *other* likes breaks S1.
- **More periods.** A platform that learns your taste from likes and adjusts later displays breaks sincerity the same way.

### S7. Strategic top-k users
- **Behavior.** Best responses are value-monotone, by S1. But in period 2, a user with a good period-1 match likes back only partners better than it.
- **Consequence.** Like probabilities then depend on realized history. That is the threshold history effect Rios & Torrico simulate, and their theory, R1–R4 and [[Top-k Match Quality]] all assume it away.
- **Open.** Guarantees for credit-DH against strategic top-k users.

## Formal statements and proofs
These are written-out proofs, not machine-checked.

**Setup.**
- **Market.** Two sides; display caps $K_\ell$; a design $\mathcal D$ of feasible period-1 decisions $d$. A decision consists of arcs $s\to r$ ($s$ sees $r$) and mutual-view edges. Each pair is shown at most one way, and each user gets at most $K_\ell$ displays.
- **Randomness.** Values $q_{\ell\ell'}$ are independent across ordered pairs. The platform's coins $\omega=(\omega_0,(\omega_r)_r)$ and each user's private randomization $\xi_\ell$ are independent of values and of each other.
- **Timing.**
  1. The platform commits to a policy.
  2. Period 1 shows $d$. Each shown user sees its value and likes or passes ($a_{\ell\ell'}\in\{0,1\}$), all at once. Mutual views match if both like, and $s\in B_r$ if $s\to r$ and $a_{sr}=1$.
  3. Period 2 shows each responder $S_r\subseteq B_r$ with $|S_r|\le K_r$. $r$ sees $q_{rs}$ for $s\in S_r$ and likes or passes.
- **Information.** A user knows:
  - its values for profiles shown to it;
  - its own likes;
  - its own mutual-view outcomes;
  - in period 2, the set $S_\ell$.

  It never sees other users' likes, backlogs or displays.
- **Strategies and match events.** A strategy picks each like as a function of the user's information and $\xi_\ell$.
  - A mutual view $\{\ell,\ell'\}$ matches iff $a_{\ell\ell'}a_{\ell'\ell}=1$.
  - An arc $s\to r$ matches iff $a_{sr}\,\mathbb 1[s\in S_r]\,a_{rs}=1$.
- **Consent-only.** The policy is consent-only if $d=d(\omega_0)$ and $S_r=g_r(B_r,\omega_r)$ for some functions $g_r$.

**Lemma 1 (a like changes one event).** Assume the policy is consent-only. Fix a realization of values and coins, a user $s$, and all other users' strategies. For each profile $\ell'$ shown to $s$, the indicator that $s$ and $\ell'$ match equals $a_{s\ell'}Z_{s\ell'}$, where $Z_{s\ell'}\in\{0,1\}$ depends on none of $s$'s actions.
- *Mutual view:* $Z=a_{\ell's}$.
- *$s$ initiates toward $r$:* $Z=\mathbb 1[s\in g_r(B^{-s}_r\cup\{s\},\omega_r)]\,a_{rs}$, where $B_r^{-s}$ is $r$'s backlog without $s$.
- *$s$ answers $r$ in period 2:* $Z=\mathbb 1[r\in S_s]$.

*Proof.*
- Period-1 actions are simultaneous, so no one's period-1 information depends on $s$.
- $a_{sr}$ enters only $B_r$, hence only $S_r$, which only $r$ observes.
- $r$'s later actions affect $s$ only through $a_{rs}$. $r$'s information in the formula for $Z_{sr}$ is $(B_r^{-s}\cup\{s\},\omega_r)$ together with $r$'s own values and mutual views. None of these involve $s$'s actions, since a pair is shown one way only.
- A mutual-view action of $s$ changes only $\ell'$'s knowledge of that one match. $\ell'$ cannot then affect $s$ through another pair, because they share no other pair.
- $B_s$, and so $S_s$, depends only on others' period-1 likes and $\omega_s$.
- Period-2 actions are last. $\square$

**Theorem 1 (sincere liking is ex-post dominant).** Under a consent-only policy with additive utilities, take any realization of values and coins and any strategies of the others. Then no strategy gives user $s$ more utility than liking exactly when $q_{s\ell'}>c_s$.

*Proof.* By Lemma 1, $u_s=\sum_{\ell'}a_{s\ell'}Z_{s\ell'}(q_{s\ell'}-c_s)$. Each term is at most $Z_{s\ell'}(q_{s\ell'}-c_s)^+$, and sincere liking attains that bound term by term. The $Z$'s are the same under every strategy of $s$. $\square$

**Corollary 1.** Under sincere play, likes are independent coins with $\phi_{\ell\ell'}=\Pr[q_{\ell\ell'}>c_\ell]$. They are the same in both periods and depend neither on history nor on the rest of the display, so Rios & Torrico's assumptions hold exactly.

**Proposition 1 (top-k users).** Take $u_s=\mathrm{top}_k(\cdot)-c_s|M_s|$ and a consent-only policy.
- **(a) Period 2.** Some optimal set of period-2 likes consists of the $j$ most valued members of $S_s$, for some $j$. *Proof.* These matches are certain. Swapping a liked member for a more valued unliked one raises $\mathrm{top}_k$ pointwise and leaves the cost unchanged.
- **(b) One like at a time.** Hold the rest of the realization fixed. The gain from liking $\ell'$ is $Z_{s\ell'}\big(\mathrm{top}_k(M\cup\{\ell'\})-\mathrm{top}_k(M)-c_s\big)$, which is nondecreasing in $q_{s\ell'}$. So if $s$'s other decisions don't depend on $q_{s\ell'}$, the best decision is a threshold in $q_{s\ell'}$.
- **(c) History dependence.** Suppose a top-1 responder already holds a period-1 match of value $v$, and is shown one member in period 2. It likes back iff $q>v+c$. So $\phi^2$ depends on realized history, and Corollary 1 fails.

**Lemma 2 (welfare identity).** Take any policy, consent-only or not, that observes only likes, and suppose everyone plays sincerely. Then $W=\mathbb E\sum_{e\in M}(A_{\ell\ell'}+A_{\ell'\ell})$, where $A_{\ell\ell'}=\mathbb E[q_{\ell\ell'}-c_\ell\mid q_{\ell\ell'}>c_\ell]$.

*Proof.*
- Every action is a function of the bits $b_{\ell\ell'}=\mathbb 1[q_{\ell\ell'}>c_\ell]$ and the coins, so the match set $M$ is too.
- Given the bits, $q_{\ell\ell'}$ has law $D_{\ell\ell'}$ conditioned on its own bit, independently of everything else.
- So $\mathbb E[\mathbb 1[e\in M](q_{\ell\ell'}-c_\ell)]=\mathbb E[\mathbb 1[e\in M]A_{\ell\ell'}]$, because $e\in M$ forces $b_{\ell\ell'}=1$. $\square$

**Theorem 2 (equilibrium welfare).** Take additive utilities. Weight DH-int by the expected welfare of a consented match: mutual views by $\beta_e(A_{\ell\ell'}+A_{\ell'\ell})$ and responses by $\phi_{rs}(A_{sr}+A_{rs})$, with $\phi=\Pr[q>c]$.
- (i) Sincere play is an ex-post equilibrium in weakly dominant strategies.
- (ii) Its welfare is at least $c_K\sup_\pi W(\pi;\text{sincere})$. The supremum is over all adaptive policies that observe likes.

*Proof.*
- (i) DH-int's period-2 rule shows $r$ the top $K_r$ of $B_r$ by fixed weights, so it is consent-only. Theorem 1 applies.
- (ii) By Lemma 2 and Corollary 1, welfare under sincere play is the objective of Rios & Torrico's Problem 4.2 with independent coins $\phi$ and non-negative rewards $A+A$.
  - The best adaptive policy is $\max_d$ of that objective, since period-2 choices separate across responders.
  - R2 then gives $c_K$. It is machine-checked as `dhInt_quality_approx_cK` in `lean/DatingAlgo/PoissonGap.lean`. $\square$

**Proposition 2 (no information when matches are free).** Suppose $c_\ell=0$ and $q\ge0$. Then sincere means liking everyone, $\phi\equiv1$, and a match reveals nothing about $q$.
- Theorem 2 still holds, with $A=\mathbb E[q]$.
- The display cap $K$ already acts as an application limit, so the congestion collapse of [[Arnosti 2021 - Managing Congestion in Matching Markets]] does not arise in two curated periods.

**Proposition 3 (cheap-talk reports).**
- **Variant.** Between periods, agents report values in $[0,Q]$:
  - $\hat q_{rs}$ for each $s\in B_r$, by $r$'s agent;
  - $\hat q_{sr}$ for each $r$ that $s$ liked, by $s$'s agent.

  The rule shows $r$ the top $K_r$ of $\{s\in B_r:\hat q_{rs}>c_r\}$ by $(\hat q_{rs}-c_r)+(\hat q_{sr}-c_s)$. This is B1's rule with reports in place of screened values. Users like sincerely.
- **(a) Senders report the maximum.** For a sender, reporting $\hat q_{sr}=Q$ is weakly dominant.
  - Its report affects only whether it is in $S_r$, and only upward.
  - Being shown gives it $a_{rs}(q_{sr}-c_s)\ge0$, since a sincere sender liked $r$ only if $q_{sr}>c_s$.
- **(b) Responders dictate.** For a responder, reporting $Q$ for its $K_r$ most valued members with $q_{rs}>c_r$, and $0$ for the rest, is weakly dominant.
  - Members reported $0$ are excluded, because $0\le c_r$.
  - So $S_r$ becomes exactly $r$'s own favorites, which maximizes $r$'s payoff $\sum_{s\in S_r}(q_{rs}-c_r)^+$.
  - Hence dominant strategies implement *responder dictatorship*.
- **(c) Welfare.** Responder dictatorship can earn an arbitrarily small fraction of the welfare of truthful reports, which B1 bounds by $c_K$.
  - *Example.* $K=1$; the responder's net values are $1$ and $1/2$, and the senders' are $\varepsilon$ and $H$. Truthful reports give welfare $H+1/2$; dictatorship gives $1+\varepsilon$.
  - The two outcomes coincide when net values are symmetric.
- **(d) Report-based programs.** Credit-DH and value-indexed DH-int give their plans the same weakness.
  - *Example.* One responder with one slot, and two initiators who both like it.
  - The program sets $y=1$ on whichever reports the higher value.
  - So inflating one's report strictly raises one's chance of being shown.

**Proposition 3′ (what truthful report rules can do).** Use the variant of Proposition 3, with any rule, possibly randomized, mapping reports and backlogs to displays. Users like sincerely.
- **(a) Senders.** Suppose truthful reporting is dominant for sender $s$. Then $s$'s report cannot change its own probability of being shown to $r$ (given everyone else's reports).
  - *Proof.* Every type of $s$ that is in $B_r$ has $q_{sr}>c_s$, so being shown to $r$ has value $\Pr[r\text{ likes }s](q_{sr}-c_s)\ge0$ for every type.
  - If two reports gave different chances of being shown, the type sent to the lower chance would gain by sending the other report. That gain is strict whenever $\Pr[r\text{ likes }s]>0$.
  - So the platform can never use a sender's own value to prioritize that sender.
- **(b) Responders.** A deterministic rule is truthful for responder $r$ iff it has a *menu* form. That means a set $\mathcal M$ of possible displays, depending on $B_r$ and others' reports but not on $r$'s, such that $r$ is always shown its favorite element of $\mathcal M$, by $\sum_{s\in S}(q_{rs}-c_r)^+$.
  - *Proof.* This is the taxation principle without money. If the chosen display is not $r$'s favorite in the rule's range, some type misreports to reach a better one. Conversely, a favorite-in-menu rule leaves no profitable misreport.
- **Consequence.** Truthful use of agents' reports means *delegation through a menu*.
  - The platform decides which displays are allowed, and the agent picks.
  - It cannot weigh one user's report against another's.
  - The extremes are a single-item menu (DH-int on priors, which ignores reports) and the full menu (responder dictatorship).
  - Which menu is best, and how close it gets to truthful sum-ranking, is open.

**Proposition 4 (ranking by selectivity breaks sincerity).**
- **Rule.** A responder's backlog is shown in order of how few period-1 likes each sender gave. Ties go to $t$ (by a fixed or random tie-break).
- **Instance.**
  - Sender $s$ (cost 1) is shown $r$ and $r'$, with $q_{sr}=10$ and $q_{sr'}=2$.
  - $r$ has one slot. A rival $t$ liked exactly two profiles, including $r$.
  - $r'$ answers everyone, and all responders like back.
- **Payoffs.**
  - Sincere play earns $\tfrac12\cdot9+1=5.5$ with a fair tie-break.
  - Passing on $r'$ earns $9$.

So a strategy that hides a valuable like does strictly better.

**Proposition 5 (like budgets $L$).** Take a consent-only policy and additive utilities.
- **(a) Period 2.** The best response likes the $\min(L,\#\{q>c\})$ most valued shown members.
- **(b) Period 1.** By Lemma 1, $u_s=\sum_{r\in\text{likes}}Z_{sr}(q_{sr}-c_s)$, and $\pi_{sr}=\mathbb E Z_{sr}$ does not depend on $s$'s actions. So the best response likes the $L$ profiles with the largest positive $\pi_{sr}(q_{sr}-c_s)$.
  - *Shading example.* $L=1$, $c=0$; values $10$ and $3$, with match chances $0.05$ and $0.5$. The initiator likes the second.
- **(c) Substitution.** Whether $s$ likes $r$ now depends on the other profiles in $s$'s display. That breaks Rios & Torrico's no-substitution assumption.
- **(d) What survives.**
  - For a fixed $d$, arrivals at a responder remain independent across senders, because each sender's likes depend only on its own values and display.
  - So R1's lemma still bounds each responder against the program built from $\phi_{sr}(d)$.
  - What breaks is that $\phi_{sr}(d)$ depends on $s$'s whole display. The program is no longer linear in $d$, and $\pi$ is an equilibrium fixed point.

## Evidence
- [[Rios 2026 - The Dating Heuristic]]: the model, the designs, and the no-substitution and history assumptions.
- [[History-Dependent Like Probabilities]]: the history effects strategic users produce.
- [[Match Quality with Queried Values]]: B1, B3 and value-indexed DH-int, whose report-based rules S5 shows are manipulable.
- [[Top-k Match Quality]]: credit-DH, also report-based.
- [[Match Quality in the Dating Heuristic Framework]]: R2, which S2 applies.
- [[Coles 2013 - Preference Signaling in Matching Markets]], [[Lee 2015 - Propose with a Rose]], [[Preference Signaling]]: scarce signals (S3, S4, S5).
- [[Arnosti 2021 - Managing Congestion in Matching Markets]]: free applications and limits (S3, Proposition 2).
- [[Kanoria 2021 - Facilitating the Search for Partners on Matching Platforms]], [[Congestion in Matching Markets]]: costly screening, the effective cost $c/p$, and restricting who initiates.
- **Brute force, 2026-10-21.** `data/scripts/strategic_check.py`, run on two seeds:
  - *Theorem 1.* Under both consent-only period-2 rules, no deviation ever beat sincere liking on any realization. This covered 160 random markets (one-directional, and two-directional with mutual views), 200 realizations each, and about 30 deviations per market: arbitrary strategies, dropping one like, and liking only the best.
  - *Selectivity rule.* A profitable deviation turned up in random markets, though rarely: an expected gain of 0.018, and up to 5 on a single realization. Proposition 4's example gives 9 vs 5.5.
  - *Lemma 2.* Truth and identity agreed to within $3\times10^{-13}$ on 400 exact computations, for a consent-only and a non-consent rule.
  - *Proposition 3.* Responder dictatorship's welfare ratio reached $0.021$ on random backlogs.

## Gaps
- **Proofs.** They are written out but not machine-checked. Theorem 1 and Lemma 2 would be natural Lean targets; Theorem 2 then follows from the existing R2.
- **Who should initiate.** [[Kanoria 2021 - Facilitating the Search for Partners on Matching Platforms]] shows that blocking one side from proposing can raise equilibrium welfare. Could a one-directional DH-int beat a two-directional one once likes are costly or budgeted? With free likes and additive users (Theorem 2) it cannot.
- **Interdependent values.** [[Lee 2015 - Propose with a Rose]] suggests that recipients value the sender's interest itself, so values are not purely private. The model here assumes independent private values.
- **Not addressed yet:**
  - guarantees under like budgets;
  - incentive-compatible ways to use agents' reports;
  - more than two periods;
  - strategic top-k users.
- **Follow-up.** [[Truthful Swiping with an LLM Oracle]] adds a truthful oracle: it characterizes when sincere swiping is dominant (top-k: at most k acceptable profiles seen), shows DH is not truthful for top-k, and gives screened DH.
