---
type: synthesis
question: "With a truthful, accurate LLM oracle for match values, can a dating-heuristic platform make sincere swiping a dominant strategy, earn close to full-information welfare, and use few oracle queries, for additive, top-k and general utilities?"
created: 2026-10-22
updated: 2026-10-26
tags: [dating/platforms, matching/quality, game-theory/incentives, elicitation, research/project]
aliases: [truthful swiping, sincere swiping, screened DH, SDH, price of individual rationality, cost-separable, swipe-local policy, DSIC swiping]
sources: ["[[Rios 2026 - The Dating Heuristic]]", "[[Lee 2015 - Propose with a Rose]]"]
origin: claude
status: seed
---
# Truthful Swiping with an LLM Oracle

> [!question] With a truthful, accurate LLM oracle for match values, can a dating-heuristic platform make sincere swiping a dominant strategy, earn close to full-information welfare, and use few oracle queries, for additive, top-k and general utilities?

> [!note] Preliminary
> Written 2026-10-22. Revised 2026-10-26: the terminology for dominant strategies is fixed, and the note adds Section T5 (DSIC), a worked example and a glossary. Every result is machine-checked in Lean except the continuous-values extension of Theorem 3(b) (see Evidence). Formalizing corrected Theorem 3(c), sharpened Theorem 2(b) from $1/\lceil b/k\rceil$ to $k/b$, and weakened the hypotheses of Theorem 4 and Proposition 6(b) to $np\to\infty$. This continues [[Strategic Users in the Dating Heuristic Framework]], with the choices made for this phase:
> - a truthful swipe is the *sincere threshold*: swipe right iff the match is worth it on its own;
> - match costs first, then swipe budgets;
> - welfare is compared with *full information*, the best policy that knows every value;
> - when dominant strategies fail, report the impossibility, then try both a Bayes–Nash guarantee for DH and a changed game.
>
> As in earlier notes, $c_\ell$ is user $\ell$'s match cost and $c_k=1-e^{-k}k^k/k!$ is the Poisson constant.
>
> **Reading aids.** The [[#Glossary]] at the end defines every technical term, grouped by topic. The [[#Worked example]] runs SDH by hand on a four-user market.

## Answer

**Summary**
- **Truthfulness constrains what users see, not how displays are chosen (Theorem 1).**
  - Call a policy *swipe-local* if displays depend only on the oracle's answers, coins, and (for a responder) its own backlog.
  - Under such a policy, sincere swiping is a dominant strategy, best whatever the others do, exactly when every acceptable profile a user sees adds at least $c_\ell$ to every set of the other acceptable profiles they see.
  - **Additive:** always holds.
  - **Top-k:** holds iff the user sees at most $k$ acceptable profiles.
  - **Matroid-rank** (e.g. at most one partner per city): holds iff the acceptable profiles seen are independent.
- **Impossibility 1: DH is not truthful for top-k.**
  - DH-int and credit-DH can show a top-$k$ user more than $k$ acceptable profiles.
  - Then *no* swipe rule is dominant (the 10/5 example below).
  - With values just above cost, sincere swiping isn't even a Bayes–Nash equilibrium.
- **Impossibility 2: the price of individual rationality (Theorem 2).**
  - **Bound.** For top-$k$, no mechanism whose equilibrium is sincere swiping (dominant, ex post or Bayes–Nash; auditing with the oracle included) earns more than about $k/b$ of the full-information optimum. Here $b$ is the most matches the design allows a user ($2K$ in two-directional designs).
  - **Tight.** The best outcome that gives no user more than $k$ matches already earns $k/b$, so the price is exactly about $k/b$. (The 2026-10-22 version proved only $1/\lceil b/k\rceil$; formalizing sharpened it.)
  - **Subadditive utilities.** The price is at most $b$, and top-1 makes that tight for the class.
  - **Additive.** No price.
  - **Why.** The full-information benchmark exploits sincere users. It gives them matches they would accept one at a time but not all together. No mechanism that users play voluntarily can do that.
- **Impossibility 3: queries are unavoidable (Theorem 4).** Getting a constant fraction of full information takes $\Omega(b/p)$ oracle calls per user, where $p$ is the chance a pair is mutually acceptable. That holds even without incentives. Free swipes are worth only about $b$ calls per user.
- **Mechanism: screened DH (SDH, Theorem 3).**
  1. **Plan.** Solve DH's program in its full-information form.
  2. **Screen.** Query each pair with the probability the plan needs.
  3. **Select.** Pick the best match set among the pairs found acceptable, capping each user at an *IR set*: one the user would keep in full.
  4. **Show.** Use DH's two periods: initiations, then backlog responses.

  Every shown pair matches, and sincere swiping is dominant whatever the others do (DSIC, T5).

  | Utility class | SDH guarantee | Upper bound for any truthful mechanism | Oracle calls per user |
  | --- | --- | --- | --- |
  | additive | $c_b^2\,\mathrm{OPT_{FI}}$ | $\mathrm{OPT_{FI}}$ | $O(b/\hat p)$ |
  | top-$k$ | $c_{k}^2\,\mathrm{OPT_{IR}}\ge c_k^2\,\frac kb\,\mathrm{OPT_{FI}}$ | $\approx\frac kb\,\mathrm{OPT_{FI}}$ | $O(k/\hat p)$ |
  | matroid rank | $(1-1/e)^2\,\mathrm{OPT_{IR}}$ | $\mathrm{OPT_{IR}}$ | $O(\text{rank}/\hat p)$ |
  | subadditive | $\frac{c_1^2}{b}\mathrm{OPT_{FI}}\approx\frac{0.40}{b}\mathrm{OPT_{FI}}$ | $\approx\frac1b\,\mathrm{OPT_{FI}}$ | $O(1/\hat p)$ |

  - $\hat p$ is, roughly, the chance a queried pair passes the plan's bar ($\hat p=p$ when values are fixed); Theorem 3(c) gives the exact definition.
  - With a budget of $Q$ calls per user, SDH gets a $\min(1,Q\hat p/b')$ fraction of these guarantees, which matches Theorem 4 up to constants.
- **Dominant strategies, not just ex post (T5).**
  - Every "dominant" claim in this note holds against *any* behavior of the other users, sincere or not, adaptive or not, and for every outcome of the platform's coins. That is DSIC in its strongest, universal form.
  - The 2026-10-22 version said "ex-post dominant". That clashed with the standard *ex-post IC*, which only asks for a best response when the others are truthful. The proofs never assumed that.
  - The results weaker than DSIC are Proposition 4 (an approximate Bayes–Nash equilibrium) and the menu design of Proposition 5(d).
  - **Without queries, DSIC is expensive for top-$k$.** It forces each user to see at most $k$ profiles that can match them. On a random market where pairs are acceptable with probability $p$, that caps top-1 welfare at about $2p\,\mathrm{OPT_{IR}}$ (Proposition 6). The oracle is what makes DSIC affordable.
  - **DSIC covers swipes, not the oracle.** If users could steer what their LLM agent tells the platform, SDH would not be truthful in those reports.
- **Bayes–Nash route inside DH (Proposition 4).**
  - **Regret.** For top-$k$ users under any swipe-local policy, sincere swiping's regret is exactly $c_\ell(|M_\ell|-k)^+$: the cost of dates beyond the $k$-th.
  - **Welfare.** Credit-DH run on net values loses exactly the same amount against $\rho c_k$ of the best no-query policy.
  - **So** DH is approximately truthful when users rarely get more than $k$ matches. Equilibria with thresholds above cost are open.
- **Budgets (Proposition 5).**
  - Sincere swiping is feasible only if a user sees at most $L$ acceptable profiles per period.
  - SDH with per-period caps $\min(K,L)$ never hits the budget, so every result holds with $K\to\min(K,L)$.
  - Without screening, binding budgets bring back shading ([[Strategic Users in the Dating Heuristic Framework|S4]]).
- **What swipes do here.** With a truthful oracle, swipes are *consent*, not information: SDH shows only pairs it knows will accept. Truthfulness still matters, because a planned match forms only if both users actually swipe right. With no queries, swipes are the only information, and sincere play makes like probabilities known: $\phi=\Pr[q>c]$.

### Model
This is the two-period model of [[Rios 2026 - The Dating Heuristic]], with the strategic layer of [[Strategic Users in the Dating Heuristic Framework]].
- **Values and costs.** $q_{\ell x}\ge0$ is $\ell$'s value for $x$, drawn from a known prior, independently across ordered pairs. Each match costs $\ell$ an amount $c_\ell>0$.
- **Utility.** $u_\ell(S)=v_\ell(S)-c_\ell|S|$ for the set $S$ of $\ell$'s matches, where $v_\ell$ is monotone, $v_\ell(\emptyset)=0$ and $v_\ell(\{x\})=q_{\ell x}$. The classes are:
  - *additive:* $v(S)=\sum_S q$;
  - *top-$k$:* the $k$ largest values in $S$;
  - *weighted matroid rank:* the most valuable subset of $S$ that is independent in a matroid $\mathcal M_\ell$. Top-$k$ is the uniform matroid; "at most one partner per city" is a partition matroid;
  - *subadditive:* $v(S\cup T)\le v(S)+v(T)$. This includes submodular and XOS.
- **Swipes.** Shown $x$, user $\ell$ likes or passes. A match needs both likes: a mutual view in period 1, or a period-1 initiation answered in period 2. A pair is shown at most one way.
  - **Sincere:** like iff $q_{\ell x}>c_\ell$.
  - **Like probability:** $\phi_{\ell x}=\Pr[q_{\ell x}>c_\ell]$.
- **Oracle.** A query $(\ell,x)$ returns $q_{\ell x}$ exactly and costs one call, charged to $\ell$.
  - For matroid-rank users the platform also knows $\mathcal M_\ell$.
  - For general utilities the oracle answers $v_\ell(S)$.
  - The platform therefore knows each user's utility class and $k$.
- **Acceptable graph.** $G(q)$ is the set of pairs where both values exceed cost.
  - $p_e=\phi_{\ell x}\phi_{x\ell}$ is the chance pair $e$ is acceptable.
  - $w_e=(q_{\ell x}-c_\ell)+(q_{x\ell}-c_x)>0$ is its net weight.
- **Capacity.** $b_\ell$ is the most matches the design allows $\ell$:
  - $2K_\ell$ in two-directional designs;
  - in one-directional designs, $K_\ell$ for initiators, and for responders $K_\ell$, or $2K_\ell$ with period-1 mutual views.
- **Benchmarks.**
  - $\mathrm{OPT_{FI}}$: the best policy that knows every value, facing sincere users.
  - $\mathrm{OPT_{IR}}$: the same, but every user's match set must be one the user would keep in full.
  - $\mathrm{OPT_0}$: the best policy that makes no queries.

**Lemma R (realizability).** If likes are certain, a match set can be shown in the design iff every user $\ell$ has at most $b_\ell$ matches.
- *Two-directional designs.* A graph with degrees at most $2K$ has an orientation with in- and out-degree at most $K$: add a vertex joined to every odd-degree vertex and follow Euler tours. Out-arcs are period-1 initiations and in-arcs are period-2 responses.
- *One-directional designs.* Orient every pair from initiator to responder. With mutual views, a responder splits its pairs into at most $K$ mutual views and at most $K$ responses.

Hence $\mathrm{OPT_{FI}}=\mathbb E\max\{\sum_\ell u_\ell(M_\ell):M\subseteq G(q),\ \deg_M\le b\}$. Sincere users never match outside $G$.

### T1. When sincere swiping is dominant
**Swipe-local policies.**
- Period-1 displays are $d(\omega_0,q)$, and responder $r$'s period-2 display is $S_r=g_r(B_r,\omega_r,q)$.
- Displays may depend on oracle answers, since those are functions of $q$, which no swipe changes.
- Included: DH-int, credit-DH, B1's screening, and SDH below.
- Excluded:
  - rules that use a user's likes elsewhere ([[Strategic Users in the Dating Heuristic Framework|S6]]);
  - rules where a user's period-2 display depends on its own period-1 outcomes.

**Lemma 1′ (one swipe, one event).** Under a swipe-local policy, fix values, coins and others' strategies.
- The set $N_\ell$ that $\ell$ sees does not depend on $\ell$'s actions.
- For each $x\in N_\ell$, $\ell$ and $x$ match iff $\ell$ likes $x$ and $Z_{\ell x}=1$, where $Z_{\ell x}$ does not depend on $\ell$'s actions.

*Proof.* This is Lemma 1 of [[Strategic Users in the Dating Heuristic Framework]]. Adding $q$ to the arguments changes nothing, because $q$ is exogenous. $\square$

**Theorem 1 (characterization).** Let $v_\ell$ be subadditive and the policy swipe-local. Let $A=\{x\in N_\ell:q_{\ell x}>c_\ell\}$ be the acceptable profiles $\ell$ sees. Call $A$ *cost-separable* if $v(T\cup\{x\})-v(T)\ge c_\ell$ for every $x\in A$ and every $T\subseteq A\setminus\{x\}$.
- (a) Suppose $A$ is cost-separable in every realization, whatever the others do. Then sincere swiping is dominant for $\ell$: in every realization of values and coins, and against any behavior of the others, no other swipes give $\ell$ more.
- (b) Conversely, suppose that with positive probability $A$ is not cost-separable, and the profiles involved can all match $\ell$ at once for some strategies of the others. Then sincere swiping is not dominant.

*Proof.*
- By Lemma 1′, if $\ell$ likes the set $D$, its matches are $D\cap R$, where $R=\{x:Z_{\ell x}=1\}$ doesn't depend on $\ell$. Sincere play gets $A\cap R$.
- Subadditivity gives $v(T\cup\{x\})-v(T)\le v(\{x\})\le c_\ell$ for $x\notin A$. So removing unacceptable profiles never lowers $u$.
- Cost-separability means adding acceptable ones never lowers $u$ either.
- Go from $D\cap R$ to $A\cap R$ by adding $(A\cap R)\setminus D$ one at a time, then removing $D\setminus A$. Hence $u(A\cap R)\ge u(D\cap R)$.
- (b) Take the violating $x$ and $T$, and strategies under which exactly $T\cup\{x\}$ match $\ell$. Sincere play gets $T\cup\{x\}$; skipping $x$ gets $T$, which is strictly better. $\square$

*In words.* Under a swipe-local policy your swipes only decide which of the profiles you are shown you end up matched with. They cannot change who is shown to you or who would like you back. So the only reason to pass on someone you like is that adding them would make your set worse. That happens exactly when one more match adds less than its cost:
- for additive users, never;
- for top-$k$ users, once you could end up with more than $k$ matches.

**Corollaries** (with $c_\ell>0$).
- **Additive:** always cost-separable. This is Theorem 1 of the strategic note.
- **Top-$k$:** cost-separable iff $|A|\le k$.
  - If $|A|\ge k+1$, the least valued of $k+1$ acceptable profiles adds $0<c_\ell$ to the other $k$.
  - If $|A|\le k$, top-$k$ is additive on $A$.
- **Matroid rank:** cost-separable iff $A$ is independent in $\mathcal M_\ell$.
  - If $A$ contains a circuit $C$, its least valued element $x$ has $v(C)=v(C\setminus x)$.
  - If $A$ is independent, $v$ is additive on $A$.
- **Zero cost:** with $c_\ell=0$ every monotone $v$ is cost-separable. Sincere swiping is dominant but says nothing ([[Strategic Users in the Dating Heuristic Framework|S3]]).

**Impossibility 1 (DH-style policies and top-$k$).**
- DH-int, weighted DH-int and credit-DH are swipe-local, but they show a user up to $K$ profiles per period. Once a top-$k$ user can see $k+1$ acceptable ones, part (b) applies.
- **No dominant strategy at all.** A top-1 sender with cost 1 initiates toward $r_1$ (value 10) and $r_2$ (value 5).
  - If both would like back, liking only $r_1$ earns 9 and liking both earns 8.
  - If only $r_2$ would, liking only $r_1$ earns 0 and liking both earns 4.

  So the best swipes depend on the others' strategies.
- **Not even Bayes–Nash.** Suppose that when $\ell$ swipes on $x$, with probability at least $\pi$ the profile $x$ matches back *and* $\ell$ ends up with $k$ other matches worth at least $q_{\ell x}$.
  - Then liking $x$ gains at most $(q_{\ell x}-c_\ell)-\pi c_\ell$ in expectation.
  - That is negative when $q_{\ell x}<c_\ell(1+\pi)$.
  - So if the prior has mass just above cost, sincere swiping is not a best response.
  - *Example:* $c=1$, value $1.05$, $\pi=0.3$, and $x$ always likes back. The expected gain is exactly $0.7\cdot0.05-0.3\cdot1=-0.265$; the general bound gives $-0.25$.

### T2. The price of individual rationality
**Theorem 2.** Let $b=\max_\ell b_\ell$.
- **(a) Bound for truthful mechanisms.** For top-$k$ users and any $\varepsilon>0$, some instance has the following property. Every mechanism in which sincere swiping is an equilibrium (dominant, ex post or Bayes–Nash) earns at most $(1+\varepsilon)\frac kb+o(1)$ of $\mathrm{OPT_{FI}}$.
- **(b) Matching guarantee.** $\mathrm{OPT_{IR}}\ge\frac kb\,\mathrm{OPT_{FI}}$ for $k\le b$, where $\mathrm{OPT_{IR}}$ caps each user at $\min(k,b)$ matches. That cap is exactly the set of top-$k$ outcomes users keep in full. Since $k/b\ge1/\lceil b/k\rceil$, this also gives the first version's $\mathrm{OPT_{FI}}/\lceil b/k\rceil$, and it matches (a).
- **(c) Subadditive utilities.** The best matching is at least $\mathrm{OPT_{FI}}/b$, and (a) with $k=1$ shows this is tight for the class.
- **(d) Additive utilities.** No price: $\mathrm{OPT_{IR}}=\mathrm{OPT_{FI}}$.

*Proof.*
- **(a) Instance.**
  - A top-$k$ user $a$ has cost 1 and $b$ admirers, and values each admirer at $1+\varepsilon$.
  - Each admirer values $a$ at $H$, has cost 1, and has no other partner.
  - $\mathrm{OPT_{FI}}$ shows $a$ all $b$ admirers (Lemma R), for welfare $b(H-1)+(1+\varepsilon)\min(k,b)-b$.
- **(a) Any equilibrium.**
  - In any equilibrium $a$ can pass on everyone, so $\mathbb E\,u_a\ge0$. With $m$ matches that reads $\mathbb E[(1+\varepsilon)\min(m,k)-m]\ge0$, so $\mathbb E\,m\le(1+\varepsilon)k$.
  - Welfare is then at most $\mathbb E\,m\,(H-1)+\varepsilon k$.
  - Let $H\to\infty$.
  - The argument only uses $\mathbb E\,u_a\ge0$. So it also covers a platform that *audits* swipes with the oracle and punishes insincere ones: punishment can push users toward accepting more, but never below zero utility.
- **(b)** Fix a realization and an optimal $M$.
  - Since $\mathrm{top}_k\le$ sum and every term $q-c$ is positive, $W(M)\le\sum_{e\in M}w_e$.
  - The graph is bipartite with degrees at most $b$, so by König's edge-coloring theorem $M$ splits into $b$ matchings, colored $0,\dots,b-1$.
  - Take the $b$ windows of $k$ cyclically consecutive colors. Each edge lies in exactly $k$ windows, so the windows' weights sum to $k\sum_M w$, and the best window $M'$ carries at least a $k/b$ share. (Grouping the matchings into $\lceil b/k\rceil$ blocks, as the first version did, only gives $1/\lceil b/k\rceil$.)
  - On $M'$ every user has at most $k$ matches, so $W(M')=\sum_{M'}w_e$.
- **(c)** Subadditivity gives $W(M)\le\sum_{e\in M}w_e$, and a single partner is always cost-separable. Use $b$ matchings in place of the groups.
- **(d)** Every match in $G$ raises both users' utility. $\square$

**Reading.** The gap is not caused by swipes needing to be truthful. In the benchmark, sincere users accept every match they'd accept on its own, even when the bundle hurts them. No mechanism that users play voluntarily can do that. For top-$k$ and general utilities, the meaningful benchmark is $\mathrm{OPT_{IR}}$, and against it SDH gets constants.

### T3. Screened DH
**IR families.** Each user gets a family $\mathcal F_\ell$ of sets they'd keep in full:
- sets of size at most $b'_\ell$, where $b'_\ell=b_\ell$ (additive), $\min(b_\ell,k)$ (top-$k$), or $1$ (general subadditive);
- or, for matroid-rank users, the independent sets of $\mathcal M_\ell$ truncated at $b_\ell$.

On such sets every user's utility is additive, so welfare is $\sum w_e$.

**SDH.**
1. **Plan.** For pair $e=\{\ell,x\}$, a value combination is the vector $s=(q_{\ell x},q_{x\ell})$. For each acceptable combination $s$, its net weight is $w_{e,s}=(s_1-c_\ell)+(s_2-c_x)$; let $\pi_{e,s}=\Pr[e\text{ acceptable with combination }s]$. Solve
   $$\max\sum_{e,s}w_{e,s}\,x_{e,s}\quad\text{s.t.}\quad0\le x_{e,s}\le\pi_{e,s},\qquad\Big(\textstyle\sum_s x_{e,s}\Big)_{e\ni\ell}\in P(\mathcal F_\ell)\ \ \forall\ell.$$
   - For size caps the last constraint is $\sum_{e\ni\ell}x_e\le b'_\ell$.
   - Without loss of generality, each pair's mass fills its highest-weight combinations first, and splits the last level it reaches (the *bar*) proportionally among the combinations tied there. Such a plan is *bar-shaped*.
   - This is DH-int's period-2 program in the full-information limit: the like probability $\phi$ is replaced by the probability that screening finds a combination.
   - *In words:* $x_{e,s}$ is how often the plan matches pair $e$ when the pair's values are $s$.
     - The plan cannot match a pair more often than the pair has those values ($x_{e,s}\le\pi_{e,s}$).
     - It respects each user's IR family only *on average*, so it is a relaxation: in a given realization it may have promised a user more matches than fit.
     - "Highest-weight combinations first" means that a plan using pair $e$ only some of the time uses it when $e$ is worth the most. So there is a weight bar below which the plan never uses $e$.
2. **Screen.** Query pair $e$ with probability $\tau_e=\max_s x_{e,s}/\pi_{e,s}$: just enough that screening finds $e$ in each combination at least as often as the plan uses it. Ask the side less likely to accept first, and the other side only if the first accepts. The second call is skipped whenever the first answer is no, so starting with the likelier "no" saves calls.
3. **Select.** Take a maximum-weight $M$ among the pairs found acceptable, with $M_\ell\in\mathcal F_\ell$. This is a bipartite $b$-matching, or a weighted matroid intersection, so it is polynomial.
4. **Show.** Orient $M$ as in Lemma R. Period 1 shows the initiations. In period 2, each responder sees its planned initiators who liked it.

**Theorem 3.**
- **(a) Truthful.** SDH is swipe-local, and each user sees only planned partners, all of them acceptable.
  - Under sincere play a user sees exactly its planned set, which lies in $\mathcal F_\ell$ and is cost-separable.
  - If others deviate, a responder sees only the planned initiators who actually liked it. That is a subset of its planned set, so it is still in $\mathcal F_\ell$.
  - So sincere swiping is dominant (Theorem 1) for every outcome of the platform's coins, whatever the others do (T5).
  - Under sincere play every shown pair matches.
- **(b) Welfare.** $\mathbb E\,W\ge\gamma\,\mathrm{LP}\ge\gamma\,\mathrm{OPT_{IR}}$, with $\gamma=c_{b'}^2$ for size caps ($b'=\min_\ell b'_\ell$) and $\gamma=(1-1/e)^2$ for matroids.
- **(c) Queries.** Take a bar-shaped plan. Let $\hat p_e$ be the probability of an acceptable combination strictly above $e$'s bar if that is positive, and otherwise the probability of one at the bar; it equals $p_e$ when values are fixed. Let $\hat p=\min\hat p_e$ over the pairs the plan uses. The expected calls charged to $\ell$ are at most
  $$\sum_{e\ni\ell}\tau_e\ \le\ \sum_{e\ni\ell}x_e/\hat p_e\ \le\ b'_\ell/\hat p.$$
  A queried pair costs at most $1+\min(\phi_{\ell x},\phi_{x\ell})\le1+\sqrt{p_e}$ calls.

  > [!warning] Correction (found while formalizing, 2026-10-26)
  > The first version filled each pair's combinations from the top in an arbitrary order and defined $\hat p_e$ as the chance of reaching "at or above the threshold". Both break $\tau_e\le x_e/\hat p_e$:
  > - *Ties at the bar.* Two combinations at the bar, each with probability $1/2$, and $x_e=1/2$. Filling one first gives $x=(1/2,0)$, so $\tau_e=1$ while $x_e/\hat p_e=1/2$. Splitting the bar proportionally gives $x=(1/4,1/4)$ and $\tau_e=1/2$.
  > - *"At or above".* With mass above the bar, $\tau_e=1$ while $x_e$ can be below the mass at or above the bar.
  >
  > The corrected statement above is the one proved in Lean. The brute-force script never hit a tie at a partially filled bar, so it did not catch this.
- **(d) Query budget.** Scaling the plan by $\lambda=\min(1,Q\hat p/b')$ keeps calls at most $Q$ per user and gives $\mathbb E\,W\ge\gamma\lambda\,\mathrm{OPT_{IR}}$.

*Proof of (b).*
- **Idea.**
  - The plan keeps its promises only on average, so in a given realization a user may have more found pairs than its cap allows.
  - The proof settles these conflicts in two rounds, first on one side and then on the other, and shows that each round keeps at least a $c_{b'}$ fraction.
  - $c_{b'}$ measures what is lost when a random number of candidates, with mean at most $b'$, is cut down to $b'$.
- **Upper bound.** For each realization take an optimal $M^*(q)$ with $M^*_\ell\in\mathcal F_\ell$. Then $x_{e,s}=\Pr[e\in M^*,\ \text{combination }s]$ is feasible and has value $\mathrm{OPT_{IR}}$.
- **Candidates.** After screening, each pair is found with combination $s$ independently, with probability $\tau_e\pi_{e,s}\ge x_{e,s}$. For the analysis only, thin this to exactly $x_{e,s}$.
- **Two-stage selection.**
  - Each responder-side user keeps its best feasible subset of candidates.
  - Each user on the other side keeps its best feasible subset of what was kept.
  - The result is feasible and lies inside the found pairs, so SDH's choice is at least as good.
- **Stage 1.**
  - *Layer cake:* a size-$b'$ best subset is worth $\int_0^\infty\min(N(\theta),b')\,d\theta$, where $N(\theta)$ counts candidates of weight at least $\theta$.
  - $N(\theta)$ is a sum of independent indicators with mean at most $b'$, so R1's lemma ([[Match Quality in the Dating Heuristic Framework]]) gives $\mathbb E\min(N,b')\ge c_{b'}\,\mathbb E N$.
  - So stage 1 keeps at least $c_{b'}\,\mathrm{LP}$.
- **Stage 2.** The pairs kept at a user come from different responder-side users, so they are independent with marginals at most $x$. The same lemma gives another $c_{b'}$.
- **Matroids.** Replace R1's lemma by the $1-1/e$ [[Correlation Gap]] of matroid rank functions. The layer cake works the same way, since weighted rank is the integral of the rank of the superlevel sets. $\square$

*Proof of (c).*
- If some combination strictly above the bar has mass, it is used whenever it occurs, so $x_e$ is at least that mass, which is $\hat p_e$. And $\tau_e\le1\le x_e/\hat p_e$.
- Otherwise only the bar level has mass. Every combination there is used the same fraction $f$ of the time, so $\tau_e=f$ and $x_e=f\hat p_e$.
- An unused pair has $\tau_e=0$. Finally, $\sum_{e\ni\ell}x_e\le b'_\ell$. $\square$

*Bar shape is without loss of generality.* Fix a pair and its total $x_e$. Fill from the top as above, giving $y$. Then $\sum_s(w_{e,s}-\theta)(y_s-x_{e,s})\ge0$ term by term, because $y\ge x$ above the bar $\theta$ and $y\le x$ below it, and $\sum_s y_s=\sum_s x_{e,s}$. So $y$ is worth at least as much and has the same total.

**What it gives against full information.** Combine Theorem 3 with Theorem 2.
- **Additive:** $c_b^2\,\mathrm{OPT_{FI}}$, which is $0.53$ for $K=1$ and $0.65$ for $K=2$ (two-directional), tending to 1.
- **Top-$k$:** $c_k^2\,k/b$ of $\mathrm{OPT_{FI}}$, against an upper bound of about $k/b$.
- **Subadditive:** $c_1^2/b\approx0.40/b$, against $1/b$.

**Remarks.**
- **Any query rule keeps (a).** The incentive argument doesn't care how the queried set is chosen, as long as it uses only coins and oracle answers.
  - So for $b'=1$ (top-1 and general utilities), any stochastic-matching query algorithm can replace steps 1–3. One example is the $0.68$ non-adaptive algorithm with $O(1/p)$ queries per vertex ($0.73$ on bipartite graphs).
  - Querying more than the plan asks approaches $\mathrm{OPT_{IR}}$. On $G(m,m,p)$, three times the plan's rate gave $0.91$ ($b=1$) to about $1.0$ ($b=4$).
- **Constants.** $c^2$ is loose: on random markets SDH earned at least $0.77$ of the LP for $b'=1$.

**Continuous values.** Nothing above needs $s$ to be discrete. With continuous priors, $s=(q_{\ell x},q_{x\ell})$ is a point in the plane, for example two scores between 0 and 10.
- **The plan.** Replace $x_{e,s}$ by a function $y_e(s)\in[0,1]$: the probability the plan uses $e$ when its values are $s$. Sums over $s$ become expectations:
  $$\max\ \sum_e\mathbb E\big[w_{e,s}\,y_e(s)\,\mathbb 1\{s\text{ acceptable}\}\big],\qquad x_e=\mathbb E\big[y_e(s)\,\mathbb 1\{s\text{ acceptable}\}\big],$$
  with $(x_e)_{e\ni\ell}\in P(\mathcal F_\ell)$ as before.
- **One bar per pair.** For a fixed total $x_e$, the best $y_e$ uses $e$ exactly when its net weight is in the top $x_e$ of the probability mass. This is "highest-weight combinations first".
  - So only the net weight matters, not the whole vector $s$.
  - Geometrically, the plan matches $e$ when $s$ lies in the acceptable quadrant ($s_1>c_\ell$, $s_2>c_x$) and above the line $(s_1-c_\ell)+(s_2-c_x)=\theta_e$. Call $\theta_e$ the pair's bar.
  - Let $F_e(x_e)$ be the expected weight of that top $x_e$ mass. It is concave, because the best outcomes are added first.
  - The plan becomes $\max\sum_eF_e(x_e)$ under the same constraints: one number per pair and a concave objective. Solve it directly, or cut each pair's weight distribution into $M$ equal-probability slices to get an ordinary LP with $M$ variables per pair.
- **Welfare is unchanged.** The proof of (b) uses only two facts: screening finds each pair at least as often as the plan uses it, and pairs are independent. The layer-cake step is an integral anyway. So $\gamma$ is the same.
- **Queries can get worse.**
  - A continuous weight has no atom at the bar, so $y_e$ is 1 above the bar and 0 below.
  - Then $\tau_e=1$ for every pair the plan uses at all, since you can't tell whether a pair clears the bar without asking.
  - So $\hat p_e=x_e$, and (c)'s bound becomes the number of pairs the plan touches at $\ell$. That is large when the LP spreads small amounts over many pairs.
  - With discrete values the bar often sits on an atom, which is why $\tau_e<1$ can happen there.
- **Example.** Ann values Bo uniformly on $[0,4]$, Bo values Ann at 2, and both costs are 1.
  - The pair is acceptable when Ann's value $q$ exceeds 1, so $p_e=3/4$, and its net weight is $(q-1)+(2-1)=q$.
  - Three ways to use the pair with total probability $x_e=1/4$:

    | How | Expected weight | Calls to Ann |
    | --- | --- | --- |
    | always query, keep $q>3$ (the plan's choice) | $\int_3^4\frac q4\,dq=\frac78$ | 1 |
    | query with probability $1/2$, keep $q>2$ | $\frac12\int_2^4\frac q4\,dq=\frac34$ | $1/2$ |
    | query with probability $1/3$, keep every acceptable $q$ | $\frac13\int_1^4\frac q4\,dq=\frac58$ | $1/3$ |

  - With continuous values there is a real trade-off between welfare and calls, and the plan above ignores the calls.
- **A likely fix (not worked out).**
  - Make $\tau_e$ a variable of the plan, with $x_{e,s}\le\tau_e\pi_{e,s}$ and a call budget per user.
  - For continuous values the pair's value becomes $\tau_eF_e(x_e/\tau_e)$. That is the perspective of $F_e$, which is jointly concave. The table's three rows are points on this curve.
  - The proof of (b) looks unchanged, since it only needs screening to find each pair at least as often as the plan uses it. This is not yet checked (Gaps).
- **Evidence.** The script tests only discrete priors (two values per side). The example is exact arithmetic.

### Worked example
Four users, all top-1 with match cost 1, in a two-directional design with $K=1$. So $b=2$ and $b'=\min(b,k)=1$.
- Ann is on one side; Bo, Cy and Dee are on the other.
- Ann values Bo at 4, Cy at 2.5 and Dee at 2, each with probability $1/2$ and otherwise at 0. Bo, Cy and Dee each value Ann at 2 for sure.
- So each of Ann's pairs is acceptable with probability $1/2$. The net weights are $w=(4-1)+(2-1)=4$ for Ann–Bo, $2.5$ for Ann–Cy and $2$ for Ann–Dee.

The four steps of SDH:
1. **Plan.** The LP maximizes $4x_B+2.5x_C+2x_D$ subject to $x_e\le1/2$ and Ann's cap $x_B+x_C+x_D\le1$.
   - The optimum is $x_B=x_C=1/2$ and $x_D=0$, so $\mathrm{LP}=3.25$.
   - The plan uses Bo whenever Bo is acceptable, Cy whenever Cy is, and never Dee.
2. **Screen.** $\tau_B=\tau_C=1$ and $\tau_D=0$.
   - Ann is the side less likely to accept, so she is asked first. That charges 2 calls to Ann.
   - Bo and Cy are asked only when Ann says yes, $1/2$ call each.
   - Theorem 3(c)'s bound for Ann, $b'/\hat p=1/(1/2)=2$, is met exactly.
3. **Select.**
   - If Ann–Bo is found acceptable, pick it (weight 4).
   - Otherwise pick Ann–Cy if it is found (2.5).
   - Otherwise pick nothing. Ann never gets two matches.
4. **Show.** Say Ann–Bo is picked. Ann sees Bo in period 1 and likes him. Bo sees Ann in his period-2 backlog and likes her back. Each sees exactly one profile, which is acceptable, so liking it is dominant.

**Outcome.**
- SDH earns $\frac12\cdot4+\frac14\cdot2.5=2.625$.
- $\mathrm{OPT_{IR}}$, which also falls back on Dee, earns $2.875$.
- $\mathrm{OPT_{FI}}$ equals $\mathrm{OPT_{IR}}$ here: a second match for Ann gains her partner 1 but costs her 1.
- So SDH gets $0.81$ of the LP and $0.91$ of $\mathrm{OPT_{IR}}$, well above its guarantee $c_1^2\approx0.40$.

**Where the loss comes from.**
- The LP keeps Ann's cap only on average. It plans Bo and Cy with probability $1/2$ each, but when both are acceptable (probability $1/4$) only one can be used.
- The plan never screens Dee, so when Bo and Cy both fail, nothing is left.

**Contrast with DH-int.** Without the oracle, DH-int might show Ann Bo in period 1, and Cy in period 2 after Cy liked her. If both are acceptable to Ann, she faces the dilemma of Impossibility 1: liking Cy back makes a sure match, and Bo may also like her back, leaving her with two matches when she wants one.

### T4. Queries are unavoidable
**Theorem 4.** Consider $n$ users per side, two-directional, caps $K$, $b=2K$, additive.
- Each $I$-user accepts each $J$-user independently with probability $p$ (value 2, cost 1).
- $J$-users accept everyone (value 2, cost 1).

Suppose $np\to\infty$ with $b\le np$. (The first version assumed $np\ge C(K+\log n)$, which implies both; the Lean proof needs only these.) Users swipe sincerely, as in $\mathrm{OPT_{FI}}$'s definition. Then any policy, truthful or not, that averages $\bar q$ oracle calls per user earns at most
$$p\,(2\bar q/b+2)\,(1+o(1))\cdot\mathrm{OPT_{FI}}.$$
So a constant fraction needs $\Omega(b/p)$ calls per user, and zero queries gets at most about $2p$.

*In words.* Each oracle call or display uncovers at most one fresh pair, and a fresh pair is acceptable only with probability $p$. To give a user about $b$ acceptable partners, the platform must uncover about $b/p$ pairs around that user. Displays are capped at $b$, so the rest must come from queries.

*Proof.*
- **Revealing a pair.** Only a query of the $I$-side or a display reveals whether a pair is acceptable. Before that it is a fresh $p$-coin.
- **Matches.** Matches are displayed acceptable pairs.
  - There are at most $2n\bar q$ queried pairs.
  - Each user sees at most $b$ profiles, so at most $2nb$ pairs are displayed.
  - So $\mathbb E[\text{matches}]\le p(2n\bar q+2nb)$, each worth 2.
- **Benchmark.**
  - Pick a threshold $D\ge b$ a little above the mean degree $\mu=(n-1)p$, say $D\approx(1+\delta)np$. Keep the edges of $G$ whose two ends both have degree at most $D$; call them $G'$.
  - $G'$ has every degree at most $D$, so by König's edge-coloring theorem it splits into $D$ matchings, and $b$ cyclically consecutive colors give a $b$-matching with at least $\frac bD|G'|$ edges (as in Theorem 2(b)).
  - An edge is kept unless one of its ends has more than $D$ edges. By Chebyshev's inequality that has probability at most $(n-1)p(1-p)/(D-\mu)^2$ per end, so $\mathbb E|G'|\ge n^2p\,\big(1-2(n-1)p(1-p)/(D-\mu)^2\big)$.
  - So $\mathrm{OPT_{FI}}\ge2\frac bD\,\mathbb E|G'|=(1-o(1))\,2bn$ as $np\to\infty$. $\square$
  - The first version used Chernoff bounds on the largest degree and the integrality of bipartite $b$-matching polytopes. The argument above avoids both and needs no $\log n$.

SDH on this instance uses $b/p$ calls per $I$-user and $b$ per $J$-user, within a constant of the bound. The bound mirrors the $\Omega(1/p)$-per-vertex lower bound of stochastic matching.

### Proposition 4. The Bayes–Nash route inside DH
Assume top-$k$ users, $c_\ell>0$, and a swipe-local policy with no queries.
- **(a) Regret identity.** In every realization and against any strategies of others, the best play in hindsight beats sincere swiping by exactly $c_\ell(|M_\ell|-k)^+$, where $M_\ell$ is the sincere match set.
  - By Lemma 1′, the best play keeps the $k$ most valued acceptable profiles in $R$, while sincere play keeps all of them.
  - So sincere swiping is an $\varepsilon$-Bayes–Nash equilibrium, with $\varepsilon_\ell=c_\ell\,\mathbb E(|M_\ell|-k)^+$: if the others are sincere, no deviation gains more than $\varepsilon_\ell$ in expectation.
  - This route is not DSIC. Against arbitrary behavior of the others, the regret can reach $c_\ell(|A|-k)^+$, where $A$ is the set of acceptable profiles $\ell$ sees. Making it DSIC without queries is costly (Proposition 6).
- **(b) Welfare identity.** Under sincere play,
  $$W=U_k^{\rm net}-\sum_\ell c_\ell\,\mathbb E(|M_\ell|-k)^+,\qquad U_k^{\rm net}=\mathbb E\sum_\ell\mathrm{top}_k\{q_{\ell x}-c_\ell\}.$$
  - Credit-DH runs on net values with the sincere like probabilities.
  - Given a like, $q$ has its prior conditioned on $q>c$, independently of everything else (Lemma 2 of the strategic note).
  - So T2 of [[Top-k Match Quality]] gives $U_k^{\rm net}\ge\rho c_k\,\mathrm{OPT_0}$, and $W\ge\rho c_k\,\mathrm{OPT_0}-\sum_\ell\varepsilon_\ell$.
- **(c) One quantity.** The incentive to deviate and the welfare loss are the same number: the expected cost of dates beyond the $k$-th.
  - Suppose a user's matches are independent and expected to number at most $k$. Then Hoeffding's convex ordering gives $\varepsilon_\ell\le c_\ell\,\mathbb E(\mathrm{Pois}(k)-k)^+=c_\ell\,k\,e^{-k}k^k/k!$, which is $0.37\,c_\ell$ for top-1.
  - Credit-DH's program does not cap a user's expected number of matches. Adding $\sum_xp_{\ell x}\le k$ is the natural fix, and its welfare cost is unbounded so far.
- **(d) Open.** Exact Bayes–Nash play, with thresholds above cost, makes $\phi$ depend on the plan: a fixed point.

### Proposition 5. Swipe budgets
Each user can like at most $L_\ell$ profiles per period.
- **(a) Screened.** Sincere swiping is feasible iff $\ell$ never sees more than $L_\ell$ acceptable profiles in a period. SDH with per-period caps $\min(K_\ell,L_\ell)$ shows only acceptable profiles, at most $L_\ell$ per period. So the budget never binds, and Theorems 3 and 4 hold with $K\to\min(K,L)$.
- **(b) Benchmark.** A full-information policy gains nothing from showing more than $L$ acceptable profiles per period: it can show just those the user would like. So the budgeted benchmark is $\mathrm{OPT_{FI}}$ with caps $\min(K,L)$, and budgets cost nothing beyond the caps.
- **(c) Unscreened.** A binding budget makes sincere swiping infeasible.
  - In period 2, liking your $L$ most valued backlog members is dominant and reveals a ranking.
  - In period 1, users shade toward likely matches ([[Strategic Users in the Dating Heuristic Framework|S4, Prop. 5]]).
- **(d) Budgets as menus (not analyzed).**
  - Show $\ell$ more than $L$ profiles that the oracle has screened on the *other* side, and let $\ell$ pick $L$.
  - $\ell$'s own side then needs no queries, and the swipes reveal $\ell$'s top $L$, as in [[Lee 2015 - Propose with a Rose|scarce roses]].
  - This is Proposition 3′'s delegation through a menu, with the menu now screened.
  - It is truthful for period-2 picks, which are sure matches. For period-1 picks it needs the others' cooperation.

### T5. Dominant strategies (DSIC), not just ex post
**Three strengths of truthfulness**, from strongest to weakest, for a fixed user $\ell$ *(standard definitions, not from a vault source)*:
- **Dominant strategy (DSIC).** Sincere swiping is a best response to *every* behavior of the others, in every realization of the values. The others may be sincere, strategic, careless or adversarial.
- **Ex post (ex-post IC).** Sincere swiping is a best response in every realization of the values, *provided the others are sincere*. It is a Nash equilibrium that no one regrets after all values are revealed.
- **Bayes–Nash (BIC).** Sincere swiping is a best response *on average* over the others' values, provided the others are sincere.

A platform that flips coins adds one more quantifier. *Universally* truthful means the property holds for every outcome of the coins; *truthful in expectation* means it holds only on average over them.

> [!warning] Terminology fixed on 2026-10-26
> The first version of this note called Theorems 1 and 3 "ex-post dominant". The proofs never assumed the others were sincere, so the claims were DSIC all along. "Ex post" was meant as "in every realization of values and coins", which clashes with the standard meaning above. [[Strategic Users in the Dating Heuristic Framework]] used the same phrase and is fixed too.

**Theorem 5 (DSIC).** Under a swipe-local policy, Theorem 1(a)'s conclusion holds against every behavior of the others, including strategies that react to what they have seen, and for every outcome of the platform's coins. Hence:
- **(a) SDH** is universally DSIC for every utility class in T3, and so is SDH with swipe budgets (Proposition 5(a)).
- **(b) Additive users.** DH-int, weighted DH-int and credit-DH are universally DSIC.
- **(c) Prior-free incentives.** SDH's plan uses the prior, but its incentives do not. A wrong prior can lower welfare, but sincere swiping stays dominant.
- **(d) Individual rationality.** Under SDH, a sincere user's utility is at least 0 whatever the others do.
- **(e) Robustness.** Under SDH, a deviating user can only break pairs it belongs to. If the users in a set $D$ deviate and everyone else is sincere, welfare is at least the sum of $w_e$ over planned pairs with neither end in $D$.

*Proof.*
- **The others act on $\ell$ only through $R$.**
  - Lemma 1′ fixes the others' strategies, but its proof (Lemma 1 of the strategic note) never assumes they are sincere.
  - Another user $x$ may react to what $x$ has seen. But $\ell$'s swipes reach $x$ only through the pair $\ell x$: a like from $\ell$ puts $\ell$ in $x$'s backlog, and nothing else $\ell$ does is visible to $x$.
  - So for any behavior of the others, $\ell$'s matches are $D\cap R$ with $R$ independent of $\ell$'s swipes, and Theorem 1(a)'s exchange argument goes through.
- **SDH under deviations.** Every profile SDH shows is acceptable. A responder sees only the planned initiators who actually liked it, which is a subset of its planned set, and the IR families are closed under subsets. So $A$ is cost-separable whatever the others do.
- **(c)** The argument never uses the prior.
- **(d)** Starting from the empty set, each member of a cost-separable set adds at least $c_\ell$, so $v_\ell(S)\ge c_\ell|S|$.
- **(e)** A planned pair whose two ends are sincere always matches: the initiator likes, so the responder sees the initiator and likes back. Every user's matches lie inside its IR set, where utility is additive, so welfare is the sum of $w_e$ over the matched pairs. $\square$

**Ex post is genuinely weaker here.**
- Ex-post IC needs only the set that *would* match under everyone's sincere play to be cost-separable. DSIC needs the whole acceptable set the user sees to be (Theorem 1).
- The two differ only when the platform knows that some shown profile will pass.
- *Example.* A top-1 user with cost 1 is shown $x_1$ (value 3) and $x_2$ (value 2), and the oracle knows $x_2$ would pass.
  - If $x_2$ passes, as sincerity says, sincere swiping gets 2, the best possible.
  - If $x_2$ likes anyway, sincere swiping gets $3-2=1$, while liking only $x_1$ gets 2.
- SDH shows only pairs the oracle found mutually acceptable, so for SDH the two notions coincide.

**Proposition 6 (DSIC without the oracle).** Suppose the platform makes no queries, the policy is swipe-local, and values are independent with $0<\phi_{\ell x}<1$.
- **(a) Characterization.** Sincere swiping is dominant for a top-$k$ user iff the user never sees more than $k$ profiles that can match it.
  - Examples: two-directional DH-int with $2K\le k$, or one-directional DH-int with $K\le k$ and no mutual views.
  - Such a policy gets the additive guarantee, $c_K$ against the best policy with the same caps (Theorem 2 of [[Strategic Users in the Dating Heuristic Framework]]), because top-$k$ is additive on at most $k$ profiles.
- **(b) Cost.** Take $n$ users per side and top-1 utilities.
  - Every pair is acceptable with probability $p$: each value is 2 with probability $\sqrt p$ and 0 otherwise, and every cost is 1.
  - Suppose $np\to\infty$ (the first version assumed $np\ge C\log n$).
  - Then every zero-query DSIC policy earns at most $2p(1+o(1))\,\mathrm{OPT_{IR}}$. SDH earns at least $c_1^2\,\mathrm{OPT_{IR}}\approx0.40\,\mathrm{OPT_{IR}}$ with $O(1/p)$ calls per user.
  - Without DSIC, the counting of Theorem 4 allows up to $2pb$. DSIC cuts the effective display to $k=1$.

*Proof.*
- **(a)** Without queries, what $\ell$ sees doesn't depend on $\ell$'s own values: period-1 displays use only coins, and period-2 displays use $\ell$'s backlog. So if $\ell$ can see $k+1$ profiles that can match it, all of them are acceptable to $\ell$ with positive probability, and Theorem 1(b) applies. Conversely, $|A|\le k$ makes $A$ cost-separable for top-$k$.
- **(b) Matches.**
  - Every match starts as a period-1 initiation or a mutual view, chosen before either value of the pair is known, so it succeeds with probability at most $p$.
  - Each user sees at most one profile that can match, so there are at most $2n$ such attempts.
  - Hence $\mathbb E[\text{matches}]\le2np$, each worth $w=2$.
- **(b) Benchmark.** Theorem 4's benchmark with $b=1$: $G(n,n,p)$ has a matching of expected size $(1-o(1))n$, so $\mathrm{OPT_{IR}}\ge(1-o(1))\,2n$. $\square$

**What DSIC does not cover: the oracle's answers.**
- The oracle is assumed truthful, so users have nothing to report and swipes are their only actions.
- If a user could steer what its LLM agent tells the platform, SDH would not be DSIC in those reports. It picks the heaviest pairs, and there are no payments to tie a user's report to welfare.
- *Example.* A top-1 user $\ell$ with cost 1 values $x$ at 3 and $y$ at 2. $x$ values $\ell$ at $1.1$ and $y$ values $\ell$ at 3, both with cost 1.
  - Truthfully, the pair weights are $2.1$ and $3$, so SDH matches $\ell$ with $y$ and $\ell$ gets 1.
  - Reporting 5 for $x$ makes that pair weigh $4.1$. SDH then matches $\ell$ with $x$, and $\ell$ gets $3-1=2$.
- Truthful reporting to the oracle is open (Gaps).

## Evidence
- **Vault.**
  - [[Rios 2026 - The Dating Heuristic]]: the model and designs.
  - [[Strategic Users in the Dating Heuristic Framework]]: Lemma 1, Theorem 1, Lemma 2, S3, S4, S6, Proposition 3′.
  - [[Match Quality in the Dating Heuristic Framework]]: R1's lemma, used in Theorem 3.
  - [[Top-k Match Quality]]: credit-DH, T2, $\rho$.
  - [[Match Quality with Queried Values]]: B1 screening and value-indexed programs.
  - [[Correlation Gap]], [[Submodular Maximization]]: the matroid case.
  - [[Lee 2015 - Propose with a Rose]]: budgets as roses.
- **Brute force, 2026-10-22, rerun 2026-10-26** after adding the DSIC checks, which changed the random market sample. `data/scripts/truthful_swipe_check.py`, seeds 1–3; every assertion held.
  - *Theorem 1:* exact on 30,000 random cases (additive, top-$k$, partition matroid, coverage, XOS). This includes both corollaries and the top-$k$ regret formula of Proposition 4(a).
  - *Lemma R:* 3,000 random graphs, all orientable.
  - *Theorem 2:*
    - the per-realization bound held on random top-$k$ markets (worst $0.569$ against $1/2$, $0.5$ against $1/4$);
    - the instance gives $0.5003$, $0.2502$, $0.5003$ for $(K,k)=(1,1),(2,1),(2,2)$, against $k/b$;
    - the XOS matching bound is attained with equality on some instances.
  - *Theorem 3:* on 450 small markets, exact expectations.
    - $\mathrm{LP}\ge\mathrm{OPT_{IR}}$ always.
    - Worst SDH/LP: $0.771$ ($b'=1$, bound $0.40$), $0.924$ ($b'=2$, bound $0.53$), $1.0$ ($b'=4$).
    - $\tau_e\le x_e/\hat p_e$ and the per-user query bound always held.
    - Simulated two-period play: caps held and every shown pair matched.
  - *Theorem 5:*
    - For each user, every action of each partner on the user's pairs was tried; that covers every behavior of the others. No deviation beat sincere swiping in 59,528 checks, and sincere utility was never negative.
    - Random deviators never pushed welfare below the planned pairs with two sincere ends (3,000 trials).
    - Both T5 examples (ex post but not DSIC; a report that manipulates SDH) reproduce.
  - *Theorem 4:* on $G(300,300,0.1)$, $b$-matchings saturate. At the plan's query rate SDH earns $0.51$–$0.59$ ($b=1$), $0.64$–$0.67$ ($b=2$) and $0.78$–$0.81$ ($b=4$) of $\mathrm{OPT_{FI}}$, scaling roughly linearly below that rate.
  - *Impossibility 1:* the 10/5 table and the $-0.265$ Bayes–Nash example.
  - *Worked example:* $\mathrm{LP}=3.25$, $\tau=(1,1,0)$, SDH $=2.625$, $\mathrm{OPT_{IR}}=2.875$, and 2 calls for Ann.
  - *Not checked by script:* Proposition 6(b) is a counting argument (it is proved in Lean).
- **Lean, 2026-10-26.** `lean/check.sh`: the whole project builds (777 theorems), every theorem is fully proved, and only the standard axioms are used. `lean/README.md` maps each result to its Lean name and lists the modeling choices. The SDH results are in `lean/DatingAlgo/TruthfulSwiping.lean`, `ScreenedDH.lean` and `ProdExp.lean`; the rest are in `SwipeLocal.lean`, `SwipeRegret.lean`, `MatroidSwiping.lean`, `Orientation.lean`, `SDHRobust.lean`, `EdgeColoring.lean`, `PriceOfIR.lean`, `QueryLowerBound.lean`, `WorkedExample.lean` and `MatroidSDH.lean`.
  - *Theorem 1* (`sincere_best`, `sincere_not_best`, `costSeparable_topK_iff`): for every set $R$ of profiles that would match, assuming only subadditivity and $v(\{x\})=q_x$.
  - *Theorems 3(a), 5(a)* (`sdh_dsic`): SDH's two-period game, against every behavior of the others, including strategies that react to what they see, for every realization of values and coins. The proof also shows that for top-$k$ users DSIC needs only that a user has at most $k$ planned partners (`sdh_dsic_topK`).
  - *Theorem 3(b)* (`sdh_welfare`): $\mathrm{SDH}\ge c_K^2\,\mathrm{OPT_{IR}}$ with $K$ at most every cap, through the LP bound, thinning and the two-stage selection. The layer-cake step is a new lemma, the $c_K$ gap for independent random weights.
  - *Theorem 3(c), (d)* (`sdhTau_le`, `sum_callsI_le`, `exists_barShaped`, `sdh_budget`), in the corrected form above.
  - *Lemma 1′ and Theorem 5 for every swipe-local policy* (`matchSet_update`, `swipeLocal_dsic`, `swipeLocal_dsic_additive`): any period-1 displays and any period-2 rule that picks from the backlog, with mutual views. So DH-int, weighted DH-int and credit-DH are universally DSIC for additive users.
  - *Matroid users* (`costSeparable_wRank_iff`, `sdh_dsic_matroid`, `sdh_welfare_matroid`): Theorem 1's matroid corollary, SDH's DSIC, and $\mathrm{SDH}\ge(1-1/e)^2\,\mathrm{OPT_{IR}}$, with the plan in each user's matroid polytope. This includes a new proof of the $1-1/e$ correlation gap for matroid rank.
  - *Lemma R* (`lemmaR`, `lemmaR_realize`): by splitting off two edges at a vertex rather than Euler tours.
  - *Theorem 5(e)* (`sdh_robust`) and *Impossibility 1* (`impossibility1_no_dominant`, `like_gain_le`).
  - *Theorem 2* (`thm2a`, `optFI_topK_le`, `optFI_subadditive_le`, `optFI_additive`), with (b) sharpened to $k/b$ through König's edge-coloring theorem (`EdgeColoring.lean`, from Hall's theorem). In (a) the mechanism enters only through the distribution of the top-$k$ user's match count, with expected utility at least 0.
  - *Theorem 4 and Proposition 6(b)* (`thm4_asymp`, `prop6b_asymp`): policies are adaptive trees that reveal one pair at a time by query or display; the explicit bound holds for every threshold $D$, and the asymptotic forms come with an explicit $m_0$.
  - *Propositions 4–6* (`topK_regret_le`, `topK_regret_attained`, `topK_util_eq_net`, `excess_le`, `sdh_budget_feasible`, `budget_resp_attained`, `zeroQuery_topK_dsic_iff`), the T5 examples (`expost_not_dsic`, `report_manipulation`), the worked example and the continuous-values table.
- **Literature** *(not in vault: web search, 2026-10-22).*
  - Stochastic matching with few queries: Assadi, Khanna & Li (EC 2016), $\Omega(1/p)$ queries per vertex for any constant factor.
  - Derakhshan & Saneian, "Query Efficient Weighted Stochastic Matching" (ICALP 2025): $0.68$ weighted ($0.73$ bipartite), non-adaptive, $O(1/p)$ per vertex.
  - Behnezhad, Derakhshan & Hajiaghayi (STOC 2020) and Behnezhad & Derakhshan (FOCS 2020): $1-\varepsilon$, with degree exponential in $1/p$.
  - Chen, Immorlica, Karlin, Mahdian & Rudra, "Approximating Matches Made in Heaven" (ICALP 2009): dating and kidney exchange with probe limits ("patience").
  - None of these is ingested; they are candidates.

## Gaps
- **Proofs.** Every numbered result is in Lean (see Evidence). Not in Lean:
  - Theorem 3(b) for continuous priors: the Lean framework has finitely many value combinations per pair. The continuous example, the concavity of $F_e$ and $\tau_e=1$ for fully used pairs are checked.
  - The inequality $U_k^{\rm net}\ge\rho c_k\,\mathrm{OPT_0}$ in Proposition 4(b), which cites R5 of [[Top-k Match Quality]] (not formalized there either).
  - Proposition 5(d), which the note does not analyze.
- **Constants.** $c_{b'}^2$ is loose. Plugging in the stochastic-matching algorithms above should improve $b'=1$. Whether $(1-\varepsilon)\mathrm{OPT_{IR}}$ is reachable with $O_\varepsilon(b'/p)$ queries per user is open.
- **Query-aware plan.** With continuous values the plan queries every pair it uses (T3, Continuous values). Making $\tau_e$ a plan variable with a call budget looks like it keeps Theorem 3(b), but it is not worked out or checked.
- **General submodular utilities against $\mathrm{OPT_{IR}}$.** Cost-separable families are not matroids, and only the matching bound ($1/b$) is known.
- **Complements.** Non-subadditive utilities are out of scope.
- **Private $k$.** If users report $k$ instead of the oracle knowing it, over-reporting buys options: shown $k+1$ sure matches, a top-$k$ user keeps its best $k$. So $k$ must come from the oracle.
- **Oracle.** A strategic or noisy oracle (the "for now" assumption) is not addressed; [[Match Quality with Queried Values]] has the noisy-score sandwich.
  - T5 shows SDH is not DSIC in value reports. A strategic oracle needs a different selection rule. There is no money to pay with, so VCG-style payments are not available.
- **Zero-query DSIC.** Proposition 6(b) is an upper bound on one market. The best zero-query DSIC policy for general priors, and how much a few queries recover, are not worked out.
- **Bayes–Nash.** True equilibrium thresholds, and load-capped credit-DH, are not worked out.
- **Not addressed:** more than two periods, and the menu design of Proposition 5(d).

## Glossary
*Standard game-theory and optimization terms are general knowledge, not from a vault source. Project terms link to the note that introduced them.*

### Incentives and game theory
- **Mechanism, policy.** The platform's rule for what to query, whom to show to whom, and when. "Policy" stresses the algorithm; "mechanism" stresses that users respond to it strategically.
- **Strategy.** A user's plan for swiping: for every situation it could be in (its values, what it has been shown so far), whether to like or pass. "The others' behavior" means their strategies, which may be anything, insincere or adaptive included.
- **Sincere swiping.** Like a profile iff its value exceeds your match cost, $q_{\ell x}>c_\ell$. That is, like exactly the people you'd want to match with *on their own*. This is what "truthful" means in this note.
- **Indirect mechanism.** Users don't report values; they act (swipe), and the platform reacts. "Truthful" then means that a designated honest action, sincere swiping, is optimal.
- **Best response.** A strategy that gives the user the most expected utility, given the others' strategies.
- **Dominant strategy.** A strategy that is a best response to *every* behavior of the others. *Weakly* dominant means never worse, possibly tied. Every "dominant" in this note is weak.
- **DSIC** (dominant-strategy incentive compatible). The truthful action is a dominant strategy for every user. Here: sincere swiping is dominant (T5).
- **Ex ante, interim, ex post.** Before anyone knows their values; after learning only your own; after everything is revealed.
- **Ex-post IC, ex-post equilibrium.** Truthful play is a best response in every realization of the values, *assuming the others are truthful*. Weaker than DSIC (T5).
- **Bayes–Nash equilibrium (BNE), BIC.** Each strategy is a best response *on average* over the others' values, given their strategies. BIC means truthful play is a BNE. Weaker than ex post.
- **$\varepsilon$-equilibrium.** No user can gain more than $\varepsilon$ by deviating.
- **Universally truthful, truthful in expectation.** For a platform that flips coins: truthful for every outcome of the coins, or only on average over them.
- **Realization.** One outcome of all the randomness: values and platform coins.
- **Regret.** How much better the best play in hindsight, knowing everything that happened, would have done than the strategy used. Zero regret in every realization against any behavior of the others is the same as dominance.
- **Individual rationality (IR).** Standard meaning: taking part gives a user at least what staying out would, i.e. utility at least 0. SDH satisfies it (T5(d)). This note also says *IR set* for a match set the user would keep in full; see "IR family" below.
- **Social welfare $W$.** The sum of all users' utilities, in expectation.
- **Price of individual rationality.** How much welfare is lost, in the worst case, by letting users keep only the matches that are good for them, compared with the full-information optimum. It is analogous to the price of anarchy. Theorem 2 puts it at about $k/b$ for top-$k$.
- **Audit.** The platform uses the oracle to check whether swipes were sincere, and punishes insincere ones. Theorem 2 shows audits cannot beat the price of IR.
- **Swipe-local policy.** Displays depend only on oracle answers, coins and, for a responder, its own backlog, never on a user's swipes elsewhere. Lemma 1′ then says your swipes change only your own matches, one pair at a time.
- **Swipes as consent.** With a truthful oracle, the platform already knows who would accept, so a swipe confirms rather than informs. A match still needs both likes.

### The dating model
- **DH, DH-int.** Rios & Torrico's dating heuristic. It solves a program that plans period-1 displays together with the period-2 backlog responses they should produce, then shows the period-1 part. DH-int uses binary period-1 variables. See [[Dating Heuristic]].
- **Weighted DH-int.** DH-int with each planned match weighted by its value, or by its expected net value, instead of counted once ([[Match Quality in the Dating Heuristic Framework]]).
- **Credit-DH.** DH-int's program with *credit* variables that pay each user only for its $k$ best planned matches, plus a random period-2 rule. It keeps a constant factor for top-$k$ ([[From DH-int to Credit-DH]], [[Top-k Match Quality]]).
- **SDH (screened DH).** This note's mechanism (T3): plan, screen with the oracle, select, show.
- **Periods.** Two rounds. Period 1 has initiations and mutual views; period 2 has backlog responses only.
- **Initiation, initiator.** In period 1, $\ell$ is shown $x$ and may like $x$; the like goes to $x$'s backlog.
- **Backlog $B_r$.** The users who liked $r$ in period 1 and are waiting for $r$'s answer.
- **Response, responder.** In period 2, $r$ is shown some of its backlog. Liking one back makes a sure match, since that user already liked $r$.
- **Mutual view.** Both users see each other in period 1, and they match iff both like.
- **One-directional, two-directional design.** In a one-directional design one side initiates and the other responds. In a two-directional design every user does both.
- **Display cap $K_\ell$.** The most profiles $\ell$ sees per period.
- **Capacity $b_\ell$.** The most matches the design allows $\ell$: $2K_\ell$ in two-directional designs ($K_\ell$ as initiator plus $K_\ell$ as responder).
- **$b'_\ell$.** The cap SDH actually uses: the size of $\ell$'s largest IR set. It is $b_\ell$ (additive), $\min(b_\ell,k)$ (top-$k$) or 1 (general).
- **Match cost $c_\ell$.** What one match costs $\ell$ (time, a date). It is what makes too many matches bad.
- **Value $q_{\ell x}$.** How much $\ell$ values $x$ as a match. It is directional ($q_{\ell x}\ne q_{x\ell}$ in general) and private: only $\ell$ and the oracle know it.
- **Prior.** The known distribution the values are drawn from.
- **Like probability $\phi_{\ell x}$.** $\Pr[q_{\ell x}>c_\ell]$: the chance a sincere $\ell$ likes $x$.
- **Acceptable pair, acceptable graph $G(q)$, $p_e$.** A pair is acceptable when both values exceed their costs, and $G(q)$ is the set of all such pairs. $p_e=\phi_{\ell x}\phi_{x\ell}$ is the chance pair $e$ is acceptable.
- **Net weight $w_e$.** $(q_{\ell x}-c_\ell)+(q_{x\ell}-c_x)$: what the match adds to welfare when both users value it fully.
- **Oracle, query, call.** The LLM agent. Asked about $(\ell,x)$, it returns $q_{\ell x}$ exactly. Each query is one call, charged to $\ell$.
- **Screening.** Querying a pair before showing it, to check that it is acceptable.
- **$N_\ell$, $A$, $Z_{\ell x}$, $R$ (Lemma 1′).**
  - $N_\ell$ is the set of profiles $\ell$ sees, and $A$ is the subset acceptable to $\ell$.
  - $Z_{\ell x}=1$ if $x$ would end up matched with $\ell$ given that $\ell$ likes $x$, and $R$ is the set of such $x$.
  - So $\ell$'s matches are its likes intersected with $R$.
- **Value combination $s$, $\pi_{e,s}$.** A pair's two values taken together, and the probability of that combination.
- **$x_{e,s}$, $x_e$.** The plan's probability of matching pair $e$ when its values are $s$, and its total over $s$.
- **$\tau_e$.** The probability that SDH queries pair $e$.
- **Plan's bar, bar-shaped, $\hat p_e$, $\hat p$.** The plan's bar for $e$ is the lowest weight at which the plan uses $e$. A *bar-shaped* plan uses combinations above the bar whenever they occur, those at the bar a fixed fraction of the time, and those below never. $\hat p_e$ is the chance of a combination strictly above the bar if that is positive, otherwise at the bar; $\hat p=\min_e\hat p_e$ over the pairs the plan uses (Theorem 3(c)).
- **Swipe budget $L_\ell$.** The most likes $\ell$ may give per period.

### Utilities
- **Utility $u_\ell(S)=v_\ell(S)-c_\ell|S|$.** The value of the match set minus the cost of each match.
- **Monotone.** More matches never lower $v$, before costs.
- **Marginal value.** $v(T\cup\{x\})-v(T)$: what $x$ adds to $T$.
- **Additive.** $v(S)=\sum_{x\in S}q_{\ell x}$: every match counts in full.
- **Top-$k$.** $v(S)$ is the sum of the $k$ largest values in $S$, so only your $k$ best matches count. With $k=1$ you end up with one partner.
- **Matroid.**
  - A family of *independent* sets that contains every subset of its members.
  - It also has the exchange property: a smaller independent set can always be extended by some element of a larger one.
  - *Uniform matroid:* independent means size at most $k$.
  - *Partition matroid:* at most a fixed number from each group, e.g. one partner per city.
  - *Circuit:* a minimal dependent set.
- **Weighted matroid rank.** $v(S)$ is the largest total value of an independent subset of $S$. Top-$k$ is the uniform case.
- **Submodular.** Diminishing returns: $x$ adds less to a larger set ([[Submodular Maximization]]).
- **XOS** (fractionally subadditive). $v$ is a maximum of additive functions. Every submodular function is XOS.
- **Subadditive.** $v(S\cup T)\le v(S)+v(T)$: matches are never complements. Every XOS function is subadditive.
- **Cost-separable.** A set $A$ in which every member adds at least its cost to every subset of the other members. Then liking all of $A$ is safe, and every subset of $A$ is worth at least its costs (Theorem 1).
- **IR family $\mathcal F_\ell$.** The sets SDH may give $\ell$: size-capped sets, or independent sets of $\ell$'s matroid. Once their members are acceptable they are cost-separable, so utility is additive on them.
- **Closed under subsets** (downward closed). Every subset of a member is a member.

### Benchmarks and constants
- **$\mathrm{OPT_{FI}}$** (full information). The best welfare that a policy knowing every value can get from sincere users. It may hand users bundles they would not keep, which no voluntary mechanism can do (Theorem 2).
- **$\mathrm{OPT_{IR}}$.** The best full-information welfare when every user's match set is an IR set.
- **$\mathrm{OPT_0}$.** The best welfare with no queries.
- **LP.** The optimal value of SDH's plan. It is an upper bound on $\mathrm{OPT_{IR}}$.
- **"Gets $\gamma$ of OPT".** Expected welfare is at least $\gamma$ times the benchmark: an approximation ratio. $\gamma$ is SDH's constant in Theorem 3.
- **Poisson constant $c_k$.** $c_k=1-e^{-k}k^k/k!=\mathbb E\min(\mathrm{Pois}(k),k)/k$: the fraction kept when a random number of candidates with mean $k$ is cut down to $k$.
  - $c_1\approx0.632$, $c_2\approx0.729$, $c_4\approx0.805$, tending to 1.
  - Squared: $c_1^2\approx0.40$, $c_2^2\approx0.53$, $c_4^2\approx0.65$.
- **$\rho$.** Credit-DH's survival factor, at least $1/2$ ([[Top-k Match Quality]]).

### Algorithms and proof tools
- **Linear program (LP), relaxation.** Optimize a linear objective over linear constraints, with fractional variables. A relaxation enforces constraints only on average, so its value is an upper bound on the true optimum.
- **Polytope $P(\mathcal F)$.** The convex hull of the indicator vectors of the sets in $\mathcal F$. For size caps it is just $\sum x\le b'$.
- **$b$-matching.** A set of pairs in which each user $\ell$ appears at most $b_\ell$ times. A matching is the case $b=1$.
- **Weighted matroid intersection.** Find a maximum-weight set that is independent in two matroids at once. It runs in polynomial time and is used when users have matroid constraints.
- **Orientation, Euler tour (Lemma R).** Orienting a match means deciding who initiates it. An Euler tour walks every edge once, so orienting edges along it splits each user's matches evenly between initiations and responses.
- **König's edge-colouring theorem.** A bipartite graph with maximum degree $b$ splits into $b$ matchings. Theorems 2(b) and 4 use it. The Lean proof gets it from Hall's marriage theorem: some matching covers every vertex of maximum degree, so remove it and repeat.
- **Contention resolution, two-stage selection.** When a plan promises a user more candidates than it can keep, keep a subset so that each candidate survives with good probability. SDH's proof does this on one side, then on the other.
- **Thinning.** For the analysis only, discard extra candidates at random so that their probabilities are exactly the plan's.
- **Layer cake.** Write a value as an integral over thresholds $\theta$ of the number of items worth at least $\theta$.
- **R1's lemma.** If $N$ is a sum of independent indicators with mean at most $k$, then $\mathbb E\min(N,k)\ge c_k\,\mathbb E N$. It is machine-checked in `lean/DatingAlgo/PoissonGap.lean` ([[Match Quality in the Dating Heuristic Framework]]).
- **Correlation gap.** For monotone submodular $f$, sampling independently loses at most a factor $1-1/e$ against any correlated distribution with the same marginals ([[Correlation Gap]]).
- **Chebyshev's inequality.** A random variable exceeds its mean by $t$ with probability at most its variance over $t^2$. Theorem 4's benchmark uses it on users' degrees.
- **Hoeffding's convex ordering.** Among sums of independent indicators with a given mean, the binomial, and in the limit the Poisson, is the most spread out. So convex quantities like $\mathbb E(N-k)^+$ are largest there.
- **Stochastic matching.** Find a large matching in a random graph by querying edges. *Adaptive* algorithms choose each query after seeing earlier answers; *non-adaptive* ones choose all queries up front.
- **$G(n,n,p)$.** A random bipartite graph with $n$ vertices per side, where each pair is an edge with probability $p$, independently.
