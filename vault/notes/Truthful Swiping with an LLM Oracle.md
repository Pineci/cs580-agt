---
type: synthesis
question: "With a truthful, accurate LLM oracle for match values, can a dating-heuristic platform make sincere swiping a dominant strategy, earn close to full-information welfare, and use few oracle queries, for additive, top-k and general utilities?"
created: 2026-10-22
updated: 2026-10-22
tags: [dating/platforms, matching/quality, game-theory/incentives, elicitation, research/project]
aliases: [truthful swiping, sincere swiping, screened DH, SDH, price of individual rationality, cost-separable, swipe-local policy]
sources: ["[[Rios 2026 - The Dating Heuristic]]", "[[Lee 2015 - Propose with a Rose]]"]
origin: claude
status: seed
---
# Truthful Swiping with an LLM Oracle

> [!question] With a truthful, accurate LLM oracle for match values, can a dating-heuristic platform make sincere swiping a dominant strategy, earn close to full-information welfare, and use few oracle queries, for additive, top-k and general utilities?

> [!note] Preliminary
> Written 2026-10-22. Informal proofs, not machine-checked; the claims were brute-forced on small markets (see Evidence). This continues [[Strategic Users in the Dating Heuristic Framework]], with the choices made for this phase:
> - a truthful swipe is the *sincere threshold*: swipe right iff the match is worth it on its own;
> - match costs first, then swipe budgets;
> - welfare is compared with *full information*, the best policy that knows every value;
> - when dominant strategies fail, report the impossibility, then try both a Bayes–Nash guarantee for DH and a changed game.
>
> As in earlier notes, $c_\ell$ is user $\ell$'s match cost and $c_k=1-e^{-k}k^k/k!$ is the Poisson constant.

## Answer

**Summary**
- **Truthfulness constrains what users see, not how displays are chosen (Theorem 1).**
  - Call a policy *swipe-local* if displays depend only on the oracle's answers, coins, and (for a responder) its own backlog.
  - Under such a policy, sincere swiping is ex-post dominant exactly when every acceptable profile a user sees adds at least $c_\ell$ to every set of the other acceptable profiles they see.
  - **Additive:** always holds.
  - **Top-k:** holds iff the user sees at most $k$ acceptable profiles.
  - **Matroid-rank** (e.g. at most one partner per city): holds iff the acceptable profiles seen are independent.
- **Impossibility 1: DH is not truthful for top-k.**
  - DH-int and credit-DH can show a top-$k$ user more than $k$ acceptable profiles.
  - Then *no* swipe rule is dominant (the 10/5 example below).
  - With values just above cost, sincere swiping isn't even a Bayes–Nash equilibrium.
- **Impossibility 2: the price of individual rationality (Theorem 2).**
  - **Bound.** For top-$k$, no mechanism whose equilibrium is sincere swiping (dominant, ex post or Bayes–Nash; auditing with the oracle included) earns more than about $k/b$ of the full-information optimum. Here $b$ is the most matches the design allows a user ($2K$ in two-directional designs).
  - **Tight.** The best outcome that gives no user more than $k$ matches already earns $1/\lceil b/k\rceil$.
  - **Subadditive utilities.** The price is at most $b$, and top-1 makes that tight for the class.
  - **Additive.** No price.
  - **Why.** The full-information benchmark exploits sincere users. It gives them matches they would accept one at a time but not all together. No mechanism that users play voluntarily can do that.
- **Impossibility 3: queries are unavoidable (Theorem 4).** Getting a constant fraction of full information takes $\Omega(b/p)$ oracle calls per user, where $p$ is the chance a pair is mutually acceptable. That holds even without incentives. Free swipes are worth only about $b$ calls per user.
- **Mechanism: screened DH (SDH, Theorem 3).**
  1. **Plan.** Solve DH's program in its full-information form.
  2. **Screen.** Query each pair with the probability the plan needs.
  3. **Select.** Pick the best match set among the pairs found acceptable, capping each user at an *IR set*: one the user would keep in full.
  4. **Show.** Use DH's two periods: initiations, then backlog responses.

  Every shown pair matches, and sincere swiping is ex-post dominant.

  | Utility class | SDH guarantee | Upper bound for any truthful mechanism | Oracle calls per user |
  | --- | --- | --- | --- |
  | additive | $c_b^2\,\mathrm{OPT_{FI}}$ | $\mathrm{OPT_{FI}}$ | $O(b/\hat p)$ |
  | top-$k$ | $c_{k}^2\,\mathrm{OPT_{IR}}\ge \frac{c_k^2}{\lceil b/k\rceil}\mathrm{OPT_{FI}}$ | $\approx\frac kb\,\mathrm{OPT_{FI}}$ | $O(k/\hat p)$ |
  | matroid rank | $(1-1/e)^2\,\mathrm{OPT_{IR}}$ | $\mathrm{OPT_{IR}}$ | $O(\text{rank}/\hat p)$ |
  | subadditive | $\frac{c_1^2}{b}\mathrm{OPT_{FI}}\approx\frac{0.40}{b}\mathrm{OPT_{FI}}$ | $\approx\frac1b\,\mathrm{OPT_{FI}}$ | $O(1/\hat p)$ |

  - $\hat p$ is the chance a queried pair passes the plan's bar; $\hat p=p$ when values are fixed.
  - With a budget of $Q$ calls per user, SDH gets a $\min(1,Q\hat p/b')$ fraction of these guarantees, which matches Theorem 4 up to constants.
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
- (a) If $A$ is cost-separable in every realization, sincere swiping is ex-post dominant for $\ell$.
- (b) Conversely, suppose that with positive probability $A$ is not cost-separable, and the profiles involved can all match $\ell$ at once for some strategies of the others. Then sincere swiping is not ex-post dominant.

*Proof.*
- By Lemma 1′, if $\ell$ likes the set $D$, its matches are $D\cap R$, where $R=\{x:Z_{\ell x}=1\}$ doesn't depend on $\ell$. Sincere play gets $A\cap R$.
- Subadditivity gives $v(T\cup\{x\})-v(T)\le v(\{x\})\le c_\ell$ for $x\notin A$. So removing unacceptable profiles never lowers $u$.
- Cost-separability means adding acceptable ones never lowers $u$ either.
- Go from $D\cap R$ to $A\cap R$ by adding $(A\cap R)\setminus D$ one at a time, then removing $D\setminus A$. Hence $u(A\cap R)\ge u(D\cap R)$.
- (b) Take the violating $x$ and $T$, and strategies under which exactly $T\cup\{x\}$ match $\ell$. Sincere play gets $T\cup\{x\}$; skipping $x$ gets $T$, which is strictly better. $\square$

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
  - *Example:* $c=1$, value $1.05$, $\pi=0.3$: the gain is $-0.265$.

### T2. The price of individual rationality
**Theorem 2.** Let $b=\max_\ell b_\ell$.
- **(a) Bound for truthful mechanisms.** For top-$k$ users and any $\varepsilon>0$, some instance has the following property. Every mechanism in which sincere swiping is an equilibrium (dominant, ex post or Bayes–Nash) earns at most $(1+\varepsilon)\frac kb+o(1)$ of $\mathrm{OPT_{FI}}$.
- **(b) Matching guarantee.** $\mathrm{OPT_{IR}}\ge\mathrm{OPT_{FI}}/\lceil b/k\rceil$, where $\mathrm{OPT_{IR}}$ caps each user at $\min(k,b)$ matches. That cap is exactly the set of top-$k$ outcomes users keep in full.
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
  - The graph is bipartite with degrees at most $b$, so by König's theorem $M$ splits into $b$ matchings.
  - Grouping them into $\lceil b/k\rceil$ groups of at most $k$ matchings, the best group $M'$ carries at least a $1/\lceil b/k\rceil$ share of $\sum_M w$.
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
1. **Plan.** For pair $e$ and each acceptable value combination $s$ (net weight $w_s$), let $\pi_{e,s}=\Pr[e\text{ acceptable with combination }s]$. Solve
   $$\max\sum_{e,s}w_s\,x_{e,s}\quad\text{s.t.}\quad0\le x_{e,s}\le\pi_{e,s},\qquad\Big(\textstyle\sum_s x_{e,s}\Big)_{e\ni\ell}\in P(\mathcal F_\ell)\ \ \forall\ell.$$
   - For size caps the last constraint is $\sum_{e\ni\ell}x_e\le b'_\ell$.
   - Without loss of generality, each pair's mass fills its highest-weight combinations first.
   - This is DH-int's period-2 program in the full-information limit: the like probability $\phi$ is replaced by the probability that screening finds a combination.
2. **Screen.** Query pair $e$ with probability $\tau_e=\max_s x_{e,s}/\pi_{e,s}$. Ask the side less likely to accept first, and the other side only if the first accepts.
3. **Select.** Take a maximum-weight $M$ among the pairs found acceptable, with $M_\ell\in\mathcal F_\ell$. This is a bipartite $b$-matching, or a weighted matroid intersection, so it is polynomial.
4. **Show.** Orient $M$ as in Lemma R. Period 1 shows the initiations. In period 2, each responder sees its planned initiators who liked it.

**Theorem 3.**
- **(a) Truthful.** SDH is swipe-local, and each user sees exactly its planned partners, an acceptable set in $\mathcal F_\ell$, which is cost-separable. So sincere swiping is ex-post dominant (Theorem 1) for every outcome of the platform's coins. Under sincere play every shown pair matches.
- **(b) Welfare.** $\mathbb E\,W\ge\gamma\,\mathrm{LP}\ge\gamma\,\mathrm{OPT_{IR}}$, with $\gamma=c_{b'}^2$ for size caps ($b'=\min_\ell b'_\ell$) and $\gamma=(1-1/e)^2$ for matroids.
- **(c) Queries.** Let $\hat p_e$ be the probability that querying $e$ finds a combination at or above the plan's threshold for $e$; it equals $p_e$ when values are fixed. The expected calls charged to $\ell$ are at most
  $$\sum_{e\ni\ell}\tau_e\ \le\ \sum_{e\ni\ell}x_e/\hat p_e\ \le\ b'_\ell/\hat p.$$
  A queried pair costs at most $1+\min(\phi_{\ell x},\phi_{x\ell})\le1+\sqrt{p_e}$ calls.
- **(d) Query budget.** Scaling the plan by $\lambda=\min(1,Q\hat p/b')$ keeps calls at most $Q$ per user and gives $\mathbb E\,W\ge\gamma\lambda\,\mathrm{OPT_{IR}}$.

*Proof of (b).*
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
- If some combination strictly above the threshold has mass, it is filled completely, so $\tau_e=1$. In that case $x_e$ is at least that mass, which is $\hat p_e$.
- Otherwise only the threshold level has mass, and $\tau_e=x_e/\hat p_e$.
- Finally, $\sum_{e\ni\ell}x_e\le b'_\ell$. $\square$

**What it gives against full information.** Combine Theorem 3 with Theorem 2.
- **Additive:** $c_b^2\,\mathrm{OPT_{FI}}$, which is $0.53$ for $K=1$ and $0.65$ for $K=2$ (two-directional), tending to 1.
- **Top-$k$:** $c_k^2/\lceil b/k\rceil$ of $\mathrm{OPT_{FI}}$, against an upper bound of about $k/b$.
- **Subadditive:** $c_1^2/b\approx0.40/b$, against $1/b$.

**Remarks.**
- **Any query rule keeps (a).** The incentive argument doesn't care how the queried set is chosen, as long as it uses only coins and oracle answers.
  - So for $b'=1$ (top-1 and general utilities), any stochastic-matching query algorithm can replace steps 1–3. One example is the $0.68$ non-adaptive algorithm with $O(1/p)$ queries per vertex ($0.73$ on bipartite graphs).
  - Querying more than the plan asks approaches $\mathrm{OPT_{IR}}$. On $G(m,m,p)$, three times the plan's rate gave $0.91$ ($b=1$) to $0.998$ ($b=4$).
- **Constants.** $c^2$ is loose: on random markets SDH earned at least $0.75$ of the LP for $b'=1$.

### T4. Queries are unavoidable
**Theorem 4.** Consider $n$ users per side, two-directional, caps $K$, $b=2K$, additive.
- Each $I$-user accepts each $J$-user independently with probability $p$ (value 2, cost 1).
- $J$-users accept everyone (value 2, cost 1).

Suppose $np\ge C(K+\log n)$ for a large constant $C$. Then any policy, truthful or not, that averages $\bar q$ oracle calls per user earns at most
$$p\,(2\bar q/b+2)\,(1+o(1))\cdot\mathrm{OPT_{FI}}.$$
So a constant fraction needs $\Omega(b/p)$ calls per user, and zero queries gets at most about $2p$.

*Proof.*
- **Revealing a pair.** Only a query of the $I$-side or a display reveals whether a pair is acceptable. Before that it is a fresh $p$-coin.
- **Matches.** Matches are displayed acceptable pairs.
  - There are at most $2n\bar q$ queried pairs.
  - Each user sees at most $b$ profiles, so at most $2nb$ pairs are displayed.
  - So $\mathbb E[\text{matches}]\le p(2n\bar q+2nb)$, each worth 2.
- **Benchmark.**
  - Set $y_e=b/D_{\max}$ on the edges of $G$, where $D_{\max}$ is the largest degree. This is a fractional $b$-matching of size $b|E|/D_{\max}$.
  - By Chernoff bounds this is $(1-o(1))bn$ with high probability.
  - Bipartite $b$-matching polytopes are integral, so $\mathrm{OPT_{FI}}\ge(1-o(1))\,2bn$. $\square$

SDH on this instance uses $b/p$ calls per $I$-user and $b$ per $J$-user, within a constant of the bound. The bound mirrors the $\Omega(1/p)$-per-vertex lower bound of stochastic matching.

### Proposition 4. The Bayes–Nash route inside DH
Assume top-$k$ users, $c_\ell>0$, and a swipe-local policy with no queries.
- **(a) Regret identity.** In every realization and against any strategies of others, the best play in hindsight beats sincere swiping by exactly $c_\ell(|M_\ell|-k)^+$, where $M_\ell$ is the sincere match set.
  - By Lemma 1′, the best play keeps the $k$ most valued acceptable profiles in $R$, while sincere play keeps all of them.
  - So sincere swiping is an $\varepsilon$-equilibrium, with $\varepsilon_\ell=c_\ell\,\mathbb E(|M_\ell|-k)^+$.
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

## Evidence
- **Vault.**
  - [[Rios 2026 - The Dating Heuristic]]: the model and designs.
  - [[Strategic Users in the Dating Heuristic Framework]]: Lemma 1, Theorem 1, Lemma 2, S3, S4, S6, Proposition 3′.
  - [[Match Quality in the Dating Heuristic Framework]]: R1's lemma, used in Theorem 3.
  - [[Top-k Match Quality]]: credit-DH, T2, $\rho$.
  - [[Match Quality with Queried Values]]: B1 screening and value-indexed programs.
  - [[Correlation Gap]], [[Submodular Maximization]]: the matroid case.
  - [[Lee 2015 - Propose with a Rose]]: budgets as roses.
- **Brute force, 2026-10-22.** `data/scripts/truthful_swipe_check.py`, seeds 1–3; every assertion held.
  - *Theorem 1:* exact on 30,000 random cases (additive, top-$k$, partition matroid, coverage, XOS). This includes both corollaries and the top-$k$ regret formula of Proposition 4(a).
  - *Lemma R:* 3,000 random graphs, all orientable.
  - *Theorem 2:*
    - the per-realization bound held on random top-$k$ markets (worst $0.569$ against $1/2$, $0.423$ against $1/4$);
    - the instance gives $0.5003$, $0.2502$, $0.5003$ for $(K,k)=(1,1),(2,1),(2,2)$, against $k/b$;
    - the XOS matching bound is attained with equality on some instances.
  - *Theorem 3:* on 450 small markets, exact expectations.
    - $\mathrm{LP}\ge\mathrm{OPT_{IR}}$ always.
    - Worst SDH/LP: $0.751$ ($b'=1$, bound $0.40$), $0.934$ ($b'=2$, bound $0.53$), $1.0$ ($b'=4$).
    - $\tau_e\le x_e/\hat p_e$ and the per-user query bound always held.
    - Simulated two-period play: caps held, every shown pair matched, and no profitable deviation in 22,938 trials.
  - *Theorem 4:* on $G(300,300,0.1)$, $b$-matchings saturate. At the plan's query rate SDH earns $0.49$–$0.57$ ($b=1$), $0.64$–$0.68$ ($b=2$) and $0.79$–$0.81$ ($b=4$) of $\mathrm{OPT_{FI}}$, scaling roughly linearly below that rate.
  - *Impossibility 1:* the 10/5 table and the $-0.265$ Bayes–Nash example.
- **Literature** *(not in vault: web search, 2026-10-22).*
  - Stochastic matching with few queries: Assadi, Khanna & Li (EC 2016), $\Omega(1/p)$ queries per vertex for any constant factor.
  - Derakhshan & Saneian, "Query Efficient Weighted Stochastic Matching" (ICALP 2025): $0.68$ weighted ($0.73$ bipartite), non-adaptive, $O(1/p)$ per vertex.
  - Behnezhad, Derakhshan & Hajiaghayi (STOC 2020) and Behnezhad & Derakhshan (FOCS 2020): $1-\varepsilon$, with degree exponential in $1/p$.
  - Chen, Immorlica, Karlin, Mahdian & Rudra, "Approximating Matches Made in Heaven" (ICALP 2009): dating and kidney exchange with probe limits ("patience").
  - None of these is ingested; they are candidates.

## Gaps
- **Proofs.** None is in Lean. Theorem 1 and Lemma R are pure combinatorics. Theorem 3(b) reduces to R1's lemma, which is already in `lean/DatingAlgo/PoissonGap.lean`.
- **Constants.** $c_{b'}^2$ is loose. Plugging in the stochastic-matching algorithms above should improve $b'=1$. Whether $(1-\varepsilon)\mathrm{OPT_{IR}}$ is reachable with $O_\varepsilon(b'/p)$ queries per user is open.
- **General submodular utilities against $\mathrm{OPT_{IR}}$.** Cost-separable families are not matroids, and only the matching bound ($1/b$) is known.
- **Complements.** Non-subadditive utilities are out of scope.
- **Private $k$.** If users report $k$ instead of the oracle knowing it, over-reporting buys options: shown $k+1$ sure matches, a top-$k$ user keeps its best $k$. So $k$ must come from the oracle.
- **Oracle.** A strategic or noisy oracle (the "for now" assumption) is not addressed; [[Match Quality with Queried Values]] has the noisy-score sandwich.
- **Bayes–Nash.** True equilibrium thresholds, and load-capped credit-DH, are not worked out.
- **Not addressed:** more than two periods, and the menu design of Proposition 5(d).
