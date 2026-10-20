---
type: synthesis
question: "Do Theorems 5.3 and 5.4 of Rios & Torrico (multi-period DHT guarantees) hold as stated?"
created: 2026-10-20
updated: 2026-10-20
tags: [dating/platforms, matching/assortment, research/project]
aliases: [Theorem 5.3 counterexample, Theorem 5.4 counterexample, DHT counterexample]
sources: ["[[Rios 2026 - The Dating Heuristic]]"]
origin: claude
status: growing
---
# Counterexamples to the Multi-Period Dating Heuristic Guarantees

> [!question] Do Theorems 5.3 and 5.4 of Rios & Torrico (multi-period DHT guarantees) hold as stated?

## Answer
Theorem 5.3 is false as stated. Theorem 5.4's proof is wrong: the policy it builds misses $1-1/e$. But Theorem 5.4 only claims that *some* semi-adaptive policy reaches $1-1/e$, and that is still open. Both counterexamples are machine-checked in Lean. This is the project's own analysis from 2026-10-20; the paper does not acknowledge it.

**What the theorems claim.** [[Rios 2026 - The Dating Heuristic]] claims that the $T$-period [[Dating Heuristic]] variants are $(1-1/e)$-approximations:
- **Theorem 5.3:** DHT against the best semi-adaptive policy.
- **Theorem 5.4:** *some* semi-adaptive policy against the best adaptive policy, in the one-directional sequential design. The proof uses a rounded-LP policy (Remark 5.5).

**First flaw: the relaxations ignore timing.**
- Both proofs use relaxations, (19) and (41), that pool each user's display slots over all periods: $\sum \le K_\ell T$. That ignores two timing facts:
  - a user can't respond in period 1, because the backlog starts empty;
  - likes received in the last period can never be answered.
- Claim F.1 asserts that DHT's period-by-period backlog responses realize the optimum over *all* likes received. It relies on "$L_\ell = \bigcup_t B^t_\ell$", which is false: last-period likes are in no backlog.

**Second flaw: DHT's schedule ignores when likes arrive.** This one matters for $T \ge 3$, and fixing the relaxation alone does not remove it (see "Repairing the relaxation").
- Step 7 shows each user's initiations in decreasing order of the *target's* like probability. That can push every like for a popular user into period $T-1$, leaving one period to answer them.
- Steps 9–12 add a mutual view only if both users still have room in that period. So DHT can drop mutual views that the relaxation counted.

**What still stands.** The two-period Theorem 4.3 is unaffected, because its program (16) keeps a separate capacity for each period. It is machine-checked in `lean/` for every design.

**Repair.** Theorem 5.3 holds for a repaired algorithm, and this is machine-checked in Lean. The repair uses a per-period relaxation $\mathrm{Rel}_\tau$, and DHT shows each initiation in the period that $\mathrm{Rel}_\tau$ chose. See "Repairing the relaxation".

## Evidence
**Counterexample to Theorem 5.4's proof.** Machine-checked in Lean: `theorem_5_4_counterexample` in `lean/DatingAlgo/MultiPeriod.lean`. Also checked by brute force in `data/scripts/thm54_counterexample.py`.
- **Instance.**
  - $T=2$, and every display cap is 1.
  - Initiators $i_1, i_2$; responders $j_1, j_2$.
  - Every initiator likes every responder for sure.
  - $j_1$ reciprocates for sure, and $j_2$ with probability $0.99$.
- **LP (41).** Its unique optimum is $x\equiv1$: each initiator initiates toward both responders. It is integral, so rounding returns it unchanged. This rounding step is argued, not formalized in Lean.
- **DHT.** It shows $j_1$ in period 1 and $j_2$ in period 2. $j_2$'s likes arrive in the last period and are never answered, so DHT earns at most 1 expected match, even with clairvoyant responders.
- **Alternative.** Show $i_1\to j_1$ and $i_2\to j_2$ in period 1 and let responders answer in period 2. That earns $1.99$.
- **Ratio:** $0.50 < 1-1/e \approx 0.632$.
- **What this does not show.** The alternative is itself semi-adaptive, so this instance does not refute Theorem 5.4's existence claim.

**Theorem 5.3 counterexample.** Machine-checked in Lean: `theorem_5_3_counterexample` in `lean/DatingAlgo/MultiPeriodDHT.lean`. Also checked by brute force in `data/scripts/thm53_counterexample.py`.
- **Instance.**
  - $T=2$, every display cap is 1, and the design is two-directional, with or without mutual views.
  - User $i$ is liked by four initiators $a_1,\dots,a_4$, each with probability $1/2$, and $i$ reciprocates each for sure.
  - $i$ could also initiate toward $j$, who reciprocates with probability $0.99$.
- **What goes wrong.** In (19) each unit of $i$'s budget earns at most 1, and an initiation or mutual view by $i$ earns at most $0.99$. Answering the four $a_k$ earns exactly 2, so every optimal solution spends both of $i$'s slots on responses. But only $i$'s period-2 slot can respond.
- **What Lean checks.**
  1. (19) has optimum 2, and every optimal solution has $i$ initiate nothing and no mutual views.
  2. For every optimal solution and every DHT schedule for it, every feasible response plan yields at most 1 expected match. This includes clairvoyant ones, so it covers DHT's Step 14.
  3. An explicit semi-adaptive policy earns exactly $0.99 + 15/16 = 1.9275$: $i$ initiates toward $j$ in period 1 and answers the first $a_k$ who liked it in period 2.
  4. $1 < (1-1/e)\cdot 1.9275$.
- **Ratio:** $0.519$.

**Unbounded loss for $T \ge 3$ (decoy family).** Brute force in `data/scripts/thm53_repair_test.py`, not in Lean.
- **Instance.**
  - One-directional and sequential-only, with every cap 1.
  - Initiators $v_1,\dots,v_{T-1}$ like responder $i$ for sure, and $i$ likes each back with probability $1-\eta$.
  - Each $v$ also has $T-2$ "decoys" $z$: $v$ likes $z$ with probability $\varepsilon$, and $z$ likes $v$ back with probability close to 1.
- **What goes wrong.** In every optimal solution of (19), each $v$ initiates toward $i$ and every decoy. Step 7 shows the decoys first, because they reciprocate more often. So all $T-1$ likes for $i$ arrive in period $T-1$, and $i$ can answer only one.
- **Result.** DHT earns at most $(1-\eta) + (T-1)(T-2)\varepsilon$. Showing $i$ to every $v$ in period 1 earns at least $(T-1)(1-\eta)$. So the ratio tends to $1/(T-1)$.
- **Brute force** with $\varepsilon=\eta=0.01$: $0.505$ at $T=3$ and $0.347$ at $T=4$.

## Repairing the relaxation
Two timing-aware repairs were tested by exact brute force in `data/scripts/thm53_repair_test.py`. The benchmark is OPT, the best semi-adaptive policy, computed exactly: enumerate every initiation schedule and answer the backlog greedily. Greedy is optimal for a fixed schedule, because all backlog profiles share the deadline $T$. The search covered 4,500 random markets ($T \le 3$, all three designs) plus hill-climbing.

Earlier versions of this note, the log and commit messages call these relaxations R1 and R2. They were renamed so they don't clash with results R1–R4 in [[Match Quality in the Dating Heuristic Framework]].

**Aggregated relaxation $\mathrm{Rel}_{\text{agg}}$: DHT does not keep $1-1/e$.**
- **The relaxation.** For each user $\ell$:
  - responses use at most $K_\ell(T-1)$ slots;
  - initiations and mutual views use at most $K_\ell(T-1)$;
  - the total is at most $K_\ell T$.
- **Result.** DHT runs unchanged on its optimal solutions.
  - For $T=2$, $\mathrm{Rel}_{\text{agg}}$ coincides with the two-period program (16), and DHT is DH-int, so Theorem 4.3 applies. Both $T=2$ counterexamples above are fixed.
  - For $T \ge 3$, the decoy family still gives $1/(T-1)$, for every optimal solution, even though $\mathrm{Rel}_{\text{agg}}$ equals OPT there.
  - Worst ratios to OPT found by the random search:
    - with the best optimal solution: $0.506$ at $T=3$;
    - with the worst optimal solution and mutual views: $0.002$, because Steps 9–12 drop mutual views.
- **Conclusion.** The loss comes from DHT's schedule, not from the relaxation.

**Per-period relaxation $\mathrm{Rel}_\tau$: $1-1/e$ holds, with DHT showing each initiation in the period the solution chose ("DHT-$\tau$"). Machine-checked in Lean.**
- **The relaxation.** It is time-indexed, with binary $x^t_{\ell\ell'}$ and $w^t_e$ ($w^T=0$) and $y^t_{\ell\ell'}\in[0,1]$:
  - $\max \sum_{t,e}\beta_e w^t_e + \sum_{t,\ell,\ell'}\phi_{\ell\ell'} y^t_{\ell\ell'}$ subject to:
  - $\sum_{s\le t} y^s_{\ell\ell'} \le \phi_{\ell'\ell}\sum_{s<t} x^s_{\ell'\ell}$ (answer only likes received earlier);
  - $\sum_t (x^t_{\ell\ell'}+x^t_{\ell'\ell}+w^t_e)\le 1$;
  - $\sum_{\ell'}(x^t_{\ell\ell'}+y^t_{\ell\ell'})+\sum_{e\ni\ell}w^t_e \le K_\ell$ for every $\ell$ and $t$.
- **Numerics.** DHT-$\tau$ never fell below $(1-1/e)\,\mathrm{Rel}_\tau$. Its worst ratio to OPT was $0.76$.
- **Proof sketch.** This is the paper's two-period argument, run on a matroid that remembers periods.
  1. *Upper bound.* Take an optimal semi-adaptive policy. Its fixed schedule gives $x^t, w^t$. Let $y^t_{\ell\ell'}$ be the probability that $\ell$ answers $\ell'$ in period $t$. The constraints hold on every sample path and are linear, so $\mathrm{Rel}_\tau\ge\mathrm{OPT}$.
  2. *One user's value.* Fix an optimal $(x^*,w^*)$. The users who like $\ell$ form a random set $L_\ell$: each is independent, with probability $q_{\ell'}=\phi_{\ell'\ell}x^*_{\ell'\ell}$, and arrives in a known period. Let $f_\ell(L)$ be the best total $\phi_{\ell\ell'}$ that $\ell$ can answer from $L$ in its leftover slots after arrival. The answerable sets form a laminar matroid, since each profile's usable periods form a suffix. So $f_\ell$ is a weighted matroid rank function, which is monotone submodular.
  3. *Greedy is optimal.* Answering the best available profiles each period attains $f_\ell(L)$ on every path, by an exchange argument. So DHT-$\tau$ earns $\sum\beta_e w^*_e + \sum_\ell \mathbb E f_\ell(L_\ell)$.
  4. *The LP is the concave closure.* Given $(x^*,w^*)$, $\mathrm{Rel}_\tau$'s response part for $\ell$ is $\max\{\phi\cdot y: y\le q,\ y\in P(M_\ell)\}$. By Hall's theorem and the integrality of the matroid polytope, this is the concave closure $f^+_\ell(q)$.
  5. *[[Correlation Gap]].* $\mathbb E f_\ell(L_\ell)\ge(1-1/e)f^+_\ell(q)$. Summing over users gives $\text{DHT-}\tau\ge(1-1/e)\,\mathrm{Rel}_\tau\ge(1-1/e)\,\mathrm{OPT}$.
- **Cost.** $\mathrm{Rel}_\tau$ is a MIP with $T$ times as many binary variables as (19).
- **Machine-checked.** `theorem_5_3_repair` and `dhtTau_approx` in `lean/DatingAlgo/MultiPeriodRepair.lean` prove $\text{DHT-}\tau\ge(1-1/e)\,\mathrm{Rel}_\tau\ge(1-1/e)\,\mathrm{OPT}$.
  - The result holds for every design, every optimal solution of $\mathrm{Rel}_\tau$, and every tie-breaking among equally good backlog profiles.
  - DHT-$\tau$'s responses use only the backlog.
  - Also proved:
    - the lower bound holds for every *feasible* solution of $\mathrm{Rel}_\tau$ (`dhtTau_ge`);
    - $\mathrm{Rel}_\tau$ has an optimal solution whenever it is feasible (`exists_isOptTau`).
- **The Lean proof takes a simpler route than the sketch.**
  - *Step 1 is an identity* (`expected_matches_eq`): for every policy in the benchmark, expected matches *equal* $\mathrm{Rel}_\tau$'s objective at the policy's schedule and response probabilities.
  - *No matroids.* Steps 2 and 4 are replaced by a splitting argument (`indepExp_split_le` in `lean/DatingAlgo/GreedyGap.lean`).
    - Assign each profile that likes $\ell$ to period $t$ with probability $y^t_{\ell\ell'}/q_{\ell'}$. The profiles assigned to $t$ form an independent random set with marginals $y^t$.
    - In each period, answering the best profiles assigned to it that fit its free slots is a feasible plan. So greedy earns at least the sum of these per-period values.
    - The top-$K$ correlation gap that is already in `lean/` then bounds each period. So the laminar-matroid correlation gap is not needed.
  - *Step 3* (`greedy_optimal`) is proved by counting rather than exchange. For every threshold $\theta>0$, greedy has answered at least as many profiles of weight $\ge\theta$ as any plan, clairvoyant or not, after every period.
- **What the benchmark must satisfy.** Two rules of the paper's model are needed for $\mathrm{Rel}_\tau\ge\mathrm{OPT}$, and the Lean benchmark assumes both.
  - *Each pair is shown at most one way* ($x_{\ell\ell'}+x_{\ell'\ell}+w_e\le1$). Without it, two users could initiate toward each other in the last period. That acts as a mutual view, which $\mathrm{Rel}_\tau$ forbids there. With $T=1$ this earns $\beta_e>0$ while $\mathrm{Rel}_\tau=0$.
  - *Responses never anticipate likes.* Whether $\ell$ is shown $\ell'$ cannot depend on whether $\ell$ likes $\ell'$, which is revealed only when $\ell$ sees $\ell'$. Every non-anticipating policy satisfies this, including every rule that uses only the backlog. A clairvoyant responder can beat $\mathrm{Rel}_\tau$.
    - Example: one-directional sequential design, $T=2$, every cap 1. Two initiators like $\ell$ for sure, and $\ell$ likes each with probability $1/2$.
    - A responder who knows its own likes matches with probability $3/4$, but $\mathrm{Rel}_\tau=1/2$.

## Gaps
- **$\mathrm{Rel}_{\text{agg}}$ with a better scheduler is untested.** It is unknown whether some schedule built from $\mathrm{Rel}_{\text{agg}}$'s chosen sets always reaches $1-1/e$.
- **Theorem 5.4's existence claim is open.** No instance is known where every semi-adaptive policy misses $1-1/e$ of the best adaptive policy. The Lean repair covers semi-adaptive benchmarks only: responses may adapt to anything observed, but initiations are fixed in advance. An adaptive benchmark needs an LP version of $\mathrm{Rel}_\tau$ plus rounding; $\mathrm{Rel}_\tau$ itself is a MIP.
- **Lean's DHT predicate assumes no mutual-view interference.** Every run of Algorithm 3 satisfies `IsDHTSchedule` when the solution has no mutual views, which covers the Theorem 5.3 counterexample. With mutual views, Algorithm 3 handles users one at a time, so Step 12 can fill a user's slot before that user's own initiations and push one to a later period; the predicate does not allow that.
- **The decoy family is not in Lean.** Only its $T=3$ and $T=4$ cases are checked, by brute force.
- **Simulations unaffected.** The paper's simulations run DH-int as a rolling policy, which these counterexamples do not concern.
