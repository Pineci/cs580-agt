---
type: synthesis
question: "Do Theorems 5.3 and 5.4 of Rios & Torrico (multi-period DHT guarantees) hold as stated?"
created: 2026-10-20
updated: 2026-10-20
tags: [dating/platforms, matching/assortment, research/project]
aliases: [Theorem 5.3 counterexample, Theorem 5.4 counterexample, DHT counterexample]
sources: ["[[Rios 2026 - The Dating Heuristic]]"]
origin: claude
status: seed
---
# Counterexamples to the Multi-Period Dating Heuristic Guarantees

> [!question] Do Theorems 5.3 and 5.4 of Rios & Torrico (multi-period DHT guarantees) hold as stated?

## Answer
No, as far as we can tell. Both appear to be false as stated. This is the project's own analysis from 2026-10-20; the paper does not acknowledge it.

**What the theorems claim.** [[Rios 2026 - The Dating Heuristic]] claims that the $T$-period [[Dating Heuristic]] variants are $(1-1/e)$-approximations:
- **Theorem 5.3:** DHT against the best semi-adaptive policy.
- **Theorem 5.4:** a rounded-LP policy against the best adaptive policy, in the one-directional sequential design.

**The flaw.**
- Both proofs use relaxations, (19) and (41), that pool each user's display slots over all periods: $\sum \le K_\ell T$. That ignores two timing facts:
  - a user can't respond in period 1, because the backlog starts empty;
  - likes received in the last period can never be answered.
- Claim F.1 asserts that DHT's period-by-period backlog responses realize the optimum over *all* likes received. It relies on "$L_\ell = \bigcup_t B^t_\ell$", which is false: last-period likes are in no backlog.

**What still stands.** The two-period Theorem 4.3 is unaffected, because its program (16) keeps a separate capacity for each period. It is machine-checked in `lean/` for every design.

## Evidence
**Theorem 5.4 counterexample.** Machine-checked in Lean: `theorem_5_4_counterexample` in `lean/DatingAlgo/MultiPeriod.lean`. Also checked by brute force in `data/scripts/thm54_counterexample.py`.
- **Instance.**
  - $T=2$, and every display cap is 1.
  - Initiators $i_1, i_2$; responders $j_1, j_2$.
  - Every initiator likes every responder for sure.
  - $j_1$ reciprocates for sure, and $j_2$ with probability $0.99$.
- **LP (41).** Its unique optimum is $x\equiv1$: each initiator initiates toward both responders. It is integral, so rounding returns it unchanged.
- **DHT.** It shows $j_1$ in period 1 and $j_2$ in period 2. $j_2$'s likes arrive in the last period and are never answered, so DHT earns at most 1 expected match, even with clairvoyant responders.
- **Alternative.** Show $i_1\to j_1$ and $i_2\to j_2$ in period 1 and let responders answer in period 2. That earns $1.99$.
- **Ratio:** $0.50 < 1-1/e \approx 0.632$.

**Theorem 5.3 counterexample.** Brute force over every optimal solution of (19), in `data/scripts/thm53_counterexample.py`.
- **Instance.**
  - $T=2$, and every display cap is 1.
  - User $i$ is liked by four initiators, each with probability $1/2$, and $i$ reciprocates each for sure.
  - $i$ could also initiate toward $j$, who reciprocates with probability $0.99$.
- **What goes wrong.** (19) values spending both of $i$'s slots on responses, because responses cost only $\phi$ of the responder's budget. But only $i$'s period-2 slot can respond.
- **Result.** Every optimal (19) solution leads DHT to at most 1.0 expected matches. A simple semi-adaptive policy earns 1.93: $i$ initiates toward $j$ in period 1 and responds in period 2.
- **Ratio:** $0.52$.

## Gaps
- **Possible repair, not yet checked.** Add timing to the relaxations: responses use at most $K_\ell(T-1)$ slots; initiations and mutual views use at most $K_\ell(T-1)$ slots; and the total is at most $K_\ell T$. Whether DHT then keeps $1-1/e$, or what constant it gets, is open.
- **5.3 is not yet in Lean.** Formalizing it needs the two-directional $T$-period model with mutual views.
- **Simulations unaffected.** The paper's simulations run DH-int as a rolling policy, which these counterexamples do not concern.
