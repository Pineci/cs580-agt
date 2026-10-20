---
type: concept
created: 2026-10-19
updated: 2026-10-20
tags: [dating/platforms, matching/assortment, algorithms]
aliases: [DH, DH-int, DHT, Integral Dating Heuristic, T-periods DH-int, one-lookahead policy, one-lookahead policies]
sources: ["[[Rios 2026 - The Dating Heuristic]]"]
origin: claude
status: seed
---
# Dating Heuristic

A one-period-lookahead policy for deciding which profiles a dating platform shows each user. Each period it solves a linear or mixed-integer program that plans this period's displays together with the backlog responses they are expected to generate next period. It then shows only this period's part. It was introduced by Rios, Saban & Zheng (2023) and analyzed in [[Rios 2026 - The Dating Heuristic]].

## Variants
From Table 1 of [[Rios 2026 - The Dating Heuristic]]:

| Variant | Type | Lookahead horizon | First-period variables | Later-period variables |
| --- | --- | --- | --- | --- |
| DH | adaptive | 2 periods | continuous, then rounded | continuous |
| DH-int | adaptive | 2 periods | binary | continuous |
| DHT | semi-adaptive | $T$ periods | binary | binary |

## Details
- **DH-int program,** solved every period $t$:
  - **Objective.** Maximize the sum of three terms:
    - expected matches this period from showing backlog profiles, $\sum\phi^t x^t$;
    - expected matches from same-period mutual views, $\sum\beta^t w^t$;
    - expected matches next period, using proxy probabilities, $\sum\hat\phi^{t+1}x^{t+1}+\sum\hat\beta^{t+1}w^{t+1}$.
  - **Constraints.**
    - At most $K_\ell$ profiles per user per period.
    - Each pair is viewed at most once.
    - $x^{t+1}_{\ell\ell'}\le\phi^t_{\ell'\ell}\,x^t_{\ell'\ell}$ for non-backlog profiles: $\ell$ can be shown $\ell'$ next period only to the extent that $\ell'$ is shown $\ell$ now and likes them.
  - **Proxy.** $\hat\phi^{t+1}$ ignores history; usually $\hat\phi^{t+1}=\phi^t$.
- **Original DH.**
  - The same idea as an LP with every variable continuous.
  - Rounding adds backlog profiles with positive weight first, then initiating profiles, each in decreasing order.
  - The original paper also adds a penalty term for history effects.
- **DHT.**
  - Solves one $T$-period relaxation up front, with per-user budget $K_\ell T$.
  - Shows the selected initiating profiles in decreasing order of the other side's like probability, then fills leftover slots from the backlog.
  - Never re-optimizes, which makes it cheap to run.
- **Guarantees.** Both proofs use the [[Correlation Gap]] of monotone [[Submodular Maximization|submodular]] second-period values.
  - DH-int is a $(1-1/e)$-approximation of the optimal adaptive policy in the two-period model, for every platform design.
  - DHT is $(1-1/e)$ against the best semi-adaptive policy over $T$ periods, assuming like probabilities don't change over time.
    - *This claim (the paper's Theorem 5.3) appears to be false; see [[Counterexamples to the Multi-Period Dating Heuristic Guarantees]].* The two-period claim above is machine-checked in `lean/`.
  - DH-int is not polynomial-time, because it solves a MIP.
- **Why it works,** per the simulations in [[Rios 2026 - The Dating Heuristic]]:
  - It balances the chance of an initial like against the chance of reciprocation.
  - It accepts lower like rates on initial shows in exchange for backlogs that convert at higher rates.
- **Performance** (Houston data, 7 days, $K=3$, linear history effect):

  | Algorithm | Matches |
  | --- | --- |
  | DH-int | 4691 |
  | DH | 4634 |
  | DHT | 4442 |
  | Greedy | 3948 |
  | Per-period perfect matching | 3676 |
  | Partner's production algorithm | 3597 |

  DH-int is close to the upper bound.

## Related
- [[Two-Sided Assortment Optimization]]
- [[History-Dependent Like Probabilities]]
- [[Correlation Gap]]
- [[Submodular Maximization]]
- [[Match Quality in the Dating Heuristic Framework]]: the project's analysis of DH-int when match *quality*, not just count, matters. It includes a sharper, tight constant $1-e^{-K}K^K/K!$ for DH-int itself.
