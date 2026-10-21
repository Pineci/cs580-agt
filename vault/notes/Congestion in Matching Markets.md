---
type: concept
created: 2026-10-21
updated: 2026-10-21
tags: [matching/congestion, market-design, game-theory/incentives]
aliases: [congestion, matching market congestion, application limits, like caps, swipe limits, tragedy of the commons in matching, costly screening, wasted search]
sources: ["[[Arnosti 2021 - Managing Congestion in Matching Markets]]", "[[Kanoria 2021 - Facilitating the Search for Partners on Matching Platforms]]", "[[Coles 2013 - Preference Signaling in Matching Markets]]"]
origin: claude
status: seed
---
# Congestion in Matching Markets

A decentralized matching market is *congested* when attention is scarce relative to activity. Agents spend effort on applications that are never read, on screening partners who are no longer available, or on offers that are declined. Each agent ignores the effort it imposes on others, so the market can lose much of its value. A platform has several levers: limits, costs, restricting who may initiate, signals, and central curation.

## Details
**Free applications cause a tragedy of the commons** ([[Arnosti 2021 - Managing Congestion in Matching Markets]]).
- **Model.** A mean-field market with application cost $c_a$ and screening cost $c_s$.
- **Two regimes.**
  - *Screening-limited:* employers earn exactly zero.
  - *Application-limited:* with $r>1$ applicants per employer, applicants keep at most $\frac1r(1-(r-1)\log\frac{r}{r-1})$ of their benchmark, whatever the costs.
- **Levers.**
  - An application limit brings either side near its benchmark. In screening-limited markets it is a Pareto improvement.
  - Raising the application cost looks the same as a limit to employers, but always weakly hurts applicants.
- **Where the gains come from.** Limits help through *availability*, not information: an application reveals nothing about fit.

**Wasted screening, and who should propose** ([[Kanoria 2021 - Facilitating the Search for Partners on Matching Platforms]]).
- **Model.** Agents pay $c$ to learn their value for a candidate.
- **Recipients are too selective.** They ignore the screening they make proposers waste. A proposer whose acceptance chance is $p$ effectively pays $c/p$, so proposers stop screening early.
- **Restricting who proposes.**
  - In unbalanced markets the long side proposes and can barely screen. Blocking it from proposing gives a better equilibrium.
  - With quality tiers, blocking the long side *and* hiding quality removes "reaching" for top partners. This is a Pareto improvement as $c\to0$.

**Scarce signals ease congestion.** [[Coles 2013 - Preference Signaling in Matching Markets]] gives each worker one signal and each firm one offer. The signals cut the number of offers that collide; see [[Preference Signaling]].

**In the dating-heuristic model.**
- [[Rios 2026 - The Dating Heuristic|Rios & Torrico]] handle congestion centrally. The display cap $K$ already acts as an application limit, and DH-int routes attention away from swamped popular profiles. Their naive baselines fail for exactly this reason (Prop. D.1).
- With strategic users ([[Strategic Users in the Dating Heuristic Framework]]):
  - free matches make likes uninformative rather than congesting;
  - like budgets ration likes the way an application limit does;
  - Kanoria & Saban's $c/p$ effect suggests that the platform's display plan decides whether users bother to evaluate profiles before liking them.

## Related
- [[Preference Signaling]]
- [[Two-Sided Assortment Optimization]]
- [[Strategic Users in the Dating Heuristic Framework]]
- [[Dating Heuristic]]
