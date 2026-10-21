---
type: concept
created: 2026-10-21
updated: 2026-10-21
tags: [matching/signaling, game-theory/incentives, market-design]
aliases: [signaling, signals of interest, roses, virtual roses, scarce signals, preference signals]
sources: ["[[Coles 2013 - Preference Signaling in Matching Markets]]", "[[Lee 2015 - Propose with a Rose]]"]
origin: claude
status: seed
---
# Preference Signaling

In a congested matching market, a participant can send a free but *rationed* message saying "I am especially interested in you". The message has no direct payoff. It is credible only because it is scarce. Unlimited claims of interest carry no information, which is a *babbling* equilibrium ([[Coles 2013 - Preference Signaling in Matching Markets]]).

## Details
**Theory ([[Coles 2013 - Preference Signaling in Matching Markets]]).** Each worker may signal one firm, and each firm may make one offer.
- **Workers.** In the informative (non-babbling) equilibria, each worker signals her top firm.
- **Firms.** Firms use cutoff strategies, offering to their best signaler unless she ranks too far below their overall favorite.
- **Strategic complements.** When other firms respond more to signals, a firm's favorite becomes likelier to be taken, so responding becomes more attractive.
- **Welfare.** Whenever firms respond at all, signals strictly raise the number of matches and every worker's welfare. Firm welfare can go either way, because responding imposes a congestion externality on other firms.
- **Where it matters most.** The gain is largest in balanced markets.
- **Tiered preferences.** Workers signal within their tier.

**Evidence ([[Lee 2015 - Propose with a Rose]]).** This is a field experiment on a Korean dating site, where senders got 2 or 8 roses at random.
- **Acceptance.** A rose raises acceptance by about 3.3 points (about 20%).
  - The effect is concentrated on middle-ranked recipients, and on cases where the sender outranks the recipient.
  - Top recipients ignore roses.
- **Dates.** With 8 roses, senders got 44–86% more accepted proposals.
- **Mechanism.** Roses inform the recipient rather than merely drawing attention.
- **Use in practice.** Many users left roses unused, and roses were not aimed at attainable partners.

**In the dating-heuristic model.**
- A backlog like in [[Rios 2026 - The Dating Heuristic|Rios & Torrico]] is already a signal of interest. A signal only adds information if likes are rationed or costly.
- With free matches, strategic users like everyone and likes say nothing (S3 of [[Strategic Users in the Dating Heuristic Framework]]).
- Like budgets restore information (S4 there), at two costs:
  - likes shade toward attainable partners;
  - they create substitution effects within a display.
- Numeric value reports from LLM agents are unrationed claims, and they are manipulable (S5 there). Rationing is the classic fix.
- *My reading, not a claim of either source.* Lee & Niederle's finding that recipients respond to the sender's interest suggests values are interdependent. The strategic note assumes independent private values.

## Related
- [[Strategic Users in the Dating Heuristic Framework]]
- [[History-Dependent Like Probabilities]]: the "signaling" history effect in Rios & Torrico's simulations.
- [[Two-Sided Assortment Optimization]]
- [[Arnosti 2021 - Managing Congestion in Matching Markets]]: the congestion that makes signals valuable.
