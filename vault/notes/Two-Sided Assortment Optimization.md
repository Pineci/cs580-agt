---
type: concept
created: 2026-10-19
updated: 2026-10-21
tags: [matching/assortment, dating/platforms]
aliases: [curated dating, curated dating platform, curated dating platforms, profile recommendation, dating platform design, backlog, sequential match, non-sequential match, one-directional, two-directional]
sources: ["[[Rios 2026 - The Dating Heuristic]]", "[[Kanoria 2021 - Facilitating the Search for Partners on Matching Platforms]]"]
origin: claude
status: seed
---
# Two-Sided Assortment Optimization

On a two-sided platform, deciding which options (profiles, suppliers, customers) to show each participant when a match requires interest from *both* sides. The running example: which profiles a dating app should show each user each day to maximize mutual likes.

## Details
- **One-sided vs. two-sided.**
  - One-sided assortment optimization (retail) picks product sets for a stream of customers.
  - Two-sided versions add the requirement that the other side accepts too. Earlier papers [[Rios 2026 - The Dating Heuristic]] cites:
    - Ashlagi et al. (2022): strongly NP-hard, constant-factor approximation.
    - Torrico, Carvalho & Lodi (2021): improved approximation.
    - Aouad & Saban (2022): online version, where greedy gets 1/2.
  - In those models one side initiates, each agent matches at most once, and choices follow a choice model.
- **The dating-platform model of [[Rios 2026 - The Dating Heuristic]].**
  - Users may like many profiles and match many times.
  - Each period a user sees at most $K_\ell$ profiles.
  - Likes are independent across profiles.
  - Matches form in two ways:
    - **Sequential:** through the *backlog*, the people who liked you but haven't been shown to you yet.
    - **Non-sequential:** both users see each other in the same period and both like.
- **Platform design levers,** modeled as restrictions on which policies are allowed:
  - **One- vs. two-directional:** whether only one side may initiate. Coffee Meets Bagel's "Ladies Choice" is one-directional.
  - **Sequential-only vs. non-sequential allowed:** whether two users may see each other in the same period. Tinder's "Hot Takes" and video speed-dating allow it.
  - **Telling users a profile already liked them.** A paid feature on many apps. It raises reciprocation; compare the signaling results of Lee & Niederle (2014).
- **Why it's hard.**
  - The problem is NP-hard (Rios, Saban & Zheng 2023).
  - The state (potentials, backlogs, histories) grows combinatorially.
  - So practical policies are one-period-lookahead heuristics like the [[Dating Heuristic]].
- **Naive policies can fail badly.** Both of these are only $O(1/n)$-approximate in the worst case:
  - Per-user greedy, which ignores congestion on popular profiles.
  - Per-period maximum matching, which ignores what realized likes reveal.
- **Empirical patterns** from the Houston simulation in [[Rios 2026 - The Dating Heuristic]]:
  - Most matches are sequential.
  - One-directional designs lose relatively little: about 9% for DH-int.
  - Women initiating beat men initiating for every algorithm tested.
- **Related problem:** stochastic matching in the query-commit model. Chen et al. (2009) show greedy gets 1/4; see also Jeloudar et al. (2021).

### Who should initiate, when users are strategic (2026-10-21)
- **Non-strategic users.** In [[Rios 2026 - The Dating Heuristic]], a one-directional design can only lose matches, about 9% fewer than two-directional.
- **Strategic users.** In [[Kanoria 2021 - Facilitating the Search for Partners on Matching Platforms]], screening is costly and users act strategically. There, blocking the long side from proposing creates a better equilibrium, and with quality tiers, hiding quality as well gives a Pareto improvement as $c\to0$.
- **Open target.** A one-directional DH-int might beat a two-directional one once likes are costly or budgeted. See [[Strategic Users in the Dating Heuristic Framework]] and [[Congestion in Matching Markets]].

## Related
- [[Dating Heuristic]]
- [[History-Dependent Like Probabilities]]
- [[Submodular Maximization]]
- [[Stable Matching]]: the centralized-clearinghouse alternative, which is one-to-one and judged by stability rather than by number of matches.
- [[Query-Enhanced Algorithms]]: displays as elicitation; see the note there.
