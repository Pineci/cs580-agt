---
type: concept
created: 2026-10-19
updated: 2026-10-19
tags: [social-choice/distortion]
aliases: [distortion in social choice, utilitarian distortion, average-case distortion, ordinal algorithm, ordinal algorithms]
sources: ["[[Filos-Ratsikas 2026 - The Distortion of Stable Matching]]"]
origin: claude
status: seed
---
# Distortion

Distortion is the worst-case ratio between the best achievable value of a social objective and the value achieved by an algorithm that sees only limited information about the agents' utilities. The objective is usually utilitarian welfare, the sum of cardinal utilities. The limited information is typically just the rankings those utilities induce. The notion is due to Procaccia & Rosenschein (2006).

## Details
- **What makes it different.** It is like an approximation or competitive ratio, but the handicap is informational rather than computational or temporal. The motivation is that people find it hard to state cardinal values accurately ([[Filos-Ratsikas 2026 - The Distortion of Stable Matching]]).
- **Definition.**
  $$\mathrm{dist}(\mathcal A)=\sup_{\mathbf v}\frac{\mathrm{OPT}(\mathbf v)}{\mathbb E[\mathrm{SW}(\mathcal A(\succ_{\mathbf v})\mid\mathbf v)]}$$
  The adversary chooses the worst utilities consistent with the reported rankings, after seeing the algorithm's choice.
- **Lines of work.**
  - Deterministic and randomized ordinal algorithms, for voting and for matching.
  - [[Query-Enhanced Algorithms]], which also buy a few cardinal values.
  - Learning-augmented algorithms that use predictions.
  - Average-case distortion with i.i.d. values (Caragiannis & Fehrs 2024).
  - Survey: Anshelevich, Filos-Ratsikas, Shah & Voudouris (2021).
- **Normalization.** Lower bounds for ordinal algorithms usually assume unit-sum utilities. Lower bounds for query-enhanced algorithms are usually stated without normalization.
- **Randomization can help a great deal.** In stable matching, deterministic ordinal distortion is unbounded, while randomized ordinal distortion is exactly 2.

## In stable matching
[[Filos-Ratsikas 2026 - The Distortion of Stable Matching]] was the first to study distortion for [[Stable Matching]]. Its benchmark is the best *stable* matching, since even with full information the best unrestricted matching can be infinitely better.

| Information available | Distortion |
| --- | --- |
| Rankings, deterministic algorithm (incl. [[Deferred Acceptance]]) | unbounded |
| Rankings, randomized algorithm | exactly 2. The lower bound holds even for unstable or fractional outputs. |
| 1 value query per agent, deterministic | 2 (1-MoWo) |
| $<\tfrac12\log_2 n$ adaptive or $<n/2$ non-adaptive queries per agent | still at least 2 |
| $O(\log n/\varepsilon^2)$ adaptive queries per agent | $1+\varepsilon$ (Stable-TSF) |
| [[Rotation Poset]] is a path; $O(\log n/\varepsilon)$ queries per agent | $1+\varepsilon$ |
| Average case, values i.i.d. | at most 2 for DA; about 1.00–1.05 in experiments |

## Related
- [[Query-Enhanced Algorithms]]
- [[Stable Matching]]
- [[Deferred Acceptance]]
