---
type: concept
created: 2026-10-19
updated: 2026-10-21
tags: [dating/behavior, dating/platforms]
aliases: [history effect, history effects, history-dependent preferences, like probability, like probabilities]
sources: ["[[Rios 2026 - The Dating Heuristic]]", "[[Lee 2015 - Propose with a Rose]]"]
origin: claude
status: seed
---
# History-Dependent Like Probabilities

The probability that a dating-app user likes a profile they're shown is modeled as depending on their own past experience on the platform, rather than as a fixed number. Relevant history includes matches obtained, likes and dislikes given, the backlog, and time on the app.

## Details
- **Formal model in [[Rios 2026 - The Dating Heuristic]].**
  - $\phi^t_{\ell\ell'}(\sigma^t_\ell)=\Pr(\ell\text{ likes }\ell'\mid\sigma^t_\ell)$.
  - The history $\sigma^t_\ell$ is (likes given, dislikes given, backlog, matches so far).
  - Users can't see who disliked them or who their potentials are, so those aren't part of the history.
  - Like probabilities are independent across users and don't depend on the other profiles shown alongside. The data show little substitution (Rios, Saban & Zheng 2023).
- **Parametric form used in the simulations:**
  $$\phi=\frac{\exp(u_{\ell\ell'}+\gamma(\sigma))}{1+\exp(u_{\ell\ell'}+\gamma(\sigma))}$$
  Here $u$ comes from a logit with user and date fixed effects. Five forms of $\gamma$ are compared:
  - none;
  - **linear in matches:** $\gamma|M|$ with $\gamma=-0.170$, as estimated by Rios, Saban & Zheng (2023). More recent matches make users pickier.
  - **threshold:** stop liking after more than 5 matches, capturing limited time and attention;
  - **disengagement:** $\gamma t$ with $\gamma=-0.2$;
  - **signaling:** $+0.2$ when the user knows the profile is from their backlog, i.e. already likes them. Compare Lee & Niederle (2014), "propose with a rose".
    - Their experiment ([[Lee 2015 - Propose with a Rose]]) measures something different: the extra effect of a *scarce* signal on top of a known like. It is about $+3.3$ points of acceptance, concentrated where attainability is in doubt.
    - Strategic users produce history effects of their own. Under a top-$k$ objective, thresholds rise with matches already held: see S7 of [[Strategic Users in the Dating Heuristic Framework]].
- **Consequence for algorithms.**
  - History dependence makes next period's objective nonlinear in this period's decisions.
  - One-lookahead heuristics like the [[Dating Heuristic]] therefore substitute current probabilities for next-period ones. This is optimistic when probabilities fall with history.
  - DH-int's advantage over the baselines grew with the strength of the linear effect, from about 20% to 25%.
- **Asymmetry in the calibration data** (Houston, 2020):
  - Women's like probabilities are concentrated near 0, with mean about 0.30.
  - Men's are spread out with a mode near 1, with mean about 0.53.

## Related
- [[Dating Heuristic]]
- [[Two-Sided Assortment Optimization]]
