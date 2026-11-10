# Lean proofs

Machine-checked versions of Rios & Torrico's dating-heuristic results and of the
project's own match-quality and truthful-swiping results, in Lean 4 with Mathlib.
- The math is in the vault notes `vault/sources/Rios 2026 - The Dating Heuristic.md`,
  `vault/notes/Match Quality in the Dating Heuristic Framework.md` and
  `vault/notes/Truthful Swiping with an LLM Oracle.md` and
  `vault/notes/Max-Min Match Quality and Egalitarian Matching.md`.
- `lean/check.sh` reports the current status.

## Setup

From the repo root:

```bash
./setup_lean.sh
```

This installs elan (the Lean version manager) if needed, then downloads the pinned
Lean version and Mathlib's prebuilt cache, about 7 GB on disk. It finishes by
building the project and listing open targets. It is safe to re-run.

**Editor.** Install the "Lean 4" extension in VS Code and open any `.lean` file. The
first file you open takes a few seconds to load Mathlib.

**iCloud.** Lake keeps Mathlib under `lean/.lake`. Here that is a symlink to
`lean/.lake.nosync`, which iCloud Drive doesn't sync, so the 7 GB never uploads.
Both are gitignored.

## Day to day

```bash
lean/check.sh            # build, then report what is proved
lean/check.sh --strict   # also fail unless everything is fully proved
```

`check.sh` runs `lake build`, then `scripts/AxiomCheck.lean`. That script asks Lean
which axioms every theorem depends on and reports:
- **open:** the theorem's own proof contains `sorry`;
- **depending on an open result:** no `sorry` of its own, but it relies on one,
  possibly indirectly;
- **non-standard axioms:** anything beyond `propext`, `Classical.choice` and
  `Quot.sound`. This makes the check fail.

**Check single files with the build's options.** `lake env lean File.lean` ignores the
`autoImplicit := false` setting in `lakefile.toml`, so a file can pass it and still
fail `lake build`. To check one file, use
`lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false File.lean`.
`lake build` (or `check.sh`) is the ground truth.

## Status

Current count: 1008 theorems, all fully proved. The count includes lemmas Lean generates
for definitions and structures, such as the fields of `Feasible19`.

### Rios & Torrico's results

| Paper result | File | Status |
| --- | --- | --- |
| **Theorem 4.3**: DH-int is a $(1-1/e)$-approximation (two periods, every design) | `TwoPeriod.lean` (`dhInt_approx`), `Designs.lean` (`dhInt_approx_market`) | proved, assuming DH-int's MIP (16) has an optimal solution (existence not formalized). "Every design" means every predicate on period-1 displays; OPT is Problem 4.2's optimum |
| Correlation-gap step of Thm 4.3 (Agrawal et al. 2010, for weighted top-K) | `CorrelationGap.lean` (`topK_correlation_gap`) | proved from scratch |
| Lemma C.5 (DH-int's program bounds OPT) | `TwoPeriod.lean` | proved |
| Lemma 4.1 (`f` monotone submodular) | `TopK.lean`, `Submodularity.lean` | proved |
| Lemma C.2 (`M²` monotone submodular) | `Submodularity.lean` | proved |
| Proposition 3.4 (`f` not submodular with period-2 mutual views) | `NonSubmodular.lean` | proved (smaller instance than the paper's) |
| Proposition D.1 (local greedy can be $O(1/n)$-bad) | `Baselines.lean` | instance values proved (local greedy earns 1, another display earns $1+(n-1)(1-\varepsilon)$); the $O(1/n)$ ratio follows by arithmetic |
| Lemma E.5, §E.1 (designs as partition matroids) | `Designs.lean` | proved: feasibility is equivalent to independence in two partition structures; the matroids themselves are not constructed |
| **Theorem 5.4** ($T$ periods, one-directional: *some* semi-adaptive policy is within $1-1/e$ of the best adaptive policy) | `MultiPeriod.lean` (`theorem_5_4_counterexample`) | **proof refuted**: the policy of Remark 5.5 (LP (41), rounding, DHT) gets ratio 0.50 < 0.632. The existence claim itself is open. The rounding step is argued in the docstring, not formalized |
| **Theorem 5.3** ($T$ periods, DHT) | `MultiPeriodDHT.lean` (`theorem_5_3_counterexample`) | **refuted**: proved counterexample, ratio 0.52 < 0.632. It covers every optimal solution of (19), both two-directional designs, and clairvoyant responders |
| Lemmas C.3, C.4 | — | not needed: our direct correlation-gap proof replaces them |
| Thm 4.4, Props E.1/E.6/E.10/E.12 | — | not formalized: they apply cited algorithms (continuous greedy, local search, dependent rounding) to the structure above |
| Lemma E.9, E.11; Thm E.13; Prop D.2; Lemma 5.2, F.2; Prop B.2; Lemma B.1 | — | not formalized |

### The project's repair of Theorem 5.3

A corrected $T$-period algorithm with the guarantee Theorem 5.3 claims. It is not a minimal
fix of DHT: it uses a new relaxation, $\mathrm{Rel}_\tau$, and a new scheduler, DHT-τ, which
keeps only DHT's response step (vault note, "Repairing the relaxation").

| Result | File | Status |
| --- | --- | --- |
| $\text{DHT-}\tau \ge (1-1/e)\,\mathrm{Rel}_\tau \ge (1-1/e)\,\mathrm{OPT}$ | `MultiPeriodRepair.lean` (`theorem_5_3_repair`, `dhtTau_approx`) | proved, for every design, every optimal solution of $\mathrm{Rel}_\tau$ and every tie-breaking. OPT is the best semi-adaptive policy with non-anticipating responses |
| Correlation gap for greedy $T$-period backlog responses (one user; replaces the vault sketch's laminar-matroid gap) | `GreedyGap.lean` (`greedy_correlation_gap`, `greedy_optimal`) | proved |

### Match-quality results (vault note)

| Result | File | Status |
| --- | --- | --- |
| R1: sharper constant $c_K$ for DH-int, for any $K$ at most every cap (e.g. $K=\min_\ell K_\ell$) | `PoissonGap.lean` (`dhInt_approx_cK`) | proved; the tightness example is not formalized |
| R1 key lemma: $\mathbb E\min(X,K)\ge c_K\min(\mu,K)$ | `PoissonGap.lean` (`poissonBinomial_min_ge`) | proved: finite comparison with $\mathbb E\min(\mathrm{Poi}(\mu),K)$, no measure theory |
| $c_K$ increases in $K$, so $c_K \ge c_1 = 1-1/e$ | `CorrelationGap.lean` (`cK_mono`, `one_sub_exp_neg_one_le_cK`) | proved |
| R2: quality-weighted DH-int keeps $c_K$ (so also $1-1/e$) | `PoissonGap.lean` (`dhInt_quality_approx_cK`); `TwoPeriod.lean` (`dhInt_quality_approx`, the $1-1/e$ version) | proved |
| R3: no quality guarantee for DH-int as written; trade-off; mixing | `QualityBounds.lean` | arithmetic core only: the inequalities are proved for the numbers involved, but the instances and DH-int's behavior on them are not modeled |
| R4: additive optimum loses $(K+1)/2$ in best-match quality ($k=1$) | `QualityTopK.lean` | proved on the instance, for every $K$: every additive optimum has best-match total $2K$, while another feasible set gets $2K+2K(K-1)q_o$. That quality-weighted DH-int picks an additive optimum there is argued in prose |
| R5: top-$k$ algorithm (credit-DH, $\rho\,c_k$) | — | informal proof in the vault note "Top-k Match Quality"; not formalized |

### Truthful swiping and screened DH (vault note "Truthful Swiping with an LLM Oracle")

| Result | File | Status |
| --- | --- | --- |
| Theorem 1(a): if the acceptable profiles seen are cost-separable, sincere swiping is best against every set $R$ of profiles that would match | `TruthfulSwiping.lean` (`sincere_best`) | proved, per realization. Only subadditivity and $v(\{x\}) = q_x$ are assumed |
| Theorem 1(b): otherwise some $R$ makes another choice strictly better | `TruthfulSwiping.lean` (`sincere_not_best`) | proved |
| Theorem 1 corollaries: additive always; top-$k$ iff at most $k$ acceptable | `TruthfulSwiping.lean` (`costSeparable_sum`, `costSeparable_topK_iff`) | proved |
| Theorem 1, matroid corollary: acceptable profiles are cost-separable iff independent | `MatroidSwiping.lean` (`costSeparable_wRank_iff`; `wRank` is weighted matroid rank on Mathlib's `Matroid`) | proved, for $c > 0$ and non-negative values |
| Lemma 1′ for SDH: whatever a user does, its matches are $D \cap R$ with $R$ independent of its swipes | `TruthfulSwiping.lean` (`matchesOf_update`) | proved for SDH's two-period game |
| Lemma 1′ for every swipe-local policy: what a user sees, and $R$, do not depend on its strategy | `SwipeLocal.lean` (`seen_update`, `wouldMatch_update`, `matchSet_update`) | proved, for any period-1 displays and any period-2 rule that picks from the backlog, with mutual views |
| Theorem 5: DSIC under every swipe-local policy when the acceptable profiles seen are cost-separable; 5(b) DH-int, weighted DH-int and credit-DH are universally DSIC for additive users | `SwipeLocal.lean` (`swipeLocal_dsic`, `swipeLocal_dsic_additive`, `swipeLocal_dsic_topK`) | proved, against every behavior of the others |
| Theorems 3(a), 5(a): SDH is DSIC | `TruthfulSwiping.lean` (`sdh_dsic`, `sdh_dsic_topK`) | proved: against every behavior of the others, including strategies that react to what they see, for every realization of values and coins. For top-$k$ it needs only at most $k$ planned partners |
| Theorem 5(d): a sincere user's utility is at least 0 | `TruthfulSwiping.lean` (`sdh_sincere_nonneg`) | proved |
| Theorems 3(a), 5(a) for matroid users | `MatroidSwiping.lean` (`sdh_dsic_matroid`) | proved, for a loopless matroid and independent planned partners |
| Theorem 5(e): if the users outside `Dev` are sincere, welfare is at least the net weight of the planned pairs with neither end in `Dev` | `SDHRobust.lean` (`sdh_robust`); key step `sdh_arc_matches` in `TruthfulSwiping.lean` | proved, for values additive on planned partners |
| Lemma R: a match set with every degree at most $2K$ can be oriented with at most $K$ initiations and $K$ responses per user, and SDH's game then matches exactly that set | `Orientation.lean` (`exists_balanced`, `lemmaR`, `lemmaR_realize`, `matchesOf_card_le`) | proved. The proof splits off two edges at a vertex and inducts, instead of the note's Euler tours |
| Impossibility 1: the 10/5 example (no dominant strategy) and the Bayes–Nash failure | `SwipeRegret.lean` (`impossibility1_values`, `impossibility1_no_dominant`, `like_gain_le`, `impossibility1_bn_example`) | proved |
| Theorem 2(a): on the note's instance, any mechanism in which `a`'s expected utility is at least 0 earns at most $((1+\varepsilon)k/b + \delta)\,\mathrm{OPT_{FI}}$ for large $H$ | `PriceOfIR.lean` (`thm2a_welfare_le`, `thm2a`) | proved. The mechanism enters only through the distribution of `a`'s match count and $\mathbb E\,u_a \ge 0$, which every equilibrium gives |
| Theorem 2(b): $\mathrm{OPT_{FI}} \le (b/k)\,\mathrm{OPT_{IR}}$ for top-$k$ | `PriceOfIR.lean` (`welfare_topK_le`, `optFI_topK_le`, `optFI_topK_le_ceil`) | proved, **sharpened** from the note's $\lceil b/k\rceil$ to $b/k$, via König's edge-coloring theorem (`EdgeColoring.lean`) |
| Theorem 2(c), (d): subadditive $\mathrm{OPT_{FI}} \le b\,\mathrm{OPT_{IR}}$ (cap 1); additive $\mathrm{OPT_{FI}} = \mathrm{OPT_{IR}}$ | `PriceOfIR.lean` (`optFI_subadditive_le`, `optFI_additive`) | proved |
| SDH against full information: $c_k^2 (k/b)$ for top-$k$, $c_1^2/b$ for subadditive | `PriceOfIR.lean` (`sdh_vs_optFI_topK`, `sdh_vs_optFI_subadditive`) | proved |
| König's edge-coloring theorem; a degree-$\le k$ subgraph keeps a $k/b$ share of any weight | `EdgeColoring.lean` (`exists_matching_cover_max`, `exists_edgeColoring`, `exists_degCap_subset`) | proved from Hall's theorem in Mathlib |
| Theorem 3(b), first step: the LP bounds $\mathrm{OPT_{IR}}$, and has an optimal plan | `ScreenedDH.lean` (`exists_lpValue_eq_optIR`, `optIR_le_lpValue`, `exists_isLPOptimal`) | proved |
| Theorem 3(b): SDH $\ge c_K^2\,\mathrm{LP} \ge c_K^2\,\mathrm{OPT_{IR}}$ for size caps, $K$ at most every cap | `ScreenedDH.lean` (`lpValue_le_sdhValue`, `sdh_welfare`) | proved, for every feasible plan and every query probabilities with $x_{e,c} \le \tau_e \pi_{e,c}$ |
| Theorem 3(b) for matroid users: SDH $\ge (1-1/e)^2\,\mathrm{LP} \ge (1-1/e)^2\,\mathrm{OPT_{IR}}$ | `MatroidSDH.lean` (`matroid_correlation_gap`, `prodExp_matroid_gap`, `lpValue_le_sdhValueM`, `sdh_welfare_matroid`) | proved. The plan constrains each user's pair totals to the matroid polytope, defined as the convex hull of indicator vectors of independent sets. The correlation gap is proved without derivatives, by adding `N` independent rounds and letting `N → ∞` |
| Theorem 3(c) for matroid users: a user's planned total is at most its rank | `MatroidSDH.lean` (`sum_le_of_mem_matroidPolytope`) | proved; with the per-pair bound `sdhTau_le` this gives $O(\mathrm{rank}/\hat p)$ calls |
| The $c_K$ gap for independent random weights (layer cake + R1's lemma) | `ProdExp.lean` (`prodExp_randomWeight_gap`, `prodExp_columns_gap`) | proved |
| Welfare on IR sets is the sum of net weights | `ScreenedDH.lean` (`welfare_eq_sum_wt`) | proved |
| Theorem 3(c): $\tau_e \le x_e/\hat p_e$, calls per user $\le b'_\ell/\hat p$, a queried pair costs $\le 1 + \sqrt{\phi_I \phi_J}$ calls | `ScreenedDH.lean` (`sdhTau_le`, `sum_callsI_le`, `sum_callsJ_le`, `callsI_add_callsJ`) | proved for **corrected** statements: the plan splits a tied bar level proportionally, and $\hat p_e$ is the mass strictly above the bar if positive, else at the bar. The note's version (ties filled in any order) is false |
| Bar shape is without loss of generality | `ScreenedDH.lean` (`exists_barShaped`, `exists_optimal_barShaped`) | proved |
| Theorem 3(d): scaling the plan by $\lambda$ scales calls by $\lambda$ and keeps $c_K^2 \lambda\,\mathrm{OPT_{IR}}$ | `ScreenedDH.lean` (`sdh_budget`, `sum_callsI_budget`) | proved |
| Theorem 4: any policy earns at most $p(2\bar q/b + 2)(1 + o(1))\,\mathrm{OPT_{FI}}$ | `QueryLowerBound.lean` (`indepExp_revealed_true`, `thm4_policy`, `maxBMatch_ge`, `thm4`, `thm4_asymp`) | proved, with an explicit threshold; $np \to \infty$ with $b \le np$ suffices (the note assumed $np \ge C(K + \log n)$). The benchmark uses Chebyshev and König instead of Chernoff bounds and LP integrality |
| Proposition 4: regret identity $c(\lvert M\rvert - k)^+$, ε-Bayes–Nash, not DSIC; welfare identity; $\mathbb E(\lvert M\rvert-k)^+ \le k e^{-k}k^k/k!$ | `SwipeRegret.lean` (`topK_regret_le`, `topK_regret_attained`, `topK_regret_expect`, `topK_regret_worst`, `topK_util_eq_net`, `excess_le`) | proved. The inequality $U_k^{\rm net} \ge \rho c_k\,\mathrm{OPT_0}$ in 4(b) cites R5 (`Top-k Match Quality`), which is not formalized |
| Proposition 5: budgets never bind under SDH; per-period matches $\le \min(K, L)$; period-2 best response under a budget | `SDHRobust.lean` (`sdh_budget_feasible`), `SwipeLocal.lean` (`matchSet_card_le_budget`), `SwipeRegret.lean` (`budget_resp_le`, `budget_resp_attained`) | proved; 5(d) is not analyzed in the note |
| Proposition 6: zero-query DSIC for top-$k$ iff at most $k$ profiles that can match; then $\mathbb E W \le 2p(1+o(1))\,\mathrm{OPT_{IR}}$ | `SwipeRegret.lean` (`zeroQuery_topK_dsic_iff`), `QueryLowerBound.lean` (`prop6b_policy`, `prop6b_asymp`) | proved |
| T5 examples: ex post but not DSIC; SDH is manipulable through oracle reports | `SwipeRegret.lean` (`expost_not_dsic`), `SDHRobust.lean` (`report_manipulation`) | proved |
| Worked example: LP $= 3.25$, $\tau = (1,1,0)$, SDH $= 2.625$, $\mathrm{OPT_{IR}} = 2.875$, 2 calls for Ann | `WorkedExample.lean` | proved, on the `ScreenedMarket` definitions |
| Continuous values: the example table; $F_e$ concave; a fully used combination forces $\tau_e = 1$ | `WorkedExample.lean` (`continuous_example`, `pairValue_concave`, `sdhTau_eq_one_of_full`) | proved |
| Theorem 3(b) for continuous priors (any priors with finite means): SDH $\ge c_K^2$ times the plan's value | `ContinuousSDH.lean` (`contSDH_welfare`) | proved, with SDH's own max-weight selection, for every feasible query-aware plan (SDH's plan is the case with no budget). See the query-budget section below |

### The live-set theorem and the two-cost model (vault note "The Live-Set Theorem for Truthful Swiping")

One user, yes/no swipes, a platform that cannot see values. `twoCostUtil v c d S` is
$\max_{T \subseteq S} v(T) - c\lvert T\rvert - d\lvert S \setminus T\rvert$. A `SwipeTree`
is what the user faces once the platform's coins and the others' strategies are fixed.

| Result | File | Status |
| --- | --- | --- |
| Theorem A, top-$k$: for $d > 0$, sincere swiping is dominant iff the matches are $X \cap S$ for a live set with $\lvert S\rvert \le k$ | `LiveSet.lean` (`liveSet_iff` for any outcome rule with $M(X) \subseteq X$; `swipeTree_liveSet_iff` for swipe trees; `liveSet_of_dominant`, `twoCost_sincere_best_topK` for the two directions) | proved. Types are the value vectors within $\delta \le c$ of the cost; the "if" direction holds for every non-negative value vector and $d \ge 0$ |
| Theorem A, additive users: matches are $X \cap S$ with $S$ unrestricted | `LiveSet.lean` (`liveSet_iff_additive`) | proved, as the case $k = \lvert\beta\rvert$ |
| Theorem A at $d = 0$: the size restriction disappears | `LiveSet.lean` (`liveSet_iff_zero_drop`) | proved for top-$k$ with $k \ge 1$ (the note states it for every subadditive class) |
| Corollary: own-swipe independence | `LiveSet.lean` (`own_swipe_independence`) | proved |
| Swipe trees: every path is the path of the set it likes; matches are liked profiles | `LiveSet.lean` (`SwipeTree.exists_run_of_reach`, `SwipeTree.run_subset`) | proved |
| Theorem B, top-$k$: under a live set of any size the regret of sincere swiping is exactly $d(\lvert M\rvert - k)^+$; welfare identity; sincere is best at $d = 0$ | `LiveSet.lean` (`twoCost_topK_regret_le`, `twoCost_topK_regret_attained`, `twoCost_topK_eq_net`, `twoCost_zero_drop_sincere_best`) | proved, for $0 \le d \le c$ and non-negative values |
| $d = c$ is the one-cost model | `LiveSet.lean` (`twoCostUtil_eq_swipeUtil`) | proved, for monotone valuations |
| Theorem A for matroid users and for classes containing top-1; Theorem A′ (platform coins); Theorem B for matroid and subadditive users; Theorem B′ (general costs); Proposition P | — | not formalized |

### Max-min screened DH (vault note "Max-Min Match Quality and Egalitarian Matching")

The note claims that SDH run on a max-min optimal plan gives every user at least
$c_K^2\,\theta^*$. That is **false** for SDH's own selection (the best capped set of
found pairs), whose guarantee is on total weight only. It is **true** when the selection
protects every pair: with `c_K`-balanced selection rules at both stages. Uniformly
random selection gives `1/4`. See the note's Correction section.

| Result | File | Status |
| --- | --- | --- |
| The max-min LP bounds the benchmark: every full-information policy (any law over capped sets of acceptable pairs, chosen knowing all values) induces a feasible plan with the same expected surplus for every user, so $\mathrm{OPT}_{\min} \le \theta^*$ | `MaxMinSDH.lean` (`exists_plan_of_policy`, `floor_le_maxMin`) | proved |
| Composition: if every stage-1 rule is $\gamma_1$-balanced and every stage-2 rule is $\gamma_2$-balanced, every user gets at least $\gamma_1\gamma_2$ of its planned surplus | `MaxMinSDH.lean` (`mmUtilI_ge`, `mmUtilJ_ge`; key step `expect_pairVal`, an exact factorization $\mathbb E[\text{gain}]\,\kappa_1\kappa_2$) | proved, for every feasible plan and query probabilities with $x_{e,c} \le \tau_e \pi_{e,c}$. The mechanism screens and thins as SDH's analysis does (`thinLaw`) |
| Random order: uniformly random selection is $1/2$-balanced, so every user gets $\ge 1/4$ of its planned surplus and the worst-off user $\ge \theta^*/4 \ge \mathrm{OPT}_{\min}/4$ | `UniformRule.lean` (`uniformRule_balanced`, via `min_one_div_ge`); `MaxMinSDH.lean` (`mmsdh_quarter`, `mmsdh_quarter_maxMin`) | proved. **Weaker constant than the note's** $c_K^2$ |
| The note's constant: a $c_K$-balanced rule exists for the rank-$K$ uniform matroid (Chekuri–Vondrák–Zenklusen), so with balanced rules every user gets $\ge c_K^2$ of its planned surplus and the worst-off user $\ge c_K^2\,\theta^* \ge c_K^2\,\mathrm{OPT}_{\min}$, for $K$ at most every cap | `BalancedCRS.lean` (`exists_balanced_rule`, via Mathlib's Sion minimax theorem and `prodExp_randomWeight_gap`); `MaxMinSDH.lean` (`mmsdh_cK`, `mmsdh_cK_maxMin`) | proved. The rules exist but are not explicit: they depend on the plan's candidate probabilities, never on values or swipes |
| Counterexample: SDH's max-weight selection, with any tie-breaking, gives the worst-off user $\theta^*/3 < c_1^2\,\theta^*$ on a max-min optimal plan (3 users, caps 1) | `MaxMinCounterexample.lean` (`mmExample_maxMin`, `mmExample_sdhUtil`, `maxMin_sdh_counterexample`) | proved: the note's claim is **refuted** for SDH as defined |
| Truthfulness of MM-SDH | `TruthfulSwiping.lean` (`sdh_dsic`) | covered: `sdh_dsic` holds for every planned set of acceptable pairs, so it applies to MM-SDH's selected set unchanged |

### Query budgets in screened DH (vault note "Query Budgets in Screened DH")

The plan's query probabilities $\tau_e$ become variables, with $x_{e,s} \le \tau_e \pi_{e,s}$
(densities $y_e \le \tau_e$ for general priors) and a per-user budget on expected calls.
`BudgetedSDH.lean` has finitely many value combinations per pair; `ContinuousSDH.lean` has
any priors with finite means, continuous ones included.

| Result | File | Status |
| --- | --- | --- |
| Q(b): Q-SDH's expected calls are $\sum_e \tau_e a^\ell_e$, within budget | `BudgetedSDH.lean` (`qsdh_callsI`, `qsdh_callsJ`); `ContinuousSDH.lean` (`contCallsI_eq`, `contCallsJ_eq`) | proved |
| Q(c): every user gets $\gamma_1\gamma_2$ of its planned surplus with balanced rules; $1/4$ with random order, $c_K^2$ with $c_K$-balanced rules | `BudgetedSDH.lean` (`qsdh_quarter`, `qsdh_cK`); `ContinuousSDH.lean` (`contUtil_ge`, `contUtil_quarter`, `contUtil_cK`) | proved. Discrete: direct from the max-min theorems. Continuous: Q-SDH's utility equals MM-SDH's in a discrete surrogate market (`contUtilI_eq`, `contUtilJ_eq`, via the coarsening lemma `integral_prodExp_bern`) |
| Q(d): SDH's max-weight selection keeps $c_K^2$ of the plan's value | `BudgetedSDH.lean` (`qsdh_welfare`); `ContinuousSDH.lean` (`contSDH_welfare`, key step `rules_le_bestMatch`) | proved |
| Q(e): every budgeted screened policy induces a feasible query-aware plan with the same expected surplus for every user | `BudgetedSDH.lean` (`exists_qplan_of_policy`; adaptive query trees: `QTree.mem_run_update`, `isBudgetedPolicy_of_trees`); `ContinuousSDH.lean` (`exists_contPlan_of_policy`, via `measurePreserving_update`, `integral_mul_coord_eq`) | proved. Policies are described by the law of their (queried, matched) sets given all values (discrete) or by the chances $q_e, m_e$ of querying and matching $e$ given all values (continuous). The one property used is non-anticipation: the chance of querying $e$ does not depend on $e$'s own values. Every mixture of adaptive query trees has it |
| Q(f): for an objective $W$ that is monotone and positively homogeneous, Q-SDH on an $\varepsilon$-optimal plan gets $\gamma(W(P) - \varepsilon)$ against every budgeted policy $P$; $\gamma = 1/4$ or $c_K^2$ | `BudgetedSDH.lean` (`objective_of_perUser`, `qsdh_objective_quarter`, `qsdh_objective_cK`); `ContinuousSDH.lean` (`cont_objective_of_perUser`, `cont_objective_quarter`, `cont_objective_cK`) | proved |
| Objectives covered: max-min over any nonempty set of users, max-min of weighted (e.g. normalized) utilities, weighted welfare | `BudgetedSDH.lean` (`isMonoHom_inf'`, `isMonoHom_weightedInf`, `isMonoHom_weightedSum`) | proved |
| The query-aware plan is never worse than Theorem 3(d)'s scaling | `BudgetedSDH.lean` (`qfeasible_scaled`) | proved |
| Q(a): truthfulness | `TruthfulSwiping.lean` (`sdh_dsic`) | covered: `sdh_dsic` holds for every planned set of acceptable pairs |

## Layout

| File | Contents |
| --- | --- |
| `DatingAlgo/Basic.lean` | `cK`; `indepExp`, the expectation over independent coin flips as a finite sum |
| `DatingAlgo/IndepExp.lean` | linearity, marginals, generating function, conditioning, monotonicity in the ground set, relabelling and restricting coins, atoms |
| `DatingAlgo/TopK.lean` | weighted top-K: recursion, concavity in the cap, submodularity |
| `DatingAlgo/CorrelationGap.lean` | unweighted and weighted correlation gap; `c_K` increases, so `c_K ≥ 1 - 1/e` |
| `DatingAlgo/TwoPeriod.lean` | abstract two-period model, DH-int's program, Lemma C.5, Theorem 4.3, R2 with $1-1/e$ |
| `DatingAlgo/Submodularity.lean` | Lemma 4.1, Lemma C.2 |
| `DatingAlgo/Designs.lean` | concrete markets and designs, Thm 4.3 per design, Appendix E matroid structure |
| `DatingAlgo/Baselines.lean` | Proposition D.1 |
| `DatingAlgo/NonSubmodular.lean` | Proposition 3.4 |
| `DatingAlgo/QualityBounds.lean` | R3 |
| `DatingAlgo/QualityTopK.lean` | R4 |
| `DatingAlgo/MultiPeriodModel.lean` | shared $T$-period instance, like outcomes, DHT's initiation order (`IsDHTInit`) |
| `DatingAlgo/MultiPeriod.lean` | one-directional $T$-period model; counterexample to Theorem 5.4's proof |
| `DatingAlgo/MultiPeriodDHT.lean` | two-directional $T$-period model, relaxation (19), DHT's schedules; counterexample to Theorem 5.3 |
| `DatingAlgo/GreedyGap.lean` | one user over $T$ periods: greedy backlog responses are optimal on every sample path; their correlation gap; the splitting lemma |
| `DatingAlgo/MultiPeriodRepair.lean` | per-period relaxation $\mathrm{Rel}_\tau$, DHT-τ, and the repaired Theorem 5.3 |
| `DatingAlgo/PoissonGap.lean` | R1 and its key lemma, via the finite formula for $\mathbb E\min(\mathrm{Poi}(\mu),j)$ and its concavity; R2 with $c_K$ |
| `DatingAlgo/ProdExp.lean` | `prodExp`: expectations over independent finite random variables; pushforwards, regrouping into columns; the $c_K$ gap for random weights |
| `DatingAlgo/TruthfulSwiping.lean` | cost-separability, Theorem 1, SDH's two-period game and its DSIC property |
| `DatingAlgo/ScreenedDH.lean` | SDH's market, LP, screening and selection; Theorem 3(b)–(d) |
| `DatingAlgo/SwipeLocal.lean` | general swipe-local two-period policies: Lemma 1′, Theorem 5(a, b), the counting step of Proposition 5(b) |
| `DatingAlgo/SwipeRegret.lean` | Proposition 4 (regret and welfare identities), Impossibility 1, Proposition 6(a), Proposition 5(c), the ex-post example of T5 |
| `DatingAlgo/MatroidSwiping.lean` | weighted matroid rank; the matroid corollary of Theorem 1; SDH is DSIC for matroid users |
| `DatingAlgo/Orientation.lean` | Lemma R: balanced orientations of multigraphs, realizability in SDH's game |
| `DatingAlgo/SDHRobust.lean` | Theorem 5(e), Proposition 5(a), SDH's manipulability through oracle reports |
| `DatingAlgo/EdgeColoring.lean` | Hall's step, König's edge-coloring theorem, degree-capped subgraphs |
| `DatingAlgo/PriceOfIR.lean` | Theorem 2 and SDH against full information |
| `DatingAlgo/QueryLowerBound.lean` | adaptive reveal trees, the revealing lemma, the $G(n,n,p)$ benchmark, Theorem 4, Proposition 6(b) |
| `DatingAlgo/WorkedExample.lean` | the worked example; the continuous-values remark |
| `DatingAlgo/MatroidSDH.lean` | matroid polytope, matroid correlation gap, Theorem 3(b) for matroid users |
| `DatingAlgo/SelectionRule.lean` | selection rules, keep probabilities, balanced rules, the uniform rule |
| `DatingAlgo/UniformRule.lean` | the uniform rule is `1/2`-balanced |
| `DatingAlgo/BalancedCRS.lean` | a `c_K`-balanced rule exists (Sion's minimax theorem + the `c_K` correlation gap) |
| `DatingAlgo/MaxMinSDH.lean` | max-min SDH: the benchmark, the mechanism, the composition theorem, the `1/4` and `c_K^2` guarantees |
| `DatingAlgo/MaxMinCounterexample.lean` | SDH's own selection fails the note's max-min guarantee |
| `DatingAlgo/BudgetedSDH.lean` | query budgets, discrete priors: the query-aware plan, calls, budgeted and adaptive policies, the benchmark, monotone homogeneous objectives |
| `DatingAlgo/ContinuousSDH.lean` | query budgets for any priors with finite means: resampling and coarsening lemmas, the surrogate market, per-user and total-welfare guarantees, the benchmark, objectives |
| `DatingAlgo/LiveSet.lean` | two-cost utility, swipe trees, Theorem A (live-set characterization) and Theorem B (regret $d(\lvert M\rvert-k)^+$) for top-$k$ users |
| `DatingAlgo/Targets.lean` | open targets (none at the moment) |
| `scripts/AxiomCheck.lean` | the axiom report used by `check.sh` |

## Modeling choices

- **Abstract first stage.** The two-period model takes first-stage decisions as
  abstract. A design is any predicate on decisions, so Theorem 4.3 holds "for every
  design" literally. `Designs.lean` connects it to concrete display sets.
- **No measure theory, except for continuous priors.** All randomness is independent coin
  flips over finite sets, so expectations are finite sums (`indepExp`, `prodExp`).
  `ContinuousSDH.lean` is the exception: values have arbitrary laws (`Measure.pi`), while
  the coins given the values stay finite sums.
- **Count and quality share one theorem.** Count and quality are the same model with
  different rewards (`r2 = φ²` versus `φ² q`), so Theorem 4.3 and R2 are one theorem.
- **Bounding DHT in the counterexamples.** Both counterexamples bound DHT's responders by
  clairvoyant ones, who know their own future likes. The alternative policies' responders
  use only observable information. In `MultiPeriodDHT.lean` they are functions of the
  backlog (`backlogResp`).
- **DHT as a predicate.** `IsDHTSchedule` lists properties of Algorithm 3's schedule,
  whatever its tie-breaking, and the bound holds for every schedule with these properties.
  - Every run has them when the solution of (19) has no mutual views. That covers the
    Theorem 5.3 counterexample, where every optimal solution has none.
  - With mutual views a run can break them: Step 12 can fill a user's slot before that
    user's Steps 6–8, delaying an initiation.
  - `thm53DHTSched_isDHT` shows the predicate is satisfiable.
- **Screened DH** (`ScreenedDH.lean`, `TruthfulSwiping.lean`):
  - Pairs are `I × J`. Each pair has an independent random value combination from a finite
    type `C`; the two directions within a pair may have any joint law.
  - Users' utilities enter only through the net weights: `welfare_eq_sum_wt` shows that on
    capped sets the sum of utilities is the sum of net weights when each user's value is
    additive on sets within its cap (additive users, top-$k$ users with cap at most $k$,
    any user with cap 1).
  - The DSIC game fixes one realization of values and of SDH's coins (the planned,
    oriented matches), so the result holds for every realization. The others' period-2
    responses are arbitrary functions of what they are shown.
  - The analysis of Theorem 3(b) thins the found pairs with an extra coin per pair
    (`thinLaw`) so that candidates have exactly the plan's probabilities.
- **Truthful swiping beyond SDH** (`SwipeLocal.lean`, `SwipeRegret.lean`, `PriceOfIR.lean`,
  `QueryLowerBound.lean`):
  - A swipe-local policy is fixed period-1 displays plus a period-2 rule choosing from each
    responder's backlog, for one realization of values, oracle answers and coins.
  - Single-user results (Theorem 1, Proposition 4, Impossibility 1, Proposition 6(a)) are
    stated for every set $R$ of profiles that would match, which is how "whatever the
    others do" enters. Proposition 6(a) lets any subset of the profiles that can match
    turn out to like back.
  - Theorem 2(a) abstracts the mechanism to a distribution of the top-$k$ user's number
    of matches with non-negative expected utility; that is all the proof uses.
  - Theorem 4 describes a policy by the pairs it reveals, adaptively, by query or display
    (`RevealTree`), with matches among the revealed acceptable pairs. Users swipe
    sincerely, as in $\mathrm{OPT_{FI}}$; the class contains every real policy, so the upper
    bound covers them all.
  - Proposition 6(b) takes the period-1 pairs that can match as fixed before values are
    drawn, at most $2n$ of them, which is what Proposition 6(a) gives.
- **The repaired Theorem 5.3** (`MultiPeriodRepair.lean`) makes these modeling choices:
  - $\mathrm{Rel}_\tau$'s binary variables are encoded as a `Schedule`, and a design is any predicate on
    schedules.
  - The benchmark policies follow two rules of the paper's model:
    - each pair is shown at most one way;
    - responses never anticipate a like (`RespBlind`). Every rule that uses only the
      backlog satisfies this.
  - Without either rule, $\mathrm{Rel}_\tau$ no longer bounds OPT (examples in the vault note).
  - `exists_isOptTau` shows that the hypothesis "optimal solution of $\mathrm{Rel}_\tau$" can be met.

- **Max-min SDH** (`MaxMinSDH.lean`):
  - Utilities are additive within caps: a user's utility from a capped set is the sum of
    its surpluses. This covers additive users, and top-$k$ users with cap at most $k$.
  - The benchmark ranges over full-information policies that may randomize. Their
    floor is compared user by user, so a policy that is good on average but bad for
    one user doesn't count.
  - A selection rule (`IsRule`) sees only its own candidate set and its own coins. That
    keeps the policy swipe-local and makes different users' selections independent,
    which the composition proof needs.

- **Query budgets** (`BudgetedSDH.lean`, `ContinuousSDH.lean`):
  - Calls are charged as in `ScreenedDH.lean`: the side less likely to accept is asked
    first, the other side only after a yes. Budgets bound expected calls.
  - Budgeted policies are described by what the proof needs: the law of the queried and
    matched sets (discrete) or their marginals $q_e, m_e$ (continuous), given all values.
    This class contains every adaptive policy, so the benchmark bound covers them all.
  - Continuous priors are laws on $\mathbb R^2$ with finite means. Given the values, Q-SDH's
    candidates are independent coins with probability $y_e(s)$; the query coin
    (probability $\tau_e$) only enters the calls. SDH's value (`contSDHValue`) uses the
    found pairs, found with probability $\tau_e\,\mathbb 1[\text{acceptable}]$.
  - The objective theorems compare $W$ of expected utilities (ex ante), and need an
    $\varepsilon$-optimal plan, which always exists; no optimal continuous plan is assumed.

## Conventions

- **Stating vs. proving.** New results start as statements closed with `sorry`, in
  the file where they belong or in `Targets.lean`.
- **Faithful statements first.** A precisely stated open target is useful; a proved
  theorem that says the wrong thing is harmful. Each docstring says which result it
  formalizes. Two statement bugs caught during this work show why:
  - a Mathlib API change made a pair condition vacuous;
  - an undeclared variable passed `lake env lean` but not `lake build`.
- **Pinned versions.** `lean-toolchain` and the Mathlib `rev` in `lakefile.toml` are
  pinned to the same release (`v4.35.0`). Bump them together, run
  `lake update && lean/check.sh`, and commit `lake-manifest.json`.
- `import Mathlib` triggers a harmless warning about Lean's new module system.
