# Lean proofs

Machine-checked versions of Rios & Torrico's dating-heuristic results and of the
project's own match-quality and truthful-swiping results, in Lean 4 with Mathlib.
- The math is in the vault notes `vault/sources/Rios 2026 - The Dating Heuristic.md`,
  `vault/notes/Match Quality in the Dating Heuristic Framework.md` and
  `vault/notes/Truthful Swiping with an LLM Oracle.md`.
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

Current count: 539 theorems, all fully proved. The count includes lemmas Lean generates
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
| Theorem 1 corollaries: additive always; top-$k$ iff at most $k$ acceptable | `TruthfulSwiping.lean` (`costSeparable_sum`, `costSeparable_topK_iff`) | proved; the matroid corollary is not formalized |
| Lemma 1′ for SDH: whatever a user does, its matches are $D \cap R$ with $R$ independent of its swipes | `TruthfulSwiping.lean` (`matchesOf_update`) | proved for SDH's two-period game; not for general swipe-local policies |
| Theorems 3(a), 5(a): SDH is DSIC | `TruthfulSwiping.lean` (`sdh_dsic`, `sdh_dsic_topK`) | proved: against every behavior of the others, including strategies that react to what they see, for every realization of values and coins. For top-$k$ it needs only at most $k$ planned partners |
| Theorem 5(d): a sincere user's utility is at least 0 | `TruthfulSwiping.lean` (`sdh_sincere_nonneg`) | proved |
| Theorem 5(e), its key step: a planned pair with two sincere ends matches | `TruthfulSwiping.lean` (`sdh_arc_matches`) | proved; the welfare sum over pairs is not formalized |
| Theorem 3(b), first step: the LP bounds $\mathrm{OPT_{IR}}$, and has an optimal plan | `ScreenedDH.lean` (`exists_lpValue_eq_optIR`, `optIR_le_lpValue`, `exists_isLPOptimal`) | proved |
| Theorem 3(b): SDH $\ge c_K^2\,\mathrm{LP} \ge c_K^2\,\mathrm{OPT_{IR}}$ for size caps, $K$ at most every cap | `ScreenedDH.lean` (`lpValue_le_sdhValue`, `sdh_welfare`) | proved, for every feasible plan and every query probabilities with $x_{e,c} \le \tau_e \pi_{e,c}$. The matroid case, $(1-1/e)^2$, is not formalized |
| The $c_K$ gap for independent random weights (layer cake + R1's lemma) | `ProdExp.lean` (`prodExp_randomWeight_gap`, `prodExp_columns_gap`) | proved |
| Welfare on IR sets is the sum of net weights | `ScreenedDH.lean` (`welfare_eq_sum_wt`) | proved |
| Theorem 3(c): $\tau_e \le x_e/\hat p_e$, calls per user $\le b'_\ell/\hat p$, a queried pair costs $\le 1 + \sqrt{\phi_I \phi_J}$ calls | `ScreenedDH.lean` (`sdhTau_le`, `sum_callsI_le`, `sum_callsJ_le`, `callsI_add_callsJ`) | proved for **corrected** statements: the plan splits a tied bar level proportionally, and $\hat p_e$ is the mass strictly above the bar if positive, else at the bar. The note's version (ties filled in any order) is false |
| Bar shape is without loss of generality | `ScreenedDH.lean` (`exists_barShaped`, `exists_optimal_barShaped`) | proved |
| Theorem 3(d): scaling the plan by $\lambda$ scales calls by $\lambda$ and keeps $c_K^2 \lambda\,\mathrm{OPT_{IR}}$ | `ScreenedDH.lean` (`sdh_budget`, `sum_callsI_budget`) | proved |
| Lemma R, Theorems 2 and 4, Propositions 4–6, continuous values | — | not formalized |

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
| `DatingAlgo/Targets.lean` | open targets (none at the moment) |
| `scripts/AxiomCheck.lean` | the axiom report used by `check.sh` |

## Modeling choices

- **Abstract first stage.** The two-period model takes first-stage decisions as
  abstract. A design is any predicate on decisions, so Theorem 4.3 holds "for every
  design" literally. `Designs.lean` connects it to concrete display sets.
- **No measure theory.** All randomness is independent coin flips over finite sets, so
  expectations are finite sums (`indepExp`).
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
- **The repaired Theorem 5.3** (`MultiPeriodRepair.lean`) makes these modeling choices:
  - $\mathrm{Rel}_\tau$'s binary variables are encoded as a `Schedule`, and a design is any predicate on
    schedules.
  - The benchmark policies follow two rules of the paper's model:
    - each pair is shown at most one way;
    - responses never anticipate a like (`RespBlind`). Every rule that uses only the
      backlog satisfies this.
  - Without either rule, $\mathrm{Rel}_\tau$ no longer bounds OPT (examples in the vault note).
  - `exists_isOptTau` shows that the hypothesis "optimal solution of $\mathrm{Rel}_\tau$" can be met.

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
