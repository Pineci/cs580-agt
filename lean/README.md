# Lean proofs

Machine-checked versions of Rios & Torrico's dating-heuristic results and of the
project's own match-quality results, in Lean 4 with Mathlib.
- The math is in the vault notes `vault/sources/Rios 2026 - The Dating Heuristic.md` and
  `vault/notes/Match Quality in the Dating Heuristic Framework.md`.
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

Current count: 411 theorems, all fully proved. The count includes lemmas Lean generates
for definitions and structures, such as the fields of `Feasible19`.

### Rios & Torrico's results

| Paper result | File | Status |
| --- | --- | --- |
| **Theorem 4.3**: DH-int is a $(1-1/e)$-approximation (two periods, every design) | `TwoPeriod.lean` (`dhInt_approx`), `Designs.lean` (`dhInt_approx_market`) | proved |
| Correlation-gap step of Thm 4.3 (Agrawal et al. 2010, for weighted top-K) | `CorrelationGap.lean` (`topK_correlation_gap`) | proved from scratch |
| Lemma C.5 (DH-int's program bounds OPT) | `TwoPeriod.lean` | proved |
| Lemma 4.1 (`f` monotone submodular) | `TopK.lean`, `Submodularity.lean` | proved |
| Lemma C.2 (`M²` monotone submodular) | `Submodularity.lean` | proved |
| Proposition 3.4 (`f` not submodular with period-2 mutual views) | `NonSubmodular.lean` | proved (smaller instance than the paper's) |
| Proposition D.1 (local greedy can be $O(1/n)$-bad) | `Baselines.lean` | proved |
| Lemma E.5, §E.1 (designs as partition matroids) | `Designs.lean` | proved |
| **Theorem 5.4** ($T$ periods, one-directional) | `MultiPeriod.lean` | **refuted**: proved counterexample, ratio 0.50 < 0.632 |
| **Theorem 5.3** ($T$ periods, DHT) | `MultiPeriodDHT.lean` (`theorem_5_3_counterexample`) | **refuted**: proved counterexample, ratio 0.52 < 0.632. It covers every optimal solution of (19), both two-directional designs, and clairvoyant responders |
| Theorem 5.3, **repaired** (vault note, per-period repair): per-period relaxation $\mathrm{Rel}_\tau$, DHT-τ shows initiations in $\mathrm{Rel}_\tau$'s periods, $\text{DHT-}\tau \ge (1-1/e)\,\mathrm{Rel}_\tau \ge (1-1/e)\,\mathrm{OPT}$ | `MultiPeriodRepair.lean` (`theorem_5_3_repair`, `dhtTau_approx`) | proved, for every design, every optimal solution of $\mathrm{Rel}_\tau$ and every tie-breaking. OPT is the best semi-adaptive policy with non-anticipating responses |
| Correlation gap for greedy $T$-period backlog responses (one user; replaces the laminar-matroid gap) | `GreedyGap.lean` (`greedy_correlation_gap`, `greedy_optimal`) | proved |
| Lemmas C.3, C.4 | — | not needed: our direct correlation-gap proof replaces them |
| Thm 4.4, Props E.1/E.6/E.10/E.12 | — | not formalized: they apply cited algorithms (continuous greedy, local search, dependent rounding) to the structure above |
| Lemma E.9, E.11; Thm E.13; Prop D.2; Lemma 5.2, F.2; Prop B.2; Lemma B.1 | — | not formalized |

### Match-quality results (vault note)

| Result | File | Status |
| --- | --- | --- |
| R1: sharper constant $c_K$ for DH-int | `PoissonGap.lean` (`dhInt_approx_cK`) | proved |
| R1 key lemma: $\mathbb E\min(X,K)\ge c_K\min(\mu,K)$ | `PoissonGap.lean` (`poissonBinomial_min_ge`) | proved: finite comparison with $\mathbb E\min(\mathrm{Poi}(\mu),K)$, no measure theory |
| $c_K \ge 1-1/e$ | `CorrelationGap.lean` | proved |
| R2: quality-weighted DH-int keeps $1-1/e$ | `TwoPeriod.lean` (`dhInt_quality_approx`) | proved |
| R3: no quality guarantee for DH-int as written; trade-off; mixing | `QualityBounds.lean` | proved |
| R4: additive optimum loses $(K+1)/2$ in best-match quality ($k=1$) | `QualityTopK.lean` | proved |
| R5: top-1 algorithm | — | open mathematically |

## Layout

| File | Contents |
| --- | --- |
| `DatingAlgo/Basic.lean` | `cK`; `indepExp`, the expectation over independent coin flips as a finite sum |
| `DatingAlgo/IndepExp.lean` | linearity, marginals, generating function, conditioning, monotonicity in the ground set |
| `DatingAlgo/TopK.lean` | weighted top-K: recursion, concavity in the cap, submodularity |
| `DatingAlgo/CorrelationGap.lean` | unweighted and weighted correlation gap, `c_K ≥ 1 - 1/e` |
| `DatingAlgo/TwoPeriod.lean` | abstract two-period model, DH-int's program, Lemma C.5, Theorem 4.3, R2 |
| `DatingAlgo/Submodularity.lean` | Lemma 4.1, Lemma C.2 |
| `DatingAlgo/Designs.lean` | concrete markets and designs, Thm 4.3 per design, Appendix E matroid structure |
| `DatingAlgo/Baselines.lean` | Proposition D.1 |
| `DatingAlgo/NonSubmodular.lean` | Proposition 3.4 |
| `DatingAlgo/QualityBounds.lean` | R3 |
| `DatingAlgo/QualityTopK.lean` | R4 |
| `DatingAlgo/MultiPeriod.lean` | one-directional $T$-period model; counterexample to Theorem 5.4 |
| `DatingAlgo/MultiPeriodDHT.lean` | two-directional $T$-period model, relaxation (19), DHT's schedules; counterexample to Theorem 5.3 |
| `DatingAlgo/GreedyGap.lean` | one user over $T$ periods: greedy backlog responses are optimal on every sample path; their correlation gap; the splitting lemma |
| `DatingAlgo/MultiPeriodRepair.lean` | per-period relaxation $\mathrm{Rel}_\tau$, DHT-τ, and the repaired Theorem 5.3 |
| `DatingAlgo/PoissonGap.lean` | R1 and its key lemma, via the finite formula for $\mathbb E\min(\mathrm{Poi}(\mu),j)$ and its concavity |
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
- **DHT as a predicate.** `IsDHTSchedule` lists properties that every run of Algorithm 3
  has, whatever its tie-breaking. The bound holds for every schedule with these properties.
  `thm53DHTSched_isDHT` shows the predicate is satisfiable.
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
