# Lean proofs

Machine-checked versions of the project's results, in Lean 4 with Mathlib. The math
these files formalize is in the vault note
`vault/notes/Match Quality in the Dating Heuristic Framework.md`.

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
lean/check.sh            # build, then list open targets
lean/check.sh --strict   # also fail unless everything is fully proved
```

`check.sh` runs `lake build`, then `scripts/AxiomCheck.lean`. That script asks Lean
which axioms every declaration depends on and reports:
- **open targets:** theorems in `DatingAlgo/Targets.lean`, still closed with `sorry`;
- **leaks:** any declaration *outside* `Targets.lean` that depends on `sorry`, even
  indirectly, for example by using an open target;
- **non-standard axioms:** anything beyond `propext`, `Classical.choice` and `Quot.sound`.

A file can look finished and still rely on an open target. That's why the check uses
axioms rather than grepping for `sorry`.

## Layout

| File | Contents |
| --- | --- |
| `DatingAlgo/Basic.lean` | `cK k = 1 - e^{-k} k^k / k!`; `indepExp`, the expectation over independent coin flips, done as a finite sum with no measure theory |
| `DatingAlgo/QualityBounds.lean` | R3: the quality guarantee from a bounded quality range, the count–quality trade-off instance, and the mixing guarantee |
| `DatingAlgo/TopK.lean` | weighted top-K, the period-2 value of a responder: monotone, non-negative, and equal to the plain sum when the backlog fits |
| `DatingAlgo/Targets.lean` | open targets, stated with `sorry` |
| `scripts/AxiomCheck.lean` | the axiom report used by `check.sh` |

## Conventions

- **Stating vs. proving.** New results go into `Targets.lean` as a statement closed
  with `sorry`. Once proved, move the theorem to the file where it belongs.
  `check.sh` must then report no leaks.
- **Faithful statements first.** A precisely stated open target is useful; a proved
  theorem that says the wrong thing is harmful. Each docstring should say which
  result in the vault note it formalizes.
- **Pinned versions.** `lean-toolchain` and the Mathlib `rev` in `lakefile.toml` are
  pinned to the same release (`v4.35.0`). Bump them together, run
  `lake update && lean/check.sh`, and commit `lake-manifest.json`.
- `import Mathlib` triggers a harmless warning about Lean's new module system.

## Status

| Result (vault note) | Lean status | Difficulty to finish |
| --- | --- | --- |
| R3: bounded quality range, trade-off instance, mixing | proved | done |
| `topK` basic facts (monotone, fits-in-cap) | proved | done |
| Paper's Lemma 4.1 (top-K submodular) | target | moderate: finite combinatorics |
| R1 key lemma: $\mathbb E\min(X,K)\ge c_K\min(\mu,K)$ | target | hard: needs a Poisson / convex-order argument; Mathlib's binomial and Poisson support helps |
| R1/R2: weighted correlation gap for top-K | target | moderate once the key lemma is proved (layer-cake) |
| Paper's Theorem 4.3 and R2 end to end | not stated yet | hard: needs a model of policies and the two-period dynamics |
| R4: additive-optimal can lose $2k/(K+k)$ | not stated yet | moderate: a concrete instance |
| R5: top-1 algorithm | open mathematically | research |
