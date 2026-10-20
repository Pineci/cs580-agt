# cs580-agt-dating-algo

Shared workspace for a CS 580 (algorithmic game theory) project on dating /
matching algorithms.

```
.
├── CLAUDE.md          # instructions for Claude Code (shared with the team)
├── vault/             # Obsidian vault: papers, reading notes, concepts (own CLAUDE.md)
├── data/              # datasets, scripts (data/scripts/), figures (data/figures/)
├── lean/              # Lean 4 + Mathlib proofs of the project's results (own README)
├── setup_lean.sh      # one-time Lean setup
└── check_latex_deps.sh
```

The LaTeX writeup (`paper/`) and its Overleaf sync are not set up yet.
See `vault/README.md` for opening the vault in Obsidian.

## Getting started

```bash
git clone <repo-url> cs580-agt-dating-algo
cd cs580-agt-dating-algo
```

Always `git pull --rebase` before starting work, and keep commits small.

## Adding papers

Drop PDFs into `vault/inbox/` and ask Claude (started in `vault/`) to ingest
them. Each paper gets a source note in `vault/sources/`, and its PDF moves to
`vault/sources/_raw/<citekey>.pdf`, with citekeys like `gale1962college`.
Keep files under 50 MB (GitHub's hard limit is 100 MB).

## Lean proofs

The project's proofs are checked in Lean 4 with Mathlib. One-time setup installs
Lean and downloads about 7 GB:

```bash
./setup_lean.sh
```

Then `lean/check.sh` rebuilds and lists which results are fully proved. Details are
in `lean/README.md`.

## LaTeX tooling

Check for missing LaTeX packages (report only, or install with `tlmgr`):

```bash
./check_latex_deps.sh
./check_latex_deps.sh --install
```

`.vscode/settings.json` sets up the LaTeX Workshop extension to build with
`latexmk` on save.
