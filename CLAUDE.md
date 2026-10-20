# CS 580 AGT dating-algorithm project — workspace

This directory is the shared workspace for a CS 580 (algorithmic game theory)
project on dating / matching algorithms. It is a single git repo shared with
collaborators — anything committed here is visible to the whole team.

<!-- TODO: replace with a one-paragraph description of the project question. -->

## Directory layout

- `vault/` — Obsidian vault: the project's knowledge base. Papers (PDFs plus
  one source note each), reading notes, concept notes, maps, daily notes.
  **`vault/CLAUDE.md` governs everything inside `vault/`** — layout,
  frontmatter, linking, and the ingest / query / capture / connect /
  cleanup / review workflows.
- `data/` — datasets, analysis scripts, generated figures.
  - Scripts go in `data/scripts/`, outputs in `data/figures/`.
- `lean/` — Lean 4 + Mathlib formalization of the project's results. See
  "Lean proofs" below and `lean/README.md`.
- `paper/` — **not set up yet.** The LaTeX writeup and how it syncs with
  Overleaf is still being decided (Overleaf's GitHub sync mirrors a whole
  repo, so `paper/` will likely end up as its own repo). Don't create
  `paper/` or a LaTeX template without asking.

There is no `notes/` or `sources/` at the repo root: notes and papers live
in the vault.

## Working with the vault

- Paths in `vault/CLAUDE.md` and `vault/_claude/workflows/` are relative to
  `vault/`. For vault work (ingesting papers, querying notes), start Claude
  Code in `vault/` so those paths and `python3 _claude/vault_tool.py` work
  as written. From the repo root, prefix them with `vault/`
  (e.g. `python3 vault/_claude/vault_tool.py status`).
- When asked to add, ingest, or look up papers or notes — from either
  directory — follow `vault/CLAUDE.md` and the matching workflow.

## Working in a shared repo

- **Pull before editing.** Run `git pull --rebase` before making changes —
  collaborators may have pushed since the last session. This includes vault
  work: `vault/index.md` and `vault/log.md` change on every ingest, so a
  stale copy conflicts.
- **Don't `git push` without asking.** Show the diff first and wait for approval.
- **Don't commit on someone's behalf without asking**, and keep commits
  scoped to one change (e.g. one ingest per commit) so collaborators can
  review them. After an ingest, offer to commit so others get it promptly.
- Don't delete or rename files other people added without asking. Vault
  operations that follow `vault/CLAUDE.md` are fine when requested: ingest
  moving `vault/inbox/` items into `vault/sources/_raw/`, and renames or
  archives done with `vault/_claude/vault_tool.py`.
- **Never run `git init` inside `vault/`** (or any other subfolder). The
  vault is already tracked by this repo; a nested repo would break it for
  everyone.

## Adding papers

- Drop PDFs into `vault/inbox/` and ask Claude to ingest them (the vault's
  ingest workflow). Ingest writes a source note in `vault/sources/` named
  `Author Year - Short Title` and moves the PDF into `vault/sources/_raw/`.
- Paper citekeys follow `lastnameYEARkeyword` (e.g. `gale1962college`) — the
  same key the LaTeX `.bib` will use. The source note's `citekey:` field
  holds it, and the raw PDF is renamed to `<citekey>.pdf`.
- GitHub rejects files over 100 MB and warns above 50 MB — flag any PDF
  that large instead of committing it.

## Using the knowledge base

- For citation grounding or background: search the vault before
  web-searching. Start from `vault/index.md`, then `vault/sources/` and
  `vault/notes/` (the vault's query workflow). Raw PDFs are in
  `vault/sources/_raw/`.
- For figures: write generation scripts to `data/scripts/`, outputs to
  `data/figures/`; copy a final figure into the paper only when it's ready.

## Lean proofs

- **Setup and checking.** `./setup_lean.sh` sets everything up once.
  `lean/check.sh` builds the project and reports open results, results that
  depend on open ones, and non-standard axioms. Run it after every Lean
  change, and report its summary rather than claiming a result is "proved".
- **Single files.** `lake env lean File.lean` ignores the lakefile's
  `autoImplicit := false`. Check single files with
  `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false File.lean`;
  `lake build` is the ground truth. Parallel provers must not run
  `lake build` at the same time.
- **Workflow.** New results start as statements closed with `sorry`, in the
  file where they belong or in `lean/DatingAlgo/Targets.lean`. The status
  table in `lean/README.md` records what is proved, open, or refuted.
- **Faithfulness.** Statements must match the math in the vault, especially
  `vault/notes/Match Quality in the Dating Heuristic Framework.md`. Docstrings
  name the result they formalize. Never weaken a statement just to make it
  provable without saying so.
- **Versions and size.** Don't bump the pinned Lean/Mathlib versions without
  asking. `lean/.lake` (about 7 GB) is a symlink to the iCloud-excluded
  `lean/.lake.nosync`; never commit either.

## Marking changes for review (LaTeX)

These rules apply to LaTeX files (the future `paper/`). Vault notes follow
`vault/CLAUDE.md` instead (`origin:` field, "respect human writing").

Any text changes I make to LaTeX files will be **marked** so they can be
reviewed — this matters more with several co-authors editing the same text:

- **Adding or changing text:** wrap in red, e.g.
  `\textcolor{red}{new or rewritten text}`.
- **Removing text:** strike through instead of deleting, e.g.
  `\sout{the old text}`. This requires `\usepackage[normalem]{ulem}` in
  the preamble — if it isn't there yet, add it before using `\sout`.
- For convenience, I may define and use these macros (add to preamble if missing):
  ```latex
  \usepackage[normalem]{ulem}
  \newcommand{\new}[1]{\textcolor{red}{#1}}
  \newcommand{\old}[1]{\sout{#1}}
  ```
  Then mark changes as `\new{...}` and `\old{...}`.
- Once changes are reviewed and accepted, I can do a cleanup pass to unwrap
  `\new{}` and delete `\old{}` content — but **only when explicitly asked**.
- This applies to prose. Pure-math edits inside `equation`/`align` environments
  are harder to color cleanly; for those, I'll show the diff in chat and
  hold off on the in-file mark unless told to apply it.

## Citation style (LaTeX)

- **Use `\citep{key}` for parenthetical citations** (default).
- **Use `\citet{key}` for inline/textual citations** (e.g., "As \citet{key} shows...").
- **Never use bare `\cite{key}`.** Flag any I encounter and offer to convert.
- Citation keys follow `lastnameYEARkeyword` style (e.g., `gale1962college`).
  Match this when adding new entries, and reuse the `citekey:` from the
  paper's vault source note when one exists.
- In the vault, sources are cited with wikilinks per `vault/CLAUDE.md`.

## LaTeX tooling

- Toolchain: MacTeX provides `latexmk`, `pdflatex`, BibTeX.
- `./check_latex_deps.sh` reports LaTeX packages used by any `.tex` file in
  the repo that aren't installed; `--install` installs them via `tlmgr`
  (asks for an admin password — the user runs that, not me).
- `.vscode/settings.json` configures LaTeX Workshop to build with `latexmk`
  on save.
- Build artifacts (`.aux`, `.bbl`, `.log`, etc.) are gitignored.

## What NOT to do without asking

- Don't `git push`.
- In LaTeX files:
  - Don't reformat or rewrap existing paragraphs — only change what's needed.
  - Don't restructure sections (reorder, rename, split, merge).
  - Don't replace macros in a preamble or add new packages.
- Vault restructuring (merges, splits, renames, archiving) goes through the
  vault's cleanup workflow, which proposes a plan and waits for approval.

## Notes & caveats

- This folder lives in iCloud Drive. If git reports odd errors, check for
  iCloud "conflicted copy" / `file 2` duplicates inside `.git/` before
  doing anything destructive.
- Claude can occasionally ignore project memory. If I drift from these rules
  (especially the change-marking or pull-before-edit), call it out and I'll
  re-anchor.
