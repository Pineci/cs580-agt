# CS 580 AGT dating-algorithm project — workspace

This directory is the shared workspace for a CS 580 (algorithmic game theory)
project on dating / matching algorithms. It is a single git repo shared with
collaborators — anything committed here is visible to the whole team.

<!-- TODO: replace with a one-paragraph description of the project question. -->

## Directory layout

- `notes/` — markdown notes, reading notes, drafts, outlines.
- `data/` — datasets, analysis scripts, generated figures.
  - Scripts go in `data/scripts/`, outputs in `data/figures/`.
- `sources/` — PDFs of cited/referenced papers. **Tracked in git** so the
  whole team shares them.
- `paper/` — **not set up yet.** The LaTeX writeup and how it syncs with
  Overleaf is still being decided (Overleaf's GitHub sync mirrors a whole
  repo, so `paper/` will likely end up as its own repo). Don't create
  `paper/` or a LaTeX template without asking.

## Working in a shared repo

- **Pull before editing.** Run `git pull --rebase` before making changes —
  collaborators may have pushed since the last session.
- **Don't `git push` without asking.** Show the diff first and wait for approval.
- **Don't commit on someone's behalf without asking**, and keep commits
  scoped to one change so collaborators can review them.
- Don't delete or rename files other people added (notes, sources, data)
  without asking.

## Adding papers to `sources/`

- Name PDFs by their citation key: `lastnameYEARkeyword.pdf`
  (e.g. `gale1962college.pdf`), so the file matches its BibTeX entry.
- When a paper is added, a short reading note can go in
  `notes/papers/<citation-key>.md`.
- GitHub rejects files over 100 MB and warns above 50 MB — flag any PDF
  that large instead of committing it.

## Using the local database

- For citation grounding: check `sources/` for relevant PDFs and `notes/`
  for reading notes before web-searching.
- For figures: write generation scripts to `data/scripts/`, outputs to
  `data/figures/`; copy a final figure into the paper only when it's ready.

## Marking changes for review (LaTeX)

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

## Citation style

- **Use `\citep{key}` for parenthetical citations** (default).
- **Use `\citet{key}` for inline/textual citations** (e.g., "As \citet{key} shows...").
- **Never use bare `\cite{key}`.** Flag any I encounter and offer to convert.
- Citation keys follow `lastnameYEARkeyword` style (e.g., `gale1962college`).
  Match this when adding new entries.

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
- Don't reformat or rewrap existing paragraphs — only change what's needed.
- Don't restructure sections (reorder, rename, split, merge).
- Don't replace macros in a preamble or add new packages.

## Notes & caveats

- This folder lives in iCloud Drive. If git reports odd errors, check for
  iCloud "conflicted copy" / `file 2` duplicates inside `.git/` before
  doing anything destructive.
- Claude can occasionally ignore project memory. If I drift from these rules
  (especially the change-marking or pull-before-edit), call it out and I'll
  re-anchor.
