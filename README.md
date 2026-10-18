# cs580-agt-dating-algo

Shared workspace for a CS 580 (algorithmic game theory) project on dating /
matching algorithms.

```
.
├── CLAUDE.md          # instructions for Claude Code (shared with the team)
├── notes/             # markdown notes, reading notes, drafts, outlines
├── data/              # datasets, scripts (data/scripts/), figures (data/figures/)
├── sources/           # PDFs of cited/referenced papers (tracked in git)
└── check_latex_deps.sh
```

The LaTeX writeup (`paper/`) and its Overleaf sync are not set up yet.

## Getting started

```bash
git clone <repo-url> cs580-agt-dating-algo
cd cs580-agt-dating-algo
```

Always `git pull --rebase` before starting work, and keep commits small.

## Adding papers

Drop PDFs into `sources/`, named by citation key: `lastnameYEARkeyword.pdf`
(e.g. `gale1962college.pdf`). Optional reading notes go in
`notes/papers/<citation-key>.md`. Keep files under 50 MB (GitHub's hard
limit is 100 MB).

## LaTeX tooling

Check for missing LaTeX packages (report only, or install with `tlmgr`):

```bash
./check_latex_deps.sh
./check_latex_deps.sh --install
```

`.vscode/settings.json` sets up the LaTeX Workshop extension to build with
`latexmk` on save.
