# Second-brain vault

This directory is an Obsidian vault used as the shared knowledge base for the CS 580 dating-algorithm project. You (Claude) help ingest sources, maintain notes, and answer questions from it. Obsidian is the viewer; plain Markdown files are the source of truth. Always work from the vault root.

## Project context

- **Parent instructions also apply.** `../CLAUDE.md` covers the whole project repo: git rules (pull before editing, never push or commit without asking), the LaTeX paper, and `../data/`. Its change-marking and `\citep`/`\citet` rules are for LaTeX only; notes here follow this file.
- **Git.** The vault is versioned by the project repo one level up. Never run `git init` here. Pull before an ingest or cleanup and offer to commit after (one ingest per commit): `index.md` and `log.md` change on every ingest and conflict when collaborators work from stale copies. `../.gitattributes` makes git keep both sides' lines in `log.md`, `index.md`, and `journal/` notes instead of stopping on a conflict; after pulling such a merge, fix duplicate frontmatter keys (keep the latest `updated:`) and duplicate index lines.
- **Shared, not personal.** "The user" means whichever collaborator is asking. `origin: human` protects any collaborator's writing, not just the current user's.
- **Papers.** `citekey` follows `lastnameYEARkeyword` (e.g. `gale1962college`), matching the LaTeX bibliography. When ingest moves a paper's PDF into `sources/_raw/`, name it `<citekey>.pdf`. Flag any file over 50 MB instead of adding it (GitHub's hard limit is 100 MB).

## Layout

| Folder | Holds | Who writes |
| --- | --- | --- |
| `inbox/` | Unprocessed drops: clippings, PDFs, pasted text, quick captures | User, capture workflow |
| `sources/` | One note per ingested source (article, paper, book, talk, transcript) | Ingest workflow |
| `sources/_raw/` | Original files after ingest. Immutable — never edit | Ingest workflow (move only) |
| `notes/` | Atomic notes: concepts, people, questions, syntheses | Both |
| `maps/` | Maps of content (MOCs): curated hub notes per topic | Both |
| `journal/` | Daily notes `YYYY-MM-DD.md` and weekly reviews `YYYY-Www Review.md` | Both |
| `attachments/` | Images and other embedded files | Both |
| `templates/` | Note templates (also used by Obsidian's Templates plugin) | User |
| `_archive/` | Retired notes. Nothing is ever deleted; it is moved here | Workflows |
| `_claude/` | Workflow instructions and the helper script. Not notes: never index, link, or lint them | User |
| `index.md` | Catalog of every note with a one-line summary, grouped by map | Workflows |
| `log.md` | Append-only record of every ingest, cleanup, and filed answer | Workflows |

## Note format

Every note outside `inbox/`, `sources/_raw/`, and `templates/` starts with YAML frontmatter:

```yaml
---
type: concept        # concept | source | person | question | synthesis | map | project | daily | review
created: 2026-01-31
updated: 2026-01-31
tags: [topic/subtopic]
aliases: []
sources: []          # wikilinks to source notes this note draws on, e.g. ["[[Smith 2024 - Title]]"]
origin: claude       # human | claude | mixed
status: seed         # seed | growing | evergreen
---
```

Source notes add `source_type` (article | paper | book | video | podcast | transcript | other), `title`, `authors`, `year`, `url`, `raw` (wikilink to the original in `sources/_raw/`, if any), and for papers `venue` and `citekey`. Templates for each type are in `templates/`.

## Workflows

Detailed procedures live in `_claude/workflows/`. When a request matches a row below, read that file in full **before doing anything else** and follow it. Users won't name the workflow; match on intent.

| When the user wants to… | Read |
| --- | --- |
| Add, file, clip, process, or digest material (an article, paper, PDF, URL, transcript, pasted text) or process the inbox | `_claude/workflows/ingest.md` |
| Know what their notes say, what they've read about something, or get a comparison or synthesis across notes | `_claude/workflows/query.md` |
| Jot down, note, or capture a quick thought, task, link, or quote | `_claude/workflows/capture.md` |
| Link up a note, find related notes, or weave in a note they wrote | `_claude/workflows/connect.md` |
| Explicitly asks for a vault cleanup, tidy-up, or health check | `_claude/workflows/cleanup.md` |
| Explicitly asks for a weekly (or periodic) review | `_claude/workflows/review.md` |

Cleanup and review change many files, so start them only on an explicit request, never as a side effect of another task. Mention the matching workflow if one would help but wasn't asked for.

## Rules

- **Filenames are titles.** Human-readable, Title Case, spaces allowed. No `/ \ : * ? " < > | # ^ [ ]`. Source notes are named `Author Year - Short Title`.
- **Link with wikilinks** `[[Note Title]]`, `[[Note Title#Heading]]`, `[[Note Title|display text]]`. Never use Markdown links for internal notes.
- **Before creating a note, check it doesn't exist** under another name: search filenames and `aliases:` lines. Prefer extending an existing note to creating a near-duplicate.
- **Atomic notes.** One idea per note in `notes/`; a note that grows past ~1,500 words or covers several ideas is a split candidate.
- **Cite.** Claims in concept notes that come from a source link the source note inline, and the source goes in `sources:`.
- **Respect human writing.** In notes with `origin: human` (or no `origin` field, which means the same), don't rewrite prose. You may fix frontmatter, links, and typos, and you may append clearly marked sections. Set `origin: mixed` after substantive additions.
- **Never delete.** Retire notes with `python3 _claude/vault_tool.py archive "<Note>"`.
- **Never rename or move a note by hand.** Obsidian only updates links when *it* renames a file. Use `python3 _claude/vault_tool.py rename "<Old>" "<New>"`, which rewrites every link.
- **Bump `updated:`** whenever you change a note.
- **Math** uses Obsidian's MathJax: `$inline$` and `$$display$$`.
- **Conflicts** between sources are recorded, not resolved silently:
  `> [!warning] Conflict` callout naming both sources.
- **Log** every operation that changes the vault by appending to `log.md`:
  `## [YYYY-MM-DD] <operation> | <subject>` followed by a short bullet list of notes created or changed.

## Helper script

`python3 _claude/vault_tool.py <command>` (stdlib only, finds the vault root itself):

- `status`: date, inbox contents, note counts, git state, recent log entries
- `lint [--json] [--all] [--path PREFIX]`: broken links, orphans, frontmatter problems, near-duplicates, tag variants, stubs, oversized notes
- `backlinks "<Note>"`: every link pointing at a note
- `mentions "<Note>"`: unlinked plain-text mentions of a note's title or aliases
- `rename "<Old>" "<New>" [--dry-run]`: rename or move a note and rewrite all links to it
- `retarget "<Old>" "<New>" [--keep-display] [--dry-run]`: point links at a different note (fixes broken links, finishes merges)
- `archive "<Note>" [--force]`: move a note to `_archive/` (refuses if links still point at it, unless forced)
