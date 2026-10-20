# Weekly review

*Weekly review of the Obsidian second-brain vault — what was added and changed, daily-note captures to promote into real notes, open tasks and questions, inbox backlog, emerging themes, and suggested next reads. Writes a review note to the journal.*

Period: the last 7 days unless the user gave another span.

Run `python3 _claude/vault_tool.py status` first; it gives today's date and ISO week.

The point of a review is to turn a week of scattered captures and ingests into a few decisions: what to promote, what to read next, what questions are open. Keep it skimmable.

## Gather

1. **Activity:** the `log.md` entries in the period. If it's a git repo, cross-check with `git log --since="<N> days ago" --stat` to catch hand edits that weren't logged.
2. **Captures:** the `## Captures` sections of daily notes in `journal/` for the period. Sort them into: worth promoting to a note, worth ingesting (links), tasks, and done or noise.
3. **Open loops:** unchecked `- [ ]` tasks, `> [!question]` callouts, `type: question` notes, and `status: seed` notes touched this period.
4. **Inbox:** items waiting, with age.
5. **Themes:** look across the period's new notes and captures for recurring ideas or a cluster that has no map yet, and connections between this week's material and older notes (run `vault_tool.py mentions` on the week's new notes).
6. **Health:** the summary counts from `vault_tool.py lint`. Report only the totals; fixing is the cleanup workflow's job.

## Write

Create `journal/<ISO week> Review.md` (e.g. `2026-W42 Review.md`; the ISO week is in the status output) with `type: review`, `origin: claude`:

```markdown
# 2026-W42 Review

## This week
2–4 sentences: what came in and what it was mostly about.

## Added and changed
- [[Note]]: one line each (group if there are many)

## Promote
- Capture from [[2026-10-14]]: "…" → suggested note title

## Open loops
- [ ] task or question, with link to where it lives

## Themes and connections
- …

## Suggested next
- Inbox items to ingest first, sources a gap points to, notes worth developing from seed

## Vault health
N notes · N broken links · N orphans · N in inbox
```

Link it from that week's daily notes if they exist, and append `## [YYYY-MM-DD] review | <ISO week>` to `log.md`.

Then ask which promotions and ingests to do now. Promoting a capture means creating the note (via the conventions in `CLAUDE.md`) and replacing the capture text with a link to it. Don't promote anything unasked.
