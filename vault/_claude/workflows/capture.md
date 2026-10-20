# Quick capture

*Quickly capture a thought, idea, task, quote, or link into today's daily note in the Obsidian vault, with minimal processing.*

Capture: whatever the user asked to save, kept in their own words.

First run `python3 _claude/vault_tool.py status` to get the current date and time.

Capture is for speed. The user wants it saved and out of their head, so keep it to one short exchange.

1. Open `journal/<today>.md` (today's date is in the status output). If it doesn't exist, create it from `templates/Daily.md` with the date filled in.
2. Under `## Captures`, append one entry, keeping the user's wording:
   `- HH:MM <their text>`
   - Add `[[wikilinks]]` only for notes that already exist and are clearly what they mean (check with Glob); don't create new notes.
   - A task becomes `- [ ] HH:MM …`, a URL stays as a bare link, and a quote goes in `> …` with attribution if given.
3. If it's a URL or something substantial they'll want processed later, also note `→ ingest candidate` on the entry.
4. Reply with one line confirming where it went. No summary, no suggestions.

Don't touch `index.md` or `log.md`. Daily notes are raw material; the review and ingest workflows promote captures later.
