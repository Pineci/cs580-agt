# Connect a note

*Find and add missing connections for a note in the Obsidian vault — unlinked mentions, related notes, relevant maps, and non-obvious links between ideas.*

Target: the note(s) the user named. If none, pick the notes in `notes/` modified most recently (up to 5) and confirm the choice with the user.

Links are what make the vault a second brain rather than a folder of files. Good links are ones the user would actually follow: they explain, contrast, generalize, apply, or depend on each other. Shared keywords alone aren't enough.

## Find candidates

1. Read the target note.
2. `python3 _claude/vault_tool.py mentions "<Note>"` lists other notes that mention this note's title or aliases in plain text without linking it. These are the strongest candidates.
3. `python3 _claude/vault_tool.py backlinks "<Note>"` shows what already links here, so you don't duplicate.
4. Grep for the target's key terms and synonyms, and read the plausible hits. Look for:
   - **Same idea, different words** (possible duplicate: flag it for the cleanup workflow, don't merge here)
   - **Prerequisites and consequences**: what you need to understand first, what this enables
   - **Contrasts and alternatives**: competing methods, opposite claims
   - **Generalizations and special cases**
   - **Applications**: projects or questions where this idea is used
5. Check which map(s) in `maps/` it belongs in.

## Propose, then apply

Show a short list, strongest first: each proposed link with a one-line reason and where it would go. Mark which are unlinked mentions (just wrapping existing text in `[[ ]]`) and which are new sentences.

On approval:

- **Unlinked mention:** wrap the existing text, using `[[Note|text as written]]` if the wording differs from the title. Link the first mention per note only.
- **New relationship:** add a bullet with the reason under the note's `## Related` section (create the section if missing), e.g. `- [[Mirror Descent]]: generalizes this to non-Euclidean geometry`. Add the reverse link on the other note when the relationship matters in both directions.
- **Map:** add the note to the map if missing, and to `index.md` if missing.
- In `origin: human` notes, only wrap existing text or append to `## Related`; don't rewrite sentences.

Bump `updated:` on every note you touch, and append `## [YYYY-MM-DD] connect | <Note>` with the links added to `log.md`.
