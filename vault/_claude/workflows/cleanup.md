# Clean up the vault

*Health-check and tidy the Obsidian second-brain vault — fix broken links, merge duplicates, normalize frontmatter and tags, connect orphans, split oversized notes, and flag contradictions. Proposes a plan and waits for approval before changing anything.*

Scope: whatever the user named (nothing named = whole vault, all checks). A folder like `notes/` limits the report to that folder (pass it as `--path`); a check name limits the work to that category.

Follow the conventions in `CLAUDE.md`. Cleanup touches many files at once, so it works in three phases, and nothing changes until the user approves the plan.

## Phase 1: Diagnose

Run `python3 _claude/vault_tool.py status` first.

1. **Checkpoint.** If the vault is a git repo with uncommitted changes, recommend a commit first (`git add -A && git commit -m "pre-cleanup checkpoint"`) and ask before running it. If it isn't a repo, mention once that there's no undo, and suggest `git init`.
2. Run `python3 _claude/vault_tool.py lint --json` (add `--path` for a folder scope). This covers the mechanical checks.
3. Add the judgment checks the script can't do. Look at the possible-duplicate pairs and decide which are true duplicates (same idea) versus merely similar names. Skim the large notes for split points. Read the orphans and stubs and decide for each: link it somewhere, flesh it out from its sources, merge it, or archive it. Spot-check a sample of notes that share a topic for contradictions or claims a newer source supersedes. For tag variants, pick the canonical spelling (the most-used one, lowercase, hyphenated).

## Phase 2: Propose

Present one plan, grouped by category, with counts and concrete actions:

- **Safe fixes** (mechanical, apply as a batch on approval): broken links with an obvious target, missing or malformed frontmatter fields, tag spelling variants, missing `updated:` dates, notes missing from `index.md`.
- **Needs a decision** (list each item): merges, renames, splits, archiving, fixes to `origin: human` notes beyond frontmatter and links, broken links with no clear target (create the note, retarget, or unlink).
- **Flags only** (report, don't change): contradictions, stale claims, inbox items older than two weeks.

Then stop and ask which parts to apply. The user may approve some categories and not others.

## Phase 3: Apply

Use the script for anything that touches links, since hand-editing misses links in other files:

- **Fix a broken link:** `vault_tool.py retarget "<broken target>" "<correct note>"`.
- **Rename:** `vault_tool.py rename "<Old>" "<New>"` (always `--dry-run` first and check the count).
- **Merge A into B:**
  1. Integrate A's content into B: combine overlapping points, keep anything unique, and keep both notes' citations. Union `tags`, `aliases`, and `sources`, and add A's title to B's `aliases`.
  2. `vault_tool.py retarget "A" "B" --keep-display` (keeps old link text readable).
  3. `vault_tool.py archive "A"`.
- **Split:** create the new notes, move the content, leave a short summary with links in the original, and update backlinks that pointed at moved sections (`vault_tool.py backlinks`).
- **Orphan:** link it from the most relevant map or concept note, or archive it if it has no value.
- **Retire:** `vault_tool.py archive "<Note>"`. Never delete.

Bump `updated:` on every note you touch. When finished:

1. Re-run `lint` and show before/after counts for each category.
2. Append to `log.md`:
   ```
   ## [YYYY-MM-DD] cleanup | <scope>
   - fixed N broken links; merged [[A]] → [[B]]; archived [[C]]; …
   ```
3. If it's a git repo, show `git diff --stat` so the user can review, and offer to commit.
