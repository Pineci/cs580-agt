# Second-brain vault (works with Claude)

This is an Obsidian vault set up so Claude can maintain it as a personal knowledge base: file articles and papers into linked notes, answer questions from your notes with citations, and keep links and structure tidy.

Nothing needs installing beyond the tools themselves. Everything Claude needs is in this folder:

- `CLAUDE.md`: the vault's conventions and a table that tells Claude which workflow to follow for each kind of request
- `_claude/workflows/`: step-by-step instructions for each workflow (plain Markdown, edit freely)
- `_claude/vault_tool.py`: a small helper that renames, merges, and archives notes without breaking links, and checks vault health
- `templates/`: note templates, also usable from Obsidian's Templates plugin

## Requirements

[Obsidian](https://obsidian.md), [Claude Code](https://docs.claude.com/en/docs/claude-code/overview) (terminal, desktop app, or IDE extension), and Python 3.8+. Git is optional but strongly recommended as an undo history.

## Getting started

1. Open this folder in Obsidian (*Open folder as vault*).
2. Recommended Obsidian settings:
   - **Files and links:** turn on *Use [[Wikilinks]]* and *Automatically update internal links*, set *New link format* to *Shortest path when possible*, set the attachment folder to `attachments`, and add `_claude/`, `_archive/`, and `sources/_raw/` to *Excluded files*.
   - **Core plugins:** set Templates' folder to `templates`; set Daily notes to folder `journal`, format `YYYY-MM-DD`, template `templates/Daily`.
3. Don't `git init` here: the vault is already tracked by the project repo one level up (`cs580-agt-dating-algo/`). Commit and pull from there.
4. Start Claude Code **from this folder** (`cd` here, then run `claude`, or open this folder in the desktop app). Claude reads `CLAUDE.md` automatically.

## What to ask

No special commands. Just say what you want:

| Say something like… | What happens |
| --- | --- |
| "Add this to my vault: <URL>" · "Process my inbox" | **Ingest:** writes a source note, updates or creates linked concept notes, flags contradictions, updates `index.md` and `log.md` |
| "What do my notes say about X?" · "Compare A and B from what I've read" | **Query:** an answer citing your notes, with gaps called out; offers to save good syntheses as notes |
| "Jot down: …" | **Capture:** appends to today's daily note |
| "Link up my note on X" · "What's related to X?" | **Connect:** finds unlinked mentions and related notes, proposes links |
| "Clean up the vault" · "Run a health check" | **Cleanup:** diagnoses, proposes a plan, applies only what you approve |
| "Do my weekly review" | **Review:** writes a review note with new material, open loops, and suggestions |

Drop files into `inbox/` (or point the Obsidian Web Clipper there) and ask Claude to process it whenever convenient.

## Good to know

- **Rename notes in Obsidian, or ask Claude.** Renaming in Finder or a terminal breaks links. Claude uses the helper script, which rewrites them.
- **Nothing gets deleted.** Retired notes move to `_archive/`, and original files are kept in `sources/_raw/`.
- **Your own writing is protected.** Notes without `origin: claude` are treated as yours; Claude adds to them but doesn't rewrite them.
- **Vault health check, anytime:** `python3 _claude/vault_tool.py lint`.
- **Changing how Claude works here:** edit the files in `_claude/workflows/` or the rules in `CLAUDE.md`. If you rename folders or note types, update `CLAUDE.md`, `templates/`, and the constants at the top of `_claude/vault_tool.py` together.
- **Fewer permission prompts (optional, per person):** create `.claude/settings.local.json` in the vault with:
  ```json
  { "permissions": { "allow": ["Bash(python3 _claude/vault_tool.py *)", "Bash(git status)", "Bash(git diff *)", "Bash(git log *)"] } }
  ```
