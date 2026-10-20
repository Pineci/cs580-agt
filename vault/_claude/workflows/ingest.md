# Ingest into the vault

*Ingest sources into the Obsidian second-brain vault — turn articles, papers, PDFs, URLs, transcripts, pasted text, or inbox items into a source note plus linked concept notes, then update the index and log.*

Follow the conventions in `CLAUDE.md` (layout, frontmatter, filenames, linking rules). The goal is not a summary that sits alone: it is to fold each source into the existing web of notes so the vault gets denser, not just bigger.

## What to ingest

Run `python3 _claude/vault_tool.py status` first; it lists the inbox.

- Nothing specific, or "the inbox" → every item in `inbox/` from the status output, oldest first.
- A path, URL, or pasted text → just that.
- More than ~5 items → confirm the list with the user first, then do them one at a time, finishing each completely (steps 1–7) before starting the next, so an interruption leaves the vault consistent.

## Steps for each source

1. **Read all of it.** Use Read for files (PDFs included) and WebFetch for URLs. Don't summarize from the first page. If it can't be read in full, say so and stop for that item.

2. **Check whether it's already here.** Grep `sources/` for the URL, title, DOI, or arXiv id. If it exists, update that source note instead of creating a second one.

3. **Write the source note** in `sources/`, named `Author Year - Short Title` (e.g. `Hazan 2016 - Introduction to Online Convex Optimization`). Use `templates/Paper.md` for academic papers and `templates/Source.md` for everything else; fill every frontmatter field you can. Write the summary and key points in your own words. Quote sparingly (short, attributed, only when the exact wording matters). For papers, state assumptions and results precisely, with math in `$…$`, since that is what gets queried later.

4. **Fold concepts into the vault.** List the 3–8 ideas, methods, people, or results from this source that are worth knowing on their own. For each:
   - Search for an existing note: filenames (`Glob notes/**/*.md`) *and* `aliases:` lines (`Grep -i "aliases:.*term"`). Check synonyms and abbreviations.
   - **Exists** → add what this source contributes under a dated bullet or a short new section, citing `[[Source Note]]`; add the source to its `sources:`; bump `updated:`. Respect `origin: human` notes (append, don't rewrite) and set them to `origin: mixed`.
   - **Doesn't exist and is substantive** → create it in `notes/` from `templates/Concept.md` (or `Person.md`), with `origin: claude`.
   - **Minor** → mention it in the source note only. Don't create stubs for passing mentions; a vault full of 2-line notes is worse than none.
   - If the source **contradicts** an existing note, add a `> [!warning] Conflict` callout to that note naming both sources. Don't silently pick a side.

5. **Link it in.** The source note's `## Concepts` section links every concept note touched. Add the source and any new concept notes to the relevant map in `maps/`. If the source starts a genuinely new area (several notes, no fitting map), propose a new map rather than creating one unasked.

6. **Update `index.md`** with one line per new note: `- [[Title]] — one-line summary`, under its map's heading (or **Sources** / **Unsorted**).

7. **Close out.**
   - Inbox file or downloaded original → move it into `sources/_raw/` (use `mv`; never delete), and set the source note's `raw:` to `[[filename.ext]]`. For a paper, name the moved file `<citekey>.pdf`.
   - Pasted text or a URL with no file → no raw file needed; `url:` is enough.
   - Append to `log.md`:
     ```
     ## [YYYY-MM-DD] ingest | Source Note Title
     - + [[Source Note Title]]
     - + [[New Concept]]
     - ~ [[Existing Concept]] (added X)
     ```

## Finish

Run `python3 _claude/vault_tool.py lint --path sources/` and fix any broken links you introduced. Then report briefly: notes created, notes updated, conflicts found, and anything you skipped or were unsure about (e.g. "didn't create a note for X; mention it if you want one").
