# Query the vault

*Answer questions from the Obsidian second-brain vault, with every claim cited to the notes it came from.*

The value of answering from the vault rather than from general knowledge is that the user can trust and trace it. So: find the relevant notes, answer from them, cite them, and be explicit about the edges of what the vault covers.

## Find

1. Read `index.md` and any map in `maps/` that matches the topic. These are the fastest route to the right notes.
2. Grep for the key terms *and* their synonyms, abbreviations, and notation (e.g. "online gradient descent", "OGD", "projected gradient"). Search `notes/`, `sources/`, `maps/`, and `journal/`. Check `aliases:` lines too.
3. Read the most promising 5–15 notes in full, then follow their wikilinks one hop where a linked note looks relevant. Prefer source notes for specific claims (numbers, theorems, quotes) and concept notes for the overview.
4. Don't read `sources/_raw/` originals unless the notes are too thin to answer and the user wants depth; say when you do.

## Answer

- Lead with the direct answer, then the supporting detail.
- Cite with wikilinks right after the claim they support: "regret is $O(\sqrt{T})$ under convexity ([[Zinkevich 2003 - Online Convex Programming]])". Every substantive claim gets one.
- Keep vault knowledge and your own knowledge visibly separate. If you add something not in the vault, mark it: *(not in vault: general knowledge)*. Never present your own knowledge as if the notes said it.
- If notes disagree, say so and cite both sides; point out any `[!warning] Conflict` callouts.
- If the vault doesn't cover the question, or only partly, say exactly what's missing. That gap is useful information ("you have nothing on X; the closest is [[Y]]").
- Match length to the question. A lookup gets a few lines; a synthesis across many notes can be longer, organized by idea rather than by note.

## Filing the answer back

Good answers compound. If the answer is a substantive synthesis (it connects several notes, or resolves a question the vault didn't answer directly), end by offering to save it. Don't save without a yes. If the user agrees:

- Create `notes/<Descriptive Title>.md` from `templates/Synthesis.md` with the question, answer, evidence (wikilinks), and gaps; `origin: claude`.
- Link it from the most relevant map, add a line to `index.md`, and append to `log.md`: `## [YYYY-MM-DD] query | <Title>`.
