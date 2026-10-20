#!/usr/bin/env python3
"""vault_tool.py - link-aware maintenance helpers for an Obsidian vault.

Stdlib only. Locates the vault root from its own path (<vault>/_claude/),
so it can be run from anywhere. Run with no arguments for help.
"""

import argparse
import datetime as dt
import difflib
import json
import os
import re
import shutil
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

# ---- configuration (keep in sync with CLAUDE.md) -------------------------------

VAULT = Path(__file__).resolve().parents[1]
SKIP_DIRS = {".obsidian", ".claude", "_claude", ".git", ".trash", "_archive", "node_modules"}
NO_FRONTMATTER_REQUIRED = ("inbox/", "sources/_raw/", "templates/")
ROOT_FILES = ("index.md", "log.md", "CLAUDE.md", "CLAUDE.local.md", "README.md")
NOT_ORPHANS = ROOT_FILES + ("inbox/", "journal/", "sources/_raw/", "templates/")
REQUIRED_KEYS = ("type", "created")
ALLOWED_TYPES = {"concept", "source", "person", "question", "synthesis", "map",
                 "project", "daily", "review"}
STUB_WORDS = 30
LARGE_WORDS = 2500
DUP_RATIO = 0.88
SECTION_LIMIT = 40

# ---- parsing -----------------------------------------------------------------

FENCE_RE = re.compile(r"^(```|~~~).*?^\1[^\n]*$", re.M | re.S)
INLINE_CODE_RE = re.compile(r"`[^`\n]+`")
WIKILINK_RE = re.compile(r"(!?)\[\[([^\[\]\n]+?)\]\]")
TAG_RE = re.compile(r"(?<![\w/&#(\[])#([A-Za-z0-9_\-/]*[A-Za-z_\-/][A-Za-z0-9_\-/]*)")


def read(p):
    with open(p, encoding="utf-8", errors="replace", newline="") as f:
        return f.read()


def write(p, text):
    with open(p, "w", encoding="utf-8", newline="") as f:
        f.write(text)


def split_frontmatter(text):
    """Return (frontmatter_text or None, body, body_offset_lines)."""
    if not (text.startswith("---\n") or text.startswith("---\r\n")):
        return None, text, 0
    lines = text.splitlines(keepends=True)
    for i in range(1, len(lines)):
        if lines[i].strip() == "---":
            return "".join(lines[1:i]), "".join(lines[i + 1:]), i + 1
    return None, text, 0


def parse_yaml_subset(fm):
    """Parse the simple YAML used in note frontmatter. Returns (dict, ok)."""
    data, key, ok = {}, None, True
    for raw in fm.splitlines():
        line = raw.split(" #", 1)[0].rstrip() if not raw.lstrip().startswith(("'", '"')) else raw.rstrip()
        if not line.strip():
            continue
        m = re.match(r"^([A-Za-z0-9_\-]+):\s*(.*)$", line)
        if m:
            key, val = m.group(1), m.group(2).strip()
            if val == "":
                data[key] = []
            elif val.startswith("[") and val.endswith("]"):
                inner = val[1:-1].strip()
                data[key] = [unquote(x) for x in split_inline_list(inner)] if inner else []
            else:
                data[key] = unquote(val)
        elif line.lstrip().startswith("- ") and key is not None:
            if not isinstance(data.get(key), list):
                data[key] = []
            data[key].append(unquote(line.lstrip()[2:].strip()))
        elif raw.startswith((" ", "\t")) and key is not None:
            continue  # nested/multiline value: tolerated, not parsed
        else:
            ok = False
    return data, ok


def split_inline_list(s):
    out, cur, depth, q = [], "", 0, None
    for ch in s:
        if q:
            cur += ch
            if ch == q:
                q = None
        elif ch in "\"'":
            q = ch
            cur += ch
        elif ch == "[":
            depth += 1
            cur += ch
        elif ch == "]":
            depth -= 1
            cur += ch
        elif ch == "," and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


def unquote(s):
    s = s.strip()
    if len(s) >= 2 and s[0] == s[-1] and s[0] in "\"'":
        return s[1:-1]
    return s


def as_list(v):
    if v is None:
        return []
    return v if isinstance(v, list) else [v]


def mask_code(text):
    """Blank out code so links/tags inside it are ignored, keeping offsets and line numbers."""
    blank = lambda m: re.sub(r"[^\n]", " ", m.group(0))
    return INLINE_CODE_RE.sub(blank, FENCE_RE.sub(blank, text))


def parse_link(inner):
    """'Target#Heading|Display' -> (target, heading, display). Handles escaped pipes in tables."""
    inner = inner.replace("\\|", "|")
    display = None
    if "|" in inner:
        inner, display = inner.split("|", 1)
    heading = None
    if "#" in inner:
        inner, heading = inner.split("#", 1)
    return inner.strip(), heading, display


# ---- vault model -------------------------------------------------------------

class Note:
    def __init__(self, path):
        self.path = path
        self.rel = path.relative_to(VAULT).as_posix()
        self.title = path.stem
        self.text = read(path)
        fm, self.body, self.body_line = split_frontmatter(self.text)
        self.has_fm = fm is not None
        self.fm, self.fm_ok = parse_yaml_subset(fm) if fm is not None else ({}, True)
        self.masked = mask_code(self.text)

    def links(self):
        """Yield (line_no, embed, target, heading, display, match_span)."""
        for m in WIKILINK_RE.finditer(self.masked):
            target, heading, display = parse_link(m.group(2))
            line_no = self.masked.count("\n", 0, m.start()) + 1
            yield line_no, m.group(1) == "!", target, heading, display, m.span()

    def tags(self):
        tags = {t.lstrip("#") for t in as_list(self.fm.get("tags")) if t}
        _, body_masked, _ = split_frontmatter(self.masked)
        tags.update(TAG_RE.findall(body_masked))
        return tags

    def aliases(self):
        return [a for a in as_list(self.fm.get("aliases")) if a]

    def word_count(self):
        return len(re.findall(r"\w+", self.body))


class Vault:
    def __init__(self):
        self.notes, self.files = [], []
        for root, dirs, files in os.walk(VAULT):
            dirs[:] = [d for d in dirs if d not in SKIP_DIRS and not d.startswith(".")]
            for f in files:
                if f.startswith("."):
                    continue
                p = Path(root) / f
                self.files.append(p)
                if p.suffix.lower() == ".md":
                    self.notes.append(Note(p))
        self.by_path = {n.path: n for n in self.notes}
        # lowercase relpath (no .md for notes) -> paths
        self.index = defaultdict(list)
        for p in self.files:
            rel = p.relative_to(VAULT).as_posix()
            key = rel[:-3] if rel.lower().endswith(".md") else rel
            self.index[key.lower()].append(p)

    def resolve(self, target):
        """Resolve a link target the way Obsidian does: by exact path, else by path suffix."""
        t = target.strip().lstrip("/")
        if t.lower().endswith(".md"):
            t = t[:-3]
        tl = t.lower()
        if not tl:
            return []
        if tl in self.index:
            return list(self.index[tl])
        hits = []
        for key, paths in self.index.items():
            if key.endswith("/" + tl):
                hits.extend(paths)
        return hits

    def find_note(self, name):
        """Find exactly one note by title, relpath, or alias. Exits with a message otherwise."""
        hits = [p for p in self.resolve(name) if p.suffix.lower() == ".md"]
        if not hits:
            nl = name.strip().lower()
            hits = [n.path for n in self.notes if nl in (a.lower() for a in n.aliases())]
        if len(hits) == 1:
            return self.by_path[hits[0]]
        if not hits:
            sys.exit(f"error: no note matches {name!r}")
        sys.exit(f"error: {name!r} is ambiguous: " + ", ".join(sorted(rel(p) for p in hits)))

    def link_name_for(self, path):
        """Shortest link target that resolves uniquely to path."""
        stem = path.stem
        if len(self.resolve(stem)) == 1:
            return stem
        r = rel(path)
        return r[:-3] if r.lower().endswith(".md") else r


def rel(p):
    return Path(p).relative_to(VAULT).as_posix()


# ---- commands ----------------------------------------------------------------

def cmd_status(args):
    v = Vault()
    now = dt.datetime.now()
    print(f"Now: {now:%Y-%m-%d %H:%M} ({now:%A}), ISO week {now:%G-W%V}")
    print(f"Vault: {VAULT}")
    counts = defaultdict(int)
    for n in v.notes:
        counts[n.rel.split("/")[0] if "/" in n.rel else "(root)"] += 1
    print("Notes by folder: " + ", ".join(f"{k} {counts[k]}" for k in sorted(counts)))
    inbox = sorted(p for p in v.files if rel(p).startswith("inbox/"))
    print(f"Inbox: {len(inbox)} item(s)")
    for p in inbox[:50]:
        age = (dt.datetime.now() - dt.datetime.fromtimestamp(p.stat().st_mtime)).days
        print(f"  - {rel(p)}  ({age}d old)")
    try:
        out = subprocess.run(["git", "-C", str(VAULT), "status", "--porcelain"],
                             capture_output=True, text=True, timeout=20)
        if out.returncode == 0:
            dirty = [l for l in out.stdout.splitlines() if l.strip()]
            print(f"Git: repository, {len(dirty)} uncommitted change(s)")
        else:
            print("Git: not a repository (no undo history; consider `git init`)")
    except (OSError, subprocess.TimeoutExpired):
        print("Git: unavailable")
    log = VAULT / "log.md"
    if log.exists():
        entries = [l for l in read(log).splitlines() if l.startswith("## [")]
        print("Recent log entries:" if entries else "Log: empty")
        for e in entries[-5:]:
            print("  " + e[3:])


def lint(v, path_prefix=None):
    inbound = defaultdict(set)
    outbound = defaultdict(int)
    broken, used_files = [], set()
    for n in v.notes:
        for line_no, embed, target, _, _, _ in n.links():
            if not target:
                continue  # [[#Heading]] self-link
            hits = v.resolve(target)
            if not hits:
                broken.append({"file": n.rel, "line": line_no, "target": target})
            for h in hits:
                used_files.add(h)
                if h != n.path:
                    inbound[h].add(n.rel)
            outbound[n.path] += 1

    scope = [n for n in v.notes if not path_prefix or n.rel.startswith(path_prefix)]
    in_scope = lambda f: not path_prefix or f.startswith(path_prefix)
    r = {"broken_links": [b for b in broken if in_scope(b["file"])]}

    stems = defaultdict(list)
    for n in v.notes:
        stems[n.title.lower()].append(n.rel)
    r["ambiguous_names"] = [{"name": k, "files": sorted(fs)} for k, fs in sorted(stems.items()) if len(fs) > 1]

    r["orphans"] = sorted(n.rel for n in scope
                          if not inbound[n.path] and not n.rel.startswith(NOT_ORPHANS) and n.rel not in NOT_ORPHANS)
    r["dead_ends"] = sorted(n.rel for n in scope if outbound[n.path] == 0
                            and not n.rel.startswith(NOT_ORPHANS) and n.rel not in NOT_ORPHANS)

    fm_problems = []
    for n in scope:
        if n.rel.startswith(NO_FRONTMATTER_REQUIRED) or n.rel in ROOT_FILES:
            continue
        issues = []
        if not n.has_fm:
            issues.append("no frontmatter")
        else:
            if not n.fm_ok:
                issues.append("frontmatter not parseable")
            issues += [f"missing {k}" for k in REQUIRED_KEYS if not n.fm.get(k)]
            t = n.fm.get("type")
            if t and t not in ALLOWED_TYPES:
                issues.append(f"unknown type {t!r}")
            for k in ("created", "updated"):
                val = n.fm.get(k)
                if val and not re.match(r"^\d{4}-\d{2}-\d{2}", str(val)):
                    issues.append(f"{k} not YYYY-MM-DD")
        if issues:
            fm_problems.append({"file": n.rel, "issues": issues})
    r["frontmatter_problems"] = fm_problems

    r["stubs"] = sorted(n.rel for n in scope if n.word_count() < STUB_WORDS
                        and not n.rel.startswith(NO_FRONTMATTER_REQUIRED + ("journal/",))
                        and n.rel not in ROOT_FILES)
    r["large_notes"] = sorted(({"file": n.rel, "words": n.word_count()} for n in scope
                               if n.word_count() > LARGE_WORDS and not n.rel.startswith(("sources/_raw/",))
                               and n.rel not in ROOT_FILES), key=lambda x: -x["words"])

    variants = defaultdict(set)
    for n in v.notes:
        for t in n.tags():
            norm = re.sub(r"[\s_\-]+", "-", t.lower()).rstrip("/")
            norm = re.sub(r"(?<=[a-z])s$", "", norm)
            variants[norm].add(t)
    r["tag_variants"] = [sorted(s) for s in variants.values() if len(s) > 1]

    candidates = [n for n in v.notes if not n.rel.startswith(NOT_ORPHANS)]
    norm = lambda s: re.sub(r"[^a-z0-9]+", " ", s.lower()).strip()
    names = []
    for n in candidates:
        for label in [n.title] + n.aliases():
            names.append((norm(label), n.rel))
    dups, seen = [], set()
    if len(names) <= 4000:
        names.sort()
        for i, (a, fa) in enumerate(names):
            for b, fb in names[i + 1:i + 60]:
                if fa == fb or not a or not b:
                    continue
                if a == b or near_duplicate(a, b):
                    pair = tuple(sorted((fa, fb)))
                    if pair not in seen and (in_scope(fa) or in_scope(fb)):
                        seen.add(pair)
                        dups.append(list(pair))
    r["possible_duplicates"] = dups

    attach = [p for p in v.files if p.suffix.lower() != ".md" and rel(p).startswith("attachments/")]
    r["unused_attachments"] = sorted(rel(p) for p in attach if p not in used_files)

    now = dt.datetime.now()
    r["inbox"] = [{"file": rel(p), "age_days": (now - dt.datetime.fromtimestamp(p.stat().st_mtime)).days}
                  for p in sorted(v.files) if rel(p).startswith("inbox/")]
    r["summary"] = {"notes": len(v.notes), "scoped_notes": len(scope),
                    **{k: len(val) for k, val in r.items() if isinstance(val, list)}}
    return r


def near_duplicate(a, b):
    """Similar spelling, or one multi-word name is the other plus a word or two."""
    if abs(len(a) - len(b)) <= 4 and difflib.SequenceMatcher(None, a, b).ratio() >= DUP_RATIO:
        return True
    ta, tb = a.split(), b.split()
    short, long_ = (ta, tb) if len(ta) <= len(tb) else (tb, ta)
    return len(short) >= 2 and len(long_) - len(short) <= 2 and set(short) <= set(long_)


def cmd_lint(args):
    r = lint(Vault(), args.path)
    if args.json:
        print(json.dumps(r, indent=2))
        return
    limit = None if args.all else SECTION_LIMIT
    s = r["summary"]
    print(f"# Vault lint: {s['notes']} notes" + (f" ({s['scoped_notes']} under {args.path})" if args.path else ""))
    sections = [
        ("broken_links", "Broken links", lambda x: f"{x['file']}:{x['line']} -> [[{x['target']}]]"),
        ("ambiguous_names", "Ambiguous names (same title in several folders)", lambda x: f"{x['name']}: {', '.join(x['files'])}"),
        ("possible_duplicates", "Possible duplicates (similar titles/aliases)", lambda x: " <-> ".join(x)),
        ("frontmatter_problems", "Frontmatter problems", lambda x: f"{x['file']}: {'; '.join(x['issues'])}"),
        ("tag_variants", "Tag variants", lambda x: ", ".join("#" + t for t in x)),
        ("orphans", "Orphans (no inbound links)", str),
        ("dead_ends", "Dead ends (no outbound links)", str),
        ("stubs", f"Stubs (< {STUB_WORDS} words)", str),
        ("large_notes", f"Large notes (> {LARGE_WORDS} words; split candidates)", lambda x: f"{x['file']} ({x['words']} words)"),
        ("unused_attachments", "Unused attachments", str),
        ("inbox", "Inbox", lambda x: f"{x['file']} ({x['age_days']}d old)"),
    ]
    for key, title, fmt in sections:
        items = r[key]
        print(f"\n## {title}: {len(items)}")
        for it in items[:limit]:
            print("- " + fmt(it))
        if limit and len(items) > limit:
            print(f"- ... {len(items) - limit} more (use --all or --json)")


def cmd_backlinks(args):
    v = Vault()
    note = v.find_note(args.note)
    count = 0
    for n in v.notes:
        if n.path == note.path:
            continue
        lines = n.text.splitlines()
        for line_no, _, target, _, _, _ in n.links():
            if target and note.path in v.resolve(target):
                count += 1
                print(f"{n.rel}:{line_no}: {lines[line_no - 1].strip()[:160]}")
    print(f"-- {count} link(s) to {note.rel}", file=sys.stderr)


def cmd_mentions(args):
    v = Vault()
    note = v.find_note(args.note)
    terms = sorted({t for t in [note.title] + note.aliases() if len(t) >= 4}, key=len, reverse=True)
    if not terms:
        sys.exit("error: title and aliases are too short to search reliably")
    pat = re.compile(r"(?<![\w\[])(" + "|".join(re.escape(t) for t in terms) + r")(?![\w\]])", re.I)
    count = 0
    for n in v.notes:
        if n.path == note.path or n.rel.startswith(("sources/_raw/", "templates/")):
            continue
        masked = WIKILINK_RE.sub(lambda m: " " * len(m.group(0)), n.masked)
        _, _, offset = split_frontmatter(n.text)
        lines, orig = masked.splitlines(), n.text.splitlines()
        for i, line in enumerate(lines):
            if i < offset or line.lstrip().startswith("#"):
                continue
            if pat.search(line):
                count += 1
                print(f"{n.rel}:{i + 1}: {orig[i].strip()[:160]}")
    print(f"-- {count} unlinked mention(s) of {', '.join(terms)}", file=sys.stderr)


def rewrite_links(v, matches, new_name, keep_display, dry_run):
    """Rewrite every wikilink for which matches(target) is true. Returns {relpath: count}."""
    changed = {}
    for n in v.notes:
        out, last, count = [], 0, 0
        for _, embed, target, heading, display, (s, e) in n.links():
            if not target or not matches(target):
                continue
            if display is None and keep_display:
                display = target
            new = ("!" if embed else "") + "[[" + new_name + (f"#{heading}" if heading else "")
            new += (f"|{display}" if display is not None else "") + "]]"
            if "\\|" in n.text[s:e]:
                new = new.replace("|", "\\|")
            if new == n.text[s:e]:
                continue
            out.append(n.text[last:s] + new)
            last, count = e, count + 1
        if count:
            changed[n.rel] = count
            if not dry_run:
                write(n.path, "".join(out) + n.text[last:])
    return changed


def warn_ambiguous(v, path):
    """Links that might mean `path` but also match another note; these are never rewritten."""
    amb = [(n.rel, ln, t) for n in v.notes for ln, _, t, _, _, _ in n.links()
           if t and path in (hits := v.resolve(t)) and len(hits) > 1]
    if amb:
        print(f"warning: {len(amb)} ambiguous link(s) may refer to {rel(path)} but were left alone "
              "(the title matches several notes); check them and fix by hand with a path link:")
        for f, ln, t in amb[:20]:
            print(f"  {f}:{ln} -> [[{t}]]")


def report_changes(changed, dry_run):
    verb = "would update" if dry_run else "updated"
    total = sum(changed.values())
    print(f"{verb} {total} link(s) in {len(changed)} file(s)")
    for f, c in sorted(changed.items()):
        print(f"  {f}: {c}")


def cmd_rename(args):
    v = Vault()
    note = v.find_note(args.old)
    new = args.new.strip()
    if new.lower().endswith(".md"):
        new = new[:-3]
    if re.search(r'[\\:*?"<>|#^\[\]]', new.split("/")[-1]):
        sys.exit("error: new name contains characters Obsidian can't link to: \\ : * ? \" < > | # ^ [ ]")
    dest = (VAULT / (new + ".md")) if "/" in new else note.path.with_name(new + ".md")
    if dest.exists() and dest.resolve() != note.path.resolve():
        sys.exit(f"error: {rel(dest)} already exists")
    old_path = note.path
    clash = [n.rel for n in v.notes if n.title.lower() == dest.stem.lower() and n.path != old_path]
    new_name = rel(dest)[:-3] if clash else dest.stem
    matches = lambda t: v.resolve(t) == [old_path]
    verb = "would rename" if args.dry_run else "renamed"
    changed = rewrite_links(v, matches, new_name, False, args.dry_run)
    if not args.dry_run:
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.move(str(old_path), str(dest))
    print(f"{verb} {rel(old_path)} -> {rel(dest)}")
    report_changes(changed, args.dry_run)
    warn_ambiguous(v, old_path)
    if clash:
        print("warning: another note has the same title (" + ", ".join(clash) +
              "); links to it by bare title are now ambiguous. Run lint.")


def cmd_retarget(args):
    v = Vault()
    dest = v.find_note(args.new)
    old = args.old.strip()
    old_l = old.lower()[:-3] if old.lower().endswith(".md") else old.lower()
    old_hits = [p for p in v.resolve(old) if p.suffix.lower() == ".md"]
    old_path = old_hits[0] if len(old_hits) == 1 else None
    if old_path == dest.path:
        sys.exit("error: old and new are the same note")

    def matches(t):
        tl = t.strip().lower()
        tl = tl[:-3] if tl.endswith(".md") else tl
        if old_path is not None:
            return v.resolve(t) == [old_path]
        return tl == old_l or tl.split("/")[-1] == old_l.split("/")[-1]

    changed = rewrite_links(v, matches, v.link_name_for(dest.path), args.keep_display, args.dry_run)
    report_changes(changed, args.dry_run)
    if old_path is not None:
        warn_ambiguous(v, old_path)
    if old_path is not None and not args.dry_run:
        print(f"note: {rel(old_path)} still exists; archive it once its content is merged")


def cmd_archive(args):
    v = Vault()
    note = v.find_note(args.note)
    refs = [(n.rel, ln) for n in v.notes if n.path != note.path
            for ln, _, t, _, _, _ in n.links() if t and note.path in v.resolve(t)]
    warn_ambiguous(v, note.path)
    if refs and not args.force:
        print(f"refusing: {len(refs)} link(s) still point at {note.rel}:")
        for f, ln in refs[:20]:
            print(f"  {f}:{ln}")
        sys.exit("retarget them first, or pass --force")
    dest = VAULT / "_archive" / note.rel
    if dest.exists():
        dest = dest.with_name(f"{dest.stem} ({dt.date.today().isoformat()}){dest.suffix}")
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.move(str(note.path), str(dest))
    print(f"archived {note.rel} -> {rel(dest)}")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sp = ap.add_subparsers(dest="cmd", required=True)
    sp.add_parser("status", help="date, inbox, counts, git state, recent log")
    p = sp.add_parser("lint", help="vault health report")
    p.add_argument("--json", action="store_true")
    p.add_argument("--all", action="store_true", help="don't truncate sections")
    p.add_argument("--path", help="only report on notes under this relative path prefix")
    p = sp.add_parser("backlinks", help="links pointing at a note")
    p.add_argument("note")
    p = sp.add_parser("mentions", help="unlinked mentions of a note's title/aliases")
    p.add_argument("note")
    p = sp.add_parser("rename", help="rename/move a note and rewrite links")
    p.add_argument("old")
    p.add_argument("new", help="new title, or vault-relative path like notes/New Title")
    p.add_argument("--dry-run", action="store_true")
    p = sp.add_parser("retarget", help="point links at a different note")
    p.add_argument("old", help="old target (may be a broken link target)")
    p.add_argument("new")
    p.add_argument("--keep-display", action="store_true",
                   help="keep the old text visible: [[Old]] -> [[New|Old]]")
    p.add_argument("--dry-run", action="store_true")
    p = sp.add_parser("archive", help="move a note to _archive/")
    p.add_argument("note")
    p.add_argument("--force", action="store_true")
    args = ap.parse_args()
    {"status": cmd_status, "lint": cmd_lint, "backlinks": cmd_backlinks, "mentions": cmd_mentions,
     "rename": cmd_rename, "retarget": cmd_retarget, "archive": cmd_archive}[args.cmd](args)


if __name__ == "__main__":
    if hasattr(__import__("signal"), "SIGPIPE"):
        import signal
        signal.signal(signal.SIGPIPE, signal.SIG_DFL)  # quiet exit when piped to head
    main()
