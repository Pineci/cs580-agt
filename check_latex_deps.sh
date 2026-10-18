#!/bin/bash
# Finds LaTeX packages used by any .tex file in this repo that aren't installed, and installs them via tlmgr.
# Usage: ./check_latex_deps.sh            (report only)
#        ./check_latex_deps.sh --install  (also installs; asks for admin password)
cd "$(dirname "$0")" || exit 1
eval "$(/usr/libexec/path_helper)" 2>/dev/null
command -v kpsewhich >/dev/null || { echo "No TeX found on PATH. Open a new Terminal window, or install MacTeX/BasicTeX."; exit 1; }

pkgs=$(find . -name '*.tex' -not -path '*/archive/*' -not -path './.git/*' -print0 \
  | xargs -0 grep -hoE '\\(usepackage|RequirePackage)(\[[^]]*\])?\{[^}]+\}' \
  | sed -E 's/.*\{([^}]+)\}/\1/' | tr ',' '\n' | tr -d ' ' | sort -u)

missing=()
for p in $pkgs; do
  kpsewhich "$p.sty" >/dev/null && continue
  [ -n "$(find . -name "$p.sty" -print -quit)" ] && continue   # local .sty in the repo
  missing+=("$p")
done
command -v latexmk >/dev/null || missing+=("latexmk")

[ ${#missing[@]} -eq 0 ] && { echo "All packages present."; exit 0; }
echo "Missing: ${missing[*]}"
echo "Looking up which TeX Live packages provide them..."
tl=()
for p in "${missing[@]}"; do
  if [ "$p" = latexmk ]; then tl+=(latexmk); continue; fi
  owner=$(tlmgr search --global --file "/$p.sty" 2>/dev/null | grep -E '^[A-Za-z0-9_.-]+:$' | head -1 | tr -d ':')
  if [ -n "$owner" ]; then tl+=("$owner"); else echo "  (couldn't find a package for $p)"; fi
done
tl=($(printf '%s\n' "${tl[@]}" | sort -u))
echo "Install command:  sudo tlmgr install ${tl[*]}"
if [ "$1" = "--install" ]; then
  sudo tlmgr update --self && sudo tlmgr install "${tl[@]}"
fi
