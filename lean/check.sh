#!/usr/bin/env bash
# Builds the Lean project and reports what is and isn't fully proved.
# Usage: lean/check.sh           build, then list open targets (exits 0 if the build succeeds)
#        lean/check.sh --strict  also fail if anything depends on sorry or a non-standard axiom
set -euo pipefail
cd "$(dirname "$0")"
[ -x "$HOME/.elan/bin/lake" ] && export PATH="$HOME/.elan/bin:$PATH"
command -v lake >/dev/null || { echo "lake not found. Run ./setup_lean.sh from the repo root first."; exit 1; }

strict=0
[ "${1:-}" = "--strict" ] && strict=1

echo "== Building (lake build)"
lake build

echo
echo "== Axiom check (scripts/AxiomCheck.lean)"
out=$(lake env lean scripts/AxiomCheck.lean)
checked=$(echo "$out" | awk '/^CHECKED/ {print $2}')
targets=$(echo "$out" | awk '/^SORRY/ && $3 == "DatingAlgo.Targets" {print "  " $2}')
leaks=$(echo "$out" | awk '/^SORRY/ && $3 != "DatingAlgo.Targets" {print "  " $2 " (" $3 ")"}')
axioms=$(echo "$out" | awk '/^AXIOM/ {$1=""; print " " $0}')
count() { [ -z "$1" ] && echo 0 || echo "$1" | wc -l | tr -d ' '; }

echo "Checked ${checked:-0} declarations."
echo "Open targets (sorry in Targets.lean): $(count "$targets")"
[ -n "$targets" ] && echo "$targets"
if [ -n "$leaks" ]; then
  echo "WARNING: these declarations outside Targets.lean depend on sorry:"
  echo "$leaks"
fi
if [ -n "$axioms" ]; then
  echo "WARNING: these declarations use non-standard axioms:"
  echo "$axioms"
fi
[ -z "$leaks" ] && [ -z "$axioms" ] && echo "Everything outside Targets.lean is fully proved."

if [ "$strict" = 1 ] && { [ -n "$targets" ] || [ -n "$leaks" ] || [ -n "$axioms" ]; }; then
  echo "--strict: failing because something is not fully proved."
  exit 1
fi
exit 0
