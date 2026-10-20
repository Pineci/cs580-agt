#!/usr/bin/env bash
# Builds the Lean project and reports what is and isn't fully proved.
# Usage: lean/check.sh           build, then list open results (exits 0 if the build succeeds
#                                and no non-standard axioms are used)
#        lean/check.sh --strict  also fail if anything is open or depends on an open result
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
if ! out=$(lake env lean scripts/AxiomCheck.lean 2>&1); then
  echo "$out"
  echo "The axiom check itself failed to run."
  exit 1
fi
checked=$(echo "$out" | awk '/^CHECKED/ {print $2}')
open=$(echo "$out" | awk '/^OPEN/ {print "  " $2 "  (" $3 ")"}')
depends=$(echo "$out" | awk '/^DEPENDS/ {print "  " $2 "  (" $3 ")"}')
axioms=$(echo "$out" | awk '/^AXIOM/ {$1=""; print " " $0}')
count() { [ -z "$1" ] && echo 0 || echo "$1" | wc -l | tr -d ' '; }
n_open=$(count "$open"); n_dep=$(count "$depends")

echo "Checked ${checked:-0} theorems: $((${checked:-0} - n_open - n_dep)) fully proved,"
echo "$n_open open (contain sorry), $n_dep proved but depending on an open result."
[ -n "$open" ] && { echo; echo "Open:"; echo "$open"; }
[ -n "$depends" ] && { echo; echo "Depending on an open result:"; echo "$depends"; }
if [ -n "$axioms" ]; then
  echo
  echo "ERROR: these declarations use non-standard axioms:"
  echo "$axioms"
  exit 1
fi

if [ "$strict" = 1 ] && [ $((n_open + n_dep)) -gt 0 ]; then
  echo "--strict: failing because some results are not fully proved."
  exit 1
fi
exit 0
