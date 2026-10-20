#!/usr/bin/env bash
# One-time setup for the Lean 4 + Mathlib proof project in lean/.
# Usage: ./setup_lean.sh
#
# What it does:
#   1. Installs elan, the Lean version manager, if it's missing. Uses Homebrew on
#      macOS when available, otherwise the official installer from github.com/leanprover/elan.
#   2. Keeps build files out of iCloud: lean/.lake is a symlink to lean/.lake.nosync,
#      which iCloud Drive doesn't sync.
#   3. Downloads the Lean version pinned in lean/lean-toolchain and Mathlib's prebuilt
#      cache. The first run downloads a few GB and uses about 7 GB of disk.
#   4. Builds the project and reports open proof targets (lean/check.sh).
#
# Safe to re-run. Windows: use WSL, or the Lean 4 VS Code extension's installer.
set -euo pipefail
cd "$(dirname "$0")/lean"

[ -x "$HOME/.elan/bin/elan" ] && export PATH="$HOME/.elan/bin:$PATH"
if ! command -v elan >/dev/null 2>&1; then
  echo "== Installing elan (Lean version manager)"
  if [ "$(uname)" = "Darwin" ] && command -v brew >/dev/null 2>&1; then
    brew install elan-init
  else
    curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain none
    export PATH="$HOME/.elan/bin:$PATH"
  fi
fi
echo "Using $(elan --version)"

# Lake keeps Mathlib (about 7 GB) under .lake. Point it at a folder iCloud won't sync.
if [ -L .lake ]; then
  mkdir -p .lake.nosync            # symlink came from another machine; recreate its target
elif [ -d .lake ]; then
  echo "Note: lean/.lake is a real folder. If this repo is in iCloud Drive, move it to"
  echo "      lean/.lake.nosync and run: ln -s .lake.nosync lean/.lake"
else
  mkdir -p .lake.nosync
  ln -s .lake.nosync .lake
fi

echo "== Fetching Mathlib and its prebuilt cache (first run downloads a few GB)"
lake exe cache get

echo "== Building and checking"
./check.sh

cat <<'EOF'

Setup complete. Day to day:
  lean/check.sh            rebuild and list open targets
  lean/check.sh --strict   fail unless everything is fully proved
Editor: install the "Lean 4" extension in VS Code, then open lean/ (or any .lean file).
EOF
