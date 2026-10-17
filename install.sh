#!/usr/bin/env bash
# Build tvim and put its bin/ directory on PATH (idempotent), so `tvim file` just works.
set -euo pipefail

REPO_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BASHRC="$HOME/.bashrc"
BEGIN="# >>> tvim >>>"
END="# <<< tvim <<<"

make -C "$REPO_DIR"

touch "$BASHRC"
tmp="$(mktemp)"
# drop any previous tvim block, then append a fresh one
awk -v b="$BEGIN" -v e="$END" '$0==b{skip=1} !skip{print} $0==e{skip=0}' "$BASHRC" > "$tmp"
cat >> "$tmp" <<BLOCK
$BEGIN
case ":\$PATH:" in *":$REPO_DIR/bin:"*) ;; *) export PATH="$REPO_DIR/bin:\$PATH" ;; esac
$END
BLOCK
cat "$tmp" > "$BASHRC"
rm -f "$tmp"

echo "tvim built: $REPO_DIR/bin/tvim"
echo "PATH updated in $BASHRC - run 'source ~/.bashrc' (or open a new shell), then: tvim <file>"


