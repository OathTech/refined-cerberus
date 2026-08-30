#!/usr/bin/env bash
# Idempotent setup of the cerberus-lean SEMANTICS dependency workspace
# (.cerberus-ws) — the pattern of setup-refinedc.sh, adapted: a git
# clone of the local cerberus-lean repo at the pinned commit, PRIMED
# with the gitignored build state a bare clone lacks (generated/,
# native/, .lake, the lem-sync stamps). Lake consumes it as a path
# dependency (lakefile.toml), so the pin lives here, drift-checked.
#
#   scripts/setup-cerberus-dep.sh          # setup (offline; local clone)
#   scripts/setup-cerberus-dep.sh --check  # verify, change nothing
#
# Priming provenance: the PRIMARY cerberus-lean checkout. If it is not
# at the pin, we STOP (fail-closed) — priming from a different rev is
# exactly the stale-tree hazard the lem-sync stamp gate exists for
# (cerberus-lean 8545eb8a7); the stamp rides along so staleness that
# slips through still fails the dep build loudly.
set -euo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CONTAINER="$(dirname "$(dirname "$REPO")")"
# When run from a worktree, REPO is worktrees/<branch>; the container
# is two levels up from the PRIMARY checkout. Resolve robustly:
case "$REPO" in
  */worktrees/*) PRIMARY_RC="$(dirname "$(dirname "$REPO")")" ;;
  *)             PRIMARY_RC="$REPO" ;;
esac
CONTAINER="$(dirname "$PRIMARY_RC")"
SRC="$CONTAINER/cerberus-lean"
WS="$REPO/.cerberus-ws"

# shellcheck source=semantics-pin.env
source "$REPO/scripts/semantics-pin.env"

check_only=0
[[ "${1:-}" == "--check" ]] && check_only=1
say() { echo "== setup-cerberus-dep: $*"; }

# --- A: clone at the pin ----------------------------------------------------
if [[ ! -d "$WS/.git" ]]; then
  [[ $check_only == 1 ]] && { say "A MISSING: no workspace clone"; exit 1; }
  say "A: cloning $SRC -> $WS @ $CERBERUS_LEAN_COMMIT"
  git clone --no-checkout "$SRC" "$WS"
  git -C "$WS" checkout --detach "$CERBERUS_LEAN_COMMIT"
else
  at="$(git -C "$WS" rev-parse HEAD)"
  [[ "$at" == "$CERBERUS_LEAN_COMMIT" ]] || {
    say "A DRIFT: workspace at $at, pin is $CERBERUS_LEAN_COMMIT — move the pin or re-run setup deliberately"; exit 1; }
  say "A ok: workspace at pinned commit"
fi

# --- B: prime gitignored build state from the primary checkout --------------
prime_done="$WS/.primed-from"
if [[ ! -f "$prime_done" ]]; then
  [[ $check_only == 1 ]] && { say "B MISSING: not primed"; exit 1; }
  src_at="$(git -C "$SRC" rev-parse HEAD)"
  if [[ "$src_at" != "$CERBERUS_LEAN_COMMIT" ]]; then
    say "B FAIL-CLOSED: primary checkout is at $src_at, pin is $CERBERUS_LEAN_COMMIT."
    say "  Priming from a mismatched tree is the stale-semantics hazard; re-pin or wait."
    exit 1
  fi
  for p in lean_frontend/generated lean_frontend/native lean_frontend/.lake; do
    [[ -e "$SRC/$p" ]] || { say "B FAIL: $SRC/$p missing — primary checkout not built?"; exit 1; }
    say "B: priming $p"
    mkdir -p "$WS/$(dirname "$p")"
    cp -a "$SRC/$p" "$WS/$p"
  done
  for f in lean_frontend/lem_sync.sha256 ocaml_frontend/lem_sync.sha256; do
    if [[ -f "$SRC/$f" ]]; then
      mkdir -p "$WS/$(dirname "$f")"
      cp "$SRC/$f" "$WS/$f"
    fi
  done
  # The Lean-side stamp is written by `make lean-prelude-src` (cerberus
  # 8545eb8a7); a checkout that hasn't re-run it since that gate landed
  # has none. Record it HERE against the primed tree: provenance for
  # the primed tree's freshness is the pin's merge-time green battery
  # (recorded in .primed-from); the stamp then catches any LATER drift
  # of .cerberus-ws via --check-lean.
  if [[ ! -f "$WS/lean_frontend/lem_sync.sha256" ]]; then
    say "B: source has no Lean stamp; recording one against the primed tree"
    ( cd "$WS" && tools/check_lem_sync.sh --record-lean )
  fi
  ( cd "$WS" && tools/check_lem_sync.sh --check-lean ) || {
    say "B FAIL: Lean lem-sync stamp check red in the workspace"; exit 1; }
  [[ -f "$WS/ocaml_frontend/lem_sync.sha256" ]] || {
    say "B FAIL: OCaml lem-sync stamp missing (source checkout incomplete?)"; exit 1; }
  echo "$src_at $(date -u +%Y-%m-%dT%H:%M:%SZ 2>/dev/null || echo unstamped)" > "$prime_done"
else
  say "B ok: primed ($(cat "$prime_done"))"
fi

say "DONE. Lake consumes $WS/lean_frontend as a path dependency."
