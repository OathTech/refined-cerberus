#!/usr/bin/env bash
# Idempotent setup of the cerberus-lean SEMANTICS dependency workspace
# (.cerberus-ws) — the pattern of the donor-toolchain setup script on branch refinedc/dev, adapted: a git
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
    # CONTENT-BASED guard (2026-08-31): the mainline often moves with
    # docs/records-only commits; demanding commit equality made every
    # such move a false drift stop. Priming from a moved source is
    # SAFE iff the pin..source diff is EMPTY on every path that feeds
    # the primed build state: the .lem sources (they determine
    # generated/), the generated tree itself, native/, and the lem
    # runtime seams. Any real change on those paths still fail-closes.
    # 2026-09-02 fail-open FOUND AND CLOSED (re-review N-3 diagnosis): the
    # hand-written seams lean_frontend/*.lean (copied into generated/ per
    # handwritten_copy.manifest — CerbMem.lean among them) were NOT on
    # this list, so a source whose CerbMem.lean differed from the pin's
    # primed with a green guard. They are on it now; and section C below
    # checks the primed copies against the PINNED clone's seam sources
    # directly, independent of this guard.
    # 2026-09-03 audit N-5: the lean_frontend/generated leg of this list
    # is VACUOUS for git-diff — the directory is gitignored upstream
    # (`git -C cerberus-lean ls-files lean_frontend/generated` is empty),
    # so the diff on it is always quiet. The lem-generated content is
    # protected by the `frontend` (.lem) leg plus the Lean lem-sync
    # STAMP (tools/check_lem_sync.sh --check-lean), which is the real
    # check and is re-run in --check mode below, not only at prime time.
    CONTENT_PATHS=(frontend lean_frontend/generated lean_frontend/native \
      'lean_frontend/*.lean' lean_frontend/handwritten_copy.manifest \
      lean_frontend/lakefile.toml lean_frontend/Makefile Makefile)
    if git -C "$SRC" diff --quiet "$CERBERUS_LEAN_COMMIT" "$src_at" -- "${CONTENT_PATHS[@]}"; then
      say "B: source at $src_at ≠ pin, but content-identical on all primed paths (verified) — priming allowed"
    else
      say "B FAIL-CLOSED: primary checkout ($src_at) differs from pin ($CERBERUS_LEAN_COMMIT) on primed content:"
      git -C "$SRC" diff --stat "$CERBERUS_LEAN_COMMIT" "$src_at" -- "${CONTENT_PATHS[@]}" | tail -5 >&2
      say "  Re-pin deliberately or wait; priming mismatched semantics is the stale-tree hazard."
      exit 1
    fi
  fi
  for p in lean_frontend/generated lean_frontend/native lean_frontend/.lake; do
    [[ -e "$SRC/$p" ]] || { say "B FAIL: $SRC/$p missing — primary checkout not built?"; exit 1; }
    say "B: priming $p"
    # copy the CONTENTS into place: native/ already exists in the clone
    # (tracked md5.c), and `cp -a dir dest` onto an existing dest would
    # nest it as dest/native/ (2026-09-02 re-pin finding; inert for the
    # library build, which never links native/*.o, but wrong)
    mkdir -p "$WS/$p"
    cp -a "$SRC/$p/." "$WS/$p"
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
  # 2026-09-03 audit N-5: re-verify the lem-generated content on every
  # run over an already-primed workspace (this is what --check does),
  # not only at prime time — the stamp is the only non-vacuous check on
  # generated/ (see the CONTENT_PATHS note above).
  ( cd "$WS" && tools/check_lem_sync.sh --check-lean ) || {
    say "B FAIL: Lean lem-sync stamp check red in the workspace (generated/ drifted from the stamp — re-prime: rm -rf $WS; re-run)"; exit 1; }
  say "B ok: Lean lem-sync stamp verified in the workspace"
fi

# --- C: hand-written seam identity (runs in BOTH modes; fail-closed) ---------
# The clone at $WS IS the pin, so $WS/lean_frontend/<seam>.lean is the pin's
# hand-written source; the primed generated/<seam>.lean must be byte-identical
# to it. The pin's own manifest (handwritten_copy.manifest) is the list; a pin
# without a manifest falls back to every lean_frontend/*.lean with a
# generated twin. Any mismatch or missing copy is a stop — priming from a
# source whose seams moved is exactly the stale-tree hazard.
seam_list=()
if [[ -f "$WS/lean_frontend/handwritten_copy.manifest" ]]; then
  while IFS= read -r line; do
    [[ -z "$line" || "$line" == \#* ]] && continue
    seam_list+=("$line")
  done < "$WS/lean_frontend/handwritten_copy.manifest"
else
  for f in "$WS"/lean_frontend/*.lean; do
    [[ -f "$WS/lean_frontend/generated/$(basename "$f")" ]] && seam_list+=("$(basename "$f")")
  done
fi
[[ ${#seam_list[@]} -gt 0 ]] || { say "C FAIL: no hand-written seams found to check (manifest empty?)"; exit 1; }
seam_bad=0
for f in "${seam_list[@]}"; do
  if [[ ! -f "$WS/lean_frontend/generated/$f" ]]; then
    say "C FAIL: primed generated/$f missing"; seam_bad=1
  elif ! cmp -s "$WS/lean_frontend/$f" "$WS/lean_frontend/generated/$f"; then
    say "C FAIL: primed generated/$f differs from the PIN's lean_frontend/$f (primed from a moved source?)"; seam_bad=1
  fi
done
[[ $seam_bad -eq 0 ]] || { say "C FAIL-CLOSED: re-prime from a source whose seams equal the pin (rm -rf $WS; re-run)"; exit 1; }
say "C ok: ${#seam_list[@]} hand-written seams byte-identical to the pin"

say "DONE. Lake consumes $WS/lean_frontend as a path dependency."
