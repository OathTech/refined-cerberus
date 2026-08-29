#!/usr/bin/env bash
# Create a build-primed git worktree for parallel work. Offline-safe.
# Adapted from the container's scripts/new-worktree.sh (the proven
# pattern; simplified — this repo has no opam/generated-tree extras).
#
# Usage:
#   scripts/new-worktree.sh <branch-name> [base-ref]
#
# Creates worktrees/<branch-name> with a new branch (from base-ref,
# default: current HEAD), then primes .lake from the main checkout so
# the first build needs no network and rebuilds only what changed.
set -euo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BRANCH="${1:?usage: new-worktree.sh <branch> [base-ref]}"
BASE="${2:-HEAD}"

DST="$REPO/worktrees/$BRANCH"
[[ -e "$DST" ]] && { echo "error: $DST already exists" >&2; exit 1; }
mkdir -p "$REPO/worktrees"

# Project-scoped git redirects (container deps/gitconfig), this
# process only.
CONTAINER="$(dirname "$REPO")"
[[ -f "$CONTAINER/deps/gitconfig" ]] && \
  export GIT_CONFIG_GLOBAL="$CONTAINER/deps/gitconfig"

git -C "$REPO" worktree add -b "$BRANCH" "$DST" "$BASE"

# Prime Lake state: dependency clones + build artifacts. Plain copy;
# Lake rebuilds anything whose inputs differ.
if [[ -d "$REPO/.lake" ]]; then
  echo "priming $DST/.lake from main checkout..."
  cp -a "$REPO/.lake" "$DST/.lake"
fi

echo
echo "Worktree ready: $DST"
echo "Build there with:  scripts/capped ~/.elan/bin/lake build"
