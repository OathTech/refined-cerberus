#!/usr/bin/env bash
# Activate the repo-local RefinedC toolchain (pattern:
# opendnp3-verified/scripts/env.sh). Shell-scoped only — no global state.
#   source scripts/env-refinedc.sh
_RC_REPO="$(cd "$(dirname "${BASH_SOURCE[0]:-$0}")/.." && pwd)"
export OPAMROOT="$_RC_REPO/.opamroot"
export RC_WS="$_RC_REPO/.refinedc-ws"
eval "$(opam env --root="$OPAMROOT" --switch="$RC_WS" --set-switch --set-root 2>/dev/null)" || \
  echo "env-refinedc: switch not ready yet (run scripts/setup-refinedc.sh)" >&2
echo "refinedc env: root=$OPAMROOT switch=$RC_WS" >&2
