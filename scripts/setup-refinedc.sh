#!/usr/bin/env bash
# Idempotent repo-local RefinedC toolchain setup (pattern:
# opendnp3-verified/scripts/setup-toolchain.sh — everything inside this
# repository; ~/.opam and all machine-global state untouched).
#
#   scripts/setup-refinedc.sh          # full setup (network needed first run)
#   scripts/setup-refinedc.sh --check  # report status, change nothing
#
# Phases (each skipped if already done):
#   A. local opam root (.opamroot) — bare init, no shell/global config
#   B. workspace clone (.refinedc-ws) from the container's deps/refinedc,
#      pinned per scripts/refinedc-pins.env
#   C. local directory switch in the workspace (donor-prescribed compiler)
#   D. opam repos (coq-released, iris-dev) on the LOCAL root only
#   E. make config + builddep (coq 9.1 + iris + stdpp + cerberus-lib + tool
#      deps) — the long phase
#   F. make all (lithium + caesium + typing theories)
#
# After setup, theory builds are offline (`source scripts/env-refinedc.sh`,
# then dune/make in .refinedc-ws). In-sandbox note: plain dune/make work
# in-sandbox; opam INSTALL operations may need the outside-sandbox operator
# (opam's bubblewrap sandbox does not nest).
set -euo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CONTAINER="$(dirname "$REPO")"
# shellcheck source=refinedc-pins.env
source "$REPO/scripts/refinedc-pins.env"

export OPAMROOT="$REPO/.opamroot"
WS="$REPO/.refinedc-ws"
DEPSRC="$CONTAINER/deps/refinedc"

check_only=0
[[ "${1:-}" == "--check" ]] && check_only=1

say() { echo "== setup-refinedc: $*"; }

# --- A: local opam root -----------------------------------------------------
if [[ ! -f "$OPAMROOT/config" ]]; then
  [[ $check_only == 1 ]] && { say "A MISSING: no local opam root"; exit 1; }
  say "A: initializing local opam root at $OPAMROOT"
  opam init --root="$OPAMROOT" --bare --no-setup --no-opamrc -y
else
  say "A ok: local opam root present"
fi

# --- B: workspace clone -----------------------------------------------------
if [[ ! -d "$WS/.git" ]]; then
  [[ $check_only == 1 ]] && { say "B MISSING: no workspace clone"; exit 1; }
  say "B: cloning $DEPSRC -> $WS @ $REFINEDC_COMMIT"
  git clone "$DEPSRC" "$WS"
  git -C "$WS" checkout --detach "$REFINEDC_COMMIT"
  git -C "$WS" remote add upstream https://gitlab.mpi-sws.org/iris/refinedc.git
else
  at="$(git -C "$WS" rev-parse HEAD)"
  if [[ "$at" != "$REFINEDC_COMMIT" ]]; then
    say "B DRIFT: workspace at $at, pin is $REFINEDC_COMMIT (move the pin or the tree deliberately)"
    exit 1
  fi
  say "B ok: workspace at pinned commit"
fi

# --- C: local switch --------------------------------------------------------
if ! opam switch list --root="$OPAMROOT" -s 2>/dev/null | grep -qx "$WS"; then
  [[ $check_only == 1 ]] && { say "C MISSING: no switch"; exit 1; }
  say "C: creating directory switch in $WS ($OCAML_SWITCH_PKGS)"
  # shellcheck disable=SC2086
  ( cd "$WS" && opam switch create --root="$OPAMROOT" . $OCAML_SWITCH_PKGS --no-install -y )
else
  say "C ok: switch registered"
fi

# --- D: repos on the local root --------------------------------------------
have_repos="$(opam repo list --root="$OPAMROOT" --all -s 2>/dev/null || true)"
for r in "coq-released https://coq.inria.fr/opam/released" \
         "iris-dev https://gitlab.mpi-sws.org/iris/opam.git"; do
  name="${r%% *}"; url="${r#* }"
  if ! grep -qx "$name" <<<"$have_repos"; then
    [[ $check_only == 1 ]] && { say "D MISSING: repo $name"; exit 1; }
    say "D: adding repo $name (local root only)"
    opam repo add --root="$OPAMROOT" "$name" "$url" --all-switches
  fi
done
say "D ok: repos present"

# --- E: builddep ------------------------------------------------------------
oexec() { opam exec --root="$OPAMROOT" --switch="$WS" -- "$@"; }
if ! oexec coqc --version >/dev/null 2>&1; then
  [[ $check_only == 1 ]] && { say "E MISSING: coq not installed"; exit 1; }
  say "E: make config + builddep (the long phase; log follows)"
  ( cd "$WS" && oexec make config && oexec make builddep OPAMFLAGS="-y" )
else
  say "E ok: coqc present ($(oexec coqc --version | head -1))"
fi

# --- F: theories ------------------------------------------------------------
if [[ ! -f "$WS/_build/default/theories/typing/typing.vo" && \
      ! -f "$WS/_build/default/theories/typing/.typing.theory.d" ]]; then
  [[ $check_only == 1 ]] && { say "F INCOMPLETE: theories not built"; exit 1; }
  say "F: building theories (make all)"
  ( cd "$WS" && oexec make all )
else
  say "F ok: theories built"
fi

say "DONE. Activate with: source scripts/env-refinedc.sh"
