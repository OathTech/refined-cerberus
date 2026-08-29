# RefinedC donor toolchain: repo-local setup record

Date: 2026-08-29. Provenance: [AGENT], executed outside-sandbox on
[USER] instruction ("setup refinedC yourself. Be careful to do this in
a way that allows later in-sandbox working and doesn't disturb global
properties"), pattern copied from the working BRiCk setup at
`/home/dev/projects/opendnp3-verified` (BUILDING.md there is the
pattern's documentation; `.brick-workspace` + local `_opam`/opamroot).

## What exists now (all gitignored, all inside this repo)

| Path | Contents | Size |
|---|---|---|
| `.opamroot/` | repo-local opam ROOT (bare init, `--no-setup --no-opamrc`; `~/.opam` untouched) | 153M |
| `.refinedc-ws/` | RefinedC workspace: clone of `../deps/refinedc` (origin = local path; `upstream` remote = gitlab.mpi-sws.org) at pin `25f706d41`, with local `_opam` directory switch + full `_build` | 3.6G |

Pins: `scripts/refinedc-pins.env`. Toolchain: OCaml 4.14.2+flambda
(DEVELOPERS.md-prescribed), Rocq 9.1.0, rocq-iris dev.2026-07-16.1,
rocq-stdpp-unstable, coq-record-update 0.3.6, cerberus-lib pinned at
`f11e6b335` (their Makefile's pin, github). opam repos coq-released +
iris-dev registered on the LOCAL root only.

## Scripts

- `scripts/setup-refinedc.sh` — idempotent phases A–F; `--check` mode
  verifies without changing anything (verified green post-setup).
- `scripts/env-refinedc.sh` — per-shell activation (OPAMROOT + switch
  env). Source from the repo root.

## Verification transcript (2026-08-29)

1. `--check`: A–F all ok (coqc = Rocq 9.1.0).
2. coqc probe importing `lithium.interpreter`,
   `refinedc.typing.typing`, `caesium.lang/lifting` from
   `_build/default`: OK.
3. Frontend end-to-end: `dune exec -- refinedc check
   examples/wrapping_add.c` regenerated
   `examples/proofs/wrapping_add/generated_{code,spec,proof_*}.v`;
   `dune build examples/proofs/wrapping_add/` compiled the typing
   proof to `.vo` (their Lithium automation closed it). The complete
   donor pipeline — C → frontend → generated Coq → automation → Qed —
   runs locally.

## Why this matters beyond "the donor builds"

- **The statement oracle is mechanical now**: `refinedc check`
  regenerates each example's `generated_spec.v` (e.g.
  `type_of_wrapping_add` — the exact fn-type statement). The
  transfer-ladder's frozen Lean statements can be translated from,
  and reviewed against, this generated artifact instead of the
  annotation grammar alone.
- **"Automation-closed" is donor-native**: every generated proof is
  the same short script (`start_function` … `repeat liRStep` …
  sidecondition hooks). Their own acceptance form for an example IS
  automation-closes-it — supporting the wall rule that only
  automation-closed rows count.
- Lithium/typing behavior questions can now be answered by running
  their code, not just reading it (interpreter experiments,
  goal-state dumps, trace hooks).

## In-sandbox notes (the "later in-sandbox working" requirement)

- Theory/proof builds (`dune build`, `coqc`, `make all`) need only
  PATH/OPAMROOT from `env-refinedc.sh` + writes inside this repo and
  `/tmp` — sandbox-compatible, offline.
- `opam install`-class operations use opam's bubblewrap sandbox,
  which does not nest inside the agent sandbox — those are
  outside-sandbox/operator actions (matches the container's existing
  opam discipline).
- Network was needed only for: opam repo indexes, dependency
  tarballs, the cerberus-lib git pin. All are now cached under
  `.opamroot`/`_opam`; rebuilds are offline.

## Global-state audit

`~/.opam`, `~/.gitconfig`, shell profiles: untouched (everything ran
with `--root`/`OPAMROOT` + repo-local switch). apt: nothing installed
(the DEVELOPERS.md `libmpfr-dev` note never bit — cerberus-lib at the
pin built without it). `~/.cache/dune` was written by dune's shared
cache (same as every dune build on this box, benign; disable with
`DUNE_CACHE=disabled` if certification-integrity requires for a
specific run).
