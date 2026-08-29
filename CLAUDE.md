# refined-cerberus

**NORTH STAR [USER 2026-08-29]: the product is a Lean-native C
verification framework** — RefinedC's architecture (type system +
Lithium-class automation) rebuilt natively in Lean on iris-lean,
attached directly to the cerberus-lean Core semantics, able to
verify NEW C programs with specs and proofs authored in Lean,
kernel-certified against the executable semantics. Replay harnesses,
transfer walls, and donor fidelity are MECHANISMS driving the build,
never the product: the product gauge is the native-verification
exhibit (a never-seen program verified end-to-end) at every arc
close; build metrics and product capability live on separate
ledgers. Full ruling + the three binding instruments: DECISIONS.md.

The Iris program logic is instantiated directly over Core; RefinedC
is the design target (not an end state); its frontend/annotation
layer is out of scope.

This file is WORKING PRACTICES ONLY. Design rulings live in
`docs/DECISIONS.md` (append-only register, [USER]/[AGENT]
provenance) — never here. Founding rationale:
`docs/2026-08-29_rules-of-engagement.md`. Predecessor history: the
cerberus-lean park branch `arc/segment-ladder`,
`lean_frontend/docs/reasoning-era/POSTMORTEM-AND-FORWARD-BRIEF.md`
— read it before touching design.

## Layout

| Path | What |
|------|------|
| `RefinedCerberus/` | the Lean package (Audit.lean = in-build axiom gate, last import of the lib root) |
| `docs/` | dated records + `DECISIONS.md` (rulings register) |
| `scripts/` | `capped` (cgroup-capped builds), `test_unit.sh` (gates), `new-worktree.sh`, `setup-refinedc.sh`/`env-refinedc.sh`/`refinedc-pins.env` (donor toolchain) |
| `worktrees/` | build-primed parallel checkouts (gitignored) |
| `.refinedc-ws/`, `.opamroot/` | repo-local RUNNABLE RefinedC (Rocq 9.1 + frontend, gitignored; see docs/2026-08-29_refinedc-toolchain-setup.md) — donor questions can be answered by running their code |
| `../deps/refinedc` | the NORMATIVE donor source (BSD) — read-only |
| `../deps/iris-lean` | iris-lean checkout backing the Lake pin — read-only |
| `../cerberus-lean` | the semantics repo — read-only from here |

## Building

```bash
scripts/capped ~/.elan/bin/lake build   # NEVER uncapped; elaborates the audit
scripts/test_unit.sh                    # grep ban + capped build
```

Toolchain: Lean 4.32.2 (elan). Deps (batteries, Qq, iris) are
git-pinned in lakefile.toml and resolve offline through the
container's `deps/gitconfig` redirects (`capped` self-loads the
container env). `lake update` only with `GIT_CONFIG_GLOBAL` set,
and only to move a pin deliberately. The cerberus-lean dependency
is added when its mainline pin lands (see DECISIONS).

## The referent discipline

- `deps/refinedc` is the normative spec for everything above the
  semantics. Design questions are answered by reading their code.
- **The PORT LEDGER is the central artifact**: every ported
  judgment/rule/type-former/tactic cites its donor (file:line);
  every divergence carries a forcing fact **about Cerberus** (never
  about our Lean port's internals), binned: (a) unnecessary
  invention → adopt theirs; (b) real Cerberus constraint → forcing
  fact stated; (c) inherited pseudo-constraint → named and priced.
  The operator adjudicates the ledger.
- The attachment layer (Iris-over-Core) is the one sanctioned
  design zone; its scope is decided in operator conversation before
  any brief. Acceptance question for every choice there: "does this
  let RefinedC's next layer port literally?"
- For concrete Core-wrangling obligations, search the park-branch
  proof quarry before re-deriving (see DECISIONS).

## Process

- **Arcs with charters**, DRAFT until [USER]-blessed. Dated docs in
  `docs/` are the record; decisions carry provenance tags.
- **Orchestrator/worker**: exact scoping; park-don't-improvise;
  workers commit their own green slices; the orchestrator
  independently re-verifies gates at boundaries (worker-claimed
  green is never accepted); quoted outputs verbatim, derived
  tallies labeled. **Park-ends-slice**: a committed park record
  stops the work.
- **Worktrees for parallel work** (`scripts/new-worktree.sh
  <branch>`); the primary checkout stays parked on main. Arc
  branches merge ff-only on explicit per-merge [USER] sign-off; the
  pre-merge audit ask is unconditional.
- **No design pass is dispatched before its scope is discussed with
  the operator.** A brief is a bundle of decisions, not a
  substitute for the conversation.
- **Fresh-eyes full reviews** on core documents at major revisions
  (never same-reviewer deltas); hostile adversarial review before
  ratification.
- Honest-gaps: unproved looks unproved; fail-closed, fail-noisy;
  stop-and-report over silent workaround.

## Trust rules (non-negotiable)

- **Kernel-only proof methods**: no `native_decide`/`bv_decide`/
  anything carrying `ofReduceBool`/`ofReduceNat`. `#guard` is a
  test, never "kernel-checked".
- **Exact axiom-cone assertions** in-build (Audit.lean): classical
  trio + declared boundary list only; boundary entries carry
  provenance (permanent-immovable or temporal-with-mover).
- **Capped builds always**; heavy lanes serial on this shared box;
  commit promptly (kill-loss containment).
- **No grind campaigns**: a ~1hr pass is a stop-and-report event;
  the banned pattern is bulk terms at the kernel in place of
  structure.
- **Classical names only** for mechanisms; house jargon banned.
- Profile before perf design; perf plans discussed then
  adversarially reviewed before execution.
- **Gates minimal**: new gates only for load-bearing TRUST
  properties; gates are plant-tested in both directions.

## Machine etiquette

- No machine-global state; no pushes without explicit per-push
  [USER] sign-off at the point of the push.
- Other agents work in sibling directories of the container: write
  ONLY inside `refined-cerberus/`; everything else is read-only
  reference.
- **Sandbox regime** [USER 2026-08-29]: sessions run inside the nono
  sandbox — no network; writes confined to this repo; `~/projects/`
  readable (donor source, proof-quarry git, practice donors) but
  read-only. Everything needed is local: opam/Lake/elan caches,
  the repo-local toolchain, git redirects to read-only local repos.
  opam `install`-class operations and network fetches are
  outside-sandbox operator actions. KNOWN GAP: `scripts/capped`
  (systemd-run) needs systemd user-bus access the sandbox profile
  does not grant ([USER 2026-08-29]: bus-grant experiments rolled
  back as out of scope) — in-sandbox capped invocations FAIL CLOSED.
  Heavy Lean builds are outside-sandbox operator actions until a
  capping route is ratified; never substitute uncapped runs.

## Current state

See `docs/DECISIONS.md` tail + latest dated doc. Arc 0
(scaffolding) complete except the semantics pin; arc 1 (the
RefinedC port map) in flight.
