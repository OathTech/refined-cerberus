# refined-cerberus (main: the cerberus-heaplang demo)

**What this repository's `main` contains**: the demo package
`cerberus-heaplang/` — a classical (Reynolds/O'Hearn) separation logic
over a fragment of Cerberus Core, built on iris-lean, whose exports are
statements about the cerberus-lean semantics' execution and memory
states — plus the durable infrastructure around it (gate runner,
capped builds, the pinned semantics workspace) and the records.

**TRUST ARCHITECTURE [USER 2026-08-29]: the cerberus-lean
operational semantics is the ONLY trusted semantics.** Everything
above it — the relational mirror, the WP, any type system or
automation — is DERIVED and has no independent semantic authority;
any disagreement with the engine is by definition a defect in the
derived layer. The exports are adequacy results stated EXCLUSIVELY
over the cerberus-lean semantics ([USER], verbatim: "'mirroring'
without proof is valueless"). Operational consequence: no layer
counts as capability until its downward theorem into the engine
exists — the adequacy spine is load-bearing from the first rung.

**Longer-term direction** ([USER 2026-08-29, 2026-09-03]): an
agent-driven C verification layer in the RefinedC design family,
built above this logic, adopting only the slice of RefinedC that
serves that goal. That work — its Lake package, the donor toolchain,
the design notes — lives on the branch `refinedc/dev` until it is
presentable; nothing of it is on `main`.

This file is WORKING PRACTICES ONLY. Design rulings live in
`docs/DECISIONS.md` (append-only register, [USER]/[AGENT]
provenance) — never here. Founding rationale:
`docs/2026-08-29_rules-of-engagement.md`.

## Layout

| Path | What |
|------|------|
| `cerberus-heaplang/` | THE package: its own lakefile, README, ARCHITECTURE.md, docs/, and in-build axiom audit (Audit.lean, last import of the lib root) |
| `docs/` | dated records + `DECISIONS.md` (rulings register) |
| `scripts/` | `capped` (cgroup-capped builds), `test_unit.sh` (the gates), `new-worktree.sh`, `setup-cerberus-dep.sh` + `semantics-pin.env` (the pinned semantics workspace) |
| `worktrees/` | build-primed parallel checkouts (gitignored) |
| `../deps/iris-lean` | iris-lean checkout backing the Lake pin — read-only |
| `../cerberus-lean` | the semantics repo — read-only from here |

## Building

```bash
scripts/setup-cerberus-dep.sh                                   # once: the pinned semantics workspace
cd cerberus-heaplang && ../scripts/capped ~/.elan/bin/lake build # NEVER uncapped; elaborates the audit
scripts/test_unit.sh                                            # gates 1-2 (+ speedbump reports); --fast = the build only
```

Toolchain: Lean 4.32.2 (elan). Deps (batteries, Qq, iris) are
git-pinned in `cerberus-heaplang/lakefile.toml` and resolve offline
through the container's `deps/gitconfig` redirects (`capped`
self-loads the container env). `lake update` only with
`GIT_CONFIG_GLOBAL` set, and only to move a pin deliberately. The
semantics dependency is the pinned workspace `.cerberus-ws/lean_frontend`
(`scripts/semantics-pin.env`; re-pins are forced-semantics-change
slices, scouted first).

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
  ratification. Every auditor is briefed with `docs/AUDIT-BRIEF.md`
  (audits find substantive logical/coverage gaps in scope; hardening
  recommendations are graded down).
- Honest-gaps: unproved looks unproved; fail-closed, fail-noisy;
  stop-and-report over silent workaround.

## Trust rules (non-negotiable)

- **Kernel-only proof methods**: no `native_decide`/`bv_decide`/
  anything carrying `ofReduceBool`/`ofReduceNat`. `#guard` is a
  test, never "kernel-checked".
- **Exact axiom-cone assertions** in-build (Audit.lean): classical
  trio + declared boundary list only; boundary entries carry
  provenance (permanent-immovable or temporal-with-mover).
- **The referent of every export is the genuine semantics** ([USER
  2026-09-02]): no hand-written definition (driver loop, discharge,
  scheduler) may appear in the statement of an exported theorem;
  proof devices (the mirror, the collapse) live in proofs only. A
  semantics-side limitation that blocks such a statement is REQUESTED
  from the cerberus-lean team (a dated request note in `docs/`), never
  worked around; until it lands the affected exports are labelled
  PROVISIONAL on every surface.
- **Capped builds always**; heavy lanes serial on this shared box;
  commit promptly (kill-loss containment).
- **No grind campaigns**: a ~1hr pass is a stop-and-report event;
  the banned pattern is bulk terms at the kernel in place of
  structure.
- **Classical names only** for mechanisms; house jargon banned.
- Profile before perf design; perf plans discussed then
  adversarially reviewed before execution.
- **Speedbumps, not adversarial gates** ([USER 2026-09-02], DECISIONS):
  the trust base is the build + the in-build axiom sweep + the
  banned-methods grep; nothing else is a fail-closed gate. Every
  other check is a speedbump — a claim-point report that catches
  honest drift, never designed to survive adversarial attack, never
  a fast-tier blocker. New checks are welcome when high bang-for-
  buck (cheap, catches a real class of mistake); no giant
  enumerative tables unless a trust property is legitimately at
  risk. Over-elaborate gating is cut, not classified. Two tiers:
  `test_unit.sh --fast` (builds) for intermediate commits, the full
  run at claim points (phase exits, merge asks).

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
  outside-sandbox operator actions. `scripts/capped` is the
  cerberus-lean mainline script (cgroup-direct, bus-free mode,
  2026-09-01): it creates a sibling cgroup under app.slice and
  enforces the cap without systemd-run, so builds ARE capped in the
  sandbox. The 2026-08-29 interim "run uncapped in-sandbox" ruling
  is RETIRED ([USER 2026-09-02]); an uncapped-warning from `capped`
  again means a broken environment, stop and report.

## Current state

See `docs/DECISIONS.md` tail and `cerberus-heaplang/ARCHITECTURE.md` §7
(the acceptance-goals ledger). The RefinedC-family layer is on
`refinedc/dev`.
