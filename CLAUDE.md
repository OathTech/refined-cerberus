# refined-cerberus

A port of the RefinedC reasoning system (Coq: Lithium + type system)
onto the Cerberus C semantics, via the cerberus-lean Lean 4 port,
with iris-lean as the intermediate program logic.

This file is the OPERATING MANUAL. The full decision record with
rationale is `docs/2026-08-29_rules-of-engagement.md` (blessed).
Dated docs in `docs/` are the record; decisions carry [USER]/[AGENT]
provenance. Predecessor-effort history lives in the cerberus-lean
repo (park branch `arc/segment-ladder`,
`lean_frontend/docs/reasoning-era/POSTMORTEM-AND-FORWARD-BRIEF.md`
— read it before touching design).

## Mission and shape [USER 2026-08-29]

- **Instantiate the Iris program logic directly over Core.** No
  Caesium-shaped intermediate layer.
- **RefinedC is a TARGET, not an end state.** Steer hard at their
  design (coherent north star, reuse their design beats); extension
  beyond them comes only after parity.
- **The predecessor reasoning-era designs are HIGHLY UNTRUSTED**
  (that route failed). Reasoning-era *model-fidelity facts* (claims
  about Cerberus/Core itself) are leads only — re-verify against
  the actual code before use. No mechanism is justified by "v1 did
  it".
- **The park branches are a PROOF QUARRY** [USER 2026-08-29]:
  several branches carry blobs of Lean proving properties over Core
  (`arc/segment-ladder`, `arc/t5-seal`, tags `park/*` in
  cerberus-lean) — "there's a good chance we have nearly the
  reasoning we want somewhere in the repo, for any given bit of
  core wrangling." When a concrete Core-wrangling obligation comes
  up (step lemmas, inversions, totality facts, term manipulation),
  SEARCH THE QUARRY before re-deriving. Quarried proofs are raw
  material, not design: they re-enter only where the
  RefinedC-targeted structure calls for them, re-verified in place.
- **RefinedC's frontend/annotation layer is OUT OF SCOPE.** Port
  target = program-logic lifting + type system + Lithium-style
  automation. Specs and proofs are authored in Lean natively.
- Partial correctness first; RefinedC's evaluated/sequentialized
  fragment first.

## The referent discipline (the core rule)

- `deps/refinedc` (BSD, in the container) is the **normative spec**
  for everything above the semantics: judgment forms, typing rules,
  Lithium's algorithm. Design questions are answered by reading
  their code.
- **The PORT LEDGER is the central artifact**: every ported
  judgment/rule/type-former/tactic carries a donor citation
  (file:line); every divergence carries a forcing fact **about
  Cerberus** (never about our Lean port's internals), binned:
  (a) unnecessary invention → adopt theirs; (b) real Cerberus
  constraint → forcing fact stated; (c) inherited pseudo-constraint
  → named and priced, never hidden in (b). Operator adjudicates.
- **The attachment layer (Iris-over-Core) is the ONE sanctioned
  design zone.** Its scope is decided in operator conversation
  before any brief. Acceptance question for every choice there:
  "does this let RefinedC's next layer port literally?"

## Dependencies

- Strictly one-way: refined-cerberus → cerberus-lean (semantics),
  → iris-lean. Nothing in cerberus-lean references this repo.
- Lake deps resolve to local checkouts via
  `GIT_CONFIG_GLOBAL=<container>/deps/gitconfig` (insteadOf
  redirects; never installed globally). Mirrors in
  `<container>/deps/mirrors/`.
- Semantics pin [USER 2026-08-29]: WAIT for `core/semantics-first`
  to land on the cerberus-lean mainline, then pin the post-merge
  commit. Pins bump deliberately (pin-dance discipline).

## Process

- **Arcs with charters**, DRAFT until [USER]-blessed.
  Orchestrator/worker: exact scoping, park-don't-improvise, workers
  commit their own green slices, orchestrator independently
  re-verifies gates at boundaries; quoted outputs verbatim, derived
  tallies labeled. **Park-ends-slice**: a committed park record
  stops the work.
- **Branches + ff-only merges** on explicit per-merge [USER]
  sign-off; the pre-merge audit ask is unconditional. No commits on
  main after arc-0 scaffolding ([USER 2026-08-29]: main is fine
  during setup; thereafter arc branches in WORKTREES —
  `scripts/new-worktree.sh <branch>` creates a build-primed one
  under `worktrees/` (gitignored) — so parallel streams never
  collide on the primary checkout).
- **No design pass dispatched before its scope is discussed with
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
- **Exact axiom-cone assertions**: classical trio + declared
  boundary list only (permanent = immovable objects; temporal =
  expected mover), build-failing.
- **Capped builds always** (cgroup wrapper; this box OOMs
  uncapped); heavy lanes serial; commit promptly.
- **No grind campaigns**: ~1hr pass = stop-and-report; the banned
  pattern is bulk terms at the kernel in place of structure.
- **Classical names only** for mechanisms; house jargon banned.
- Profile before perf design; perf plans discussed then
  adversarially reviewed before execution.
- Gates minimal: axiom cones + kernel-method ban + the build. New
  gates only for load-bearing TRUST properties (anti-gate-grind).
  The convergence-era doctrine/gate apparatus is deliberately NOT
  imported (see the decision record §6).

## Validation [USER 2026-08-29]

- **Acceptance ladder = RefinedC's own examples/tutorial suite**
  (BSD): the gauge is "their proofs transfer."
- Semantics differential lanes (in cerberus-lean) stay ground truth
  at the adequacy boundary.
- The frozen 15-program corpus: secondary check once expressible,
  never a driver.

## Machine etiquette

- No machine-global state (see the user-global rules); no pushes
  without explicit per-push sign-off.
- Other agents work in sibling directories of the container: this
  effort writes ONLY inside `refined-cerberus/`; the rest of the
  container is read-only reference.

## Building

```bash
scripts/capped ~/.elan/bin/lake build   # NEVER uncapped; runs the in-build audit
scripts/test_unit.sh                    # grep ban + capped build
```
Toolchain: Lean 4.32.2 (elan). Deps (batteries, Qq, iris @ 34390a0
subDir Iris) resolve offline through the container's deps/gitconfig
(capped self-loads it via the container env.sh). `lake update` only
with `GIT_CONFIG_GLOBAL` set, and only to move a pin deliberately.

## Current state (2026-08-29)

- Arc 0 scaffolding DONE except the semantics pin: rules blessed,
  manual landed, Lake skeleton + iris-lean wiring green (full stack
  builds: 303 modules), BI proof-mode smoke lemma proved (empty
  axiom cone, pinned), in-build axiom sweep + curated pins live and
  plant-tested (sorry-plant went red, revert went green),
  new-worktree helper in place. PENDING: cerberus-lean dependency —
  waits on the `core/semantics-first` mainline landing, then pin +
  re-gate.
- Arc 1 next: the port map — read-only recon of deps/refinedc
  (layer map, typing-rule inventory, Lithium algorithm note) →
  agenda for the attachment-layer scope conversation.
