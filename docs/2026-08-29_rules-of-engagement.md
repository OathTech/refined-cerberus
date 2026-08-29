# Refined-Cerberus: rules of engagement

**Status: BLESSED [USER 2026-08-29] — all decision points ratified
(the §7 validation pair by explicit "(1) agree, (2) agree").
CLAUDE.md is the operating-manual form of this document; this file
is the decision record.**
Proposed by the orchestrating agent 2026-08-29, at operator direction
("we want arc / charter / orchestrator practices. But we want to be
fairly skeptical of the more detailed things which were layered over
as we tried to get the design to converge").

Input documents: the reasoning-era postmortem
(`cerberus-lean` park branch `arc/segment-ladder`,
`lean_frontend/docs/reasoning-era/POSTMORTEM-AND-FORWARD-BRIEF.md`)
and the operator rulings of 2026-08-29 (this conversation).

---

## 0. Ratified orientation (operator, 2026-08-29)

- **Attachment layer**: instantiate the Iris program logic (iris-lean)
  **directly over Core**. No Caesium-shaped intermediate. Rationale:
  keeps the ability to extend our reasoning.
- **RefinedC is a TARGET, not an end state.** We steer hard at their
  design to keep the north star coherent and reuse their design beats
  — avoiding the constant what-are-we-doing wars of the failed era —
  but the port is allowed to grow past them once parity is real.
- **RefinedC's frontend/annotation layer is OUT OF SCOPE** —
  "irrelevant to our core goal." The port target is the logic:
  program-logic lifting + type system + Lithium-style automation.
  Specs/proof artifacts are authored in Lean natively (the
  AI-driven-proof orientation; reach parity, not interface parity).
- **The v1 experiments are HIGHLY UNTRUSTED.** That design route
  failed. Nothing from the reasoning era enters this repo as a
  design. Distinction: reasoning-era *model-fidelity facts* (claims
  about Cerberus/Core itself, e.g. engine-of-record, label
  resolution, PVI) are admissible as *leads*, each re-verified
  against the actual code before use.

## 1. Repo and dependency shape

- `refined-cerberus` is a standalone repo. Dependency is strictly
  one-way: refined-cerberus → cerberus-lean (the semantics) and
  refined-cerberus → iris-lean. Nothing in cerberus-lean ever
  references this repo.
- Lake deps resolve to the local checkouts via the established
  `GIT_CONFIG_GLOBAL=deps/gitconfig` insteadOf pattern (offline,
  never machine-global). Mirrors already exist for iris-lean and
  refinedc.
- The semantics is consumed at a **pinned commit**, bumped
  deliberately (the two-repo pin-dance discipline, adapted).
- [USER 2026-08-29] Semantics pin: `core/semantics-first` "should
  land on cerberus quite soon, we'll just work from there" — we
  WAIT for its audited merge to the cerberus-lean mainline and pin
  the post-merge commit. Until then no semantics dependency is
  wired; arc-1 (below) needs no semantics build.

## 2. The referent discipline (the core rule of the retrofit)

This single rule replaces most of the accreted statement/spec
doctrine of the failed era:

- **RefinedC's Coq development (`deps/refinedc`, BSD) is the
  normative spec** for everything above the semantics: judgment
  forms, the typing rule set, Lithium's algorithm, automation
  structure. Design questions are answered by reading their code.
- **The PORT LEDGER is the central artifact.** Every ported
  judgment, rule, type former, and tactic carries a donor citation
  (file:line into deps/refinedc). Every divergence carries a
  **forcing fact**, and the forcing fact must be about *Cerberus*
  (Core's meaning, ISO obligations) — never about our Lean port's
  internals. Divergences are binned per the anti-innovation ruling:
  (a) unnecessary invention → adopt theirs; (b) real Cerberus
  constraint → forcing fact stated; (c) inherited pseudo-constraint
  (traces to our own prior choice) → named and priced, never hidden
  in bin (b). The operator adjudicates the ledger.
- **Target-not-end-state, sequenced:** parity first, extensions
  after. Pre-parity, "we can do better than RefinedC here" is a
  ledger note, not a license. The one standing exception is the
  attachment layer (§0), which has no RefinedC counterpart to copy.
- Strict-retrofit consequences (postmortem, operator-set): partial
  correctness first; their evaluated/sequentialized fragment first.
- Scope [USER 2026-08-29]: frontend/annotation layer excluded (§0);
  "normative" applies to theories/{lithium,typing} and Caesium's
  *role*; frontend/ and the annotation grammar are not port rows.

## 3. The attachment layer: the one sanctioned design zone

The Iris-over-Core instantiation is the only place we design rather
than port. Containment rules for it:

- Its scope is decided in **operator conversation before any brief**
  (the twice-learned rule). Arc-1's port map produces the agenda for
  that conversation; nothing is dispatched ahead of it.
- It is built to *serve the target*: the acceptance question for
  every attachment-layer choice is "does this let RefinedC's next
  layer port literally?" — not "is this elegant."
- Reasoning-era artifacts may be consulted as reconnaissance only;
  any fact relied on is re-verified against the semantics code
  first, and any *mechanism* proposed must be re-justified from the
  donor or the literature (classical names), never by "v1 did it".

## 4. Process kept: arc / charter / orchestrator (operator-ratified)

- Work runs in **arcs with charters**; charters are DRAFT until the
  operator blesses them. Dated docs in `docs/`; the repo is the
  record; decisions logged with [USER]/[AGENT] provenance.
- **Orchestrator/worker**: exact scoping, park-don't-improvise,
  workers commit their own green slices, orchestrator independently
  re-verifies gates at boundaries (worker-claimed green is never
  accepted), quoted outputs verbatim, derived tallies labeled.
- **Park-ends-slice**: a committed park/frontier record stops the
  work; pushing past it needs orchestrator approval.
- **Branches + ff-only merges** on explicit per-merge [USER]
  sign-off; the pre-merge audit ask is unconditional; no commits on
  main except establishing scaffolding in arc-0 (proposed below).
- **No design pass is dispatched before its scope is discussed with
  the operator.** A brief is a bundle of decisions, not a substitute
  for the conversation.
- **Fresh-eyes full reviews** on core documents at major revisions —
  never same-reviewer delta convergence. Hostile adversarial review
  before any ratification.
- Honest-gaps principle: unproved things look unproved; fail-closed,
  fail-noisy; stop-and-report over silent workaround.

## 5. Trust rules kept (non-negotiable, imported verbatim)

- **Kernel-only proof methods**: no `native_decide`, no `bv_decide`,
  nothing carrying `ofReduceBool/ofReduceNat`; `#guard` is a test,
  never "kernel-checked".
- **Exact axiom-cone assertions**: classical trio + a declared
  boundary list only; boundary entries are permanent (immovable
  objects) or temporal (with expected mover); build-failing.
- **Capped builds always** (the cgroup wrapper pattern; this box
  OOMs the uncapped); heavy lanes serial; commit promptly.
- **No grind campaigns**: ~1hr build/proof pass = stop-and-report;
  the banned pattern is bulk terms at the kernel in place of
  structure; long construction of real content is fine.
- **Classical names only**: every mechanism named from the
  literature (abstraction, memoization, sharing, reflection, data
  refinement…); un-nameable mechanisms are presumptively hacks;
  house jargon banned.
- Profile before designing performance fixes; perf plans discussed
  before dispatch and adversarially reviewed (scaling is where
  forbidden hacks historically crept in).

## 6. Deliberately NOT imported (the skeptical set)

Layered convergence-era machinery, dropped unless a concrete need
re-earns each item:

- The harness-statement template / choice-stream spec doctrine /
  statement-slate machinery — RefinedC's own spec forms (typing
  judgments, function specs) are the spec discipline here.
- The frozen-corpus freeze gates and hash manifests — see §7 for
  what replaces the corpus's role.
- The accreted gate zoo. Starting gate set is minimal: axiom-cone
  assertions, the kernel-method grep ban, and the build itself.
  Gates are added only for load-bearing **trust** properties
  (anti-gate-grind ruling); discipline points get documentation and
  structurally-forcing examples, not gates.
- Scheduled professor cadences, the cargo-cult checklist apparatus,
  the down-pressure registers. The *instrument* survives —
  adversarial fresh-eyes review, deployed at orchestrator
  discretion and pre-merge — without the standing apparatus. The
  ledger's donor-citation requirement is itself the main structural
  defense against per-instance-rule-in-costume disease.
- Every reasoning-era design artifact (V1 state decomposition,
  segment rules, mechanism C, seg_discover, …): reconnaissance
  only, per §0/§3.

## 7. Validation referents

- [USER 2026-08-29] **RefinedC's own examples/tutorial suite (BSD)
  is the acceptance ladder** — the retrofit's gauge is "their
  proofs transfer." This is the gauge-failure fix: the instrument
  measures the target itself.
- The semantics repo's differential lanes remain ground truth for
  everything at the adequacy boundary (unchanged, lives there).
- [USER 2026-08-29] The frozen 15-program corpus: **secondary
  check** once the port can express it, not a driver. (Its specs
  were shaped by the failed era's doctrine; the programs are still
  good C.)

## 8. Proposed first arcs

- **Arc 0 — scaffolding (S)**: Lake project skeleton; pins +
  gitconfig wiring; smoke build importing iris-lean (and the
  semantics once §1's pin decision lands); the minimal gate runner
  (axiom cones + kernel-method ban); CLAUDE.md operating manual =
  the blessed version of this document. Commits on main are
  legitimate for this arc only (empty repo, establishing record).
- **Arc 1 — the port map (M, read-only recon)**: systematic read of
  deps/refinedc (ARCHITECTURE.md, theories/lithium, theories/typing,
  theories/caesium's *role*) producing: the layer map
  (what-plays-Caesium's-part = Core + attachment layer), the typing
  rule inventory (the ledger's row list), a Lithium algorithm note,
  and the agenda for the attachment-layer scope conversation. This
  is grinding against an existing surface — the documented strength.
- **Then**: the attachment-layer conversation (§3) → its charter →
  build.

## 9. Machine etiquette (standing, from the container rules)

No machine-global state; no pushes without explicit per-push
sign-off; other agents work in sibling directories — this effort
writes **only inside `refined-cerberus/`** and treats the rest of
the container as read-only.
