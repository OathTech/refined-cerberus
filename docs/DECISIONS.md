# Decisions register

Append-only log of design rulings and their provenance. One entry
per ruling: date, [USER]/[AGENT] tag, the ruling, pointer to the
fuller record. CLAUDE.md is working practices ONLY and never logs
rulings ([USER 2026-08-29]: "CLAUDE.md isn't the right place for
logging design rulings" — the predecessor repo's CLAUDE.md became
an unreadable chronicle; this file is the fix). Full rationale for
the founding slate: `2026-08-29_rules-of-engagement.md`.

- **2026-08-29 [USER] Attachment layer**: instantiate the Iris
  program logic directly over Core; no Caesium-shaped intermediate.
  Preserves the ability to extend our reasoning.
- **2026-08-29 [USER] RefinedC is a target, not an end state**:
  steer hard at their design (coherent north star, reuse their
  design beats, no what-are-we-doing wars); extension beyond them
  only after parity.
- **2026-08-29 [USER] v1/reasoning-era designs are highly
  untrusted**: that route failed; nothing enters as design.
  Model-fidelity facts are leads only, re-verified against code.
- **2026-08-29 [USER] Proof quarry**: the cerberus-lean park
  branches carry substantial Lean proof text over Core — for
  concrete Core-wrangling obligations, search there before
  re-deriving; quarried material re-enters only where the
  RefinedC-targeted structure calls for it, re-verified in place.
- **2026-08-29 [USER] Frontend out of scope**: RefinedC's
  frontend/annotation layer is irrelevant to the core goal. Port
  target = program-logic lifting + type system + Lithium-style
  automation; specs/proofs authored in Lean natively.
- **2026-08-29 [USER] Semantics pin**: wait for
  `core/semantics-first` to land on the cerberus-lean mainline;
  pin the post-merge commit.
- **2026-08-29 [USER] Validation**: acceptance ladder = RefinedC's
  own examples/tutorial suite ("their proofs transfer"); the frozen
  15-program corpus is a secondary check once expressible, never a
  driver.
- **2026-08-29 [USER] Process**: arc/charter/orchestrator practices
  carry over; the convergence-era layered doctrine does NOT (each
  item re-earns its place). See rules-of-engagement §4–§6.
- **2026-08-29 [USER] Worktrees**: main is fine during arc-0 setup;
  thereafter arc branches in build-primed worktrees for parallel
  work.
- **2026-08-29 [USER] CLAUDE.md is working practices only**: design
  rulings live here, not there.
- **2026-08-29 [USER] THE NORTH STAR** (ratified verbatim from the
  metric/goal-collapse conversation): the product is a **Lean-native
  C verification framework** — RefinedC's architecture (ownership/
  refinement type system + Lithium-class goal-directed automation)
  rebuilt natively in Lean on iris-lean, attached directly to the
  cerberus-lean Core semantics, able to verify NEW C programs (specs
  and proofs authored in Lean, kernel-certified against the
  executable semantics, cost comparable to RefinedC's), extensible
  past their fragment toward the parent project's Linux-stack aim.
  Replay harnesses, transfer walls, and donor fidelity are
  MECHANISMS in service of this — each retired or demoted to a
  validation lane at parity, never reported as the product. (The
  house parallel: the OCaml differential oracle drove the semantics
  build and stayed a validation lane forever; replay is this port's
  OCaml oracle.) Binding instruments: (1) TWO LEDGERS — wall/replay
  metrics = the build ledger; the product ledger = a NATIVE
  VERIFICATION EXHIBIT at every arc close (a never-seen C program,
  in no donor corpus, verified end-to-end: Lean spec, our
  automation, trio cone); arc reports carry both, never conflated.
  (2) DISPOSITION-AT-INTRODUCTION — every scaffolding mechanism is
  born with a recorded disposition (dies-at-parity or
  demotes-to-validation-lane), decided at introduction; replay's
  disposition: demotes to a differential lane. (3) ENGINE-NOT-
  REPLAYER — the Lithium port is a free-running goal-solving
  engine; replay is a test harness AROUND it (feed their goal,
  compare outcomes), never a code path or mode INSIDE it. Carried
  into the Lane L charter as a design constraint.
- **2026-08-29 [AGENT] Arc-0 audit re-baseline**: the BI smoke
  lemma's axiom cone is empty (stronger than the trio bound); pinned
  as such at first build. Plant-test transcript in the arc-0 commit
  message (`a7ff8b0`).

## The attachment-targeting conversation (2026-08-29)

- **2026-08-29 [USER] TRUST ARCHITECTURE** (verbatim): "the
  cerberus-lean operational semantics is the ***only*** semantics
  that we trust. The relational semantics is a derived layer on top
  of it"; "we are going to build on top of the actual cerberus-lean
  operational semantics… This will be legitimately built on
  cerberus-lean, or it is off target"; "the intended end state of
  all of this is an adequacy result that can be stated *exclusively*
  over the cerberus-lean semantics… 'mirroring' without proof is
  valueless." Named failure mode: a pile of RefinedC machinery not
  coupled to cerberus-lean has no value regardless of donor
  fidelity. Consequences: any layer/engine disagreement is by
  definition a defect in the derived layer; no ported layer counts
  as capability until its downward theorem exists (adequacy spine
  load-bearing from rung one, never retrofitted); transfer-ladder
  rows count only when the proof discharges through the spine into
  an engine-only statement. Baked into CLAUDE.md header.
- **2026-08-29 [USER] Calls = substitution at the attachment
  layer**: substitution is reconstructed at the attachment layer and
  the environment disappears — keeps typed_function/wp_call literal.
  (Independently the failed prototype's final design conversation
  reached the same conclusion — corroboration, not justification.)
- **2026-08-29 [USER] Prototype relational-semantics work upgraded
  to DESIGN DONOR** for the derived-layer question specifically ("we
  may already have a design donor here") — evaluated on merits
  against the criterion sane / legitimate / scales-to-RefinedC;
  the untrusted-as-design default still governs everything else.
- **2026-08-29 [AGENT] Targeting calls** (each derived from ratified
  rulings; full statements in the port map §4 and the conversation
  record): (1) fragment referent = sequentialised Core, Eunseq out
  of fragment 1 [from "their sequentialized fragment first"];
  (2) atomics stubbed with temporal ledger row [sequential-first;
  ladder is gauge not goal]; (3) annotation payloads re-home to
  Lean-side spec/proof-script channels, annotation-fired rules
  become explicitly-invoked steps — a divergence CLASS whose forcing
  fact is the ratified frontend-out-of-scope ruling; (4) provenance
  referent = whatever the semantics pin runs; (5) allocation-failure
  stance follows the pinned engine's actual create behavior;
  (6) alignment recorded against the matching Caesium config;
  (7) wp/wp_det relational split ports unchanged; (8) adequacy shape
  mirrors theirs + an executable-layer corollary; (9) layouts/
  op_types, mem_cast dissolve-or-port, liveness ghosts, RA bundle,
  W-analog extent = fact-finding against the semantics, each ending
  in a ledger row. Pre-registered fallback on calls: if the
  substitution correspondence resists, an env-aware call rule as a
  ledgered divergence — no heroic grinding past its value.
- **2026-08-29 [AGENT] Statement-layer derisk plan** ([USER]
  prompted: "danger of doing violence to our goals… derisk the
  design"): empirical shape-correspondence study first (both
  pipelines executable, C as join key), then two candidate designs
  argued against the measured table under hostile review, then a
  vertical spike with pre-registered kill criteria. Evidence:
  `docs/2026-08-30_caesium-core-shape-study.md` (finding: sharp
  statement-position grammar; control flow near-bijective via
  save/run; shared Ail ancestry; bind layer dissolves by grammar;
  divergences: pattern-shaped correspondence with inline UB
  templates, per-iteration locals lifetime).
- **2026-08-30 [AGENT] Relational-layer candidates memo delivered**
  (`docs/2026-08-30_relational-semantics-candidates.md`, written
  under the trust-architecture rulings): recommends the HYBRID —
  the prototype's proved per-step spine (two-sided runner
  characterization + engine-only adequacy path) as the trunk,
  syntactic per-construct characterization lemmas grown on it as
  the WP layer; pre-registered falsification probe (two exemplar
  lemmas at ∀-configuration). NOT yet ratified — hostile review
  pending. New facts of record: the Lean pipeline never calls
  Core_sequentialise (verified: zero callers; test_exec.sh notes
  it) → realizing the sequentialised fragment needs Lean-side
  wiring + a validation lane, [USER] decision pending (cross-repo);
  the trimmed relsemcore spine (runND_sound) survives
  core/semantics-first; finalize runs a second evaluator
  (Driver.hack) → result postconditions need a characterization
  lemma family.
- **2026-08-30 [AGENT, prompted by USER: "Do we actually need to
  sequentialize?"] Sequentialisation is NOT needed — fragment 1 =
  non-sequentialised Core, exactly as the validated engine runs it.**
  Supersedes the earlier item-17 call (sequentialised referent).
  Evidence (`docs/2026-08-30_eunseq-census.md`): 98 Eunseq nodes /
  201 arms across 23 files — 92% of arms read-only+pure; a store
  NEVER occurs as an arm (assignment stores are sequenced after the
  unseq join); everything reduces to 4 templates + one rmw variant;
  Eunseq never spans statements; the save/run skeleton is invariant
  under the pass (token-level proof the pass touches only unseq
  nodes). The Eunseq proof rule is SHARED READS / DISJOINT WRITES
  (fractional-permission separation — classical lineage; full
  pairwise disjointness is unsatisfiable on ordinary C since
  read-read overlap is ubiquitous), whose side condition literally
  mirrors the engine's own join-time race criterion (`overlapping`,
  CerbMem.lean:1186 = impl_mem.ml:527-532 — the rule's premise IS
  the engine's check). Calls are a second ATOMIC rule shape: the
  engine's Eccall step makes callee bodies atomic w.r.t. sibling
  arms (core_reduction.lem:1347-1368), so no interleaving reasoning.
  Consequences: the cross-repo Core_sequentialise wiring + lane
  drops from the queue entirely; the attachment layer owes the
  one-time unseq-rule meta-theorem; the port becomes strictly more
  honest than RefinedC and CN on unsequenced-race UB (both miss the
  class). [USER] veto point: this flip is evidence-based but stands
  as an [AGENT] call until seen.
- **2026-08-31 [USER] The spike becomes cerberus-heaplang**:
  restructured as a standalone demo Lean development alongside the
  future RefinedC port ('Cerberus-heaplang'); the RefinedCerberus
  root package is reserved for the port; the runEffectful boundary
  lives only in the demo's audit, with upstream retirement planned.
  Mechanics + re-run plant-test transcripts:
  `cerberus-heaplang/docs/2026-08-31_restructure-notes.md`.
- **2026-08-31 [USER] The heaplang end state + two-phase arc**:
  end state = "a tiny separation logic (really just
  reynolds/ohearn) over a synthetic fragment of core. So not at all
  RefinedC, but it'll derisk a lot of the fundamental machinery."
  Base logic = partial correctness (donor parity); termination
  measures = optional variant layer producing step bounds that
  upgrade to the unconditional production equation. Phase 1
  restratifies coverage-preserving (frozen-corpus regression gate;
  S0 jump-kernel probe first); phase 2 extends (loops/branches/
  invariants; fib + list-reverse acceptance). [USER]: run on the
  branch without check-in until P2 works or a blocker needs
  discussion. Plan:
  cerberus-heaplang/docs/2026-08-31_two-phase-arc-plan.md.
- **2026-08-31 [USER] Array pre-state ruling**: the one-allocation
  array (single cell, per-element structure in invariants/decode
  premises) is RATIFIED — "this is I think the only way this example
  can work in C!" Forcing fact: Cerberus provenance (arithmetic-
  derived pointers must stay in-allocation; loaded pointers carry
  their own rights); donor-aligned (Caesium's array is one block
  with element views). Supersedes the amendment's literal per-cell
  big-sep phrasing; first-class element ownership remains the
  registered sub-allocation-view growth step (structs/arrays as
  type formers in the port).
- **2026-08-31 [USER] Demo-first ruling**: "we're going to get
  cerberus-heaplang right, we're not kicking off refinedC until
  this is perfect." The foundational audit (F-01..F-10,
  orchestrator-verified) is adopted in full: its phase structure
  and 8-test acceptance suite become the foundations arc
  (cerberus-heaplang/docs/2026-08-31_foundations-arc-plan.md); the
  RefinedC port is gated on the arc's fresh re-audit returning no
  High findings. Supersedes the orchestrator's proposal to fold
  F-03/F-04 remediation into the port kickoff.
- **2026-08-31 [USER] Foundations arc run authorization**: "launch
  it on a branch. You can run long-cycle on this, get it done and
  then we'll check in" — phases proceed sequentially on the branch
  without per-phase pauses; the check-in is at arc end (acceptance
  suite + fresh re-audit). The Phase-1 design-decision record is
  still written operator-visible in the arc docs but does not
  block.
- **2026-08-31 [USER] The substitution ruling DOWNGRADED + the
  rulings-skepticism discipline**: "I don't feel strongly about args
  by substitution (that might have been inherited from the failed
  reasoning project). I think you should be a bit skeptical /
  careful about things I've 'ruled'." The 2026-08-29
  calls-by-substitution ruling is downgraded to an OPEN QUESTION:
  gathered evidence already contradicts it (the env is live state in
  the language tuple; the engine's call protocol binds args via
  bindArgs into the env, not substitution — the mirror follows the
  engine). The logic-level shape (env-aware call rule with a
  Cerberus forcing fact vs a substitution-facade with an env≈subst
  correspondence) is settled empirically by the future calls-arc
  probe with pre-registered criteria. Standing discipline: [USER]
  tags fix PROVENANCE, not truth — values/goals rulings are fixed
  points; technical rulings are revisitable claims, with
  evidence-conflicts surfaced for re-adjudication and failed-era
  "corroboration" screened as a contamination vector.
- **2026-08-31 [USER] Direction: the calls arc** (post-foundations):
  grow the miniature logic with function calls and specs, "derisk
  all the crux points… creep up on refinedC step by step"; flagship
  = recursive fib (partial, then total via the measure-across-calls
  layer). Prerequisites are foundations Phases 1-3 outputs.
- **2026-09-01 [USER] The independent skeptical re-audit adopted; the
  allocation arc**: the operator's independent audit found two
  Criticals the fresh re-audit and all five gates missed — R-01 the
  stranded create rule (cursorOwn never launchable), R-02 allocating
  production exhibits bypassing the logic with operational traces —
  root-caused to R-04: every coverage instrument validated
  DECLARATIONS AND NAMES, NOT PROOF FLOW. The 2026-09-01 foundational
  re-audit is struck as the acceptance record. [USER] "Go ahead":
  P0-P7 adopted verbatim as the allocation arc
  (cerberus-heaplang/docs/2026-09-01_alloc-arc-plan.md wrapper),
  long-cycle on branch heaplang-alloc-arc. Standing lesson entering
  house practice: coverage/closure claims require DEPENDENCY-CONE
  verification (launch → resource → rule → consumer), never
  name-level checks; re-audits trace proof flow.
- **2026-09-02 [USER] SPEEDBUMPS, NOT ADVERSARIAL GATES** (verbatim):
  "our aim here is to build a relatively small Reynolds/O'Hearn style
  logic, so if we're building over-elaborate gating, that should be
  cut fairly brutally. We *do not* want to build heavy gates that are
  intended to survive adversarial attack, we want to build
  speedbumps." Also [USER 2026-09-01]: gate cruft (over-strong gates
  accumulating) is a project-slowing defect; ACL2Lean's two-tier
  gating is the model. CONFLICT SURFACED AND RESOLVED: the adopted
  skeptical re-audit's P3 prescription (dependency-certified
  consumers, layer-cut check, plants retained as gates) is
  adversarial-grade gating — the ruling supersedes it (the audit is
  a claim; the aim is the operator's). Disposition: the trust base
  stays (banned-methods grep + the builds with the in-build axiom
  sweep = the proofs); P3's 1,507-line generator is CUT to a ~300-
  line claim-point SPEEDBUMP REPORT (cone-derived rows + the one
  discriminating rule-in-consumer-cone check that caught real
  overclaims); the layer cut, production staging, execution witness,
  accumulating machinery, plant-gates, and gate 5 (census freeze —
  redundant with committed signature snapshots) are removed.
  Executed as slice 0 of the restart, before the retirement re-pin.
- **2026-09-02 [USER] P3.5 — CUT THE CRUFT; THE STANDING AUDITOR BRIEF**
  (verbatim): "I think this is on me for not briefing the auditor
  correctly. We want to build the core logic to be well-designed and
  minimal, and we want to close ALL substantive logical and coverage
  gaps wrt our scope. We do not want to make everything insanely
  hardened against all possible attacks, that's out of scope and will
  slow us down enormously. You can cut the built up cruft from this
  and elsewhere, and log this decision so the next auditor sees the
  brief. This can be P3.5 - delete the junk here and elsewhere in the
  project. We want this to be a reasonable set of gates sized
  proportionate to the demo-level work we're doing and consistent
  with moving fast. The actual logic itself must be pristine, enough
  to make Reynolds and O'Hearn weep with joy. The rest just needs to
  be sufficient". Standing brief for every future auditor:
  `docs/AUDIT-BRIEF.md`. P3.5 inventory + plan: the resume note
  (`docs/2026-09-02_resume-note.md`), executed as the restart's first
  slice, before the retirement re-pin.
- **2026-09-02 [USER] REFINEMENT — new checks are allowed, bang-for-buck
  is the test** (verbatim): "We don't want to quite go so far as to
  say we should never add a new check. But a gate should be high bang
  for buck. No giant enumerative tables unless we are actually
  legitimately worried about trust". Applied to AUDIT-BRIEF.md and the
  P3.5 plan: the manifest's hand-maintained multi-cell row table (~340
  lines) is cut to one line per construct; new checks are welcome
  when cheap and catching a real class of mistake.
