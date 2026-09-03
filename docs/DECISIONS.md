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
- **2026-09-02 [AGENT] THE TAG-DEFINITION ENVIRONMENT IS A PARAMETER OF
  THE LANGUAGE INSTANCE (the retirement re-pin's second change)**
  (coordinator adjudication, verbatim): "The C1 reader-consumer
  threading makes the tag-definition environment an explicit leading
  `TagDefs` argument on the memory functions (sizeofCtype,
  memValueToBytes, reconstructValue, loadM, storeM, allocateObject,
  alignofIval, arrayShiftPtrval, isAtomicMemberAccess) and a
  `_lemReader_tagDefs` binder in the Driver actions. cerberus-heaplang
  adopts option (a): the tag environment is a program-wide constant of
  the language instance (as Caesium's global environment is in
  RefinedC), so the heap predicates whose footprints depend on type
  layout are indexed by it, and the rules generic in a MachineCtx
  supply `M.tagDefs`. Rejected: (b) pinning `fmapEmpty` throughout
  with a `M.tagDefs = fmapEmpty` premise — a representation accident
  of the kind [USER 2026-09-02] asked to forbid, and it forecloses
  struct types; (c) a scalar-only independence lemma — a bridge to
  (b). The tag environment is recorded as a parameter of the language
  instance for the parametric-semantics spike (branch
  parametric-spike)." Operator veto open. Implementation note [AGENT
  2026-09-02, worker]: the state interpretation must remain a plain
  Iris instance (`StateInterp Mem Empty GF` is synthesized by type
  class, so it cannot take the environment as an explicit argument);
  therefore the ghost METADATA cell records the allocation's `size` as
  ghost data — the engine's own `Allocation.size`, Caesium's
  `allocation` start/len shape — and the coupling invariant `CohG`
  computes no layout, while the assertions (`pointsToCell tds …`,
  `cellOwn`, `pointsToView`, `StorableAt`, `CellCoh`, `Sat`, …) carry
  `tds` explicitly and pin `size = sizeofCtype tds ty`. The concrete
  profile contexts `spikeCtx`/`procCtx`/`rsCtx` are `@[reducible]` so
  the clients' `fmapEmpty` matches the rules' `M.tagDefs` under the
  proof mode. Record: `cerberus-heaplang/docs/2026-09-02_repin-notes.md`.
- **2026-09-02 [AGENT] R-11 / P7 CLOSED — the runEffectful boundary is
  retired**: semantics pin 58ec50779 → ddcfc919972a31bc43a0454e6b2e76a19e6c4594
  (the cerberus-lean effect-retirement head; LemLib 045dcb0, zero
  axioms). Audit.lean's boundary allowance is deleted; every export
  and every theorem of every module is pinned/bounded by the classical
  trio, exactly. The production-entry statements quantify over the
  supply-threaded entry's supply ([USER 2026-09-02], resume note
  Slice 1). Record: `cerberus-heaplang/docs/2026-09-02_repin-notes.md`.
- **2026-09-02 [USER] ONE CHANGE AT A TIME; REYNOLDS/O'HEARN IS THE STABLE
  SPEC** (verbatim): "during our design exploration we should try to
  'change one thing at once' - the nice thing about aiming for
  Reynolds/O'Hearn is it's a very stable and clean design target. We
  can then build to this spec with different internals and get the
  design right. Whereas if we're working on RefinedC the design is more
  complex and we need to do more adaptations". Applied: every slice is
  exactly one of — forced semantics change (pin moves), spec addition
  (new rules/statements), internals refactor (public statements frozen,
  verified by identical pre/post `scripts/signature_snapshot.lean`
  output), or RefinedC-shaped adaptation (last). Never two in one slice.
- **2026-09-02 [AGENT] PARAMETRIC-SEMANTICS SPIKE DISPATCHED** on the
  operator's question ("make the logic parametric in its underlying
  semantics ... a kind of parametricity property (analogous to
  'theorems for free')"; [USER]: "this would be a parallel spike"):
  read-only, branch `parametric-spike`, deliverable
  `cerberus-heaplang/docs/2026-09-02_parametric-semantics-spike.md`
  (measured inventory: 44 of 76 rule proofs unfold `Step` by
  definition; 17 touch ghost/cursor internals; 14 clean; the donor
  proves memory rules by inversion, Iris-style parametricity is
  control-only in RefinedC; memory interface = 7 laws all already
  lemmas; control mixin not an `EctxLanguage` instance because `Erun`
  discards its context).
- **2026-09-02 [USER] PARAMETRIC INTERFACES NOT ADOPTED — EXPERIMENT,
  DEFERRED POSSIBLY PERMANENTLY** (verbatim): "I'm uncertain whether to
  adopt this. I feel like abstractions should do some work for us.
  There's nothing especially wrong about proving the proof rules
  correct wrt the semantics directly, it just means that the proof
  discipline is a bit harder to enforce. How much does this actually
  buy us?" — orchestrator assessment: modest (same proofs relocated
  behind a one-instance class; zero proof economy; the enforcement gap
  is catchable by a report line); [USER]: "this should land on main
  with a clear note at the top level that it's an experiment and that
  we've deferred it, possibly forever." Disposition: the note carries
  the DEFERRED banner; the rules stay proved directly against `Step`
  and the memory state, as the donor does; `scripts/parametric_inventory.lean`
  is kept as an on-demand instrument (its representation-reference
  counts are the candidate speedbump line). Re-open triggers: a second
  memory-model instance, or a type layer needing an abstract memory
  contract. Pointer: cerberus-heaplang README "Deferred design experiments".
- **2026-09-02 [AGENT] ALLOC ARC P4 CLOSED — R-05, R-06, R-08, R-09 (the
  raw separation-logic API closure)**, a SPEC-ADDITION slice under the
  one-change-at-a-time ruling: (P4.1) THE THREE ALLOCATION FACTS —
  linear/fractional bytes (`bytesOwn_fractional`/`_agree`), PERSISTENT
  allocation knowledge (`allocMeta`/`locInBounds` = the metadata cell at
  the discarded fraction; `Persistent` instances are the persistence law;
  `pointsToView_persist`, `pointsToView_locInBounds`), and NO liveness
  token (metadata immutability documented in Heap.lean's header; the
  bundles keep the metadata at a fraction because full metadata is the
  exclusivity anchor `bigSepM_own_disjoint` needs — a named divergence
  from the donor's killable `alloc_alive`); the view/points-to laws
  (`pointsToView_fractional`/`_agree`, `pointsToCell_fractional`/
  `_agree`/`_combine`), the provenance-preserving shift
  `cellPtr_arrayShift`, `wps_fupd`, the PUBLIC single-cell readouts
  (`cellOwn_readout`/`pointsToCell_readout`); every advertised view law
  has a StructExhibit client. (P4.2) statement-level framing at both
  strata (`frameLs`/`frameLsT`, `wps_frame_labels`/`wpt_frame_labels`,
  `blockSpecs(T)_frame`, `wps_sound_frame`, `wpt_frame`); `RF` removed
  from the list/tree invariants, the framed theorems DERIVED. (P4.3)
  LoopExhibit on `SymFrame` with irrelevant-binding tests (incl. the
  engine-level `counter_loop_certified_irrelevant_binding`);
  `SemTripleU` over any `MachineCtx` + entry environment with
  `SemTriple` its proved instance (`SemTriple_iff_U`) — generalization
  chosen over the rename because the statement is clean and the proofs
  are the existing adequacy composed with the readout. Definition of
  done measured by `scripts/parametric_inventory.lean` (client-module
  section, new): Array/Struct/ListRev/TreeRot/Loop at ZERO direct
  references to the ghost maps/CohG/cursor, the engine transition and
  the judgment internals (before: 4 offenders). Not added, by the
  no-consumer rule: `wpt_sound_frame`. Record:
  `cerberus-heaplang/docs/2026-09-02_p4-notes.md` (spec diff, inventory
  before/after, gate tail); signatures pre/post committed alongside.
- **2026-09-02 [USER] FEATURE SET FROZEN UNTIL QUALITY IS STRONG; THEN THE
  AUDIT ROUND; THEN CALLS + MALLOC/FREE** (verbatim): "the feature set
  is frozen while we get this to a really strong state just in terms
  of quality. But after that we're doing call/compositional reasoning
  + malloc/free which will cover the entire Reynolds/O'Hearn logic I
  think. Before then we're going to do another audit round so we might
  find other areas for improvement first." Orchestrator's tracking
  assessment (same day, on request): all four goal parts met at
  fragment scope — a Reynolds/O'Hearn logic (minus dispose and
  procedures), over real Core, genuinely on iris-lean, with every
  export's axiom cone the classical trio and the closed-program
  statements ending at the shipped `runND ∘ drive ∘ initial_driver_state`.
- **2026-09-02 [USER] TWO TRUST CLAIMS — iris-lean is BELOW THE LINE for
  the closed-program exports**: "I guess iris-lean is in the trust base
  via the specification idiom? But we could prove adequacy for closed
  programs without any specification without iris-lean (i.e the proof
  machinery is not in the trust base)". Agreed and adopted as the
  trust-story structure (P6 requirement): (1) the closed-program
  exports have Iris-free statements — cerberus-lean's semantics as the
  referents plus the pure readout predicates (`Sat`/`CellCoh`); iris-lean
  appears only inside kernel-checked proof terms and contributes no
  axiom, so it is checked, not trusted; (2) the reusable rules are
  stated in Iris assertions, whose must-read set (the specification
  idiom: `pointsToCell`, `CohG`, iris-lean's WP/BI) is the sense in
  which iris-lean is "in the trust base" — definitions, not axioms.
  [USER]: the exports are "just memory + pure properties".
- **2026-09-02 [USER] NO BORING LOGIC; A PROJECTION THEOREM ONLY** — the
  "boring semantic separation logic" factoring was discussed
  (assertions as heap predicates, boring rules proved via Iris
  mirrors) and REJECTED as a second logic: it does not help the
  RefinedC implementation (RefinedC's types are Iris predicates; its
  automation works on Iris goals) and would duplicate every assertion
  and rule. [USER] (verbatim): "I would focus on the specifiation
  layer, i.e don't prove the rules, but show that any iris-level
  triple can be projected into a 'boring' triple over semantic states.
  This gives us the ability to state properties via iris but doesn't
  mirror the logic". Target statement shape ([USER], verbatim):
  "s |= P && core_exec(prog, s) ~~> term ==> term = some(s') && s' |= Q
  For some P / Q which are boring state descriptions" — "ie. just
  memory + pure properties". Slice: the PROJECTION — one theorem (any
  Iris triple with a concrete-map pre and an arbitrary Iris post
  projects to a `SemTripleU`-shaped statement whose post is "every
  pure consequence of the Iris post at the final state") plus
  convenience pure-consequence lemmas for the points-to shapes; the
  per-exhibit readout theorems become instances. Sequenced after P5,
  before P6 (docs describe the final statement form). Not a new
  assertion language; no rule restated.
- **2026-09-02 [USER] THE DEMO IS CLASSICAL SEPARATION LOGIC OVER CORE, NOTHING
  MORE; DERISKING HAPPENS ON A COPY IN A SIBLING SUBFOLDER; THE DEMO IS
  THE SEED OF THE NEXT LOGIC** (verbatim): "I think there's value in
  getting our demo polished up and not overloading it. So we might want
  to get to a really nice Reynolds/O'Hearn logic. And then maybe do a
  derisking slice on a copy of the tree, something like that which
  covers these extensions. So the things that are in our demo logic are
  just the things you'd need for classical separation logic, over
  cerberus core. But then we basically plunder this as the center of
  the next logic"; "I'm thinking these will literally be different
  subfolders of the project"; "It also means we can do nice things like
  build some more classical separation logic examples in the demo
  folder while we're noodling with the derisk slice." Disposition:
  (1) `cerberus-heaplang/` = the demo, scope EXACTLY classical SL over
  Core — points-to + ∗, small axioms for load/store/allocate/dispose,
  frame, consequence, sequencing, conditionals, loops, procedures with
  specs incl. recursion (dispose and procedures land in the post-audit
  kill + calls arcs); projected to boring memory+pure statements; its
  ongoing track after that is more classical examples (API-only
  modules: swap, in-place append, list length/membership, dispose-a-
  list, recursive tree traversal). (2) A sibling nested Lake package
  (name TBD, e.g. `cerberus-heaplang-ext/`), created by COPYING the
  demo's sources at a recorded seed commit (copy, not a dependency —
  free to change internals; fixes do not propagate and need not),
  sharing `.cerberus-ws` + the pin and covered by the gate runner with
  its own in-build audit, hosts the derisking slices (ranked by the
  orchestrator, [AGENT]: compiled-Core exhibit; value-indexed cells +
  named struct fields; a straight-line symbolic-execution tactic;
  the Eunseq rule; the pointer-operation family with the provenance
  fork). (3) The root `RefinedCerberus/` package is fed by both: the
  demo as the stable design/trust reference, the extension package as
  measured answers to the RefinedC gaps (list of the gaps in the
  2026-09-02 conversation: value layer over bytes; the type layer;
  the typing-judgment architecture; Eunseq as a semantic gap; UB
  fidelity to PNVI; compiled-program structure — globals/init/libc;
  struct/union/padding; the meta engine + solvers; the end-to-end
  spec attachment). [USER] on automation: heavy agent labor changes
  the KIND of automation needed (a mechanical symbolic executor for
  straight-line stretches, agents for specs/invariants/hard steps),
  not the need; Lithium's engine is not ported, its judgment SHAPE
  (syntax-directed rules, unification instantiation, pure side
  conditions) is what survives.
- **2026-09-02 [USER] THE GRUMPY-PROFESSOR STANDARD FOR THE DEMO** (verbatim):
  "When you get done answering this review, run a 2nd review which is
  briefed to the 'grumpy PL professor' standard. I.e a Fable-class
  reviewer, reviewing the work in persona as a PL professor at a
  world-class university. The professor knows everything there is to
  know about Reynolds/O'Hearn, but the professor has a very low
  tolerance for unclarity, or assumptions that aren't completely
  justified, or anything that doesn't line up with the academic goals
  of the demo logic. The professor gives you a grade and anything B or
  below is a fail, go fix it". Sequence: the quality audit round
  (dependency-tracing, AUDIT-BRIEF.md) → its fix slice → the professor
  review (fresh Fable-class reviewer, in persona, letter grade) → fix
  → re-mark by a NEW professor instance (never same-reviewer delta
  convergence) until the grade is A-range.
- **2026-09-02 [AGENT] QUALITY-AUDIT RESPONSE PLAN** (audit record:
  `cerberus-heaplang/docs/2026-09-02_quality-audit.md`; verdict: no
  unsound/vacuous rule, no trust gap, 109/109 exports trio-exact and
  traced to the engine functions; "the logic is not yet pristine").
  Two slices, one-change-at-a-time: **QA-1 (spec generalizations
  within the frozen fragment)** — H-1: mirror the engine's store/save
  operand-evaluation arms at their true generality (`valueFromPexprs
  [pe1,pe2,pe3] = none`; `Step.save_eval` + `wps_save`/`wpt_save` at
  `evalPexprs … = some cvals`), then restate the two production programs
  in their natural shape; M-3/Q9 the six missing stratum twins; Q3
  drop derivable `hnv` premises; Q4 one conditional rule with the
  verdict inside the logic (the two verdict rules become derived); Q5
  `StorableAt` everywhere; Q6/Q7 premises replaced by lemmas if
  provable; Q8 annotation-generic pure/annot rules; Q12 derived
  annotation-insensitive small axioms; Q13 extern-resolution lookup
  lemma; Q16. Every public statement change must be a strict
  generalization or premise removal, listed in the spec-delta record.
  **QA-2 (pruning + restatement)** — M-1/Q17 retire the dead island
  (`StraightFrag`, `engine_complete`, `prod_loop_done`, `prod_run_eq`,
  `sem_triple_prod`; plus `spike_engine_adequacy_alloc` and the other
  consumerless API names the audit lists) — [AGENT] decision consistent
  with the auditor's recommendation and prune-don't-merge, OPERATOR
  VETO OPEN (asked 2026-09-02, unanswered); M-2/Q11 base stratum
  generalized over `M`/`ρ` with the classical sequencing rule, or
  demoted to the two small axioms; Q10 one naming scheme; Q14/Q15
  statement cosmetics; the Notes (109 pins; trust-diagram arrow for the
  total drive equations; dead names). Then the grumpy-professor review.
- **2026-09-02 [AGENT] QA-1 ADJUDICATIONS** (record:
  `cerberus-heaplang/docs/2026-09-02_qa1-notes.md`): (1) `Frag.save`'s
  new premise `∀ pe ∈ saveParamPexprs ps, peDepth pe ≤ lemDefaultFuel`
  is ACCEPTED as a deliberate exception to the slice's
  strict-generalization rule: it is the fuel-honesty condition every
  other evaluating `Frag` constructor already carries (`Frag.if_`'s
  `hdg`), it narrows `Frag` only on shapes that never had a rule or a
  mirror step and cannot past fuel, and it is what certifying the
  save-EVAL arm against the engine's fueled evaluator requires; the
  audit's alternative (narrow to literal initializers) is the larger
  narrowing. (2) `counter_loop_certified_production`'s fuel premise
  `6·n+8` (was `7·n+7`): accepted — the natural program shape costs one
  save-entry step and saves one per iteration; weaker for all n ≥ 1.
  (3) Literal-initializer exhibits consuming `wpt_save_vals` (the
  instance) while the production programs consume the general
  `wpt_save`: accepted; both have consumers. Stopped items are
  FINDINGS, not deferrals: Q6 (`decIndep` splice lemma false without a
  layout side condition — `reconstructValue` consults the union and
  funptr tables recursively), Q7/Q16 (whole-engine-AST fuel-indexed
  induction — grind class), Q8 (annotation-generic pure/annot rules are
  FALSE under the canonical-annotation protocol D3) — each is now
  documented at the rule; Q3 partial for the same D3 reason.
- **2026-09-02 [AGENT] QA-2 ADJUDICATIONS** (record:
  `cerberus-heaplang/docs/2026-09-02_qa2-notes.md`): (1) the dead
  straight-line production island and the consumerless API names are
  RETIRED (deleted) — the [AGENT] decision the plan announced,
  operator veto still open; (2) M-2 resolved by DEMOTION, not
  generalization: a classical raw-WP sequencing rule over an arbitrary
  machine context is FALSE at a populated label map (a jump discards
  the sequencing context — Rules.lean header), so sequencing belongs
  to the label-context judgments `wps`/`wpt`; the base stratum is the
  two raw-WP small axioms `wp_store`/`wp_load` only, and the spike
  exhibits are re-derived through `wps`; (3) the worker's retirements
  beyond the audit's named list (LoopExhibit's consumerless `LoopTotal`
  section; the frozen jump-profile spellings in Soundness/Adequacy)
  are ACCEPTED — zero-consumer traces recorded, prune-don't-merge;
  (4) four exhibits the README listed as pinned but never were are now
  pinned (the sentence was made true rather than weakened). Result:
  2,085 → 1,949 declarations; 120 trio-exact export pins.
- **2026-09-02 [AGENT] PROFESSOR REVIEW 1 (B+) — RESPONSE ADJUDICATIONS**
  (records: `cerberus-heaplang/docs/2026-09-02_professor-review-1.md`,
  `…_pr1-notes.md`, `…_pr2-notes.md`): the grade clears the operator's
  fail line (B or below) by one notch, but the two items the professor
  names as separating it from A- are defects in the STATEMENTS of the
  main results (run-length-coupled fuel premise; a headline projection
  whose conclusion is not boring) — treated as required, all eight
  required fixes executed, re-mark by a NEW professor instance follows.
  PR-1 adjudications: (1) fix 8's lifting shape differs from the
  review's (`WP ⊢ wps` is unprovable: iris-lean's `wp.pre` places `▷`
  after the step's `|={∅}=>`, `wps.pre` before the `∀`) — the
  mask-generic `AtomicStep` specification + three lifting lemmas
  achieve one proof per small axiom; accepted. (2) The three
  mirror-only termination exports are DELETED, not relabelled; the
  negative test is re-proved at the engine. (3) The triple/drive
  collapse to the `U` forms and `driveU` is accepted (prune, traces
  recorded); `rsCtx` (Step.lean, frozen) is now consumerless — a later
  slice. (4) `hlib` discharge STOPPED as a finding: the premise is
  dischargeable on the success path but `Round.lean`'s refused
  classifications carry the location in the killed payload; removing
  it means editing the frozen certification — deferred with the
  reason. (5) `hbsz` stays (QA-1's whole-AST-induction stop stands).
- **2026-09-02 [AGENT] PROFESSOR REVIEW 2 (A-) — RESPONSE; ARC AT CLOSING
  STATE** (records: `cerberus-heaplang/docs/2026-09-02_professor-review-2.md`,
  `…_pr3-notes.md`). Of the four required fixes: (1) `peDepth`/`PePure`
  documented; (2) six tree-refuting module headers corrected and every
  header the WALKTHROUGH cites purged of process vocabulary; (3) `hlib`
  DISCHARGED by the professor's route (`requestLoc` names the engine's
  location conditional; `storeM_loc_irrel`/`loadM_loc_irrel`; 46
  statements lose the premise, 9 strictly generalized, certification
  theorems unchanged); (4) `hbsz` stated as the exact registered gap
  `esize (subst_sym_expr x v e) = esize e` (obstacle: the fuel-indexed
  `subst_sym_expr_lemFuel`), the alternative the professor named as
  acceptable. `rsCtx` retired. Remaining for a full A: the recommended
  additive capacity face over `allocCap` (an authoritative-sum ghost
  algebra + inequality coupling) — design work; and the `hbsz`
  induction (grind class). Orchestrator recommendation to the operator:
  close the arc at A-, merge, and carry both as the first items of the
  demo's post-freeze quality track (the malloc/free arc reshapes
  allocation anyway). Operator decision pending.
- **2026-09-02 [USER] THE DRIVER IN EVERY EXPORT IS THE GENUINE CERBERUS ONE;
  SEMANTICS-SIDE LIMITATIONS ARE REQUESTED UPSTREAM, NEVER WORKED AROUND**
  (verbatim): "There should not be any reason for the driver to not be
  the actual, genuine, legitimate, original Cerberus one. We should not
  be writing our own trusted driver code. This is very clearly not
  achieving the end to end root of trust behavior that we're aiming for
  here." and "If we have limitations on the Cerberus side, we can in
  fact make requests to the Cerberus team to improve the quality of
  Cerberus Lean. This is the more appropriate way to deal with
  limitations like this, not to invent some fake driver which doesn't
  give us the complete root of trust that we're looking for." Also the
  operator's restatement of the trust architecture (same day): the
  Cerberus operational semantics is the true Cerberus and the root of
  trust; relational artifacts in the repo (RelSem etc.) are subsidiary
  bridging artifacts; Iris needs a non-fuel semantics, hence a mirror,
  with every claim about a Core program deriving from an operational
  behaviour of the Cerberus semantics. FINDING (surfaced by the
  2026-09-02 detailed audit and the second professor): the
  partial-correctness exports (`MemTripleU`, `project_triple*`, the
  `*_certified` partial statements) are stated over `driveU`, a
  package-defined loop around the engine's `step_ctx`, because the
  shipped driver's fuel-exhaustion arm is the runtime's OPAQUE sentinel
  and cannot be classified in any ∀-fuel statement. Disposition: (1)
  the request `docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md`
  (a distinguished, transparent fuel-exhaustion kill in the ND monad)
  goes to the cerberus-lean team via the operator; (2) NO workaround
  driver is built (the orchestrator's proposed existential-over-the-
  opaque-tail statement is WITHDRAWN); (3) until the request lands, the
  driveU-based exports are labelled PROVISIONAL on every surface —
  sound facts about `driveU`, not the root-of-trust statement; the
  total-lane production statements, which are over the shipped
  pipeline, are the root-of-trust exports; (4) the trust rule "no
  hand-written definition in any export's referent" enters CLAUDE.md.
- **2026-09-02 [AGENT] DETAILED AUDIT (third independent auditor,
  `docs/2026-09-02_cerberus-heaplang-detailed-audit.md`) — DISPOSITION**:
  H-1 (no bridge to `RelSem`; two-sidedness assumes a mirror step):
  the RelSem-bridge requirement is REJECTED on the trust ruling (RelSem
  is a subsidiary artifact; the engine is the root); the auditor's
  qualified statement of what is proved is adopted verbatim in the
  docs; MIRROR COMPLETENESS ON THE FRAGMENT (mirror stuck ⇒ an engine
  refusal/kill fact, per constructor) is registered as the open
  architecture item for the post-freeze quality track. M-1 (allocation
  health footprint-relative): documented as footprint-relative
  freshness now; a global memory well-formedness invariant belongs to
  the malloc/free arc. M-2 (API classification), L-1 (audit skips
  internal-detail constants while claiming "every"), L-2 (Step-proved
  coverage witnesses inside a positive exhibit module), L-3 (short
  normative architecture statement): all accepted, executed in the
  audit-response-3 slice. The auditor's uncommitted README edit on
  main's working tree was moved to this branch and main restored.
- **2026-09-02 [USER] RelSem IS NOT MAINLINE MATERIAL** (verbatim): "the
  RelSem work should not be on main, I'll get it killed". Consequence
  here: every reference to `RelSem.Machine.Step`/`runND_sound`/
  `HarnessAdequate`/`relsemcore` is removed from the package (docs,
  Round.lean, ARCHITECTURE); the mirror's only reference is the engine
  round `CerberusRound`; no other relational semantics is referenced or
  bridged. Zero hits outside the dated records (measured).
- **2026-09-02 [AGENT] AUDIT-RESPONSE-3 ADJUDICATIONS** (record:
  `cerberus-heaplang/docs/2026-09-02_audit-response-3-notes.md`):
  (1) L-1 turned out to be a REAL gap, not wording: a `private theorem
  plant : True := by sorry` in a leaf module passed the OLD in-build
  audit (exit 0, counts unchanged — measured) because both sweeps
  skipped `isInternalDetail` constants; the sweeps now include them
  (2249 theorems / 3536 constants, no measurable cost), the plant goes
  red, and the plant is not retained. The 116 exact export pins were
  never at risk (their cones are collected transitively), so no export
  was affected. (2) PROVISIONAL labels on every `driveU`-based export
  surface; the total-lane production statements named as the
  root-of-trust exports. (3) `ARCHITECTURE.md` (152 lines) is the
  normative statement; README/WALKTHROUGH point at it. (4) Observed and
  reported upstream (appended to the fuel-exhaustion request): a
  `(sorry : String)` placeholder in the pinned generated `Cmm_op.lean`
  concurrency debug arm — outside every cone of ours by the sweep.
- **2026-09-02 [USER] THE DEMO'S ACCEPTANCE GOALS** (verbatim): "we should log
  as our goal for this demo these goals 'a generic logic with adequacy
  over the shipped driver, a complete logic for the fragment, a globally
  well-formed allocator model,' - covering all of Core isn't a goal for
  the demo, but the rest are". Recorded as the three acceptance goals,
  with the orchestrator's agreed precisions: (1) SHIPPED-DRIVER
  ADEQUACY — no export labelled PROVISIONAL remains; every partial-
  correctness statement quantifies over the shipped driver's fuel with
  exhaustion a classified outcome; DEPENDS on the cerberus-lean fuel-
  exhaustion request. (2) MIRROR COMPLETENESS FOR THE FRAGMENT — for
  every fragment configuration, either the mirror steps and the engine
  round matches it, or the engine round is classified (value, refusal/
  kill/UB, or nondeterministic fork) as an engine fact; a STANDING
  obligation each arc re-establishes for its constructors. (3) A GLOBAL
  MEMORY WELL-FORMEDNESS INVARIANT (allocation-id discipline, live/dead
  consistency, range disjointness of all live allocations, cursor
  bounds) in the launch premise and state interpretation, proved for the
  production initial state and preserved by every supported operation;
  "fresh" then means fresh in the concrete allocation model. Not a goal:
  full Core. Sequencing [AGENT]: completeness first (no dependency),
  the invariant with the kill/free arc, shipped-driver adequacy when the
  upstream outcome lands; calls after completeness.
- **2026-09-02 [AGENT] AUDIT-RESPONSE-4 ADJUDICATIONS; A FAIL-OPEN IN THE
  PRIMING GUARD FOUND AND CLOSED** (record:
  `cerberus-heaplang/docs/2026-09-02_audit-response-4-notes.md`): the
  re-review's N-1..N-4 fixed as specified (docs + two emitted-sentence
  texts). N-3's diagnosis found the real cause of the count difference:
  the PRIMARY checkout's `.cerberus-ws` (re-primed 2026-09-02T15:15 from
  the cerberus-lean checkout at `4cb8c4ee9`) carries that commit's
  hand-written `CerbMem.lean` (mem-scale C3 delta, +353/−15), not the
  pin's, because `scripts/setup-cerberus-dep.sh`'s content guard did not
  list the hand-written seams `lean_frontend/*.lean` (copied into
  `generated/` at build time) — a FAIL-OPEN (a defect by house rule).
  Closed in this slice: the seams and the copy manifest are on the guard's
  path list, and a new section C verifies every primed seam copy
  byte-identical to the PINNED clone's source in both prime and --check
  modes (fallback to all `lean_frontend/*.lean` with a generated twin
  when the pin predates the manifest, as ours does — 21 seams). Tested:
  C ok on the correctly primed worktree workspace; the same check finds
  `CerbMem.lean` MISMATCH on the primary's. The primary's workspace is
  replaced by a copy of the verified pinned one. The third auditor's
  re-review ran against the C3 memory model (green, 116 pins) — the
  package holds against both texts, but that run was not a build against
  the pin; recorded. A deliberate re-pin to a post-C3 head is a separate
  forced-semantics-change slice, not taken now.
- **2026-09-02 [USER] MIRROR COMPLETENESS — GO** (verbatim): "Can we work
  on this before the cerberus-lean team resolve the fuel issue? And are
  there any considerations about how we do this that impact our future
  RefinedC buildout? If both are clear, you can go ahead and begin
  executing on this while we wait for the cerberus-lean team". Operator's
  understanding, confirmed with the precision recorded here: on the
  fragment the mirror is EXACTLY the engine restricted to its successful
  deterministic rounds — mirror steps iff the engine has a successful
  deterministic round, with the same successor; the engine's failure
  outcomes (UB, kills, the nondeterministic fork) are stuck in the mirror
  and CLASSIFIED in the engine, not modelled as transitions. [AGENT]
  answers: (1) independent of the fuel fix — completeness is about
  single rounds (`step_ctx` + the shipped request handling + the memory
  functions), not the loop; (2) RefinedC-shaping constraints — one
  coverage lemma per fragment constructor (linear growth; a missing arm
  fails a proof, not an audit); classify refusals in the engine's own
  kill vocabulary (`Undef0` codes, `Error0`), which is what a "no UB"
  claim needs; do not bake determinism in — the fork is a class the
  mirror may later cover with a nondeterministic step (Iris WP handles
  demonic choice); freeze respected — no new constructs, coverage bugs
  found on the way are quality fixes. FINDING folded into the slice:
  the round relation `CerberusRound` and the certification/classification
  exports (`engine_step_matchU`, `step_iff_cerberusRound`,
  `cerberusRound_classify`) are stated over `outcomesU`, i.e. over the
  hand-written `dischargeStep` — the new trust rule applies; the slice
  restates the round over the SHIPPED driver's one-iteration unfolding
  (the `loop_step_frag` shape: `runOne (drive_nonmemory_steps_aux2_lemFuel
  (fl+1) …) dst = runOne (… fl …) dst'`, killed/done terminals, ≥2
  outcomes for a fork), no fuel dependency, `dischargeStep` demoted to a
  proof device.
- **2026-09-02 [AGENT] MIRROR COMPLETENESS LANDED — WITH FOUR REGISTERED GAPS;
  DECISIONS PENDING** (record:
  `cerberus-heaplang/docs/2026-09-02_mirror-completeness-notes.md`).
  Commit 1: `CerberusRound` restated as ONE ITERATION OF THE SHIPPED
  DRIVER'S THREAD LOOP (`step_ctx` → `can_advance` → `advance_step` at
  every embedding driver state; no fuel dependency; at the context's
  own tagDefs/extern/tid — no pin was deep); `engine_step_matchU`,
  `step_iff_cerberusRound`, `cerberusRound_classify`, `cerberusRound_refused_*`
  restated over it; `dischargeStep`/`outcomesU` are proof devices. The
  one non-engine constant in the statement is `runOne`, the `ND`
  constructor's eliminator (destructor plumbing, not driver content) —
  accepted. Commit 2: `frag_round_complete` — at every non-value
  fragment configuration the mirror steps, or the shipped round is a
  classified refusal (`ShippedRefusal`: ILLTYPED / KILL with the
  engine's `kill_reason` / FORK — `eqPtrval`'s differing-provenance
  `msum` delivers exactly two executions / PANIC forms), or the
  configuration is one of four REGISTERED GAPS (`OpenRound`, each an
  engine fact): (a) the LETS-ANNOT beta at the symbol binder — engine
  SUCCESS, no mirror rule (~1 day: an 8th `Step.sseq_inv` disjunct, 38
  sites); (b) load/store ACTION_EVAL whose pointer operand evaluates to
  a non-pointer — engine SUCCESS into the ill-typed action (~1 day);
  (c) operand evaluation outside the mirror evaluator (`evalPexpr`
  covers PEval/PEsym/eight integer binops/PEarray_shift; the engine's
  `eval_pexpr_aux2` also succeeds on ctype/float equality, div/rem/exp,
  and/or, floats, procedure-name symbols) — either a complete mirror
  evaluator (LARGE: `M.file` in `evalPexpr`, ~340 call sites) or an
  honest narrowing of `Frag`'s operand grammar to the covered set
  (`PePure` for `if_`/`run`/`save`/`pure_sym` too); (d) a jump with no
  current procedure — an engine `failwith` (opaque) inside the lookup
  key; only the step's shape is statable. Orchestrator recommendation:
  fix (a) and (b) at the engine's generality (they are exactly the
  store/save class); NARROW for (c) — the classical-SL demo's operand
  language is integers, symbols and pointer shifts, so declare the
  fragment as what the mirror evaluator covers and state completeness
  relative to that declared fragment (a complete evaluator belongs to
  the compiled-Core derisking package); accept (d) as the engine's own
  panic, classified by shape. Pins 116 → 139. Verified by the
  orchestrator: FULL gate ALL GATES GREEN, GATE-EXIT=0.
- **2026-09-02 [USER] THE BOUNDARY IS FAIL-CLOSED; NON-MIRRORED SHAPES ARE
  CAPTURED, NEVER ACCIDENTAL** (verbatim): "the aim here is that
  non-mirrored statements are captured, and we can't accidentally
  introduce them. It's fine to have a carefully characterized boundary
  that is fail-closed outside the boundary"; earlier: "Are (a-c)
  actually in scope for our demo though? Another reasonable way to
  handle this is to fail-closed if we've achieved complete coverage."
  Mechanism: `Frag` is the boundary (refused at the adequacy premise);
  inside it `frag_round_complete` dispatches exhaustively over the
  constructors, so a constructor without its coverage lemma breaks the
  proof and an engine success without a mirror step is an undischargeable
  obligation.
- **2026-09-02/03 [AGENT] FRAGMENT CLOSURE LANDED** (record:
  `cerberus-heaplang/docs/2026-09-02_fragment-closure-notes.md`): (a)
  `Frag.sseq_sym` narrowed to `BareHead` heads (values, `create`, the
  PtrEq memop forms — `create` added beyond the brief because exhibits
  bind its result there); (b) reclassified as `ShippedRefusal.error_next`
  (ILLTYPED at distance one, engine facts proved); (c) operand grammar
  narrowed to `PePure` for `if_`/`run`/`save`, and `PePure.op` to the
  eight mirrored binops (measured: `Div/Rem/Exp` at integers are engine
  SUCCESSES, so the brief's "division-class UB" premise was wrong —
  excluded syntactically instead); every rejected operand is now a
  proved engine KILL (`Other (DErr_core_run …)`, exact payload) through
  the new `EvalClass` kill bridge; (d) `ShippedRefusal.panic_noproc`.
  TWO RESIDUAL `OpenRound` ARMS remain, each with a mirror-side witness
  and the engine shape: `eval_uncovered` — value-dependent engine
  successes not syntactically excludable (the eight binops at two
  floats, `OpEq` at two ctypes, a procedure-named symbol evaluating to a
  function pointer); `run_surplus` — NOT anticipated: `step_ctx`'s Erun
  arm zips (truncating) and succeeds when a surplus argument fails to
  evaluate while the mirror requires all arguments. Pins 139 → 159; all
  rules, exhibits and production statements byte-identical.
  Orchestrator recommendation: LEAVE both registered (they are
  characterized, per the ruling) — the closer is a well-formedness
  premise on `M` (exact `run` arity against `M.labels`; no procedure
  name among operand symbols; integer/pointer-only fragment types with
  an env-typing invariant), moderate effort with no RefinedC value now;
  the compiled-Core derisking package needs a complete evaluator anyway,
  at which point both vanish.
- **2026-09-03 [USER] POLISH IS SIZED BY RefinedC VALUE; SCHEDULE STRICTLY TO
  THE refined-cerberus BUILD-OUT; THE REST IS A SIDE THREAD** (verbatim):
  "which of these polish steps actually helps us with RefinedC - we
  wouldn't want to spend a lot of effort we later throw away. We should
  size everything proportionate to effort"; "for things like
  presentation polish, they can be done in parallel on the demo later,
  and therefore aren't blocking on refinedC build-out. We want to
  schedule strictly to enable our refined-cerberus build, and then do
  the rest as a side thread". Ranking [AGENT, operator agreed]: KEEP —
  partial lane over the shipped driver (upstream fuel; our restatement
  small); the global memory well-formedness invariant (K0); SPLITTABLE
  CAPACITY upgraded to needed-for-calls (an allocating callee's
  precondition cannot be an ordered prefix of the caller's plan; done
  inside the calls arc); the read-only metadata flag folded into K1
  (same mechanism as `alive`). LEAVE — gap (c) residuals (the compiled-
  Core package's complete evaluator subsumes them), `hbsz` (whole-AST
  induction), `finalize`'s opaque leaf (upstream), presentation polish
  (side thread).
- **2026-09-03 [USER] THREE LANES** (operator: "I agree with this analysis"):
  LANE A, the demo core, strictly sequential (shared `Step`/`Soundness`/
  `Round`): fragment closure → kill/free K0–K4 (read-only flag in K1) →
  calls with splittable capacity → the partial-lane restatement when the
  fuel outcome ships; LANE B, the derisking sibling package (a copy
  seeded at the closure landing), parallel: compiled-Core exhibit first,
  then value-indexed cells, then the straight-line tactic; LANE C,
  design, read-only, parallel: the refined-cerberus design notes. Two
  build lanes at most on the box.
- **2026-09-03 [USER] ADOPT ONLY THE SLICE OF RefinedC THAT SERVES AGENT-DRIVEN
  VERIFICATION AT SCALE** (verbatim): "we only want to adopt refinedC
  inasmuch as it supports our goal of agent-driven formal verification
  for very large bits of software. We mostly want to support an
  agent-driven verification workflow over core. So this doesn't
  literally require refined-C, it requires the slice of refinedC which
  supports that goal." Applied as the organizing criterion of the Lane
  C note `docs/2026-09-03_refinedc-layer-design-spike.md` (branch
  design-refinedc, efcb888): taken — types as uniform spec vocabulary,
  the syntax-directed judgment shape, per-procedure specs with a
  persistent table; not taken — Lithium's engine/completeness
  engineering, subtyping/coercion instance families, Shr/Copyable for
  now, annotation conveniences, mem_cast generality. Two decisions
  PENDING the operator: (1) the root package depends on the demo via a
  Lake path-require (orchestrator recommends: dependency, not copy —
  one trust base, fixes propagate; the copy ruling was for the
  derisking package); (2) the value layer (GAP 1 symbolic integer
  codec round trip; GAP 2 the pointer round trip promoted out of the
  exhibit) lives in the demo core, queued in Lane A after K1.
- **2026-09-03 [USER] AUDITS ARE NOT SKIPPED; EVERY MERGE IS AUDITED OVER THE
  RANGE SINCE THE LAST AUDIT** (verbatim): "I think we should not skip the
  audit, we've repeatedly seen failed audits on this work. We should run
  an audit on all the changes since the *last* audit". Supersedes the
  orchestrator's recurring "propose waiving" habit: the pre-merge ask
  still names scope, but the default is an independent, dependency-
  tracing audit of `git diff <last-audited head>..<merge candidate>`,
  by a fresh reviewer, before any fast-forward. First application: the
  audit of b34998d..c2c4e4d (AR-4, the shipped round, mirror
  completeness, fragment closure) before `fragment-closure` merges.
- **2026-09-03 [AGENT] ERRATUM to "2026-09-02/03 [AGENT] FRAGMENT CLOSURE
  LANDED"** (source: the independent audit
  `cerberus-heaplang/docs/2026-09-03_audit-since-b34998d.md`, finding M-1,
  established by execution; response record
  `cerberus-heaplang/docs/2026-09-03_audit-since-b34998d-response.md`).
  The entry above says "every rejected operand is now a proved engine
  KILL" and describes `eval_uncovered` as "value-dependent engine
  successes". Both overstate what the theorems say. Tree's truth: the
  classifier `evalClass` (EvalClass.lean) answers `.uncovered` at the
  FIRST uncovered LEAF of an operand and carries NO engine claim, so the
  residual `OpenRound.eval_uncovered` contains operands whose
  whole-operand outcome is NOT characterized — including ones the engine
  KILLS (the auditor's counterexample: `f + 1` with `f` a `Proc`-named
  unbound symbol is `PePure`, classified `.uncovered`, and the engine
  kills it as `Illformed_program … ill-typed PEop`) and ones it PANICS
  on (a float guard under `Eif`). Corrected statement: every operand the
  classifier REJECTS (`evalClass … = .kill err`) is a proved engine KILL;
  operands the classifier leaves UNCOVERED are not characterized (the
  residual is a SUPERSET of the engine-accepted shapes). The Lean
  statements (`frag_round_complete`, `OpenRound`) were and are honest —
  the arm claims only the step's shape; the overclaim was prose, now
  corrected on every surface (Round.lean docstrings, EvalClass.lean and
  Soundness.lean headers, README, ARCHITECTURE §2/§7, WALKTHROUGH §5/§7).
  Mover: `evalClass` computing the engine's value at the three leaf
  shapes (`nullPtrval` for the `Proc`-named symbol, the float binops,
  `ctypeEqual`), which reserves `.uncovered` for the leaf itself and
  puts the downstream rejections under the KILL bridge. Also corrected
  in the same pass (audit N-1/N-3/N-4): the round `CerberusRound` and
  its certification/completeness are consumed by NO adequacy export (the
  `driveU` lanes consume the device lemma `outcomesU_of_step`, the
  production collapse `loop_step_frag`); `engine_step_matchU` has no
  `SeqWF` premise; the slogan "mirror steps iff the engine has a
  successful deterministic round" carries its two disclosed exceptions
  (the REMOVE-ANNOT value round; `error_next`, an engine SUCCESS round
  into an ILLTYPED-next configuration, filed under refusals) wherever it
  appears. Whether `error_next` belongs under `ShippedRefusal` is a
  naming decision left to the operator (audit N-4).
- **2026-09-03 [USER] THE ROOT PACKAGE'S RAW LOGIC IS A COPY, NOT A LAKE
  DEPENDENCY ON THE DEMO** — operator: "it depends on the exact blast
  radius. I'm reluctant to couple the demo to a further exploration
  which might break the demo as a nice persistent artifact"; "what
  benefit do we get from this? We're not literally going to reuse the
  demo infra? We'll need to make changes". Agreed [AGENT]: the root
  needs the demo GROWN (a fragment covering compiled Core — `Eunseq`,
  member shifts, the case evaluation arm, more memops, bounds,
  alloc/kill, calls), which changes `Frag`/`Step`/the certification/
  completeness — exactly what the demo freeze keeps fixed; a dependency
  on the frozen demo is a foundation too small to build on and its "one
  trust base" benefit is moot (the grown fragment is re-certified
  anyway). Disposition: the demo stays the pristine persistent
  reference; the derisking sibling package (Lane B) is seeded by copy
  from the closure head, grows the fragment, and becomes the root's
  raw-logic layer; reused are the architecture and proof techniques,
  not the artifacts; the codec laws (GAP 1/2) land in the grown copy
  and enter the demo only if its own examples want them. The Lane C
  note's S0 is corrected accordingly (design-refinedc, bff3208).
