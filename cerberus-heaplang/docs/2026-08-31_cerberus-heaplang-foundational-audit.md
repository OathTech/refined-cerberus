# Foundational audit of `cerberus-heaplang`

Date: 2026-08-31  
Repository revision audited: `59a8d39` (`main`)  
Cerberus Lean pin: `58ec50779f036da1794c440d215d41a755027382`  
Iris Lean pin: `34390a0133986385c62bf59a6eb01938945b48ec`

## Executive verdict

`cerberus-heaplang` contains a real, kernel-checked, sequential
separation logic in the Reynolds/O'Hearn tradition. Its separating
conjunction is Iris BI conjunction, its points-to assertions are Iris
GenHeap ownership, full ownership is required for writes, fractional
ownership supports reads, its frame and consequence rules are genuine,
and the linked-list proof uses a structurally recursive representation
predicate and a conventional loop invariant. This is not a trace
checker or an example-specific replay dressed up as a logic.

The connection to Cerberus Lean is also substantive. Iris WP is defined
over a relational `Language` instance, and the package proves the
relations needed to connect that WP to calls of Cerberus's generated
`step_ctx` and memory functions. On the actually certified subset, the
proof directions used by adequacy are sound.

The project is nevertheless **not yet in a good state if its claim is
read as a generally usable separation logic over Cerberus Core**. It is
a legitimate restricted demonstration with several material claim and
architecture defects:

1. An advertised rule, value-scrutinee `Ecase`, does not enter the
   `FragJ` cone and therefore cannot reach loop adequacy. This is a
   concrete coverage failure which was noted in dated phase notes but
   was not carried into the current public register or retired.
2. The total Fibonacci theorem is not a product of the Iris logic or of
   the advertised invariant-plus-variant rule. It is a separate
   operational induction which explicitly supplies `Step` constructors
   to `driveJ_step`. The variant rule is unused, does not enforce that
   jumps decrease its measure, and has no connection to total WP or a
   drive bound.
3. The Iris language is built over a manually maintained, fused,
   syntax-indexed projection of the engine. It freezes most of the
   machine context and duplicates fragment membership and decomposition
   in several inductives. That is defensible for a spike, but it is the
   main source of silent coverage drift and accidental example
   coupling. The `Ecase` defect is evidence that this risk is already
   realized.
4. Array and list examples add layout-specific interior load/store WP
   rules rather than consuming a generic sub-allocation access layer.
   The examples therefore extend the logic in order to verify
   themselves.
5. Several important public descriptions are stronger than the proved
   statements: not all theorem cones are checked for exact equality,
   the loop production theorem is not a production `runND` theorem, and
   the list theorem's conclusion is weaker than the phrase “in-place
   reversal” normally conveys.

No new kernel trust hole, `sorry`, prohibited decision procedure, or
axiom outside the declared boundary was found. The known `runEffectful` seam remains a
real production-facing blocker, but it is well documented and already
has an owner and retirement direction. The newly identified defects
above should be addressed first because they lack equivalent closure
plans and are more likely to reproduce as the fragment grows.

## Answers to the three audit questions

### 1. Is this legitimately a Reynolds/O'Hearn separation logic using Iris and correctly connected to Cerberus Lean?

**Yes, with a strict scope qualification.** It is a legitimate
sequential, partial-correctness separation logic for allocation-rooted
heaplets and a small synthetic Core fragment. It is not yet a general
logic for Cerberus Core, a C frontend logic, a concurrent Iris logic, or
a logic with generic C object-layout ownership.

The positive case is strong:

- `Heap.lean:234-265` defines a concrete coupling invariant from ghost
  cells to live, writable Cerberus allocations and their exact bytes,
  including pairwise range disjointness.
- `Heap.lean:442-465` constructs the Iris ghost prerequisites and a
  `StateInterp Mem Empty` containing the coherent GenHeap.
- `Rules.lean` proves Iris WP load/store rules; `Wps.lean` lifts the
  same reasoning to a jump-aware statement judgment.
- `Adequacy.lean:371-390` defines a semantic triple quantified over an
  arbitrary disjoint frame `R`, and `semantic_triple_sound`
  (`Adequacy.lean:464`) proves that an Iris triple implies that engine
  triple.
- `ListRevExhibit.lean` uses a recursive `isList` assertion, separation
  between nodes, and the invariant
  `isList prev reversed ∗ isList cur rest` rather than a monolithic
  execution calculation.

The connection is sound on the declared and actually reachable cone:

- The straight-line lane proves `engine_complete`
  (`Soundness.lean:1660`). Each actual discharged engine behavior is a
  mirror step, a value-protocol step, or a refusal at a configuration
  proved stuck in the mirror. Iris `NotStuck` excludes the refusal case.
  This is the direction required by `drive_classify` and
  `spike_engine_adequacy`.
- The jump lane proves `engine_step_matchJ`
  (`Soundness.lean:3949`). Given a `FragJ` mirror step, the engine's
  discharged behavior is exactly the corresponding singleton.
  `engine_adequacyJ` obtains a mirror step from Iris `NotStuck` and uses
  that equality.
- Both paths operate on the generated Core AST and real `CerbMem`
  state and invoke the generated `step_ctx`, `loadM`, `storeM`, and
  `allocateObject` definitions. They do not prove facts about a toy AST
  and then assume a compiler relation.

There is an important conceptual correction to the concern about
“operational” versus “relational” semantics: an Iris language is
normally supplied by a small-step relation, and the package's `Step` is
such a `Prop`-valued relation. Using a relation derived from an
operational interpreter is not itself suspect. The problem is that this
particular relation is a large hand-maintained projection with multiple
parallel coverage predicates, and that some exported results bypass it
and the logic entirely.

### 2. Are there unacceptable or unaccounted trust gaps?

There is no evidence of an unaccounted kernel axiom or proof bypass.
There are, however, material **specification, attachment, and coverage
gaps**. These do not let Lean prove a false theorem about the function
that occurs in the theorem statement, but they can make the theorem
true about the wrong projection, weaker than its prose description, or
unavailable for supposedly supported syntax. For a verification
framework, those are trust-story defects even when they are not kernel
unsoundness.

The highest-priority gaps are findings F-01 through F-04 below. The
known `runEffectful` issue is F-08.

### 3. Is the documentation adequate?

The documentation is unusually extensive and often admirably candid.
It explains frozen contexts, fuel, the absence of `wp_create`, whole
allocation ownership, production versus projected drive lanes,
`runEffectful`, and the use of a mirror relation. The walkthrough makes
many theorem statements inspectable in full.

It is not yet adequate as a reliable statement of the overall design
and trust story because the most prominent summaries overstate several
facts which lower-level dated notes describe more accurately. A reader
should not have to discover from `Soundness.lean` that advertised
`Ecase` is outside `FragJ`, or from `FibExhibit.lean` that totality is a
manual operational proof unrelated to the documented variant rule.
The README also describes a nonexistent `Language.Context`, calls an
upper-bound axiom sweep “exact”, and gives a production-sounding name to
a loop theorem whose statement still uses `driveJ`.

## Architecture actually present

The load-bearing flow is:

```text
Iris BI / GenHeap ownership
        |
        v
WP over Language(CoreRt, Mem, Empty, CoreRVal)
        |
        v
hand-written Step Q (CoreExpr × EnvStack × Mem)
        |
        +-- straight: engine_complete --> package drive
        |
        +-- jumps: engine_step_matchJ --> package driveJ
                                          |
                                          v
                           selected production collapse lemmas
                                          |
                                          v
                         shipped Driver.drive / CerbND.runND
                         (straight-line examples only)
```

`Step` fuses an engine expression step, action request, sequential
memory discharge, and continuation into one Iris primitive step. The
Iris state is only `Mem`; the expression value `CoreRt` carries the Core
expression, environment stack, and label map. File, tags, extern map,
thread metadata, most driver state, traces, counters, nondeterministic
branches, and concurrency are frozen or projected out. `driveJ` keeps a
`core_run_state` parameter constant and retains only the behavior needed
by the selected fragment.

The Cerberus pin itself contains a separate derived relational spine in
`lean_frontend/relsemcore/RelSem`: `Machine.lean` defines `Step`/`Steps`,
`RunND.lean` proves `runND_sound`, and `Cerberus.lean` defines
`HarnessAdequate`. `cerberus-heaplang` has no `RelSem` import. This audit
does not assert that the existing spine can directly replace the
Iris-language relation; its state split may be unsuitable for syntax
rules and atomicity. It does mean the repository currently has two
independent derived semantic presentations, and their relationship is
neither proved nor documented in the heaplang trust diagram.

## Detailed findings

Severity meanings used here:

- **High**: blocks the advertised foundational claim or is likely to
  cause repeated silent miscoverage.
- **Medium**: does not invalidate the restricted core result but weakens
  a public claim, trust control, or example independence.
- **Known blocker**: material but already explicitly registered with a
  retirement owner; listed after newly discovered defects as requested.

### F-01 — Advertised `Ecase` cannot reach engine adequacy

Severity: **High**  
Status before this audit: partially noted in phase notes, absent from
the README divergence register and contradicted by the public scope
claim.

Evidence:

- `Step.case_value` exists at `Step.lean:925`.
- `wps_case_value` exists at `Wps.lean:831`.
- `step_ctx_case_value` exists at `Soundness.lean:2459`.
- `FragJ` at `Soundness.lean:3244-3306` has no `Ecase` constructor.
- `engine_step_matchJ` explicitly eliminates its `case_` branch because
  “Ecase is outside the J cone” at `Soundness.lean:4112-4116`.
- `wps_case_value` has no consumer in the package.
- README lines 247-253 include value-scrutinee `Ecase` in “the certified
  fragment”; the divergence table only excludes the non-value EVAL arm.

Impact:

The local rule is proved against the mirror and has a per-step engine
equation, but no exported loop adequacy theorem can consume it. This is
exactly the kind of gap that duplicated syntax cones permit: rule
existence, per-step certification, fragment closure, and adequacy
reachability are independent checklists.

Remediation:

1. Immediately remove value-scrutinee `Ecase` from the public certified
   scope or mark it “local rule only; not adequacy-exportable”.
2. Add the required `FragJ` closure constructor and substitution-closure
   lemmas, then extend `decompJ` and `engine_step_matchJ`.
3. Add an engine-facing adequacy test whose program necessarily executes
   the `Ecase` rule.
4. Introduce a mechanical advertised-rule coverage gate: a construct is
   “certified” only when it has a logic rule, fragment-cone membership,
   engine matching, and an adequacy consumer. A source-code comment is
   not an adequate gate.

Acceptance criterion: an `Ecase` program has a theorem stated over
`driveJ` or the replacement canonical engine relation, and deleting any
one of its cone/match cases fails the coverage gate.

### F-02 — Total correctness is an operational side proof, not a logic result

Severity: **High**

Evidence:

- `blockSpecs_intro_variant` is defined at `Wps.lean:1692` and has no
  use anywhere in package Lean sources.
- Its conclusion is the same partial-correctness `blockSpecs` as
  `blockSpecs_intro`. It offers smaller-measure body specifications as
  optional meta-level hypotheses, but the `wps` jump rule can still
  discharge a jump directly from `Ls`; the theorem itself contains no
  obligation that every recursive jump decreases `μ`.
- It produces no total WP, termination proposition, step bound, or
  engine equation.
- `fib_loop_drive` (`FibExhibit.lean:479`) performs induction on the
  numeric distance and explicitly rewrites with `driveJ_step`,
  `Step.if_true`, `Step.run`, `Step.if_false`, and `driveJ_done`.
- `fib_certified_total` (`FibExhibit.lean:570`) invokes that operational
  proof, not `fib_wps`, `fib_blockSpecs`,
  `blockSpecs_intro_variant`, Iris total WP, or Iris adequacy.
- `FibExhibit.lean:470-472` candidly says the general
  variant-rule-to-bound theorem is open, but the README and walkthrough
  present the total theorem as “the loop variant's step bound” alongside
  the logical invariant story without exposing the separate proof path.

Impact:

The equation proved by `fib_certified_total` is valid and useful as an
engine regression theorem. It is not evidence that the separation logic
supports total correctness. It also bakes the exact two-step body shape
of this example into the total proof. Any change in evaluation
granularity requires replaying the operational proof rather than
reusing a logical total-correctness rule.

The pinned Iris already provides `TotalWeakestPre` and
`TotalAdequacy`. Ignoring that relational/logical layer in favor of
explicit drive rewrites is precisely the architectural failure mode
this audit was asked to look for.

Remediation options, in preferred order:

1. Define the loop total-correctness layer using Iris total WP (`TWP`)
   and prove a jump-aware total statement judgment with a genuinely
   decreasing label measure.
2. If an exact executable step bound is required in addition to
   termination, separate the results:
   - logical theorem: total WP / termination and postcondition;
   - cost theorem: a generic simulation from a logical cost algebra or
     per-rule cost semantics to `driveJ` fuel.
3. Require each back-edge rule to carry a proof that the target measure
   is smaller. Do not make use of the smaller hypothesis optional.
4. Refactor Fibonacci totality as a corollary of the generic theorem,
   then prove total list reversal through the same route.
5. Until then, rename/document `fib_certified_total` as an independent
   operational engine theorem and do not claim it demonstrates total
   correctness of the separation logic.

Acceptance criterion: the total Fibonacci and list-reversal theorems
depend on a generic total statement rule or Iris TWP theorem; their
proofs contain no example-level `Step.*` constructors or `driveJ_step`
chains.

### F-03 — The attachment relation is a manually duplicated, frozen projection

Severity: **High architectural risk**

Evidence:

- `Step.lean` openly describes `Step` as a hand-written mirror.
- `Soundness.lean` separately defines `Redex`, `Decomp`, `RedexJ`,
  `DecompJ`, `FragP`, and `FragJ`, plus shape-specific inversion and
  matching lemmas.
- `Lang.lean:43-46` makes this projected `Step` the Iris `primStep`.
- `Heap.lean:457-460` puts only `Mem` in the state interpretation.
- `Soundness.lean:73-109` freezes the file, tags, externs, tid, thread
  fields, and run state.
- `dischargeStep` (`Soundness.lean:149`) is a package reimplementation
  of selected driver behavior. It accepts one-layer active/killed
  memory outcomes and maps other forms to `offFragment`.
- `drive`/`driveJ` (`Adequacy.lean:77`, `:529`) are package execution
  functions. Loop conclusions do not reach the shipped driver.
- The current Cerberus pin's separate `RelSem` relation and
  `runND_sound` theorem are not connected to this relation.

Assessment:

This is not an unsound way to build a bounded spike. The per-shape
proofs are real, and the frozen fields are mostly described honestly.
It is not a scalable foundation for a logic advertised over Cerberus
Core. Each new construct requires coordinated edits across syntax
recognizers, the Step relation, decomposition, closure, inversion,
engine matching, WP rules, drive classification, and documentation.
Canonical annotation shapes and the exact authored examples influence
which cases are admitted. Silent omission is fail-closed for theorem
truth but fail-open for coverage claims.

Remediation:

1. Choose one authoritative derived relational kernel over a
   Cerberus machine configuration. Either reuse the pinned `RelSem`
   spine or define a syntax-facing round relation directly in terms of
   `step_ctx` plus the real discharge relation. If both layers remain,
   prove their simulation/characterization relationship once.
2. Put every semantically live component needed by supported constructs
   in the relational state or in an explicit immutable `MachineCtx`
   parameter with preservation theorems. Do not hide it in a family of
   example profiles.
3. Make Iris `primStep` the authoritative derived relation, not an
   independently transcribed instruction set. Per-construct WP lemmas
   should characterize instances of that relation.
4. Replace parallel `FragP`/`FragJ` whitelists with one capability
   predicate or a generated coverage table. Prove closure of that
   predicate under steps and substitutions.
5. Retain `drive` only as a test/executable specification if useful;
   exported adequacy should target the canonical Cerberus relational
   or runner statement, with projection theorems as corollaries.

Acceptance criterion: adding a supported Core constructor has one
semantic coverage point, and a theorem states that Iris `primStep` is
equivalent to or soundly characterized by the selected Cerberus round
relation on the supported fragment. Coverage cannot differ between a
logic rule and adequacy without a failed check.

### F-04 — Flagship examples extend the logic with their own layout rules

Severity: **High for example independence; not a soundness failure**

Evidence:

- The core resource is one ghost cell per whole Cerberus allocation.
- The generic core supports whole-cell load/store.
- `Rules.lean:976` adds an integer-specific interior load theorem, and
  `Wps.lean:1558` exposes `wps_load_interior` for the array exhibit.
- `ListRevExhibit.lean:174` and `:223` prove node-pointer-specific
  interior memory lemmas.
- `ListRevExhibit.lean:601` and `:691` define
  `wps_load_interior_node` and `wps_store_interior_node` inside the
  example module, specialized to `nodeTy`, `nodePtrTy`, eight-byte
  fields, and byte splicing.
- The list proof consumes these example-local rules at lines 1454 and
  1478.

Assessment:

All these theorems are proved, so “small axiom” here does not mean a
Lean axiom. The defect is modularity: array and node layouts are not
instances of a general typed subrange rule; they enlarge the logic with
exactly the capabilities their examples require. That makes it hard to
tell whether a new struct proof is a client of the logic or another
logic extension.

Remediation:

1. Introduce generic allocation ownership plus byte-range or typed-view
   ownership, with a proved agreement between subviews and the
   allocation metadata/provenance.
2. Prove generic in-bounds typed load and full-ownership store rules for
   a subrange, parameterized by serialization, decoding, alignment,
   compatibility, and side-table conditions.
3. Derive integer array-element and node-field rules as ordinary client
   lemmas in the example modules.
4. Move all engine discharge facts that are independent of a concrete
   program or layout out of exhibit files.

Acceptance criterion: deleting the array and list modules leaves the
complete memory rule library; recreating either proof requires only
layout/serialization instances and representation predicates, not a new
WP lifting proof.

### F-05 — Loop “production” export is not a production execution theorem

Severity: **Medium**

Evidence:

- README line 71 calls `counter_loop_certified_production` a production
  theorem, but its lane is explicitly “driveJ @ production run state”.
- `ProdEntry.lean:358-374` says the result is only a registration tie
  and that the full production `runND` equation remains open.
- The theorem still executes the package-defined `driveJ`; it does not
  conclude an equation for `_root_.drive` under `CerbND.runND`.
- Straight-line `exhibitA_prod` does reach the shipped pipeline, so the
  distinction is material rather than terminological.

Remediation: rename the current theorem to include “registration” or
“driveJ”, keep it as an intermediate lemma, and reserve “production” for
statements whose execution function is the shipped runner. Prove the
proc-carrying, populated-label scheduler collapse before restoring the
name.

### F-06 — The list theorem is weaker than a standard “in-place reversal” specification

Severity: **Medium**

Evidence:

- `list_reverse_certified` is partial correctness for arbitrary
  `nsteps`, including zero. It proves safety and a postcondition only if
  `driveJ` returns `.done`.
- The conclusion `ChainAt σ' p' xs.reverse`
  (`ListRevExhibit.lean:1245`) describes some final chain with the right
  values and coherent nodes.
- It does not expose the initial node-identity sequence, prove a
  permutation/equality of allocation IDs, state that the same node set
  forms the final chain, or return an arbitrary framed footprint.
- Internally the Iris proof owns and updates the same nodes and performs
  no allocation, so a stronger theorem should be obtainable. The
  exported readout discards that evidence.

Impact: the theorem supports “a reversed chain exists in the final
memory”, but the usual extensional claim “the original cells were
relinked in place and all unrelated state was preserved” is stronger.

Remediation: index `SeedChain`/`isList`/`ChainAt` by an ordered list or
finite set of node allocation IDs; state equality/permutation of the
initial and final node sets; export the semantic frame; and add a total
theorem. Also provide a wrapper specialized to the concrete `SpikeGF`
so the engine-facing flagship statement does not retain a ghost-functor
binder.

### F-07 — The axiom audit is an upper-bound audit, not an exact-cone audit

Severity: **Medium trust-instrumentation defect**

Evidence:

- The curated `#print axioms` probes in `Audit.lean` pin exact output for
  selected theorems.
- The exhaustive pass at `Audit.lean:365-396` only checks that each
  theorem's collected axioms are contained in an allowed list. It does
  not require equality.
- Every theorem in the two boundary modules is allowed
  `runEffectful`, whether it appears in that theorem's statement, proof,
  or not at all.
- README lines 100-118 say every theorem has its “exact axiom cone
  asserted in-build”, that `runEffectful` enters through statements
  only, and that all non-boundary cones are “exactly” the trio. The
  exhaustive algorithm does not establish those claims.

The current build does show that no theorem exceeds its declared upper
bound, and the selected headline cones print as documented. This is a
good control; it is simply described too strongly.

Remediation:

1. Change public wording to “exhaustively bounded; selected headline
   cones exactly pinned” immediately.
2. Isolate declarations whose statements contain
   `initial_driver_state` into a minimal boundary module and prove
   parametric trio-only lemmas elsewhere.
3. For production exports, mechanically check the origin of
   `runEffectful` or exact-pin every public boundary theorem.
4. Change the build summary from “trio-exact” to “within trio” unless an
   equality check is implemented.

### F-08 — `runEffectful` remains a real, known production boundary

Severity: **Known blocker; lower discovery priority than F-01 through F-04**

The axiom is:

```lean
axiom runEffectful {α : Type} : (Unit → BaseIO α) → α
```

It enters through the shipped initial driver/run state used by
production-facing statements. The repository documents the exact
statement, confines the allowed cone to `ProdEntry` and `ProdExhibit`,
and records an upstream retirement plan. That handling is substantially
better than for the newly identified gaps.

It is still unacceptable in the final trusted encoding. The proper end
state is an explicit seed/state parameter or an upstream effectful
initialization theorem whose pure semantic result no longer requires an
axiom. Retirement should proceed in parallel, but it should not consume
the review bandwidth needed to close F-01 through F-04.

### F-09 — Documentation contains concrete contradictions and lacks one authoritative coverage matrix

Severity: **Medium**

Concrete issues:

- README line 379 says `Lang.lean` provides “evaluation contexts,
  wp_bind for real Esseq”. `Lang.lean:18-23` and `:80-88` explicitly
  explain that no `Language.Context` instance can exist for that frame
  because `Erun` discards it.
- README includes value-scrutinee `Ecase` in the certified fragment,
  contradicting `Soundness.lean:3225-3229` and `:4112-4116`.
- The total-correctness narrative does not clearly separate the Iris
  partial proof from the manual operational total proof.
- “Exact axiom cone” overstates the exhaustive gate (F-07).
- “Wrong mirror can only make theorems unprovable” is safe only when the
  engine-facing statement uses a faithful specification idiom and the
  relevant matching theorem is in scope. A bad `drive`, discharge, or
  readout definition can yield a true but irrelevant theorem; a missing
  fragment case can make a rule dead. The slogan needs this
  qualification.
- Dated notes sometimes preserve the accurate status after top-level
  summaries have moved on. There is no generated matrix showing, for
  each construct, Step rule, logic rule, fragment cone, match theorem,
  adequacy lane, production lane, and example consumer.

Remediation: make one generated capability matrix authoritative and
link every overview to it. Separate “proved theorem”, “supported local
rule”, “adequacy-exportable”, and “production-exported”. Add a compact
trust table distinguishing kernel axioms, semantic dependencies,
package specification idioms, validation evidence, and known scope
restrictions.

### F-10 — Whole-allocation ownership and no allocation rule are legitimate restrictions, not yet a general C heap logic

Severity: **Known limitation**

Whole allocations are valid separation units, and the resulting logic
is genuinely local across disjoint allocations. The absence of
`wp_create` is also handled soundly: allocation can fail in states not
constrained by current ownership, so an allocator resource is needed.

These are not defects in the restricted demo, and both are documented.
They become blockers if the project claims ordinary struct/array field
ownership, local allocation reasoning, or parity with a usable C
separation logic. The generic view and allocator work proposed under
F-04 should retire them rather than adding more example-local rules.

## Trust boundary accounting

| Layer | Current status | Audit assessment |
|---|---|---|
| Lean kernel and definitions | All project proofs elaborate; no `sorryAx`/`ofReduce*` found | Appropriate |
| Classical axioms | `propext`, `Classical.choice`, `Quot.sound` | Conventional for this Iris Lean development; accurately exposed for pinned examples |
| Iris Lean | Pinned dependency supplying BI, GenHeap, WP, adequacy, fixpoints | Legitimate use; total WP is available but currently unused |
| Cerberus Lean generated semantics | Pinned at `58ec50779`; differential validation is evidence, not proof of OCaml equivalence | Correctly identified as the authoritative semantics, with upstream validation honestly scoped |
| `runEffectful` | Allowed only in two production boundary modules | Known unacceptable final seam; registered and owned |
| `Step` / fragment cones | Derived package relation with per-shape proofs | Sound where connected, but duplicated and already miscovered |
| `dischargeStep`, `drive`, `driveJ` | Package-defined specification idioms projected from driver behavior | Must not be described as the shipped driver; require a canonical relational/runner bridge |
| `Coh`, `ChainAt`, seeded maps | Package readout/specification idioms | Reasonable, but list readout loses identity/frame facts and whole-allocation granularity is narrow |
| Examples | Genuine compositional partial proofs | Array/list extend the rule layer; fib totality is operational, not logical |

## Remediation plan

The plan is ordered to retire unknown and reproducing defects before the
already-managed `runEffectful` seam.

### Phase 0 — Correct claims and install coverage gates

Goal: make the repository impossible to misunderstand while structural
work proceeds.

1. Correct the README `Lang.lean` row, `Ecase` scope, exact-cone
   wording, totality provenance, loop production naming, and list
   theorem strength.
2. Add a checked capability manifest with columns:
   Core form, relational rule, WP/WPS rule, fragment closure,
   engine-match theorem, partial adequacy, total adequacy, production
   runner theorem, consumer.
3. Make `Ecase` red until either removed from advertised support or
   exported through adequacy.
4. Reclassify `fib_certified_total` as an operational theorem pending
   Phase 3.

Exit criteria:

- No overview claims more than the capability manifest.
- Every advertised construct has an adequacy-level regression theorem.
- Gate output says “bounded” versus “exact” accurately.

### Phase 1 — Establish one authoritative Cerberus relational kernel

Goal: prevent future logic/engine coverage drift.

1. Decide whether to rehabilitate the pinned `RelSem` machine relation
   or define a new syntax-facing Cerberus round relation from
   `step_ctx` and the real discharge protocol.
2. Define a full supported configuration, including all state read by
   the fragment. Immutable fields may live in an explicit `MachineCtx`;
   they must not be implicit example constants.
3. Prove a two-sided characterization on the deterministic supported
   fragment, or document and prove the exact one-sided theorem required
   by adequacy where two-sidedness is impossible.
4. Instantiate Iris `Language` over this relation.
5. Prove the relationship to `RelSem.Step`/`runND_sound` if a distinct
   syntax-facing relation is retained.
6. Derive syntax rules from characterization theorems rather than
   transcribing a second operational semantics.

Exit criteria:

- One theorem identifies the Iris primitive step with the authoritative
  Cerberus derived relation on the supported fragment.
- The supported state includes or explicitly parameterizes every field
  read by those steps.
- `FragP`/`FragJ` divergence is eliminated or mechanically impossible.
- Value `Ecase` and one new non-example construct pass through the same
  generic route.

### Phase 2 — Make the heap logic generic enough that examples are clients

Goal: obtain a reusable Reynolds/O'Hearn memory layer rather than a
collection of layout-specific WP proofs.

1. Split allocation metadata/provenance authority from byte or typed
   range ownership.
2. Add generic subrange splitting/joining and agreement laws.
3. Prove generic typed load/store rules for interior ranges, including
   serialization, decoder, alignment, bounds, type compatibility, and
   side-table obligations.
4. Add allocator-cursor or allocation-capability ownership and prove a
   sound `wp_create`/`wps_create` rule.
5. Re-express arrays and nodes entirely through instances of those
   generic rules.

Exit criteria:

- No example module defines a new WP/WPS lifting rule.
- Array and list proofs survive replacement of their concrete layout by
  another layout satisfying the same generic view interface.
- A fresh struct example can be verified without editing core logic.

### Phase 3 — Put total correctness back in the logic

Goal: make variant reasoning a relational/logical capability.

1. Use Iris `TotalWeakestPre`/`TotalAdequacy`, or justify and implement
   an equivalent least-fixpoint total judgment.
2. Define a jump-aware total statement judgment whose back-edge rule
   requires a strictly decreasing well-founded measure.
3. Prove its collapse to total WP and its adequacy over the authoritative
   Cerberus relation.
4. Separately add a generic cost semantics if exact runner fuel bounds
   are desired.
5. Refactor Fibonacci totality and add total list reversal as clients.

Exit criteria:

- Removing the decrease proof makes a looping example unprovable.
- `blockSpecs_intro_variant` is either replaced or has a theorem-level
  termination consequence.
- Total example proofs contain no explicit engine `Step` constructors.

### Phase 4 — Strengthen the flagship specifications

Goal: ensure examples demonstrate the intended properties rather than
weaker readouts.

1. Carry node identities/footprint through `isList` and `ChainAt`.
2. Prove final node IDs are exactly a permutation of the initial IDs.
3. State and prove preservation of an arbitrary disjoint frame.
4. Add a total step or total-WP theorem for reversal.
5. Export a concrete engine-only wrapper using `SpikeGF`.
6. Add a second, structurally different client—such as a tree rotation
   or two distinct struct layouts—to test that list accidents have not
   become logic laws.

Exit criteria: the public theorem literally states same-footprint,
in-place reversal plus termination and frame preservation.

### Phase 5 — Complete production attachment and retire declared trust

Goal: make final public theorems about the shipped runner.

1. Prove the loop scheduler/driver collapse for proc-carrying threads
   with populated labels.
2. Export total loop examples as `_root_.drive` / `CerbND.runND`
   theorems.
3. Retire `runEffectful` upstream by explicit initialization state or
   seed threading.
4. Narrow the boundary module while retirement is in progress and
   exact-pin all public theorems that still carry the axiom.
5. Re-run semantic-pin and differential validation gates after any
   upstream pin change.

Exit criteria:

- Public production theorems mention no package `drive`/`driveJ`.
- No project theorem depends on `runEffectful`.
- The exhaustive axiom audit reports only the declared classical base.

## Recommended acceptance suite

A “good and legitimate state” should be judged by these tests, not by
line count or number of mirrored constructors:

1. **Rule-consumption test:** every advertised syntax rule reaches an
   engine-facing adequacy theorem.
2. **Fresh-client test:** verify a new struct-manipulating program
   without adding core WP rules.
3. **Perturbation test:** alter field offsets/layout through an interface
   instance; examples should require only instance proofs.
4. **Totality test:** Fibonacci and list reversal derive from total WP;
   no operational replay in exhibit proofs.
5. **State-read test:** a generated/read-set census for every supported
   Cerberus step is covered by relational state or explicit immutable
   context.
6. **Production test:** at least one loop theorem concludes directly
   about the shipped `runND (Driver.drive ...)` computation.
7. **Axiom test:** exhaustive upper-bound sweep, exact pins for all
   public exports, and zero `runEffectful` after retirement.
8. **Mutation tests:** deleting a fragment constructor, engine match
   case, readout field, or measure-decrease premise must make a named
   gate fail.

## Validation performed for this audit

Read and traced:

- all main logic and attachment modules (`Heap`, `Step`, `Lang`,
  `Rules`, `Wps`, `Soundness`, `Adequacy`, `DriverCollapse`,
  `ProdEntry`, `Audit`);
- the counter, Fibonacci, array, and list-reversal exhibits;
- the README, walkthrough, decisions register, relational-semantics
  candidate memo, hostile review, and phase/list audit notes;
- the pinned Iris total-WP implementation and the pinned Cerberus
  `RelSem` spine.

Mechanical checks:

```text
./scripts/test_unit.sh
  root package: build successful
  cerberus-heaplang: build successful
  heaplang theorem sweep: 755 within declared upper bounds
  banned-axiom sweep: 1499 constants checked
  sorryAx/ofReduceBool/ofReduceNat: absent
  banned source methods: absent
```

Targeted use searches additionally established that
`blockSpecs_intro_variant` and `wps_case_value` have no package
consumer, and that no `RelSem` module is imported by
`cerberus-heaplang`.

## Final assessment

The right disposition is **retain and refactor**, not reject. The work
already demonstrates the hard core of the idea: Iris BI resources can
be coupled to Cerberus memory, small axioms can be proved, and Iris
adequacy can be connected to real generated engine functions. That is a
meaningful result.

The next milestone should not be another example or another mirrored
constructor. It should be closure of the semantic architecture:
one authoritative derived relation, mechanically complete rule
coverage, generic interior ownership, and a logical total-correctness
path. Once those are in place, the examples will test the logic rather
than shape it, and the remaining production work—including the known
`runEffectful` retirement—will have a trustworthy foundation to land on.
