# Skeptical re-audit of `cerberus-heaplang`

Date: 2026-09-01

Audited revision: `e9bcaef50fc78eff73055fcd6aa9be70140306ac` (`main`, equal to `origin/main`)

Cerberus Lean revision: `58ec50779f036da1794c440d215d41a755027382`

iris-lean revision: `34390a0133986385c62bf59a6eb01938945b48ec`

## Executive verdict

The revision builds cleanly against the pinned Cerberus Lean and
iris-lean revisions, and the new total-correctness layer is substantive.
There is now a real Iris-backed, relational separation logic for the
package's restricted Core language. In particular, the base triple has
real separating conjunction, frame, consequence and sequencing; the
statement logic handles label invariants; and the total statement
judgment enforces a decreasing budget and collapses to iris-lean's
`TotalWeakestPre`.

The project is nevertheless **not yet in the intended end-to-end state**.
The principal defect is not `runEffectful`. It is a previously
unaccounted-for break in the heap-allocation proof path:

1. `wps_create` requires an exclusive `cursorOwn` resource, but every
   partial- and total-adequacy launcher initializes the cursor ghost map
   to the empty map and gives the client only seeded cell ownership.
   There is no cursor-allocation lemma or adequacy launcher that gives a
   client `cursorOwn`. Consequently the advertised create rule cannot be
   used by an adequacy proof.
2. The self-contained heap-allocating production examples work around
   that break by constructing concrete `Step.create`/engine traces in the
   example modules. Their store/load or loop suffixes use the logic, but
   their allocation prefixes do not. `exhibitA_prod` additionally uses a
   handwritten six-step operational trace for termination.

This is exactly the combination the audit was asked to reject: a
proper-looking logic rule that is stranded, paired with example-specific
operational reasoning that bypasses it. The capability manifest calls
these examples consumers but checks declarations and names, not proof
dependencies, so all gates pass despite the break.

The appropriate overall classification is therefore:

- **Reynolds/O'Hearn separation logic:** yes for the restricted,
  already-seeded fragment; not yet for the complete self-contained heap
  demos because allocation is outside the usable logical path.
- **Based on Cerberus Lean:** qualified yes. The language uses Cerberus's
  real generated syntax, memory and engine functions, and its custom
  `Step` is certified against `step_ctx`. It is still a package-authored
  semantic projection with mostly one-sided certification, not the
  pinned `RelSemCore` relation or a proved equivalent presentation.
- **Using iris-lean:** yes, genuinely. The BI, GenHeap, WP, adequacy and
  TotalWP components are consumed rather than merely imitated.
- **Trust story:** conventional kernel/dependency trust is well gated;
  semantic-projection and coverage trust remain larger than the current
  headline documentation admits.
- **Documentation:** not adequate at this revision. It contains stale
  contradictions and makes the stranded allocation path look closed.

The two allocation findings are release blockers for calling the project
a clean end-to-end demo of separation logic over Cerberus Core.

## Scope and method

This review treated the three requested properties as separate proof
obligations:

1. the logic must have the standard local, relational shape associated
   with Reynolds/O'Hearn separation logic;
2. the Iris language and state interpretation must attach that logic to
   Cerberus Lean without an unreported semantic shortcut; and
3. the examples must consume that interface, rather than validate their
   conclusions by replaying their own concrete programs.

The audit read the language instance, ghost-state coupling, base rules,
partial and total statement judgments, soundness and adequacy layers,
all headline example proof bodies, production collapse, audit gates,
capability manifest and user-facing documentation. It also performed
exhaustive source searches for allocator resources, advertised view
laws, frame rules and direct operational proof terms.

The full repository test was run from the root:

```text
./scripts/test_unit.sh
```

Result: all five gates passed. The root package built; the standalone
heaplang package completed 443 jobs; the in-build axiom and banned-axiom
sweeps passed; the capability manifest and statement census were
drift-free. The final line was `ALL GATES GREEN`.

This is valuable evidence for reproducibility and theorem hygiene. It is
not evidence that a named consumer actually depends on the corresponding
logic rule, which is the gap exposed below.

## What the new revision genuinely fixes

The remediation since the earlier foundational audit is significant and
should be retained.

### A real total statement logic now exists

`Wpt.lean:77-78` defines label specifications indexed by a natural-number
variant. `wpt.pre` is structural in the budget; its jump clause includes
the mandatory fact `1 + m <= k` (`Wpt.lean:99-137`), and a non-value,
non-jump at zero budget is false. `blockSpecsT` verifies each registered
body at its claimed variant. `wpt_sound` proves the collapse into
iris-lean's total WP (`Wpt.lean:1823-1870`), and
`wpt_strongly_normalizing` consumes `twp_total` directly
(`TotalAdequacy.lean:953-1008`). The generic `wpt_engine_boundU/J`
simulation connects this judgment's budget to engine fuel.

The fib, list-reversal and tree examples' total proofs use this layer;
they do not contain example-level `Step` constructor or `driveJ_step`
chains. `DivergeExhibit` is a useful negative test: its deliberate
self-step is incompatible with the total judgment. The former criticism
that termination was merely a side-car operational simulation is thus
closed for those examples.

### The Iris use is real

The base triple is literally an Iris WP entailment at `NotStuck`
(`Rules.lean:834-842`). Its frame and consequence theorems are derived
from Iris BI/WP rules (`Rules.lean:844-855`). The statement WP is a
guarded Iris fixpoint with value, jump and relational step clauses
(`Wps.lean:112-181`), and `wps_sound` collapses it to the base Iris WP
(`Wps.lean:2404-2455`).

The state interpretation uses three iris-lean GenHeaps: allocation
metadata, individual bytes and the allocator cursor. `pointsToCell` and
`pointsToView` are spatial assertions; byte ranges split at separating
conjunction; stores update owned ghost bytes. This is not a shallow
encoding of Hoare triples as arbitrary Lean propositions.

### The logical operational semantics is relational

The Iris `Language` instance defines `primStep` as the Prop-valued custom
`Step` relation over a runtime tuple containing the Core expression,
environment and `MachineCtx` (`Lang.lean:1-73`). `wps.pre` and `wpt.pre`
quantify over every `PrimStep` successor, rather than calling the engine
as an evaluator inside each client proof.

The main engine attachment theorem, `engine_step_matchU`, says that a
mirror step at any well-sized `Frag` expression produces exactly the
matching singleton result from the engine (`Soundness.lean:4384-4405`).
The Iris `NotStuck` obligation supplies such a relational step. This is a
defensible soundness architecture for a restricted deterministic engine
fragment, provided that operational unfolding stays in the generic
attachment layer and the supported-fragment claim remains qualified.

### Generic heap views and multiple clients are substantive

The byte and metadata ghost layers are generic, and the array, list,
struct and tree examples reuse the generic interior load/store rules.
The tree-rotation client is especially useful evidence that the logic is
not merely specialized to a single linear list example. The semantic
`SemTriple` also quantifies over an arbitrary disjoint cell-map rest and
returns it (`Adequacy.lean:731-747`), while `semantic_frame` provides a
named-frame theorem (`Adequacy.lean:911-930`).

These successes make the remaining allocator break more important, not
less: the internal architecture is now strong enough that example-level
operational allocation should no longer be necessary.

## Findings

### R-01 — Critical: the allocation rule is unreachable from adequacy

`cursorOwn c` is full ownership of key `0` in the cursor GenHeap
(`Heap.lean:1183-1185`). `wps_create` requires it as its precondition and
returns the advanced cursor with the newly allocated cell
(`Wps.lean:2184-2206`). Its local proof is substantial: it reads the
cursor against `CohG`, executes the real allocator seam and updates
metadata, bytes and cursor ghost state.

The problem is launch, not the local rule.

Every relevant launcher creates the cursor GenHeap with the empty map:

- `spike_step_adequacy`: `Adequacy.lean:413-442`;
- `wpt_engine_boundU`: `TotalAdequacy.lean:889-911`;
- `wpt_strongly_normalizing`: `TotalAdequacy.lean:975-1002`.

Each then passes the user's proof only the big separating conjunction of
`cellOwn`s. None passes `cursorOwn`. An exhaustive source search finds
`cursorHeap_update` but no `cursorHeap_alloc`, and the only actual client
of `wps_create`, `struct_create_store_wps`, is a local entailment whose
premise already assumes `cursorOwn` (`StructExhibit.lean:319-351`). It is
not consumed by an engine- or adequacy-facing theorem.

This is not merely an absent convenience lemma. With the cursor authority
initialized at the empty map, the exclusive fragment at key `0` cannot
be invented by the client. `CohG` intentionally makes allocator-health
facts vacuous when the cursor map is empty (`Heap.lean:1205-1233`), so
the existing `Coh` launch assumption also does not provide the facts
needed to seed a live cursor for an arbitrary memory.

There is a second abstraction problem in the same interface. A simple
Reynolds/O'Hearn allocation rule should normally look like
`{emp} alloc(n) {p. p |-> uninit[n]}` (with failure or a global allocation
health premise modeled explicitly). It should not require a client to
own Cerberus's implementation cursor and predict its next address and
allocation id. Exact cursor reasoning can be an internal lemma, but it
is the wrong public abstraction for the intended simple separation
logic.

Impact:

- no heap-allocating whole program is currently proved by `wps_create`
  through adequacy;
- the manifest's statement that the create defect is retired is false;
- the total logic has no `wpt_create`, so it cannot verify a
  self-contained allocating program at all;
- the deterministic allocator's incidental cursor layout leaks into
  the client specification.

Required remediation:

1. Define an explicit allocator-health invariant for launch states. It
   must justify fresh ids, absence from dead allocations, a nonzero fresh
   base for the supported allocation sizes, and the ordering facts needed
   by existing tracked metadata and bytes.
2. Put allocator authority inside `stateInterp`, or otherwise arrange
   that allocation can update it while it is temporarily available to a
   WP rule. Do not expose the linear cursor token in the public client
   precondition.
3. Retain the exact-cursor theorem as an internal rule if useful, but
   export an existential allocation rule that returns the engine-produced
   pointer and its fresh `pointsToCell`.
4. Add partial and total adequacy launchers that initialize and preserve
   the allocator invariant from the actual `MemState.lastAddress` and
   `nextAllocId`.
5. Add `wpt_create` and prove it through the same relational step clause.
6. Add both partial and total, engine-facing allocate-then-initialize
   consumers. A theorem ending at `wps` is not an adequacy consumer.

Acceptance test: deleting either the public create rule or allocator
launch initialization must break a headline self-contained allocation
theorem.

### R-02 — Critical: allocating examples bypass the separation logic

The allocating production results are established partly by the logic
and partly by concrete example-specific traces.

In `ProdExhibit.lean`, `semAProd` proves only the store/load compute
suffix via `SemTriple` (`ProdExhibit.lean:222-225`). The create prefix is
proved by unfolding `drive`, `engineSteps_create` and the beta step
(`ProdExhibit.lean:227-257`). `prodA_terminates` then manually unfolds
the store, annotation beta, load, merge, annotation removal and done
rounds (`ProdExhibit.lean:299-363`). `exhibitA_prod` combines those
operational witnesses with the partial semantic triple
(`ProdExhibit.lean:372-390`).

`counter_loop_certified_production` is logic-driven for its loop, but the
cold-start create prefix is an explicit `Step.sseq_ctx (Step.create ...)`,
`Step.sseq_pure`, followed by two `driverDone_step` applications
(`ProdLoopExhibit.lean:275-321`). `list_reverse_certified_production`
does the same for two creates and their sequencing, with four explicit
`driverDone_step` links (`ProdLoopExhibit.lean:880-976`). The production
fib theorem is the positive control: because it allocates no heap, it can
remain in the generic total-logic path.

The older straight-line `Exhibit.lean` also contains an example-specific
`engineSteps_store`/beta/load/merge/remove/done termination trace. A
generic semantics attachment module must of course reason operationally;
a total theorem for a user program should not.

This is not unsound—the concrete traces are proved—but it defeats the
purpose of the demo. A reader cannot conclude that the separation logic
verifies the self-contained allocating programs. They can conclude only
that the logic verifies a suffix after an operationally proved setup.

Required remediation:

1. After R-01, prove each complete program in `wps`/`wpt`, including all
   creates, stores, loads and loop back edges.
2. Derive production equations only through generic adequacy and driver
   collapse theorems. Positive example modules should contain no direct
   `Step.*`, `engineSteps_*`, `driveJ_step` or `driverDone_step` proof
   chains.
3. Keep direct operational reasoning in `Soundness`, `DriverCollapse`
   and narrowly identified negative tests such as `DivergeExhibit`.
4. Add a source-layer gate for direct forbidden dependencies in positive
   exhibit declarations. Also add dependency witnesses showing that each
   headline construct actually flows through its named logical rule;
   text search alone is not sufficient because a helper can hide a
   bypass.

Acceptance test: the complete create/store/load theorem and at least one
allocating loop production theorem must fail if `wpt_create` is removed,
and their example-level proof declarations must have no direct
operational-semantic dependencies.

### R-03 — High architectural risk: the Cerberus relation is still a bespoke projection

The package's `Step` is a 1,943-line hand-written relation over Cerberus
types. `Soundness.lean` is a 4,943-line proof that selected constructors
match the concrete engine. Most of the unified cone is certified in the
mirror-to-engine direction by `engine_step_matchU`; only selected parts
have explicit two-sided completeness theorems. The package deliberately
does not import or bridge to the pin's `RelSem.Machine.Step`,
`runND_sound` or `HarnessAdequate`; the README says so at
`README.md:231-244`.

This does **not** mean the current Iris reasoning is operational rather
than relational. Iris runs over the Prop relation in `Lang.lean`, and the
generic matching theorem is enough for sound execution of a reducible,
in-cone configuration through this deterministic driver path. Nor is the
Cerberus `RelSemCore` relation necessarily the right granularity for
local heap rules.

The remaining trust issue is semantic duplication and coverage. A missed
engine behavior, a too-weak fragment side condition, or an omitted
constructor is a modeling error outside the Lean kernel's view. The pin
prevents silent upstream drift, but it does not prove that the custom
relation is the desired relational C semantics. Calling this logic
unqualifiedly "over Cerberus Core" is stronger than what is currently
proved; it is over a certified package projection of a selected Core
engine fragment.

Required remediation: make one of the following choices explicit and
complete it.

- Preferred: define Iris `primStep` from the relational graph of one
  discharged Cerberus engine round, then derive syntax-directed
  introduction/inversion lemmas for logical use. This removes a second
  authoritative transition system.
- Alternative: retain the ergonomic custom `Step`, but prove a two-sided
  equivalence with the discharged engine relation for every `Frag`
  configuration, including an explicit classification of refusal and
  nondeterministic channels.

If the project intends to claim compatibility with Cerberus Lean's
separate `RelSemCore` semantics, add a bridge theorem. If not, state that
the engine-round graph is the chosen reference relation and explain why
that choice has the right granularity. In either design, direct engine
unfolding belongs in this attachment proof, not in clients.

### R-04 — High: the capability gate validates declarations, not use

The manifest defines an exportable row from mirror, cone, engine-match,
partial-lane and consumer cells, and defines `fullRow` by adding only the
logic cell (`scripts/capability_manifest.lean:89-106`). Total and
production cells are omitted from `fullRow`. The create row lists
`wps_create`, `exhibitA_prod` and `struct_create_store_wps` by name while
also admitting that no `wpt_create` exists and that production creates
cross `driverDone_step` instead (`scripts/capability_manifest.lean:198-212`).

The generator checks existence/kind and drift. It does not prove that
`exhibitA_prod` depends on `wps_create`, that
`struct_create_store_wps` reaches adequacy, or even that a named consumer
uses the construct rather than merely being about a program containing
it. `FULL-ROW` is consequently a misleading label for rows whose total
or production lanes are red.

This gate failed its most important adversarial test in the live tree:
it reports create as certified while the create logic rule is
unlaunchable and the production consumers bypass it.

Required remediation:

1. Separate “declared theorem exists” from “dependency-certified
   consumer”.
2. For each public row, check a staged dependency chain: logical rule ->
   WP collapse -> adequacy -> engine/production consumer.
3. Require a genuine execution witness for the syntax constructor and a
   proof dependency on its logical rule. For create, also require the
   allocator-launch theorem.
4. Either include logic, total and production in `FULL-ROW`, or rename
   the current output to `CORE-DRIVE-ROW` and report each lane separately.
5. Add a planted test where a consumer name remains but its proof is
   replaced by a direct trace; gate 4 must fail.

### R-05 — Medium: statement/loop framing is not a reusable standard rule

The base `triple_frame` and semantic frame theorem are good. At the
statement layer, however, `wps_frame` explicitly says the frame is
released at a jump and only the label invariant crosses a back edge
(`Wps.lean:276-289`). The total layer has no general `wpt_frame` theorem.
The list and tree clients compensate by parameterizing every label
invariant and postcondition by an `RF` proposition and threading it
manually.

That is sound but it is not the clean user-facing frame abstraction one
expects from a Reynolds/O'Hearn presentation of loops. It also means the
presence of a base frame theorem does not demonstrate a reusable frame
rule for the headline statement logic.

Required remediation: define framing of a label specification, for
example by mapping every label assertion to `Ls ... * R`; prove framing
for `blockSpecs`/`blockSpecsT` and for `wps`/`wpt`; then derive framed
list/tree theorems from unframed bodies. The examples should instantiate
a generic rule rather than bake `RF` into each invariant definition.

### R-06 — Medium: advertised split/fractional features have no client

`metaOwn_fractional`, `pointsToView_split` and `pointsToView_join` are
proved in `Heap.lean:1345-1427`. Exhaustive search finds no use outside
their definitions. The interior load/store rules instead split byte
ranges directly with `bytesOwn_append`, which is genuinely used. All
headline reads use full ownership; there is no nontrivial fractional
read example and no client that splits one allocation into simultaneous
typed field views and recombines it.

These laws may be correct, but under the requested standard they are
cargo-cult surface until exercised. Either add:

- a struct/tree client that obtains disjoint typed field views using
  `pointsToView_split`, updates through those views and rejoins; and
- a read-only client using a proper fraction and preserving it;

or remove fractional/split/join capability claims until such consumers
exist. The dependency-aware manifest should enforce the decision.

### R-07 — Medium: production modules contain non-production scaffolding and example constants

`StmtProbe/` is a separate 1,398-line toy language and statement logic.
The top-level library imports it (`CerberusHeapLang.lean:26`), the audit
sweeps and pins it, yet the README says it has no bearing on the claims
and is retained only as a record (`README.md:514-516`). This is almost a
literal example of a second proper-looking but unused logic in the
production library.

Similarly, `Rules.lean` contains `intTy`, the values and byte encodings
for 5/6/7, and `exhibit`/`exhibitC_triple`; `Wps.lean` ends with
`wps_exhibit_store_frame` and `wps_exhibit_seq_stores`. These do not make
the generic rules unsound, but they blur the boundary between logic and
examples and make accidental example coupling harder to detect.

Required remediation: move `StmtProbe` to an archival/test target not
imported by `CerberusHeapLang`; move example constants and canned example
proofs into exhibit modules. Keep the production library's dependency
direction `semantics -> logic -> adequacy -> clients` mechanically
acyclic.

### R-08 — Medium: one loop still pins an accidental environment-map representation

`LoopExhibit.lean` deliberately defines and threads `IsXFrame`, which
pins a precise `Fmap` shape (`LoopExhibit.lean:152-201`). The package now
has generic `SymFrame` laws in `EnvLaws.lean`, and later clients use
them. Retaining the representation-pinned first loop makes the counter
and its production theorem weaker evidence of a clean abstract logic.

Required remediation: port the counter proof to `SymFrame` and delete
the TreeMap/Fmap-shape pin. Add a test with an irrelevant binding in the
same frame so the proof cannot regress to exact-map equality.

### R-09 — Medium: `SemTriple` is less general than its prose suggests

`SemTriple` quantifies over every memory satisfying `P` plus an arbitrary
disjoint cell frame, which is the right spatial quantification. It still
runs only `spikeThread e` in the fixed `spikeCtx`/`spikeEnv`
(`Adequacy.lean:739-747`). The internal runtime and unified matching
theorems support arbitrary `MachineCtx`, but this exported base semantic
triple is not over every Cerberus configuration.

Required remediation: either generalize the semantic triple over a
well-formed `MachineCtx` and entry environment, or consistently describe
it as “all compatible memories at the fixed demo machine profile.” The
current phrase “every configuration” should not survive unchanged.

### R-10 — Medium: documentation is contradictory and overstates closure

The source and README contain enough design material to reconstruct the
architecture, but not a reliable current trust story. Concrete examples:

- `Wps.lean:56-60` says no `wps_create` exists at any layer, while the
  theorem exists at line 2192.
- The README's seam table still says whole-allocation cells have no
  per-byte split (`README.md:370`), despite the new byte/view layer.
- The same table says the production loop export is still waiting
  (`README.md:377`), although Phase 5 production theorems are present.
- The module table calls value-case “local rule only” and names retired
  `DecompJ.step_factor`/`engine_step_matchJ`
  (`README.md:489,496`), while the current code has `Frag.case_value` and
  `engine_step_matchU`.
- `Soundness.lean:3557-3575` likewise says `Ecase` stays out immediately
  before the current `Frag` definition that includes it.
- The manifest and README say the allocator defect is retired, but no
  adequacy launcher supplies its resource.
- `README.md:305-316` describes production loops as being driven by the
  total statement judgment without clearly disclosing that allocating
  prefixes are handwritten semantic rounds.

The root `docs/2026-09-01_foundational-re-audit.md` concludes “zero High”
and treats the existence of `struct_create_store_wps` as closure. It did
not trace the cursor resource into adequacy and therefore must not be
used as the current acceptance record.

Required remediation: update the README, walkthrough, manifest notes and
trust diagram only after R-01 through R-04 are implemented. Generate
theorem names and capability status where possible. The documentation
must distinguish:

- local rule proved;
- rule usable from an adequacy launcher;
- partial consumer;
- total consumer;
- production consumer;
- exact semantic relation against which each statement is proved.

### R-11 — Known, Low for this audit: `runEffectful`

The production boundary still depends on the known `runEffectful` axiom.
The in-build audit bounds it to production-entry statement cones and
checks that non-boundary theorems use only `propext`, `Classical.choice`
and `Quot.sound`. This is currently documented and is not the dominant
new risk.

One qualification should be preserved: an “origin check” can establish
that a boundary statement carries the axiom and that clean modules do
not; it cannot, merely from the final axiom set, distinguish the intended
statement-borne occurrence from an additional proof-side occurrence once
the same theorem statement already mentions `runEffectful`. Keep the
retirement plan and avoid expanding this boundary while fixing the
logical defects above.

## Answers to the three audit questions

### 1. Is this legitimately a Reynolds/O'Hearn logic connected through Iris to Cerberus Lean?

**For the seeded-memory restricted fragment, yes. For the advertised
self-contained heap language, not yet.**

The spatial assertions, frame/consequence rules, compositional
load/store rules, loop invariants, Iris WP collapse and adequacy are
genuine. The total extension is also genuine. The current fatal break is
allocation: the public-looking rule is neither a standard abstract
allocation spec nor usable from adequacy, and allocating examples cross
the missing portion operationally.

The Cerberus connection is real but should be described precisely: the
logic is over a package-defined relational projection that is proved to
match selected discharged engine rounds. It is not yet proved equivalent
to all Cerberus Core behavior or to Cerberus Lean's separate `RelSemCore`
presentation.

### 2. Are there unacceptable or unaccounted trust gaps?

There is no newly found kernel-level axiom hole, `sorry`, or build/pin
failure. The unacceptable gaps are modeling and proof-architecture gaps:

- stranded allocator ownership and an unlaunchable allocation rule;
- direct operational proof of the allocation prefixes and termination
  traces of headline examples;
- a manually maintained, mostly one-sided semantic projection without a
  dependency-aware coverage oracle; and
- claims gates that validate names rather than proof flow.

The known `runEffectful` seam is smaller and better accounted for than
these new findings.

### 3. Is the documentation adequate?

**No.** It is extensive, but extensiveness is not the same as reliability.
The current material is stale in mutually contradictory ways and labels
the create path closed without tracing its resource to launch. A reader
can understand many individual modules but cannot obtain an accurate
end-to-end design and trust story from the headline documents.

## Effect of the future RefinedC-style target

The eventual target is a variant of RefinedC over Cerberus Lean, using
iris-lean. That does not require this small demo to reproduce RefinedC's
semantic type system, Lithium automation, concurrency or complete C
coverage. It does change what counts as a successful scaffold.

The local RefinedC checkout in `../deps/refinedc` provides a useful
architectural comparator:

- Caesium supplies a relational Iris language. Its `state_interp` is the
  authoritative `state_ctx` (`theories/caesium/lifting.v:9-20`).
- The raw memory model separates authoritative heap/allocation state from
  user resources: byte points-to, persistent allocation metadata and
  bounds, allocation-liveness tokens and `freeable`
  (`theories/caesium/ghost_state.v:54-197`).
- Its expression allocation rule returns an existential fresh location,
  bytes and a freeability token; the client never reasons about an
  allocator cursor (`theories/caesium/lifting.v:979-998`).
- Allocation success and allocation failure are both in the relational
  semantics. Failure enters a dedicated non-terminating state rather than
  being classified as UB (`theories/caesium/lang.v:487-494,542-544`).
- Statement WP and recursive block reasoning are a layer over expression
  WP (`theories/caesium/lifting.v:1002-1021,1306-1320`).
- Semantic refinement types are a still higher layer over those raw
  resources (`theories/typing/type.v`); automation is separate again.

The Cerberus engine is not Caesium. In particular, the current Cerberus
driver classifies a failed `allocateObject` request as a refused/killed
driver outcome, not RefinedC's deliberate `AllocFailed` divergence. The
demo must not invent RefinedC behavior and call it Cerberus soundness.
Instead it should make its no-OOM policy an explicit abstract resource or
support an honest failure result if the chosen Cerberus semantic face
provides one.

The scaffold should therefore establish the following migration
contract, without implementing the future type system:

| Concern | This demo must settle now | Deferred RefinedC-style layer |
|---|---|---|
| Reference semantics | One explicit relational Cerberus transition and a fail-closed coverage theorem | Broader C/Core coverage and frontend translation |
| Iris state | Authoritative bytes, allocations and allocator health tied to real `MemState` | More ghost state for sharing, invariants and concurrency |
| Client memory resources | Abstract locations/pointers, byte ranges, bounds/metadata knowledge, ownership split/join | Semantic `type` interpretations over locations and values |
| Allocation | Existential pointer result, explicit failure/capacity policy, no public cursor arithmetic | `malloced`, freeability, lifetime and ownership disciplines |
| Statements | Reusable label specs, sequencing, frame and total variants | Typing judgments for generated statements/functions |
| Automation | Dependency/capability auditing only | Lithium-style proof search and frontend-generated obligations |
| Adequacy | Raw logic to relational semantics to production runner | Whole translated-program and function-spec adequacy |

This makes several current cleanup items strategically important rather
than cosmetic. A duplicated or one-sided transition system would be a
bad foundation for a type system. Client-visible allocator cursor state
would leak through every future allocation type rule. A statement logic
without a reusable frame transformation would force future semantic
types to bake frames into each control-flow invariant. Conversely, it
would be cargo cult to add a `type` record or automation framework now
without a client and soundness theorem. The demo should finish the raw
semantic and separation-logic layers first.

## Implementation-grade remediation plan

The phases below are ordered. Later feature work should not be used to
declare an earlier phase closed.

### P0 — Correct the claims before changing the logic

Affected files: `README.md`, `docs/CAPABILITY_MANIFEST.md`,
`scripts/capability_manifest.lean`, the previous re-audit summary and
module headers in `Wps.lean`/`Soundness.lean`.

1. Mark create as “local rule only; allocator resource not launchable.”
2. Mark `exhibitA_prod`, `counter_loop_certified_production` and
   `list_reverse_certified_production` as mixed logical/operational
   proofs, not create-rule consumers.
3. Rename the present `FULL-ROW` output or make its definition include
   logic, partial, total and production cells.
4. Remove the stale statements that no `wps_create` exists, that
   per-byte splitting is absent, that `Ecase` is local-only and that the
   production loop export is pending.
5. Add a closure table for R-01 through R-11 with an owner, intended
   theorem names, test and status. “Theorem exists” is not an acceptable
   closure test.

Definition of done: generated and handwritten claims say exactly what
the current proof graph says, even before the defect is fixed.

### P1 — Repair allocation with a public abstraction that can migrate

This phase should not merely pass `cursorOwn` into the existing examples.
That would make the rule reachable while preserving the wrong client
abstraction.

#### P1.1 Choose and state the allocation-failure policy

For the current `NotStuck` logic and the production driver, the
recommended minimal policy is an **abstract finite allocation-capacity
resource**. It certifies that a known finite sequence of create requests
will not hit Cerberus's allocation-refusal path. This is faithful to the
concrete deterministic allocator while hiding its cursor.

Add internal data and pure relations, with names of this shape:

```lean
structure AllocReq where
  align : Int
  ty : ctype

def advanceCursor : AllocCursor -> AllocReq -> Option AllocCursor
def PlanFits : AllocCursor -> List AllocReq -> Prop
```

`advanceCursor` must use the same `freshBase`, positive-size and nonzero
guard as `allocateObject_success`; `PlanFits` must run requests in order.
The type-specific non-atomic and decode-inert premises can remain on the
logical create rule rather than in `AllocReq`.

Expose an opaque logical assertion, not `cursorOwn`:

```lean
allocCap (reqs : List AllocReq) : IProp GF
```

Its implementation may existentially own the current cursor fragment
and a pure `PlanFits` proof. Client theorems must use only introduction,
create and weakening/elimination lemmas for `allocCap`; they must never
name `lastAddress`, `nextAllocId`, `freshBase` or `cursorOwn`.

An alternative policy—model a failure result or failure state—is
acceptable only after proving how it corresponds to an actual Cerberus
relational outcome. Do not copy RefinedC's `AllocFailed` loop unless the
Cerberus semantics is deliberately changed and that change is part of
the trusted semantic dependency.

#### P1.2 Strengthen launch coherence

`Coh` currently says that tracked cells exist and are disjoint. Add a
launch predicate, for example `LaunchCoh σ m`, that extends it with the
non-vacuous facts required by `CohG` when cursor key `0` is present:

- every tracked allocation id is below `σ.nextAllocId`;
- all ids at or above `σ.nextAllocId` are absent from both live and dead
  allocation tables;
- every tracked allocation and byte address lies at or above
  `σ.lastAddress`; and
- the requested initial `AllocPlan` fits the actual
  `⟨σ.lastAddress, σ.nextAllocId⟩`.

Prove these facts generically from a footprint plus explicit allocator
health. Prove a concrete instance for `prodMem₀`; do not encode its errno
address or the demo's future allocations in the generic theorem.

#### P1.3 Add one shared allocation-aware launcher

In `Adequacy.lean`, factor initialization into a helper with a result of
this conceptual shape:

```lean
launchResources σ m reqs :
  emptyMetaInterp * emptyByteInterp * emptyCursorInterp ==*
  stateInterp σ 0 [] 0 * cellsOwn m * allocCap reqs
```

The proof must call iris-lean's `genHeap_alloc` at cursor key `0`, put
the resulting cursor authority into the `stateInterp` witness with a
singleton cursor map, and wrap the exclusive fragment in `allocCap`.
This is the missing allocation step in the current launch path.

Use that one helper in allocation-aware variants of:

- `spike_step_adequacy`;
- `wpt_engine_boundU/J`; and
- `wpt_strongly_normalizing`.

For incremental migration, the existing cursor-free launchers may remain
for no-allocation programs. After every current client is ported, prefer
one complete state interpretation/launcher and retire the vacuous empty
cursor mode. This follows RefinedC's useful invariant that `state_ctx`
always describes the complete machine state.

#### P1.4 Split the internal exact rule from the public rule

Rename the current theorem conceptually to `wps_create_cursor_internal`.
It may continue to mention exact `la`, `nid` and `freshBase`; only the
heap implementation module may use it.

The public rule should have the following logical shape:

```text
allocCap (req :: rest)
  * (forall p,
       p |->cell[ty] undefBytes
       * allocCap rest -* post(p))
|- wps(create(req), post)
```

The returned pointer is existential/continuation-bound. Its allocation
id and address must not occur in the precondition. The postcondition may
also provide persistent allocation metadata/bounds knowledge if that is
split from `pointsToCell` as described in P4.

Add a total analogue `wpt_create`. A bare create takes one relational
create step and produces a bare value whose delivery cost is one, so the
standalone rule should prove and document the exact cost bound (expected
minimum `2 <= k`; verify this against `driveU` rather than copying the
number from this plan).

Required local tests:

- success consumes the head request and returns `allocCap rest`;
- two creates consume a two-element plan in order;
- swapping requests is not silently allowed when alignment/size changes
  the concrete cursor evolution;
- an empty or insufficient plan cannot prove create;
- deleting the nonzero condition breaks the internal soundness proof;
- no public create theorem statement contains `AllocCursor`,
  `lastAddress`, `nextAllocId` or `freshBase`.

Definition of done: the only exact cursor theorem is internal, while
partial and total public allocation rules are launchable from real
Cerberus memory and expose only an existential pointer plus spatial
resources.

### P2 — Replace operational example prefixes with whole-program logic proofs

Affected files: `Exhibit.lean`, `ProdExhibit.lean`,
`ProdLoopExhibit.lean`, `StructExhibit.lean`, and possibly a new small
`AllocExhibit.lean`.

Perform the conversion in this order:

1. Turn `struct_create_store_wps` into a public-rule client whose
   precondition is `allocCap [structReq]`, not `cursorOwn`.
2. Add an adequacy theorem for that program. This closes the current gap
   between a local entailment and an engine-facing consumer.
3. Prove the complete create/store/load `progAProd` in `wpt`, including
   create, sequencing, store and load. Replace `prodA_pre` and
   `prodA_terminates` with one logical total theorem plus generic
   adequacy/driver collapse.
4. Prove the counter production program using a one-request plan and the
   existing logical loop suffix.
5. Prove list-reversal production using a two-request plan and the
   existing total list proof. The exact cold-start pointers may be
   recovered in the production boundary by evaluating the concrete plan;
   they must not parameterize the generic list logic.
6. Delete the positive-example `Step.sseq_*`, `Step.create`,
   `engineSteps_*` and chained `driverDone_step` proof bodies made
   redundant by these theorems.

The production route after this phase must be:

```text
program syntax
  -> wps/wpt derivation using public heap rules
  -> wps_sound/wpt_sound
  -> allocation-aware Iris adequacy
  -> generic measure/driver collapse
  -> runND production statement
```

No arrow may be supplied by an example-specific engine trace.

Definition of done: removing `wps_create` breaks the partial allocation
consumer; removing `wpt_create` breaks the complete create/store/load and
at least one allocating-loop production theorem.

### P3 — Make proof-flow and semantic coverage gates fail closed

#### P3.1 Dependency-certified consumers

Extend the existing Lean environment traversal used by `Audit.lean`.
For each manifest row, record distinct fields for:

- syntax constructor or evaluator case;
- relational rule;
- public logical rule;
- partial adequacy consumer;
- total adequacy consumer; and
- production consumer.

Check that each later declaration's transitive constant-dependency cone
contains the preceding public abstraction. In particular, the create
production consumer must contain `wpt_create` and the allocation-aware
launcher, not merely `Step.create`.

A raw transitive ban on `Step.*` will not work because sound logical
rules legitimately depend on the relation. Add a **layer-cut check**:
every path from a positive exhibit to an operational constructor must
cross an approved public rule/adequacy declaration. Also ban direct
references from positive exhibit declaration bodies to `Step.*`,
`engineSteps_*`, `driveJ_step` and `driverDone_step`.

Plant and retain these negative tests:

1. replace a logical create proof with a direct `Step.create` trace while
   keeping the theorem name—the gate must fail;
2. list a local `wps` theorem as an adequacy consumer—the gate must fail;
3. keep partial coverage but remove `wpt_create`—the total and full-row
   statuses must turn red;
4. add a new `Frag` constructor without a rule/consumer—the manifest
   generation must fail rather than silently grow a red or declared row.

#### P3.2 Two-sided relation coverage

Give the engine-facing one-round relation a name independent of examples,
for example `CerberusRound M`. Then prove, for every well-sized `Frag`
configuration, a theorem of this conceptual form:

```text
Step M c c' <-> CerberusRound M c c'
```

If a global iff is awkward because engine outcomes include refusal,
killed or nondeterministic branches, use an exhaustive sum
classification whose successful-next arm is exactly `Step` and whose
other arms are explicitly disjoint from `NotStuck`. One-sided
match-given-step lemmas may remain implementation lemmas, but not the
headline coverage claim.

Decide separately whether `CerberusRound` is:

- the graph of the discharged `step_ctx` engine round; or
- a relation bridged to `RelSem.Machine.Step`.

For the small demo, the first choice is acceptable and probably the
right granularity. If the future RefinedC variant will claim that
`RelSemCore` is its reference semantics, the bridge must be completed
before building semantic types. Do not let the type layer make this
choice implicitly.

Definition of done: the manifest derives its supported relation cases
from an exhaustive theorem, and a planted engine/mirror mismatch fails
the build.

### P4 — Finish the raw separation-logic API with RefinedC-compatible boundaries

This phase is not a request to port RefinedC's type system. It makes the
raw resources suitable for a later type interpretation.

#### P4.1 Separate three allocation facts

RefinedC usefully distinguishes byte ownership, persistent range metadata
and allocation liveness/freeability. Adopt the same separation of
concerns where it matches Cerberus:

1. **linear/fractional bytes:** the existing per-byte GenHeap;
2. **persistent allocation knowledge:** id, base, size/type, provenance
   and in-bounds facts, derived from immutable allocation metadata; and
3. **linear allocation capability/liveness:** only if and when kill/free
   enters the supported fragment.

Do not add a decorative liveness token before a `kill` rule and consumer
exist. For the current no-free fragment, document metadata immutability
and expose a persistent `allocMeta`/`locInBounds` view. Keep
`pointsToCell` and `pointsToView` as convenient derived bundles.

Required laws and consumers:

- byte-range split/join;
- typed-view split/join through the public theorems, not a duplicated
  `bytesOwn_append` proof in the client;
- fractional read preserving the fraction;
- full-ownership write;
- metadata/bounds agreement for two views of one allocation; and
- provenance-preserving pointer shift within bounds.

Use a struct client for view split/update/join and a read-only client for
a nontrivial fractional load. If no client exists, do not advertise the
feature.

#### P4.2 Add statement-level frame transformations

Define label-spec framing at both strata, for example:

```text
frameLs  R Ls  l args env = Ls l args env * R
frameLsT R Ls  l k args env = Ls l k args env * R
```

Prove:

- `blockSpecs_frame` and `blockSpecsT_frame`;
- `wps_frame_labels` and `wpt_frame_labels`; and
- derived whole-loop frame rules.

Then remove `RF` from the core definitions of the list/tree invariants
and obtain their public arbitrary-frame theorems by applying the generic
rule. This is the right precursor to future semantic types: a type
interpretation should compose by BI framing, not be threaded through
every label predicate by hand.

#### P4.3 Remove representation accidents

Port `LoopExhibit` from `IsXFrame` to `SymFrame`, and add an irrelevant
environment binding to its test configuration. Generalize `SemTriple`
over a well-formed `MachineCtx` and entry environment, or rename the
current theorem to make its fixed demo profile explicit.

Definition of done: the array, struct, list and tree clients import only
the public raw-logic API; none unfolds the ghost maps, `CohG`, cursor or
engine transition; and every nontrivial advertised rule has a compiling
consumer.

### P5 — Enforce module layering and add a RefinedC-readiness smoke test

Adopt and gate this dependency direction:

```text
Cerberus semantics / relational attachment
                 |
                 v
       Iris state + raw heap model
                 |
                 v
       expression and statement rules
                 |
                 v
        partial/total adequacy
                 |
                 v
        examples / production export
```

Specific actions:

1. Move `StmtProbe` to an archival/test target not imported by the main
   library.
2. Move `intTy`, 5/6/7 and canned exhibit proofs out of `Rules.lean` and
   `Wps.lean`.
3. Add an `API.lean` (or equivalent explicit export list) for future
   client/type-layer imports. It should expose pointer/location
   assertions, raw rules, statement judgments and adequacy—not `CohG`,
   cursor internals or engine unfolding helpers.
4. Add an import/dependency gate: semantic and heap modules may not
   depend on examples; rules may not depend on production; clients may
   not depend directly on internal attachment modules.
5. Add one **readiness smoke test**, not a proto-type-system: in a module
   importing only the public API, define a small semantic predicate of
   shape `PointerValue -> IProp` for a two-field object and derive its
   load/store/allocate rule solely from the raw API. This test must be a
   real consumer. Do not add a RefinedC-style `type` record, subtyping
   framework or automation until an actual next-layer client needs it.

Definition of done: the smoke test demonstrates that a future type
interpretation can sit above the raw logic without importing Cerberus
engine proofs or allocation cursor details.

### P6 — Rewrite the authoritative documentation

After P1 through P5, update the README, walkthrough, manifest and trust
story together. Draw one theorem-labelled diagram:

```text
Cerberus generated types + chosen relational transition
                         |
                         v
              iris-lean Language instance
                         |
      authoritative stateInterp / raw spatial resources
                         |
       base WP -> wps -> wpt / block specifications
                         |
             Iris partial + total adequacy
                         |
              generic driver collapse
                         |
        whole-program production statements

        future semantic types and automation sit here:
                    above raw rules,
             below generated client proofs
```

Every arrow must name its theorem, direction, fragment and axioms.
Document the difference between Cerberus allocation refusal and
RefinedC's `AllocFailed` divergence. Maintain a generated scope ledger
with separate statuses for local rule, launchability, partial consumer,
total consumer and production consumer.

Definition of done: a new reader can identify the semantic authority,
trusted components, no-OOM/failure policy, public client API and exact
scope without consulting dated archaeology notes.

### P7 — Retire the known production boundary seam

Retire `runEffectful` by the already planned upstream/pin change. Re-run
the exact-cone and banned-axiom sweeps and require production statements
to return to the classical trio. This remains important, but it should
not displace P1 through P3.

### Recommended merge sequence

Keep the work reviewable and prevent an operational workaround from
being mistaken for closure:

| Change | May contain | Must prove before merge |
|---|---|---|
| 1. Claims correction | Documentation and manifest status only | Current gates green; create visibly downgraded |
| 2. Allocation model | `AllocReq`, `PlanFits`, `allocCap`, `LaunchCoh` and pure lemmas | No example constants; plan success/failure unit proofs |
| 3. Launch plumbing | Shared `launchResources` and adequacy variants | Cursor key is nonempty; `CohG` non-vacuous; old no-alloc clients still green |
| 4. Logical rules | Internal exact create, public `wps_create`, `wpt_create` | Public statements cursor-free; partial and total local consumers |
| 5. Whole-program consumers | Struct, create/store/load, counter and list production rewrites | No direct operational proof terms in positive example declarations |
| 6. Oracle upgrade | Dependency stages, layer cuts and planted failures | Every bypass plant is detected |
| 7. Relation closure | `CerberusRound` and exhaustive/two-sided coverage | Every `Frag` row covered; mismatch plant fails |
| 8. Raw API closure | Persistent bounds/meta, frame transformations and real view/fraction clients | Public-API-only readiness smoke test |
| 9. Documentation closure | README, walkthrough, trust diagram and generated ledger | No stale-name/status searches; audit closure table complete |
| 10. Boundary retirement | Upstream `runEffectful` removal | Production theorem cones return to the classical trio |

Changes 2 through 5 form the allocation release blocker. Change 6 is
required before calling that blocker mechanically closed. Change 7 is
required before placing a RefinedC-style semantic type layer on top.

## Final acceptance checklist

The project should not declare the remediation complete until all of the
following are true:

- clean build against exact Cerberus Lean and iris-lean pins;
- no `sorry`, added axioms or unbounded production boundary dependencies;
- the allocation-failure/no-OOM policy is explicit and matches an actual
  Cerberus semantic outcome;
- the public allocation rule returns an existential pointer and has no
  client-visible Cerberus cursor arithmetic or token;
- allocator authority and an abstract capacity resource are initialized
  and preserved by every applicable adequacy launcher;
- partial and total allocation rules both have engine-facing consumers;
- complete allocating examples are logic proofs, not trace proofs;
- positive exhibits have no direct operational-semantic proof chains;
- loop framing is derived generically at both partial and total strata;
- every advertised split/fractional feature has a real consumer;
- capability rows validate dependency flow, not only declaration names;
- the chosen Cerberus relational presentation and its correspondence to
  the engine are explicit and proved at the claimed scope;
- the raw client API exposes bytes, bounds/metadata and allocation results
  without exposing `CohG`, cursor internals or engine unfolding;
- a public-API-only semantic-predicate smoke test demonstrates that a
  future RefinedC-style type interpretation can consume the raw logic;
- no unused proto-type-system or automation framework has been added;
- documentation contains no stale theorem names or contradictory seam
  status; and
- `runEffectful` remains isolated until it is retired.

Until the P2 exit criterion is met, the accurate one-sentence claim is:

> `cerberus-heaplang` contains a genuine Iris-backed separation logic and
> total statement logic for a certified, restricted Cerberus engine
> relation, with end-to-end seeded-heap examples; allocation and the
> allocating production demos are not yet connected through that logic.
