# Detailed audit of `cerberus-heaplang`

Date: 2026-09-02  
Audited revision: `d50e776175d89ca8bfddac2fa6b6f62ce7ad8cc9`  
Cerberus Lean pin: `ddcfc919972a31bc43a0454e6b2e76a19e6c4594`  
Iris Lean pin: `34390a0133986385c62bf59a6eb01938945b48ec`

This is a fresh audit of the current tree, not a restatement of the earlier
foundational and quality audits. It asks three questions:

1. Is this genuinely a Reynolds/O'Hearn-style separation logic, implemented
   with Iris, and correctly connected to Cerberus Lean?
2. Are there hidden, understated, or unacceptable trust gaps?
3. Is the documentation adequate to understand the design and trust story?

The review was deliberately suspicious of (a) operational proofs appearing
where reusable relational/logical rules should appear and (b) the logic being
specialized to accidental shapes of the demonstrations.

## Executive verdict

**The separation-logic part is genuine. The unqualified semantic-integration
claim is not yet earned.**

The project really does instantiate Iris with a relational `Language`, a
state interpretation, authoritative ghost state, spatial points-to resources,
fractional permissions, frame rules, partial and total weakest preconditions,
and adequacy. The heap rules are not example calculations disguised as rules:
they are generic in the machine context, environments, types, locations,
values, memory orders, and frames. The core logic does not import the example
modules. The examples exercise the public rules, and the readiness example is
good evidence that another representation predicate can be built above them.

The connection to Cerberus is also substantive. `Step` uses Cerberus's actual
generated Core types and memory operations, and `Soundness.lean` proves that a
mirror step has exactly the singleton successful outcome produced by one
discharged `step_ctx` round. The production theorems additionally reach the
shipped `drive`/`runND` entry. I found no admitted theorem, boundary axiom, or
example-specific constant on which a core rule depends.

However, Iris is instantiated over the package's hand-written `Step`, not over
Cerberus Lean's existing relational semantics. `CerberusRound` is the graph of
the executable round's **successful singleton result**, and the advertised
two-sided theorem assumes in advance that a mirror step exists. The
`refused` arm says only that the mirror is stuck; for most rows it proves no
fact about the engine. No theorem relates this presentation to
`RelSem.Machine.Step`, `runND_sound`, or `HarnessAdequate`. The current adequacy
theorems remain sound because Iris `NotStuck` supplies the missing mirror step
at every proved reachable state. What has been established is therefore:

> a sound Iris program logic for the package's restricted relational mirror,
> with a verified forward connection to successful Cerberus engine rounds on
> proved-safe executions.

It has **not** established:

> that its Iris language is Cerberus Lean's designated relational Core
> semantics, or a total characterization of that semantics on the declared
> fragment.

The README and `Round.lean` explicitly disclose this. It is not a concealed
kernel-trust hole. It is nevertheless a release-blocking architecture gap if
the intended claim is “a separation logic over the Cerberus relational
semantics,” rather than the narrower statement above.

### Scorecard

| Question | Verdict |
|---|---|
| Genuine Reynolds/O'Hearn spatial logic? | **Yes, for the modeled resources and fragment.** Real Iris BI resources, `∗`, fractions, framing, heap update rules, loops, and adequacy are present. |
| Correct use of Iris? | **Yes, with a conventional custom-language instantiation.** The reusable logic reasons over relational `primStep`; engine unfolding is mostly confined to the semantic and memory boundary. |
| Correct Cerberus connection? | **Sound but qualified.** Strong forward simulation for proved-safe fragment executions and a real production-driver endpoint; no bridge to the repository's existing relational spine and no full engine/mirror correspondence at stuck states. |
| Hidden proof-theoretic trust hole? | **None found in the current sources.** The classical trio is the documented axiom base. The in-build audit has one coverage overclaim described below. |
| Example specialization? | **No problematic dependency found in the core logic.** The fragment is intentionally example-sized, but no example constant is baked into the definitions or rules. A few example/test modules do cross the documented layer boundary. |
| Documentation adequate? | **Technically strong, operationally unwieldy.** It is unusually candid and detailed, but lacks a short authoritative design document and contains several contradictions about the public boundary and operational-proof discipline. |

## What was reviewed

I read the main definitions and proof boundaries in:

- `Step.lean`, `Lang.lean`, `Soundness.lean`, and `Round.lean`;
- `Heap.lean`, `Rules.lean`, `Wps.lean`, and `Wpt.lean`;
- `Adequacy.lean`, `TotalAdequacy.lean`, `DriverCollapse.lean`,
  `ProdLoop.lean`, and `ProdEntry.lean`;
- the public API and representative positive, negative, allocation, struct,
  list, tree, case, weak-sequencing, and production exhibits;
- `README.md`, `docs/WALKTHROUGH.md`, `docs/CAPABILITY_MANIFEST.md`, the
  current audit gate, and the two previous major audits;
- the pinned generated `CerbMem.allocateObject` and the pinned
  `relsemcore/RelSem/Machine.lean`, `RunND.lean`, and `Cerberus.lean`.

I also checked the package for `sorry`, `admit`, declared axioms, `unsafe`,
`native_decide`, `bv_decide`, and `ofReduce*`; checked the core-to-example
import direction; checked the dependency revisions; and compared the current
tree to the last recorded full green gate revision.

The current logic sources are unchanged since `cfdef37`, whose record in
`cerberus-heaplang/docs/2026-09-02_pr3-notes.md` reports the full gate green
with 116 exact export pins, 1,158 swept theorems, and 1,950 swept constants.
The commits between that revision and the audited revision change records and
deduplicate signature snapshots only.

I could not independently rerun the capped Lean builds in this session. The
repository's required cgroup wrapper was denied access to `/sys/fs/cgroup` by
the enclosing `nono` OS sandbox and its systemd fallback could not connect to
the user bus. I did not bypass the repository's memory cap: prior records make
clear that an uncapped build is unsafe. The banned-method scan and import
direction check did run. Accordingly, this audit relies on source inspection
plus the recorded green build for kernel-elaboration evidence, and says so
rather than presenting the old transcript as a new run.

## 1. Is it a real separation logic?

### 1.1 The Iris language is relational

`Lang.lean:47-50` instantiates Iris's `Language` with:

```lean
primStep := fun p _obs q =>
  Step p.1.M (p.1.e, p.1.ρ, p.2) (q.1.e, q.1.ρ, q.2.1) ∧
    q.1.M = p.1.M ∧ q.2.2 = []
```

This is not an evaluator masquerading as an Iris step. `Step` is an inductive
relation on Core expression/environment/memory configurations
(`Step.lean:1034-1035`). The lack of an Iris `Language.Context` instance is
also justified: Core's global `Erun` jump discards an `Esseq` context, so the
usual context-filling law would be false. The statement-level judgments prove
sequencing directly instead.

The fact that the project must prove facts about the executable semantics is
not itself an architectural mistake. A program logic needs an operational or
relational language model, and an adequacy theorem must eventually relate
logical steps to executions. The important separation is whether ordinary
client proofs unfold the interpreter. Here, most interpreter reasoning is in
`Soundness`, the memory seam in `Heap`, and the production-driver collapse;
ordinary heap reasoning uses `wps_*`/`wpt_*` rules.

### 1.2 The heap assertions are spatial, not pure encodings

The state interpretation uses three Iris `GenHeap`s: bytes, allocation
metadata, and the allocator cursor. A whole cell combines metadata and a
separating conjunction of per-byte resources. Typed subrange views share
metadata fractionally while owning disjoint byte ranges. The development
proves split/join, fractional, agreement, persistence, and bounds laws.

The concrete coupling is meaningful:

- `CellCoh` requires a live writable Cerberus allocation of the expected
  provenance id, base, size, and type; exact bytes in the real memory; and a
  decode result independent of the two unowned side tables.
- `Coh` requires every tracked cell to satisfy `CellCoh` and distinct tracked
  allocations to have disjoint ranges (`Heap.lean:344-347`).
- `CohG` connects the ghost maps to the actual `MemState` readout and pins the
  allocator fields when a cursor resource is present
  (`Heap.lean:1455-1473`).
- `storeM_success`, `loadM_success`, their view variants, and
  `allocateObject_success` unfold the real generated memory functions. The
  Iris rules update the authoritative state and the owned fragments together.

This is recognizably Reynolds/O'Hearn separation logic: ownership is local,
`∗` represents disjoint resources, reads admit fractional sharing, writes
require full ownership, and frame/consequence rules are semantic Iris laws.
It is not merely a predicate over a monolithic memory state with a theorem
named “frame.”

### 1.3 The rules are reusable logical rules

`Rules.lean` proves the five memory specifications once as an
`AtomicStep`. They are then lifted to raw Iris WP, partial `wps`, and total
`wpt`. `wps` is a guarded Iris fixpoint (`Wps.lean:116-171`); `wpt` is the
budget-indexed total analogue (`Wpt.lean:99-133`). Both have consequence,
frame, sequencing, conditionals, binding, jumps, and block-specification
rules. `wps_sound` and `wpt_sound` collapse them to Iris WP/TWP.

The allocation capacity is a deliberate nonstandard point. `allocCap reqs`
is exclusive ownership of a hidden deterministic cursor plus an ordered
request plan. It is not an additive capacity that can be split with `∗`.
That weakens modularity for programs that distribute allocation authority,
but it does not make the existing allocation rule unsound. The docs describe
this limitation accurately.

### 1.4 Adequacy is not vacuous

`MemTripleU` quantifies over every disjoint logical frame and every concrete
memory satisfying the union footprint. It forbids killed/stuck results at
every finite drive length and constrains every delivered result. The
allocation twin adds `LaunchCoh`. The projection theorem accepts an arbitrary
Iris postcondition and a pure readout obligation rather than hard-coding one
example postcondition.

The total lane separately connects a `wpt` budget to an exact engine drive
bound. Production exhibits use the generic allocation-aware total theorem and
the driver collapse to reach `CerbND.runND (_root_.drive ...)`. In particular,
the current flagship allocation example no longer proves termination with a
hand-written sequence of engine steps.

This is strong evidence that Iris is doing real work rather than decorating a
closed evaluation proof.

## 2. Findings

### H-1 — The logic is not yet tied to a designated Cerberus relational Core semantics

Severity: **High for the stated architecture; not a false-theorem finding.**

The semantic chain is:

```text
Iris WP/TWP
    over package Step
        -- forward certified on Frag when Step exists -->
CerberusRound = successful singleton graph of discharged step_ctx
        -- total production lane only -->
shipped drive/runND
```

The key facts are:

- Iris `primStep` is the package-authored `Step` (`Lang.lean:47-50`).
- `CerberusRound` is an equation saying `outcomesU = [.next ...]`
  (`Round.lean:86-89`). It models successful next rounds only.
- `Step.toCerberusRound` is a forward implication under `Frag` and the
  engine fuel bound (`Round.lean:96-105`).
- `step_iff_cerberusRound` is two-sided only after assuming
  `hstep : ∃ c', Step M c c'` (`Round.lean:107-129`). Its reverse direction
  obtains one mirror successor and uses equality of the singleton engine
  outputs. It is not an independent completeness proof for the mirror.
- `RoundClass.refused` contains `toVal = none` and absence of a mirror step,
  but no engine fact (`Round.lean:147-150`). The module explicitly says that
  most panic/nondeterministic refusal cases are not classified.
- No `CerberusHeapLang` source imports `RelSem`; `Round.lean:22-28` and
  `README.md:309-316` explicitly disclaim a bridge to
  `RelSem.Machine.Step`, `runND_sound`, and `HarnessAdequate`.

The `cerberusRound_classify` theorem should therefore not be read as an
engine-completeness result. Its non-value proof performs a classical case
split on whether `Step` exists. In the negative branch it reports only that
the mirror refused. The “exhaustiveness” is exhaustiveness of this four-way
*description of the mirror*, not a total relational classification of the
engine.

Why the current theorems are still sound: Iris WP at `NotStuck` establishes a
mirror value or mirror reducibility at every reachable state. In the latter
case a `Step` witness exists, and the strong singleton theorem applies. Engine
behaviors at mirror-stuck configurations cannot be reached by a proved-safe
logical execution. This is a legitimate fail-closed proof technique.

Why the gap still matters: the project cannot yet use “the Iris logic is over
Cerberus Lean's relational semantics” without qualification. It has selected
and certified its own successful-round relation. This risks semantic drift,
especially when adding concurrency, nondeterministic memory operations,
procedures, failures, or UB, where “successful singleton” is no longer the
right whole behavior.

The pinned `RelSem.Machine.Step` is itself described in its header as a
“spike-grade skeleton” and operates on reified driver `ndM` computations, not
directly on Core expression redexes. Therefore “replace `Step` with
`RelSem.Machine.Step`” is not a sufficiently considered fix. The project must
make an explicit semantic-authority decision:

1. If `RelSem` is authoritative, prove a commuting bridge from the Core-level
   transition used by Iris to an appropriate number of `RelSem.Machine.Step`
   steps, including terminal and killed outcomes and all enabled branches.
2. If a Core-round relation is authoritative, define and document that
   relation as a first-class relational semantics, including success,
   refusal/UB, and nondeterminism, then instantiate Iris over it or prove an
   unconditional correspondence theorem on a clearly stated admissible-state
   domain.
3. Keep the executable `step_ctx`/driver equivalence as a later refinement or
   adequacy layer. Do not use the existence of a logical `Step` as the premise
   of the only two-sided semantic-identification theorem.

Acceptance criterion: a reader should be able to point to one relation and
say both “this is the Cerberus Core semantics used by the logic” and “this
theorem connects it to the shipped runner,” without first assuming that the
hand-written mirror steps.

### M-1 — Allocation health is footprint-relative, not a global memory invariant

Severity: **Medium semantic-domain gap.**

The allocation-aware launcher is described as requiring an “allocator
healthy” memory. Its actual facts are narrower (`Adequacy.lean:437-451`):

- ids at or above `nextAllocId` are absent from the live and dead tables;
- every **tracked** cell id is below `nextAllocId`;
- every **tracked** cell address is at or above `lastAddress`;
- the requested plan fits the cursor.

Neither `Coh` nor `LaunchCoh` requires all live Cerberus allocations to be
pairwise range-disjoint or to lie above the downward allocation cursor. The
generated `allocateObject` computes a new address below `lastAddress`, inserts
the next id, and writes the bytes; it does not scan existing allocation ranges
for overlap (`generated/CerbMem.lean:1842` onward).

Consequently a malformed initial `MemState` can satisfy `LaunchCoh` for its
tracked footprint while containing an untracked, lower-address allocation
that overlaps the next planned range. The create rule remains locally sound
for every *owned* frame—any owned cell is tracked and protected by
`addr_lo`—but the new allocation need not be globally fresh from every
allocation represented by the concrete state.

This does not refute a theorem in the tree. Separation logic may intentionally
say nothing about unreachable, unowned storage, and the production cold-start
state is healthy. It does make two things unclear:

- whether arbitrary memories quantified by `MemTripleU_alloc` are intended to
  be reachable/well-formed Cerberus states; and
- whether “fresh allocation” means fresh from the logical footprint or fresh
  in the complete Cerberus allocation model.

For a reference-semantics logic, the cleaner design is a persistent global
`MemWF` component of the state interpretation/launch premise, proved for the
production initial state and preserved by every supported memory operation.
At minimum it should cover global allocation-id discipline, live/dead
consistency, range disjointness, byte-range consistency, and cursor bounds.
If footprint-relative freshness is intentional, rename the launch condition
and document that the general theorem permits concrete state outside the
logical footprint that is not globally well formed.

### M-2 — The documented public abstraction boundary is internally inconsistent

Severity: **Medium API/documentation issue; Low proof risk today.**

`API.lean` correctly admits that Lean imports do not hide internal names and
that the public/internal boundary is conventional (`API.lean:14-26`). But its
own table violates the convention:

- `allocCap_intro` is listed as a public assertion law (`API.lean:39`) while
  its theorem statement explicitly accepts internal `AllocCursor` and
  `cursorOwn` (`Heap.lean:2077-2080`). The adjacent prose says clients receive
  `allocCap` from launchers and “never build it.”
- `CellCoh` is listed below the line as internal (`API.lean:54`), but the
  advertised public `cellOwn_readout`, `cellOwn_consequence`, and
  `pointsToCell_consequence` expose `CellCoh` in their conclusions
  (`Adequacy.lean:1513-1524`, `1575-1580`).
- `project_triple_pure` exposes `CohG`, `metaInterp`, and `byteInterp` in its
  readout premise. The docs acknowledge this exception, but it means the
  headline projection is not a clean abstract façade even though its
  conclusion is Iris-free.

This is not merely cosmetic for future clients: it leaves no stable rule for
which implementation predicates a representation layer may mention. The
readiness smoke test is disciplined, but the table is the only enforcement.

Fix the classification rather than the proofs first. Mark `allocCap_intro` as
launcher/internal. Either make `CellCoh` and a deliberately small pure memory
view public, or wrap it in public readout records whose fields are the facts a
client needs. A stronger façade could live in a namespace/module whose
statements do not mention ghost carriers, even though Lean will still make the
underlying imports discoverable.

### L-1 — The in-build audit overstates its coverage of internal constants

Severity: **Low for current exports; Medium if the audit text is treated as a
whole-package trust guarantee.**

`Audit.lean` provides valuable checks:

- 116 named exports must depend on exactly `propext`, `Classical.choice`, and
  `Quot.sound`;
- ordinary theorems originating in `CerberusHeapLang.*` may use no other
  axiom; and
- ordinary constants are scanned for `sorryAx` and the two `ofReduce*`
  axioms.

But both exhaustive loops explicitly skip `n.isInternalDetail`
(`Audit.lean:216`, `233`). The emitted text nevertheless says “every theorem,”
“every constant kind,” and “absent from all cones.” A private/internal-detail
constant unused by a pinned export is outside the scan. If it is used by a
pinned export, the export's transitive axiom collection should still catch it,
so the headline exports remain protected. The overclaim concerns package-wide
cleanliness and unpinned/dead declarations.

I found no actual `sorry`, `admit`, declared axiom, or banned reduction method
in the current sources. This is a gate-specification defect, not evidence of a
present proof hole.

Fix: do not skip internal details in the banned-axiom pass, or change every
claim to state the exact scope. Add a planted `private theorem ... := by
sorry` regression to establish the intended behavior. The exact export list
is manual by design; documentation should continue to distinguish it from a
semantic-coverage proof.

### L-2 — Some exhibit modules still reason directly with the internal relation

Severity: **Low, but directly relevant to the requested layering discipline.**

The main production proofs now go through `wpt_create`, the generic memory
rules, allocation adequacy, and driver collapse. That is the right shape.
There are nevertheless direct `Step` proofs in client/exhibit modules:

- `ProdExhibit.lean:35-36` says there is no `Step.*` in any proof of the
  module, but `store_sym_lit_step` and `store_lit_sym_step` are proved by
  `Step.store_eval` at lines 100-118.
- `DivergeExhibit.lean:79-85` proves the self-step by `Step.run` for the
  operational negative regression.

The first pair are coverage witnesses and the second supports a negative
test; none is the logical proof of a positive production correctness theorem.
Thus this is not example-specific unsoundness. It does blur the stated rule
that a client reasoning through `Step` bypasses the logic, and it makes the
module-level claim false.

Move mirror/engine coverage witnesses to a semantic regression module that is
not presented as a client. Keep positive exhibit modules importing the public
API and proving properties through public rules. If direct operational lemmas
are intentionally allowed in negative tests, state that narrow exception.

### L-3 — Documentation is candid but too diffuse to serve as an architecture spec

Severity: **Low documentation-quality issue.**

The documentation's technical honesty is a major strength. It explicitly
records:

- the `RelSem` non-bridge;
- annotation-free authored Core rather than frontend-produced Core;
- static engine fuel bounds and the separate `peDepth` restriction;
- unsupported free/procedures/concurrency and other Core constructs;
- opaque engine constants and differential testing as a trust boundary;
- nonadditive allocation capacity, absent read-only cells, and the carried
  `Ecase` size premise;
- the distinction between package `driveU` statements and shipped-driver
  production statements.

That is enough for a determined expert to reconstruct the design. It is not a
good entry path. The repository root README is one line; the package README is
553 lines; the walkthrough is 983 lines; and the audit/history directory has
many chronological records and large signature snapshots. Architectural
truth is repeated across headers, README tables, the walkthrough, decision
records, and audits. The API contradictions and the false `ProdExhibit`
layering statement show the predictable result: local prose drifts even while
the overall story remains unusually thorough.

Add one short, normative `ARCHITECTURE.md` with:

1. the exact theorem claim in one paragraph;
2. one diagram distinguishing `Step`, `CerberusRound`, `RelSem`, `driveU`, and
   shipped `drive/runND`;
3. a table of trusted components, checked components, assumptions, and scope
   exclusions;
4. the public client surface and the definition of “internal”;
5. a “not proved” list; and
6. links to the README/walkthrough/history for details.

Make that document the source of truth and point the root README to it.

## 3. Trust analysis

### 3.1 Kernel and axiom trust

On the available evidence, the proof-theoretic story is good. The named
exports are recorded as having exactly the standard classical trio
`propext`, `Classical.choice`, and `Quot.sound`. No project boundary axiom is
declared. Iris Lean contributes definitions and kernel-checked theorems rather
than a new axiom. The semantics dependency and Lem runtime are likewise
reported axiom-free.

The trio is not the interesting trust risk here. The important risks are
semantic identity and statement interpretation: whether the generated Lean
engine is the intended Cerberus semantics, whether the chosen fragment is the
claimed one, and whether the readout predicates express the intended heap
facts.

### 3.2 Generated semantics versus Cerberus

The Lean port and OCaml Cerberus are generated from the same Lem source and
differentially tested. That is strong engineering evidence, not a formal
equivalence theorem. The README says this plainly and lists the validation
corpora. Treating the generated Lean semantics as the reference artifact is a
reasonable project trust decision, provided it is explicit.

If the intended claim instead reaches the Cerberus specification independent
of this generated artifact, the proof is incomplete: generation correctness
and Lean/OCaml semantic equivalence remain external trust assumptions.

### 3.3 Opaque constants

The documented opaque constants do not act like Lean axioms: proofs cannot
unfold them, so a theorem involving them must be parametric in their value or
avoid the relevant branch. This is generally handled conservatively. It also
explains why full refusal classification is not currently available.

The correct conclusion is not “opaques are harmless,” but “the exported
theorems are kernel-valid for every interpretation of the opaques; the claim
that an `@[implemented_by]` runtime implementation has the expected meaning
is part of the executable-artifact trust boundary.” The current docs mostly
make this distinction.

### 3.4 Scope restrictions are not hidden trust gaps

The following are important limitations but are properly visible in theorem
premises or documentation:

- the 18-constructor, annotation-free `Frag` rather than full Core;
- cons-shaped environments and `MachineCtx.SeqWF`;
- no procedures, free, concurrency, general `Eunseq`, or general memops;
- a hand-written partial pure-expression evaluator on `PePure` plus static
  depth bounds;
- authored Core inside a synthetic file, not frontend output;
- empty tag definitions in the demonstrations;
- writable non-atomic cells and explicit decode/storability premises;
- the carried `Frag.case_value` size condition; and
- ordered, exclusive allocation plans.

These restrictions mean “demo logic over a Core fragment,” not “C separation
logic.” They become trust problems only if omitted from headline claims.

## 4. Is the logic accidentally specialized to the examples?

I found no structural example-to-logic dependency.

- The checked import direction prevents `Step`, heap, rule, and adequacy
  modules from importing an exhibit, production exhibit, or example module.
- The generic rules quantify over types, values, environments, locations,
  machine contexts, and frames. Core definitions do not depend on `intTy`,
  `sevenVal`, concrete program symbols, list/tree layouts, or seeded example
  heaps.
- `Examples/ReadinessSmoke.lean` imports only `CerberusHeapLang.API`, defines a
  fresh two-field representation predicate, and derives field load/store and
  allocation rules. This is the best current anti-specialization test.
- List reversal and tree rotation use recursive representation predicates and
  arbitrary disjoint frames, rather than closed concrete memories only.
- Production allocation binds the pointer produced by `create`; it no longer
  assumes a precomputed address or allocation id.

There are still two qualifications.

First, `Frag` is plainly feature-selected: its 18 constructors correspond to
the constructs needed by the demonstration suite, and the capability manifest
requires an exhibit consumer for every row. That is acceptable for a demo,
but “every row has an example” is not evidence that the fragment is a natural
semantic boundary. The boundary should be justified by semantic closure and
rule design, not only coverage demand.

Second, some restrictions are easy for authored examples to satisfy but hard
for frontend output: empty node annotations, empty tag maps, `PePure`, static
depth proofs, and the `Ecase` branch-size premise. The documentation admits
this. These should remain explicit fragment predicates and should not migrate
into generic heap assertions or rule conclusions.

The recommended regression test is not another fixed example. It is a small
parametric client module, like `ReadinessSmoke`, that:

- defines a new representation predicate without importing example layout;
- uses arbitrary tag definitions and a nonempty environment;
- frames an unrelated allocation through a loop and an allocation;
- mentions no `Step`, `CohG`, cursor representation, or concrete address;
- projects to an engine-facing theorem.

## 5. Recommended disposition

### Required before an unqualified “over Cerberus relational semantics” claim

1. Resolve H-1: designate the relational semantic authority and prove the
   bridge without assuming a mirror step exists. Cover terminal, refusal/UB,
   and nondeterministic outcomes on the stated admissible domain.
2. Decide the concrete-state domain for allocation. Add and preserve a global
   memory well-formedness invariant, or explicitly limit freshness and the
   general allocation theorem to the tracked logical footprint.
3. Publish a short normative architecture/trust document using the qualified
   theorem claim from this audit.

### Should fix for a clean demo API

4. Repair the `API.lean` public/internal classifications, especially
   `allocCap_intro` and `CellCoh`.
5. Move direct `Step` regression lemmas out of positive client modules and
   correct the false `ProdExhibit` header statement.
6. Make the audit's internal-detail exclusion honest or remove it, with a
   planted private-`sorry` test.

### Reasonable to retain as explicit demo limitations

7. The annotation-free restricted fragment, absent dispose/procedures, ordered
   allocation plan, static fuel premises, and handwritten pure evaluator can
   remain. They are engineering scope choices, not foundational defects, so
   long as the claim continues to say “fragment” and the frontend gap remains
   prominent.

## Bottom line

This is substantially better than a toy heap encoding. It contains a real
Iris separation logic, sound generic rules over the actual Cerberus memory
operations, nontrivial control-flow reasoning, semantic projection, and real
production-driver examples. The examples do not determine the core logic.

The remaining central issue is semantic authority. The development proves a
sound connection from its own relational mirror to successful executable
engine rounds on logically safe executions. That is a respectable and useful
result. It should not yet be advertised as an unqualified Iris logic over the
Cerberus relational Core semantics until the missing relational bridge and
behavior-completeness story are resolved.
