# cerberus-heaplang

A demonstration separation logic for the Cerberus Core engine — the
HeapLang-analog of the cerberus-lean semantics. **Cerberus** is an
executable semantics for C: it elaborates C into a typed functional
intermediate language, **Core**, and runs Core on an interpreter
with a byte-level, provenance-aware memory object model
(**provenance**: the memory model's record of which allocation a
pointer derives from, policing arithmetic and comparisons as the C
standard does). The engine here is the Lean 4 port of that
semantics, differentially validated against the original OCaml
implementation and pinned by commit in
`../scripts/semantics-pin.env` (what that validation covers, and
the in-package path to its record: "What you are asked to take on
faith", below). This package builds a small Iris
program logic — points-to, store/load small axioms, frame,
sequencing, consequence, loop rules — over a fragment of Core, and
certifies every rule against that engine, so that the exported
theorems are statements in engine vocabulary alone.

**New reader? Start with the
[walkthrough](docs/WALKTHROUGH.md)** — what a Core program looks
like, what a triple means here, the trust story, and how to check
the claims yourself in five minutes.

The analogy to Iris HeapLang is in the ROLE (the demonstration
language a logic is exercised on), not the extent: unlike HeapLang
this package has no concurrency, no prophecy variables, and a small
lemma suite rather than HeapLang's full library (allocation IS in
the logic: `wps_create` through the allocator-cursor resource —
Phase 2). What it has instead is an object language
that is the intermediate language of a real C semantics, executed
by the real interpreter.

**What this is NOT**: the RefinedC port. That development — the
Lean-native RefinedC-architecture verifier — lives alongside, in
this repository's root `RefinedCerberus` package, and is the actual
product; this package is a self-contained demonstration that the
attachment pattern (mirror step relation → Iris logic → per-rule
engine certification → production-entry export) works end-to-end.

## The claim, and the exhibits that back it

The claim: this is a separation logic in the Reynolds/O'Hearn
tradition — small axioms, the frame rule, representation predicates
by structural recursion, loop invariants of the textbook shape —
whose theorems are about the execution of a real C semantics'
engine, ending at the tradition's canonical exhibit, in-place
linked-list reversal.

**The authoritative scope statement is the generated
[capability manifest](docs/CAPABILITY_MANIFEST.md)** — one row per
supported Core construct (mirror rule / logic rule / fragment cone
/ engine match / adequacy, total, and production lanes / example
consumer), regenerated and drift-checked by `scripts/test_unit.sh`
gate 4. Since Phase-1 S1c its row set is DERIVED from the unified
fragment cone: the generator enumerates the cone's constructors out
of the built environment and requires every mirror-relation
constructor to be claimed by exactly one row, so the mirror, the
cone, and this claims surface cannot diverge without a failed
check. Every scope claim in this README is read under it: a
construct is claimed at exactly its manifest level, no more.

The exhibits, in pedagogical order (column
legend, for first read — each term gets its full treatment below:
**Lane** = which execution function the theorem is stated against,
`drive`/`driveJ` being the engine's driver loop projected into the
package and `production` the shipped pipeline itself, defined in
the paragraph after the table; **trio** = the classical axioms
`propext`, `Classical.choice`, `Quot.sound`; **in-budget fuel** =
a hypothesis that the step count fits the engine's own interpreter
budget, `lemDefaultFuel = 10^6`; **interior** = appears in proofs
only, never in exported conclusions — the trust story below):

| Theorem (file) | Claim | Hypotheses | Lane | Axiom cone |
|---|---|---|---|---|
| `wp_store`, `wp_load` (Rules.lean) | The small axioms: cell ownership entails the store/load WP, every undefined-behavior arm excluded by the precondition | typing side conditions (`rfl` at concrete instances) | derived logic (interior; meaning lands via the exports below) | trio |
| `exhibitA_semantic` / `exhibitA_engine` (Exhibit.lean) | `lets _ = store(x,7) in load(x)` on the engine cannot kill; any delivered value is `Specified(7)` | in-budget fuel; seeded cell | drive | trio |
| `exhibitB_semantic` / `exhibitB_engine` (Exhibit.lean) | THE FRAME: `⦃x ↦ - ∗ y ↦ a⦄ store(x,7) ⦃x ↦ 7 ∗ y ↦ a⦄` over engine configurations — y and all unnamed rest verbatim | in-budget fuel; seeded cells | drive | trio |
| `exhibitC_semantic` / `exhibitC_engine` (Exhibit.lean) | Sequenced stores to disjoint cells both land, non-conflictingly — locality read back from the engine's bytemap | in-budget fuel; seeded cells | drive | trio |
| `counter_loop_certified` (LoopExhibit.lean) | THE FIRST LOOP: save entry, real `x > 0` guard, store under the loop, context-discarding back edge — never kills, final bytes pinned by a data-dependent post | in-budget fuel; seeded cell | driveJ | trio |
| `fib_certified`, `fib_certified_total` (FibExhibit.lean) | Iterative fib with invariant `a = fib i ∧ b = fib (i+1)` delivers `fib n`; `fib_certified_total` is a separate OPERATIONAL ENGINE THEOREM — an unconditional equation, at step bound `2·n + 4`, `driveJ … = .done (fib n)`, no fuel hypotheses at all — proved by direct induction on the drive, NOT by the logic (no total WP exists yet; manifest Notes 2) | partial form: in-budget fuel; engine theorem: NONE | driveJ | trio |
| `array_sum_certified` (ArrayExhibit.lean) | The array walk: real pointer arithmetic, interior loads of a seeded one-allocation array — delivers `vs.sum` with the array preserved | in-budget fuel; seeded array (coherence, per-element decode, size/location) | driveJ | trio |
| `list_reverse_certified`, `list_reverse_demo` (ListRevExhibit.lean) | THE CANONICAL EXHIBIT: in-place reversal of a linked list of two-field nodes — any delivered value is a pointer whose final-heap chain is `xs.reverse`; the demo instantiates a 3-node `[1,2,3]` chain, every decode fact `rfl` | in-budget fuel; seeded chain (`SeedChain`, `Coh`) | driveJ | trio |
| `exhibitA_prod` (ProdExhibit.lean) | The production run of a self-contained create/store/load program IS the singleton Active execution delivering 7 with the exact final bytes | file-system state and argv only — everything else discharged | production | trio + `runEffectful` |
| `counter_loop_certified_production` (ProdEntry.lean) | THE REGISTRATION THEOREM (that is what it is, despite the declaration's name — naming debt, manifest Notes 3): the counter loop re-exported with the label plumbing DERIVED from the shipped label-collection — nothing hand-built; NOT a production `runND` equation | as `counter_loop_certified` | driveJ @ production run state | trio + `runEffectful` |

Two lanes appear above, and the difference is part of every claim.
The **drive lanes** (`drive`, and `driveJ` for programs with jumps)
state theorems against the engine's own
`{step_ctx → sequential discharge}` loop, projected to
(thread state, memory state) — the projection is a package
definition, small and cited line-by-line against the engine's
driver. The **production lane** states theorems against the shipped
pipeline itself — `CerbND.runND (Driver.drive …)` from
`initial_driver_state`, the composite the cerberus-lean executable
runs — with no package-defined execution function in the statement
at all. Straight-line programs are exported all the way to the
production lane; loop programs currently stop at the drive lane
plus a proved registration tie (see "Scope of the claims"). Every
drive-lane statement also quantifies over `aids : Nat → Nat`, the
action-id supply: the oracle for the driver's fresh action-id
draws, ∀-quantified so the theorems hold for every supply — on
this deterministic fragment the choice is irrelevant.

The proof of the flagship is textbook-compositional and that is the
point of the exhibit: representation predicate `isList` by plain
structural recursion (no step-indexing), loop invariant
`isList prev reversed ∗ isList cur rest` with
`xs = reversed.reverse ++ rest`, every construct discharged by its
small axiom or rule, no monolithic unfolding anywhere.

## The trust story

The only trusted semantics is the cerberus-lean operational
semantics (the Lean port of Cerberus Core, pinned by commit in
`../scripts/semantics-pin.env` and differentially validated
upstream against the OCaml oracle); everything in this package is
derived and proved down into that engine. Every theorem is
kernel-checked with its transitive axiom cone BOUNDED in-build, and
the headline theorems' cones EXACTLY PINNED
(`CerberusHeapLang/Audit.lean`, the last import of the library
root — the exhaustive sweep is an upper-bound check, the curated
pins are equality checks; "exhaustively bounded, headline cones
exactly pinned" is the precise claim): every cone is within the
classical trio (`propext`, `Classical.choice`, `Quot.sound`),
except in the two production-entry modules (`ProdEntry`,
`ProdExhibit`) whose
statements mention the shipped initial driver state and are
therefore additionally allowed the semantics repo's one residual
axiom
`runEffectful` — a declared TEMPORAL boundary (an effectful
initialization seam), entering through the statements only, whose
upstream retirement is planned (after which this boundary vanishes
at a pin bump with no restatement here). Non-kernel proof methods
(`native_decide`, `bv_decide`, `ofReduce*`) are banned by a grep
gate and would in any case enter a cone and fail the audit — a
build that weakens any of this fails.

The package's own step relation (`Step`) and the Iris layer are
INTERIOR: they appear in proofs, never in exported conclusions, and
are certified per-rule against the engine (`Soundness.lean`). A
wrong mirror can therefore only make theorems unprovable, never
false — with the caveat that keeps the slogan honest (2026-08-31
audit, F-09): the guarantee holds only relative to a FAITHFUL
specification idiom. A wrong statement-level definition
(`drive`/`driveJ`, `dischargeStep`, a readout predicate) yields a
true-but-irrelevant theorem rather than a false one, and a missing
mirror/cone case silently narrows coverage without falsifying
anything — which is why the specification idiom is read (below)
and coverage is gated by the
[capability manifest](docs/CAPABILITY_MANIFEST.md) rather than
trusted to prose (and the manifest's row set is itself derived from
the cone's constructors in the built environment — a mirror or cone
case added or deleted without a manifest row fails gate 4, so the
coverage channel closes by a failed check, not by vigilance). What remains statement-level trust — the specification
idiom: the drive-loop projections and the footprint/readout
predicates the exported statements are phrased in — is kept small,
pinned by executable concrete instances (the demos), and laid out
for reading, identifier by identifier and with a mechanical
statement-surface census, in the
[walkthrough](docs/WALKTHROUGH.md) §5 (the trust tiers are its §4).

### What you are asked to take on faith

Self-contained, because these are the only two places where the
trust story bottoms out outside this package.

**1. The one axiom, verbatim.** The full statement of
`runEffectful`, from the vendored lem runtime the engine builds on
(`.lake/packages/LemLib/lean-lib/LemLib.lean:54` in this package's
checkout):

```lean
axiom runEffectful {α : Type} : (Unit → BaseIO α) → α
```

It is the semantics port's effect-erasure seam: generated code
uses it to read ambient state that the original OCaml reads
effectfully. It enters this package through the STATEMENTS of the
two production-entry modules only — the shipped
`initial_driver_state` draws its symbol supply through
`runEffectful (CerberusFresh.freshIntIO ())`, and the certified
fragment provably never reads that field, so the theorems hold for
every value the seam could produce. It is declared TEMPORAL:
upstream retirement is designed and in flight on the semantics/lem
side, after which this boundary vanishes here at a pin bump with
no restatement (the `Audit.lean` header carries the full
provenance).

**2. What "differentially validated" covers.** The Lean port and
the OCaml Cerberus — both generated from the same Lem model — are
run on the same programs and their full verdict lines compared
(defined values, exact undefined-behaviour codes, errors) against
pinned fail-closed baselines, with an un-forked upstream checkout
as a third comparison point; among the recorded lanes: the
106-program upstream minimal suite (106/106), a 213-test CN corpus
(213/213 exact match), a 16-URI multi-TU libxml2 corpus (16/16
byte-identical against the oracle), 1,669 csmith programs at a
classified pinned baseline, ~2,000 recorded harness-family
differential executions, and a 2,186-file upstream CI sweep with
zero mismatches among its 1,316 comparable files. This samples
behaviour — it is not an equivalence proof — and the OCaml oracle
itself remains on the trust boundary. The record is in this
package's reach: the pinned semantics workspace
(`../scripts/setup-cerberus-dep.sh`) carries it at
`../.cerberus-ws/lean_frontend/VALIDATION.md`, and that file, not
the pin file, is the authority on what is compared, how often, and
what it does and does not establish. It is the engine's own trust
story, imported: this package's theorems discharge INTO that
engine and neither add to nor draw on its evidence.

**A disambiguation on that path — two presentations, one engine.**
The pinned semantics workspace also carries the semantics repo's
OWN small derived relational spine (`relsemcore`: a `RelSem`
machine `Step` relation, the `runND_sound` runner-soundness
theorem, and the `HarnessAdequate` harness statement). That spine
is the SEMANTICS REPO'S validation instrument for its own
driver/harness — it is NOT part of this package's chain: this
package neither imports nor builds on it, and NO bridging theorem
between the two presentations exists or is claimed. This package's
chain into the engine is exactly the one described in the trust
story above — the interior mirror `Step`, certified per-rule
against the engine's own `step_ctx`/discharge functions
(`Soundness.lean`), landing through the adequacy theorems in the
drive and production lanes. A bridge between the two presentations
is recorded as OUT of scope for this phase (foundations arc plan,
Phase 1 item 6).

## Scope of the claims

THE LOOP CLAIMS. `counter_loop_certified` (LoopExhibit.lean),
`fib_certified` (FibExhibit.lean), `array_sum_certified`
(ArrayExhibit.lean) and `list_reverse_certified`
(ListRevExhibit.lean) certify authored Core LOOPS — save entry,
big-step guards, context-discarding back edges, and (array-sum)
interior loads with real pointer arithmetic — against the engine's
own `{step_ctx → sequential discharge}` loop (`driveJ`,
Adequacy.lean) at a proc-carrying thread whose label map is tied to
`core_run_state.labeled`: the engine never kills, never derails,
and a delivered value satisfies the data-dependent postcondition
(`fib n` from the Lean-side `fibSpec`; `vs.sum` with the array
preserved). These are PARTIAL-correctness statements with in-budget
fuel hypotheses — and, for `array_sum_certified`, stated pre-state
hypotheses: the coherence-seeded one-allocation array (`hcoh`),
per-element decode premises (`hdec`, rfl-dischargeable at concrete
engine-serialized bytes), and size/location side conditions
(`hsz`/`hlib`); `list_reverse_certified` is stated over a SEEDED
INPUT CHAIN (`SeedChain` — one disjoint one-allocation node cell
per element, engine-serialized field images, per-node
machine-address WF `0 < a < 2^64`) and concludes that any delivered
value is a POINTER whose FINAL-heap chain is `xs.reverse`
(`ChainAt` — per-node `CellCoh` + field decode facts about the
final `MemState`; the concrete `list_reverse_demo` instantiates a
3-node [1,2,3] chain with every decode fact discharged by `rfl`) —
except `fib_certified_total`, which is UNCONDITIONAL — at the
concrete step bound `2·n + 4`, `driveJ` DELIVERS `fib n`, with no
fuel hypotheses at all — and which is an OPERATIONAL ENGINE
THEOREM, not a logic result (2026-08-31 audit, F-02): it is proved
by direct induction on the drive (explicit `Step`/`driveJ_step`
rewrites), consuming neither `fib_wps` nor the variant loop rule
nor any total WP; the logic itself has no total-correctness lane
yet (Phase 3; manifest Notes 2). Scope honesty for all of them: the
drive lane is the sequential driver's loop projected to
(thread_state, MemState) with the run state a constant parameter
(certified faithful for this fragment — the real driver
additionally ticks `aid_supply`, which the fragment ignores); the
PRODUCTION-pipeline export of a loop run (the `runND` equation) is
NOT yet established — the production tie delivered so far is the
REGISTRATION equation (`fib_labeledAt_production` /
`loop_labeledAt_production`, ProdEntry.lean): the exhibits' label
maps are exactly what the shipped
`collect_labeled_continuations_NEW ∘ initial_core_run_state`
computes, so `LabeledAt` at the production initial run state is
derived, not hypothesized, and `counter_loop_certified_production`
re-exports the counter loop with NOTHING hand-built in the label
plumbing.

The flagship straight-line demonstration is unconditional:
`exhibitA_prod` (ProdExhibit.lean) quantifies over nothing but the
file-system state `fs` and the argument list `args` — every other
hypothesis is discharged concretely — and concludes that the
production run of its create/store/load program IS the singleton
Active execution delivering 7 with the exact final bytes.

The GENERAL production-entry theorems are conditioned, and the
conditions are part of the claim. `sem_triple_prod` and
`prod_run_eq` (ProdEntry.lean) conclude their `runND` equation only
under: `hterm`, a proved in-budget-termination hypothesis for the
compute part (∀ aids, the drive completes to `.done v σfin` in k
steps); `hpre`, a proved setup-prefix alignment equation (the
program's prefix drives the production cold-start memory to the
footprint-satisfying configuration); and the fuel side conditions
`hfuel`/`hfuelc` (`esize … ≤ lemDefaultFuel = 10^6`, the engine's
own budget). `SemTriple` itself (Adequacy.lean) is PARTIAL
correctness — fuel exhaustion (`.more`) is unconstrained — under
the same fuel cap, and its conclusion constrains only the P ⊎ R
split it quantifies (untracked cells outside it are not claimed
preserved by the general statements; the production equation does
pin the full final `layout_state`). Everything is single-threaded,
over the certified fragment only — authoritatively, the
adequacy-exportable rows of the
[capability manifest](docs/CAPABILITY_MANIFEST.md); in prose:
`store`/`load`/`create`, strong
sequencing `Esseq` at wildcard, `Specified`-binder and
plain-symbol-binder patterns, weak sequencing `Ewseq` at wildcard
(the S1b drift-test construct), `Esave`/`Eif`/`Erun`,
value-scrutinee `Ecase` (S1b export — audit F-01 discharged),
`PEsym`-shaped pure exits, the `Load0` AND `Store0`
operand-evaluation steps, the `PtrEq` memop with its
operand-evaluation step, `PEval`/`PEsym`/integer-`PEop`/
`PEarray_shift` operands, plus the run-time annotation residue.
<!-- MANIFEST-SCOPE-BEGIN
tokens: value store load create sseq-wild sseq-spec sseq-sym wseq-wild annot save if run case-value pure-sym memop-ptreq memop-op load-op store-op pure-operands
MANIFEST-SCOPE-END -->
Each qualifier is registered
at source (module headers; `docs/2026-08-30_spike-report.md`); this
section, under the manifest, is the summary the claims above are
read under.

## Registered divergences and seams

Acceptable qualifiers are clear, known divergences with retirement
or growth paths. The register (each entry's home is authoritative):

| Divergence / seam | Discharge / path | Registered at |
|---|---|---|
| `runEffectful` in the production-entry statement cones | Temporal boundary (statement printed verbatim in "What you are asked to take on faith", above); upstream retirement planned — vanishes at a pin bump, no restatement | `Audit.lean` header |
| tagDefs argument: the theorems pin `drive`'s tagDefs to `fmapEmpty`; the shipped `Main.lean:871` passes `CerbTags.tagDefs ()` after `setTagDefsIO` | Semantically forced equal for the synthetic file: `(prodFile e).tagDefs = fmapEmpty` by `rfl`; the effectful set-then-read global is inert here (scalar layout paths provably never read it; struct/union paths would) | This table + `docs/2026-08-30_spike-report.md` register |
| Memory orders accepted arbitrarily: `Step.store`/`wp_store` hold at ANY `memory_order` | Mirror-true: the sequential driver drops `mo` (`action_request_sequential2`, Driver.lean:273 — `mo1` unused); NA-only side conditions would be a divergence FROM the engine | This table + `docs/2026-08-30_spike-report.md` register |
| Whole-allocation byte-list cells (no per-byte split) | Registered growth step for structs | `Heap.lean` header; `docs/2026-08-30_spike-report.md` R2 |
| `Ewseq` at spec/sym binder patterns outside the fragment (the WILDCARD lane exported in S1b as the drift test); `Ecase`'s EVAL arm (non-value scrutinees) unmirrored | Mechanical per-construct extension, path named | `Step.lean` header; `docs/2026-08-30_spike-report.md` "Honestly open" |
| `counter_loop_certified_production` is the REGISTRATION theorem, not a production `runND` equation — the declaration name overstates its lane (2026-08-31 audit F-05) | Naming debt registered; docs call it the registration theorem; rename lands with Phase 5's real production theorem (a rename now is statement-surface churn) | Manifest Notes 3; `ProdEntry.lean` |
| PURE exits certified at `PEsym` shape only (general `PePure` exits are a bounded matcher extension) | Extend `stepDischarge_pure_sym` per-constructor when needed | `Soundness.lean`; `docs/2026-08-31_phase2-s4-notes.md` |
| The array exhibit's pre-state is ONE allocation (not a ∗-of-per-element-cells): the engine's loads bounds-check against the pointer's PROVENANCE allocation and `arrayShiftPtrval` preserves provenance, so distinct-allocation "arrays" are not walkable in the engine — C's object model | Forcing fact about Cerberus, recorded; per-element structure lives in the index-partitioned invariant + decode premises | `ArrayExhibit.lean` header; `docs/2026-08-31_phase2-s4-notes.md` |
| The pointer-test memop coverage is `PtrEq` only; the family (PtrNe/Lt/…) and eqPtrval's differing-provenance ND fork are fail-closed ABSENCES of a mirror step (the fork is a real `msum`, CerbMem.lean:1753 — enumerated by the exhaustive runners, not single-layer) | Mechanical per-memop extension (dischargeStep arm + Step rule + wps axiom) | `Soundness.lean` dischargeStep memop arm; `docs/2026-08-31_listrev-notes.md` |
| The plain-symbol binder beta is mirrored at BARE values only (`Step.sseq_sym_pure`; no LETS-ANNOT variant) | The fragment's only sym-binder producer is the memop protocol, which delivers bare values (step_ctx's MEMOP continuation — `mk_pure_e`, no Eannot residue); the annot variant is a mechanical extension | `Step.lean` (the rule's docstring); `docs/2026-08-31_listrev-notes.md` |
| List-reverse TOTAL export (variant → unconditional driveJ bound, the fib pattern) not delivered: the drive induction must thread a pure heap invariant through the per-iteration memory operations (fib's lane is state-free) | The pure drive-invariant lane is the named mover; the per-iteration step count is fixed (11), so the bound would be 11·n + 6 | `docs/2026-08-31_listrev-notes.md` §Findings |
| Production-face loop export (`runND` equation for a loop run) | The DriverCollapse scheduler equations are pinned at the straight-line profile; the drive-lane step bound (`fib_certified_total`) is the in-budget discharge waiting for it | `ProdEntry.lean`; `docs/2026-08-31_phase2-s4-notes.md` |
| Fuel side condition (no fuel parametricity) | Fuel-irrelevance theorem for `get_ctx` or graceful driver exhaustion would remove it | `docs/2026-08-30_spike-report.md` "What remains"; `ProdEntry.lean` header |
| REMOVE-ANNOT value protocol; canonical-annotation subrelation | Deliberate, engine-faithful readout composition | `Step.lean` header; `docs/2026-08-30_spike-sliceA-notes.md` D1/D3 |

## How to build

From the repository root (offline; deps resolve through the
container's git redirects, which `scripts/capped` self-loads):

```bash
scripts/setup-cerberus-dep.sh        # once: the pinned semantics workspace
cd cerberus-heaplang
../scripts/capped ~/.elan/bin/lake build
```

A green build is the verification run for exactly what the sweeps
check: it elaborates every proof through the Lean kernel and then
`Audit.lean`, which (1) bounds the transitive axiom cone of every
theorem in the package by the declared boundary, (2) pins the
headline theorems' exact cones, and (3) checks every constant of
every kind — defs included — for the banned axioms
(`sorryAx`/`ofReduceBool`/`ofReduceNat`). It certifies nothing
beyond that: in particular it does not discharge the scope
qualifiers above — they are part of the theorem statements. Expected
tail:

```
info: CerberusHeapLang/Audit.lean:385:0: CerberusHeapLang axiom sweep: 827 theorems BOUNDED by the declared upper bounds (40 in the production-entry boundary modules, bounded by trio + runEffectful; all others bounded by the trio; exact cones pinned only for the curated headline list above)
info: CerberusHeapLang/Audit.lean:385:0: CerberusHeapLang banned-axiom sweep: 1670 constants of every kind checked; sorryAx/ofReduceBool/ofReduceNat absent from all cones
Build completed successfully (439 jobs).
```

(In sandboxed environments `../scripts/capped` may warn
`running UNCAPPED` — the cap is a resource-limit wrapper with no
bearing on the verification claim; linter warnings from the
dependency's `generated/*` files ahead of the tail are expected.
The walkthrough §6 gives the full build-experience notes.)

Or run both packages plus the grep gate: `scripts/test_unit.sh` from
the repository root.

## How to verify me

Spot-check the headline cones yourself (from `cerberus-heaplang/`):

```bash
../scripts/capped ~/.elan/bin/lake env lean --stdin <<'EOF'
import CerberusHeapLang
#print axioms CerberusHeapLang.semantic_triple_sound
#print axioms CerberusHeapLang.engine_complete
#print axioms CerberusHeapLang.counter_loop_certified
#print axioms CerberusHeapLang.fib_certified
#print axioms CerberusHeapLang.fib_certified_total
#print axioms CerberusHeapLang.array_sum_certified
#print axioms CerberusHeapLang.list_reverse_certified
#print axioms CerberusHeapLang.list_reverse_demo
#print axioms CerberusHeapLang.exhibitA_prod
#print axioms CerberusHeapLang.counter_loop_certified_production
EOF
```

Observed output (2026-08-31, this checkout):

```
'CerberusHeapLang.semantic_triple_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.engine_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.counter_loop_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.fib_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.fib_certified_total' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.array_sum_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.list_reverse_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.list_reverse_demo' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.exhibitA_prod' depends on axioms: [propext, runEffectful, Classical.choice, Quot.sound]
'CerberusHeapLang.counter_loop_certified_production' depends on axioms: [propext,
 runEffectful,
 Classical.choice,
 Quot.sound]
```

Expected: everything reports exactly
`[propext, Classical.choice, Quot.sound]` except the two
production-entry statements, which additionally carry
`runEffectful` (the one declared temporal boundary, above).
`sorryAx` appearing anywhere is a failure.

To separate the trust base from the proof machinery mechanically,
the statement-surface census (`scripts/statement_census.lean`, a
read-only reporting instrument) bins every constant in each pinned
theorem's statement into engine / spec-idiom / Iris / Lean-core;
the [walkthrough](docs/WALKTHROUGH.md) §5 pastes its output and
reads the three headline statements identifier by identifier. For
per-construct coverage, regenerate the
[capability manifest](docs/CAPABILITY_MANIFEST.md)
(`scripts/capability_manifest.lean`) and diff it against the
committed copy — `scripts/test_unit.sh` gate 4 does exactly that,
and additionally fails if this README's certified-scope token list
strays outside the manifest's adequacy-exportable set.

## The modules

In teaching order (= import order; one line each — the
[walkthrough](docs/WALKTHROUGH.md) §7 has the guided version):

| Module | Contents | Headline |
|--------|----------|----------|
| `Step.lean` | The fragment's mirror small-step over the ENGINE's generated AST/state types (values, `store`/`load`/`create`, the `PtrEq` memop, strong sequencing at wildcard, `Specified`-binder and plain-symbol-binder patterns, `Esave`/`Eif`, value-scrutinee `Ecase` (local rule only — manifest), the global context-discarding `Erun`, pure/operand evaluation, the annotation residue; the runtime tuple carries the live env stack and the per-procedure label map) — hand-written, zero authority until certified | `Step` |
| `Heap.lean` | Points-to over the engine's memory state via iris-lean GenHeap (allocation-rooted byte-list cells); the memM-level store/load facts | `pointsToCell` (`↦c`), `storeM_success`, `loadM_success` |
| `Lang.lean` | The iris-lean `Language` instance over Step (primStep over the runtime tuple, componentwise value protocol, pure-determinism facts for the beta/merge taus, the `SpikeGF` ghost-functor witness). Deliberately NO `Language.Context`/wp_bind instance: the global jump rule falsifies the frame law (`Erun` discards its context), so sequencing is proved directly (`wp_sseq`, `wps_seq`) — the module header records the falsification | `instance : Language CoreRt Mem Empty CoreRVal` |
| `EnvLaws.lean` | The env-map seam, closed: lawfulness of the engine's symbol order (`Std.TransCmp` via the String×Nat lexicographic characterization) and the lookup-after-add law over reachable frames — loop invariants carry `SymFrame` instead of frame-shape pins | `envAdd_lookup` |
| `Rules.lean` | The base logic: small axioms, sequencing, frame, consequence, wand — plus the compositional two-store triple | `wp_store`, `wp_load`, `wp_sseq`, `triple_frame`, `triple_seq` |
| `Wps.lean` | The statement-stratified WP (the classical label-context judgment as a package-local guarded fixpoint): value/jump/step clauses, the jump-aware sequencing rules, the branch/entry rules, the small axioms at the stratum, THE GENERIC TYPED-SUBRANGE RULES (`wps_load_at`/`wps_store_at` over views + the derived whole-cell interior forms — Phase 2, F-04 retired), THE ALLOCATION RULE (`wps_create` through the allocator-cursor resource — Phase 2, D26 retired), the per-label invariant loop rule (and `blockSpecs_intro_variant`, which offers smaller-measure hypotheses but carries NO termination consequence and has no consumer yet — the total lane is Phase 3, manifest Notes 2), and the Löb-tied collapse into the base WP | `wps`, `wps_seq`, `wps_seq_spec`, `wps_load_at`, `wps_store_at`, `wps_create`, `blockSpecs_intro`, `wps_sound` |
| `Soundness.lean` | Per-construct certification of Step against the engine's own `step_ctx` + request discharge (context-undisturbed shape; refusals classified; the jump layer: the evaluator bridge, the factor theorem with the jump disjunct, the context-discard certification, the step-match completeness at the jump profile) | `engine_complete`, `stepDischarge_run`, `DecompJ.step_factor`, `engine_step_matchJ` |
| `Adequacy.lean` | The exported semantic face over engine configurations: triples with an arbitrary framed rest, driven by the engine's step function; the jump-profile drive lane (`driveJ`) with its adequacy and per-step drive equations | `semantic_triple_sound`, `semantic_frame`, `spike_engine_adequacy`, `engine_adequacyJ`, `driveJ_step` |
| `Exhibit.lean` | End-to-end exhibits at the engine level: store-then-load returns 7; the frame exhibit; disjoint sequential stores; termination of the probe program as a theorem | `exhibitA_engine`, `exhibitB_engine`, `exhibitC_engine`, `exhibitA_terminates` |
| `LoopExhibit.lean` | THE FIRST LOOP: the counter loop — save entry, real `x > 0` guard, a store under the loop, the context-discarding back edge — certified end-to-end through `driveJ` with a data-dependent post | `counter_loop_certified` |
| `FibExhibit.lean` | Iterative two-accumulator fib with the data-dependent invariant `a = fib i ∧ b = fib (i+1)`; partial via `engine_adequacyJ`; plus the separate OPERATIONAL ENGINE THEOREM `fib_certified_total` — an unconditional driveJ equation at step bound `2·n+4`, proved by direct operational induction, not by the logic (manifest Notes 2) | `fib_certified`, `fib_certified_total` |
| `ArrayExhibit.lean` | The array-sum walk — real pointer arithmetic, operand-evaluated loads, interior reads of the seeded array allocation, the `Specified`-binder unwrap, the index-partitioned invariant; the array preserved in the conclusion | `array_sum_certified` |
| `StructExhibit.lean` | THE FRESH-CLIENT TEST (Phase 2 acceptance): a two-field struct update (layout `{int x @ 0; int y @ 8}` in one 16-byte allocation — a third distinct layout) verified end-to-end with ZERO core-logic edits — every rule a one-line client instance of the generic subrange rules; plus the allocation consumer (create a fresh struct through the cursor resource and initialize a field) | `struct_update_certified`, `struct_create_store_wps` |
| `ListRevExhibit.lean` | THE CANONICAL EXHIBIT: in-place reversal of a linked list of one-allocation two-field nodes — the honest null encoding + the engine's own `PtrEq` memop as the null test (the null/pointer byte ROUND TRIPS proved against repr/abst), interior next-field loads AND stores by in-allocation arithmetic, `isList` by plain structural recursion, the textbook `blockSpecs_intro` proof with invariant `isList prev reversed ∗ isList cur rest`; conclusion: any delivered value is a pointer whose final-heap chain is `xs.reverse` | `list_reverse_certified`, `list_reverse_demo` |
| `DriverCollapse.lean` | The production scheduler/ND/readout collapsed onto the demo's drive loop — proved from the driver's OWN round functions; bounded by the trio, its three headline equations exact-pinned | `prod_loop_done`, `driver2_done`, `finalize_done` |
| `ProdEntry.lean` | Cold start from the SHIPPED `initial_driver_state` (errno allocated by the real allocator) + the production-entry theorem; the REGISTRATION TIE — `LabeledAt` derived from the shipped `collect_labeled_continuations_NEW` for the authored loop programs, and the counter loop re-exported at the derived tie (the registration theorem — manifest Notes 3) | `sem_triple_prod`, `prod_run_eq`, `fib_labeledAt_production`, `counter_loop_certified_production` |
| `ProdExhibit.lean` | The demonstration: a self-contained program (create/store/load) run through the production pipeline delivers 7 with the exact final bytes | `exhibitA_prod` |
| `Audit.lean` | The in-build axiom gate: curated exact-cone pins + the exhaustive theorem sweep with the module-scoped `runEffectful` boundary + the banned-axiom sweep over every constant kind (all plant-tested both directions — record: `docs/2026-08-31_restructure-notes.md`) | the sweeps |

(`StmtProbe/` is a self-contained toy-language design probe for the
statement WP — no engine imports, no bearing on the claims; kept as
a record.)

History and design findings: the dated records in `docs/`
(`2026-08-30_spike-report.md` is the founding report; plans,
reviews and slice notes alongside).

---

Built by AI agents (Claude, Anthropic) under the direction and
review of Mike Dodds.
