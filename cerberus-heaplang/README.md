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
lemma suite rather than HeapLang's full library (allocation has
PUBLIC partial+total rules over an abstract capacity resource
`allocCap`, launchable through the allocation-aware launchers —
alloc arc P1; EVERY allocating exhibit consumes it whole-program
since alloc arc P2 — the struct client, the create/store/load
production demo, and both allocating loop exports; the re-audit's
R-01/R-02 release blockers are CLOSED). What
it has instead is an object language
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
| `fib_certified`, `fib_certified_total`, `fib_terminates` (FibExhibit.lean) | Iterative fib with invariant `a = fib i ∧ b = fib (i+1)` delivers `fib n`; `fib_certified_total` is the unconditional TOTAL equation — at step bound `2·n + 4`, `driveJ … = .done (fib n) σ₀`, no fuel hypotheses at all — A COROLLARY OF THE TOTAL STATEMENT JUDGMENT through the generic measure→drive-fuel simulation (Phase 3; manifest Notes 2; the variant `2·(n−i)+3` is pinned by the invariant, the back edge discharges the mandatory decrease); `fib_terminates` is strong normalization over the unified relation via Iris TotalAdequacy | partial form: in-budget fuel; total forms: NONE | driveJ + total | trio |
| `array_sum_certified` (ArrayExhibit.lean) | The array walk: real pointer arithmetic, interior loads of a seeded one-allocation array — delivers `vs.sum` with the array preserved | in-budget fuel; seeded array (coherence, per-element decode, size/location) | driveJ | trio |
| `list_reverse_certified`, `list_reverse_demo`, `list_reverse_certified_total`, `list_reverse_terminates` (ListRevExhibit.lean) | THE CANONICAL EXHIBIT AT FULL STRENGTH (Phase 4, audit F-06): SAME-FOOTPRINT, IN-PLACE reversal with FRAME PRESERVATION and TERMINATION — the predicates are indexed by the ordered node list of (allocation id, value); from a seeded chain `m₀` next to an ARBITRARY disjoint frame footprint `R`, any delivered value is a pointer heading a final footprint `Q` with `SeedChain Q p' ns.reverse` (the SAME allocation ids in exactly reversed order — a permutation of the original node set — each node still carrying its own value), the literal footprint equality `∀ k, (get? Q k).isSome ↔ (get? m₀ k).isSome`, and `Sat σ' (Q ∪ R)` — the frame verbatim; the TOTAL form is the same conclusion as an unconditional `driveJ` equation at the DERIVED bound `13·|ns| + 7`, no fuel hypotheses; plus termination over the unified relation; the demo instantiates a 3-node chain, every decode fact `rfl`. No ghost-functor binder in any of the four statements (SpikeGF-concrete) | partial: in-budget fuel + seeded chain + disjoint frame; total: seeded chain + disjoint frame only | driveJ + total | trio |
| `tree_rotate_certified`, `tree_rotate_certified_total` (TreeRotExhibit.lean) | THE SECOND CLIENT (Phase 4 — the accident-detector): in-place right ROTATION of a binary tree (one-allocation three-field nodes: value + two child pointers) through the SAME generic layer with ZERO core-logic edits — seeded tree + arbitrary disjoint frame in; rotated tree (`SeedTree Q py (node y vy a (node x vx b c))` — same allocations, the rotated id list a PERMUTATION of the original, footprint equality stated on the maps) + frame verbatim out; the total form is an unconditional `drive` equation at the constant straight-line budget 19 | partial: in-budget fuel + seeded tree + disjoint frame; total: seeded tree + disjoint frame only | drive + total | trio |
| `exhibitA_prod` (ProdExhibit.lean) | The production run of a self-contained create/store/load program IS the singleton Active execution delivering 7, the final memory holding 7's image at the program's own fresh cell (existential allocation id/address — the program BINDS its created pointer, alloc arc P2). WHOLE-PROGRAM LOGIC PROOF (R-02 conversion, P2 step 3): one total judgment `progAProd_wpt` (PUBLIC `wpt_create` from `allocCap [⟨4,intTy⟩]` + generic heap rules, budget 11) through the generic `wpt_driver_done_alloc` → `prod_run_eqJ` collapse — zero operational proof terms | file-system state and argv only — everything else discharged | production | trio + `runEffectful` |
| `fib_certified_production` (ProdLoopExhibit.lean) | THE PRODUCTION LOOP THEOREM (Phase 5 — audit F-05 closed): running the SHIPPED pipeline `CerbND.runND (Driver.drive …) (initial_driver_state …)` cold on the synthetic fib file IS the singleton Active execution delivering `fib n` — a back-edge loop through the production scheduler itself, label map computed by the shipped registration, termination from the total judgment | `0 ≤ n` + the engine's own fuel budget (`2·n + 6 ≤ 10^6`) + fs/argv | production | trio + `runEffectful` |
| `counter_loop_certified_production` (ProdLoopExhibit.lean) | THE COUNTER LOOP ON THE SHIPPED PIPELINE: a SELF-CONTAINED program that BINDS its engine-created cell (`lets p = create(4,int)`, entry jump carrying the counter AND the pointer as label arguments, the loop storing through the pointer argument); conclusion: one Active execution, value `Vunit`, the program's own cell's final bytes pinned data-dependently at an EXISTENTIAL allocation id/address. WHOLE-PROGRAM LOGIC PROOF (R-02 conversion, alloc arc P2 step 4): `ctrProd_wpt` = create through the PUBLIC `wpt_create` from the one-request plan + the loop's total judgment, collapsed by the generic `wpt_driver_done_alloc` → `prod_run_eqJ` — zero operational proof terms | `0 ≤ n` + the engine's own fuel budget (`7·n + 7 ≤ 10^6`) + fs/argv | production | trio + `runEffectful` |
| `list_reverse_certified_production` (ProdLoopExhibit.lean) | THE FLAGSHIP'S PRODUCTION INSTANCE: a SELF-CONTAINED two-node build-and-reverse program that BINDS its engine-created nodes (two `lets n = create(8,node)` binds, four field stores through the bound pointers, entry jump into the authored flagship loop); conclusion: one Active execution whose delivered pointer heads a footprint seeded as the REVERSED chain — the program's OWN nodes at EXISTENTIAL engine-picked allocation ids, own values — satisfied by the final production memory. WHOLE-PROGRAM LOGIC PROOF (R-02 conversion, alloc arc P2 step 5): `lrProd_wpt` = two PUBLIC `wpt_create`s from the two-request plan (their exported address bounds feeding `isList`'s node WF) + the generic typed-subrange stores + the GENERIC list logic consumed VERBATIM at the existential ids (`wpt_mono_Ls` transport), collapsed by `wpt_driver_done_alloc` → `prod_run_eqJ` — zero operational proof terms | fs/argv only — everything else discharged | production | trio + `runEffectful` |
| `counter_loop_certified_registration` (ProdEntry.lean) | THE REGISTRATION THEOREM (renamed at Phase 5 from `counter_loop_certified_production` — the F-05 naming debt paid): the counter loop re-exported with the label plumbing DERIVED from the shipped label-collection — nothing hand-built; the driveJ-lane tie, kept as a lemma | as `counter_loop_certified` | driveJ @ production run state | trio + `runEffectful` |

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
at all. Straight-line programs AND loop programs are exported all
the way to the production lane (Phase 5 — the proc-carrying,
populated-label scheduler collapse: `fib_certified_production`,
`counter_loop_certified_production`,
`list_reverse_certified_production`); the drive-lane loop theorems
remain as the engine-level lemmas beneath them. Every
drive-lane statement also quantifies over `aids : Nat → Nat`, the
action-id supply: the oracle for the driver's fresh action-id
draws, ∀-quantified so the theorems hold for every supply — on
this deterministic fragment the choice is irrelevant.

The proof of the flagship is textbook-compositional and that is the
point of the exhibit: representation predicate `isList` by plain
structural recursion (no step-indexing), IDENTITY-INDEXED since
Phase 4 (each node is its allocation id paired with its value — the
metadata heap's authority), loop invariant
`isList prev reversed ∗ isList cur rest ∗ RF` with
`ns = reversed.reverse ++ rest` (the arbitrary frame `RF` threaded
through the invariant — the only thing that crosses a back edge),
every construct discharged by its small axiom or rule, no
monolithic unfolding anywhere.

## The trust story

The only trusted semantics is the cerberus-lean operational
semantics (the Lean port of Cerberus Core, pinned by commit in
`../scripts/semantics-pin.env` and differentially validated
upstream against the OCaml oracle); everything in this package is
derived and proved down into that engine. Every theorem is
kernel-checked with its transitive axiom cone BOUNDED in-build, the
boundary axiom's origin MECHANICALLY CHECKED, and the headline
theorems' cones EXACTLY PINNED
(`CerberusHeapLang/Audit.lean`, the last import of the library
root — the exhaustive sweep is an upper-bound check PLUS, in the
boundary modules, the Phase-5 ORIGIN DISCIPLINE: `runEffectful` in
a theorem's cone must be reachable through the statement's
constants, so every boundary cone is exact-by-construction; the
curated pins are additional equality checks): every cone is within
the classical trio (`propext`, `Classical.choice`, `Quot.sound`),
except in the three production-entry modules (`ProdEntry`,
`ProdExhibit`, `ProdLoopExhibit`) whose
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
three production-entry modules only (mechanically enforced: the
in-build origin discipline fails the build on any proof-borne
occurrence) — the shipped
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
Phase 1 item 6; the relation-closure question — two-sided coverage
of the package's own projection — is re-audit R-03, owner alloc arc
P3: the closure table, `docs/2026-09-01_alloc-arc-plan.md`).

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
(`hsz`/`hlib`); `list_reverse_certified` (Phase 4 — the full
F-06 statement) is stated over a SEEDED INPUT CHAIN
(`SeedChain m₀ head ns` — the node list `ns` carries each node's
ALLOCATION ID with its value; one disjoint one-allocation cell per
node at that id, engine-serialized field images, per-node
machine-address WF `0 < a < 2^64`) NEXT TO an arbitrary disjoint
frame footprint `R` (the `SemTriple` rest-quantifier at the driveJ
lane), and concludes that any delivered value is a POINTER heading
a final footprint `Q` with `SeedChain Q p' ns.reverse` — the same
allocations, in exactly reversed chain order, each node its own
value — plus the literal footprint equality
`∀ k, (get? Q k).isSome ↔ (get? m₀ k).isSome` and
`Sat σ' (Q ∪ R)`: the frame returned VERBATIM (the id-indexed
`ChainAt` readout is a demoted corollary via `seedChain_chainAt`;
the concrete `list_reverse_demo` instantiates a 3-node chain with
every decode fact discharged by `rfl` and includes it); the SECOND
CLIENT `tree_rotate_certified` (TreeRotExhibit.lean) replays the
same statement shape for a binary-tree rotation with zero core
edits — except the TOTAL exports, which are UNCONDITIONAL:
`fib_certified_total` (at the concrete step bound `2·n + 4`,
`driveJ` DELIVERS `fib n` with the state verbatim, no fuel
hypotheses at all), `list_reverse_certified_total` (at the
DERIVED bound `13·|ns| + 7`, `driveJ` delivers the reversed final
chain, same footprint, frame verbatim) and
`tree_rotate_certified_total` (constant budget 19). Since
foundations Phase 3 these ARE logic results (audit
F-02 remediated): corollaries of the total statement judgment
(`wpt`, Wpt.lean — mandatory back-edge variant decrease, collapse
into the pinned Iris TotalWeakestPre) through the generic
measure→drive-fuel simulation (TotalAdequacy.lean), with zero
example-level `Step`/`driveJ_step` rewrites; the companion
`fib_terminates`/`list_reverse_terminates` state termination over
the unified relation via Iris TotalAdequacy (`twp_total`), and the
negative exhibit `diverge_total_unprovable` (DivergeExhibit.lean)
shows a diverging loop's total derivation is FALSE — the mandatory
decrease is what makes it unprovable (manifest Notes 2). Scope
honesty for all of them: the
drive lane is the sequential driver's loop projected to
(thread_state, MemState) with the run state a constant parameter
(certified faithful for this fragment — the real driver
additionally ticks `aid_supply`, which the fragment ignores). The
PRODUCTION-pipeline export of loop runs IS established (Phase 5):
the `*_production` theorems (ProdLoopExhibit.lean) conclude about
the shipped `runND ∘ Driver.drive ∘ initial_driver_state` composite
through the proc-carrying scheduler collapse — one production
driver round per certified mirror step, driven by the total
statement judgment — with the label plumbing DERIVED from the
shipped registration (`fib_labeledAt_production` /
`loop_labeledAt_production` / the per-program `*_labeledAt` ties:
the exhibits' label maps are exactly what
`collect_labeled_continuations_NEW ∘ initial_core_run_state`
computes); `counter_loop_certified_registration` (the renamed F-05
naming debt) remains the driveJ-lane registration lemma. ONE SCOPE
DISCLOSURE on the self-contained exports (2026-09-01 re-audit,
R-02): their ALLOCATION PREFIXES are NOT driven by the logic — the
cold-start creates (and the reversal instance's chain-building field
stores) are handwritten certified operational rounds crossing
`driverDone_step`; the total statement judgment drives the loop
suffixes only. The allocation LOGIC PATH itself is repaired (alloc
arc P1): public `wps_create`/`wpt_create` over the abstract
capacity `allocCap`, allocation-aware launchers granting it from
real memory, and a minimal engine-facing chain-closer
(`alloc_create_launch_smoke`, AllocExhibit — a `driveU` `.done`
equation at fuel 2 through the public total rule). Whole-program
consumers (alloc arc P2): the struct client + adequacy, and
`exhibitA_prod`'s complete create/store/load. The two allocating
LOOP exports do NOT yet consume the path — P2 steps 4-5.

The flagship straight-line demonstration is unconditional:
`exhibitA_prod` (ProdExhibit.lean) quantifies over nothing but the
file-system state `fs` and the argument list `args` — every other
hypothesis is discharged concretely — and concludes that the
production run of its create/store/load program IS the singleton
Active execution delivering 7 with the exact final bytes. Its PROOF
is a WHOLE-PROGRAM LOGIC proof since alloc arc P2 (R-02 conversion):
the program binds its created pointer, one total judgment carries
create/store/load through the PUBLIC `wpt_create` and the generic
heap rules, and the generic allocation-aware driver collapse
(`wpt_driver_done_alloc` → `prod_run_eqJ`) reaches the shipped
pipeline — no handwritten operational rounds remain in the module.

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
| Allocation rules + launch REPAIRED (alloc arc P1), partial-lane whole-program consumer LANDED (P2 items 1-2): the public `wps_create`/`wpt_create` (existential pointer, `allocCap` capacity, cursor-free statements, pure address-bounds export) are launchable via the allocation-aware launchers (`launchResources` under `LaunchCoh`), with local consumers, the engine-facing smoke `alloc_create_launch_smoke` (AllocExhibit), and the struct client `struct_create_store_wps`/`struct_create_store_adequacy` (StructExhibit — public rule + engine-facing adequacy through `spike_engine_adequacy_alloc`); and — alloc arc P2 — the whole-program production consumers (`progAProd_wpt`/`ctrProd_wpt`/`lrProd_wpt` through `wpt_driver_done_alloc`); R-01's closure test PASSED (deleting the public rule breaks the struct/two-create consumers; deleting `wpt_create` breaks the create/store/load and both loop production chains; deleting `launchResources` breaks the launch family — plant transcripts in `docs/2026-09-01_p2-notes.md`) | — (CLOSED; the closure table records the transcripts: `docs/2026-09-01_alloc-arc-plan.md`) | `Wps.lean`/`Wpt.lean` §CreateRule headers; `docs/2026-09-01_p1-notes.md` + `docs/2026-09-01_p2-notes.md`; 2026-09-01 skeptical re-audit R-01 |
| ~~R-02 (allocating exhibits bypass the separation logic)~~ CLOSED at alloc arc P2: all three allocating production exports are whole-program logic proofs (the programs bind their created pointers; creates cross the PUBLIC `wpt_create`; the generic `wpt_driver_done_alloc` → `prod_run_eqJ` collapse supplies every pipeline arrow); every handwritten `Step.*`/`engineSteps_*`/`driverDone_step` proof chain is DELETED from the positive exhibits (grep transcript + closure-test plants: `docs/2026-09-01_p2-notes.md`; closure table: `docs/2026-09-01_alloc-arc-plan.md`) | — (closed; the dependency-certified manifest upgrade is P3, R-04) | `ProdLoopExhibit.lean`/`ProdExhibit.lean` headers; 2026-09-01 skeptical re-audit R-02 |
| `Ewseq` at spec/sym binder patterns outside the fragment (the WILDCARD lane exported in S1b as the drift test); `Ecase`'s EVAL arm (non-value scrutinees) unmirrored | Mechanical per-construct extension, path named | `Step.lean` header; `docs/2026-08-30_spike-report.md` "Honestly open" |
| PURE exits certified at `PEsym` shape only (general `PePure` exits are a bounded matcher extension) | Extend `stepDischarge_pure_sym` per-constructor when needed | `Soundness.lean`; `docs/2026-08-31_phase2-s4-notes.md` |
| The array exhibit's pre-state is ONE allocation (not a ∗-of-per-element-cells): the engine's loads bounds-check against the pointer's PROVENANCE allocation and `arrayShiftPtrval` preserves provenance, so distinct-allocation "arrays" are not walkable in the engine — C's object model | Forcing fact about Cerberus, recorded; per-element structure lives in the index-partitioned invariant + decode premises | `ArrayExhibit.lean` header; `docs/2026-08-31_phase2-s4-notes.md` |
| The pointer-test memop coverage is `PtrEq` only; the family (PtrNe/Lt/…) and eqPtrval's differing-provenance ND fork are fail-closed ABSENCES of a mirror step (the fork is a real `msum`, CerbMem.lean:1753 — enumerated by the exhaustive runners, not single-layer) | Mechanical per-memop extension (dischargeStep arm + Step rule + wps axiom) | `Soundness.lean` dischargeStep memop arm; `docs/2026-08-31_listrev-notes.md` |
| The plain-symbol binder beta is mirrored at BARE values only (`Step.sseq_sym_pure`; no LETS-ANNOT variant) | The fragment's only sym-binder producer is the memop protocol, which delivers bare values (step_ctx's MEMOP continuation — `mk_pure_e`, no Eannot residue); the annot variant is a mechanical extension | `Step.lean` (the rule's docstring); `docs/2026-08-31_listrev-notes.md` |
| List-reverse TOTAL export: RETIRED (foundations Phase 3) — `list_reverse_certified_total` delivers the unconditional bound through the total judgment (the heap-resident variant rides the variant-indexed invariant); the DERIVED bound is `13·|ns| + 7` (the old 11-per-iteration note undercounted the wrapper-merge step; the true engine cost is 12 per iteration plus one unit of budget-reservation slack, documented at `lrCost`) | Closed by `docs/2026-09-01_phase3-notes.md` | `ListRevExhibit.lean` §total lane |
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
info: CerberusHeapLang/Audit.lean:622:0: CerberusHeapLang axiom sweep: 1123 theorems BOUNDED by the declared upper bounds (71 in the production-entry boundary modules, of which 13 carry the boundary axiom — each STATEMENT-BORNE, origin-checked, so every boundary cone is exact-by-construction: trio + runEffectful iff the statement carries it; all other theorems bounded by the trio; headline cones additionally pinned above)
info: CerberusHeapLang/Audit.lean:622:0: CerberusHeapLang banned-axiom sweep: 2075 constants of every kind checked; sorryAx/ofReduceBool/ofReduceNat absent from all cones
Build completed successfully (443 jobs).
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
#print axioms CerberusHeapLang.tree_rotate_certified
#print axioms CerberusHeapLang.tree_rotate_certified_total
#print axioms CerberusHeapLang.exhibitA_prod
#print axioms CerberusHeapLang.counter_loop_certified_registration
EOF
```

Observed output (2026-09-01, this checkout):

```
'CerberusHeapLang.semantic_triple_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.engine_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.counter_loop_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.fib_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.fib_certified_total' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.array_sum_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.list_reverse_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.list_reverse_demo' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.tree_rotate_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.tree_rotate_certified_total' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.exhibitA_prod' depends on axioms: [propext, runEffectful, Classical.choice, Quot.sound]
'CerberusHeapLang.counter_loop_certified_registration' depends on axioms: [propext,
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
the statement-surface census (`scripts/statement_census.lean`) bins
every constant in each pinned theorem's statement into engine /
spec-idiom / Iris / Lean-core; its output is committed
(`docs/STATEMENT_CENSUS.txt`) and drift-checked by
`scripts/test_unit.sh` gate 5, so a pinned export's statement
surface cannot change without a deliberate same-commit re-baseline;
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
| `Step.lean` | The fragment's mirror small-step over the ENGINE's generated AST/state types (values, `store`/`load`/`create`, the `PtrEq` memop, strong sequencing at wildcard, `Specified`-binder and plain-symbol-binder patterns, `Esave`/`Eif`, value-scrutinee `Ecase`, the global context-discarding `Erun`, pure/operand evaluation, the annotation residue; the runtime tuple carries the live env stack and the per-procedure label map) — hand-written, zero authority until certified | `Step` |
| `Heap.lean` | Points-to over the engine's memory state via iris-lean GenHeap (allocation-rooted byte-list cells); the memM-level store/load facts | `pointsToCell` (`↦c`), `storeM_success`, `loadM_success` |
| `Lang.lean` | The iris-lean `Language` instance over Step (primStep over the runtime tuple, componentwise value protocol, pure-determinism facts for the beta/merge taus, the `SpikeGF` ghost-functor witness). Deliberately NO `Language.Context`/wp_bind instance: the global jump rule falsifies the frame law (`Erun` discards its context), so sequencing is proved directly (`wp_sseq`, `wps_seq`) — the module header records the falsification | `instance : Language CoreRt Mem Empty CoreRVal` |
| `EnvLaws.lean` | The env-map seam, closed: lawfulness of the engine's symbol order (`Std.TransCmp` via the String×Nat lexicographic characterization) and the lookup-after-add law over reachable frames — loop invariants carry `SymFrame` instead of frame-shape pins | `envAdd_lookup` |
| `Rules.lean` | The base logic: small axioms, sequencing, frame, consequence, wand — plus the compositional two-store triple | `wp_store`, `wp_load`, `wp_sseq`, `triple_frame`, `triple_seq` |
| `Wps.lean` | The statement-stratified WP (the classical label-context judgment as a package-local guarded fixpoint): value/jump/step clauses, the jump-aware sequencing rules, the branch/entry rules, the small axioms at the stratum, THE GENERIC TYPED-SUBRANGE RULES (`wps_load_at`/`wps_store_at` over views + the derived whole-cell interior forms — Phase 2, F-04 retired), THE ALLOCATION RULES (the PUBLIC `wps_create` over the abstract capacity `allocCap` — existential pointer, cursor-free statement, launchable through the allocation-aware launchers; the exact-cursor `wps_create_cursor_internal` is heap-implementation-only — alloc arc P1), the per-label invariant loop rule `blockSpecs_intro` (partial correctness; the retired `blockSpecs_intro_variant` is replaced by the TOTAL stratum's `blockSpecsT`, Wpt.lean), and the Löb-tied collapse into the base WP | `wps`, `wps_seq`, `wps_seq_spec`, `wps_load_at`, `wps_store_at`, `wps_create`, `blockSpecs_intro`, `wps_sound` |
| `Wpt.lean` | THE TOTAL STATEMENT JUDGMENT (foundations Phase 3, audit F-02): `wpt M Ls k Ψ e ρ` by structural recursion on the step budget — variant-indexed label preconditions (`LabelSpecT`), MANDATORY back-edge decrease in the jump clause, the total rule set (sequencing/branch/entry/memory, plus — alloc arc P1 — the PUBLIC total allocation rule `wpt_create` over `allocCap` at the derived cost bound 2, with its internal exact-cursor form), `blockSpecsT` (replacing the retired variant lemma), and the collapse into the pinned Iris TotalWeakestPre | `wpt`, `wpt_run`, `wpt_seq`, `wpt_create`, `blockSpecsT`, `wpt_sound` |
| `Soundness.lean` | Per-construct certification of Step against the engine's own `step_ctx` + request discharge (context-undisturbed shape; refusals classified; the evaluator bridge, the factor theorem with the jump disjunct, the context-discard certification, and the UNIFIED step-match over the whole cone at any MachineCtx) | `engine_complete`, `stepDischarge_run`, `Decomp.step_factor`, `engine_step_matchU` |
| `Adequacy.lean` | The exported semantic face over engine configurations: triples with an arbitrary framed rest, driven by the engine's step function; the jump-profile drive lane (`driveJ`) with its adequacy and per-step drive equations; alloc arc P1: `LaunchCoh` (footprint coherence + allocator health + plan fit) and the ONE shared allocation-aware launch `launchResources` (cursor key 0 minted NONEMPTY, `allocCap` granted), with the allocation-aware step launcher | `semantic_triple_sound`, `semantic_frame`, `spike_engine_adequacy`, `engine_adequacyJ`, `driveJ_step`, `launchResources`, `spike_step_adequacy_alloc` |
| `TotalAdequacy.lean` | The two halves of total correctness, separated per the audit: TERMINATION over the unified relation (Iris `twp_total` consumed as-is) and THE GENERIC MEASURE→DRIVE-FUEL SIMULATION (the judgment's budget IS driveJ fuel — unconditional `.done` equations), on the step-monotone size potential `pot` (static fuel honesty, no run-length coupling) and the state-inert cone (final-state pins for action-free programs); alloc arc P1: allocation-aware variants of all three total launchers through `launchResources` | `wpt_strongly_normalizing`, `wpt_engine_boundJ`, `wpt_engine_boundU_alloc`, `Frag.pot_step_bound` |
| `Exhibit.lean` | End-to-end exhibits at the engine level: store-then-load returns 7; the frame exhibit; disjoint sequential stores; termination-with-delivery via the GENERIC total route (alloc arc P2: the example-specific six-step trace `exhibitA_terminates` retired for `progA_wpt` + `wpt_engine_boundU`) | `exhibitA_engine`, `exhibitB_engine`, `exhibitC_engine`, `exhibitA_total` |
| `LoopExhibit.lean` | THE FIRST LOOP: the counter loop — save entry, real `x > 0` guard, a store under the loop, the context-discarding back edge — certified end-to-end through `driveJ` with a data-dependent post | `counter_loop_certified` |
| `FibExhibit.lean` | Iterative two-accumulator fib with the data-dependent invariant `a = fib i ∧ b = fib (i+1)`; partial via `engine_adequacyJ`; TOTAL via the total judgment (Phase 3): `fib_certified_total` — the unconditional driveJ equation at step bound `2·n+4`, state verbatim — as a corollary of the generic simulation (zero Step constructors), plus `fib_terminates` (strong normalization via Iris TotalAdequacy) | `fib_certified`, `fib_certified_total`, `fib_terminates` |
| `DivergeExhibit.lean` | THE NEGATIVE TEST of the total lane: the self-jump loop steps to itself, is not strongly normalizing, and any total derivation for it is FALSE — the mandatory decrease is exactly what blocks it (the module header records the stuck obligation) | `diverge_total_unprovable` |
| `ArrayExhibit.lean` | The array-sum walk — real pointer arithmetic, operand-evaluated loads, interior reads of the seeded array allocation, the `Specified`-binder unwrap, the index-partitioned invariant; the array preserved in the conclusion | `array_sum_certified` |
| `StructExhibit.lean` | THE FRESH-CLIENT TEST (Phase 2 acceptance): a two-field struct update (layout `{int x @ 0; int y @ 8}` in one 16-byte allocation — a third distinct layout) verified end-to-end with ZERO core-logic edits — every rule a one-line client instance of the generic subrange rules; plus the allocation CLIENT (alloc arc P2 items 1-2: `lets p = create(align, struct) in ... store through p` proved from `allocCap` through the PUBLIC `wps_create` — the program binds the fresh pointer, no cursor vocabulary — and exported to the engine from the production cold-start memory through `spike_engine_adequacy_alloc`) | `struct_update_certified`, `struct_create_store_wps`, `struct_create_store_adequacy` |
| `AllocExhibit.lean` | THE PUBLIC ALLOCATION RULES' LOCAL CONSUMERS + THE LAUNCHER SMOKE (alloc arc P1.4): two creates consume a two-element plan IN ORDER (partial lane), one create at the derived minimal budget 2 (total lane), and the chain-closing engine smoke — a bare create from the production cold-start memory, proved ONLY through the public `wpt_create` and launched ONLY through `wpt_engine_boundU_alloc`, delivering a pointer at `driveU` fuel exactly 2; NO operational proof terms in this module | `alloc_two_creates_wps`, `alloc_create_wpt`, `alloc_create_launch_smoke` |
| `ListRevExhibit.lean` | THE CANONICAL EXHIBIT AT FULL STRENGTH (Phase 4): in-place reversal of a linked list of one-allocation two-field nodes — the honest null encoding + the engine's own `PtrEq` memop as the null test (the null/pointer byte ROUND TRIPS proved against repr/abst), interior next-field loads AND stores by in-allocation arithmetic, IDENTITY-INDEXED `isList` by plain structural recursion (allocation id × value per node), the textbook `blockSpecs_intro` proof with invariant `isList prev reversed ∗ isList cur rest ∗ RF`; conclusion: same-footprint in-place reversal (`SeedChain Q p' ns.reverse` + the literal footprint-equality conjunct) with an arbitrary disjoint frame returned verbatim; the TOTAL lane: the same textbook derivation at the total judgment yields the unconditional equation at the derived bound `13·|ns|+7` plus termination | `list_reverse_certified`, `list_reverse_demo`, `list_reverse_certified_total`, `list_reverse_terminates` |
| `TreeRotExhibit.lean` | THE SECOND CLIENT (Phase 4 — the accident-detector): binary-tree right rotation over one-allocation three-field nodes (value + two child pointers; the splice-ABOVE slice law's first consumer), identity-indexed `isTree`/`SeedTree` with BRANCHING recursion, certified end-to-end with ZERO core-logic edits at the flagship statement shape (same allocations — the rotated id list a permutation of the original — footprint equality, frame verbatim), partial + unconditional total (constant budget 19) | `tree_rotate_certified`, `tree_rotate_certified_total` |
| `DriverCollapse.lean` | The production scheduler/ND/readout collapsed onto the demo's drive loop — proved from the driver's OWN round functions; Phase 5 extends the round algebra to proc-carrying, populated-label threads (with-runstate and memop rounds; the per-redex driver step-match `loop_step_frag` over the full cone); bounded by the trio | `prod_loop_done`, `driver2_done`, `finalize_done`, `loop_step_frag` |
| `ProdEntry.lean` | Cold start from the SHIPPED `initial_driver_state` (errno allocated by the real allocator) + the production-entry theorem; the REGISTRATION TIE — `LabeledAt` derived from the shipped `collect_labeled_continuations_NEW` for the authored loop programs, and the counter loop re-exported at the derived tie (the registration theorem — manifest Notes 3) | `sem_triple_prod`, `prod_run_eq`, `fib_labeledAt_production`, `counter_loop_certified_registration` |
| `ProdLoop.lean` | Phase 5: the total statement judgment drives the PRODUCTION DRIVER'S OWN LOOP — the driver-level analog of the measure→drive-fuel simulation (one production round per budget unit, jump rounds included), trio-only | `wpt_driver_done` |
| `ProdLoopExhibit.lean` | THE PRODUCTION LOOP EQUATIONS — loop programs certified as `CerbND.runND (Driver.drive …) (initial_driver_state …)` equations from the cold start (no package drive/driveJ in any statement); the counter and reversal programs are SELF-CONTAINED WHOLE-PROGRAM LOGIC PROOFS (alloc arc P2: the programs bind their engine-created pointers; creates through the PUBLIC `wpt_create`; the reversal consumes the generic list logic verbatim at existential engine-picked ids) | `ctrProd_wpt`, `lrProd_wpt`, `fib_certified_production`, `counter_loop_certified_production`, `list_reverse_certified_production` |
| `ProdExhibit.lean` | The demonstration: a self-contained program (create/store/load — the fresh pointer BOUND by the program) run through the production pipeline delivers 7 at the program's own cell — ONE whole-program total judgment through the PUBLIC create rule and the generic driver collapse (R-02 conversion, P2 step 3) | `progAProd_wpt`, `exhibitA_prod` |
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
