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

**The per-construct scope statement is the generated
[capability manifest](docs/CAPABILITY_MANIFEST.md)** — one row per
constructor of the fragment `Frag`, read out of the built
environment (an unmapped constructor is a red run), naming the
logical rule that covers the construct and the exhibit modules whose
proofs actually depend on that rule (proof-term dependency cone); a
rule consumed by no exhibit is a red row. It is a claim-point
SPEEDBUMP ([USER 2026-09-02]: the trust base is the builds with
their in-build axiom sweeps plus the banned-methods grep; everything
else is a report that catches honest drift, not a gate designed to
survive adversarial attack) — `scripts/test_unit.sh` regenerates it
and reports drift or a red row. Every scope claim in this README is
read under it: a construct is claimed at exactly its manifest level,
no more. (The dependency-certifying/layer-cut generator of alloc arc
P3 was cut in P3.5: `docs/2026-09-02_p3.5-notes.md`.)

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
| `exhibitA_prod` (ProdExhibit.lean) | The production run of a self-contained create/store/load program IS the singleton Active execution delivering 7, the final memory holding 7's image at the program's own fresh cell (existential allocation id/address — the program BINDS its created pointer, alloc arc P2). WHOLE-PROGRAM LOGIC PROOF (R-02 conversion, P2 step 3): one total judgment `progAProd_wpt` (PUBLIC `wpt_create` from `allocCap [⟨4,intTy⟩]` + generic heap rules, budget 11) through the generic `wpt_driver_done_alloc` → `prod_run_eqJ` collapse — zero operational proof terms | file-system state and argv only — everything else discharged | production | trio |
| `fib_certified_production` (ProdLoopExhibit.lean) | THE PRODUCTION LOOP THEOREM (Phase 5 — audit F-05 closed): running the SHIPPED pipeline `CerbND.runND (Driver.drive …) (initial_driver_state …)` cold on the synthetic fib file IS the singleton Active execution delivering `fib n` — a back-edge loop through the production scheduler itself, label map computed by the shipped registration, termination from the total judgment | `0 ≤ n` + the engine's own fuel budget (`2·n + 6 ≤ 10^6`) + fs/argv | production | trio |
| `counter_loop_certified_production` (ProdLoopExhibit.lean) | THE COUNTER LOOP ON THE SHIPPED PIPELINE: a SELF-CONTAINED program that BINDS its engine-created cell (`lets p = create(4,int)`, entry jump carrying the counter AND the pointer as label arguments, the loop storing through the pointer argument); conclusion: one Active execution, value `Vunit`, the program's own cell's final bytes pinned data-dependently at an EXISTENTIAL allocation id/address. WHOLE-PROGRAM LOGIC PROOF (R-02 conversion, alloc arc P2 step 4): `ctrProd_wpt` = create through the PUBLIC `wpt_create` from the one-request plan + the loop's total judgment, collapsed by the generic `wpt_driver_done_alloc` → `prod_run_eqJ` — zero operational proof terms | `0 ≤ n` + the engine's own fuel budget (`7·n + 7 ≤ 10^6`) + fs/argv | production | trio |
| `list_reverse_certified_production` (ProdLoopExhibit.lean) | THE FLAGSHIP'S PRODUCTION INSTANCE: a SELF-CONTAINED two-node build-and-reverse program that BINDS its engine-created nodes (two `lets n = create(8,node)` binds, four field stores through the bound pointers, entry jump into the authored flagship loop); conclusion: one Active execution whose delivered pointer heads a footprint seeded as the REVERSED chain — the program's OWN nodes at EXISTENTIAL engine-picked allocation ids, own values — satisfied by the final production memory. WHOLE-PROGRAM LOGIC PROOF (R-02 conversion, alloc arc P2 step 5): `lrProd_wpt` = two PUBLIC `wpt_create`s from the two-request plan (their exported address bounds feeding `isList`'s node WF) + the generic typed-subrange stores + the GENERIC list logic consumed VERBATIM at the existential ids (`wpt_mono_Ls` transport), collapsed by `wpt_driver_done_alloc` → `prod_run_eqJ` — zero operational proof terms | fs/argv only — everything else discharged | production | trio |
| `counter_loop_certified_registration` (ProdEntry.lean) | THE REGISTRATION THEOREM (renamed at Phase 5 from `counter_loop_certified_production` — the F-05 naming debt paid): the counter loop re-exported with the label plumbing DERIVED from the shipped label-collection — nothing hand-built; the driveJ-lane tie, kept as a lemma | as `counter_loop_certified` | driveJ @ production run state | trio |

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
`isList prev reversed ∗ isList cur rest` with
`ns = reversed.reverse ++ rest` — UNFRAMED: the arbitrary frame is
added afterwards by the generic statement-level frame rule
(`wps_frame_labels`/`blockSpecs_frame`, alloc arc P4.2), which
carries it across every back edge through the framed label context
`frameLs` — every construct discharged by its small axiom or rule,
no monolithic unfolding anywhere.

## The trust story

The only trusted semantics is the cerberus-lean operational
semantics (the Lean port of Cerberus Core, pinned by commit in
`../scripts/semantics-pin.env` and differentially validated
upstream against the OCaml oracle); everything in this package is
derived and proved down into that engine. Every theorem is
kernel-checked with its transitive axiom cone BOUNDED in-build and
the public exports' cones EXACTLY PINNED
(`CerberusHeapLang/Audit.lean`, the last import of the library
root): THE TRUST BASE IS THE CLASSICAL TRIO (`propext`,
`Classical.choice`, `Quot.sound`), EXACTLY, OVER EVERY EXPORT — no
module is allowed anything else, and the semantics dependency
declares no axiom of its own (the lem runtime's former effect-erasure
axiom `runEffectful`, once a declared temporal boundary of the
production-entry statements, was retired upstream by the cerberus-lean
effect-retirement arc and left this package at the 2026-09-02 re-pin;
the production entry is now the pure supply-threaded
`initial_driver_state`, over whose supply the production theorems
quantify). Non-kernel proof methods (`native_decide`, `bv_decide`,
`ofReduce*`) are banned by a grep gate and would in any case enter a
cone and fail the audit — a build that weakens any of this fails.

**Two trust claims** ([USER 2026-09-02], DECISIONS; the structure the
rest of this section fills in). (1) The CLOSED-PROGRAM exports have
Iris-free statements: their referents are cerberus-lean's semantics —
`step_ctx`/the driver's discharge in the drive lanes, the shipped
`runND ∘ drive ∘ initial_driver_state` in the production lane — plus
the pure readout predicates (`Sat`/`CellCoh`, `readBytesFrom`, the
seeded footprints). iris-lean appears only INSIDE their kernel-checked
proof terms and contributes no axiom (every export's cone is pinned to
the classical trio), so for these statements it is CHECKED, not
trusted. (2) The REUSABLE rules are stated in Iris assertions
(`pointsToCell`/`cellOwn`, `CohG`, iris-lean's WP and BI connectives),
and that must-read set — the specification idiom — is the one sense
in which iris-lean is "in the trust base": definitions to read, not
axioms to accept. THE PROJECTION THEOREM makes claim (1) uniform
(`project_triple`, `Adequacy.lean`; record
`docs/2026-09-02_projection-notes.md`): ANY Iris triple with a
concrete-map precondition and an ARBITRARY Iris postcondition projects
to the boring triple over engine states `MemTripleU` — memory splits
as P ⊎ R, the engine's drive never kills or derails, every delivered
`(v, σ')` satisfies "every pure consequence of the Iris post (with the
frame) at σ'" — with no rule restated and no second assertion language
([USER]: "state properties via iris but don't mirror the logic"); the
pure-consequence lemmas (`cellOwn_consequence`,
`pointsToCell_consequence`, `cells_consequence`, the `∗`/`∨`/`∃`/pure
combinators) discharge that post for the points-to shapes, and the
exhibits' engine readouts are their instances.

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
and coverage is reported by the
[capability manifest](docs/CAPABILITY_MANIFEST.md) rather than
trusted to prose (its row set is derived from the fragment's
constructors in the built environment — a fragment constructor
without a mapped, exhibit-consumed rule is a red row at the claim
gate, so the coverage channel closes by a visible report, not by
vigilance). What remains statement-level trust — the specification
idiom: the drive-loop projections and the footprint/readout
predicates the exported statements are phrased in — is kept small,
pinned by executable concrete instances (the demos), and laid out
for reading, identifier by identifier, in the
[walkthrough](docs/WALKTHROUGH.md) §5 (the trust tiers are its §4).

### What you are asked to take on faith

Self-contained, because this is the only place where the trust
story bottoms out outside this package.

**No axiom beyond Lean's own three.** Every theorem's cone is exactly
the classical trio; neither this package nor the pinned semantics
workspace nor its lem runtime (`LemLib`, zero `axiom` declarations at
the pin) declares an axiom. (Until 2026-09-02 there was one — the lem
runtime's effect-erasure seam `runEffectful`, entering through the
production-entry statements; the cerberus-lean effect-retirement arc
deleted it, and the re-pin record is
`docs/2026-09-02_repin-notes.md`.) What remains on the engine's
RUNTIME trust boundary — kernel-checked opaques with native
implementations (`CerberusFresh.digest`, the CerbGlobal switch refs)
— contributes nothing to any axiom cone and cannot be unfolded by
any proof.

**What "differentially validated" covers.** The Lean port and
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
Phase 1 item 6). The relation-closure question (re-audit R-03) is
answered at alloc arc P3.2 (`Round.lean`): the engine-facing
one-round relation is NAMED — `CerberusRound M aid`, the graph of
the discharged `step_ctx` round, chosen as the reference relation
because one round is exactly the unit the shipped driver iterates —
and `cerberusRound_classify` classifies EVERY well-sized `Frag`
configuration into value-done / value-annot / two-sided step
(`Step M c c' ↔ CerberusRound M aid c c'` wherever the mirror steps)
/ mirror-stuck; the capability manifest derives its engine-match
column from that theorem. The honest residual: at mirror-STUCK
configurations the engine's behavior is classified only for the
store/load/create/case redexes (`cerberusRound_refused_*`); the
other rows' refusal channels are `failwithI` panics (opaque — not
classifiable in the kernel) or the memop ND fork, listed per row in
the manifest (Notes 7) and in the closure table
(`docs/2026-09-01_alloc-arc-plan.md`). No bridge to `RelSemCore` is
claimed; a future type layer claiming it must prove the bridge
first.

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
conditions are part of the claim (and — alloc arc P3 honesty note —
those conditions are OPERATIONAL drive equations: `sem_triple_prod`
is the last generic face of the cold-start prefix technique P2
retired from the exhibits, has no consumer since P2, and is a
retirement candidate for the P5 scaffolding pass; the allocating
exports reach the pipeline through `wpt_driver_done_alloc` →
`prod_run_eqJ` instead). `sem_triple_prod` and
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
Each qualifier is registered
at source (module headers; `docs/2026-08-30_spike-report.md`); this
section, under the manifest, is the summary the claims above are
read under.

## Registered divergences and seams

Acceptable qualifiers are clear, known divergences with retirement
or growth paths. The register (each entry's home is authoritative):

| Divergence / seam | Discharge / path | Registered at |
|---|---|---|
| ~~`runEffectful` in the production-entry statement cones~~ RETIRED 2026-09-02 (alloc arc P7): the semantics pin moved to the cerberus-lean effect-retirement head; the production theorems quantify over the supply-threaded entry's supply and are trio-exact | — (closed; `docs/2026-09-02_repin-notes.md`) | `Audit.lean` header |
| The tag-definition environment is an explicit parameter of the heap predicates and rules (`pointsToCell tds …`, `M.tagDefs` in the rules); the demos state their footprints at the program's environment `fmapEmpty`, which is what the shipped `drive fmapEmpty` passes | By design ([AGENT 2026-09-02], DECISIONS.md: the environment is a program-wide constant of the language instance, as Caesium's global environment); struct/union layouts become expressible without restatement | `Heap.lean` header; `docs/2026-09-02_repin-notes.md` |
| tagDefs argument: the theorems pin `drive`'s tagDefs to `fmapEmpty`; the shipped `Main.lean:871` passes `CerbTags.tagDefs ()` after `setTagDefsIO` | Semantically forced equal for the synthetic file: `(prodFile e).tagDefs = fmapEmpty` by `rfl`; the effectful set-then-read global is inert here (scalar layout paths provably never read it; struct/union paths would) | This table + `docs/2026-08-30_spike-report.md` register |
| Memory orders accepted arbitrarily: `Step.store`/`wp_store` hold at ANY `memory_order` | Mirror-true: the sequential driver drops `mo` (`action_request_sequential2`, Driver.lean:273 — `mo1` unused); NA-only side conditions would be a divergence FROM the engine | This table + `docs/2026-08-30_spike-report.md` register |
| Allocation rules + launch REPAIRED (alloc arc P1), partial-lane whole-program consumer LANDED (P2 items 1-2): the public `wps_create`/`wpt_create` (existential pointer, `allocCap` capacity, cursor-free statements, pure address-bounds export) are launchable via the allocation-aware launchers (`launchResources` under `LaunchCoh`), with local consumers, the engine-facing smoke `alloc_create_launch_smoke` (AllocExhibit), and the struct client `struct_create_store_wps`/`struct_create_store_adequacy` (StructExhibit — public rule + engine-facing adequacy through `spike_engine_adequacy_alloc`); and — alloc arc P2 — the whole-program production consumers (`progAProd_wpt`/`ctrProd_wpt`/`lrProd_wpt` through `wpt_driver_done_alloc`); R-01's closure test PASSED (deleting the public rule breaks the struct/two-create consumers; deleting `wpt_create` breaks the create/store/load and both loop production chains; deleting `launchResources` breaks the launch family — plant transcripts in `docs/2026-09-01_p2-notes.md`) | — (CLOSED; the closure table records the transcripts: `docs/2026-09-01_alloc-arc-plan.md`) | `Wps.lean`/`Wpt.lean` §CreateRule headers; `docs/2026-09-01_p1-notes.md` + `docs/2026-09-01_p2-notes.md`; 2026-09-01 skeptical re-audit R-01 |
| ~~R-02 (allocating exhibits bypass the separation logic)~~ CLOSED at alloc arc P2: all three allocating production exports are whole-program logic proofs (the programs bind their created pointers; creates cross the PUBLIC `wpt_create`; the generic `wpt_driver_done_alloc` → `prod_run_eqJ` collapse supplies every pipeline arrow); every handwritten `Step.*`/`engineSteps_*`/`driverDone_step` proof chain is DELETED from the positive exhibits (grep transcript + closure-test plants: `docs/2026-09-01_p2-notes.md`; closure table: `docs/2026-09-01_alloc-arc-plan.md`) | — (closed; the dependency-certified manifest upgrade is P3, R-04) | `ProdLoopExhibit.lean`/`ProdExhibit.lean` headers; 2026-09-01 skeptical re-audit R-02 |
| ~~R-04 (the capability gate validated declarations, not use)~~ CLOSED at speedbump level by [USER 2026-09-02] ruling: the manifest is a claim-point report (rows derived from `Frag`; one rule per construct; the rule must lie in some exhibit's proof cone — the one check that caught real overclaims); the adversarial-grade dependency-certification and layer-cut checks of alloc arc P3 were cut in P3.5 (the P3 plant transcripts remain history: `docs/2026-09-01_p3-notes.md`) | — (closed; closure table `docs/2026-09-01_alloc-arc-plan.md`; P3.5 record `docs/2026-09-02_p3.5-notes.md`) | `scripts/capability_manifest.lean` header |
| R-03 (the Cerberus relation a bespoke one-sided projection): the engine-round relation is NAMED (`CerberusRound`, Round.lean) and `cerberusRound_classify` is the exhaustive per-configuration classification over the whole `Frag` cone with the two-sided step arm (`step_iff_cerberusRound`); the manifest's engine-match column is derived from it; RESIDUAL: the refusal arm is classified two-sidedly for store/load/create/case only — the remaining rows' refusal channels are `failwithI` panics (opaque constants: a kernel classification is impossible, not merely unproved), save's EVAL round on non-value params, and the memop ND fork | Per-row refusal theorems where a non-panic channel exists (context rows: refusal propagation through `Decomp`; save: an EVAL-round arm); the panic channels stay one-sided by construction unless the semantics repo replaces `failwithI` with a value-level error | manifest Notes 7 + machine lines RELATION-REFUSAL-TWO-SIDED / -ONE-SIDED; `Round.lean` header; closure table |
| `Ewseq` at spec/sym binder patterns outside the fragment (the WILDCARD lane exported in S1b as the drift test); `Ecase`'s EVAL arm (non-value scrutinees) unmirrored | Mechanical per-construct extension, path named | `Step.lean` header; `docs/2026-08-30_spike-report.md` "Honestly open" |
| PURE exits certified at `PEsym` shape only (general `PePure` exits are a bounded matcher extension) | Extend `stepDischarge_pure_sym` per-constructor when needed | `Soundness.lean`; `docs/2026-08-31_phase2-s4-notes.md` |
| The array exhibit's pre-state is ONE allocation (not a ∗-of-per-element-cells): the engine's loads bounds-check against the pointer's PROVENANCE allocation and `arrayShiftPtrval` preserves provenance, so distinct-allocation "arrays" are not walkable in the engine — C's object model | Forcing fact about Cerberus, recorded; per-element structure lives in the index-partitioned invariant + decode premises | `ArrayExhibit.lean` header; `docs/2026-08-31_phase2-s4-notes.md` |
| The pointer-test memop coverage is `PtrEq` only; the family (PtrNe/Lt/…) and eqPtrval's differing-provenance ND fork are fail-closed ABSENCES of a mirror step (the fork is a real `msum`, CerbMem.lean:1753 — enumerated by the exhaustive runners, not single-layer) | Mechanical per-memop extension (dischargeStep arm + Step rule + wps axiom) | `Soundness.lean` dischargeStep memop arm; `docs/2026-08-31_listrev-notes.md` |
| The plain-symbol binder beta is mirrored at BARE values only (`Step.sseq_sym_pure`; no LETS-ANNOT variant) | The fragment's only sym-binder producer is the memop protocol, which delivers bare values (step_ctx's MEMOP continuation — `mk_pure_e`, no Eannot residue); the annot variant is a mechanical extension | `Step.lean` (the rule's docstring); `docs/2026-08-31_listrev-notes.md` |
| List-reverse TOTAL export: RETIRED (foundations Phase 3) — `list_reverse_certified_total` delivers the unconditional bound through the total judgment (the heap-resident variant rides the variant-indexed invariant); the DERIVED bound is `13·|ns| + 7` (the old 11-per-iteration note undercounted the wrapper-merge step; the true engine cost is 12 per iteration plus one unit of budget-reservation slack, documented at `lrCost`) | Closed by `docs/2026-09-01_phase3-notes.md` | `ListRevExhibit.lean` §total lane |
| Fuel side condition (no fuel parametricity) | Fuel-irrelevance theorem for `get_ctx` or graceful driver exhaustion would remove it | `docs/2026-08-30_spike-report.md` "What remains"; `ProdEntry.lean` header |
| REMOVE-ANNOT value protocol; canonical-annotation subrelation | Deliberate, engine-faithful readout composition | `Step.lean` header; `docs/2026-08-30_spike-sliceA-notes.md` D1/D3 |

### Deferred design experiments

- **Parametric semantics interfaces** — `docs/2026-09-02_parametric-semantics-spike.md`.
  EXPERIMENT, DEFERRED possibly permanently ([USER 2026-09-02], DECISIONS.md):
  a measured inventory of what each rule proof depends on in `Step`/the
  memory state, and a draft memory/environment/control interface. Not
  adopted: with one instance the interface relocates the same proofs
  behind a class, and RefinedC itself proves memory rules by inversion.
  The rules here are proved directly against `Step` and `CerbMem.MemState`.
  Re-open only for a second memory-model instance or a type layer that
  needs an abstract memory contract. The inventory script
  `scripts/parametric_inventory.lean` remains an on-demand instrument.

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
theorem in the package by the classical trio, (2) pins the public
exports' exact cones, and (3) checks every constant of
every kind — defs included — for the banned axioms
(`sorryAx`/`ofReduceBool`/`ofReduceNat`). It certifies nothing
beyond that: in particular it does not discharge the scope
qualifiers above — they are part of the theorem statements. Expected
tail:

```
info: CerberusHeapLang/Audit.lean:122:0: CerberusHeapLang export pins: 62 trio-exact
info: CerberusHeapLang/Audit.lean:122:0: CerberusHeapLang axiom sweep: 1115 theorems bounded by the trio
info: CerberusHeapLang/Audit.lean:122:0: CerberusHeapLang banned-axiom sweep: 1948 constants of every kind checked; sorryAx/ofReduceBool/ofReduceNat absent from all cones
Build completed successfully (441 jobs).
```

(`../scripts/capped` is the cgroup-direct cap; an `UNCAPPED` warning
means a broken environment — stop. The old note that sandboxes may run uncapped is retired; the cap is a resource-limit wrapper with no
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
'CerberusHeapLang.exhibitA_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.counter_loop_certified_registration' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Expected: everything reports exactly
`[propext, Classical.choice, Quot.sound]` — the production-entry
statements included (since the 2026-09-02 retirement re-pin).
`sorryAx` appearing anywhere is a failure.

The [walkthrough](docs/WALKTHROUGH.md) §5 reads the three headline
statements identifier by identifier, binning every constant into
engine / spec-idiom / Iris / Lean-core (the statement surfaces of
the pinned exports are also recorded in the committed signature
snapshots under `docs/`; `scripts/signature_snapshot.lean` is the
on-demand instrument). For per-construct coverage, regenerate the
[capability manifest](docs/CAPABILITY_MANIFEST.md)
(`scripts/capability_manifest.lean`) and diff it against the
committed copy — `scripts/test_unit.sh` does exactly that as its
speedbump.

## The modules

In teaching order (= import order; one line each — the
[walkthrough](docs/WALKTHROUGH.md) §7 has the guided version):

| Module | Contents | Headline |
|--------|----------|----------|
| `Step.lean` | The fragment's mirror small-step over the ENGINE's generated AST/state types (values, `store`/`load`/`create`, the `PtrEq` memop, strong sequencing at wildcard, `Specified`-binder and plain-symbol-binder patterns, `Esave`/`Eif`, value-scrutinee `Ecase`, the global context-discarding `Erun`, pure/operand evaluation, the annotation residue; the runtime tuple carries the live env stack and the per-procedure label map) — hand-written, zero authority until certified | `Step` |
| `Heap.lean` | Points-to over the engine's memory state via iris-lean GenHeap on the SPLIT carrier (per-byte heap, per-allocation metadata heap, allocator cursor); THE THREE ALLOCATION FACTS (alloc arc P4.1): fractional/linear bytes (`bytesOwn_append`, `bytesOwn_fractional`, `bytesOwn_agree`), PERSISTENT allocation knowledge (`allocMeta`/`locInBounds`, `pointsToView_persist`, `pointsToView_locInBounds`), no liveness token (metadata immutable — header); the typed-view algebra (`pointsToView_split`/`join`/`fractional`/`agree`), the points-to laws (`pointsToCell_fractional`/`agree`/`combine`), the provenance-preserving shift `cellPtr_arrayShift`; the memM-level store/load facts | `pointsToCell` (`↦c`), `pointsToView`, `allocMeta`, `pointsToCell_combine`, `storeM_success`, `loadM_success` |
| `Lang.lean` | The iris-lean `Language` instance over Step (primStep over the runtime tuple, componentwise value protocol, pure-determinism facts for the beta/merge taus, the `SpikeGF` ghost-functor witness). Deliberately NO `Language.Context`/wp_bind instance: the global jump rule falsifies the frame law (`Erun` discards its context), so sequencing is proved directly (`wp_sseq`, `wps_seq`) — the module header records the falsification | `instance : Language CoreRt Mem Empty CoreRVal` |
| `EnvLaws.lean` | The env-map seam, closed: lawfulness of the engine's symbol order (`Std.TransCmp` via the String×Nat lexicographic characterization) and the lookup-after-add law over reachable frames — loop invariants carry `SymFrame` instead of frame-shape pins | `envAdd_lookup` |
| `Rules.lean` | The base logic: small axioms, sequencing, frame, consequence, wand — plus the compositional two-store triple | `wp_store`, `wp_load`, `wp_sseq`, `triple_frame`, `triple_seq` |
| `Wps.lean` | The statement-stratified WP (the classical label-context judgment as a package-local guarded fixpoint): value/jump/step clauses, the jump-aware sequencing rules, the branch/entry rules, the small axioms at the stratum, THE GENERIC TYPED-SUBRANGE RULES (`wps_load_at`/`wps_store_at` over views + the derived whole-cell interior forms — Phase 2, F-04 retired), THE ALLOCATION RULES (the PUBLIC `wps_create` over the abstract capacity `allocCap` — existential pointer, cursor-free statement, launchable through the allocation-aware launchers; the exact-cursor `wps_create_cursor_internal` is heap-implementation-only — alloc arc P1), the per-label invariant loop rule `blockSpecs_intro` (partial correctness; the retired `blockSpecs_intro_variant` is replaced by the TOTAL stratum's `blockSpecsT`, Wpt.lean), STATEMENT-LEVEL FRAMING (alloc arc P4.2: `frameLs`, `wps_frame_labels`, `blockSpecs_frame`, the whole-loop frame rule `wps_sound_frame` — the frame crosses every back edge through the framed label context), postcondition-modality absorption `wps_fupd`, and the Löb-tied collapse into the base WP | `wps`, `wps_seq`, `wps_seq_spec`, `wps_load_at`, `wps_store_at`, `wps_create`, `blockSpecs_intro`, `wps_frame_labels`, `wps_sound` |
| `Wpt.lean` | THE TOTAL STATEMENT JUDGMENT (foundations Phase 3, audit F-02): `wpt M Ls k Ψ e ρ` by structural recursion on the step budget — variant-indexed label preconditions (`LabelSpecT`), MANDATORY back-edge decrease in the jump clause, the total rule set (sequencing/branch/entry/memory, plus — alloc arc P1 — the PUBLIC total allocation rule `wpt_create` over `allocCap` at the derived cost bound 2, with its internal exact-cursor form), `blockSpecsT` (replacing the retired variant lemma), statement-level framing at the total stratum (`frameLsT`, `wpt_frame_labels`, `blockSpecsT_frame`, `wpt_frame` — alloc arc P4.2), and the collapse into the pinned Iris TotalWeakestPre | `wpt`, `wpt_run`, `wpt_seq`, `wpt_create`, `blockSpecsT`, `wpt_frame_labels`, `wpt_sound` |
| `Soundness.lean` | Per-construct certification of Step against the engine's own `step_ctx` + request discharge (context-undisturbed shape; refusals classified; the evaluator bridge, the factor theorem with the jump disjunct, the context-discard certification, and the UNIFIED step-match over the whole cone at any MachineCtx) | `engine_complete`, `stepDischarge_run`, `Decomp.step_factor`, `engine_step_matchU` |
| `Adequacy.lean` | The exported semantic face over engine configurations: triples with an arbitrary framed rest, driven by the engine's step function — `SemTripleU` at ANY machine context and entry environment (alloc arc P4.3), `SemTriple` its fixed-profile instance (`SemTriple_iff_U`); THE PROJECTION ([USER 2026-09-02]): `MemTripleU` (the boring triple with a memory postcondition, frame built in; `SemTripleU` is its cells-shaped instance, `SemTripleU_iff_Mem`), `project_triple` (any Iris triple with a concrete-map pre and an arbitrary Iris post projects to the `MemTripleU` whose post is every pure consequence of the post at the final memory) and the pure-consequence lemmas `*_consequence` that discharge that post — `semantic_triple_soundU` and every exhibit readout are their instances; the PUBLIC single-cell readouts `cellOwn_readout`/`pointsToCell_readout` (clients never open the state interpretation); the jump-profile drive lane (`driveJ`) with its adequacy and per-step drive equations; alloc arc P1: `LaunchCoh` (footprint coherence + allocator health + plan fit) and the ONE shared allocation-aware launch `launchResources` (cursor key 0 minted NONEMPTY, `allocCap` granted), with the allocation-aware step launcher | `project_triple`, `semantic_triple_soundU`, `semantic_frameU`, `semantic_triple_sound`, `semantic_frame`, `spike_engine_adequacy`, `engine_adequacyJ`, `driveJ_step`, `launchResources`, `spike_step_adequacy_alloc` |
| `TotalAdequacy.lean` | The two halves of total correctness, separated per the audit: TERMINATION over the unified relation (Iris `twp_total` consumed as-is) and THE GENERIC MEASURE→DRIVE-FUEL SIMULATION (the judgment's budget IS driveJ fuel — unconditional `.done` equations), on the step-monotone size potential `pot` (static fuel honesty, no run-length coupling) and the state-inert cone (final-state pins for action-free programs); alloc arc P1: allocation-aware variants of all three total launchers through `launchResources` | `wpt_strongly_normalizing`, `wpt_engine_boundJ`, `wpt_engine_boundU_alloc`, `Frag.pot_step_bound` |
| `API.lean` | THE PUBLIC SURFACE as one import (alloc arc P5, R-07): a client — an exhibit today, a type interpretation tomorrow — imports this module alone. Its header is the public/internal table: PUBLIC are the pointer/location assertions and their laws, the side-condition vocabulary, the environment seam, the base logic, both statement judgments with their full rule sets (framing, fractional/agreement laws included), and the adequacy exports; INTERNAL (visible — Lean imports are transitive — but not part of the surface, with the reason why) are `CohG` and the ghost carrier, the allocator cursor, `Step`/Soundness/Round, the judgment unfoldings and the memM seams. Not imported: the production-export modules, the exhibits, `Examples.*`. The import direction (semantics → heap → rules → adequacy → clients) is a grep speedbump in `scripts/test_unit.sh` | the header table |
| `Examples/Layout.lean` | EXAMPLE SUPPORT, not logic (alloc arc P5, R-07): the concrete layout constants the exhibits share — `intTy`, the 5/6/7 values with their memory values, byte images, encoding and storability facts — and the canned exhibit-shape lemmas (`exhibit`, `exhibitC_triple`, `wps_exhibit_store_frame`, `wps_exhibit_seq_stores`) formerly at the tails of `Rules.lean`/`Wps.lean`; statement-preserving moves (the P5 snapshot diff is empty at these names). Rule modules now contain rules and their supporting lemmas only | `intTy`, `sevenBytes`, `exhibit`, `exhibitC_triple` |
| `Examples/ReadinessSmoke.lean` | THE READINESS SMOKE TEST (alloc arc P5, charter item 5): imports ONLY `API`; defines the two-field object predicate `twoField tds p xb yb` (one `long[2]` allocation, the fields its two typed sub-range views) and DERIVES its load, store and allocate rules from the public rules alone — `wps_load_at`/`wps_store_at` at offsets 0 and 8 (the y field addressed by the engine's own `arrayShiftPtrval`, through `cellPtr_arrayShift`), `wps_create` + `cellOwn_view` + one `pointsToView_split` for allocation. Byte-image indexed, decode/storability premises as in the raw rules; NOT a RefinedC-style type record, no subtyping, no automation. Measured at zero direct references to the ghost maps/`CohG`/cursor/`Step`/judgment unfoldings (`scripts/parametric_inventory.lean`) | `twoField`, `twoField_load_x`, `twoField_load_y`, `twoField_store_x`, `twoField_store_y`, `twoField_create` |
| `Exhibit.lean` | End-to-end exhibits at the engine level: store-then-load returns 7; the frame exhibit; disjoint sequential stores; termination-with-delivery via the GENERIC total route (alloc arc P2: the example-specific six-step trace `exhibitA_terminates` retired for `progA_wpt` + `wpt_engine_boundU`) | `exhibitA_engine`, `exhibitB_engine`, `exhibitC_engine`, `exhibitA_total` |
| `LoopExhibit.lean` | THE FIRST LOOP: the counter loop — save entry, real `x > 0` guard, a store under the loop, the context-discarding back edge — certified end-to-end through `driveJ` with a data-dependent post; the invariant carries `SymFrame` (the former exact-shape pin `IsXFrame` is gone — alloc arc P4.3), and the irrelevant-binding tests run it from an entry frame with an unrelated binding | `counter_loop_certified`, `counter_loop_certified_irrelevant_binding` |
| `FibExhibit.lean` | Iterative two-accumulator fib with the data-dependent invariant `a = fib i ∧ b = fib (i+1)`; partial via `engine_adequacyJ`; TOTAL via the total judgment (Phase 3): `fib_certified_total` — the unconditional driveJ equation at step bound `2·n+4`, state verbatim — as a corollary of the generic simulation (zero Step constructors), plus `fib_terminates` (strong normalization via Iris TotalAdequacy) | `fib_certified`, `fib_certified_total`, `fib_terminates` |
| `DivergeExhibit.lean` | THE NEGATIVE TEST of the total lane: the self-jump loop steps to itself, is not strongly normalizing, and any total derivation for it is FALSE — the mandatory decrease is exactly what blocks it (the module header records the stuck obligation) | `diverge_total_unprovable` |
| `ArrayExhibit.lean` | The array-sum walk — real pointer arithmetic, operand-evaluated loads, interior reads of the seeded array allocation, the `Specified`-binder unwrap, the index-partitioned invariant; the array preserved in the conclusion | `array_sum_certified` |
| `StructExhibit.lean` | THE FRESH-CLIENT TEST (Phase 2 acceptance): a two-field struct update (layout `{int x @ 0; int y @ 8}` in one 16-byte allocation — a third distinct layout) verified end-to-end with ZERO core-logic edits — every rule a one-line client instance of the generic subrange rules; THE VIEW AND FRACTION CLIENTS (alloc arc P4.1, R-06): the same update through disjoint typed field views — split, store through each view, rejoin (`struct_wps_views`); a fractional read preserving its fraction; the shared reader (`pointsToView_fractional`); two readers of one pointer recombined by agreement (`pointsToCell_combine`); read-then-persist the metadata for the bounds fact (`struct_x_read_persist_wps`); plus the allocation CLIENT (alloc arc P2 items 1-2: `lets p = create(align, struct) in ... store through p` proved from `allocCap` through the PUBLIC `wps_create` — the program binds the fresh pointer, no cursor vocabulary — and exported to the engine from the production cold-start memory through `spike_engine_adequacy_alloc`) | `struct_update_certified`, `struct_wps_views`, `cell_read_shared_wps`, `struct_create_store_wps`, `struct_create_store_adequacy` |
| `AllocExhibit.lean` | THE PUBLIC ALLOCATION RULES' LOCAL CONSUMERS + THE LAUNCHER SMOKE (alloc arc P1.4): two creates consume a two-element plan IN ORDER (partial lane), one create at the derived minimal budget 2 (total lane), and the chain-closing engine smoke — a bare create from the production cold-start memory, proved ONLY through the public `wpt_create` and launched ONLY through `wpt_engine_boundU_alloc`, delivering a pointer at `driveU` fuel exactly 2; NO operational proof terms in this module | `alloc_two_creates_wps`, `alloc_create_wpt`, `alloc_create_launch_smoke` |
| `ListRevExhibit.lean` | THE CANONICAL EXHIBIT AT FULL STRENGTH (Phase 4): in-place reversal of a linked list of one-allocation two-field nodes — the honest null encoding + the engine's own `PtrEq` memop as the null test (the null/pointer byte ROUND TRIPS proved against repr/abst), interior next-field loads AND stores by in-allocation arithmetic, IDENTITY-INDEXED `isList` by plain structural recursion (allocation id × value per node), the textbook `blockSpecs_intro` proof with the UNFRAMED invariant `isList prev reversed ∗ isList cur rest` (the arbitrary frame added by the generic statement frame rule — `lr_wps_frame`/`lr_wpt_frame`, alloc arc P4.2); conclusion: same-footprint in-place reversal (`SeedChain Q p' ns.reverse` + the literal footprint-equality conjunct) with an arbitrary disjoint frame returned verbatim; the TOTAL lane: the same textbook derivation at the total judgment yields the unconditional equation at the derived bound `13·|ns|+7` plus termination | `list_reverse_certified`, `list_reverse_demo`, `list_reverse_certified_total`, `list_reverse_terminates` |
| `TreeRotExhibit.lean` | THE SECOND CLIENT (Phase 4 — the accident-detector): binary-tree right rotation over one-allocation three-field nodes (value + two child pointers; the splice-ABOVE slice law's first consumer), identity-indexed `isTree`/`SeedTree` with BRANCHING recursion, certified end-to-end with ZERO core-logic edits at the flagship statement shape (same allocations — the rotated id list a permutation of the original — footprint equality, frame verbatim), partial + unconditional total (constant budget 19) | `tree_rotate_certified`, `tree_rotate_certified_total` |
| `DriverCollapse.lean` | The production scheduler/ND/readout collapsed onto the demo's drive loop — proved from the driver's OWN round functions; Phase 5 extends the round algebra to proc-carrying, populated-label threads (with-runstate and memop rounds; the per-redex driver step-match `loop_step_frag` over the full cone); bounded by the trio | `prod_loop_done`, `driver2_done`, `finalize_done`, `loop_step_frag` |
| `ProdEntry.lean` | Cold start from the SHIPPED `initial_driver_state` (errno allocated by the real allocator) + the production-entry theorem; the REGISTRATION TIE — `LabeledAt` derived from the shipped `collect_labeled_continuations_NEW` for the authored loop programs, and the counter loop re-exported at the derived tie (the registration theorem — manifest Notes 3) | `sem_triple_prod`, `prod_run_eq`, `fib_labeledAt_production`, `counter_loop_certified_registration` |
| `ProdLoop.lean` | Phase 5: the total statement judgment drives the PRODUCTION DRIVER'S OWN LOOP — the driver-level analog of the measure→drive-fuel simulation (one production round per budget unit, jump rounds included), trio-only | `wpt_driver_done` |
| `ProdLoopExhibit.lean` | THE PRODUCTION LOOP EQUATIONS — loop programs certified as `CerbND.runND (Driver.drive …) (initial_driver_state …)` equations from the cold start (no package drive/driveJ in any statement); the counter and reversal programs are SELF-CONTAINED WHOLE-PROGRAM LOGIC PROOFS (alloc arc P2: the programs bind their engine-created pointers; creates through the PUBLIC `wpt_create`; the reversal consumes the generic list logic verbatim at existential engine-picked ids) | `ctrProd_wpt`, `lrProd_wpt`, `fib_certified_production`, `counter_loop_certified_production`, `list_reverse_certified_production` |
| `ProdExhibit.lean` | The demonstration: a self-contained program (create/store/load — the fresh pointer BOUND by the program) run through the production pipeline delivers 7 at the program's own cell — ONE whole-program total judgment through the PUBLIC create rule and the generic driver collapse (R-02 conversion, P2 step 3) | `progAProd_wpt`, `exhibitA_prod` |
| `Audit.lean` | The in-build axiom gate: exact axiom-set pins over the public exports (the classical trio, every one) + the exhaustive theorem sweep bounded by the trio + the banned-axiom sweep over every constant kind | the sweeps |

History and design findings: the dated records in `docs/`
(`2026-08-30_spike-report.md` is the founding report; plans,
reviews and slice notes alongside).

---

Built by AI agents (Claude, Anthropic) under the direction and
review of Mike Dodds.
