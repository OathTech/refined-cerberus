# Re-review of the cerberus-heaplang detailed-audit response

Date: 2026-09-02

Reviewed revision: b34998d8d037d75f48d18cfa42a7301f59ef3be5

Original audit revision: d50e776175d89ca8bfddac2fa6b6f62ce7ad8cc9

Cerberus Lean pin: ddcfc919972a31bc43a0454e6b2e76a19e6c4594

Iris Lean pin: 34390a0133986385c62bf59a6eb01938945b48ec

This is a source-level and build-level re-review of the changes made in
response to docs/2026-09-02_cerberus-heaplang-detailed-audit.md. It asks
whether the response actually closes the earlier findings, rather than merely
whether the response document says that it does.

## Executive verdict

**The response is substantive and mostly successful.** Under the project's
now-explicit policy that the generated Cerberus Lean engine is the semantic
authority, cerberus-heaplang is a legitimate Reynolds/O'Hearn-style separation
logic implemented using Iris for its stated fragment. Its ordinary program
proofs are relational and logical: Iris is instantiated over the inductive
relation Step, heap ownership is represented by genuine spatial resources,
and positive clients use the public wps/wpt rules rather than unfolding the
executable engine. The connection from a logical step to an actual Cerberus
engine round is kernel proved.

The important qualification remains that this is a **sound, deliberately
incomplete logic for a restricted mirror**, not a complete characterization
of all engine behavior on Frag, much less of all Cerberus Core. This is now
stated plainly. Completeness is not required for the safety of the current
Iris adequacy argument: NotStuck supplies a mirror step at every reachable
non-value configuration, and the forward theorem identifies that step with
the engine's singleton successful round. It does, however, remain an open
coverage obligation when the fragment grows.

The other substantive semantic limitation also remains: the generic partial
and total adequacy/projection theorems conclude facts about package-defined
driveU, not the shipped driver. The response now labels all of those exports
**PROVISIONAL**, identifies the closed total production examples as the only
current shipped-driver lane, and requests the required transparent
fuel-exhaustion outcome upstream. That is an honest accounting of the gap,
not a technical closure of it.

I found no new proof hole in the package and no evidence that the examples'
accidental constants or layouts have entered the core logic. The repaired
audit catches internal-detail sorryAx dependencies, the public/internal table
is now internally coherent, and direct Step witnesses were removed from the
positive production exhibit. The new normative architecture document is a
major improvement.

There are four low-severity documentation/reproducibility defects in the
response. Most importantly, some sentences in the normative document
overstate how directly every export mentions the engine; the fixed numeric
audit transcript does not reproduce at the reviewed revision; and the known
sorry in the pinned generated concurrency model is not mentioned in the
normative trust documents. These do not invalidate the current theorem cones,
but should be corrected before calling the documentation settled.

### Answers to the three audit questions

| Question | Re-review verdict |
|---|---|
| Does this legitimately realize Reynolds/O'Hearn separation logic with Iris and connect it to Cerberus Lean? | **Yes, with explicit scope.** It is a genuine Iris separation logic over a package-authored relational mirror, with a proved forward connection to successful engine rounds. Closed total demos reach the shipped driver. Generic shipped-driver adequacy and mirror completeness remain open. |
| Are trust gaps hidden or inappropriately accepted? | **No unaccounted package-cone proof gap found.** The classical trio, generated-semantics trust, forward-only mirror, driveU lane, and footprint-relative allocation premise are now disclosed. The pinned out-of-cone concurrency sorry should be elevated into the normative trust story. |
| Is the documentation adequate? | **Substantially yes, after this response.** ARCHITECTURE.md supplies the missing entry point and the API boundary is much clearer. A few overbroad or non-reproducible statements still need repair. |

## Scope and verification performed

I reviewed the complete diff from d50e776 to b34998d, including:

- the new cerberus-heaplang/ARCHITECTURE.md and revised README,
  walkthrough, module headers, decision record, and response record;
- the actual definitions and theorems in Lang.lean, Round.lean,
  Adequacy.lean, TotalAdequacy.lean, ProdEntry.lean, and the production
  exhibits;
- the public/internal classification in API.lean;
- the revised exhaustive and banned-axiom sweeps in Audit.lean;
- the moved direct-step witnesses in Examples/MirrorCoverage.lean and the
  retained negative-test exception in DivergeExhibit.lean; and
- the pinned generated Cmm_op.lean declaration that Lean reports as using
  sorry.

The proof and theorem-statement layer was intentionally frozen by the response
except for relocating two existing mirror-coverage theorems and changing the
audit metaprogram. Inspection of the diff agrees with that characterization:
there is no hidden weakening of a semantic theorem.

I independently ran the full repository gate at the reviewed revision. The
first attempt was stopped before Lean by the enclosing nono OS sandbox when
the repository's cgroup wrapper tried to access the system bus. An approved
out-of-sandbox rerun completed successfully:

    ok: no banned proof-method references
    ok: root build green                       (370 jobs)
    ok: cerberus-heaplang build green          (446 jobs)
    ok: capability manifest regenerated, no drift
    ok: import direction — no core module imports an exhibit/example/production module
    ALL GATES GREEN

The heaplang audit reported 116 exact export pins, 2,210 swept theorems, and
3,474 swept constants. A second --fast run was also green and reproduced those
same three numbers. The discrepancy from the checked-in 2,249/3,536 transcript
is finding N-3 below.

I did not repeat the response team's destructive source mutation that planted
a private sorry. I inspected the new sweep and its recorded before/after
transcript. The implementation no longer calls Name.isInternalDetail, and the
recorded plant failed at the expected private theorem, so the test is credible
and consistent with the code.

## Disposition of the original findings

| Original finding | Status | Re-review |
|---|---|---|
| H-1: no adequate identification with a designated Cerberus relational semantics | **Claim repaired; technical coverage remains open** | The user explicitly designated the generated engine, not RelSem, as authoritative. The docs now state the exact forward-only theorem and do not claim completeness. This is sufficient for soundness, but mirror completeness and generic shipped-driver adequacy remain open. |
| M-1: allocation health is footprint-relative | **Documented, not technically closed** | The new prose accurately describes what LaunchCoh constrains and registers a global invariant for the malloc/free arc. No MemWF-style invariant was added. |
| M-2: public/internal API contradiction | **Closed** | allocCap_intro is now internal; CellCoh/Coh/Sat are explicitly public; the ghost-predicate leak in projection premises is named as a conventional exception. |
| L-1: audit skipped internal-detail declarations | **Closed** | Both sweeps now include internal details. The private-sorry regression recorded by the team demonstrates the old pass/new fail behavior. |
| L-2: positive exhibit modules used Step directly | **Closed** | The two coverage witnesses moved unchanged to a semantic-regression module. The only exhibit-level direct Step proof is the documented negative divergence test. |
| L-3: no short normative architecture document | **Substantially closed** | ARCHITECTURE.md provides a useful seven-section source of truth and the root README points to it. Findings N-1, N-2, and N-4 are remaining polish. |

## Detailed re-review

### H-1 — semantic authority and the Iris/Cerberus connection

Status: **Resolved as a trust-policy and claim-precision issue; two technical
limitations remain registered.**

The response does not manufacture a RelSem bridge. That is the right outcome
given the explicit decision that the executable generated engine is the
reference semantics and that the repository's spike-grade RelSem layer has no
independent authority. Requiring a bridge to a non-authoritative relation
would add another presentation without improving the trust argument.

The actual semantic chain remains:

    public Iris rules / wps / wpt
                |
                v
    Iris Language.primStep = package Step
                |
                | engine_step_matchU / Step.toCerberusRound
                v
    successful singleton discharged step_ctx round
                |
                +--> package driveU adequacy          [PROVISIONAL lane]
                |
                +--> total driver collapse for four closed demos
                     to runND (drive ...)             [shipped-driver lane]

Lang.lean:47-50 still instantiates primStep with the inductive Step.
Round.lean:104-105 defines CerberusRound as the graph of a singleton successful
outcomesU result. Step.toCerberusRound is a forward inclusion
(Round.lean:115-121). step_iff_cerberusRound still requires
hstep : ∃ c', Step ... (Round.lean:127-147), and the refused arm still contains
no engine fact (Round.lean:165-168). The classifier's negative branch is still
just a classical case split on the existence of Step (Round.lean:195-198).

The key improvement is that the architecture now says all of that directly
(ARCHITECTURE.md:22-51). It no longer invites a reader to mistake
cerberusRound_classify for an engine-completeness theorem. For partial
correctness, a forward simulation is a legitimate design: an incomplete
language relation makes the logic harder to apply, not unsound, provided
adequacy only follows mirror executions that have been proved not stuck. That
condition is exactly how the current Iris adequacy proof is organized.

Two limitations must remain prominent:

1. **Mirror completeness.** New fragment constructors need both positive
   correspondence and fail-closed refusal coverage. Otherwise a construct may
   work in the engine while being unprovable in the logic. That is a capability
   gap, not currently a theorem-validity gap.
2. **Generic shipped-driver adequacy.** MemTripleU, the projection theorems,
   and wpt_engine_boundU are still about driveU. The closed production
   theorems (exhibitA_prod and the three certified_production theorems)
   genuinely mention CerbND.runND applied to the shipped drive and have no
   termination hypothesis. They show that the logic supports nontrivial demos
   through the real runner. They do not yet provide a generic theorem taking
   an arbitrary proved public triple to a shipped-driver result. The upstream
   fuel-exhaustion request is therefore load-bearing, not cosmetic.

This leaves the project's best concise claim as the one now quoted in
ARCHITECTURE.md: a sound Iris program logic for a restricted relational
mirror, with a verified forward connection to successful Cerberus engine
rounds on proved-safe executions, plus several closed total examples at the
shipped runner.

### M-1 — global allocation well-formedness

Status: **Open, accurately documented.**

The response correctly states that LaunchCoh constrains tracked cells and
fresh ids above the cursor, not every live allocation in an arbitrary
MemState. The definition is unchanged: id_lt and addr_lo range over the
logical footprint, while fresh_alloc and fresh_dead range only over ids at or
above nextAllocId. There is still no global live-range-disjointness or
live/dead consistency invariant in the state interpretation.

That is acceptable for the current local create rule and for a demo that does
not support free: every owned cell is protected, and the production initial
state is concrete. It should not silently become the premise for malloc/free
or for claims about arbitrary reachable Cerberus memories. The registered plan
to introduce a persistent global invariant before that extension is the right
technical closure.

The response therefore closes the documentation defect but not the semantic
domain gap. This is not a blocker for the current examples; it remains a
blocker for a general allocation/free story.

### M-2 — public API boundary

Status: **Closed for a conventional Lean API.**

API.lean:62-88 now makes a consistent classification:

- allocCap and allocCap_weaken are public, while the launcher-side
  allocCap_intro, AllocCursor, and cursorOwn are internal;
- CellCoh, Coh/Sat, and the other pure readout vocabulary are public;
- CohG, metaInterp, and byteInterp remain internal but are named as a single
  documented exception where public projection/readout premises expose them;
  and
- clients are instructed to discharge those premises through public
  consequence lemmas rather than opening the ghost implementation.

Lean cannot enforce this visibility boundary, so it remains a documented
discipline. For a demo package this is adequate. A future stable library may
still want wrapper records that remove ghost predicates from public theorem
types, but the old contradiction is gone.

### L-1 — package-wide axiom sweep

Status: **Closed.**

The two loops at Audit.lean:225-254 no longer skip internal-detail names. They
select declarations by module of origin, bound every theorem by the classical
trio, and reject sorryAx, ofReduceBool, or ofReduceNat in the cone of every
package constant. The independently rerun build confirms that the widened
sweeps elaborate and that all 116 named exports remain exactly on the
classical trio.

The exact-export list remains manual and the import-direction/capability
checks remain speedbumps, as documented. Neither is a hidden kernel-trust
claim.

### L-2 — operational reasoning in examples

Status: **Closed.**

ProdExhibit.lean no longer contains a direct Step derivation. Its mixed
store-shape witnesses moved to Examples/MirrorCoverage.lean, whose header
correctly calls them semantic regression tests rather than client proofs. The
production proof itself continues through wpt_create, generic heap rules,
total adequacy, and the driver collapse.

The remaining Step.run use in DivergeExhibit.lean is narrow and justified: it
establishes the actual self-step needed to refute a total derivation. It is a
negative metatheoretic test, not a positive proof that bypasses the logic. No
core semantics/heap/rules/adequacy module imports an example or production
module, and the gate checks that direction.

This directly addresses the original concern about baking the demos into the
logic. The core rules remain generic in machine context, environment, type,
location, value, memory order, footprint, and frame. The examples contribute
no constants to core definitions.

### L-3 — architecture and trust documentation

Status: **Substantially closed.**

The new ARCHITECTURE.md is the right entry document. It distinguishes the
engine, relational mirror, Iris judgments, adequacy, projection, shipped and
provisional lanes, and open items in about 150 lines. The root README points
to it. The revised API table and repeated PROVISIONAL labels make it much
harder to miss the actual trust boundary.

The remaining problems are the new findings below. They are local wording and
reproducibility issues, not a return to the former diffuse architecture story.

## New findings in the response

### N-1 — ARCHITECTURE.md overstates direct engine reference by exports

Severity: **Low documentation defect.**

ARCHITECTURE.md:15-17 says that “every exported theorem is a statement about
the engine's execution and memory states.” That is false literally and is
contradicted by the same document at lines 101-107: reusable assertion laws
and wps/wpt rules are statements in Iris over the package relation and ghost
resources. They are sound because their adequacy path reaches the engine, not
because each statement directly names engine execution.

Lines 109-116 similarly put prod_run_eqJ in a group for which “no package
definition appears in their statements except the authored programs and the
pure readout predicates.” prod_run_eqJ has a package-defined DriverDoneAt
premise (ProdEntry.lean:332-346), and the closed examples also mention the
package's synthetic prodFile wrapper. The closed examples do directly conclude
a shipped runND/drive equation, which is the important fact; the stronger
wording is unnecessary.

Recommended correction:

> Every exported execution theorem is either explicitly provisional over
> driveU or reaches the shipped engine; every public logical rule has a
> kernel-checked adequacy path through the package mirror to the engine.

Also describe prod_run_eqJ as generic collapse machinery with a
package-defined delivery premise, and reserve “closed shipped-driver
statement” for the four discharged production examples.

### N-2 — prodMem₀_launchCoh is not a global well-formedness theorem

Severity: **Low documentation defect; related technical work remains M-1.**

ARCHITECTURE.md:143-150, README.md:367, and walkthrough lines 792 onward say
that the production cold-start state is “globally well formed” and cite
prodMem₀_launchCoh. That theorem proves LaunchCoh for the empty footprint and
any fitting plan. LaunchCoh is the very footprint-relative predicate whose
lack of a global invariant is being documented, so that citation cannot by
itself support the stronger phrase.

The concrete state is not suspicious: prodMem₀_allocations proves that its
live allocation table contains only errno, and prodMem₀_deadAllocations proves
the dead table empty (ProdEntry.lean:207-215). Those facts support an informal
direct check of the cold state. But there is no defined global MemWF predicate
and no theorem stating all of the range-disjointness, live/dead, byte-range,
id, and cursor properties listed as future work.

Replace the phrase with a concrete claim such as “contains only the
allocator-created errno allocation and no dead allocations
(prodMem₀_allocations, prodMem₀_deadAllocations)”. Reserve “globally well
formed” for the future invariant and its initialization proof.

### N-3 — the checked-in audit-count transcript is not reproducible

Severity: **Low reproducibility/documentation defect.**

The README and response record state that the reviewed audit prints 2,249
theorems and 3,536 constants. A fresh full build at exactly b34998d printed
2,210 and 3,474; an immediately repeated fast gate printed the same lower
counts. Both runs retained 116 exact export pins and passed every axiom and
banned-dependency condition.

The numerical counts are informational, not acceptance thresholds, so this
does not create a proof hole. It does mean the README's “Expected tail” is not
currently an expected transcript. Either identify and pin the environmental
input that changes internal-declaration totals, or omit fixed totals and show
only the stable semantic verdicts. If the numbers are meant to be a drift
instrument, make them an asserted baseline rather than log text.

### N-4 — the known generated concurrency sorry belongs in the normative trust story

Severity: **Low for current theorem cones; potentially High for any future
whole-engine or concurrency claim.**

The pinned generated Cmm_op.lean:283-292 contains two terms of type String
filled by sorry in the debug-log branch of auxAddToRfLoad; Lean reports
“declaration uses sorry” during the build. The response records this in the
upstream fuel request and in DECISIONS.md, and the package sweep establishes
that sorryAx reaches no CerberusHeapLang constant. The current sequential logic
and its exported theorem cones are therefore unaffected.

However, neither ARCHITECTURE.md, the package README, nor the walkthrough's
trust section mentions it. The README says the semantics workspace and Lem
runtime declare no axiom; that is narrowly compatible with a generated use of
sorryAx, but a reader can reasonably understand it as a claim that the trusted
generated semantics is admission-free.

Add a short normative qualification: the pinned semantics tree contains this
known generated admission in an unused concurrency/debug declaration; it is
outside every current export cone; concurrency is out of scope; and the item
must be closed or separately bounded before any concurrency or whole-engine
claim.

## Trust assessment after the response

### Proof-theoretic trust

For the package's current exports, the story is strong:

- 116 selected exports have exactly propext, Classical.choice, and Quot.sound
  in their transitive axiom sets;
- every package theorem is bounded by that trio, including internal details;
- every package constant is checked for the banned admitted/reduction axioms;
- the source grep rejects the banned proof methods; and
- no project-defined boundary axiom is present.

The known generated concurrency sorry is outside those cones, which is why the
build can both warn about it and correctly pass the package audit. This is a
scoped theorem-cone guarantee, not proof that every declaration in the entire
semantics dependency is admission-free.

### Semantic trust

The generated Lean engine is trusted by explicit policy and is differentially
validated against OCaml Cerberus; no formal generator or Lean/OCaml equivalence
proof is claimed. Within that boundary, the mirror-to-engine forward theorem
is genuine. The incomplete refusal side limits coverage but does not introduce
an unsound extra engine behavior into a proved program.

The generic driveU lane should continue to be called provisional until it is
restated over the shipped driver. The closed production examples are useful
evidence of the intended endpoint, but example-specific endpoints are not a
replacement for generic adequacy.

### Scope and non-specialization

The current product is a demo separation logic over an annotation-free,
sequential Core fragment with explicit fuel/shape premises, authored Core in a
synthetic file, no free, no procedures, and no concurrency. Those are scope
limitations, not hidden assumptions.

I found no accidental coupling of core logic to the verified examples:

- the dependency direction remains semantics → heap → rules → adequacy →
  clients;
- the core modules do not import examples or production artifacts;
- positive examples use public logical rules;
- mirror-shape witnesses are isolated as semantic regression tests; and
- concrete symbols, values, layouts, and expected results remain in exhibit
  modules.

The selective Frag constructors are intentionally demo-sized and will need
coverage work as capabilities grow. They do not encode the particular list,
tree, fib, or store examples as semantic laws.

## Recommended next actions

1. Keep mirror completeness and the shipped-driver generic adequacy theorem as
   explicit open acceptance items; do not relabel the driveU lane before the
   upstream fuel outcome exists.
2. Add the global MemWF invariant before free or claims about arbitrary
   reachable allocated states.
3. Repair the four low-severity normative/reproducibility findings N-1 through
   N-4.
4. Preserve the current positive-client rule: examples prove programs through
   API, while direct Step reasoning lives only in semantic coverage or clearly
   marked negative metatheory.

## Final assessment

At b34998d, I would accept the project as an honest and technically real
**demo Iris separation logic for a restricted Cerberus Core mirror, soundly
connected to the generated engine on proved-safe executions**. I would also
accept the four closed total examples as genuine demonstrations reaching the
shipped driver.

I would not yet describe the package as a generic separation logic whose
adequacy theorem is stated over the shipped Cerberus driver, a complete logic
for all behaviors of its declared fragment, a globally well-formed allocator
model, or a logic for full Cerberus Core/C. The response now mostly says the
same thing. That alignment between code and claim is its most important
improvement.
