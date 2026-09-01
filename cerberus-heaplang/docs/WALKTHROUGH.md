# A walkthrough: separation logic over an executable C semantics

This is a guided tour of `cerberus-heaplang` for a reader who knows
separation logic and roughly what Iris is, and has never heard of
Cerberus. It answers four questions: what the object language is,
what a program looks like, what a Hoare triple *means* here (down to
the quantifier structure), and why you should believe any of it —
ending with commands you can run yourself in about five minutes.

Everything quoted below is real code from
[`CerberusHeapLang/`](../CerberusHeapLang/); file and line references
are to this checkout.

## 1. What this is

**Cerberus** is a semantics for C (Memarian, Sewell, et al.,
Cambridge): it elaborates C into a small typed functional
intermediate language called **Core**, and gives Core an executable
operational semantics — an interpreter with an explicit memory
object model (allocations, byte representations, pointer
**provenance** — the memory model's record of which allocation a
pointer is derived from, used to police pointer arithmetic and
comparisons the way the C standard does). The engine used here is a
Lean 4 port of that semantics: the same elaborator and interpreter,
mechanically translated, and *differentially validated* — the Lean
engine and the original OCaml implementation are run on the same
test programs and their behaviors compared, so the Lean semantics is
tied to an independently maintained oracle rather than being a
formalization that answers only to itself. (The pinned engine
version is in `../scripts/semantics-pin.env`; validation is that
project's, not this package's — what it covers, with the
in-package path to its record, is summarized in the README's
["What you are asked to take on
faith"](../README.md#what-you-are-asked-to-take-on-faith).)

**This package** builds a small Iris separation logic — points-to,
store/load small axioms, frame, sequencing, loop rules — over a
fragment of Core, and then *certifies every rule against the
executable engine*: the exported theorems are statements about the
engine's own step function and driver, in engine vocabulary, with
the logic appearing only in the proofs. The role model is Iris's
HeapLang (the demonstration language a program logic is exercised
on); the difference is that the object language here is not a
purpose-built toy but the intermediate language of a real C
semantics, executed by the real interpreter.

The headline exhibit is the canonical one from the
Reynolds/O'Hearn separation-logic tradition: **in-place linked-list
reversal**, specified with a structurally recursive,
identity-indexed `isList` predicate and proved with a loop
invariant of the textbook shape — then read back as a theorem about
the engine's execution stating the full classical claim:
same footprint (the same allocations, nothing allocated or
leaked), in-place relinking (each node keeps its own value),
an arbitrary disjoint frame preserved verbatim, and termination
(foundations Phase 4). A second, structurally different client —
binary-tree rotation — replays the same shape with zero core
edits.

## 2. What a program looks like

Core is a functional language with explicit sequencing of memory
*actions*. The exhibit program is in-place list reversal, written
directly in Core (`ListRevExhibit.lean`). In pretty-printed form:

```
save loop: (prev : ptr := NULL(node), cur : ptr := head) in
  lets b = memop(PtrEq, [cur, NULL(node)]) in
  if b then pure(prev)
  else
    lets Specified(n) = load(node*, array_shift(cur, long, 1)) in
    lets _ = store(node*, array_shift(cur, long, 1), prev) in
    run loop(cur, n)
```

Construct by construct:

- `save loop: (…) in body` — **block entry with labelled
  continuation**. `save` registers the label `loop`, binds its
  parameters (here `prev`, `cur` with their initial values), and
  runs the body. It is how the C-to-Core elaborator expresses loop
  heads and `goto` targets.
- `run loop(cur, n)` — **the jump**. `run` *discards its evaluation
  context* and restarts the registered continuation with new
  parameter values: the loop's back edge. In the engine, registered
  continuations live in a per-procedure label map
  (`labeled_continuations`).
- `lets pat = e1 in e2` — sequencing (Core's `Esseq`), binding the
  result of `e1` by pattern. Three patterns appear: a plain symbol
  (`b`), a wildcard (`_`), and `Specified(n)` — loads in Core return
  `Specified(v)` or `Unspecified` (C's uninitialized-read
  channel), and the pattern unwraps the specified case.
- `store(τ, p, v)` / `load(τ, p)` — the memory **actions**. They go
  through the engine's memory model (`storeM`/`loadM`): liveness,
  bounds, writability and type checks, byte-level serialization.
  A failed check is undefined behavior, and the engine *kills* the
  execution — the logic's job is to prove that cannot happen.
- `memop(PtrEq, [p, q])` — a memory-model operation: pointer
  equality as the *memory model* defines it (provenance-aware).
  This is the null test — no boolean flags smuggled in from
  outside; the program tests `cur == NULL` with the engine's own
  pointer comparison.
- `array_shift(p, long, 1)` — pointer arithmetic: advance `p` by
  one `long` (8 bytes), staying inside the same allocation
  (provenance is preserved; the memory model would reject a walk
  across allocation boundaries, exactly as C's object model does).

The list nodes are honest C-style objects: each node is **one
allocation** of type `long[2]` — the value at offset 0, the next
pointer at offset 8 (`nodeTy`, `ListRevExhibit.lean`). Field access
within a node is `array_shift` arithmetic inside the allocation;
traversal between nodes is by *loaded* pointers, each carrying its
own provenance. NULL is the engine's null pointer value, which
serializes to eight zero bytes and deserializes back to null — the
round trip is proved against the engine's own
serializer/deserializer, not assumed.

And this is a real Lean term, not pseudocode — the loop body
(`ListRevExhibit.lean:505`):

```lean
def lrBody (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (mo : memory_order) (bbty nbty ubty : core_base_type) : CoreExpr :=
  Expr [] (Esseq (symPat [] lrBSym bbty)
    lrMemopE
    (Expr [] (Eif (Pexpr [] () (PEsym lrBSym))
      (Expr [] (Epure lrExitPe))
      (lrElse loc ann ra mo nbty ubty))))
```

`CoreExpr` is the *engine's generated expression type* — the very
AST the interpreter executes — and the metadata the exhibit does not
care about (source locations, annotations, base-type tags, the
memory order) is universally quantified: the theorems hold for every
instantiation.

## 3. What a triple means here

### 3.1 A small axiom

The logic's assertions are Iris propositions over a SPLIT ghost
carrier (Phase 2, the Caesium-shaped heap/allocs factorization): a
per-BYTE heap (address ↦ byte — the ghost fragment of the engine's
own bytemap), a per-allocation METADATA heap (allocation id ↦
base/type — the provenance/metadata authority), and a one-cell
allocator-cursor heap (`Heap.lean`). Typed subrange VIEWS
(`pointsToView`) own one field/element range of one allocation and
split/join at real ∗; `pointsToCell p (ty, bs)` — written with the
usual ↦ intuition — is the MAXIMAL view: *I own the whole
allocation `p` points to; it is live, in bounds, writable,
non-atomic, and its bytes are exactly `bs`.* The store small axiom (`Rules.lean:176`):

```lean
theorem wp_store … 
    (hmv : memValueFromValue fmapEmpty (Ctype [] (unatomic_ ty)) cv = some mv)
    (hst : StorableAt ty mv) :
    pointsToCell (GF := GF) pv (.own 1) ty bs ⊢
      WP (⟨storeExpr loc ann ty pv cv mo, ρ, Q⟩ : CoreRt) @ s; E
        {{ w, ∃ fp, ⌜w = (⟨SpikeVal.annot [DA_pos [] fp] Vunit, ρ, Q⟩ : CoreRVal)⌝ ∗
            pointsToCell pv (.own 1) ty (CerbMem.memValueToBytes [] mv).2 }}
```

Read it as the classic
`{p ↦ (ty, bs)} store(ty, p, v) {p ↦ (ty, bytes-of v)}`:
ownership of the cell entails a weakest precondition for the store
expression, whose postcondition returns the cell with its bytes
replaced by the engine's own serialization of `v`
(`memValueToBytes`). Three things to notice:

- **The precondition excludes undefined behavior.** The engine's
  `storeM` has a dozen ways to kill (dead allocation, out of
  bounds, ill-typed store, …). Ownership of the cell, plus the two
  explicit typing hypotheses, defeats every one of them — that is
  what makes "the engine never kills" provable later.
- **This is a small axiom in the original sense**: it mentions only
  the one cell the store touches. Everything else in the heap is
  untouched by construction, which is what the frame rule then
  exploits.
- It is proved, not assumed — by unfolding the WP one step against
  the package's mirrored step relation and running the engine's
  real `storeM` (§4 explains where that relation gets its
  authority).

The rest of the logic is the familiar kit: `wp_load`, sequencing,
the frame rule, consequence (`Rules.lean`); and for programs with
loops a *statement-level* WP `wps` with a label context — per-label
preconditions and a loop-invariant rule `blockSpecs_intro`
(`Wps.lean`, partial correctness), PLUS its TOTAL counterpart `wpt`
(`Wpt.lean`, foundations Phase 3): the same label-context shape with
variant-indexed label preconditions and a MANDATORY back-edge
decrease in the jump clause — the total rule `blockSpecsT` (which
replaced the retired, consumerless `blockSpecs_intro_variant`)
collapses into the pinned Iris TotalWeakestPre and yields both
termination and unconditional drive-fuel bounds
(the [capability manifest](CAPABILITY_MANIFEST.md), Notes 2). The
partial judgment is the classical treatment of `goto`-like jumps
(de Bruin-style label assumptions) built as a guarded fixpoint with
the same machinery Iris builds `wp` from; the total judgment is
built by structural recursion on its step budget — the
least-fixpoint discipline of total WPs, with the budget as the
well-founded measure.

### 3.2 The exported meaning: triples over the engine

Inside Iris, a triple is a statement about the *derived* logic. The
package does not stop there: it exports every claim down to the
engine. The exported form (`Adequacy.lean:371`; here abridged only
by writing the map library's fully qualified `union` as `∪`):

```lean
def SemTriple (e : CoreExpr) (P : CellMap)
    (post : value → CellMap → Prop) : Prop :=
  ∀ (R : CellMap), P ##ₘ R →
  ∀ (σ : Mem), Sat σ (P ∪ R) →
  ∀ (n : Nat) (aids : Nat → Nat), esize e + n ≤ lemDefaultFuel →
    (∀ r, drive aids n (spikeThread e) σ ≠ .killed r) ∧
    (drive aids n (spikeThread e) σ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem), drive aids n (spikeThread e) σ = .done v σ' →
      ∃ Q : CellMap, post v Q ∧ Q ##ₘ R ∧ Sat σ' (Q ∪ R))
```

There is no Iris in this statement. Unpack the quantifiers:

- **Any memory satisfying P, any frame, verbatim — at the fixed
  demo machine profile.** `P` is
  the footprint (a map of cells); `R` is an *arbitrary* disjoint
  rest of the heap. `Sat σ (P ∪ R)` says the real engine memory
  state `σ` actually carries those cells (live, in-bounds, bytes
  matching). The conclusion returns *the same R* alongside the
  post-footprint `Q` — the frame comes back untouched. This
  quantifier structure *is* the frame property, stated
  semantically. One scope honesty note (2026-09-01 re-audit,
  R-09): the memory and frame are fully quantified, but the thread
  and machine context are not — `SemTriple` runs `spikeThread e` at
  the fixed `spikeCtx`/`spikeEnv` demo profile (generalization over
  a well-formed `MachineCtx` is alloc arc P4).
- **Engine execution.** `drive` iterates the engine's own step
  function (`step_ctx`) and discharges each memory request exactly
  as the engine's sequential driver does — it is the driver's loop
  projected onto (thread state, memory state). The conclusion: the
  engine never kills (no undefined behavior reached), never gets
  stuck off-protocol, and any value it delivers satisfies the
  postcondition, with the final memory carrying `Q ∪ R`.
- **Partial correctness where labelled, total where earned.**
  Running out of the step budget `n` (`.more`) carries no
  obligation in the partial exports, and the `lemDefaultFuel` side
  condition is the engine's own internal fuel budget (10^6) — an
  honest artifact of the interpreter, not proof slack. The TOTAL
  exports (`fib_certified_total`, walked verbatim in §5.1;
  `list_reverse_certified_total`) are unconditional engine
  equations — the engine *equals* `.done …` at a concrete step
  bound, no fuel hypotheses at all — and since foundations Phase 3
  they are LOGIC RESULTS: corollaries of the total statement
  judgment through the generic measure→drive-fuel simulation (the
  manifest's total lane, Notes 2). History, one line: until Phase 3
  the fib equation was proved by a direct operational induction on
  the drive (the 2026-08-31 audit's F-02 finding); that proof is
  retired.

The bridge theorem is `semantic_triple_sound` (`Adequacy.lean:892`):
a triple proved in the derived logic (`ProvenTriple` — the only
place the WP appears in the exported layer) yields the `SemTriple`
above. Its proof is the adequacy argument: Iris adequacy over the
mirrored step relation, composed with a per-construct certification
that the engine's step is matched by the mirror (§4).

Loop programs use the same pattern one level up: `driveJ` is the
same engine loop at a run state carrying the label map (so `run`
can resolve its target), and `engine_adequacyJ` exports
`wps`-proved specifications through it.

### 3.3 The headline theorem, read line by line

`list_reverse_certified` (`ListRevExhibit.lean`; Phase 4 — the full
F-06 statement), abridged to its quantifier skeleton:

```lean
theorem list_reverse_certified …
    (ns : List (Int × Int)) (head : CerbMem.PointerValue)
    (m₀ : CellMap) (hseed : SeedChain m₀ head ns)
    (R : CellMap) (hR : m₀ ##ₘ R)
    …
    (σ₀ : Mem) (hcoh : Sat σ₀ (m₀ ∪ R))
    (nsteps : Nat) (aids : Nat → Nat)
    (hfuel : 6 + nsteps ≤ lemDefaultFuel) … :
    (∀ r, driveJ rs aids nsteps (procThread lrProcSym prog [fmapEmpty]) σ₀ ≠ .killed r) ∧
    (driveJ … ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem), driveJ … = .done v σ' →
      ∃ (p' : CerbMem.PointerValue) (Q : CellMap),
        v = ptrVal p' ∧ SeedChain Q p' ns.reverse ∧
        (∀ k, (get? Q k).isSome ↔ (get? m₀ k).isSome) ∧
        Q ##ₘ R ∧ Sat σ' (Q ∪ R))
```

- **Hypotheses**: `ns` is any list of nodes — each an ALLOCATION ID
  paired with its value; `m₀` is a cell footprint forming a linked
  chain for `ns` from `head` (`SeedChain`: one disjoint node
  allocation AT EACH LISTED ID, engine-serialized field bytes,
  well-formed machine addresses); `R` is an ARBITRARY cell
  footprint disjoint from it; `σ₀` is any engine memory actually
  carrying both (`Sat`); plus the fuel bounds.
- **Conclusion**: driving the real engine on the reversal program
  never kills, never derails, and any delivered value is a
  *pointer* heading a final footprint `Q` that is the chain for
  `ns.reverse` — the SAME allocation ids in exactly reversed order,
  each node still carrying its own value (in-place, literally: only
  the next fields moved); the footprint-equality conjunct pins the
  node set on the actual maps (no allocation, no leak); and the
  frame `R` comes back VERBATIM in `Sat σ' (Q ∪ R)`. Same
  footprint + in-place + frame, read off the engine's bytes; the
  TOTAL form adds termination (an unconditional `.done` equation at
  the derived bound `13·|ns| + 7`).

The proof is the point of the exhibit: loop invariant
`isList prev reversed ∗ isList cur rest ∗ RF` with
`ns = reversed.reverse ++ rest` (the frame proposition threaded
through the invariant — the only thing that crosses a back edge),
`isList` by plain structural recursion on the node list (no
step-indexing), each program construct discharged by its own rule —
no monolithic unfolding anywhere. The concrete instance
`list_reverse_demo` runs it on a seeded 3-node chain
`[(1,1),(2,2),(3,3)]`, every byte-level side condition discharged
by `rfl` on engine-serialized images. The SECOND CLIENT —
binary-tree rotation, `TreeRotExhibit.lean` — replays the same
statement shape on a branching structure with zero core-logic
edits (the Phase-4 accident-detector).

## 4. The trust story

What do you have to trust for these theorems to mean what §3 says
they mean? Three tiers, from nothing-new to read-this-part.

**Tier 1 — kernel-checked theorems about the engine's definitions.**
Every theorem is checked by the Lean kernel, and every theorem's
*transitive axiom cone* is BOUNDED in-build, the boundary axiom's
origin MECHANICALLY CHECKED, and the headline theorems' cones
EXACTLY PINNED (`Audit.lean`, the last import of the library; the
exhaustive sweep is an upper-bound containment check plus — in the
boundary modules — the Phase-5 origin discipline, under which
`runEffectful` in a cone must be reachable through the STATEMENT's
constants, making every boundary cone exact-by-construction; the
curated pins are additional equality checks): every cone is within
the classical trio
(`propext`, `Classical.choice`, `Quot.sound`), except the three
production-entry modules whose *statements* mention the shipped
initial driver state and are therefore additionally allowed the
semantics port's one
residual axiom `runEffectful` — a declared temporal boundary (an
effectful initialization seam scheduled for removal upstream; the
theorems hold for every value it could produce, since the program
fragment never reads the affected field). Non-kernel proof methods
(`native_decide`, `bv_decide`, `ofReduce*`) are banned by a grep
gate and would fail the in-build cone check anyway. At this tier
you trust: the Lean kernel, and the engine's definitions being the
semantics you care about (which is what the differential validation
against the OCaml oracle is for). Both take-on-faith items — the
axiom's statement, printed verbatim, and what that differential
validation actually covers, with the in-package path to its
record — are laid out in the README's ["What you are asked to take
on faith"](../README.md#what-you-are-asked-to-take-on-faith).
(One disambiguation on that path: the pinned semantics workspace
also carries the semantics repo's own derived relational spine —
`relsemcore`: `Step`/`runND_sound`/`HarnessAdequate` — which is
that repo's validation instrument for its runner, NOT part of this
package's chain; no bridging theorem between the two presentations
exists or is claimed, and this package's chain is exactly the tiers
described here. The README section above carries the full
paragraph.)

**Tier 2 — explicit hypotheses, visible in the statements.** Fuel
bounds, seeded-footprint hypotheses (`SeedChain`, `Coh`),
well-formedness premises (machine-address bounds), typing side
conditions. The house rule is that such premises are *stated, never
absorbed*: where the engine can panic or fork nondeterministically
outside the certified fragment, the logic simply has no rule (the
mirror is fail-closed), rather than a rule with a hidden totality
assumption. Every qualifier is on the claim's face; the README's
"Scope of the claims" is the complete list.

**Tier 3 — the specification idiom.** The one place trust rests on
*reading* rather than checking: the definitions the exported
statements are phrased in. `drive`/`driveJ` (the engine loop
projection), `dischargeStep` (the driver's request discharge,
mirrored function-by-function with file:line citations),
`SeedChain`/`ChainAt`/`Sat` (the footprint and readout predicates),
and the program terms themselves. If one of these said something
other than what this document claims it says, a theorem could be
true and uninteresting. Three guards:

1. **Smallness.** Each of these definitions is a screenful; they
   are listed and cited, and reading them is the intended audit.
   (`drive` is 9 lines; `SemTriple` is 9 lines; `ChainAt` is 6.)
2. **Executable vacuity checks.** The concrete demos pin the
   definitions to reality: `list_reverse_demo` exhibits a concrete
   `SeedChain` (so the hypotheses are satisfiable — the general
   theorem is not vacuously true), `fib_certified_total` is an
   unconditional *equation* on the engine's run, and
   `exhibitA_prod` concludes an equation about the *shipped*
   production pipeline (`runND (Driver.drive …)` from
   `initial_driver_state`) with only the file-system state and argv
   quantified — for that statement even the drive-loop projection
   drops out of the trust surface, because the theorem talks about
   the production entry point itself.
3. **The mirror is interior.** The package's hand-written step
   relation (`Step`) and the Iris logic have *zero authority*: they
   appear in proofs and in interior hypotheses, never in exported
   conclusions, and every rule is certified against the engine's
   own step function (`Soundness.lean`, per construct, with
   file:line citations into the engine). The design invariant is
   worth stating plainly: **because the mirror sits strictly inside
   the proofs and is closed off by the adequacy theorems, a wrong
   mirror can only make theorems unprovable — it can never make a
   false engine-level statement provable.** The same holds for the
   logic's rules and for iris-lean itself: a bug there deprives us
   of proofs, not of truth of what was proved about the engine.
   Two caveats keep this invariant honest (2026-08-31 audit, F-09).
   First, it is relative to tier 3: if a *statement-level*
   definition (`drive`, `dischargeStep`, a readout predicate) were
   wrong, a theorem could be true and irrelevant — that is exactly
   why tier 3 exists and is kept small. Second, the invariant is
   fail-open for COVERAGE: a missing mirror or cone case makes
   rules silently dead rather than false (the realized instance WAS
   value-scrutinee `Ecase` — local rules, no adequacy path — until
   the S1b export discharged it, audit F-01) — which is why
   per-construct coverage is gated by the generated
   [capability manifest](CAPABILITY_MANIFEST.md) instead of trusted
   to prose, and why (since Phase-1 S1c) the manifest's row set is
   itself DERIVED from the cone: the generator enumerates the
   fragment and mirror constructors out of the built environment,
   and a constructor without a manifest row fails gate 4 — the
   fail-open coverage channel closes by a failed check, not by
   vigilance.

The former loop/straight-line asymmetry is CLOSED (Phase 5): loop
programs now reach the production pipeline too. Three theorems
conclude directly about `CerbND.runND (Driver.drive …)
(initial_driver_state …)` from the cold start —
`fib_certified_production` (state-inert back-edge loop),
`counter_loop_certified_production` (heap-effecting loop against a
cell the program creates with the engine's real allocator), and
`list_reverse_certified_production` (the flagship's demo instance:
a two-node chain engine-built cold, then reversed in place by the
authored loop). The route is the proc-carrying, populated-label
scheduler collapse: one production driver round per certified
mirror step over the full fragment cone (`loop_step_frag`,
DriverCollapse), driven by the TOTAL statement judgment
(`wpt_driver_done`, ProdLoop — the driver-level analog of the
measure→drive-fuel simulation), with the label maps computed by
the shipped registration (the `*_labeledAt_production` ties). The
drive-lane theorems (`driveJ`) remain as lemmas — the loop
exhibits' engine-level workhorses — and the registration tie keeps
its own name (`counter_loop_certified_registration`, the renamed
F-05 debt).

One allocation caveat keeps that closure honest (the 2026-09-01
skeptical re-audit, R-01/R-02; alloc arc P1 landed the logic-path
repair). The allocation LOGIC PATH now exists end to end: public
`wps_create`/`wpt_create` take the abstract finite capacity
`allocCap (req :: rest)` and bind an existential fresh pointer
(statements cursor-free); the allocation-aware launchers
(`spike_step_adequacy_alloc`, `wpt_engine_boundU/J_alloc`,
`wpt_strongly_normalizing_alloc`) grant `allocCap` from real
Cerberus memory through `launchResources` under the `LaunchCoh`
launch invariant; and the chain is closed at the engine by
`alloc_create_launch_smoke` (AllocExhibit) — a bare create from the
production cold-start memory delivering a pointer at `driveU` fuel
exactly 2, proved only through the public total rule and the
allocation-aware launcher. THE PARTIAL-LANE WHOLE-PROGRAM
CONSUMER (alloc arc P2 items 1-2): the struct allocation client
`struct_create_store_wps` (StructExhibit) is a public-rule client
over `allocCap` — the program binds its fresh pointer
(`lets p = create(...)`) and stores through the bound symbol — and
`struct_create_store_adequacy` launches it against the real engine
from the production cold-start memory through
`spike_engine_adequacy_alloc`. THE COMPLETE
CREATE/STORE/LOAD PRODUCTION EXPORT (P2 step 3): `exhibitA_prod` is
now a whole-program logic proof — the program binds its created
pointer, `progAProd_wpt` carries create/store/load in one total
judgment through the PUBLIC `wpt_create`, and the generic
allocation-aware driver collapse (`wpt_driver_done_alloc` →
`prod_run_eqJ`) reaches the shipped pipeline; the old operational
create prefix and six-round termination trace are DELETED (likewise
Exhibit.lean's straight-line trace, retired for the generic total
route `exhibitA_total`). THE LOOP-LANE
WHOLE-PROGRAM CONSUMERS (P2 steps 4-5 — R-02 CLOSED): the counter
and reversal production programs BIND their engine-created pointers,
`ctrProd_wpt`/`lrProd_wpt` carry create + stores + loop in single
total judgments (the reversal consuming the GENERIC list logic
verbatim at existential engine-picked allocation ids, transported by
`wpt_mono_Ls`; the create rule's exported address bounds feed
`isList`'s node-WF facts), and the generic
`wpt_driver_done_alloc` → `prod_run_eqJ` collapse supplies every
pipeline arrow. The former handwritten `driverDone_step` prefixes
are DELETED; no positive exhibit contains a direct operational-
semantic proof chain (the grep transcript and the R-01/R-02
closure-test plants are in `docs/2026-09-01_p2-notes.md`). The finding-by-finding
closure table is in `docs/2026-09-01_alloc-arc-plan.md`. The
README's divergence register keeps every remaining seam on one
list, each with its discharge path.

## 5. Reading the theorems: statement surfaces

The trust base and the theorem machinery are easy to conflate in a
development this interlocked, so this section separates them
mechanically for three headline exports. For each: the statement
verbatim; a reading of every identifier in it, partitioned into
**ENGINE** (generated semantics code — trusted because it *is* the
semantics under judgment), **SPEC IDIOM** (this package's
statement-level definitions — the trust surface of tier 3, each
printed or one click away), and **HYPOTHESES** (what you are
assuming when you believe the conclusion); and one sentence on what
is provably *absent* from the statement.

The partition is not hand-asserted: a census instrument
(`scripts/statement_census.lean`) walks each pinned theorem's
statement term, collects every constant in it (proofs are not
inspected), and bins by module of origin. Regenerate it yourself:

```bash
../scripts/capped ~/.elan/bin/lake env lean scripts/statement_census.lean
```

Its output for the three theorems below is pasted verbatim at the
end of each subsection; §5.4 states the invariant the full run
witnesses and the two honest observations it surfaces.

### 5.1 `fib_certified_total` — an unconditional engine equation

Classification (foundations Phase 3; audit F-02 remediated): this
is a TOTAL-CORRECTNESS RESULT OF THE LOGIC — a corollary of the
total statement judgment (`fib_wpt`, with the variant `2·(n−i)+3`
pinned by the invariant and the back edge discharging the mandatory
decrease) through the generic measure→drive-fuel simulation
(`wpt_engine_boundJ`); the final-state pin `σ₀` comes from the
generic state-inert-cone conjunct. Zero example-level `Step`
constructors or `driveJ_step` chains appear in its proof. History,
one line: until Phase 3 this equation was proved by a direct
operational induction on the drive (the audit's F-02 finding); that
proof is retired. It earns its place here as the strongest
*statement*: an unconditional equation on the engine's run, with
the smallest statement surface. The statement, verbatim
(`FibExhibit.lean`):

```lean
theorem fib_certified_total (sbty : core_base_type) (n : Int)
    (hn : 0 ≤ n) (σ₀ : Mem) (aids : Nat → Nat) :
    driveJ (fibRS ra n ibty abty bbty) aids (2 * n.toNat + 4)
      (procThread fibProcSym (fibProg ra n sbty ibty abty bbty)
        [fmapEmpty]) σ₀ =
      .done (ivVal (fibSpec n.toNat)) σ₀
```

(`ra`/`ibty`/`abty`/`bbty` are section variables — quantified Core
metadata, like `sbty`.) Reading table:

| Identifier | Bin | What it is |
|---|---|---|
| `core_base_type`, `sym`, `value`, `Fmap`, `fmapEmpty`, `core_run_annotation` | ENGINE | generated Core AST/state types and the engine's map library |
| `driveJ` | SPEC IDIOM | the engine loop `{step_ctx → sequential discharge}` projected to (thread state, memory), 10 lines, printed below |
| `DriveResult` (`.done`) | SPEC IDIOM | the drive outcome type, printed in §3.2's vicinity below |
| `procThread` | SPEC IDIOM | the launch thread state (arena + env + current procedure), 3 lines, below |
| `fibProg`, `fibRS`, `fibProcSym` | SPEC IDIOM | the authored fib program, its label-carrying run state, its procedure symbol (`FibExhibit.lean` — the program is §2-style authored Core) |
| `fibSpec` | SPEC IDIOM | Lean-side fib, 4 lines, below |
| `ivVal` | SPEC IDIOM | injection of a mathematical integer into a Core value, 1 line, below |
| `Mem` | SPEC IDIOM | abbreviation for the engine's `CerbMem.MemState` (1 line) |
| `hn : 0 ≤ n` | HYPOTHESIS | fib of a non-negative count |
| — | HYPOTHESES | *nothing else*: no fuel bound, no seeded state (`σ₀` and `aids` are universally quantified; `aids : Nat → Nat` is the action-id supply — the ∀-quantified oracle for the driver's fresh action-id draws, irrelevant on this deterministic fragment) |

One fact the statement implies but the table does not shout: the
conclusion delivers `.done … σ₀` — the *initial* memory, returned
unchanged. The fib program provably touches no memory.

The idiom, in full — this is the entire non-engine vocabulary of
the theorem:

```lean
def driveJ (rs : core_run_state) (aids : Nat → Nat) :
    Nat → thread_state → Mem → DriveResult
  | 0, th, σ => .more th σ
  | n+1, th, σ =>
    match (step_ctx fmapEmpty σ spikeFile fmapEmpty 0 (none, th)).map
        (dischargeStep (aids 0) rs σ) with
    | [.next th' σ'] => driveJ rs (fun i => aids (i+1)) n th' σ'
    | [.done v] => .done v σ
    | [.killed r] => .killed r
    | _ => .stuck

inductive DriveResult : Type where
  | more (th : thread_state) (σ : Mem)
  | done (v : value) (σ : Mem)
  | killed (r : kill_reason mem_error)
  | stuck

def procThread (p : sym) (e : CoreExpr) (ρ : EnvStack) : thread_state :=
  { arena := e, stack0 := Stack_empty, errno := default, env := ρ,
    current_proc_opt := some p, exec_loc := default, current_loc := default }

def ivVal (i : Int) : value := Vobject (OVinteger (CerbMem.integerIval i))

def fibSpec : Nat → Int
  | 0 => 0
  | 1 => 1
  | n + 2 => fibSpec n + fibSpec (n + 1)
```

`step_ctx` is the engine's step function and `dischargeStep` is the
driver's request discharge mirrored function-by-function
(`Soundness.lean`, each projection cited to `Driver.lean` by line);
`spikeFile` is the default (empty) Core file. **Absent from the
statement**: `Step`, `wps`, `WP`, Iris, ghost state — the entire
proof machinery. Because none of it occurs in the statement, a bug
in any of it could only have made this theorem unprovable; it
cannot have made this equation about the engine's execution false.
(The remaining trust is tier 3, per §4's caveat: `driveJ` and the
program/spec definitions that DO occur in the statement — a wrong
definition there would make the equation true but about the wrong
thing, which is what the printed idiom above is for.)

Census output, verbatim (2026-08-31, this checkout):

```
== CerberusHeapLang.fib_certified_total ==
  ENGINE (6):
    Fmap
    core_base_type
    core_run_annotation
    fmapEmpty
    sym
    value
  SPEC IDIOM (CerberusHeapLang) (10):
    CerberusHeapLang.DriveResult
    CerberusHeapLang.DriveResult.done
    CerberusHeapLang.Mem
    CerberusHeapLang.driveJ
    CerberusHeapLang.fibProcSym
    CerberusHeapLang.fibProg
    CerberusHeapLang.fibRS
    CerberusHeapLang.fibSpec
    CerberusHeapLang.ivVal
    CerberusHeapLang.procThread
  IRIS (0):
  LEAN CORE/STD (17):
    Eq
    HAdd.hAdd
    HMul.hMul
    Int
    Int.instLEInt
    Int.toNat
    LE.le
    List.cons
    List.nil
    Nat
    OfNat.ofNat
    instAddNat
    instHAdd
    instHMul
    instMulNat
    instOfNat
    instOfNatNat
```

### 5.2 `list_reverse_certified` — the canonical exhibit

Classification (foundations Phase 4; audit F-06 remediated): the
flagship states SAME-FOOTPRINT, IN-PLACE reversal WITH FRAME
PRESERVATION — and it is SpikeGF-concrete: since Phase 4 no
ghost-functor binder appears in the statement. The statement,
verbatim (`ListRevExhibit.lean`; `loc`, `ann`, `ra`, `mo` and the
`*bty` base-type tags are section variables — quantified metadata):

```lean
theorem list_reverse_certified
    (sbty : core_base_type) (ns : List (Int × Int))
    (head : CerbMem.PointerValue)
    (m₀ : CellMap) (hseed : SeedChain m₀ head ns)
    (R : CellMap) (hR : m₀ ##ₘ R)
    (hlib : CerbLocation.isLibraryLocation loc = false)
    (σ₀ : Mem) (hcoh : Sat σ₀ (Iris.Std.PartialMap.union m₀ R))
    (nsteps : Nat) (aids : Nat → Nat)
    (hfuel : 6 + nsteps ≤ lemDefaultFuel)
    (hfuel2 : 5 + nsteps ≤ lemDefaultFuel) :
    let prog := lrProg loc ann ra mo sbty pbty cbty bbty nbty ubty head
    let rs := lrRS loc ann ra mo pbty cbty bbty nbty ubty
    (∀ r, driveJ rs aids nsteps
      (procThread lrProcSym prog [fmapEmpty]) σ₀ ≠ .killed r) ∧
    (driveJ rs aids nsteps
      (procThread lrProcSym prog [fmapEmpty]) σ₀ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem),
      driveJ rs aids nsteps
        (procThread lrProcSym prog [fmapEmpty]) σ₀ = .done v σ' →
      ∃ (p' : CerbMem.PointerValue) (Q : CellMap),
        v = ptrVal p' ∧
        SeedChain Q p' ns.reverse ∧
        (∀ k, (Iris.Std.PartialMap.get? Q k).isSome ↔
          (Iris.Std.PartialMap.get? m₀ k).isSome) ∧
        Q ##ₘ R ∧
        Sat σ' (Iris.Std.PartialMap.union Q R))
```

Read as a specification: the node list `ns` pairs each node's
ALLOCATION ID with its value; the input is a seeded chain footprint
`m₀` for `ns` from `head` TOGETHER WITH an arbitrary disjoint
footprint `R` (the same rest-quantifier `SemTriple` uses, here at
the jump lane); the output pointer heads a final footprint `Q`
seeded as `ns.reverse` — the SAME allocation ids in exactly
reversed chain order (a permutation of the original node set by
construction), each node still carrying its own value: in-place in
the literal sense, only the next fields moved. The footprint
equality conjunct pins the node SET on the actual maps — nothing
allocated, nothing leaked — and `Sat σ' (Q ∪ R)` returns the frame
VERBATIM. The TOTAL form (`list_reverse_certified_total`) has the
same conclusion as an unconditional `.done` equation at fuel
`13·|ns| + 7` with no fuel hypotheses; `list_reverse_terminates`
adds strong normalization.

Reading table (identifiers already read in §5.1 not repeated):

| Identifier | Bin | What it is |
|---|---|---|
| `CerbMem.PointerValue`, `CerbLocation.isLibraryLocation`, `lemDefaultFuel`, `memory_order`, `kill_reason`, `mem_error`, `core_run_state` | ENGINE | the memory model's pointer values, the engine's location test, its fuel budget, its error vocabulary |
| `lrProg`, `lrRS`, `lrProcSym` | SPEC IDIOM | the authored reversal program (§2 shows it), its label-carrying run state, its procedure symbol |
| `SeedChain` | SPEC IDIOM | the chain footprint: one disjoint node cell per (id, value) pair, at that allocation id, printed below — used for BOTH the input (`m₀`, at `ns`) and the output (`Q`, at `ns.reverse`) |
| `CellMap`, `SpikeCell`, `SpikeHeapF`, `cellPtr` | SPEC IDIOM | footprints: finite maps of allocation-id → (address, type, bytes), and the fragment pointer shape |
| `Sat` (= `Coh`), `CellCoh` | SPEC IDIOM | footprint satisfaction by the real memory state, printed below |
| `ptrVal` | SPEC IDIOM | injection of a pointer into a Core value (1 line) |
| `Iris.Std.PartialMap.get?`/`union`, `##ₘ` (disjointness) | IRIS (data-structure library) | iris-lean's finite-map operations — the vocabulary of footprint maps, NOT program-logic machinery (see §5.4) |
| `hseed`, `hR`, `hcoh` | HYPOTHESES | the seeded input chain, an arbitrary disjoint frame footprint, both carried by the initial memory |
| `hlib` | HYPOTHESIS | the program's source location is not library-internal (a WF fact about metadata) |
| `nsteps`, `aids` | quantified data | any step budget; any action-id supply (`aids` — the driver's fresh action-id oracle, ∀-quantified; irrelevant on this deterministic fragment) |
| `hfuel`, `hfuel2` | HYPOTHESES | in-budget fuel (the engine's own 10^6 budget): one nested budget fact per drive entry point — the whole program (`esize` 6) and the loop body the jump re-enters (`esize` 5; one construct less, hence the +1 slack). `hfuel2` is a trivial consequence of `hfuel`, carried separately as interim scaffolding of the in-budget form (the TOTAL export has no fuel hypotheses at all) |

The seeding predicate, in full — a pure `Prop` over engine objects,
no Iris program logic (`nodeValDec`/`nodeNextDec` say the node's
byte ranges decode — by the *engine's* decoder — to the value resp.
the next pointer):

```lean
def SeedChain : SpikeHeapF SpikeCell → CerbMem.PointerValue →
    List (Int × Int) → Prop
  | m, p, [] => m = (∅ : SpikeHeapF SpikeCell) ∧ p = nullNode
  | m, p, nd :: ns => ∃ (aN : Int) (q : CerbMem.PointerValue)
      (bs : List CerbMem.AbsByte) (m' : SpikeHeapF SpikeCell),
      p = cellPtr nd.1 aN ∧ 0 < aN ∧ aN < 2 ^ 64 ∧ bs.length = 16 ∧
      nodeValDec bs nd.2 ∧ nodeNextDec bs q ∧
      ((Iris.Std.PartialMap.singleton nd.1 (SpikeCell.mk aN nodeTy bs) :
        SpikeHeapF SpikeCell)) ##ₘ m' ∧
      m = Iris.Std.PartialMap.union
        (Iris.Std.PartialMap.singleton nd.1 (SpikeCell.mk aN nodeTy bs)) m' ∧
      SeedChain m' q ns

structure Coh (σ : Mem) (m : SpikeHeapF SpikeCell) : Prop where
  cells : ∀ id c, get? m id = some c → CellCoh σ id c
  disj : ∀ id1 id2 c1 c2, id1 ≠ id2 → get? m id1 = some c1 →
    get? m id2 = some c2 → cellsDisjoint c1 c2
```

`SeedChain.footprint` is the one-lemma reading of "same footprint":
a seeded chain's map is defined at EXACTLY the chain's id list, so
the conjunct `∀ k, (get? Q k).isSome ↔ (get? m₀ k).isSome` is
equivalent to `ns.reverse.map (·.1)` and `ns.map (·.1)` having the
same members — the reversal permutation. The pre-Phase-4 values-only
`ChainAt` conclusion is retired; the id-indexed `ChainAt` (per-node
`CellCoh` facts about the final `MemState`) remains derivable —
`seedChain_chainAt` — and the concrete `list_reverse_demo` includes
it, instantiating a 3-node chain `[(1,1),(2,2),(3,3)]` with every
byte-level side condition discharged by `rfl` on engine-serialized
images (so the hypotheses are satisfiable — the general theorem is
not vacuously true).

**Absent from the statement**: `Step`, `wps`, `wpt`, `WP`,
`isList`, the points-to, ghost state, and — since Phase 4 — the
ghost-functor binder `{GF : BundledGFunctors} [SpikeGpreS GF]` that
the census used to flag as the one machinery-shaped hypothesis: the
flagships are stated at the concrete `SpikeGF` internally and
export no Iris program-logic vocabulary at all. What remains in the
IRIS census bin is iris-lean's finite-map *library* (the footprint
maps' `get?`/`union`/disjointness and the backing `ExtTreeMap`
instance) — data-structure vocabulary, listed rather than hidden.

Census output, verbatim (2026-09-01, this checkout):

```
== CerberusHeapLang.list_reverse_certified ==
  ENGINE (14):
    CerbLocation.Loc
    CerbLocation.isLibraryLocation
    CerbMem.PointerValue
    Fmap
    core_base_type
    core_run_annotation
    core_run_state
    fmapEmpty
    kill_reason
    lemDefaultFuel
    mem_error
    memory_order
    sym
    value
  SPEC IDIOM (CerberusHeapLang) (17):
    CerberusHeapLang.CellMap
    CerberusHeapLang.CoreExpr
    CerberusHeapLang.DriveResult
    CerberusHeapLang.DriveResult.done
    CerberusHeapLang.DriveResult.killed
    CerberusHeapLang.DriveResult.stuck
    CerberusHeapLang.Mem
    CerberusHeapLang.Sat
    CerberusHeapLang.SeedChain
    CerberusHeapLang.SpikeCell
    CerberusHeapLang.SpikeHeapF
    CerberusHeapLang.driveJ
    CerberusHeapLang.lrProcSym
    CerberusHeapLang.lrProg
    CerberusHeapLang.lrRS
    CerberusHeapLang.procThread
    CerberusHeapLang.ptrVal
  IRIS (4):
    Iris.Std.PartialMap.disjoint
    Iris.Std.PartialMap.get?
    Iris.Std.PartialMap.union
    Std.ExtTreeMap.instPartialMapCompare
  LEAN CORE/STD (25):
    And
    Bool
    Bool.false
    Bool.true
    Eq
    Exists
    HAdd.hAdd
    Iff
    Int
    Int.instTransOrd
    LE.le
    List
    List.cons
    List.nil
    List.reverse
    Nat
    Ne
    OfNat.ofNat
    Option.isSome
    Prod
    instAddNat
    instHAdd
    instLENat
    instOfNatNat
    instOrdInt
```


### 5.3 `exhibitA_prod` — the shipped pipeline, no drive loop at all

The statement, verbatim (`ProdExhibit.lean:372`):

```lean
theorem exhibitA_prod (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive fmapEmpty false (prodFile progAProd) args)
          (initial_driver_state (prodFile progAProd) fs) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = sevenVal ∧
      CerbMem.readBytesFrom dst'.layout_state pxAddr 4 =
        (CerbMem.memValueToBytes [] sevenMval).2
```

Reading table:

| Identifier | Bin | What it is |
|---|---|---|
| `CerbND.runND`, `_root_.drive`, `initial_driver_state`, `driver_result`, `driver_state`, `nd_status.Active` | ENGINE | the shipped pipeline: `runND (drive …) (initial_driver_state …)` is the exact composite the cerberus-lean executable runs (its `Main.lean`). NB `_root_.drive` here is the **engine's** driver entry point, not this package's drive loop — the name collision is why the statement spells `_root_.` |
| `CerbMem.readBytesFrom`, `CerbMem.memValueToBytes`, `driver_state.layout_state`, `dres_core_value`, `CerbFS.FsState` | ENGINE | the memory model's byte reader/serializer, the final-state and result projections, the file-system state type |
| `prodFile` | SPEC IDIOM | the synthetic one-procedure Core file wrapping the program (`ProdEntry.lean` — a record literal, `main` plus one `Proc`) |
| `progAProd` | SPEC IDIOM | the authored program: `lets _ = create(4,int) in lets _ = store(x,7) in load(x)` (`ProdExhibit.lean`) |
| `pxAddr`, `sevenVal`, `sevenMval` | SPEC IDIOM | the address the production allocator deterministically mints for the program's cell; the Core value `Specified(7)` and its memory value (1 line each) |
| `fs`, `args` | HYPOTHESES | none, in effect: the theorem holds for *every* file-system state and argument list |

**Absent from the statement**: everything of ours except the
program, the wrapper file, and three value/address constants — no
`Step`, no WP, no Iris, and not even `drive`/`driveJ`: the
execution named in the conclusion is the engine's own production
entry point. This is the exhibit that pins the drive-lane idiom to
reality from the outside. Its axiom cone carries `runEffectful`
(§4 tier 1) because `initial_driver_state`'s definition draws a
symbol counter through an effectful seam — in the statement's
*cone*, not its surface.

Census output, verbatim (2026-08-31, this checkout):

```
== CerberusHeapLang.exhibitA_prod ==
  ENGINE (23):
    CerbFS.FsState
    CerbLocation.Loc
    CerbMem.AbsByte
    CerbMem.Funptrmap
    CerbMem.IntegerValue
    CerbMem.memValueToBytes
    CerbMem.readBytesFrom
    CerbND.runND
    drive
    driver_error
    driver_result
    driver_result.dres_core_value
    driver_state
    driver_state.layout_state
    fmapEmpty
    initial_driver_state
    mem_constraint
    nd_status
    nd_status.Active
    step_kind
    sym
    tag_definition
    value
  SPEC IDIOM (CerberusHeapLang) (5):
    CerberusHeapLang.prodFile
    CerberusHeapLang.progAProd
    CerberusHeapLang.pxAddr
    CerberusHeapLang.sevenMval
    CerberusHeapLang.sevenVal
  IRIS (0):
  LEAN CORE/STD (15):
    And
    Bool.false
    Eq
    Exists
    Int
    List
    List.cons
    List.nil
    Nat
    OfNat.ofNat
    Prod
    Prod.mk
    Prod.snd
    String
    instOfNatNat
```

### 5.4 The invariant, and what the census surfaces

The full census run covers all fifteen pinned theorems: the README's
verify-me list (including the Phase-4 tree-rotation exports) plus —
since the arc-close re-audit fix (L2, 2026-09-01) — the three
Phase-5 production exports (`fib_certified_production`,
`counter_loop_certified_production`,
`list_reverse_certified_production`). What it witnesses: **every exported statement is engine vocabulary plus
the enumerated spec idiom plus Lean core/std, nothing else** — with
two honest observations, reported rather than papered over:

1. **The ghost-functor binder is GONE from every loop and flagship
   export** (Phase 4 removed it from the flagships and tree
   exports; Phase 5 from the remaining loop exports —
   `counter_loop_certified`, `fib_certified`,
   `array_sum_certified`, `counter_loop_certified_registration`):
   all are stated at the concrete `SpikeGF` internally and carry no
   `Iris.BundledGFunctors`/`SpikeGpreS` hypothesis. The binder
   remains only on the GENERIC bridge theorem
   (`semantic_triple_sound` — whose hypothesis `ProvenTriple` is
   itself an Iris-level judgment, so the binder is load-bearing
   there, permanently and by design).
2. **Finite-map vocabulary.** Statements that phrase footprints
   through finite-map *operations* (the flagships' framed
   footprints and the loop exports' singleton cells —
   `list_reverse_certified`, `list_reverse_demo`,
   `tree_rotate_certified{,_total}`, `counter_loop_certified`,
   `array_sum_certified`, `counter_loop_certified_registration`)
   surface iris-lean's finite-map *library* (`Iris.Std.PartialMap`
   operations — `singleton`, `get?`, `union`, disjointness — and an
   `ExtTreeMap` instance) in the IRIS bin. That is data-structure
   vocabulary (the type of footprint maps), not program-logic
   machinery — but it is iris-lean code in a statement surface, so
   it is listed, not hidden. The three Phase-5 production exports,
   by contrast, have census-witnessed EMPTY IRIS bins: their
   footprint vocabulary enters only through the named spec-idiom
   predicates (`CellCoh`, `Sat`/`SeedChain` over `CellMap`), whose
   definitions §3 and §5.2 read. (Arc-close correction: an earlier
   revision of this item cited `counter_loop_certified_production`
   as surfacing the finite-map library — the extended census showed
   its IRIS bin is empty; re-audit finding L1.)

The census GATES since the acceptance-suite slice (2026-09-01):
its output is committed as `docs/STATEMENT_CENSUS.txt` and
`scripts/test_unit.sh` gate 5 re-runs it on every gate pass,
failing on any drift (fail-closed; plant-tested both directions —
`docs/2026-09-01_acceptance-suite-record.md`). A statement-surface
change to any pinned export therefore requires a deliberate
same-commit re-baseline of the committed census.

## 6. Check it yourself in five minutes

From the repository root (offline build; deps resolve through local
pins):

```bash
scripts/setup-cerberus-dep.sh        # once: the pinned semantics workspace
cd cerberus-heaplang
../scripts/capped ~/.elan/bin/lake build
```

A green build already runs the audit: `Audit.lean` sweeps the
axiom cone of every theorem in the package against the declared
boundary and checks every constant of every kind for
`sorryAx`/`ofReduceBool`/`ofReduceNat`. Expected tail:

```
info: CerberusHeapLang/Audit.lean:622:0: CerberusHeapLang axiom sweep: 1123 theorems BOUNDED by the declared upper bounds (71 in the production-entry boundary modules, of which 13 carry the boundary axiom — each STATEMENT-BORNE, origin-checked, so every boundary cone is exact-by-construction: trio + runEffectful iff the statement carries it; all other theorems bounded by the trio; headline cones additionally pinned above)
info: CerberusHeapLang/Audit.lean:622:0: CerberusHeapLang banned-axiom sweep: 2075 constants of every kind checked; sorryAx/ofReduceBool/ofReduceNat absent from all cones
Build completed successfully (443 jobs).
```

What to expect around that tail, so nothing surprises you:

- In sandboxed environments without a systemd user bus,
  `../scripts/capped` prints
  `capped: WARNING — systemd user bus unavailable (sandbox); running UNCAPPED`
  (plus an `interim per [USER 2026-08-29]` governance line) and
  proceeds. The cap is a resource-limit wrapper (a memory blast
  radius for builds); running without it changes nothing about
  what the build verifies.
- The tail is preceded by `unusedVariables` linter warnings from
  the semantics dependency's `generated/*` files — linter noise
  from generated code, not failures. A failure is a red `error:`
  line, a missing audit tail, or a nonzero exit.
- Timing: with the package already built, `lake build` replays
  from cache in about a second. A from-scratch elaboration of this
  package's 443 jobs is a long build — expect minutes to tens of
  minutes depending on the machine (no pinned cold timing is
  recorded). The setup script itself is offline (it clones and
  primes the workspace from the local repository, prebuilt
  semantics artifacts included) and is an idempotent, sub-second
  no-op when the workspace is already primed.

Then ask the kernel directly about three headline theorems:

```bash
../scripts/capped ~/.elan/bin/lake env lean --stdin <<'EOF'
import CerberusHeapLang
#print axioms CerberusHeapLang.list_reverse_certified
#print axioms CerberusHeapLang.fib_certified_total
#print axioms CerberusHeapLang.exhibitA_prod
EOF
```

Observed output (2026-08-31, this checkout):

```
'CerberusHeapLang.list_reverse_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.fib_certified_total' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.exhibitA_prod' depends on axioms: [propext, runEffectful, Classical.choice, Quot.sound]
```

The first two are exactly the classical trio; the production-entry
statement additionally carries the declared `runEffectful` boundary
(tier 1 above). `sorryAx` anywhere is a failure. To audit tier 3,
read the statement vocabulary — §5 walks the three headline
statements identifier by identifier and prints the idiom
definitions in full; the file map:

- `drive`, `driveJ`, `dischargeStep`, `SemTriple`, `Sat` —
  `Adequacy.lean`, `Soundness.lean`
- `SeedChain`, `ChainAt`, `lrProg`/`lrBody` — `ListRevExhibit.lean`
- the production statements' vocabulary is the engine's own
  (`runND`, `Driver.drive`, `initial_driver_state`) —
  `ProdEntry.lean`, `ProdExhibit.lean`, `ProdLoopExhibit.lean`

## 7. Reading the development

The modules in teaching order (import order is compatible), one
line each:

1. `Step.lean` — the mirrored small-step relation over the engine's
   generated AST and state types; hand-written, zero authority
   until certified.
2. `Heap.lean` — points-to over the engine's memory state
   (allocation-rooted cells, iris-lean GenHeap); the
   `storeM`/`loadM` success lemmas.
3. `Lang.lean` — the iris-lean `Language` instance over Step.
4. `Rules.lean` — the base logic: store/load small axioms,
   sequencing, frame, consequence.
5. `EnvLaws.lean` — lawfulness of the engine's environment maps
   (lookup-after-add over reachable frames).
6. `Wps.lean` — the label-context statement WP: jump-aware
   sequencing, the loop-invariant rule (partial correctness; the
   total stratum is `Wpt.lean` — §3.1), and `Wpt.lean` +
   `TotalAdequacy.lean` — the total judgment, its collapse into
   Iris TotalWeakestPre, and the two adequacy halves (termination;
   the generic drive-fuel simulation), with `DivergeExhibit.lean`
   as the negative test.
7. `Soundness.lean` — the boundary module: per-construct
   certification of Step against the engine's `step_ctx` and driver
   discharge.
8. `Adequacy.lean` — the exported face: `drive`/`driveJ`,
   `SemTriple`, `semantic_triple_sound`, the frame theorem.
9. `Exhibit.lean` — straight-line exhibits at the engine level
   (store/load, the frame exhibit, disjoint sequential stores).
10. `LoopExhibit.lean` → `FibExhibit.lean` → `ArrayExhibit.lean` →
    `ListRevExhibit.lean` — the loop exhibits, in increasing order
    of heap content, ending at list reverse.
11. `DriverCollapse.lean` → `ProdLoop.lean` → `ProdEntry.lean` →
    `ProdExhibit.lean` → `ProdLoopExhibit.lean` — the production
    pipeline: scheduler/nondeterminism collapse (Phase 5: the
    proc-carrying, populated-label rounds and the per-redex driver
    step-match), the total-driven driver simulation, cold start from
    the shipped initial state, exhibit A and the three loop programs
    at the production entry.
12. `Audit.lean` — the in-build axiom gate.

(`StmtProbe/` is a self-contained toy-language design probe for the
statement WP — no engine imports; kept as a record, skippable.)

Design records, decision provenance, and the development history
live in the dated files under [`docs/`](.); the README carries the
claims surface and the divergence register.
