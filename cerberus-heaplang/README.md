# cerberus-heaplang

A classical separation logic — Reynolds/O'Hearn: points-to and ∗,
small axioms, the frame rule, sequencing, consequence, conditionals,
loops with invariants — over the Cerberus Core semantics, built on
iris-lean. Every exported execution theorem is either explicitly
provisional over driveU or reaches the shipped engine; every public
logical rule has a kernel-checked adequacy path through the package
mirror to the engine.

**Cerberus** is an executable semantics for C: it elaborates C into a
typed functional intermediate language, **Core**, and runs Core on an
interpreter over a byte-level, provenance-aware memory object model.
The engine here is the Lean 4 port of that semantics, differentially
validated against the OCaml implementation and pinned by commit in
`../scripts/semantics-pin.env`. This package instantiates an Iris
program logic over a fragment of Core, proves every rule against that
engine, and exports closed-program theorems whose statements are
Iris-free. Its root-of-trust exports are the total-correctness
statements about the shipped cerberus-lean driver (`exhibitA_prod`,
`*_production`); its partial-correctness exports, stated over the
package's drive loop `driveU`, carry the label PROVISIONAL ("The
claim" below). **New reader? Start with the
[walkthrough](docs/WALKTHROUGH.md).** The normative architecture
statement — the semantic authority, the mirror's one-directional
certification, the two lanes, the open items, every sentence naming
its theorem — is [ARCHITECTURE.md](ARCHITECTURE.md). This package is a
demonstration of classical separation logic over Core and nothing
more; it is not the RefinedC port (this repository's root
`RefinedCerberus` package).

## Scope, exactly

**The fragment.** Straight-line and loop programs in single-threaded
Core: `store`/`load`/`create`/`alloc` actions and `kill` of EITHER kind
— `kill(static ty, p)`, C's automatic-storage dispose (kill/free arc
K2), and `free(p)`, the dynamic kill pairing with `alloc(al, n)`
(`Alloc0`, C's `malloc`; kill/free arc K3) — at evaluated operands and
at the operand-evaluation form the engine dispatches when "the operands
are not all values", the `PtrEq` memop, strong sequencing `Esseq` at the
wildcard, `Specified`-binder and plain-symbol-binder patterns (the
plain-symbol binder's head restricted to the bare-value producers
`BareHead` — a literal, `create`, `alloc`, the `PtrEq` memop — so the
value it binds is never annotated; fragment closure, 2026-09-02), weak
sequencing `Ewseq` at the wildcard, `Esave` at `PePure` initializers
within the evaluator's fuel, `Eif` at a `PePure` guard, the
context-discarding jump `Erun` at `PePure` arguments, value-scrutinee
`Ecase`, `PEsym`-shaped pure exits, the covered operand grammar
`PePure` — `PEval`/`PEsym`/the eight mirrored `PEop` binops
(`Add`/`Sub`/`Mul`/`Eq`/`Lt`/`Le`/`Gt`/`Ge`)/`PEarray_shift` — and the
run-time annotation residue. (`Frag.store` admits EITHER locking mode — `lk` is unconstrained —
while every store rule is at `Store0 false`: the locking store, whose
engine success flips the allocation's `isReadonly`, has no rule, so no
derivation traverses one; K1 audit N-2.) The per-construct authority is the
inductive `Frag` (Soundness.lean), the premise of every adequacy
theorem; the generated [capability manifest](docs/CAPABILITY_MANIFEST.md)
lists one row per (`Frag` constructor, covering rule) pair with the
exhibit modules whose proofs consume that rule (22 constructors, 25 rule
rows: `Frag.kill` is covered by the static dispose `wps_kill` AND the
dynamic `wps_free`; `Frag.load`/`Frag.store` by the object rule AND the
region rule `wps_load_region_at`/`wps_store_region_at` (kill/free arc K5);
one row each).

**Pure operands are in the covered grammar and carry their own static
fuel bound.** The engine's pure-expression evaluator is fuelled at the
same budget as its redex search (`step_eval_pexpr`/`pull_constrained`
draw from `lemDefaultFuel`), so every `Frag` constructor that evaluates
a pure operand — `if_` (the guard), `run` (the jump arguments), `save`
(the initializers), `load_op`/`memop_op`/`store_op`/`kill_op`/`alloc_op`
(the operands the engine evaluates before dispatching the action) — carries the static
premise `peDepth pe ≤ lemDefaultFuel` per operand, where `peDepth`
(Soundness.lean) is the operand's syntactic depth (1 at a value or a
symbol, `1 + max` at `PEop`/`PEarray_shift`), AND restricts its
operands to the sub-grammar `PePure` the mirror evaluator covers exactly
(values, symbols, the eight mirrored binops — `PePure.op` carries `hop :
isMirroredOp op = true` — and `PEarray_shift`). Verbatim, the premises
of `Frag.store_op`: `(hp2 : PePure pe2) (hp3 : PePure pe3) (hd2 : peDepth
pe2 ≤ lemDefaultFuel) (hd3 : peDepth pe3 ≤ lemDefaultFuel)`; of
`Frag.if_`: `(hpg : PePure g) (hdg : peDepth g ≤ lemDefaultFuel)`; of
`Frag.run`: `(hpes : ∀ pe ∈ pes, PePure pe) (hdep : ∀ pe ∈ pes, peDepth
pe ≤ lemDefaultFuel)`; of `Frag.save`: `(hp : ∀ pe ∈ saveParamPexprs ps,
PePure pe) (hd : ∀ pe ∈ saveParamPexprs ps, peDepth pe ≤ lemDefaultFuel)`.
Like the `pot` bounds below, both are `rfl` for every authored program
(`peDepth_sym_le`, `peDepth_val_le`, `PePure.of_isPePure rfl`) and never
mention the run length; unlike them they live inside `Frag`, so they
appear on no exhibit as a separate hypothesis. The declared grammar is
the mirror's exact domain by the fragment-closure ruling ([USER
2026-09-02]: the fragment is exactly what the mirror covers), which is
what lets mirror completeness classify every operand the mirror does
not evaluate (below).

**Every node of a fragment program carries the empty static annotation
list.** Each `Frag` constructor, and each redex spelling it ranges over
(`storeRedex`, `loadRedex`, `createRedex`, `killRedex`, `killOpRedex`,
`allocRedex`, `allocOpRedex`, `loadOpRedex`, `storeOpRedex`,
`memopRedex`, `pureRedex`, `saveRedex`, `ifRedex`,
`runRedex`, `caseRedex`, and the `Esseq`/`Ewseq`/`Eannot` constructors),
is stated at `Expr []`. The forcing fact: in the general arm of the
engine's `step_ctx` (generated `Core_reduction.lean`, the
`Expr e_annots expr_` match), `get_loc e_annots` reads a source
location from the redex node's annotations and, unless it is a library
location, rewrites the thread's `current_loc`; this package keeps
`currentLoc` in the immutable `MachineCtx` (Step.lean), and
`engine_step_matchU` equates the engine's successor thread with
`M.thread e' ρ'`, whose `current_loc` is `M.currentLoc`. A located node
would falsify that equation. Located Core — in particular every Core
program the C elaborator produces — is therefore outside `Frag`; the
programs proved here are authored Core with empty annotation lists.
The mover is to make `current_loc` live state, part of the runtime
tuple as the environment is.

**In the fragment, mirrored and classified, but covered by NO rule
(kill/free arc K3, the K2 range audit's N-2, decided).** (i) The STATIC
kill of a live `alloc`ated REGION — `kill(static ty, p)` at a region's
base. The engine ACCEPTS it (`killM` short-circuits the dynamic check at
`isDynamic = false`, CerbMem.lean:1573), `Frag.kill` admits it (since K3
it carries no kind premise), `Step.kill` mirrors it and `complete_kill`
classifies its round; but the static dispose rule `kill_atomic` is stated
over the OBJECT bundle `pointsToCell` (a created, typed cell) and the
free rule `free_atomic` over the REGION bundle `regionOwn` (a dynamic,
untyped cell), so no rule applies. A program that static-kills a region
— C's freeing malloc'd storage as if it were automatic — is OUTSIDE the
logic by design; we do not prove such programs. Symmetrically `free(p)`
of a CREATED object has no rule: the engine kills it (UB179a) unless the
base happens to sit in `dynamicAddrs` (the K0 audit's N-1 scenario), and
the logic takes an allocation's origin from the metadata cell, never
from that list. (ii) `alloc(al, n)` at `n ≤ 0` and alignment `al ≤ 1` —
a zero-COST request (`regionCost al n = n.toNat + max al 1 − 1 = 0`; the
engine's `sizeN.toNat` collapses EVERY non-positive size to a
successful size-0 region, so `alloc(4, −7)` is a covered size-0 request
at cost 3 — the K3 range audit's N-2): the budget fragment
`allocBudget 0` is the unit and cannot witness a cursor cell, so
`alloc_atomic` carries `0 < regionCost alignN sizeN` (every positive
size satisfies it, `regionCost_pos`; so does any non-positive size at
`al ≥ 2`). The round is classified (`complete_alloc`: the step, or the
out-of-memory kill), never assumed. (iii) `free(NULL)` — the engine's dynamic no-op
(CerbMem.lean:1562): in `Frag.kill` and mirrored by `Step.kill`, no rule
(nothing is consumed or produced; a client has no reason to write it).
(iv) — formerly K4's finding, a `load` or `store` THROUGH A REGION
POINTER — is CLOSED at K5 (kill/free arc): `regionLoadAt_atomic`/
`regionStoreAt_atomic` (Rules.lean) are typed load/store at any offset
of a live region over the TYPED REGION VIEW `typedRegionView` (Heap.lean
— `pointsToView` with the region cell for the object cell and the
region's size for the layout size), proved once through the generic
live-cell seams `loadM_live`/`storeM_live` at `regionCell a n true`;
faces `wps_load_region_at`/`wps_store_region_at` and, over whole-region
ownership `regionOwn`, `wps_load_regionOwn_at`/`wps_store_regionOwn_at`
(+ total twins). What the ENGINE checks at an untyped allocation
(CerbMem.lean): the dead list (load, :1645), the record's presence
(:1648/:1719), `isInBounds` against the record's SIZE (:1475),
writability (store, :1725) and `isAtomicMemberAccess`, which is `false`
at `alloc.ty = none` (:1619) — NO effective-type check, NO alignment
check: `malloc`'d memory is read and written at any type at any
in-bounds offset, and the rules carry exactly that (the accessed type
enters through its size and its decode/serialization). The chartered
MALLOC'D LINKED LIST is the exhibit (MallocListExhibit.lean).

**Deliberately not here.** Procedures (no call
rule, no return; every program is one `main` body with registered
labels, and `MachineCtx.SeqWF` — empty call stack, startup thread — is
a premise of every adequacy theorem at a general context, discharged at
the two profiles by `spikeCtx_wf`, `procCtx_wf`); `Eunseq`; inside the
mirrored constructs, exactly these absences — `Ewseq` at binder
patterns, `Ecase` with a non-value scrutinee, pure exits beyond
`PEsym`, the memop family beyond `PtrEq`, `PtrEq`'s
differing-provenance nondeterministic fork, and the symbol-binder beta
at annotated values — each an absence of a `Step` rule, not a rule with
a hidden assumption; concurrency, prophecy variables, the C frontend
(programs enter as authored Core in a one-procedure `file` built by
`prodFile`).

## The claim

The target statement shape is

```
s |= P && core_exec(prog, s) ~~> term ==> term = some(s') && s' |= Q
```

for P and Q "just memory + pure properties".

**Where the headline claim rests.** On the total-lane production
statements — `exhibitA_prod` (ProdExhibit.lean),
`fib_certified_production`, `counter_loop_certified_production`,
`list_reverse_certified_production` (ProdLoopExhibit.lean),
`dispose_list_certified_production` (DisposeExhibit.lean) and
`region_loop_certified_production` (RegionLoopExhibit.lean) and
`malloc_list_certified_production` (MallocListExhibit.lean). Their
execution function is the shipped `CerbND.runND (drive fmapEmpty false
file args) (initial_driver_state sup file fs).1`, the composite the
cerberus-lean executable runs, applied to the authored program wrapped
by `prodFile` (the synthetic one-procedure file); no package-defined
driver, discharge or scheduler appears in their statements, and they
carry no termination hypothesis — only the explicit in-budget bounds
`hfuel` where the step count depends on an input, and, where the
program allocates from a size-dependent budget, the BUDGET side
condition that the budget fits the cold-start memory:
`region_loop_certified_production`'s `hB : n.toNat * regionCost al sz ≤
headroom prodMem₀.lastAddress` (in the package's pure vocabulary — its
cost function at its cold-start cursor literal; the K4 range audit's
M-1) and `malloc_list_certified_production`'s `hB : n.toNat * (15 + max
al.toNat 1) ≤ 281474976710647` (the same fact in ENGINE vocabulary: per
node `16 + max(al, 1) − 1` bytes of cursor descent, `281474976710647`
the cold-start cursor's headroom; bridge `ml_budget_bridge`). These
seven are THE root-of-trust exports of this package — the closed
shipped-driver statements. They are reached through `prod_run_eqJ`
(ProdEntry.lean), which is generic collapse machinery rather than a
closed statement: its delivery premise `DriverDoneAt` (ProdLoop.lean)
and its label tie `LabeledAt` are package-defined, and the seven
statements discharge them.

**PROVISIONAL.** Every export stated over `driveU` rather than the
shipped driver — `MemTripleU`, `MemTripleU_alloc`, `SemTripleU`,
`project_triple`, `project_triple_pure`, `project_triple_alloc`,
`project_triple_pure_alloc`, `semantic_triple_soundU`,
`semantic_frameU`, `engine_adequacyU`, `engine_adequacyU_alloc`,
`wpt_engine_boundU`, `wpt_engine_boundU_alloc`, and every exhibit whose
"Execution" column below reads `driveU` — carries the label
PROVISIONAL, in exactly this sense: a sound fact about `driveU`, this
package's loop around the engine's `step_ctx`; not yet the
root-of-trust statement, which is over the shipped driver and awaits
the cerberus-lean fuel-exhaustion outcome
([`../docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md`](../docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md));
restated with no other change when it lands. The obstacle is stated
under "The trust story": the shipped driver's out-of-fuel arm is a
kernel-opaque constant, so no theorem quantifying over all fuels can
classify its outcomes. The PROVISIONAL statements are not deleted:
they are sound, and they are the shape that will be restated.

The partial-correctness realization of the target shape is the triple
`MemTripleU` (Adequacy.lean; PROVISIONAL), produced from an Iris
triple by `project_triple_pure` (both quoted in the walkthrough §1):

| Shape | In the tree |
|---|---|
| `s` | `σ : Mem` = the engine's `CerbMem.MemState`, arbitrary outside the footprint |
| `s \|= P` | `Sat M.tagDefs σ (P ∪ R)` — `Sat` is `Coh` (Heap.lean) by `abbrev`: every footprint cell live, writable, in bounds, exactly those bytes, pairwise disjoint; `R` is the arbitrary rest, returned to the post (the frame is part of the definition) |
| `prog` | `(e, ρ)` at a machine context `M`; `M.thread e ρ` is the engine's `thread_state` |
| `core_exec(prog, s) ~~> term` | `driveU M aids n (M.thread e ρ) σ` — `n` rounds of `step_ctx` followed by request discharge, for every action-id supply `aids` and every `n`; the triple carries no fuel premise |
| `term = some(s')` | `driveU … = .done v σ'`; the other two conjuncts, `≠ .killed r` (no undefined behaviour, no error kill) and `≠ .stuck` (no refusal, no off-protocol step); `.more` (fuel exhaustion) is unconstrained — partial correctness |
| `s' \|= Q` | `ψ R v σ'` for a pure `ψ : CellMap → value → Mem → Prop` |

`project_triple_pure`: under `M.SeqWF`, `Frag e`, `Frag` membership of
every registered label body, and the static fuel bounds `pot e ≤
lemDefaultFuel` and `pot cont ≤ lemDefaultFuel` per registered body
(Potential.lean; `rfl` for authored programs), an Iris triple whose
precondition is footprint ownership `[∗map] i ↦ c ∈ P, cellOwn … i (.own
1) c` and whose framed Iris post pure-entails `ψ R w.val σ'` under the
coupling invariant projects to `MemTripleU M ρ e P ψ`. The conclusion
contains no Iris vocabulary; the one Iris-shaped hypothesis is
discharged for the points-to shapes by `cellOwn_consequence`,
`pointsToCell_consequence`, `cellsOwn_consequence`, `cells_consequence`
and the combinators `pure_`/`sep_`/`or_`/`exists_consequence`.
`project_triple` is the strongest-post form beneath it; `SemTripleU`
(footprint post `Q`, `Sat σ' (Q ∪ R)`) is the cells-shaped instance
(`SemTripleU_iff_Mem`, definitional).

**Allocating programs.** `project_triple_pure_alloc` is the twin whose
Iris precondition is footprint ownership ∗ `allocBudget B` (the
∗-splittable allocation budget every `create` spends, walkthrough §3.2,
§4) and whose conclusion is `MemTripleU_alloc`: `MemTripleU` with the
launch premise `LaunchCoh M.tagDefs σ (P ∪ R) B` in place of `Sat` —
`Sat` plus the GLOBAL MEMORY WELL-FORMEDNESS INVARIANT `MemWF σ`
(Heap.lean: allocation-id discipline, live/dead consistency, pairwise
range disjointness of ALL live allocations, cursor bounds, the
dynamic-address facts — every component an engine fact of the concrete
allocator) plus the budget coupling inequality `B ≤ headroom
lastAddress` (the budget fits below the actual cursor). The premise
genuinely differs (a memory can carry the footprint with its cursor on
top of it), so the allocating triple is a separate definition;
`MemTripleU` implies `MemTripleU_alloc` at every budget
(`MemTripleU_alloc_of_MemTripleU`). The production cold-start memory
satisfies it (`prodMem₀_memWF`, `prodMem₀_launchCoh`, ProdEntry.lean);
`struct_create_store_adequacy` (StructExhibit.lean) is the worked
instance. No other precondition shape is projected: fractional cells,
views and persistent metadata are first strengthened to whole cells by
the assertion laws (`cellOwn_view`, `pointsToCell_combine`).

**Closed programs on the shipped pipeline — the root-of-trust
lane.** For the production statements the execution function is the
shipped composite `CerbND.runND (drive fmapEmpty false file args)
(initial_driver_state sup file fs).1`, reached from the total judgment
through `wpt_driver_done_alloc` (ProdLoop.lean) and `prod_run_eqJ`
(ProdEntry.lean); the statements quantify over the file-system state,
argv and the entry's symbol supply `sup`. They are total statements
(an equation on the singleton execution) because a sufficient fuel is
known; the partial lane's restatement over the same composite is what
the fuel-exhaustion request unblocks.

## The exhibits

Every theorem below is pinned in `Audit.lean` with axioms exactly
`propext`, `Classical.choice`, `Quot.sound`. "Execution" names the
execution function in the statement: `driveU` at `spikeCtx` (the
straight-line context) or at `procCtx p rs` (the context carrying a
procedure symbol and a run state with registered labels), or the
shipped pipeline. Every `driveU` row is PROVISIONAL in the sense
defined under "The claim"; the shipped-pipeline rows are the
root-of-trust exports. The last column lists EVERY hypothesis of the theorem
by name, section variables included; it is read off the
machine-printed statement of every constant in
`docs/2026-09-02_pr3-C-signatures-post.txt` (`scripts/signature_snapshot.lean`),
where section variables appear as leading binders. No statement
carries a premise on the action locations: the engine attaches
`requestLoc th loc` (the redex's own location, or the thread's
`current_loc` at a library location) to every memory request, and
`storeM_loc_irrel`/`loadM_loc_irrel` (Step.lean) show the memory
operations' outcomes do not depend on it, so the certification
equations carry the engine's own conditional and the fragment carries
no location hypothesis. `hcoh` is the seeded-footprint premise
(`Coh`/`Sat`). `∀ x, resolveExtern M.extern x
= x` (on `struct_create_store_wps`) says the program's symbols are not
extern-redirected: the engine resolves every `PEsym` through the file's
extern map with identity fallback (`resolveExtern`, Step.lean), so at
`fmapEmpty` the premise is `rfl` (`resolveExtern_id_of_empty`). No drive
statement carries a fuel hypothesis.

| Theorem (file) | Says | Execution | Hypotheses, exhaustively |
|---|---|---|---|
| `exhibitA_semantic`, `exhibitA_engine`, `exhibitA_total` (Exhibit.lean) | store 7 then load: never kills; delivers `Specified(7)`; the total form is an unconditional `.done` equation at drive length 6 | `driveU spikeCtx` — PROVISIONAL | `_semantic`: `{GF} [SpikeGpreS GF]` (the memory is quantified by `SemTripleU`); `_engine`: `n aids`, memory fixed to the constant `σ₀`; `_total`: `aids` |
| `exhibitB_semantic`, `exhibitB_engine` (Exhibit.lean) | the frame: `⦃x ↦ - ∗ y ↦ a⦄ store(x,7) ⦃x ↦ 7 ∗ y ↦ a⦄` over engine configurations, `y` and all unnamed rest verbatim | `driveU spikeCtx` — PROVISIONAL | `_semantic`: `{GF} [SpikeGpreS GF]`; `_engine`: `n aids` |
| `exhibitC_semantic`, `exhibitC_engine` (Exhibit.lean) | sequenced stores to disjoint cells both land | `driveU spikeCtx` — PROVISIONAL | as B |
| `counter_loop_certified`, `counter_loop_certified_irrelevant_binding` (LoopExhibit.lean) | the first loop: save/guard/store/back edge; the seeded cell's final bytes are data-dependent; run from an entry frame with an unrelated binding | `driveU (procCtx …)` — PROVISIONAL | `loc ann ra mo bty xbty sbty idx addr bs0 n`, `0 ≤ n`, `σ₀`, `hcoh` (the seeded cell), `nsteps aids`; `_irrelevant_binding` adds `junk : value` |
| `fib_certified`, `fib_certified_total` (FibExhibit.lean) | iterative fib delivers `fib n`; total: `driveU … (2 * n.toNat + 4) … = .done (fib n) σ₀` | `driveU (procCtx …)` — PROVISIONAL | `ra ibty abty bbty sbty n`, `0 ≤ n`, `σ₀`; `_certified` adds `nsteps aids`, `_total` adds `aids` |
| `array_sum_certified` (ArrayExhibit.lean) | array walk with pointer arithmetic delivers `vs.sum`, array preserved | `driveU (procCtx …)` — PROVISIONAL | `loc ann ra mo ibty accbty pbty xbty sbty vs id a aty bs`, `hsz : vs.length * 4 ≤ sizeofCtype fmapEmpty aty`, `ety`, `hdec` (each element's 4-byte range reconstructs, by the engine's `reconstructValue` at any side tables, to `MVinteger ety vs[i]`), `σ₀`, `hcoh`, `nsteps aids` |
| `struct_update_certified` (StructExhibit.lean) | two-field struct update at the engine | `driveU spikeCtx` — PROVISIONAL | `{GF} [SpikeGpreS GF]`, `loc ann mo mo' bty id a bs`, `σ₀`, `hcoh`, `n aids` |
| `struct_wps_views`, `cell_read_shared_wps`, `struct_x_read_persist_wps`, `struct_create_store_wps` (StructExhibit.lean) | the view/fraction/persistence laws as clients; allocate-then-initialize from `allocBudget` alone (Iris-level triples) | — (Iris) | all: `{hlc GF} [SpikeGS hlc GF] {M Ls} loc ann`; `_views`: `mo mo' bty id a b0 b1 b2 b3`, the three field lengths, `ev0 evs`; `cell_read_shared`: `pv mo bs bs' ρ`, `htrap`; `_x_read_persist`: `mo id a q dqb ρ`; `_create_store`: `aprov alignN pref mo pbty vbty ev0 evs`, `SymFrame ev0`, `∀ x, resolveExtern M.extern x = x` |
| `struct_create_store_adequacy`, `struct_create_store_adequacy_prodMem₀` (StructExhibit.lean) | allocate-then-initialize as `MemTripleU_alloc spikeCtx spikeEnv prog ∅ [⟨8, structTy⟩] ψ`, an instance of `project_triple_pure_alloc`; `_prodMem₀` fixes the memory to the production cold start | `driveU spikeCtx` — PROVISIONAL | `{GF} [SpikeGpreS GF]`, `loc ann pref mo pbty vbty`; `_prodMem₀` adds `n aids` |
| `alloc_two_creates_wps`, `alloc_create_wpt`, `alloc_create_launch_smoke` (AllocExhibit.lean) | the allocation rules' local consumers; a bare `create` from the cold-start memory delivers a pointer at drive length 2 | `driveU spikeCtx` — PROVISIONAL | `_wps`: `{hlc GF} [SpikeGS hlc GF] {M Ls} al₁ al₂ pref₁ pref₂ bty ev0 evs`; `_wpt`: `{hlc GF} [SpikeGS hlc GF] {M Ls} al pref ρ`; `_launch_smoke`: `pref aids` |
| `alloc_free_wps`, `free_launch_smoke` (AllocExhibit.lean; kill/free arc K3) | allocate a REGION then FREE it: `lets p = alloc(al, n) in free(p)` through the public `wps_alloc`/`wps_kill_eval`/`wps_free` delivers the unit value, the persistent dead region `deadRegion` of some id/base and the spent budget `regionCost al n`; from the cold-start memory `lets p = alloc(4, 8) in free(p)` driven through `wpt_engine_boundU_alloc` delivers `Vunit` at drive length exactly 5 with SOME id in `σ'.deadAllocations` and its record erased — `killM`'s effect on the tables, read off `deadRegion_dead` | `driveU spikeCtx` — PROVISIONAL | `_wps`: `{hlc GF} [SpikeGS hlc GF] {M Ls} hex al n pref hcost ev0 evs hf`; `_launch_smoke`: `pref aids` |
| `alloc_create_kill_wps`, `kill_launch_smoke` (AllocExhibit.lean; kill/free arc K2) | allocate then DISPOSE: `lets p = create(al, int) in kill(static int, p)` through the public `wps_create`/`wps_kill_eval`/`wps_kill` delivers the unit value, the persistent dead cell `deadObj` of some id/base and the spent capacity; from the cold-start memory the same program driven through `wpt_engine_boundU_alloc` delivers `Vunit` at drive length exactly 5 with SOME id in `σ'.deadAllocations` and its record erased — `killM`'s effect on the tables, read off `deadObj_dead` | `driveU spikeCtx` — PROVISIONAL | `_wps`: `{hlc GF} [SpikeGS hlc GF] {M Ls} hex al pref ev0 evs hf`; `_launch_smoke`: `pref aids` |
| `dl_wps`, `dl_wps_emp`, `dl_wpt`, `dl_wps_frame`, `dl_wpt_frame`, `dispose_list_certified_total` (DisposeExhibit.lean; kill/free arc K4) | DISPOSE A LIST — the classical `{list p} dispose(p) {emp}`: the authored loop walks a chain of CREATED nodes (ListRevExhibit's `isList`) and `kill(static node, ·)`s each through the public `wps_kill`/`wpt_kill` at the node cell; `dl_wps`/`dl_wpt` deliver unit and `deadNodes ns` (every node's persistent dead cell), `dl_wps_emp` is the textbook post, the total budget is the DERIVED `12 * ns.length + 6`; the engine equation: from the seeded chain next to an arbitrary frame `R`, `driveU … (12 * ns.length + 6) … = .done Vunit σ'`, every node id in `σ'.deadAllocations` with its record erased, `Sat σ' R` | `_wps`/`_wpt`/`_frame`: Iris (`{hlc GF} [SpikeGS hlc GF] loc ann ra mo cbty bbty nbty ubty ns p rs hQ sbty head`, `_frame` adds `RF`); `_total`: `driveU (procCtx …)` — PROVISIONAL | `_total`: `loc ann ra mo cbty bbty nbty ubty sbty`, `ns head m₀`, `hseed : SeedChain m₀ head ns`, `R`, `hR : m₀ ##ₘ R`, `σ₀`, `hcoh : Sat fmapEmpty σ₀ (m₀ ∪ R)`, `aids` |
| `rl_wps`, `rl_wpt`, `region_loop_certified_total` (RegionLoopExhibit.lean; kill/free arc K4) | N REGIONS FROM ONE LINEAR BUDGET: `save rl(i := n) in if i > 0 then lets p = alloc(al, sz) in lets _ = free(p) in run rl(i − 1) else unit` — the budget `allocBudget (n.toNat * regionCost al sz)` is the LOOP INVARIANT, split per iteration by `allocBudget_split`, spent by the public `wps_alloc`/`wpt_alloc`, each region returned by `wps_free_emp`/`wpt_free_emp`; post `emp`; total budget the DERIVED `7 * n.toNat + 3`; the engine equation: from any memory launching the empty footprint with the budget (`LaunchCoh … ∅ (n.toNat * regionCost al sz)`), `driveU … (7 * n.toNat + 3) … = .done Vunit σ'` — no out-of-memory kill because the budget fits. (The malloc'd LINKED list is the next row — MallocListExhibit.lean, K5, through the region access rules.) | `_wps`/`_wpt`: Iris (`{hlc GF} [SpikeGS hlc GF] loc ann ra al sz pref ibty pbty ubty hcost p rs hQ sbty n`, `_wpt` adds `hn : 0 ≤ n`); `_total`: `driveU (procCtx …)` — PROVISIONAL | `_total`: `loc ann ra al sz pref sbty ibty pbty ubty`, `hcost : 0 < regionCost al sz`, `n`, `hn : 0 ≤ n`, `σ₀`, `hl : LaunchCoh fmapEmpty σ₀ ∅ (n.toNat * regionCost al sz)`, `aids` |
| `ml_wps`, `ml_wpt`, `malloc_list_certified_total` (MallocListExhibit.lean; kill/free arc K5) | THE MALLOC'D LINKED LIST: `save ml(i := n, p := NULL) in if i > 0 then lets q = alloc(al, 16) in lets _ = store(long, q, i) in lets _ = store(node*, array_shift(q, long, 1), p) in run ml(i − 1, q) else lets b = memop(PtrEq, [p, NULL]) in if b then unit else lets Specified(nx) = load(node*, array_shift(p, long, 1)) in lets _ = free(p) in run ml(0, nx)` — ONE label, two phases: `i > 0` allocates a 16-byte REGION node from the split budget, writes the counter (offset 0, `long` — stored but NOT tracked by `isRegionList`: the walk never reads it, and its signed-long decode round trip is not in this tree) and the link (offset 8, `node*`) THROUGH THE REGION (`wps_store_regionOwn_at`, K5) and conses it onto `isRegionList`; `i = 0` walks the list reading each next field through the region (`wps_load_regionOwn_at`) and `free`s each node (`wps_free`, its `deadRegion` kept). Invariant `allocBudget (i · regionCost al 16) ∗ isRegionList p ids ∗ deadRegions done`, `i + |ids| + |done| = n`, `(ids ++ done).Nodup`; post `unit ∗ ∃ ids, |ids| = n.toNat ∧ ids.Nodup ∗ deadRegions ids` — `n.toNat` DISTINCT dead ids (K5.1, the K5 audit's M-1: `deadRegion` is persistent, so without `Nodup` the post would say only that SOME region is dead; distinctness comes from the public `regionOwn_ne`/`regionOwn_deadRegion_ne` at each `alloc` and is carried through the invariant); total budget the DERIVED `25 · n.toNat + 7`; the engine equation: from any memory launching the empty footprint with the budget, `driveU … (25 · n.toNat + 7) … = .done Vunit σ'` with `n.toNat` DISTINCT ids dead and erased in `σ'` | `_wps`/`_wpt`: Iris (`{hlc GF} [SpikeGS hlc GF] loc ann ra mo al pref ibty pbty qbty bbty nbty ubty n p rs hQ sbty`, `hn : 0 ≤ n`); `_total`: `driveU (procCtx …)` — PROVISIONAL | `_total`: `loc ann ra mo al pref sbty ibty pbty qbty bbty nbty ubty`, `n`, `hn : 0 ≤ n`, `σ₀`, `hl : LaunchCoh fmapEmpty σ₀ ∅ (n.toNat * regionCost al 16)`, `aids` |
| `list_reverse_certified`, `list_reverse_demo`, `list_reverse_certified_total` (ListRevExhibit.lean) | in-place reversal of a seeded chain next to an arbitrary disjoint frame — same allocation ids in reversed order, footprint equality on the maps, frame verbatim, at every drive length; total at `13 * ns.length + 7`; the demo fixes a 3-node chain | `driveU (procCtx …)` — PROVISIONAL | `loc ann ra mo pbty cbty bbty nbty ubty sbty`, `ns head m₀`, `hseed : SeedChain m₀ head ns`, `R`, `hR : m₀ ##ₘ R`, `σ₀`, `hcoh : Sat fmapEmpty σ₀ (m₀ ∪ R)`; `_certified` adds `nsteps aids`, `_total` adds `aids`; `_demo` replaces `ns head m₀ hseed` by the 3-node constants |
| `tree_rotate_certified`, `tree_rotate_certified_total` (TreeRotExhibit.lean) | binary-tree right rotation at the same statement shape; total at drive length 19 | `driveU spikeCtx` — PROVISIONAL | `loc ann mo xbty ybty bbty ubty`, `idx idy vx vy ta tb tc px m₀`, `hseed : SeedTree m₀ px (.node idx vx (.node idy vy ta tb) tc)`, `R`, `hR`, `σ₀`, `hcoh`; `_certified` adds `sbty`, `n aids`; `_total` adds `aids` |
| `case_certified`, `wseq_certified` (CaseExhibit.lean, WseqExhibit.lean) | the `Ecase`/`Ewseq` consumers | `driveU spikeCtx` — PROVISIONAL | `{GF} [SpikeGpreS GF]`, `v` resp. `v1 v2`, `σ₀ n aids` |
| `diverge_total_unprovable` (DivergeExhibit.lean) | the negative test: a total derivation for the self-jump loop is `False` | — | `{GF} [SpikeGpreS GF]`, `ra σ₀ m₀`, `hcoh : Coh fmapEmpty σ₀ m₀`, and the statement's own quantifiers `Ls Ψ k` and the derivation from `m₀`'s cell ownership |
| `exhibitA_prod` (ProdExhibit.lean) | the production run of `lets p = create(4,int) in lets _ = store(int, p, 7) in load(int, p)` is the singleton `Active` execution delivering 7, the final memory holding 7's image at the program's own cell | shipped pipeline — ROOT OF TRUST | `sup fs args` |
| `fib_certified_production`, `counter_loop_certified_production`, `list_reverse_certified_production` (ProdLoopExhibit.lean) | the loop programs on the shipped pipeline; counter and reversal bind their engine-created cells and enter their loops through `save` with live initializers | shipped pipeline — ROOT OF TRUST | fib: `sup ra n sbty ibty abty bbty`, `0 ≤ n`, `2 * n.toNat + 6 ≤ lemDefaultFuel`, `fs args`; counter: `sup ra mo bty xbty cbty sbty n`, `0 ≤ n`, `6 * n.toNat + 8 ≤ lemDefaultFuel`, `fs args`; reversal: `sup ra mo bty sbty pbty cbty bbty nbty ubty fs args` |
| `dispose_list_certified_production` (DisposeExhibit.lean), `region_loop_certified_production` (RegionLoopExhibit.lean) | kill/free arc K4 on the shipped pipeline: BUILD two nodes with `create`s (the list-reverse production's prefix, restated generically in its continuation as `lrProdPrefix_wpt`) then DISPOSE the list — EXACTLY ONE Active execution delivering `Vunit` whose final memory has two DISTINCT allocation ids in `deadAllocations` with their records erased (the proof witnesses them as the two created nodes; the statement names no node); `n` `alloc`/`free` pairs from one budget — EXACTLY ONE Active execution delivering `Vunit` (no readout of the final table: the regions are freed through the `_emp` faces, which drop the dead knowledge) | shipped pipeline — ROOT OF TRUST | dispose: `sup ra mo bty sbty cbty bbty nbty ubty fs args`; region loop: `sup ra al sz pref sbty ibty pbty ubty`, `hcost : 0 < regionCost al sz`, `n`, `hn : 0 ≤ n`, `hB : n.toNat * regionCost al sz ≤ headroom prodMem₀.lastAddress`, `hfuel : 7 * n.toNat + 5 ≤ lemDefaultFuel`, `fs args` |
| `malloc_list_certified_production` (MallocListExhibit.lean; kill/free arc K5) | THE MALLOC'D LINKED LIST on the shipped pipeline: EXACTLY ONE Active execution delivering `Vunit` whose final memory has `n.toNat` DISTINCT allocation ids (`ids.Nodup`, K5.1) in `deadAllocations` with their records erased (the proof witnesses them as the freed nodes; the statement names no node) — every `alloc` through the public `wpt_alloc`, every field write through `wpt_store_regionOwn_at`, every next-field read through `wpt_load_regionOwn_at`, every `free` through `wpt_free` | shipped pipeline — ROOT OF TRUST | `sup ra mo al pref sbty ibty pbty qbty bbty nbty ubty`, `n`, `hn : 0 ≤ n`, `hB : n.toNat * (15 + max al.toNat 1) ≤ 281474976710647` (the budget fits the cold start, in ENGINE vocabulary), `hfuel : 25 * n.toNat + 9 ≤ lemDefaultFuel`, `fs args` |
| `counter_loop_certified_registration` (ProdEntry.lean) | the counter loop with its label map derived from the shipped registration (`collect_labeled_continuations_NEW`) | `driveU (procCtx mainSym …)` — PROVISIONAL | `sup loc ann ra mo bty xbty sbty idx addr bs0 n`, `0 ≤ n`, `σ₀`, `hcoh`, `nsteps aids` |

## The trust story

**Two trust claims.**

1. **The closed-program exports have Iris-free statements.** Their
   execution functions are two, and the two lanes have different
   standing. THE ROOT-OF-TRUST LANE: in the production statements
   (`exhibitA_prod`, `*_production`) the execution function is the
   shipped `CerbND.runND (drive fmapEmpty false file args)
   (initial_driver_state sup file fs).1` — the genuine Cerberus
   driver, total statements only. THE PROVISIONAL LANE: in the drive
   statements (`MemTripleU`, `MemTripleU_alloc`, `SemTripleU`, every
   `*_certified`, `*_total`, `*_engine`) it is `driveU`
   (Adequacy.lean): this package's definition of the sequential
   driver's round loop, iterating the engine's `step_ctx` and
   discharging each request by `dischargeStep` (Soundness.lean), a
   hand-written projection of the driver's `action_request_sequential2`
   onto (thread state, memory). Each such statement is PROVISIONAL: a
   sound fact about `driveU`, this package's loop around the engine's
   `step_ctx`; not yet the root-of-trust statement, which is over the
   shipped driver and awaits the cerberus-lean fuel-exhaustion outcome
   (`../docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md`);
   restated with no other change when it lands. `driveU` is tied to
   the shipped driver by `loop_step_frag` (DriverCollapse.lean) — one
   production scheduler round is one `driveU` round — but only at
   configurations where the mirror `Step` steps, and that tie is
   consumed only by the total judgment (`wpt_driver_done`,
   `wpt_driver_done_alloc` → `prod_run_eqJ`). No partial-correctness
   statement about the shipped pipeline is proved, and none can be by
   this route today: at insufficient fuel the production driver's
   value is LemLib's `fuelExhausted`, a wrapper around the
   kernel-opaque `fuelExhaustedWith`, about which nothing is provable
   — the semantics-side limitation the request asks the cerberus-lean
   team to lift (a transparent, distinguished fuel-exhaustion outcome
   in the driver monad); no package-side workaround driver is built.
   What the mirror-to-engine connection establishes, in the words of
   the 2026-09-02 audit: "a sound Iris program logic for the package's
   restricted relational mirror, with a verified forward connection
   to successful Cerberus engine rounds on proved-safe executions" —
   `engine_step_matchU` is one-directional (mirror step ⇒ shipped
   round: one iteration of the shipped driver's thread loop,
   `CerberusRound`, Round.lean — stated in the driver's own vocabulary,
   `dischargeStep` being a proof device only), and
   `frag_round_complete` is the completeness direction: where the
   mirror is stuck, the shipped round is a classified refusal
   (`ShippedRefusal`: ILLTYPED / ILLTYPED-at-distance-one / KILL / FORK /
   PANIC) or the configuration is in the RESIDUAL (`OpenRound`, two
   arms: an operand containing a LEAF the engine accepts where the
   mirror evaluator does not evaluate — a procedure-named symbol, a
   binop at two floats, `OpEq` at two ctypes — whose whole-operand
   outcome is NOT characterized (the classifier `evalClass` answers
   `.uncovered` at the first such leaf and carries no engine claim; the
   engine may then succeed, kill, or panic), and a jump with surplus
   arguments; the register below), so the logic is SOUND and COMPLETE
   for the declared fragment up to that residual — "mirror steps iff
   the engine has a successful deterministic round, on the declared
   fragment; every stuck configuration classified", with the two
   disclosed exceptions to the iff stated in the same breath: the
   REMOVE-ANNOT round (an annotated value's annotation is stripped by an
   engine round the mirror treats as a value step, `value_annot`) and
   `error_next` (an engine SUCCESS round into a configuration whose next
   round is ILLTYPED, filed under refusals). Every operand the
   classifier REJECTS is a proved engine KILL; operands it leaves
   UNCOVERED are not characterized (the residual is a superset of the
   engine-accepted shapes). The remaining vocabulary
   is the pure readout predicates (`Sat`/`CellCoh`, `SeedChain`,
   `SeedTree`, `readBytesFrom`) and the authored programs. iris-lean
   appears only inside the kernel-checked proof terms and contributes
   no axiom: every export's axiom set is exactly `propext`,
   `Classical.choice`, `Quot.sound` (`Audit.lean`). For these
   statements iris-lean is checked, not trusted.
2. **The reusable rules are stated in Iris.** `pointsToCell`,
   `cellOwn`, `allocBudget`, the WP and BI connectives, and `CohG` (which,
   with `metaInterp`/`byteInterp`, appears in the premises of the
   projection theorems and the readout/consequence lemmas — the one
   documented exception to the public/internal line of `API.lean`,
   under the rule that a client discharges these only through the
   public `*_consequence` lemmas, never by opening them). This must-read set
   is the specification idiom, and the one sense in which iris-lean
   is in the trust base: definitions to read, not axioms to accept.

**What you are asked to take on faith.**

- *The Lean kernel*, and the three classical axioms.
- *cerberus-lean's generated semantics is the semantics you care
  about.* The Lean port and the OCaml Cerberus, both generated from
  the same Lem model, are run on the same programs and their verdicts
  compared against pinned baselines: the record at the pin
  (`../.cerberus-ws/lean_frontend/VALIDATION.md`) lists the 106-program
  upstream minimal suite (106/106), a 213-test CN corpus (213/213), a
  16-URI libxml2 corpus (16/16 byte-identical), 1,669 csmith programs
  at a classified baseline, and a 2,186-file upstream CI sweep with
  zero mismatches among its 1,316 comparable files. This samples
  behaviour; it is not an equivalence proof, and the OCaml oracle
  stays on the trust boundary. Neither the semantics workspace nor
  its lem runtime (`LemLib`) contains an `axiom` declaration; the
  semantics tree does contain one generated `sorry` (next bullet). The
  engine does declare kernel-opaque constants (`opaque`, mostly with
  `@[implemented_by]` bodies): they enter no axiom cone and cannot be
  unfolded, so a theorem can only hold for every value of them. The
  opaques reached by the export cones were measured
  (`docs/2026-09-02_qa2-notes.md`): `CerbGlobal.current_execution_mode`,
  `CerbGlobal.using_concurrency`, `CerbGlobal.has_switch` and
  `CerbGlobal.is_CHERI` (production statements only, through the
  shipped driver's code, on paths the single-threaded run never
  takes), `CerberusImpl.typeof_enum` (via `sizeofCtype`'s enum arm),
  `CerberusFresh.digest`, LemLib's `failwithI` and `fuelExhaustedWith`,
  `CerbMem`'s private `beqMemValueSafe`, `normalise_ctype`,
  `Core.instBEqCore_base_type.beq`. The fuel and well-formedness
  premises below are how the statements stay away from
  `fuelExhaustedWith` and `failwithI`.
- *The one known admission in the pinned semantics tree.* The pinned
  cerberus-lean tree contains one generated admission: two `(sorry :
  String)` terms in the debug-log branch of `auxAddToRfLoad` in the
  generated concurrency model (`Cmm_op.lean`), which Lean reports as
  `declaration uses sorry` during the build. It is outside every
  current export cone: the package sweep (`Audit.lean`) establishes
  that `sorryAx` reaches no `CerberusHeapLang` constant. Concurrency is
  out of scope for this package. The admission must be closed upstream
  or separately bounded before any concurrency or whole-engine claim
  is made on this semantics; it is reported to the cerberus-lean team
  (`../docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md`).
- *Which Cerberus configuration.* Cerberus is switch-configured (PNVI
  variants, strict pointer arithmetic, …). The statements pin: the
  tag-definition environment is `fmapEmpty` and concurrency is off
  (`drive fmapEmpty false …` in every production statement;
  `spikeCtx`/`procCtx` carry `tagDefs = fmapEmpty`); the Lean `CerbMem`
  references no `CerbGlobal` constant, so
  `loadM`/`storeM`/`allocateObject`/`eqPtrval` are switch-independent
  by construction; the one configuration read on a proved path, the
  driver's `current_execution_mode`, is discharged for both values by
  `cases` on the opaque test (`driver2_done`, DriverCollapse.lean); the
  implementation-defined layout is the port's `CerberusImpl`, the one
  the OCaml oracle is validated against. So every export holds under
  every switch setting and every execution mode, at empty tag
  definitions, single-threaded.
- *The pure readout predicates* say what this document says they say:
  `driveU`, `dischargeStep`, `Sat`/`Coh`/`CellCoh`,
  `SeedChain`/`SeedTree`, and the authored program terms; the
  walkthrough §2 prints them. A wrong definition here would make a
  theorem true but irrelevant.

**Registered divergences and limitations** — each on the face of the
theorems:

| Divergence / limitation | Discharge / mover | Home |
|---|---|---|
| Fuel: the engine's `get_ctx` is fuel-bounded (`lemDefaultFuel = 10^6`) with an opaque exhaustion leaf, so the projection theorems carry the static premises `pot e ≤ lemDefaultFuel` and `pot cont ≤ lemDefaultFuel` per registered body (never a bound on the drive length); production statements carry `k + 2 ≤ lemDefaultFuel` for the certified step count; the shipped driver's OWN fuel arm is kernel-opaque, which is why the partial lane is PROVISIONAL | a fuel-irrelevance theorem for `get_ctx`; for the driver's fuel, the fuel-exhaustion request to the cerberus-lean team | `Soundness.lean` header ("FUEL HONESTY"), `Potential.lean`; `../docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md` |
| The fragment is annotation-free (`Expr []` at every node); located Core is outside `Frag` | make `current_loc` live state | "Scope, exactly"; `Soundness.lean` `Frag` header |
| Synthetic Core entry: authored Core wrapped by `prodFile`, not C through the frontend; the loop programs' label maps are nevertheless computed by the shipped registration (`*_labeledAt_production`, `LabeledAt`) | a C-frontend entry | `ProdEntry.lean` |
| Well-formedness by shape: `MachineCtx.SeqWF` and cons-shaped environment stacks — the engine's panic channels excluded by shape, never absorbed. Action locations carry no premise: the certification equations state the request at the engine's own `requestLoc th loc`, and `storeM_loc_irrel`/`loadM_loc_irrel` (the memory operations use the location only in the kill payload) transport the mirror's premise to it | by design | `Step.lean`, `Soundness.lean` |
| The tag-definition environment is an explicit parameter of the heap predicates (`pointsToCell tds …`, `M.tagDefs`); the demos state footprints at `fmapEmpty` | by design: a program-wide constant of the language instance | `Heap.lean` header |
| Memory orders accepted arbitrarily (`Step.store`/`wp_store` at any `memory_order`) | mirror-true: the sequential driver drops `mo` (`action_request_sequential2`) | `Step.lean` |
| Mirror completeness holds on the DECLARED FRAGMENT up to a two-arm RESIDUAL (`OpenRound`, Round.lean; `frag_round_complete`; fragment closure 2026-09-02): `eval_uncovered` — an operand in the covered grammar CONTAINING A LEAF the engine's evaluator accepts where the mirror evaluator does not evaluate (a symbol unbound in the environment but naming a `Proc` of the file; one of the eight mirrored binops at two floating-point operands; `OpEq` at two ctypes — environment/file-dependent, the offending operand carried as witness, `evalClass … = .uncovered`); the classifier answers `.uncovered` at the FIRST such leaf and carries NO engine claim about the whole operand, so the arm's whole-operand outcome is NOT characterized — the engine may succeed, KILL on a later type error (`f + 1` with `f` a `Proc`-named unbound symbol is `PePure`, classified `.uncovered`, killed by the engine as `Illformed_program … ill-typed PEop` — 2026-09-03 audit, by execution) or PANIC (a float guard under `Eif`): every operand the classifier REJECTS is a proved engine KILL, operands it leaves UNCOVERED are not characterized, the residual is a SUPERSET of the engine-accepted shapes; and `run_surplus` — a jump with more arguments than the registered label's parameters whose zipped arguments evaluate and whose surplus does not (label-map-dependent). Everywhere else a mirror-stuck fragment configuration is an engine refusal in the engine's vocabulary (`ShippedRefusal`: ILLTYPED `[Step_error2 msg]`; ILLTYPED AT DISTANCE ONE — a successful round into the ill-typed load/store the engine reports on next; KILL `NDkilled r` from the shipped `advance_step`, memory kills through `liftMem` and pure-evaluator kills `Other (DErr_core_run err)` through `liftCore_run`; FORK ≥ 2 `CerbND.runND` executions; PANIC the engine's own `failwithI`, incl. the no-current-procedure lookup key). The former gaps (a) LETS-ANNOT at the symbol binder and (c) the operand grammar were closed by NARROWING `Frag` (`BareHead`, `PePure` everywhere) — fail-closed, per the ruling | the residual is not removable by a syntactic narrowing; the mover for `eval_uncovered`'s characterization is `evalClass` computing the engine's value at the three leaf shapes (reserving `.uncovered` for the leaf itself, the downstream rejections under the KILL bridge); a complete mirror evaluator (`M.file` threaded into `evalPexpr`, the float/ctype arms) would move `eval_uncovered` into `Step`; a prefix-evaluating `Step.run` would move `run_surplus` | `Round.lean` (`OpenRound`), `EvalClass.lean`; `ARCHITECTURE.md` §2, §7; `docs/2026-09-02_fragment-closure-notes.md` |
| The global memory well-formedness invariant `MemWF` (Heap.lean) is in the state interpretation (`CohG.wf`) and the launch premise (`LaunchCoh.wf`): allocation-id discipline, live/dead consistency, pairwise range disjointness of ALL live allocations, cursor bounds, and the dynamic-address facts — each an engine fact cited in the section header; fresh = disjoint from EVERY live allocation of the state (`create_fresh_global`), not only from the tracked footprint; the cold-start state satisfies it (`prodMem₀_memWF`); `loadM`/`storeM`/`allocateObject`/`killM` preserve it (`MemWF.loadM`/`MemWF.storeM`/`MemWF.allocateObject`/`MemWF.killM`). Two honest qualifications: (i) it is carried under cursor PRESENCE — the cursor-free launches (`MetaByteOf.cohG`, from `Coh` alone) have no `MemWF` premise, so non-allocating programs owe nothing and the non-allocating exports' texts are unchanged; (ii) the dynamic-address component is what the engine maintains (`dyn_lo`, `dyn_disj`), NOT "every dynamic address is a live base" — `killM` never removes an address from `dynamicAddrs` (CerbMem.lean:1576-1578) | CLOSED at K3: `MemWF.allocateRegion` is proved and pinned — every memory operation of the fragment (`loadM`/`storeM`/`allocateObject`/`allocateRegion`/`killM`) has its preservation theorem; K3 also added the engine invariant `la_pos : 0 < lastAddress` (both cursor writers guard `alignedAddr ≠ 0`; the K2.5 range audit's M-2), which is what prices a zero-size region correctly | `Heap.lean` (section "The global memory well-formedness invariant"), `Adequacy.lean` (`LaunchCoh` section); walkthrough §4 |
| Arrays are one allocation, not a ∗ of per-element cells: the engine bounds-checks against the pointer's provenance allocation and `arrayShiftPtrval` preserves provenance | forcing fact about Cerberus; per-element structure lives in the invariant + decode premises | `ArrayExhibit.lean` |
| Allocation metadata at a fraction as the exclusivity anchor AND the liveness token: the cell carries `alive` (RefinedC's `al_alive` and `freeable` collapsed into one cell — Cerberus erases the record on kill, so persistent-past-death metadata has no referent); the STATIC kill rule flips it (K2: `kill_atomic`/`wps_kill`/`wpt_kill` consume `pointsToCell … (.own 1)` and hand back at most `deadObj`; `wps_kill_emp`/`wpt_kill_emp` are the textbook `{p ↦ -} kill(p) {emp}`); the byte fragments are dropped, sound because `killM` leaves the bytemap alone and addresses are never reused (`CohG.kill`) | LANDED at K3: the dynamic kill `free_atomic`/`wps_free`/`wpt_free` over `regionOwn … (.own 1)` is the same ghost update, handing back at most `deadRegion`; the dynamic check `killM` makes (:1573) is passed through the cell's `dynamic` flag (`killM_success_dynamic`), never through `dynamicAddrs` | `Heap.lean` header, "THE THREE ALLOCATION FACTS"; Rules.lean `kill_atomic` |
| Allocation capacity is the ∗-SPLITTABLE BUDGET `allocBudget n` (K2.5): `allocBudget (a + b) ⊣⊢ allocBudget a ∗ allocBudget b`, one `create` of `ty` at alignment `al` spends `allocCost = sizeof ty + max(al, 1) − 1` — the engine's worst-case cursor descent, so the bound is CONSERVATIVE by up to `align − 1` bytes per allocation (an ordered plan could fit where the summed costs do not; the exact descent depends on the cursor's residue modulo the alignment, i.e. on the request order). RefinedC has no capacity resource at all (Caesium never refuses an allocation) | the exact order-dependent descent is not expressible order-free; the slack is the price of the classical additive shape and is irrelevant at realistic cursors (the cold-start headroom is `2^48 − 9`) | `Heap.lean` ("The allocation budget"); walkthrough §4; `docs/2026-09-03_k2.5-notes.md` |
| Read-only allocations ARE describable (K1): `MetaCell.readonly` is coupled to `Allocation.isReadonly`; `readonlyCell tds pv dq ty bs` is the read-only points-to, with `load_atomic_readonly` (loads) and NO store rule — the engine kills a store to a read-only allocation with `MerrWriteOnReadOnly kind` (`storeM_readonly_kills`, CerbMem.lean:1724-1725), stated as a fact, not absorbed. Honest qualification: no rule of this fragment MINTS a `readonlyCell` — `create` is `allocateObject … none none` (writable, :1490-1492) and the launch footprint pins `.IsWritable` | a `create_readonly`/string-literal rule (spec addition) when those constructs join the fragment | `Heap.lean` (section "The K1 bundles"), `Rules.lean` (`load_atomic_readonly`) |
| Typed access THROUGH A REGION POINTER is type-blind in the engine (K5): at an untyped allocation `loadM`/`storeM` check the dead list, the record, bounds against the record's SIZE and writability; `isAtomicMemberAccess` is `false` at `alloc.ty = none` (CerbMem.lean:1619); no effective-type or alignment check exists. So the region access rules `regionLoadAt_atomic`/`regionStoreAt_atomic` are stated at ANY accessed type at ANY in-bounds offset over the TYPED REGION VIEW (the object view with `regionCell` for `objCell`), proved through the same seams `loadM_live`/`storeM_live` as the object rules, and a region is carved into typed fields by `typedRegionView_split`/`_join` — `malloc`'d memory as C has it | forcing fact about Cerberus (the concrete memory model tracks no effective types); RefinedC's `ty_own` at a `malloc`'d block is likewise layout-free | Heap.lean "The typed region view"; Rules.lean "THE REGION ACCESS RULES"; MallocListExhibit.lean |
| The `Frag.case_value` premise `hbsz` (the selected branch's `esize` is bounded by the case node's) is carried, not proved. The equation whose proof would discharge it is `esize (subst_sym_expr x v e) = esize e` (with its mutual twin for `esizeAlts`): `esize` inspects only expression constructors and `subst_sym_expr` substitutes only into pure expressions. The obstacle: the engine's `subst_sym_expr` is `subst_sym_expr_lemFuel lemDefaultFuel`, a fuel-indexed recursion over the whole generated Core AST, so the proof is a fuel-indexed induction over that mutual recursion (`generic_expr`/`generic_pexpr`/patterns) — measured, not attempted. `rfl` for authored programs | that induction | `Soundness.lean` (`Frag.case_value`), `CaseExhibit.lean` header |
| The canonical-annotation value protocol: the pure and annotation rules are stated at `Expr []` because that is where the mirror's values live; the annotation-generic forms are false | by design | `Step.lean` header |

**One reference relation.** The mirror's only reference is the shipped
round `CerberusRound M` (Round.lean): one iteration of the shipped
driver's thread loop — the engine's step list, `can_advance`,
`advance_step` — stated in the driver's own vocabulary at every
embedding driver state, with no fuel dependency. No other relational
semantics is referenced or bridged, and none is needed for the root of
trust, which is the engine.

## The trust diagram

Every theorem named on an arrow has axiom set exactly `propext`,
`Classical.choice`, `Quot.sound` (`Audit.lean`: 165 export pins at the
time of writing; every theorem of every module bounded). "Frag" = the fragment `Frag` at a
`SeqWF` context with a cons-shaped environment; "labels" = every
registered label body in `Frag` with its own static bound
(`hQf`/`hQpot`). Arrows point the way meaning flows: a proof at the
source becomes a fact at the target.

```text
 TRUSTED ─────────────────────────────────────────────────────────────────
   cerberus-lean generated Core types + engine functions
   (step_ctx, action_request_sequential2, loadM/storeM/allocateObject,
    runND, drive, initial_driver_state)             + differential validation
 ─────────────────────────────────────────────────────────── kernel-checked
        │
        │  CerberusRound M  (Round.lean) — the reference relation: ONE ITERATION
        │    of the shipped driver's thread loop (step_ctx → can_advance →
        │    advance_step), in the driver's own vocabulary; the mirror's ONLY reference
        │  Step M  (Step.lean) — the hand-written mirror; interior, zero authority
        │    certified: engine_step_matchU  Step ⇒ shipped round  [Frag]
        │      (step_iff_cerberusRound: two-sided GIVEN a mirror step);
        │    COMPLETE on the declared fragment up to the residual: frag_round_complete
        │      mirror stuck ⇒ ShippedRefusal (ILLTYPED/ILLTYPED-next/KILL/FORK/PANIC)
        │                      ∨ OpenRound (eval_uncovered / run_surplus)
        │      (cerberusRound_classify: value_done/value_annot/step/refused/open_)
        ▼
   iris-lean Language instance over Step   (Lang.lean: instance Language CoreRt
     Mem Empty CoreRVal; NO Language.Context — Erun discards its context)
        ▼
   state interpretation + raw resources   (Heap.lean: SpikeState / CohG over the
     real MemState; bytesOwn, metaOwn, cursorOwn → pointsToView, cellOwn,
     pointsToCell, allocMeta, locInBounds; allocBudget under B ≤ headroom)
        ▼
   the small axioms, proved once   (Rules.lean: AtomicStep — store_atomic,
     load_atomic, storeAt_atomic, loadAt_atomic, create_atomic, each one
     unfolding against Step + the real storeM/loadM/allocateObject; lifted by
     wp_of_atomic / wps_of_atomic / wpt_of_atomic.  wp_store, wp_load at the
     raw WP.  No raw-WP sequencing rule: false at a populated label map)
        ▼
   the two judgments   (Wps.lean: wps = guarded fixpoint; wps_* rules,
     wps_create, blockSpecs_intro, wps_frame_labels; wps_sound ⇒ raw WP  [Löb])
                       (Wpt.lean: wpt by recursion on the budget; wpt_* rules,
     wpt_create, blockSpecsT_intro, wpt_frame_labels; wpt_sound ⇒ Iris TWP)
        │                                        │
        │ partial                                │ total
        ▼                                        ▼
   Iris adequacy                            budget induction AGAINST THE ENGINE
   (Adequacy.lean: spike_step_adequacy =    (TotalAdequacy.lean: wpt_drive_aux —
    wp_strong_adequacy_gen, ghost state      outcomesU_of_step (the device) discharges
    CONSTRUCTED by genHeap_init;             one driveU step per budget unit; no Iris adequacy in
    launchResources under LaunchCoh mints    the cone; wpt_sound is the Iris collapse)
    the cursor and grants allocBudget B)
                          [Frag + labels]                          [Frag + labels]
        ▼                                        ▼
   drive statements — PROVISIONAL, over driveU   (engine_adequacyU ⇒ driveU never kills/derails, readout at
     .done;  project_triple_pure ⇒ MemTripleU;  project_triple_pure_alloc ⇒
     MemTripleU_alloc;  wpt_engine_boundU, wpt_engine_boundU_alloc ⇒
     driveU … k = .done v σ' unconditionally)                  [Frag + labels]
        ▼
   generic driver collapse   (DriverCollapse.lean: loop_step_frag, driver2_done,
     finalize_done — proved from the driver's OWN round functions;
     ProdLoop.lean: wpt_driver_done(_alloc) ⇒ DriverDoneAt;
     ProdEntry.lean: prod_run_eqJ ⇒ runND (drive …) (initial_driver_state
     sup …).1 = [(Active dres, [], dst')])         [labels; k + 2 ≤ lemDefaultFuel]
        ▼
   whole-program production statements — THE ROOT-OF-TRUST EXPORTS
     (exhibitA_prod, fib_certified_production,
     counter_loop_certified_production,
     list_reverse_certified_production,
     dispose_list_certified_production,
     region_loop_certified_production,
     malloc_list_certified_production)                          [∀ sup fs args]
```

What the diagram does not contain: a C frontend; any statement about
`.more` (fuel exhaustion); any partial-correctness statement about the
shipped pipeline (the PROVISIONAL lane's restatement awaits the
fuel-exhaustion request); any engine fact at a mirror-stuck
configuration beyond the four refusal rows.

## The logic

Two label-context judgments over iris-lean's WP — the partial judgment
`wps` (Wps.lean) and the total judgment `wpt` (Wpt.lean) — and beneath
them the small axioms, each proved once as an atomic step specification
`AtomicStep` (Rules.lean) and lifted to every judgment by
`wp_of_atomic`, `wps_of_atomic`, `wpt_of_atomic`. Frame and consequence
at the raw WP are iris-lean's own `wp_frame_r`/`wp_mono`; there is no
raw-WP sequencing rule — at a populated label map it is false (a jump
discards the sequencing context), which is why the label-context
judgments exist. The rule set, one line per family with every theorem
named, is the public/internal table in `API.lean`'s header, maintained
once; the walkthrough §3 quotes the small axioms, frame, create, one
loop rule and the total judgment verbatim. The families: the five
atomic specifications and their raw-WP and judgment faces (with the
`_plain` forms for annotation-insensitive posts); allocation
(`wps_create`/`wpt_create` from `allocBudget`, with the plan-shaped
readings `wps_create_of_plan`/`wpt_create_of_plan`); frame across back edges
(`wps_frame_labels`/`wpt_frame_labels` through the framed label
context); consequence (budgets are upper bounds, `wpt_mono_k`);
sequencing at the three binder shapes and `Ewseq`; conditionals with
the guard's verdict as a pure premise (`wps_if`) and value-scrutinee
case; loops (`wps_save`/`wps_run`/`blockSpecs_intro`, the total twins
with the mandatory decrease `1 + m ≤ k`); the total judgment's collapse
`wpt_sound` and its negative test `diverge_total_unprovable`; operand
evaluation, the `PtrEq` memop and the value protocol; the assertion
laws; and the environment laws (`SymFrame`, `envAdd_lookup`).

Every rule in that table is consumed by an exhibit (the capability
manifest reports the fragment rows), except the laws kept as laws of the
logic: `allocMeta_agree`, `allocBudget_weaken`/`allocBudget_le`, the
plan-shaped readings `wps_create_of_plan`/`wpt_create_of_plan`, and the raw-WP `wp_load`
(the exhibits consume `wps_load`; its sibling `wp_store` is consumed by
`provenB`, Exhibit.lean). Representation predicates are ordinary
structural recursion — `isList` (ListRevExhibit.lean) is
identity-indexed (each node = allocation id × value) and unframed; the
arbitrary frame is added afterwards by `wps_frame_labels`/
`wpt_frame_labels` (`lr_wps_frame`, `lr_wpt_frame`).

## The public API, and how a client is written

`API.lean` is the public surface as one import (`import
CerberusHeapLang.API`). Its header is the public/internal table —
public: the pointer/location assertions and their laws, the
side-condition vocabulary, the environment laws, the atomic
specifications and the raw-WP small axioms, both judgments with their
rule sets, the adequacy exports and the projections (PROVISIONAL
where over `driveU`), and the pure memory view `CellCoh`/`Sat` — the
vocabulary of the boring post; internal (visible, since Lean imports
are transitive, but not part of the surface): `CohG` and the ghost
carrier, the allocator cursor and the budget authority `budgetAuth`
(clients receive `allocBudget B` from the launchers and never mint it),
`Step`/Soundness/
Round, the judgment unfoldings, the `memM` lemmas. The one documented
exception: `CohG`, `metaInterp`, `byteInterp` appear in the premises
of the projection theorems and the readout/consequence lemmas, under
the rule that a client discharges these only through the public
`*_consequence` lemmas.
The worked example is `Examples/ReadinessSmoke.lean`: importing only
the API, it defines a two-field object predicate `twoField` (two
`pointsToView`s at offsets 0 and 8 sharing the metadata at half
fraction) and derives its load, store and allocate rules from the
public rules alone (`twoField_load_x/_y`, `twoField_store_x/_y`,
`twoField_create`: `wps_load_at`/`wps_store_at`, the y field addressed
by the engine's own `arrayShiftPtrval` through `cellPtr_arrayShift`,
`wps_create` + `cellOwn_view` + one `pointsToView_split`). It has zero
direct references to the ghost maps, `CohG`, the cursor, `Step` or the
judgment unfoldings (`scripts/parametric_inventory.lean`, on demand).

## How to build and verify

From the repository root (offline; dependencies resolve through the
container's git redirects, which `scripts/capped` loads):

```bash
scripts/setup-cerberus-dep.sh        # once: the pinned semantics workspace
cd cerberus-heaplang
../scripts/capped ~/.elan/bin/lake build
```

A green build is the verification run: it elaborates every proof
through the Lean kernel and then `Audit.lean` (the last import of the
library root), which (1) pins the exact axiom set of every public
export to `propext`, `Classical.choice`, `Quot.sound`, (2) bounds every
theorem of every module by those three — internal details (private
names, proof and match auxiliaries, equation lemmas) included — and
(3) checks every constant of every kind, internal details included,
for `sorryAx`/`ofReduceBool`/`ofReduceNat`. The scope is exact: until
2026-09-02 both sweeps skipped internal-detail names, so a private
`sorry` unused by any pinned export passed; a planted one is now red
(`docs/2026-09-02_audit-response-3-notes.md`). Expected tail — the
three verdicts to check are the pin count, "every theorem bounded by
the trio" and "absent from all cones" ("trio" means the three classical
axioms); the two swept totals `N`/`M` are INFORMATIONAL and
environment-dependent, not a baseline: they include auxiliary
declarations (equation lemmas, match splitters) that a module realizes
on demand for dependency definitions when the imported environment
lacks them, so they vary with the semantics workspace's build state at
the same pin (measured 2249/3536 vs 2210/3474, `docs/2026-09-02_audit-response-4-notes.md`):

```
info: CerberusHeapLang/Audit.lean:260:0: CerberusHeapLang export pins: 165 trio-exact
info: CerberusHeapLang/Audit.lean:260:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (N swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:260:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (M constants of every kind swept, internal details included — count informational, environment-dependent)
Build completed successfully (… jobs).
```

(pin count and `Audit.lean` line as at the time of writing, 2026-09-03;
the pin list grows with the exports)

The trust base is this build with its in-build sweep, the root
package's build with its own sweep, and a grep for banned proof methods
(`native_decide`/`bv_decide`/`ofReduce*`) over both trees — the three
checks `scripts/test_unit.sh --fast` runs. The full `scripts/test_unit.sh`
adds two drift reports: the capability manifest is regenerated and
diffed, and the import direction semantics → heap → rules → adequacy →
clients is checked. Ask the kernel yourself (from `cerberus-heaplang/`):

```bash
../scripts/capped ~/.elan/bin/lake env lean --stdin <<'EOF'
import CerberusHeapLang
#print axioms CerberusHeapLang.project_triple_pure
#print axioms CerberusHeapLang.project_triple_pure_alloc
#print axioms CerberusHeapLang.struct_create_store_adequacy
#print axioms CerberusHeapLang.list_reverse_certified
#print axioms CerberusHeapLang.fib_certified_total
#print axioms CerberusHeapLang.exhibitA_prod
#print axioms CerberusHeapLang.list_reverse_certified_production
#print axioms CerberusHeapLang.dispose_list_certified_production
#print axioms CerberusHeapLang.region_loop_certified_production
#print axioms CerberusHeapLang.malloc_list_certified_production
EOF
```

Every line must read `depends on axioms: [propext, Classical.choice,
Quot.sound]`. The statement of every constant is recorded in the
committed signature snapshots under `docs/` (`*-signatures-*.txt`,
`scripts/signature_snapshot.lean`).

## The modules

In import order, one line each:

| Module | Contents | Headline |
|---|---|---|
| `Step.lean` | the fragment's mirror small-step over the engine's generated AST/state types, indexed by the explicit `MachineCtx`; hand-written, zero authority until certified | `Step`, `MachineCtx` |
| `EnvLaws.lean` | lawfulness of the engine's symbol order, `SymFrame`, lookup-after-add | `envAdd_lookup` |
| `Heap.lean` | the split ghost carrier (per-byte heap, per-allocation metadata heap — `MetaCell`: base, optional type, size, `alive`/`readonly`/`dynamic`, each coupled to the engine's `Allocation` by `MetaCoh` — allocator cursor) coupled to the real `MemState` by `CohG`; the global memory well-formedness invariant `MemWF` (in `CohG` and `LaunchCoh`), its cold-start/preservation lemmas and `create_fresh_global`; views, cells, points-to, the persistent stratum, the ∗-splittable allocation budget `allocBudget` (its authority `budgetAuth` under the coupling inequality `budgetInterp`, the cost `allocCost`, the engine bounds `freshBase_ne_zero_of_cost`/`headroom_freshBase`); the K1 bundles `regionOwn`/`readonlyCell`/`deadObj`; the `storeM`/`loadM`/`allocateObject` success lemmas and the read-only store refusal | `pointsToCell`, `pointsToView`, `allocMeta`, `regionOwn`, `readonlyCell`, `deadObj`, `allocBudget`, `allocBudget_split`, `storeM_success`, `loadM_success`, `storeM_readonly_kills` |
| `Lang.lean` | the iris-lean `Language` instance over `Step`; no `Language.Context` (falsified by `Erun`); the ghost functors | `instance : Language CoreRt Mem Empty CoreRVal` |
| `Rules.lean` | the atomic step specifications and their lifting to the raw WP; `wp_store`, `wp_load`; the readout combinator | `AtomicStep`, `store_atomic`, `wp_of_atomic`, `wp_store`, `stateInterp_readout` |
| `Wps.lean` | the partial label-context judgment as a guarded fixpoint; its rule set; statement-level framing; the Löb collapse into the raw WP | `wps`, `wps_seq`, `wps_create`, `blockSpecs_intro`, `wps_frame_labels`, `wps_sound` |
| `Wpt.lean` | the total judgment by recursion on the budget; variant-indexed label preconditions with the mandatory back-edge decrease; collapse into Iris `TotalWeakestPre` | `wpt`, `wpt_run`, `wpt_create`, `blockSpecsT_intro`, `wpt_frame_labels`, `wpt_sound` |
| `Soundness.lean` | the boundary module: the per-construct engine equations of `Step` against `step_ctx` (`step_ctx_*`), the fragment `Frag`, the decomposition `Decomp`; the discharge device `dischargeStep`/`outcomesU` and its step match (`outcomesU_of_step`, the `driveU` lane's device) | `Frag`, `Decomp.step_factor`, `step_ctx_store` |
| `EvalClass.lean` | the engine's pure-evaluator outcome on the covered grammar, classified (`evalClass`: value / kill / uncovered) and its KILL bridge level by level — the failure twin of the success bridge | `evalClass`, `evalClass_val_iff`, `step_eval_bridge_kill`, `full_eval_bridge_kill`, `evalClassList` |
| `Round.lean` | the shipped engine round (one iteration of the driver's thread loop, in the driver's own vocabulary), the certification `engine_step_matchU`, mirror completeness per redex root and its assembly, the exhaustive classification, the shipped refusal vocabulary and the residual — the reference relation the certification and completeness are stated over, consumed by no adequacy export (the `driveU` lanes consume `outcomesU_of_step`, the production collapse `loop_step_frag`) | `CerberusRound`, `engine_step_matchU`, `frag_round_complete`, `complete_*`, `cerberusRound_classify`, `ShippedRefusal`, `OpenRound` |
| `Potential.lean` | the step-monotone size potential `pot` — the static fuel bound | `pot`, `Frag.esize_le_pot`, `Frag.pot_step_bound` |
| `Adequacy.lean` | the drive `driveU`; Iris adequacy with the ghost state constructed; the allocation-aware launch; the triples; the projections and the pure-consequence lemmas | `project_triple_pure`, `MemTripleU`, `project_triple_pure_alloc`, `MemTripleU_alloc`, `engine_adequacyU` |
| `TotalAdequacy.lean` | the budget-to-drive-length simulation on `pot` | `wpt_engine_boundU`, `wpt_engine_boundU_alloc` |
| `API.lean` | the public surface as one import; the public/internal table | the header table |
| `Examples/Layout.lean`, `Examples/ReadinessSmoke.lean` | example support (`intTy`, byte images); the two-field object predicate and its rules from the API alone | `twoField`, `twoField_create` |
| `Examples/MirrorCoverage.lean` | mirror-level coverage witnesses proved directly against `Step` (the mixed `store` operand shapes) — a semantic regression module, NOT a client; the only other direct `Step` use outside the semantics layer is the negative test `DivergeExhibit.lean` (its header states the exception) | `store_sym_lit_step`, `store_lit_sym_step` |
| `Exhibit.lean`, `LoopExhibit.lean`, `FibExhibit.lean`, `DivergeExhibit.lean`, `ArrayExhibit.lean`, `StructExhibit.lean`, `AllocExhibit.lean`, `ListRevExhibit.lean`, `TreeRotExhibit.lean`, `CaseExhibit.lean`, `WseqExhibit.lean`, `DisposeExhibit.lean`, `RegionLoopExhibit.lean`, `MallocListExhibit.lean` | the exhibits (table above); the K4/K5 modules are the kill/free arc's exhibits (dispose-a-list over created nodes; n regions from one budget; THE MALLOC'D LINKED LIST — regions written, linked, read and freed through the K5 region access rules) | — |
| `DriverCollapse.lean` | the production scheduler/ND/readout collapsed onto the drive loop, proved from the driver's own round functions | `loop_step_frag`, `driver2_done`, `finalize_done` |
| `ProdLoop.lean` | the total judgment drives the production driver's per-thread loop | `wpt_driver_done`, `wpt_driver_done_alloc` |
| `ProdEntry.lean` | the cold start from the shipped `initial_driver_state`; the pipeline theorem; the registration ties | `prod_run_eqJ`, `fib_labeledAt_production` |
| `ProdExhibit.lean`, `ProdLoopExhibit.lean` | the production statements (table above) | `exhibitA_prod`, `*_production` |
| `Audit.lean` | the in-build axiom check: exact export pins, the exhaustive bound, the banned-axiom sweep — internal details included, the whole package | the sweeps |

## Records

History, provenance and process live in dated files, not here.
Rulings: `../docs/DECISIONS.md` (append-only, `[USER]`/`[AGENT]`
tagged). The kill/free arc (K0–K4, 2026-09-03) has its own record,
`docs/2026-09-03_kill-free-arc-record.md` (one paragraph per slice with
commits and audit verdicts, the measured corrections to the design note
`docs/2026-09-02_kill-free-design-spike.md`, what remains), indexing the
slice notes `docs/2026-09-03_k{0,1,2,2.5,3,4}-notes.md` and the range
audits `docs/2026-09-03_k{0,1,2,2.5,3}-audit.md`. The audit and review
record of the tree before the arc, newest
first: `docs/2026-09-03_audit-since-b34998d-response.md` (the response
to the independent audit of the range since the last audit: the
residual's characterization corrected on every surface — the classifier
answers `.uncovered` at the first uncovered leaf and carries no engine
claim; the adequacy chain's actual consumers named; the `--check` stamp
leg), `docs/2026-09-03_audit-since-b34998d.md` (the independent audit of
`b34998d..c2c4e4d`: sound at the theorem level, M-1 the residual's
prose overclaim with the engine counterexample by execution, N-1..N-6),
`docs/2026-09-02_fragment-closure-notes.md` (the fragment-closure
slice: the four completeness gaps closed fail-closed, the residual, the
narrowing premises), `docs/2026-09-02_mirror-completeness-notes.md`
(mirror completeness landed, the four gaps as found),
`docs/2026-09-02_audit-response-4-notes.md` (the response to
the re-review's four Low findings: the exported-theorem sentence, the
cold-start claim, the non-reproducible sweep totals diagnosed, the
known generated `sorry` in the trust story),
`../docs/2026-09-02_cerberus-heaplang-audit-response-re-review.md`
(the re-review of the detailed-audit response),
`docs/2026-09-02_audit-response-3-notes.md` (the response to
the detailed audit: PROVISIONAL labels, the qualified connection, the
audit-script scope with its plant transcript, the moves,
`ARCHITECTURE.md`), `../docs/2026-09-02_cerberus-heaplang-detailed-audit.md` (the
current architecture, trust and documentation audit) with the
[USER 2026-09-02] genuine-driver ruling and the upstream request
`../docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md`,
`docs/2026-09-02_pr3-notes.md` (the response to the second
review: `peDepth`/`PePure` named, the location premise discharged,
headers corrected), `docs/2026-09-02_professor-review-2.md` (the second
review, A-; its one delivery item — "allocation capacity is still not a
∗-resource" — is CLOSED: the additive face `allocBudget_split` landed at
K2.5, `docs/2026-09-03_k2.5-notes.md`, and its first loop client is K4's
`rl_wps`/`rl_wpt`), `docs/2026-09-02_pr2-notes.md` (the first review's
documentation response), `docs/2026-09-02_pr1-notes.md` (its code
response: static fuel premises, the `project_triple_pure` headline, one
triple/one drive, one proof per small axiom),
`docs/2026-09-02_professor-review-1.md` (the first review), `docs/2026-09-02_qa2-notes.md` and
`docs/2026-09-02_qa1-notes.md` (the quality audit's fix records),
`docs/2026-09-02_quality-audit.md` (the audit),
`../docs/2026-09-01_cerberus-heaplang-skeptical-re-audit.md` (the
earlier audit). The auditors' standing brief: `../docs/AUDIT-BRIEF.md`.
Earlier dated notes under `docs/` record the design and its history
back to the founding report `docs/2026-08-30_spike-report.md`;
statement-surface snapshots: `docs/*-signatures-*.txt`.

---

Built by AI agents (Claude, Anthropic) under the direction and review
of Mike Dodds.
