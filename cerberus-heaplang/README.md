# cerberus-heaplang

A classical separation logic — Reynolds/O'Hearn: points-to and ∗,
small axioms, the frame rule, sequencing, consequence, conditionals,
loops with invariants — over the Cerberus Core semantics, built on
iris-lean. Every exported execution theorem reaches the shipped engine
— the closed statements through its pipeline, the generic ones through
its driver's own per-thread loop at every fuel; every public logical
rule has a kernel-checked adequacy path through the package mirror to
the engine.

**Cerberus** is an executable semantics for C: it elaborates C into a
typed functional intermediate language, **Core**, and runs Core on an
interpreter over a byte-level, provenance-aware memory object model.
The engine here is the Lean 4 port of that semantics, differentially
validated against the OCaml implementation and pinned by commit in
`../scripts/semantics-pin.env`. This package instantiates an Iris
program logic over a fragment of Core, proves every rule against that
engine, and exports closed-program theorems whose statements are
Iris-free. Its root-of-trust exports are the closed statements about
the shipped cerberus-lean driver — total (`exhibitA_prod`,
`*_production`) and partial (`fib_rec_certified`, at every fuel of the
fuel-parametric pipeline); its generic partial-correctness exports are
stated over the shipped driver's own per-thread loop ("The claim"
below). **New reader? Start with the
[walkthrough](docs/WALKTHROUGH.md).** The normative architecture
statement — the semantic authority, the mirror's one-directional
certification, the two lanes, the open items, every sentence naming
its theorem — is [ARCHITECTURE.md](ARCHITECTURE.md). This package is a
demonstration of classical separation logic over Core and nothing
more; it is not a port of RefinedC (the RefinedC-family layer is
longer-term work on the branch `refinedc/dev`, not on `main`).

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
`BareHead` — a literal, `create`, `alloc`, the `PtrEq` memop and, since
calls arc C4, a procedure call `lets x = f(args) in …` (the RETURN plugs a
BARE value) — so the value it binds is never annotated; fragment closure,
2026-09-02), weak
sequencing `Ewseq` at the wildcard, `Esave` at `PePure` initializers
within the evaluator's fuel, `Eif` at a `PePure` guard, the
context-discarding jump `Erun` at `PePure` arguments, value-scrutinee
`Ecase`, `PEsym`-shaped pure exits, the covered operand grammar
`PePure` — `PEval`/`PEsym`/the eight mirrored `PEop` binops
(`Add`/`Sub`/`Mul`/`Eq`/`Lt`/`Le`/`Gt`/`Ge`)/`PEarray_shift` — the
run-time annotation residue, and (calls arc C2, 2026-09-03) THE
PROCEDURE CALL `Eproc () (Sym f) pes` at `PePure` arguments AND THE
RETURN — a value at a non-empty call stack — AT THE MIRROR LEVEL ONLY:
`Step.call` (the engine's PCALL round: every argument evaluated, the
callee installed with a fresh parameter frame, the caller's procedure and
the call redex's CAPTURED evaluation context pushed on the live control's
call stack, the execution location pushed) and `Step.ret`/`Step.ret_annot`
(the RETURN round: the value plugged into the captured context, the
frame and the callee's env frame popped; REMOVE-ANNOT under a frame),
certified (`engine_step_matchU`, now at a FREE successor control) and
classified (`complete_call`: unknown procedure and arity mismatch are
`call_proc`'s two `Illformed_program` KILLS, verbatim; `complete_ret`: a
value under a frame ALWAYS steps) — and, since C3 (2026-09-03), THE LOGIC
over them: the PROCEDURE SPECIFICATION TABLE `Θ : ProcSpec GF` (per
procedure symbol and argument values, a precondition and a postcondition
on the delivered value; `emptyProcSpec` recovers every pre-C3 statement),
the CALL CLAUSE of both judgments in place of C2's guard (lookup, arity,
argument evaluation, the table's precondition, and a step later the
caller's continuation `apply_ctx ctx (pure ret)` at the caller's own env),
the call rule `wps_call`/`wps_call_root` (`wpt_call`/`wpt_call_root` with
the budget split `1 + m + k' ≤ k`), the procedure rule
`procSpecs`/`procSpecs_intro` (Hoare's rule for recursive procedures:
every body verified once, at every caller tail, assuming the table — no
Löb in the introduction), and the CPS collapse `wps_sound_cps` — the ONE
Löb, whose call case runs the callee under `procSpecs` and returns into
the caller's continuation with the environment restored (`SameTail`);
the judgments are indexed by the current PROCEDURE `p : Option sym`
(RETURN does not restore `exec_loc`). Smoke: `Examples/CallSmoke.lean`
(`main` calls `f(3)`, `{⌜0 ≤ x⌝} f(x) {ret. ⌜ret = x + 1⌝}`, driven
through the partial lane over the shipped loop with `FragProcs` at two
procedures, `call_smoke_engine`); record
`docs/2026-09-03_c3-notes.md`. And, since C4 (2026-09-03), THE PRODUCTION
LANE THROUGH CALLS: the CPS driver induction `wpt_driver_cps` (ProdLoop.lean
— the driver-level twin of `wpt_sound_cps`; every PCALL and RETURN round
the shipped driver's own, `loop_step_frag`), its launcher
`wpt_driver_done_procs`, the N-procedure synthetic file `prodFileWith` with
`prod_run_eqJ_procs` (ProdEntry.lean), the `exec_loc`/`current_loc` tie of
the production entry control (`prodCtl`/`prodCtx`), and RECURSIVE FIB
(`FibRecExhibit.lean`: `fib(n) = if n < 2 then n else lets x = fib(n-1) in
lets y = fib(n-2) in save r(z := x+y) in pure(z)`, verified ONCE under the
table — Hoare's rule for recursive procedures, no Löb in the client — and
run cold on the shipped pipeline: `fib_rec_certified_production`, the
eighth root-of-trust statement); record `docs/2026-09-03_c4-notes.md`. The engine's third
stack constructor `Stack_cons` (the other interpreter's continuation
stack) is unrepresentable by `Ctl.toStack` and unreachable from
`Driver.drive` — step_ctx's value arm panics on it — a fail-closed
restriction, stated. (`Frag.store` admits EITHER locking mode — `lk` is unconstrained —
while every store rule is at `Store0 false`: the locking store, whose
engine success flips the allocation's `isReadonly`, has no rule, so no
derivation traverses one; noted by the K1 range audit.) The per-construct authority is the
inductive `Frag` (Soundness.lean), the premise of every adequacy
theorem; the generated [rule-use and classification
manifest](docs/CAPABILITY_MANIFEST.md) lists one row per engine-SUCCESS
VARIANT of each `Frag` constructor (ar5-manifest, 2026-09-04; ARCHITECTURE
§7 "The instruments around the claims"), each classified RULE (a partial
and a total rule, both in the proof-term cone of a consumer module — the
eighteen modules classified `positive-client`/`declared-smoke` in
`scripts/module_classes.tsv`, listed per row), RULE-TOTAL-UNDEMONSTRATED
(the total rule proved but consumed by no client — none since the
hygiene slice H1b of 2026-09-04 gave `wpt_load`, `wpt_case_value` and
`wpt_wseq` their consumers), NO-RULE (admitted by the fragment and the
engine, no rule, with the deciding record — the locking store, the static
kill of a region, `free(NULL)`, the zero-cost `alloc`, the union-member
pointer, the read-only-cell load at the statement level, the zero-size/
atomic/non-inert `create` types, the colliding `free`, the function-vs-
concrete `PtrEq`) or OUT-OF-SCOPE (excluded by the fragment/mirror
boundary): 23 constructors, 50 rows, 30 RULE, 0 RULE-TOTAL-UNDEMONSTRATED,
15 NO-RULE, 5 OUT-OF-SCOPE at this writing. Green means exactly what the
manifest header says — every constructor classified, every named theorem a
theorem, every RULE consumed in both judgments — and NOT that the variant
table is exhaustive over the engine's success shapes or that a NO-RULE
shape is covered; the former "0 red = every constructor has a covering
rule" reading is withdrawn.

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
`M.thread e' ρ' ctl`, whose `current_loc` is `M.currentLoc`. A located node
would falsify that equation. Located Core — in particular every Core
program the C elaborator produces — is therefore outside `Frag`; the
programs proved here are authored Core with empty annotation lists.
The mover is to make `current_loc` live state, part of the runtime
tuple as the environment is.

**In the fragment, mirrored and classified, but covered by NO rule
(kill/free arc K3; raised by the K2 range audit, decided).** (i) The STATIC
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
base happens to sit in `dynamicAddrs` (the K0 range audit's scenario), and
the logic takes an allocation's origin from the metadata cell, never
from that list. (ii) `alloc(al, n)` at `n ≤ 0` and alignment `al ≤ 1` —
a zero-COST request (`regionCost al n = n.toNat + max al 1 − 1 = 0`; the
engine's `sizeN.toNat` collapses EVERY non-positive size to a
successful size-0 region, so `alloc(4, −7)` is a covered size-0 request
at cost 3 — the K3 range audit's precision): the budget fragment
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

**Deliberately not here.** Mutual recursion exhibited (the rule admits
it — `procSpecs` assumes the table for every procedure — no exhibit yet);
function pointers (`Eccall`, another scheduler path); the single-procedure
driver lane `wpt_driver_aux`/`wpt_driver_done(_alloc)` stays at the EMPTY
table `emptyProcSpecT`, where the call clause is unsatisfiable
(`wpt_empty_call_false`), as the seven earlier production statements'
route — the total lane through calls is `wpt_driver_cps`, and the former
total `driveU` lane at the empty table was deleted in the fuel-lane
restatement (2026-09-03); a program with
two `save` labels IS exhibited since 2026-09-04 (`TwoLabelExhibit.lean`, H1b), as is mutual recursion (`EvenOddExhibit.lean`); calls arc C1 made the thread's control LIVE
STATE: `Config := CoreExpr × EnvStack × Ctl × Mem` with `Ctl` = the call
stack `κ`, the current procedure `proc` and the execution location
`execLoc`; every adequacy export is launched at an entry control with an
EMPTY call stack (`ctl.κ = []`), and the partial adequacy exports carry
the procedure well-formedness premise `MachineCtx.FragProcs` (every
declared procedure body in `Frag` within the potential bound, with `Frag`
label bodies — vacuous at both frozen profiles, `spikeCtx_fragProcs`/
`procCtx_fragProcs`; discharged at the two-procedure files,
`csCtx_fragProcs`/`frCtx_fragProcs`), since their proofs follow the
engine through a call and back; `MachineCtx.SeqWF` (startup thread) is a
premise of the round classification `cerberusRound_classify` only —
`⟨rfl⟩` at either frozen profile);
`Eunseq`; inside the
mirrored constructs, exactly these absences — `Ewseq` at binder
patterns, `Ecase` with a non-value scrutinee, pure exits beyond
`PEsym`, the memop family beyond `PtrEq`, `PtrEq`'s
differing-provenance nondeterministic fork, and the symbol-binder beta
at annotated values — each an absence of a `Step` rule, not a rule with
a hidden assumption; concurrency, prophecy variables, the C frontend
(programs enter as authored Core in a synthetic `file` — one procedure
by `prodFile`, `main` plus declared procedures by `prodFileWith`).

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
`dispose_list_certified_production` (DisposeExhibit.lean),
`region_loop_certified_production` (RegionLoopExhibit.lean),
`malloc_list_certified_production` (MallocListExhibit.lean) and
`fib_rec_certified_production` (FibRecExhibit.lean; calls arc C4). Their
execution function is the shipped `CerbND.runND (drive fmapEmpty false
file args) (initial_driver_state sup file fs).1`, the composite the
cerberus-lean executable runs, applied to the authored program wrapped
by `prodFile` (the synthetic one-procedure file) or, for recursive fib,
`prodFileWith` (`main` plus the declared `fib`); no package-defined
driver, discharge or scheduler appears in their statements, and they
carry no termination hypothesis — only the explicit in-budget bounds
`hfuel` where the step count depends on an input (recursive fib's is
`fibRounds n.toNat + 4 ≤ CerbFuel.driverFuel`, `fibRounds` the package's
round count of an activation — `fibRounds n + 9 = 12 · fib (n + 1)`, so
`n ≤ 33` is in the shipped budget), and, where the
program allocates from a size-dependent budget, the BUDGET side
condition that the budget fits the cold-start memory:
`region_loop_certified_production`'s `hB : n.toNat * regionCost al sz ≤
headroom prodMem₀.lastAddress` (in the package's pure vocabulary — its
cost function at its cold-start cursor literal; a finding of the K4
range audit, disclosed) and `malloc_list_certified_production`'s `hB : n.toNat * (15 + max
al.toNat 1) ≤ 281474976710647` (the same fact in ENGINE vocabulary: per
node `16 + max(al, 1) − 1` bytes of cursor descent, `281474976710647`
the cold-start cursor's headroom; bridge `ml_budget_bridge`); and, since
2026-09-04 (H1b), `even_odd_certified_production` (EvenOddExhibit.lean:
MUTUAL RECURSION, `even`/`odd` calling each other on the synthetic
THREE-procedure file, `hfuel : 3 * n.toNat + 6 ≤ CerbFuel.driverFuel`). These
nine are THE root-of-trust exports of this package — the closed
shipped-driver statements. They are reached through `prod_run_eqJ` or,
through calls, `prod_run_eqJ_procs` (ProdEntry.lean), which are generic
collapse machinery rather than closed statements: their delivery premise
`DriverDoneAt`, resp. the live-control `DriverDoneCtl` (ProdLoop.lean),
and their registration tie `LabeledAt`, resp. the whole-file
`LabeledProcs`, are package-defined, and the nine statements discharge
them.

**The partial lane, over the same driver.** Every generic
partial-correctness export — `MemTriple`, `MemTriple_alloc`,
`SemTriple`, `project_triple`, `project_triple_pure`,
`project_triple_alloc`, `project_triple_pure_alloc`,
`semantic_triple_sound`, `semantic_frame`, `engine_adequacy`,
`engine_adequacy_alloc`, the two lemmas over those triples
(`SemTriple_iff_Mem`, `MemTriple_alloc_of_MemTriple`), and every exhibit
whose "Execution" column below reads "the shipped loop" — is stated over
the SHIPPED driver's own per-thread loop
`drive_nonmemory_steps_aux2_lemFuel` (Driver.lean:346; the shipped
`drive_nonmemory_steps_aux2` is its instance at `CerbFuel.driverFuel`), AT
EVERY FUEL, from any driver state holding the configuration
(`DriverSafeCtl`, Adequacy.lean): the loop either EXHAUSTS — its value is
the kernel-transparent kill `CerbND.fuelExhaustedKill`, the cerberus-lean
fuel arc's out-of-fuel arm (pin `f95ef8d9c`) — or returns PROGRAM-DONE
for a value satisfying the postcondition; it never kills for any other
reason and never derails. The CLOSED partial form over the pipeline is
`prod_run_safe_procs` (ProdEntry.lean) with `fib_rec_certified` its
client ("Closed programs" below). This lane is the fuel-lane restatement
of 2026-09-03 (`docs/2026-09-03_f1-notes.md`): until then the partial
exports were stated over a package loop (`driveU`, iterating the engine's
`step_ctx` with a hand-written discharge) and carried an interim label,
because the shipped driver's out-of-fuel arm was LemLib's kernel-opaque
`fuelExhaustedWith` and no theorem over all fuels could classify its
outcomes (the request:
[`../docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md`](../docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md));
the cerberus-lean fuel arc lifted the obstacle, the package loop and every
statement over it are deleted, and no package-defined driver, discharge
or scheduler appears in any export's statement.

The partial-correctness realization of the target shape is the triple
`MemTriple` (Adequacy.lean), produced from an Iris triple by
`project_triple_pure` (both quoted in the walkthrough §1):

| Shape | In the tree |
|---|---|
| `s` | `σ : Mem` = the engine's `CerbMem.MemState`, arbitrary outside the footprint |
| `s \|= P` | `Sat M.tagDefs σ (P ∪ R)` — `Sat` is `Coh` (Heap.lean) by `abbrev`: every footprint cell live, writable, in bounds, exactly those bytes, pairwise disjoint; `R` is the arbitrary rest, returned to the post (the frame is part of the definition) |
| `prog` | `(e, ρ)` at a machine context `M` and a live control `ctl`, held by a driver state `dst` whose singleton thread is `ctlThread th₀ e ρ ctl` (the driver's own `thread_state` at that control) at layout state `σ`, with the context's file and the registration ties (`LabeledProcs`, `CtlTied`) |
| `core_exec(prog, s) ~~> term` | `runOne (drive_nonmemory_steps_aux2_lemFuel fl fmapEmpty acc [0]) dst` — the SHIPPED driver's per-thread loop with `fl` iterations available, for every `fl`, every accumulator `acc` and every such `dst`; the triple carries no fuel premise |
| `term = some(s')` | the loop returns `NDactive` with the PROGRAM-DONE singleton step map `fmapAddBy defaultCompare 0 [Step_done2 v] acc` at a final state whose layout is `σ'`; the only other admitted outcome is `NDkilled CerbND.fuelExhaustedKill` (fuel exhaustion) — no other kill (no undefined behaviour, no error kill), no refusal, no off-protocol step: partial correctness |
| `s' \|= Q` | `ψ R v σ'` for a pure `ψ : CellMap → value → Mem → Prop` |

`project_triple_pure`: at empty tag definitions and extern (the
production driver's `drive fmapEmpty false …`), an empty-stack entry
control (`ctl.κ = []`), `Frag e`, `Frag` membership of every registered
label body and of every declared procedure body (`FragProcs`), and the
static fuel bounds `pot e ≤ lemDefaultFuel` and `pot cont ≤
lemDefaultFuel` per registered body (Potential.lean; `rfl` for authored
programs), an Iris triple whose precondition is footprint ownership
`[∗map] i ↦ c ∈ P, cellOwn … i (.own 1) c` and whose framed Iris post
pure-entails `ψ R w.val σ'` under the coupling invariant projects to
`MemTriple M ctl ρ e P ψ`. The conclusion contains no Iris vocabulary;
the one Iris-shaped hypothesis is discharged for the points-to shapes by
`cellOwn_consequence`, `pointsToCell_consequence`,
`cellsOwn_consequence`, `cells_consequence` and the combinators
`pure_`/`sep_`/`or_`/`exists_consequence`. `project_triple` is the
strongest-post form beneath it; `SemTriple` (footprint post `Q`, `Sat σ'
(Q ∪ R)`) is the cells-shaped instance (`SemTriple_iff_Mem`,
definitional).

**Allocating programs.** `project_triple_pure_alloc` is the twin whose
Iris precondition is footprint ownership ∗ `allocBudget B` (the
∗-splittable allocation budget every `create` spends, walkthrough §3.2,
§4) and whose conclusion is `MemTriple_alloc`: `MemTriple` with the
launch premise `LaunchCoh M.tagDefs σ (P ∪ R) B` in place of `Sat` —
`Sat` plus the GLOBAL MEMORY WELL-FORMEDNESS INVARIANT `MemWF σ`
(Heap.lean: allocation-id discipline, live/dead consistency, pairwise
range disjointness of ALL live allocations, cursor bounds, the
dynamic-address facts — every component an engine fact of the concrete
allocator) plus the budget coupling inequality `B ≤ headroom
lastAddress` (the budget fits below the actual cursor). The premise
genuinely differs (a memory can carry the footprint with its cursor on
top of it), so the allocating triple is a separate definition;
`MemTriple` implies `MemTriple_alloc` at every budget
(`MemTriple_alloc_of_MemTriple`). The production cold-start memory
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
known. The PARTIAL closed form is `prod_run_safe_procs` (ProdEntry.lean;
the fuel-lane restatement, 2026-09-03): at EVERY `fuel`, `CerbND.runND
(CerbND.drive_lemFuel fuel fmapEmpty false (prodFileWith procs e) args)
(initial_driver_state sup (prodFileWith procs e) fs).1` is exactly one
execution, and it is either the fuel-exhaustion kill `nd_status.Killed
dst' CerbND.fuelExhaustedKill` or `nd_status.Active dres` with the
postcondition; the shipped `drive` is the instance at `fuel :=
CerbFuel.driverFuel` (`CerbND.drive_wrapper_defeq`, `rfl`) —
`drive_lemFuel` is the semantics' own fuel-parametric mirror of `drive`,
produced upstream for exactly this statement. Its client is
`fib_rec_certified`: recursive fib for EVERY `n ≥ 0`, no budget bound —
the exhaustion arm is what the shipped driver does when the run does not
fit its `10^8` iterations. Measured at the pin (`docs/2026-09-03_f1-notes.md`
§3): `drive_lemFuel`'s `fuel` bounds only the outer `driver2` rounds
(`new_drive_core_threads`, Driver.lean:355, calls the per-thread loop
through its wrapper at the fixed budget), so at every `fuel ≥ 1` the
statement is the one about the shipped `drive`; the "at every fuel of
the loop" content is the generic `DriverSafeCtl`. The seeded exhibits
(pre-seeded cells, which the cold start never contains) have no closed
form; their statements are the loop-level facts.

## The exhibits

Every theorem below is pinned in `Audit.lean` with axioms exactly
`propext`, `Classical.choice`, `Quot.sound`. "Execution" names the
execution function in the statement: "the shipped loop" — the shipped
driver's per-thread loop at every fuel from any driver state holding the
configuration (`DriverSafeCtl`, "The claim") — at `spikeCtx` (the
straight-line context, entry control `spikeCtl`) or at `procCtx rs` (the
context carrying a run state with registered labels, entry control
`procCtl p` — in procedure `p`), or the shipped pipeline (`runND ∘ drive
∘ initial_driver_state`). The shipped-pipeline rows are the closed
root-of-trust exports. The last column lists EVERY hypothesis of the theorem
by name, section variables included; it is read off the
machine-printed statement of every constant in
`docs/2026-09-03_f1-signatures-post.txt` (`scripts/signature_snapshot.lean`),
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
`fmapEmpty` the premise is `rfl` (`resolveExtern_id_of_empty`). No
shipped-loop statement carries a fuel hypothesis (the fuel is quantified
inside `DriverSafeCtl`).

| Theorem (file) | Says | Execution | Hypotheses, exhaustively |
|---|---|---|---|
| `exhibitA_semantic`, `exhibitA_engine` (Exhibit.lean) | store 7 then load: never kills otherwise; delivers `Specified(7)` (the shipped-pipeline run of the self-contained twin is `exhibitA_prod`) | the shipped loop at `spikeCtx` | `_semantic`: `{GF} [SpikeGpreS GF]` (the memory and the thread immutables are quantified by `SemTriple`); `_engine`: none — memory fixed to the constant `σ₀`, the thread `spikeThread progA` |
| `exhibitB_semantic`, `exhibitB_engine` (Exhibit.lean) | the frame: `⦃x ↦ - ∗ y ↦ a⦄ store(x,7) ⦃x ↦ 7 ∗ y ↦ a⦄` over engine configurations, `y` and all unnamed rest verbatim | the shipped loop at `spikeCtx` | `_semantic`: `{GF} [SpikeGpreS GF]`; `_engine`: none |
| `exhibitC_semantic`, `exhibitC_engine` (Exhibit.lean) | sequenced stores to disjoint cells both land | the shipped loop at `spikeCtx` | as B |
| `counter_loop_certified`, `counter_loop_certified_irrelevant_binding` (LoopExhibit.lean) | the first loop: save/guard/store/back edge; the seeded cell's final bytes are data-dependent; run from an entry frame with an unrelated binding | the shipped loop at `procCtx …` | `loc ann ra mo bty xbty sbty idx addr bs0 n`, `0 ≤ n`, `σ₀`, `hcoh` (the seeded cell); `_irrelevant_binding` adds `junk : value` |
| `fib_certified` (FibExhibit.lean) | iterative fib delivers `fib n` at every fuel (the total equation is `fib_certified_production`) | the shipped loop at `procCtx …` | `ra ibty abty bbty sbty n`, `0 ≤ n`, `σ₀` |
| `array_sum_certified` (ArrayExhibit.lean) | array walk with pointer arithmetic delivers `vs.sum`, array preserved | the shipped loop at `procCtx …` | `loc ann ra mo ibty accbty pbty xbty sbty vs id a aty bs`, `hsz : vs.length * 4 ≤ sizeofCtype fmapEmpty aty`, `ety`, `hdec` (each element's 4-byte range reconstructs, by the engine's `reconstructValue` at any side tables, to `MVinteger ety vs[i]`), `σ₀`, `hcoh` |
| `struct_update_certified` (StructExhibit.lean) | two-field struct update at the engine | the shipped loop at `spikeCtx` | `{GF} [SpikeGpreS GF]`, `loc ann mo mo' bty id a bs`, `σ₀`, `hcoh` |
| `struct_wps_views`, `cell_read_shared_wps`, `struct_x_read_persist_wps`, `struct_create_store_wps` (StructExhibit.lean) | the view/fraction/persistence laws as clients; allocate-then-initialize from `allocBudget` alone (Iris-level triples) | — (Iris) | all: `{hlc GF} [SpikeGS hlc GF] {M Ls} loc ann`; `_views`: `mo mo' bty id a b0 b1 b2 b3`, the three field lengths, `ev0 evs`; `cell_read_shared`: `pv mo bs bs' ρ`, `htrap`; `_x_read_persist`: `mo id a q dqb ρ`; `_create_store`: `aprov alignN pref mo pbty vbty ev0 evs`, `SymFrame ev0`, `∀ x, resolveExtern M.extern x = x` |
| `struct_create_store_adequacy`, `struct_create_store_adequacy_prodMem₀` (StructExhibit.lean) | allocate-then-initialize as `MemTriple_alloc spikeCtx spikeCtl spikeEnv prog ∅ (allocCost fmapEmpty structTy 8) ψ` (the budget form since K2.5), an instance of `project_triple_pure_alloc`; `_prodMem₀` fixes the memory to the production cold start | the shipped loop at `spikeCtx` | `{GF} [SpikeGpreS GF]`, `loc ann pref mo pbty vbty` |
| `alloc_two_creates_wps`, `alloc_create_wpt` (AllocExhibit.lean) | the allocation rules' local consumers (the engine runs of `create` from the cold start are `exhibitA_prod` and the production loop statements) | — (Iris) | `_wps`: `{hlc GF} [SpikeGS hlc GF] {M Ls} al₁ al₂ pref₁ pref₂ bty ev0 evs`; `_wpt`: `{hlc GF} [SpikeGS hlc GF] {M Ls} al pref ρ` |
| `alloc_free_wps` (AllocExhibit.lean; kill/free arc K3) | allocate a REGION then FREE it: `lets p = alloc(al, n) in free(p)` through the public `wps_alloc`/`wps_kill_eval`/`wps_free` delivers the unit value, the persistent dead region `deadRegion` of some id/base and the spent budget `regionCost al n` (the engine runs of alloc/free from the cold start are `region_loop_certified_production` and `malloc_list_certified_production`) | — (Iris) | `{hlc GF} [SpikeGS hlc GF] {M Ls} hex al n pref hcost ev0 evs hf` |
| `alloc_create_kill_wps` (AllocExhibit.lean; kill/free arc K2) | allocate then DISPOSE: `lets p = create(al, int) in kill(static int, p)` through the public `wps_create`/`wps_kill_eval`/`wps_kill` delivers the unit value, the persistent dead cell `deadObj` of some id/base and the spent capacity (the engine run of create/kill from the cold start is `dispose_list_certified_production`) | — (Iris) | `{hlc GF} [SpikeGS hlc GF] {M Ls} hex al pref ev0 evs hf` |
| `dl_wps`, `dl_wps_emp`, `dl_wpt`, `dl_wps_frame`, `dl_wpt_frame` (DisposeExhibit.lean; kill/free arc K4) | DISPOSE A LIST — the classical `{list p} dispose(p) {emp}`: the authored loop walks a chain of CREATED nodes (ListRevExhibit's `isList`) and `kill(static node, ·)`s each through the public `wps_kill`/`wpt_kill` at the node cell; `dl_wps`/`dl_wpt` deliver unit and `deadNodes ns` (every node's persistent dead cell), `dl_wps_emp` is the textbook post, the total budget is the DERIVED `12 * ns.length + 6`; the engine statement is `dispose_list_certified_production` below | — (Iris) | `{hlc GF} [SpikeGS hlc GF] loc ann ra mo cbty bbty nbty ubty ns p rs hQ sbty head`, `_frame` adds `RF` |
| `rl_wps`, `rl_wpt` (RegionLoopExhibit.lean; kill/free arc K4) | N REGIONS FROM ONE LINEAR BUDGET: `save rl(i := n) in if i > 0 then lets p = alloc(al, sz) in lets _ = free(p) in run rl(i − 1) else unit` — the budget `allocBudget (n.toNat * regionCost al sz)` is the LOOP INVARIANT, split per iteration by `allocBudget_split`, spent by the public `wps_alloc`/`wpt_alloc`, each region returned by `wps_free_emp`/`wpt_free_emp`; post `emp`; total budget the DERIVED `7 * n.toNat + 3`; the engine statement is `region_loop_certified_production` below. (The malloc'd LINKED list is the next row — MallocListExhibit.lean, K5, through the region access rules.) | — (Iris) | `{hlc GF} [SpikeGS hlc GF] loc ann ra al sz pref ibty pbty ubty hcost p rs hQ sbty n`, `_wpt` adds `hn : 0 ≤ n` |
| `ml_wps`, `ml_wpt` (MallocListExhibit.lean; kill/free arc K5) | THE MALLOC'D LINKED LIST: `save ml(i := n, p := NULL) in if i > 0 then lets q = alloc(al, 16) in lets _ = store(long, q, i) in lets _ = store(node*, array_shift(q, long, 1), p) in run ml(i − 1, q) else lets b = memop(PtrEq, [p, NULL]) in if b then unit else lets Specified(nx) = load(node*, array_shift(p, long, 1)) in lets _ = free(p) in run ml(0, nx)` — ONE label, two phases: `i > 0` allocates a 16-byte REGION node from the split budget, writes the counter (offset 0, `long` — stored but NOT tracked by `isRegionList`: the walk never reads it, and its signed-long decode round trip is not in this tree) and the link (offset 8, `node*`) THROUGH THE REGION (`wps_store_regionOwn_at`, K5) and conses it onto `isRegionList`; `i = 0` walks the list reading each next field through the region (`wps_load_regionOwn_at`) and `free`s each node (`wps_free`, its `deadRegion` kept). Invariant `allocBudget (i · regionCost al 16) ∗ isRegionList p ids ∗ deadRegions done`, `i + |ids| + |done| = n`, `(ids ++ done).Nodup`; post `unit ∗ ∃ ids, |ids| = n.toNat ∧ ids.Nodup ∗ deadRegions ids` — `n.toNat` DISTINCT dead ids (K5.1, the K5 range audit's finding: `deadRegion` is persistent, so without `Nodup` the post would say only that SOME region is dead; distinctness comes from the public `regionOwn_ne`/`regionOwn_deadRegion_ne` at each `alloc` and is carried through the invariant); total budget the DERIVED `25 · n.toNat + 7`; the engine statement is `malloc_list_certified_production` below | — (Iris) | `{hlc GF} [SpikeGS hlc GF] loc ann ra mo al pref ibty pbty qbty bbty nbty ubty n p rs hQ sbty`, `hn : 0 ≤ n` |
| `list_reverse_certified`, `list_reverse_demo` (ListRevExhibit.lean) | in-place reversal of a seeded chain next to an arbitrary disjoint frame — same allocation ids in reversed order, footprint equality on the maps, frame verbatim, at every fuel (the total equation on the shipped pipeline is `list_reverse_certified_production`); the demo fixes a 3-node chain | the shipped loop at `procCtx …` | `loc ann ra mo pbty cbty bbty nbty ubty sbty`, `ns head m₀`, `hseed : SeedChain m₀ head ns`, `R`, `hR : m₀ ##ₘ R`, `σ₀`, `hcoh : Sat fmapEmpty σ₀ (m₀ ∪ R)`; `_demo` replaces `ns head m₀ hseed` by the 3-node constants |
| `tree_rotate_certified` (TreeRotExhibit.lean) | binary-tree right rotation at the same statement shape, at every fuel (the former total equation over the package loop was deleted in the fuel-lane restatement; a shipped-pipeline total form needs a self-contained tree-building program — an open item) | the shipped loop at `spikeCtx` | `loc ann mo xbty ybty bbty ubty`, `sbty`, `idx idy vx vy ta tb tc px m₀`, `hseed : SeedTree m₀ px (.node idx vx (.node idy vy ta tb) tc)`, `R`, `hR`, `σ₀`, `hcoh` |
| `case_certified`, `wseq_certified` (CaseExhibit.lean, WseqExhibit.lean) | the `Ecase`/`Ewseq` consumers | the shipped loop at `spikeCtx` | `{GF} [SpikeGpreS GF]`, `v` resp. `v1 v2`, `σ₀` |
| `diverge_total_unprovable`, `dg_loop_exhausts` (DivergeExhibit.lean) | the negative test: a total derivation for the self-jump loop is `False` — proved against the engine fact `dg_loop_exhausts`: from any driver state holding the self-jump thread with its label tie, the SHIPPED loop exhausts at every fuel | `dg_loop_exhausts`: the shipped loop at `procCtx …`; `diverge_total_unprovable`: — | `diverge_total_unprovable`: `{GF} [SpikeGpreS GF]`, `ra σ₀ m₀`, `hcoh : Coh fmapEmpty σ₀ m₀`, and the statement's own quantifiers `Ls Ψ k` and the derivation from `m₀`'s cell ownership; `dg_loop_exhausts`: `ra`, and the statement's own `fl dst acc` with the thread/extern/`LabeledAt` ties |
| `exhibitA_prod` (ProdExhibit.lean) | the production run of `lets p = create(4,int) in lets _ = store(int, p, 7) in load(int, p)` is the singleton `Active` execution delivering 7, the final memory holding 7's image at the program's own cell | shipped pipeline — ROOT OF TRUST | `sup fs args` |
| `fib_certified_production`, `counter_loop_certified_production`, `list_reverse_certified_production` (ProdLoopExhibit.lean) | the loop programs on the shipped pipeline; counter and reversal bind their engine-created cells and enter their loops through `save` with live initializers | shipped pipeline — ROOT OF TRUST | fib: `sup ra n sbty ibty abty bbty`, `0 ≤ n`, `2 * n.toNat + 6 ≤ CerbFuel.driverFuel`, `fs args`; counter: `sup ra mo bty xbty cbty sbty n`, `0 ≤ n`, `6 * n.toNat + 8 ≤ CerbFuel.driverFuel`, `fs args`; reversal: `sup ra mo bty sbty pbty cbty bbty nbty ubty fs args` |
| `dispose_list_certified_production` (DisposeExhibit.lean), `region_loop_certified_production` (RegionLoopExhibit.lean) | kill/free arc K4 on the shipped pipeline: BUILD two nodes with `create`s (the list-reverse production's prefix, restated generically in its continuation as `lrProdPrefix_wpt`) then DISPOSE the list — EXACTLY ONE Active execution delivering `Vunit` whose final memory has two DISTINCT allocation ids in `deadAllocations` with their records erased (the proof witnesses them as the two created nodes; the statement names no node); `n` `alloc`/`free` pairs from one budget — EXACTLY ONE Active execution delivering `Vunit` (no readout of the final table: the regions are freed through the `_emp` faces, which drop the dead knowledge) | shipped pipeline — ROOT OF TRUST | dispose: `sup ra mo bty sbty cbty bbty nbty ubty fs args`; region loop: `sup ra al sz pref sbty ibty pbty ubty`, `hcost : 0 < regionCost al sz`, `n`, `hn : 0 ≤ n`, `hB : n.toNat * regionCost al sz ≤ headroom prodMem₀.lastAddress`, `hfuel : 7 * n.toNat + 5 ≤ CerbFuel.driverFuel`, `fs args` |
| `fib_rec_certified`, `fr_wp_readout` (FibRecExhibit.lean; calls arc C4, restated in the fuel-lane restatement) | RECURSIVE FIB, PARTIAL FORM ON THE SHIPPED PIPELINE: for EVERY `n ≥ 0` — no budget bound — and every `fuel`, `runND (CerbND.drive_lemFuel fuel fmapEmpty false (prodFileWith …) args) (initial_driver_state sup … fs).1` is EXACTLY ONE execution, either the fuel-exhaustion kill `CerbND.fuelExhaustedKill` or Active delivering `fib n` (the shipped `drive` is the instance at `fuel := CerbFuel.driverFuel`); `fr_wp_readout` is the collapse WITH the table into the raw WP | shipped pipeline at every `drive_lemFuel` fuel — ROOT OF TRUST (partial) | `sup ra n nbty xbty ybty sbty zbty`, `hn : 0 ≤ n`, `fs args fuel` |
| `fib_rec_certified_production` (FibRecExhibit.lean; calls arc C4) | RECURSIVE FIB ON THE SHIPPED PIPELINE — the first multi-procedure production statement: cold on the synthetic two-procedure file `prodFileWith [(fib, [(n, nbty)], body)] (fib(n))`, EXACTLY ONE Active execution delivering `fib n`; every PCALL and RETURN round is the driver's own; the label map (fib's `save r`) computed by the shipped registration on both procedures; termination from the total judgment at `fibRounds n + 2`, the in-budget bound `fibRounds n + 4 ≤ 10^8` (`n ≤ 33`) | shipped pipeline — ROOT OF TRUST | `sup ra n nbty xbty ybty sbty zbty`, `hn : 0 ≤ n`, `hfuel : fibRounds n.toNat + 4 ≤ CerbFuel.driverFuel`, `fs args` |
| `caseProg_wpt`, `wseqProg_wpt` (CaseExhibit.lean, WseqExhibit.lean; H1b 2026-09-04) | the `Ecase`/`Ewseq` consumers at the TOTAL judgment, budget 2 each, postcondition the engine readout `readoutPost` — the consumers of `wpt_case_value`/`wpt_wseq` (no shipped-loop total form: KNOWN-OPEN-ITEMS B1's class) | — (Iris) | `{hlc GF} [SpikeGS hlc GF] M p Ls Θ`, `v ρ` resp. `v1 v2 ev0 evs` |
| `two_label_certified`, `tl_wps`, `tl_wp_readout`, `tl_wpt`, `tl_wpt_readout` (TwoLabelExhibit.lean; H1b 2026-09-04) | TWO `save` LABELS in one procedure body: `save l1 (x := n₁) in if x > 0 then store(c, 5); run l1(x−1) else save l2 (y := n₂) in if y > 0 then store(c, 6); run l2(y−1) else unit` — the two-entry label map (`symAdd_lookup_two`), a LABEL-DEPENDENT specification (`tlLs`/`tlLsT`: a Lean `if` on the comparator verdict), both back edges by `blockSpecs_intro`; the final cell image is decided by both loops' data (6's image if `0 < n₂`, else 5's if `0 < n₁`, else the entry bytes); `_certified`: never kills otherwise, never derails, delivers `Vunit` with that image at every fuel; `tl_wpt`: total at budget `5 * n₁.toNat + 5 * n₂.toNat + 5` | `_certified`: the shipped loop at `procCtx …`; the rest — (Iris) | `_certified`: `loc ann ra mo bty xbty ybty sbty₂ sbty₁ idx addr bs0 n₁ n₂`, `hn₁ : 0 ≤ n₁`, `hn₂ : 0 ≤ n₂`, `σ₀`, `hcoh` (the seeded cell); `tl_wps`/`tl_wp_readout`/`tl_wpt`/`tl_wpt_readout`: `{hlc GF} [SpikeGS hlc GF] loc ann ra mo bty xbty ybty sbty₂ c n₁ n₂ bs0 p rs hQ hn₁ hn₂ sbty₁ f hf rest` |
| `even_odd_certified` (EvenOddExhibit.lean; H1b 2026-09-04) | MUTUAL RECURSION, PARTIAL FORM ON THE SHIPPED PIPELINE: `even`/`odd` calling each other under the SYMBOL-DEPENDENT table `eoSpec` (Hoare's rule for recursive procedures verifies each body once assuming the table for BOTH); for EVERY `n ≥ 0` and every `fuel`, `runND (drive_lemFuel fuel …)` cold on the synthetic THREE-procedure file is EXACTLY ONE execution, the exhaustion kill or Active delivering `1 - n % 2` (1 iff even) | shipped pipeline at every `drive_lemFuel` fuel — ROOT OF TRUST (partial) | `sup ra n nbty`, `hn : 0 ≤ n`, `fs args fuel` |
| `even_odd_certified_production` (EvenOddExhibit.lean; H1b 2026-09-04) | MUTUAL RECURSION ON THE SHIPPED PIPELINE — the NINTH closed statement, the first over a THREE-procedure file: EXACTLY ONE Active execution delivering `1 - n % 2`; every PCALL/RETURN round is the driver's own, alternating between the two procedures; termination from the total judgment at `3 * n + 4` | shipped pipeline — ROOT OF TRUST | `sup ra n nbty`, `hn : 0 ≤ n`, `hfuel : 3 * n.toNat + 6 ≤ CerbFuel.driverFuel`, `fs args` |
| `malloc_list_certified_production` (MallocListExhibit.lean; kill/free arc K5) | THE MALLOC'D LINKED LIST on the shipped pipeline: EXACTLY ONE Active execution delivering `Vunit` whose final memory has `n.toNat` DISTINCT allocation ids (`ids.Nodup`, K5.1) in `deadAllocations` with their records erased (the proof witnesses them as the freed nodes; the statement names no node) — every `alloc` through the public `wpt_alloc`, every field write through `wpt_store_regionOwn_at`, every next-field read through `wpt_load_regionOwn_at`, every `free` through `wpt_free` | shipped pipeline — ROOT OF TRUST | `sup ra mo al pref sbty ibty pbty qbty bbty nbty ubty`, `n`, `hn : 0 ≤ n`, `hB : n.toNat * (15 + max al.toNat 1) ≤ 281474976710647` (the budget fits the cold start, in ENGINE vocabulary), `hfuel : 25 * n.toNat + 9 ≤ CerbFuel.driverFuel`, `fs args` |

## The trust story

**Two trust claims.**

1. **The closed-program exports have Iris-free statements.** Their
   execution function is the shipped driver, in two forms. THE
   CLOSED FORMS: in the production statements (`exhibitA_prod`,
   `*_production`, and the partial `fib_rec_certified` /
   `prod_run_safe_procs`) it is the shipped `CerbND.runND (drive
   fmapEmpty false file args) (initial_driver_state sup file fs).1` — the
   genuine Cerberus driver — total statements at a certified step count,
   and, at every fuel of the semantics' fuel-parametric mirror
   `CerbND.drive_lemFuel` (pinned to `drive` by `rfl`), the partial
   statement "exhaustion or the postcondition". THE GENERIC FORMS: in the
   loop statements (`MemTriple`, `MemTriple_alloc`, `SemTriple`, every
   `*_certified`, `*_engine`) it is the shipped driver's own per-thread
   loop `drive_nonmemory_steps_aux2_lemFuel` (Driver.lean:346) at every
   fuel, from any driver state holding the configuration
   (`DriverSafeCtl`, Adequacy.lean). Both lanes iterate the same shipped
   round `loop_step_frag` (DriverCollapse.lean; since C2 stated at the
   LIVE control — the mirror's `ctl` is the driver thread's
   `stack0`/`current_proc_opt`/`exec_loc`, call and return rounds
   included) at the mirror step the logic supplies: the total lane by
   induction on the budget (`wpt_driver_aux`, `wpt_driver_cps` →
   `prod_run_eqJ`, `prod_run_eqJ_procs`), the partial lane by induction on
   the fuel (`drive_safe_aux` → `engine_adequacy` → `prod_run_safe_procs`).
   No package-defined driver, discharge or scheduler appears in any
   export's statement (the fuel-lane restatement, 2026-09-03: the former
   package loop `driveU` around the engine's `step_ctx` is deleted; until
   the cerberus-lean fuel arc — pin `f95ef8d9c`, the shipped driver's
   fuel exhaustion the kernel-TRANSPARENT kill `CerbND.fuelExhaustedKill`,
   `CerbND.driver2_lemFuel_zero` and its ND-typed siblings all `rfl`, the
   drive cone's budget the citable `CerbFuel.driverFuel = 10^8` — the
   out-of-fuel arm was LemLib's kernel-opaque `fuelExhaustedWith`, about
   which nothing is provable, the semantics-side limitation the request
   `../docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md`
   asked the cerberus-lean team to lift; no package-side workaround
   driver was ever built).
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
  semantics tree contains no admission at this pin (next bullet). The
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
- *Admissions in the pinned semantics tree: none (measured 2026-09-03).*
  Until the 2026-09-03 re-pin the pinned tree carried one generated
  admission — two `(sorry : String)` terms in the debug-log branch of
  `auxAddToRfLoad` in the generated concurrency model (`Cmm_op.lean`),
  reported as `declaration uses sorry` during the build, outside every
  export cone (the package sweep, `Audit.lean`, established that
  `sorryAx` reached no `CerberusHeapLang` constant) and reported to the
  cerberus-lean team. The fuel-arc head `f95ef8d9c` closes it
  (`cmm_op.lem`'s `sorry` target_rep replaced by
  `CerbMem.stringFromMemValue`). Measured at this pin: `grep -rn sorry`
  over the primed `generated/` finds comment text only, and neither
  build log contains `declaration uses sorry`
  (`docs/2026-09-03_repin-fuel-notes.md`). The sweep stays in force;
  concurrency remains out of scope for this package.
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
  `DriverSafeCtl`/`DriverDoneCtl` (the driver-state ties and the two
  outcome shapes, over the shipped loop), `ctlThread`, `LabeledProcs`,
  `CtlTied`, `Sat`/`Coh`/`CellCoh`, `SeedChain`/`SeedTree`, and the
  authored program terms; the walkthrough §2 prints them. A wrong
  definition here would make a theorem true but irrelevant.

**Registered divergences and limitations** — each on the face of the
theorems:

| Divergence / limitation | Discharge / mover | Home |
|---|---|---|
| Fuel: the engine's `get_ctx` is fuel-bounded (`lemDefaultFuel = 10^6`) with an opaque exhaustion leaf, so the projection theorems carry the static premises `pot e ≤ lemDefaultFuel` and `pot cont ≤ lemDefaultFuel` per registered body (never a bound on the run length); total production statements carry `k + 2 ≤ CerbFuel.driverFuel` (the shipped driver's budget, 10^8 since the fuel arc) for the certified step count; the shipped driver's OWN fuel arm is the kernel-transparent kill `CerbND.fuelExhaustedKill` (pin `f95ef8d9c`), which the partial lane states as the admitted outcome beside delivery — at every fuel of the loop (`DriverSafeCtl`) and, in the closed form, of `CerbND.drive_lemFuel` (`prod_run_safe_procs`); measured: that outer fuel bounds `driver2`'s rounds only, the loop's budget being the fixed `10^8` inside the wrapper | a fuel-irrelevance theorem for `get_ctx`; a second upstream mirror fuelling the loop as well (recorded as available in `../docs/2026-09-02_review-of-cerberus-lean-fuel-arc-design.md` §7) if a loop-fuel-parametric CLOSED statement is ever wanted | `Soundness.lean` header ("FUEL HONESTY"), `Potential.lean`, `Adequacy.lean`; `../docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md`, `docs/2026-09-03_f1-notes.md` |
| The fragment is annotation-free (`Expr []` at every node); located Core is outside `Frag` | make `current_loc` live state | "Scope, exactly"; `Soundness.lean` `Frag` header |
| Synthetic Core entry: authored Core wrapped by `prodFile`, not C through the frontend; the loop programs' label maps are nevertheless computed by the shipped registration (`*_labeledAt_production`, `LabeledAt`) | a C-frontend entry | `ProdEntry.lean` |
| The judgments are indexed by the current PROCEDURE `p : Option sym`, not the full control, and their step clauses quantify over the call stack and execution location `(κ, ℓ)` (calls arc C3) — forcing fact: RETURN does not restore `exec_loc` (PCALL pushes `push_exec_loc`, RETURN writes `current_proc_opt`/`env`/`stack0`/`arena` only), so the caller's continuation after a return runs at a control differing from the call-time one in `execLoc`; the pre-C3 judgment at `ctl` is the instance `p := ctl.proc, κ := ctl.κ, ℓ := ctl.execLoc` at the empty table | by design (every C1/C2 rule was control-general, the C1 range audit) | `Wps.lean`, `Wpt.lean`; docs/2026-09-03_c3-notes.md |
| The single-procedure driver lane (`wpt_driver_aux`/`_done(_alloc)`) is stated at the EMPTY table `emptyProcSpecT`, where the call clause is unsatisfiable (`wpt_empty_call_false`); the total lane THROUGH CALLS is the CPS lane `wpt_driver_cps`/`wpt_driver_done_procs` over the live-control delivery fact `DriverDoneCtl` (calls arc C4), consumed by `prod_run_eqJ_procs` — so the nine production statements are reached by two routes, the seven earlier ones at the empty table and recursive fib and even/odd through calls; the partial lane is at the live control throughout (`DriverSafeCtl`, `engine_adequacy`) | the single-procedure driver lane stays as the earlier statements' route (its restatement over the general lane was declined at C4: the file tie is not available at its context profile, `procCtx`); the former total `driveU` lane was deleted in the fuel-lane restatement | `ProdLoop.lean`, `ProdEntry.lean` |
| The partial adequacy exports carry `MachineCtx.FragProcs` (every declared procedure body in `Frag` within the potential bound, its label bodies too — the twin of the label-cone premises): their NotStuck oracle is the raw Iris WP, which does not exclude a call, so the fuel induction follows the engine through calls and returns (`drive_safe_aux`, the control invariant `ControlOk`, the env-depth invariant `Step.env_depth`, the ties `LabeledProcs`/`CtlTied`); vacuous at both profiles, discharged at the two-procedure files (`csCtx_fragProcs`, `frCtx_fragProcs`) | stays: the premise is the fragment membership of the FILE's bodies, which the specification table does not carry (a spec'd body may still be outside `Frag`) | `Adequacy.lean` |
| The straight-line exhibits' engine statements are at the profile `spikeCtx`/`spikeCtl` (the default file, NO current procedure); the shipped driver parks `main` at `current_proc_opt := some main_sym` (Driver.lean:530), so that thread state occurs in no pipeline run — the loop-level fact `DriverSafeCtl` admits it because the shipped round needs the current procedure's registration tie only at a jump (`loop_step_frag'`, `CtlTied.noproc`); the seeded exhibits (pre-seeded cells) likewise have no cold-start form | re-contexting the straight-line exhibits at the production context (the same hygiene slice as migrating the seven earlier production proofs to `prodCtx`, `docs/2026-09-03_c4-notes.md` §9); self-contained (building) twins for the seeded programs | `Adequacy.lean` header, `docs/2026-09-03_f1-notes.md` |
| Well-formedness by shape: `MachineCtx.SeqWF` (startup thread), the empty-stack entry control (`ctl.κ = []`, the PROGRAM-DONE selector) and cons-shaped environment stacks — the engine's panic channels excluded by shape, never absorbed; the RETURN's empty-env panic is excluded the same way (a frame is on the env stack whenever the call stack is non-empty). Action locations carry no premise: the certification equations state the request at the engine's own `requestLoc th loc`, and `storeM_loc_irrel`/`loadM_loc_irrel` (the memory operations use the location only in the kill payload) transport the mirror's premise to it | by design | `Step.lean`, `Soundness.lean` |
| The tag-definition environment is an explicit parameter of the heap predicates (`pointsToCell tds …`, `M.tagDefs`); the demos state footprints at `fmapEmpty` | by design: a program-wide constant of the language instance | `Heap.lean` header |
| Memory orders accepted arbitrarily (`Step.store`/`wp_store` at any `memory_order`) | mirror-true: the sequential driver drops `mo` (`action_request_sequential2`) | `Step.lean` |
| Mirror completeness holds on the DECLARED FRAGMENT up to a two-arm RESIDUAL (`OpenRound`, Round.lean; `frag_round_complete`; fragment closure 2026-09-02): `eval_uncovered` — an operand in the covered grammar CONTAINING A LEAF the engine's evaluator accepts where the mirror evaluator does not evaluate (a symbol unbound in the environment but naming a `Proc` of the file; one of the eight mirrored binops at two floating-point operands; `OpEq` at two ctypes — environment/file-dependent, the offending operand carried as witness, `evalClass … = .uncovered`); the classifier answers `.uncovered` at the FIRST such leaf and carries NO engine claim about the whole operand, so the arm's whole-operand outcome is NOT characterized — the engine may succeed, KILL on a later type error (`f + 1` with `f` a `Proc`-named unbound symbol is `PePure`, classified `.uncovered`, killed by the engine as `Illformed_program … ill-typed PEop` — 2026-09-03 audit, by execution) or PANIC (a float guard under `Eif`): every operand the classifier REJECTS is a proved engine KILL, operands it leaves UNCOVERED are not characterized, the residual is a SUPERSET of the engine-accepted shapes; and `run_surplus` — a jump with more arguments than the registered label's parameters whose zipped arguments evaluate and whose surplus does not (label-map-dependent). Everywhere else a mirror-stuck fragment configuration is an engine refusal in the engine's vocabulary (`ShippedRefusal`: ILLTYPED `[Step_error2 msg]`; ILLTYPED AT DISTANCE ONE — a successful round into the ill-typed load/store the engine reports on next; KILL `NDkilled r` from the shipped `advance_step`, memory kills through `liftMem` and pure-evaluator kills `Other (DErr_core_run err)` through `liftCore_run`; FORK ≥ 2 `CerbND.runND` executions; PANIC the engine's own `failwithI`, incl. the no-current-procedure lookup key). The former gaps (a) LETS-ANNOT at the symbol binder and (c) the operand grammar were closed by NARROWING `Frag` (`BareHead`, `PePure` everywhere) — fail-closed, per the ruling | the residual is not removable by a syntactic narrowing; the mover for `eval_uncovered`'s characterization is `evalClass` computing the engine's value at the three leaf shapes (reserving `.uncovered` for the leaf itself, the downstream rejections under the KILL bridge); a complete mirror evaluator (`M.file` threaded into `evalPexpr`, the float/ctype arms) would move `eval_uncovered` into `Step`; a prefix-evaluating `Step.run` would move `run_surplus` | `Round.lean` (`OpenRound`), `EvalClass.lean`; `ARCHITECTURE.md` §2, §7; `docs/2026-09-02_fragment-closure-notes.md` |
| The global memory well-formedness invariant `MemWF` (Heap.lean) is in the state interpretation (`CohG.wf`) and the launch premise (`LaunchCoh.wf`): allocation-id discipline, live/dead consistency, pairwise range disjointness of ALL live allocations, cursor bounds, and the dynamic-address facts — each an engine fact cited in the section header; fresh = disjoint from EVERY live allocation of the state (`create_fresh_global`), not only from the tracked footprint; the cold-start state satisfies it (`prodMem₀_memWF`); `loadM`/`storeM`/`allocateObject`/`killM` preserve it (`MemWF.loadM`/`MemWF.storeM`/`MemWF.allocateObject`/`MemWF.killM`). Two honest qualifications: (i) it is carried under cursor PRESENCE — the cursor-free launches (`MetaByteOf.cohG`, from `Coh` alone) have no `MemWF` premise, so non-allocating programs owe nothing and the non-allocating exports' texts are unchanged; (ii) the dynamic-address component is what the engine maintains (`dyn_lo`, `dyn_disj`), NOT "every dynamic address is a live base" — `killM` never removes an address from `dynamicAddrs` (CerbMem.lean:1576-1578) | CLOSED at K3: `MemWF.allocateRegion` is proved and pinned — every memory operation of the fragment (`loadM`/`storeM`/`allocateObject`/`allocateRegion`/`killM`) has its preservation theorem; K3 also added the engine invariant `la_pos : 0 < lastAddress` (both cursor writers guard `alignedAddr ≠ 0`; raised by the K2.5 range audit; a field added on orchestrator direction, recorded [AGENT] in DECISIONS), which is what prices a zero-size region correctly | `Heap.lean` (section "The global memory well-formedness invariant"), `Adequacy.lean` (`LaunchCoh` section); walkthrough §4 |
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
`Classical.choice`, `Quot.sound` (`Audit.lean`: 373 export pins at the
time of writing; every theorem of every module bounded). "Frag" = the fragment `Frag` at a
`SeqWF` context, an empty-stack control, with a cons-shaped environment; "labels" = every
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
   (Adequacy.lean: spike_step_adequacy =    (ProdLoop.lean: wpt_driver_aux (one procedure) and
    wp_strong_adequacy_gen, ghost state      the CPS induction wpt_driver_cps (through PCALL/RETURN):
    CONSTRUCTED by genHeap_init;             one shipped round loop_step_frag per budget unit; no Iris
    launchResources under LaunchCoh mints    adequacy in the cone; wpt_sound is the Iris collapse)
    the cursor and grants allocBudget B)
        ▼                                        ▼
   fuel induction AGAINST THE ENGINE        driver-delivery facts   DriverDoneAt / DriverDoneCtl
   (Adequacy.lean: drive_safe_aux — one       (wpt_driver_done(_alloc), wpt_driver_done_procs):
    shipped round loop_step_frag' per unit;    the shipped per-thread loop returns PROGRAM-DONE
    NotStuck supplies the mirror step)         within k + 2 iterations
        ▼                                        │
   the driver-safety fact  DriverSafeCtl         │
   (engine_adequacy(_alloc): the shipped         │
    per-thread loop drive_nonmemory_steps_aux2_  │
    lemFuel fl, at EVERY fl, from any driver     │
    state holding the configuration, exhausts    │
    — NDkilled CerbND.fuelExhaustedKill — or      │
    returns PROGRAM-DONE with the readout;        │
    project_triple_pure ⇒ MemTriple;              │
    project_triple_pure_alloc ⇒ MemTriple_alloc)  │
                          [Frag + labels + FragProcs]                [Frag + labels + FragProcs]
        ▼                                        ▼
   generic driver collapse   (DriverCollapse.lean: loop_step_frag(') — proved from the driver's
     OWN round functions; driver2_done / driver2_killed; finalize_done; runND_active / runND_killed;
     ProdEntry.lean: prod_run_eqJ / prod_run_eqJ_procs ⇒ runND (drive …)
       (initial_driver_state sup …).1 = [(Active dres, [], dst')]              [k + 2 ≤ CerbFuel.driverFuel]
     prod_run_safe_procs ⇒ ∀ fuel, runND (drive_lemFuel fuel …) (initial_driver_state sup …).1
       = [(st, [], dst')] ∧ (st = Killed dst' fuelExhaustedKill ∨ st = Active dres ∧ post)
       — drive = drive_lemFuel CerbFuel.driverFuel by rfl)          [labels / LabeledProcs]
        ▼
   whole-program production statements — THE ROOT-OF-TRUST EXPORTS
     (exhibitA_prod, fib_certified_production,
     counter_loop_certified_production,
     list_reverse_certified_production,
     dispose_list_certified_production,
     region_loop_certified_production,
     malloc_list_certified_production,
     fib_rec_certified_production)                              [∀ sup fs args]
   and the partial closed statement fib_rec_certified            [∀ sup fs args fuel]
```

What the diagram does not contain: a C frontend; a termination claim in
the partial lane (exhaustion is an admitted outcome, never excluded);
any engine fact at a mirror-stuck configuration beyond the four refusal
rows.

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

Every partial rule in that table is consumed by a client (the manifest
reports, per variant, which consumer modules' proofs flow through each
rule); every TOTAL rule of a RULE row is consumed too since 2026-09-04
(`wpt_load` by the rewritten `progA_wpt`, `wpt_case_value`/`wpt_wseq` by
the total twins `caseProg_wpt`/`wseqProg_wpt` — the manifest has no
RULE-TOTAL-UNDEMONSTRATED row left); the laws kept as
laws of the logic are exempt from the consumer check: `allocMeta_agree`, `allocBudget_weaken`/`allocBudget_le`, the
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
rule sets, the adequacy exports and the projections (over the shipped
driver's per-thread loop), and the pure memory view `CellCoh`/`Sat` — the
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
judgment unfoldings. The line is checked two ways: textually at every
claim point by `scripts/boundary_check.sh` (the full gate's client-boundary
speedbump: the modules classified `positive-client`/`declared-smoke`/
`example-support` in `scripts/module_classes.tsv` must not mention the
internals outside comments; per-module allowances carry their reason in
the TSV — NONE at this writing: the last, `progA_wpt` in `Exhibit`, was
rewritten over the public readout 2026-09-04, KNOWN-OPEN-ITEMS C8), and at the proof-term level on demand by
`scripts/parametric_inventory.lean` (fail-closed on its configuration since
2026-09-04; not a gate — ARCHITECTURE §5).

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
info: CerberusHeapLang/Audit.lean:567:0: CerberusHeapLang export pins: 373 trio-exact
info: CerberusHeapLang/Audit.lean:567:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (N swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:567:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (M constants of every kind swept, internal details included — count informational, environment-dependent)
Build completed successfully (… jobs).
```

(pin count and `Audit.lean` line as at the time of writing, 2026-09-03;
the pin list grows with the exports)

The trust base is this build with its in-build sweep and a grep for
banned proof methods (`native_decide`/`bv_decide`/`ofReduce*`) over the
tree — the two checks `scripts/test_unit.sh --fast` runs. The full `scripts/test_unit.sh`
adds three speedbumps: the rule-use and classification manifest is
regenerated and diffed, the import direction semantics → heap → rules →
adequacy → clients is checked (the protected set is the class `core` of
`scripts/module_classes.tsv`), and the client boundary is checked
(`scripts/boundary_check.sh`). The claim matrix `docs/CLAIMS.md` names, for
every headline claim, its theorems, kind, exhibits, supported variants and
known exclusions; the manifest generator checks its names exist. Ask the kernel yourself (from `cerberus-heaplang/`):

```bash
../scripts/capped ~/.elan/bin/lake env lean --stdin <<'EOF'
import CerberusHeapLang
#print axioms CerberusHeapLang.project_triple_pure
#print axioms CerberusHeapLang.project_triple_pure_alloc
#print axioms CerberusHeapLang.struct_create_store_adequacy
#print axioms CerberusHeapLang.list_reverse_certified
#print axioms CerberusHeapLang.engine_adequacy
#print axioms CerberusHeapLang.prod_run_safe_procs
#print axioms CerberusHeapLang.fib_rec_certified
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
| `Step.lean` | the fragment's mirror small-step over the engine's generated AST/state types — on configurations `Config := CoreExpr × EnvStack × Ctl × Mem` (the thread's LIVE CONTROL `Ctl`: call stack, current procedure, execution location; calls arc C1), indexed by the explicit immutable `MachineCtx`; hand-written, zero authority until certified | `Step`, `Ctl`, `MachineCtx` |
| `EnvLaws.lean` | lawfulness of the engine's symbol order; `SymMap`/`SymFrame`, the β-generic lookup-after-add law (env frames, procedure maps, label maps) | `symAdd_lookup`, `symAdd_lookup_two`, `envAdd_lookup` |
| `Heap.lean` | the split ghost carrier (per-byte heap, per-allocation metadata heap — `MetaCell`: base, optional type, size, `alive`/`readonly`/`dynamic`, each coupled to the engine's `Allocation` by `MetaCoh` — allocator cursor) coupled to the real `MemState` by `CohG`; the global memory well-formedness invariant `MemWF` (in `CohG` and `LaunchCoh`), its cold-start/preservation lemmas and `create_fresh_global`; views, cells, points-to, the persistent stratum, the ∗-splittable allocation budget `allocBudget` (its authority `budgetAuth` under the coupling inequality `budgetInterp`, the cost `allocCost`, the engine bounds `freshBase_ne_zero_of_cost`/`headroom_freshBase`); the K1 bundles `regionOwn`/`readonlyCell`/`deadObj`; the `storeM`/`loadM`/`allocateObject` success lemmas and the read-only store refusal | `pointsToCell`, `pointsToView`, `allocMeta`, `regionOwn`, `readonlyCell`, `deadObj`, `allocBudget`, `allocBudget_split`, `storeM_success`, `loadM_success`, `storeM_readonly_kills` |
| `Lang.lean` | the iris-lean `Language` instance over `Step`; no `Language.Context` (falsified by `Erun`); the ghost functors | `instance : Language CoreRt Mem Empty CoreRVal` |
| `Rules.lean` | the atomic step specifications and their lifting to the raw WP; `wp_store`, `wp_load`; the readout combinator | `AtomicStep`, `store_atomic`, `wp_of_atomic`, `wp_store`, `stateInterp_readout` |
| `Wps.lean` | the partial label-context judgment as a guarded fixpoint; its rule set; statement-level framing; the Löb collapse into the raw WP | `wps`, `wps_seq`, `wps_create`, `blockSpecs_intro`, `wps_frame_labels`, `wps_sound` |
| `Wpt.lean` | the total judgment by recursion on the budget; variant-indexed label preconditions with the mandatory back-edge decrease; collapse into Iris `TotalWeakestPre` | `wpt`, `wpt_run`, `wpt_create`, `blockSpecsT_intro`, `wpt_frame_labels`, `wpt_sound` |
| `Soundness.lean` | the boundary module: the per-construct engine equations of `Step` against `step_ctx` (`step_ctx_*`), the fragment `Frag`, the decomposition `Decomp`; the discharge device `dischargeStep`/`outcomesU` and its per-action computations `stepDischarge_*` (Round.lean's classification devices) | `Frag`, `Decomp.step_factor`, `step_ctx_store` |
| `EvalClass.lean` | the engine's pure-evaluator outcome on the covered grammar, classified (`evalClass`: value / kill / uncovered) and its KILL bridge level by level — the failure twin of the success bridge | `evalClass`, `evalClass_val_iff`, `step_eval_bridge_kill`, `full_eval_bridge_kill`, `evalClassList` |
| `Round.lean` | the shipped engine round (one iteration of the driver's thread loop, in the driver's own vocabulary), the certification `engine_step_matchU`, mirror completeness per redex root and its assembly, the exhaustive classification, the shipped refusal vocabulary and the residual — the reference relation the certification and completeness are stated over, consumed by no adequacy export (both adequacy lanes consume the shipped round `loop_step_frag`) | `CerberusRound`, `engine_step_matchU`, `frag_round_complete`, `complete_*`, `cerberusRound_classify`, `ShippedRefusal`, `OpenRound` |
| `Potential.lean` | the step-monotone size potential `pot` — the static fuel bound | `pot`, `Frag.esize_le_pot`, `Frag.pot_step_bound` |
| `Adequacy.lean` | Iris adequacy with the ghost state constructed; the allocation-aware launch; the partial lane over the shipped driver's per-thread loop — the driver-safety fact `DriverSafeCtl`, the fuel induction, `engine_adequacy(_alloc)`; the triples; the projections and the pure-consequence lemmas | `project_triple_pure`, `MemTriple`, `project_triple_pure_alloc`, `MemTriple_alloc`, `engine_adequacy`, `DriverSafeCtl` |
| `TotalAdequacy.lean` | the total lane's readout vocabulary (`readoutPost` and its plumbing); the total adequacy theorems are ProdLoop's driver lane | `readoutPost` |
| `API.lean` | the public surface as one import; the public/internal table | the header table |
| `Examples/Layout.lean`, `Examples/ReadinessSmoke.lean` | example support (`intTy`, byte images); the two-field object predicate and its rules from the API alone | `twoField`, `twoField_create` |
| `Examples/MirrorCoverage.lean` | mirror-level coverage witnesses proved directly against `Step` (the mixed `store` operand shapes) — a semantic regression module, NOT a client; the only other direct `Step` use outside the semantics layer is the negative test `DivergeExhibit.lean` (its header states the exception) | `store_sym_lit_step`, `store_lit_sym_step` |
| `Exhibit.lean`, `LoopExhibit.lean`, `FibExhibit.lean`, `DivergeExhibit.lean`, `ArrayExhibit.lean`, `StructExhibit.lean`, `AllocExhibit.lean`, `ListRevExhibit.lean`, `TreeRotExhibit.lean`, `CaseExhibit.lean`, `WseqExhibit.lean`, `DisposeExhibit.lean`, `RegionLoopExhibit.lean`, `MallocListExhibit.lean`, `FibRecExhibit.lean`, `TwoLabelExhibit.lean`, `EvenOddExhibit.lean` | the exhibits (table above); the K4/K5 modules are the kill/free arc's exhibits (dispose-a-list over created nodes; n regions from one budget; THE MALLOC'D LINKED LIST — regions written, linked, read and freed through the K5 region access rules); `FibRecExhibit.lean` is the calls arc's: RECURSIVE FIB under the specification table, on the shipped pipeline in both lanes (`fib_rec_certified` partial at every fuel, `fib_rec_certified_production` total); `TwoLabelExhibit.lean` (two `save` labels, H1b) and `EvenOddExhibit.lean` (mutual recursion on the shipped pipeline in both lanes, H1b) close the two coverage items the calls arc left open | — |
| `DriverCollapse.lean` | the production scheduler/ND/readout collapsed onto one mirror step, proved from the driver's own round functions: the shipped round at a live control (with the jump-only tie form `loop_step_frag'`), the exhaustion rounds, the killed and active `driver2` rounds, the singleton `runND`; the live-control vocabulary both lanes share (`ctlThread`, `LabeledProcs`, `CtlTied`) | `loop_step_frag`, `loop_step_frag'`, `driver2_done`, `driver2_killed`, `finalize_done`, `runND_killed` |
| `ProdLoop.lean` | the total judgment drives the production driver's per-thread loop — at one procedure (`DriverDoneAt`) and, since calls arc C4, THROUGH CALLS at a live control (`DriverDoneCtl`, the CPS induction `wpt_driver_cps`, every PCALL/RETURN round `loop_step_frag`, the whole-file tie `LabeledProcs`) | `wpt_driver_done`, `wpt_driver_done_alloc`, `wpt_driver_cps`, `wpt_driver_done_procs` |
| `ProdEntry.lean` | the cold start from the shipped `initial_driver_state`; the pipeline theorems for the one-procedure file `prodFile` and the N-procedure file `prodFileWith` (the entry control `prodCtl`, the production context `prodCtx`) — total (`prod_run_eqJ(_procs)`) and partial at every `drive_lemFuel` fuel (`prod_run_safe_procs`, both arms of the setup collapse); the registration ties | `prod_run_eqJ`, `prod_run_eqJ_procs`, `prod_run_safe_procs`, `fib_labeledAt_production` |
| `ProdExhibit.lean`, `ProdLoopExhibit.lean` | the production statements (table above) | `exhibitA_prod`, `*_production` |
| `Audit.lean` | the in-build axiom check: exact export pins, the exhaustive bound, the banned-axiom sweep — internal details included, the whole package | the sweeps |

## Records

History, provenance and process live in dated files, not here.
Rulings: `../docs/DECISIONS.md` (append-only, `[USER]`/`[AGENT]`
tagged). The kill/free arc (K0–K5.1, 2026-09-03) has its own record,
`docs/2026-09-03_kill-free-arc-record.md` (one paragraph per slice with
commits and audit verdicts, the measured corrections to the design note
`docs/2026-09-02_kill-free-design-spike.md`, what remains), indexing the
slice notes `docs/2026-09-03_k{0,1,2,2.5,3,4,5,5.1}-notes.md` and the
range audits `docs/2026-09-03_k{0,1,2,2.5,3,4,5}-audit.md` and
`docs/2026-09-03_k5.1-repin-audit.md`. After the arc, in order: the
re-pin to the fuel-arc semantics (`docs/2026-09-03_repin-fuel-notes.md`,
audited with K5.1), the calls arc's C1 and C2
(`docs/2026-09-03_c{1,2}-notes.md`, range audits
`docs/2026-09-03_c{1,2}-audit.md`), the standards audit of the whole
overnight stack (`../docs/2026-09-03_standards-audit-overnight-stack.md`)
and its response (`docs/2026-09-03_standards-audit-response.md`: the
stale admission and device sentences corrected, four proof devices
unpinned, this section), then C3 (`docs/2026-09-03_c3-notes.md`, range
audit `docs/2026-09-03_audit-c3-range.md`), C4 — the production lane
through calls and recursive fib — (`docs/2026-09-03_c4-notes.md`, range
audit `docs/2026-09-03_audit-c4-range.md`), and the fuel-lane
restatement F1 — the package loop `driveU` deleted, the partial lane
restated over the shipped driver — (`docs/2026-09-03_f1-notes.md`). The
current statement-surface snapshot is
`docs/2026-09-03_f1-signatures-post.txt`; the pre-slice snapshots that
were byte-identical to a predecessor were deduplicated on 2026-09-03
(one file kept per content, the records' references redirected in
place and re-verified by md5 in the standards audit). The audit and
review record of the tree before the arc, newest
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
the detailed audit: the interim labels of the then package-loop lane, the qualified connection, the
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
