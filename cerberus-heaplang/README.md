# cerberus-heaplang

A classical separation logic — Reynolds/O'Hearn: points-to and ∗,
small axioms, the frame rule, sequencing, consequence, conditionals,
loops with invariants — over the **real Cerberus Core semantics**,
built on **iris-lean**, whose exported theorems are statements about
the execution and memory states of the **cerberus-lean** engine.

**Cerberus** is an executable semantics for C: it elaborates C into a
typed functional intermediate language, **Core**, and runs Core on an
interpreter over a byte-level, provenance-aware memory object model
(**provenance**: the memory model's record of which allocation a
pointer derives from). The engine here is the Lean 4 port of that
semantics, differentially validated against the OCaml implementation
and pinned by commit in `../scripts/semantics-pin.env`. This package
instantiates an Iris program logic over a fragment of Core, certifies
every rule against that engine, and exports closed-program theorems
whose statements are Iris-free.

**New reader? Start with the [walkthrough](docs/WALKTHROUGH.md)** — one
exhibit read end to end, the trust tiers, the rules verbatim, and the
commands that check the claims in five minutes.

This package is the demo ([USER 2026-09-02]: "classical separation
logic over Core, nothing more"), and the seed of the next logic. It is
NOT the RefinedC port — that development is this repository's root
`RefinedCerberus` package; the demo is the stable design and trust
reference it is fed by.

## Scope, exactly

**The fragment.** Straight-line and loop programs in single-threaded
Core: `store`/`load`/`create` actions (both the evaluated-operand and
the operand-evaluation forms — the latter at the engine's own dispatch,
"the operands are not all values", so `store(int, p, 7)` with a symbol
pointer and a literal value is covered), the `PtrEq` memop, strong
sequencing `Esseq` at wildcard, `Specified`-binder and
plain-symbol-binder patterns, weak sequencing `Ewseq` at wildcard,
`Esave` at ANY initializers within the evaluator's fuel (literal or
live-variable — `save loop(x := n, c := p)` enters through the engine's
Esave EVAL arm), `Eif`/the context-discarding `Erun`, value-scrutinee
`Ecase`, `PEsym`-shaped pure exits,
`PEval`/`PEsym`/integer-`PEop`/`PEarray_shift` operands, and the
run-time annotation residue. The per-construct authority is the
inductive `Frag` (Soundness.lean) — the adequacy premise — and the
generated [capability manifest](docs/CAPABILITY_MANIFEST.md) lists one
row per `Frag` constructor with the rule covering it and the exhibit
modules whose proofs consume that rule (18 rows, 0 red). Every
construct has rules at both strata (QA-1, 2026-09-02: the six missing
total/partial twins were added).

**Deliberately not here** (the roadmap, [USER 2026-09-02]: the feature
set is frozen until the audit round; then calls/compositional reasoning
+ malloc/free, which completes the classical logic):

- `kill`/free — no dispose rule, hence no liveness token (metadata is
  immutable; "The trust story" below).
- Procedures: no call rule, no return; every program is one `main`
  body with registered labels. `MachineCtx.SeqWF` (empty call stack,
  startup thread) is a premise of every adequacy theorem stated at a
  general machine context, discharged at the demo profiles
  (`spikeCtx_wf`, `procCtx_wf`).
- `Eunseq`; and, inside the mirrored constructs, exactly these
  registered absences: `Ewseq` at binder patterns, `Ecase`'s EVAL arm
  (a non-value scrutinee), pure exits beyond `PEsym`, the memop family
  beyond `PtrEq`, `PtrEq`'s differing-provenance nondeterministic fork,
  and the symbol-binder beta at annotated values — each a fail-closed
  ABSENCE of a mirror step, not a rule with a hidden assumption. Not a
  gap: the pure and annotation rules (`wps_pure`, `wps_annot`, the
  `wpt_` twins) are stated at the empty annotation list `Expr []`
  because that is where the mirror's values live (the registered
  canonical-annotation protocol D3, `Step.lean`); the annotation-generic
  forms are FALSE there (QA-1), so `Expr []` is a fact of the value
  protocol.
- Concurrency, prophecy variables, the C frontend: programs enter as
  synthetic Core (a one-procedure `file` built by `prodFile`), not as
  C through the elaborator.
- Extensions are derisked on a COPY of this tree in a sibling package,
  never here ([USER 2026-09-02]).

## The claim

The target statement shape ([USER 2026-09-02], verbatim):

```
s |= P && core_exec(prog, s) ~~> term ==> term = some(s') && s' |= Q
```

for P and Q "just memory + pure properties". Two theorems realize it
(Adequacy.lean), differing only in what the Iris precondition may
contain; the postcondition side — an ARBITRARY Iris postcondition — is
the general part of both:

- `project_triple`: an Iris triple whose precondition is FOOTPRINT
  OWNERSHIP ALONE (`[∗map] i ↦ c ∈ P, cellOwn … i (.own 1) c` — a
  concrete cell map, no `allocCap`) projects to the boring triple
  `MemTripleU`, launched from any memory with `Sat M.tagDefs σ (P ∪ R)`.
  This is the non-allocating case: programs that only load and store.
- `project_triple_alloc`: an Iris triple whose precondition is footprint
  ownership ∗ `allocCap M.tagDefs reqs` (the capacity every `create`
  consumes, §3.3 of the walkthrough) projects to `MemTripleU_alloc`,
  the same boring triple launched from any memory with `LaunchCoh
  M.tagDefs σ (P ∪ R) reqs` — `Sat` PLUS allocator health (every id
  from the engine's `nextAllocId` up is unallocated and not dead, the
  footprint sits at or above the downward cursor `lastAddress`, the
  request plan `reqs` fits the actual cursor, cursor `≤ 2^64`). This
  is the allocating case, and the answer to "how does a program that
  allocates get a boring triple": `LaunchCoh` is what the production
  cold-start memory satisfies (`prodMem₀_launchCoh`, ProdEntry.lean),
  so an allocating client states its plan and launches from `prodMem₀`
  (`struct_create_store_adequacy`, StructExhibit.lean, is the worked
  instance). The launch premise genuinely differs (a memory can carry
  the footprint with its cursor sitting on top of it), so the
  allocating triple is a separate definition rather than
  `MemTripleU` with a side condition; `MemTripleU` implies
  `MemTripleU_alloc` at every plan (`MemTripleU_alloc_of_MemTripleU`).
  No other precondition shape is projected: an Iris pre with
  fractional cells, views or persistent metadata is first strengthened
  to whole cells by the assertion laws (`cellOwn_view`, `pointsToCell_combine`).

Both posts are "every pure consequence of the Iris post at the final
memory"; both carry the frame `R` inside the definition. Symbol by
symbol (for `MemTripleU`; `MemTripleU_alloc` differs in the `s |= P`
row only):

| Shape | In the tree |
|---|---|
| `s` | `σ : Mem` = the engine's `CerbMem.MemState`, arbitrary outside the footprint |
| `s \|= P` | `Sat M.tagDefs σ (P ∪ R)` — `Sat` (Adequacy.lean) is `Coh` (Heap.lean) by `abbrev`: every footprint cell live, writable, in bounds, exactly those bytes, pairwise disjoint; `R` is the arbitrary rest, returned to the post (the frame, built into `MemTripleU`). For `MemTripleU_alloc`: `LaunchCoh M.tagDefs σ (P ∪ R) reqs` (Adequacy.lean) — `Sat` plus the allocator-health facts above |
| `prog` | `(e, ρ)` at a machine context `M`; `M.thread e ρ` is the engine's `thread_state` |
| `core_exec(prog, s) ~~> term` | `driveU M aids n (M.thread e ρ) σ` — the iterated `{step_ctx → dischargeStep}` round of the sequential driver, for every action-id supply `aids` and every fuel `n` within the engine's own `get_ctx` budget (`esize e + n ≤ lemDefaultFuel`, likewise for every registered label body) |
| `term = some(s')` | `driveU … = .done v σ'`; the two other conjuncts, `≠ .killed r` (no undefined behaviour, no error kill) and `≠ .stuck` (no refusal, no off-protocol step); `.more` (fuel exhaustion) is unconstrained — partial correctness |
| `s' \|= Q` | `post R v σ'` — for `project_triple` and `project_triple_alloc` alike, every pure `ψ` that `Q w ∗ cells(R) ∗ metaInterp mm ∗ byteInterp mb` entails under any coupling witness `CohG σ' mm mb mk`; the pure-consequence lemmas (`cellOwn_consequence`, `pointsToCell_consequence`, `cells_consequence`, `sep_/or_/exists_/pure_consequence`) turn this into `CellCoh σ' i c` facts about the final memory |

`SemTripleU` (footprint post `Q : CellMap`, `Sat σ' (Q ∪ R)`) is the
cells-shaped instance (`SemTripleU_iff_Mem`, definitional);
`semantic_triple_soundU` is `project_triple` at that post; `SemTriple`
is its fixed-profile instance (`SemTriple_iff_U`); `drive`/`driveJ` are
`driveU` at the straight-line/proc-carrying contexts. Only the
`exhibitA/B/C_semantic` exhibits are stated AS `SemTriple` values; the
loop and allocation exhibits (`*_certified`,
`struct_create_store_adequacy`) state the `MemTripleU`/`MemTripleU_alloc`
body directly at their profile — same shape, unfolded, with the
footprint and frame instantiated.

**The production lane.** For closed programs the execution function in
the statement is the shipped pipeline itself — `CerbND.runND
(Driver.drive …) (initial_driver_state sup file fs).1` — reached from the
same logic through the generic driver collapse (`wpt_driver_done_alloc`
→ `prod_run_eqJ`). The statements quantify over the file-system state,
argv and the entry's symbol supply `sup` (the fragment never reads it).

**The exhibits** (every one pinned trio-exact in `Audit.lean`; Lane:
`drive`/`driveJ` = the driver's round loop projected to (thread,
memory), `production` = the shipped pipeline). The last column lists
EVERY hypothesis of the theorem: the explicit binders by name, and —
marked SECTION — the `variable`s of the enclosing `section`, which are
universally quantified but do not appear on the theorem line (Lean
puts them in the statement; the file:line is where they are declared).
`hlib` is `CerbLocation.isLibraryLocation loc = false` on the action
location (a constructor argument of `Frag.store/load/create`,
Soundness.lean:3585-3597); `hcoh` is the seeded-footprint premise
(`Coh`/`Sat`); the fuel pair `hfuel`/`hfuel2` is `esize + nsteps ≤
lemDefaultFuel` for the program and for the registered label body:

| Theorem (file) | Says | Lane | Hypotheses, exhaustively |
|---|---|---|---|
| `exhibitA_semantic`, `exhibitA_engine`, `exhibitA_total` (Exhibit.lean) | store 7 then load: never kills; delivers `Specified(7)`; the total form is an unconditional `.done` equation at fuel 6 | drive | `_semantic`: `{GF} [SpikeGpreS GF]` only (the seeded cell `mA` is a constant; the `SemTriple` quantifies the memory). `_engine`: `n aids`, `hn : n ≤ 999998` (the fuel budget at `esize progA = 2`); memory fixed to the constant `σ₀`. `_total`: `aids` only. No section variables |
| `exhibitB_semantic`, `exhibitB_engine` (Exhibit.lean) | THE FRAME: `⦃x ↦ - ∗ y ↦ a⦄ store(x,7) ⦃x ↦ 7 ∗ y ↦ a⦄` over engine configurations, `y` and all unnamed rest verbatim | drive | as A: `{GF} [SpikeGpreS GF]`; `n aids`, `hn : n ≤ 999999` |
| `exhibitC_semantic`, `exhibitC_engine` (Exhibit.lean) | sequenced stores to disjoint cells both land | drive | as A: `{GF} [SpikeGpreS GF]`; `n aids`, `hn : n ≤ 999998` |
| `counter_loop_certified`, `counter_loop_certified_irrelevant_binding` (LoopExhibit.lean) | the first loop: save/guard/store/back edge, the seeded cell's final bytes data-dependent (`CellCoh fmapEmpty σ' idx ⟨addr, intTy, bs'⟩`); run from an entry frame with an unrelated binding | driveJ | SECTION (LoopExhibit.lean:415-417): `loc ann ra mo bty xbty`. Explicit: `sbty idx addr bs0 n`, `hn : 0 ≤ n`, `hlib`, `σ₀`, `hcoh` (the seeded cell), `nsteps aids`, `hfuel : 4 + nsteps ≤ lemDefaultFuel`, `hfuel2 : 3 + nsteps ≤ lemDefaultFuel`; the `_irrelevant_binding` form adds `junk : value` |
| `fib_certified`, `fib_certified_total`, `fib_terminates` (FibExhibit.lean) | iterative fib delivers `fib n`; TOTAL: `driveJ … (2·n+4) … = .done (fib n) σ₀` with no fuel hypothesis; strong normalization | driveJ | SECTION (FibExhibit.lean:436-437, 598-599): `ra ibty abty bbty`. Explicit: `sbty n`, `hn : 0 ≤ n`, `σ₀`; `fib_certified` adds `nsteps aids`, `hfuel : 3 + nsteps ≤ …`, `hfuel2 : 2 + nsteps ≤ …`; `_total` adds `aids` only; `_terminates` nothing more. No `hlib` (the program has no memory actions) |
| `array_sum_certified` (ArrayExhibit.lean) | array walk with real pointer arithmetic delivers `vs.sum`, array preserved | driveJ | SECTION (ArrayExhibit.lean:636-637): `loc ann ra mo ibty accbty pbty xbty`. Explicit: `sbty vs id a aty bs`, `hsz : vs.length * 4 ≤ sizeofCtype fmapEmpty aty`, `ety`, `hdec` (each element's 4-byte slice reconstructs, by the ENGINE's `reconstructValue` at any side tables, to `MVinteger ety vs[i]`), `hlib`, `σ₀`, `hcoh` (the seeded one-allocation array), `nsteps aids`, `hfuel : 4 + nsteps ≤ …`, `hfuel2 : 3 + nsteps ≤ …` |
| `struct_update_certified` (StructExhibit.lean) | two-field struct update at the engine | drive | no section variables. Explicit: `{GF} [SpikeGpreS GF]`, `loc ann mo mo' bty id a bs`, `hlib`, `σ₀`, `hcoh` (the seeded struct cell), `n aids`, `hfuel : 2 + n ≤ lemDefaultFuel` |
| `struct_wps_views`, `cell_read_shared_wps`, `struct_x_read_persist_wps`, `struct_create_store_wps` (StructExhibit.lean) | the view/fraction/persistence laws as clients; allocate-then-initialize from `allocCap` alone (Iris-level triples) | — (Iris) | SECTION (StructExhibit.lean:325-326, 675-676): `{hlc GF} [SpikeGS hlc GF] {M Ls}`. Explicit: `loc ann`; `struct_wps_views`: `mo mo' bty id a b0 b1 b2 b3`, `h0 h1 h2` (the three 4-byte field lengths), `ev0 evs`; `cell_read_shared_wps`: `pv mo bs bs' ρ`, `htrap` (no `_Bool` trap representation); `struct_x_read_persist_wps`: `mo id a q dqb ρ`; `struct_create_store_wps`: `aprov alignN pref mo pbty vbty ev0 evs`, `hf : SymFrame ev0`, `hex : ∀ x, resolveExtern M.extern x = x` (no extern redirects — discharged at the demo profiles by `resolveExtern_id_of_empty`) |
| `struct_create_store_adequacy` (StructExhibit.lean) | allocate-then-initialize AT THE ENGINE from the production cold-start memory `prodMem₀`, THROUGH `project_triple_alloc` (footprint `∅`, plan `[⟨8, structTy⟩]`) | drive | no section variables. Explicit: `{GF} [SpikeGpreS GF]`, `loc ann pref mo pbty vbty`, `hlib`, `n aids`, `hfuel : 3 + n ≤ lemDefaultFuel`; the memory is the constant `prodMem₀` (its `LaunchCoh` is `prodMem₀_launchCoh`, ProdEntry.lean) |
| `alloc_two_creates_wps`, `alloc_create_wpt`, `alloc_create_launch_smoke` (AllocExhibit.lean) | the public allocation rules' local consumers; a bare create from the cold-start memory delivers a pointer at `driveU` fuel exactly 2 | driveU | `_wps`/`_wpt`: SECTION (AllocExhibit.lean:67) `{hlc GF} [SpikeGS hlc GF]`; explicit `{M Ls}`, `al₁ al₂ pref₁ pref₂ bty ev0 evs` resp. `al pref ρ`. `_launch_smoke`: `pref aids` only; memory `prodMem₀` |
| `list_reverse_certified`, `list_reverse_demo`, `list_reverse_certified_total`, `list_reverse_terminates` (ListRevExhibit.lean) | THE CANONICAL EXHIBIT: in-place reversal of a seeded chain next to an arbitrary disjoint frame — same allocation ids in reversed order, footprint equality on the maps, frame verbatim; TOTAL at the derived bound `13·\|ns\|+7`; termination; the demo instantiates a 3-node chain | driveJ | SECTION (ListRevExhibit.lean:1153-1154, 1988-1989): `loc ann ra mo pbty cbty bbty nbty ubty`. Explicit: `sbty`, `ns head m₀`, `hseed : SeedChain m₀ head ns`, `R`, `hR : m₀ ##ₘ R`, `σ₀`, `hcoh : Sat fmapEmpty σ₀ (m₀ ∪ R)`; `_certified` and `_demo` add `hlib`, `nsteps aids`, `hfuel : 6 + nsteps ≤ …`, `hfuel2 : 5 + nsteps ≤ …` (`_demo` fixes `ns`/`head`/`m₀` to the 3-node constants); `_total` adds `hlib`, `aids` (no fuel); `_terminates` adds nothing (no `hlib`, no fuel) |
| `tree_rotate_certified`, `tree_rotate_certified_total` (TreeRotExhibit.lean) | the second client: binary-tree right rotation at the same statement shape, zero core-logic edits; total at constant budget 19 | drive | SECTION (TreeRotExhibit.lean:1153-1154, 1426-1427): `loc ann mo xbty ybty bbty ubty`. Explicit: `idx idy vx vy ta tb tc px m₀`, `hseed : SeedTree m₀ px (.node idx vx (.node idy vy ta tb) tc)`, `R`, `hR : m₀ ##ₘ R`, `hlib`, `σ₀`, `hcoh : Sat fmapEmpty σ₀ (m₀ ∪ R)`, `aids`; `_certified` adds `sbty`, `n`, `hfuel : 6 + n ≤ lemDefaultFuel` |
| `case_certified`, `wseq_certified` (CaseExhibit.lean, WseqExhibit.lean) | the `Ecase`/`Ewseq` rows' consumers | drive | no section variables. Explicit: `{GF} [SpikeGpreS GF]`, `v` resp. `v1 v2`, `σ₀ n aids`, `hfuel : 2 + n ≤ lemDefaultFuel` |
| `diverge_total_unprovable` (DivergeExhibit.lean) | THE NEGATIVE TEST: a total derivation for the self-jump loop is `False` — the mandatory back-edge decrease is what blocks it | — | `{GF} [SpikeGpreS GF]`, `ra σ₀ m₀`, `hcoh : Coh fmapEmpty σ₀ m₀`, `Ls Ψ k` and the derivation `hwp` (from `m₀`'s cell ownership) are the statement's own quantifiers: any footprint, any ghost functors, any label spec, any post, any budget |
| `exhibitA_prod` (ProdExhibit.lean) | the production run of `lets p = create(4,int) in lets _ = store(int, p, 7) in load(int, p)` is the singleton Active execution delivering 7, the final memory holding 7's image at the program's own cell (existential id/address); proof = one total judgment `progAProd_wpt` through the PUBLIC `wpt_create` | production | `sup fs args` only; no section variables |
| `fib_certified_production`, `counter_loop_certified_production`, `list_reverse_certified_production` (ProdLoopExhibit.lean) | the loop programs on the shipped pipeline; the counter and reversal programs BIND their engine-created cells and ENTER their loops through the `save` with live initializers (`ctrProd_wpt`, `lrProd_wpt`: creates through `wpt_create`, constants stored directly through the bound pointers, `wpt_save` at the evaluated initializers, the generic list logic consumed verbatim at existential ids) | production | no section variables (every binder is on the theorem line). fib: `sup ra n sbty ibty abty bbty`, `hn : 0 ≤ n`, `hfuel : 2 * n.toNat + 6 ≤ lemDefaultFuel`, `fs args`; counter: `sup ra mo bty xbty cbty sbty n`, `hn : 0 ≤ n`, `hfuel : 6 * n.toNat + 8 ≤ lemDefaultFuel`, `fs args`; reversal: `sup ra mo bty sbty pbty cbty bbty nbty ubty fs args` — nothing else |
| `counter_loop_certified_registration` (ProdEntry.lean) | the counter loop with its label map DERIVED from the shipped registration (`collect_labeled_continuations_NEW`) | driveJ | no section variables. Explicit: `sup loc ann ra mo bty xbty sbty idx addr bs0 n`, `hn : 0 ≤ n`, `hlib`, `σ₀`, `hcoh`, `nsteps aids`, `hfuel : 4 + nsteps ≤ …`, `hfuel2 : 3 + nsteps ≤ …` |

## The trust story

**Two trust claims** ([USER 2026-09-02], DECISIONS.md):

1. **The closed-program exports have Iris-free statements.** Their
   referents are cerberus-lean's semantics — `step_ctx` and the
   driver's request discharge in the drive lanes, the shipped
   `runND ∘ Driver.drive ∘ initial_driver_state` in the production
   lane — plus the pure readout predicates (`Sat`/`CellCoh`,
   `SeedChain`, `readBytesFrom`). iris-lean appears only INSIDE their
   kernel-checked proof terms and contributes no axiom: every export's
   cone is pinned to the classical trio (`propext`, `Classical.choice`,
   `Quot.sound`) by `Audit.lean`. For these statements iris-lean is
   CHECKED, not trusted — it sits below the kernel-checked line.
2. **The reusable rules are stated in Iris.** `pointsToCell`, `cellOwn`,
   `allocCap`, the WP and BI connectives, `CohG` (which appears in one
   public statement — the pure-consequence obligation in
   `project_triple`'s post — as an opaque token a client never opens).
   This must-read set is the specification idiom, and it is the one
   sense in which iris-lean is "in the trust base": definitions to
   read, not axioms to accept.

**What you are asked to take on faith.** Self-contained, because this
is the only place where the story bottoms out outside the package.

- *The Lean kernel*, and the classical trio.
- *cerberus-lean's generated semantics is the semantics you care
  about.* The Lean port and the OCaml Cerberus — both generated from
  the same Lem model — are run on the same programs and their verdict
  lines compared against pinned fail-closed baselines: the recorded
  lanes at the pin include the 106-program upstream minimal suite
  (106/106), a 213-test CN corpus (213/213 exact match), a 16-URI
  multi-TU libxml2 corpus (16/16 byte-identical), 1,669 csmith programs
  at a classified baseline, and a 2,186-file upstream CI sweep with
  zero mismatches among its 1,316 comparable files. This samples
  behaviour, it is not an equivalence proof, and the OCaml oracle
  itself stays on the trust boundary. The authority is the pinned
  workspace's own record, `../.cerberus-ws/lean_frontend/VALIDATION.md`
  (primed by `../scripts/setup-cerberus-dep.sh`). Neither the semantics
  workspace nor its lem runtime (`LemLib`) declares an axiom. The
  engine does declare KERNEL-OPAQUE constants (`opaque`, mostly with
  `@[implemented_by]` runtime bodies): they enter no axiom cone and
  cannot be unfolded by any proof, so a theorem can only hold for
  EVERY value of them. Measured on the 120 export cones (QA-2, at the
  time of writing; a transitive constant-closure sweep in the
  `collectAxioms` convention; script in `docs/2026-09-02_p6.1-notes.md`,
  re-run in `docs/2026-09-02_qa2-notes.md`), the semantics-side
  opaques reached are: `CerbGlobal.current_execution_mode`,
  `CerbGlobal.using_concurrency` (the production lane, 8 exports:
  `driver2_done`, `loop_step_frag`, `wpt_driver_done`, `prod_run_eqJ`
  and the four production statements), `CerbGlobal.has_switch`
  (`inner_arg_temps`, read in `core_thread_step2`'s procedure-call arm,
  Core_run.lean:395) and `CerbGlobal.is_CHERI` (the pointer-size
  branch, Ctype.lean:578) — 6 exports, all in the production lane
  (`driver2_done`, `prod_run_eqJ` and the four production statements),
  reached through the shipped driver's code and never through the
  fragment's own steps; no drive-lane export reaches either —
  `CerberusImpl.typeof_enum` (115 exports, via `sizeofCtype`'s enum
  arm), `CerberusFresh.digest` (50 exports), LemLib's `failwithI` (104)
  and `fuelExhaustedWith` (116), `CerbMem`'s private `beqMemValueSafe`
  (8), the root-level `normalise_ctype` (module `Implementation`) and
  `Core.instBEqCore_base_type.beq` (6, production lane). Declared but
  NOT in any cone:
  `CerberusFresh.md5Hex`/`digestIO`/`setDigestIO`/`forceIO`,
  `CerberusImpl.register_enum`, `CerbGlobal.backend_name`/`isDefacto`/
  `isPermissive`/`isAgnostic`/`isIgnoreBitfields`/`is_PNVI`/
  `has_strict_pointer_arith`, `CerbUtils.*`. (Also in the cones, for
  completeness: iris-lean's `fixpointP`/`Tower.iso` and Lean core's
  `Float.*`/`floatSpec`/`String.Internal.append`/`Lean.opaqueId`/
  `Std.Internal.idOpaque`/`opaqueFix` — the same status.)
  The fuel side condition and the well-formedness premises below are
  how the package stays away from the leaves that could otherwise
  block a proof (`fuelExhaustedWith`, `failwithI`).
- *Which Cerberus configuration.* Cerberus is switch-configured
  (PNVI variants, strict pointer arithmetic, …), so the question
  "which configuration are these theorems about?" has a definite
  answer, pinned by the statements: (i) the tag-definition
  environment is `fmapEmpty` and concurrency is OFF — the production
  statements run `_root_.drive fmapEmpty false (prodFile …) args`
  (Driver.lean:518: `drive tagDefs with_concurrency file args`), and
  the drive-lane profiles `spikeCtx`/`procCtx`/`rsCtx` carry
  `tagDefs = fmapEmpty`; (ii) the switch set is NOT read at all on the
  memory path: the Lean `CerbMem` references no `CerbGlobal` constant
  (0 hits), so `loadM`/`storeM`/`allocateObject`/`eqPtrval` are
  switch-independent by construction (the differential pipeline runs
  the OCaml oracle with no switches set, and the port follows —
  `eqPtrval`'s docstring, CerbMem.lean:1752-1754); (iii) the two
  configuration reads that DO sit on a proved path are discharged for
  every value: the driver's `current_execution_mode` read is proved
  by `cases` on the opaque test (`driver2_done`,
  DriverCollapse.lean:929-985, the `cases hmode` at :967 — both
  scheduler branches reduce to the same singleton pick), and `using_concurrency` is read only inside
  `Core_run_aux`'s annotation helpers (`add_to_sb`/`add_to_asw`,
  Core_run_aux.lean:447-476) on the concurrency-tracking path the
  sequential driver does not take; (iv) the implementation-defined
  layout (`CerberusImpl.sizeof_ity`/`alignof_ity`, and the opaque
  `typeof_enum` for enum types, which the fragment never uses) is the
  port's `CerberusImpl` — the same one the OCaml oracle is validated
  against. So every export holds under every switch setting and every
  execution mode, at empty tag definitions, single-threaded.
- *The pure readout predicates* in the exported statements say what
  this document says they say: `driveU`/`drive`/`driveJ` (the driver's
  round loop, cited line by line against `Driver.lean`),
  `dischargeStep`, `Sat`/`Coh`/`CellCoh`, `SeedChain`/`SeedTree`, and
  the authored program terms. Each is a screenful; the walkthrough §2
  prints them. A wrong definition here would make a theorem true but
  irrelevant — which is why they are few, pinned by executable
  concrete instances (the demos), and laid out for reading.

**The registered seams** — each stated on the face of the theorems:

- *Fuel.* The engine's `get_ctx` is fuel-bounded (`lemDefaultFuel =
  10^6`) with an opaque exhaustion leaf, so partial statements carry
  `esize e + n ≤ lemDefaultFuel` (and the same per registered label
  body); the total exports are unconditional equations at a derived
  step bound instead. The production statements carry `k + 2 ≤
  lemDefaultFuel` for the certified step count.
- *Synthetic Core entry.* Programs are authored Core wrapped by
  `prodFile`, not C through the frontend; the label maps of the loop
  programs are nevertheless computed by the shipped registration
  (`*_labeledAt_production`, `LabeledAt`).
- *The frozen well-formedness.* `MachineCtx.SeqWF`, cons-shaped
  environment stacks, `isLibraryLocation loc = false` on action
  locations — the panic channels of the engine excluded by shape, never
  absorbed.
- *Donor divergences, recorded* (RefinedC's `ghost_state.v` is the
  reference): the bundles `pointsToView`/`cellOwn`/`pointsToCell` keep
  the allocation METADATA at a fraction because full metadata
  ownership is the per-allocation exclusivity anchor the frame theorem
  needs (`metaOwn_ne` → `bigSepM_own_disjoint`), where the donor's
  anchor is the killable `alloc_alive`; persistent allocation knowledge
  is the metadata cell at the DISCARDED fraction (`allocMeta`,
  `locInBounds`, `pointsToView_persist`) — a persistent stratum, not a
  killable liveness token, admissible because nothing in the fragment
  frees (named mover: the kill arc).
- *No `wp_bind`.* There is deliberately no `Language.Context` instance
  for the `Esseq` frame: Core's `Erun` DISCARDS its evaluation context
  (a jump inside `e1` and the same jump inside `Esseq pat e1 e2` step to
  the SAME configuration), so the frame law `Context.primStep_fill` is
  false for the fragment. Sequencing is therefore proved directly at
  the label-context judgments (`wps_seq`, `wpt_seq`), which carry
  jumps through per-label preconditions instead of a bind rule — the
  classical treatment of `goto`-like control. There is no sequencing
  rule at the raw WP at all: at a populated label map it is FALSE (a
  jump discards the sequencing context, so premise and conclusion land
  on the same registered body owing different postconditions).
- *Memory orders* are accepted arbitrarily by `Step.store`/`wp_store`:
  mirror-true, the sequential driver drops `mo`
  (`action_request_sequential2`, Driver.lean:273).

**Two presentations, one engine.** The pinned semantics workspace also
carries the semantics repo's own derived relational spine
(`relsemcore`: `RelSem` `Step`, `runND_sound`, `HarnessAdequate`) — its
validation instrument for its own runner. This package neither imports
nor builds on it, and no bridging theorem between the two presentations
exists or is claimed. This package's reference relation is
`CerberusRound M aid` (Round.lean), the graph of one discharged
`step_ctx` round — exactly the unit the shipped driver iterates. A
future type layer claiming `RelSemCore` as its semantics must prove the
bridge first.

## The trust diagram

Every theorem named on an arrow has axiom cone EXACTLY the classical
trio (`Audit.lean`: 120 export pins at the time of writing, every
theorem of every module bounded). "Frag" = the fragment cone `Frag` at a `SeqWF` context with
a cons-shaped environment; "labels" = every registered label body in
`Frag` with its own fuel bound (`hQf`/`hQsz`/`hQpot`). Arrows point the
way meaning flows: a proof at the source becomes a fact at the target.

```text
 TRUSTED ─────────────────────────────────────────────────────────────────
   cerberus-lean generated Core types + engine functions
   (step_ctx, the driver's request discharge, loadM/storeM/allocateObject,
    runND, Driver.drive, initial_driver_state)      + differential validation
 ─────────────────────────────────────────────────────────── kernel-checked
        │
        │  CerberusRound M aid  (Round.lean) — the reference relation: the graph
        │    of one discharged step_ctx round; NOT bridged to relsemcore
        │  Step M  (Step.lean) — the hand-written mirror; interior, zero authority
        │    certified: engine_step_matchU  Step ⇒ engine round   [Frag; trio]
        │               step_iff_cerberusRound  two-sided where the mirror steps
        │               cerberusRound_classify  exhaustive over Frag
        ▼
   iris-lean Language instance over Step   (Lang.lean: instance Language CoreRt
     Mem Empty CoreRVal; NO Language.Context — Erun discards its context)
        ▼
   state interpretation + raw resources   (Heap.lean: SpikeState / CohG over the
     real MemState; bytesOwn, metaOwn, cursorOwn → pointsToView, cellOwn,
     pointsToCell, allocMeta, locInBounds, allocCap)
        ▼
   base stratum   (Rules.lean: wp_store, wp_load — the small axioms at iris-lean's
     raw WP, generic in the machine context: one unfolding against Step + real
     storeM/loadM.  No raw-WP sequencing rule: false at a populated label map)
        ▼
   statement judgments   (Wps.lean: wps = guarded fixpoint; wps_* rules,
     wps_create, blockSpecs_intro, wps_frame_labels; wps_sound ⇒ raw WP  [Löb])
                         (Wpt.lean: wpt by recursion on the budget; wpt_* rules,
     wpt_create, blockSpecsT_intro, wpt_frame_labels; wpt_sound ⇒ Iris TWP)
        │                                        │
        │ partial lane                           │ total lane
        ▼                                        ▼
   Iris adequacy                            budget induction AGAINST THE ENGINE
   (Adequacy.lean: spike_step_adequacy =    (TotalAdequacy.lean: wpt_drive_aux —
    wp_strong_adequacy_gen, ghost state      engine_step_matchU discharges one engine
    CONSTRUCTED by genHeap_init;             step per budget unit; no Iris adequacy in
    launchResources under LaunchCoh mints    the cone.  wpt_sound ⇒ twp_total feeds only
    the cursor and grants allocCap)          wpt_strongly_normalizing)
                          [Frag; trio]                              [Frag + labels; trio]
        ▼                                        ▼
   engine drive statements   (engine_adequacyU ⇒ driveU never kills/derails,
     readout at .done;  project_triple ⇒ MemTripleU;  semantic_triple_soundU ⇒
     SemTripleU;  wpt_engine_boundU/J, wpt_engine_boundU_alloc ⇒
     driveU … k = .done v σ' unconditionally)               [Frag + labels; trio]
        ▼
   generic driver collapse   (DriverCollapse.lean: loop_step_frag, driver2_done,
     finalize_done — proved from the driver's OWN round functions;
     ProdLoop.lean: wpt_driver_done(_alloc) ⇒ DriverDoneAt;
     ProdEntry.lean: prod_run_eqJ ⇒ runND (Driver.drive …) (initial_driver_state
     sup …).1 = [(Active dres, [], dst')])               [labels; k+2 ≤ fuel; trio]
        ▼
   whole-program production statements   (exhibitA_prod,
     fib_certified_production, counter_loop_certified_production,
     list_reverse_certified_production)                          [∀ sup fs args]
        ▼
   projection to boring statements   (project_triple: footprint-only Iris pre ⇒
     MemTripleU;  project_triple_alloc: footprint ∗ allocCap pre ⇒ MemTripleU_alloc
     [LaunchCoh launch];  both posts = every pure consequence of the Iris post at
     the final memory; *_consequence discharge it; SemTripleU_iff_Mem)

   future semantic types and automation sit here: above the raw rules
   (API.lean), below generated client proofs (Examples/ReadinessSmoke.lean)
```

What the diagram does NOT contain: a bridge to `relsemcore`; a C
frontend; any statement about `.more` (fuel exhaustion).

## The logic

One line per rule family (names are the theorems; the walkthrough §3
quotes the small axioms, frame, create, one loop rule and the total
judgment verbatim). Two label-context statement strata over
iris-lean's WP — the partial judgment `wps` (Wps.lean) and the total
judgment `wpt` (Wpt.lean) — and beneath them the base stratum: the two
small axioms `wp_store`/`wp_load` at the raw WP (Rules.lean), generic
in the machine context and the environment, the reference form of the
memory rules (the statement strata restate them with the label context
and prove them the same way, directly against `Step`). Frame and
consequence at the raw WP are iris-lean's own `wp_frame_r`/`wp_mono`;
there is no raw-WP sequencing rule — at a populated label map it is
false (a jump discards the sequencing context), which is exactly why
the label-context judgments exist.

| Family | Rules |
|---|---|
| Small axioms | `wp_store`, `wp_load` (base WP: cell ownership entails the WP, every UB arm of `storeM`/`loadM` excluded by the precondition); `wps_store`, `wps_load`, the typed-subrange forms `wps_load_at`/`wps_store_at`/`wps_load_cell_at`/`wps_store_cell_at`; the same six at the total stratum, `wpt_store`, `wpt_load`, `wpt_load_at`, `wpt_store_at`, `wpt_load_cell_at`, `wpt_store_cell_at` (cost `3 ≤ k`). Storability vocabulary: `StorableAt` (whole-cell rules) and its four-field face `StorableView` (the typed-subrange rules). Plain-value forms for annotation-insensitive postconditions — the textbook `{p ↦ -} store(p, v) {p ↦ v}` with no footprint quantifier: `wps_store_plain`, `wps_load_plain`, `wpt_store_plain`, `wpt_load_plain` |
| Allocation | `wps_create`, `wpt_create` (cost bound `2 ≤ k`): `allocCap (req :: rest)` buys one `create`; the continuation binds an EXISTENTIAL pointer with full ownership at the unspecified image, `allocCap rest`, and the pure bounds `0 < addrOf p < 2^64`; cursor-free statements |
| Frame | iris-lean's `wp_frame_r` at the raw WP; `wps_frame`, `wps_frame_labels` with `frameLs R Ls = fun l vs ρ => Ls l vs ρ ∗ R`, `blockSpecs_frame`, the whole-loop `wps_sound_frame`; `wpt_frame`, `wpt_frame_labels` (`frameLsT`), `blockSpecsT_frame` — the frame crosses every back edge through the framed label context |
| Consequence | iris-lean's `wp_mono`/`wp_wand` at the raw WP; `wps_wand`, `wps_fupd` (postcondition-modality absorption), `wps_mono_Ls`, `blockSpecs_mono`; `wpt_mono`, `wpt_mono_k` (budgets are upper bounds), `wpt_mono_Ls`, `wpt_fupd`, `blockSpecsT_mono` |
| Sequencing | `wps_seq` (wildcard), `wps_seq_spec` (`Specified` binder), `wps_seq_sym` (symbol binder), `wps_wseq`; `wpt_seq`, `wpt_seq_spec`, `wpt_seq_sym`, `wpt_wseq` (budgets add) |
| Conditionals, case | `wps_if` (ONE rule, the guard's verdict inside the logic: `⌜evalPexpr … g = some (boolValue b)⌝ ∗ wps … (bif b then e2 else e3) ⊢ wps … (Eif g e2 e3)`; `wps_if_true`/`wps_if_false` are its derived instances), `wps_case_value`; `wpt_if` (`wpt_if_true`/`wpt_if_false` derived), `wpt_case_value` |
| Loops (label context) | `wps_save` (block entry at EVALUATED initializers, `evalPexprs … = some cvals` — literal or live-variable; `wps_save_vals` is the literal instance, `wps_save_eval` the engine's EVAL step), `wps_run` (the jump: the label's precondition `Ls l vs ρ` suffices — tracking stops), `blockSpecs_intro` (every registered body re-establishes its precondition; no Löb — the one Löb is in `wps_sound`); total: `wpt_save` (entry cost `saveEntryCost ps`: 1 at literal initializers, 2 otherwise — the engine's own dispatch; `wpt_save_vals`, `wpt_save_eval`), `wpt_run` with the MANDATORY decrease `1 + m ≤ k` at the variant `m`, `blockSpecsT_intro` |
| The total judgment | `wpt M Ls k Ψ e ρ` by structural recursion on the step budget `k`; `wpt_sound` collapses it into iris-lean's `TotalWeakestPre`; `diverge_total_unprovable` is the negative test |
| Operands, memop, values | `wps_load_eval`, `wps_store_eval` (premise "the operands are not all values", `valueFromPexprs [pe2, pe3] = none` — the engine's dispatch), `wps_memop_eval`, `wps_memop_ptreq`; `wps_ofVal`, `wps_pure`, `wps_annot`, `wps_annot_reindex`; the `wpt_` counterparts |
| Assertion laws | `pointsToCell_fractional`/`_agree`/`_combine`; `pointsToView_split`/`_join`/`_fractional`/`_agree`/`_persist`/`_locInBounds`; `allocMeta_persistent`, `allocMeta_agree`, `locInBounds_persistent`; `cellPtr_arrayShift` (provenance-preserving shift); `allocCap_weaken` |
| Environment seam | `SymFrame`, `envAdd_lookup` (EnvLaws.lean): lookup-after-add on any reachable frame, so invariants never pin a frame shape |

Consumers, honestly: every rule above is consumed by an exhibit
(the capability manifest reports the fragment rows), with three
exceptions that are kept as laws of the logic rather than deleted
under the no-consumer rule — `allocMeta_agree` (agreement of the
persistent allocation knowledge), `allocCap_weaken` (a plan's capacity
serves any prefix), and the raw-WP `wp_load` (the exhibits consume its
statement-stratum twin `wps_load`; its sibling `wp_store` is consumed
by `provenB`, Exhibit.lean). Nothing else in the API is consumerless
(QA-2, `docs/2026-09-02_qa2-notes.md`, by proof-term trace).

Representation predicates are ordinary structural recursion — `isList`
(ListRevExhibit.lean) is identity-indexed (each node = allocation id ×
value) and UNFRAMED; the arbitrary frame is added afterwards by
`wps_frame_labels`/`wpt_frame_labels` (`lr_wps_frame`, `lr_wpt_frame`).

## The public API, and how a client is written

`API.lean` is the public surface as one import: `import
CerberusHeapLang.API`. Its header is the public/internal table —
PUBLIC: the pointer/location assertions and their laws, the
side-condition vocabulary, the environment seam, the base logic, both
statement judgments with their full rule sets, the adequacy exports and
the projection; INTERNAL (visible, since Lean imports are transitive,
but not part of the surface): `CohG` and the ghost carrier, the
allocator cursor, `Step`/Soundness/Round, the judgment unfoldings, the
memM seams. A client that needs an internal name is a finding about the
surface, answered by a new public lemma (as `cellOwn_readout` was).

**The worked example** is `Examples/ReadinessSmoke.lean`: importing
ONLY the API, it defines a two-field object predicate

```lean
def twoField (tds : CerbTags.TagDefsMap) (p : CerbMem.PointerValue)
    (xb yb : List CerbMem.AbsByte) : IProp GF :=
  iprop(∃ (id a : Int), ⌜p = cellPtr id a⌝ ∗
    pointsToView tds id a objTy 0 (.own (Qp.half 1)) (.own 1) fieldTy xb ∗
    pointsToView tds id a objTy 8 (.own (Qp.half 1)) (.own 1) fieldTy yb)
```

and DERIVES its load, store and allocate rules from the public rules
alone (`twoField_load_x/_y`, `twoField_store_x/_y`, `twoField_create`):
`wps_load_at`/`wps_store_at` at offsets 0 and 8 (the y field addressed
by the engine's own `arrayShiftPtrval`, through `cellPtr_arrayShift`),
`wps_create` + `cellOwn_view` + one `pointsToView_split` for
allocation. It is measured at zero direct references to the ghost maps,
`CohG`, the cursor, `Step` or the judgment unfoldings
(`scripts/parametric_inventory.lean`, on demand). The exhibits above are
the other clients; the production-export layer (`DriverCollapse`,
`ProdLoop`, `ProdEntry`) is itself a client of adequacy.

## How to build and verify

From the repository root (offline; deps resolve through the container's
git redirects, which `scripts/capped` self-loads):

```bash
scripts/setup-cerberus-dep.sh        # once: the pinned semantics workspace
cd cerberus-heaplang
../scripts/capped ~/.elan/bin/lake build
```

A green build IS the verification run: it elaborates every proof
through the Lean kernel and then `Audit.lean` (the last import of the
library root), which (1) pins the exact axiom set of every public
export to the classical trio, (2) bounds every theorem of every module
by the trio, and (3) checks every constant of every kind for
`sorryAx`/`ofReduceBool`/`ofReduceNat`. Expected tail (the counts are
those at the time of writing — QA-2, commit noted in
`docs/2026-09-02_qa2-notes.md`; the build prints the current values;
the pin count moves with every slice that adds or retires an export):

```
info: CerberusHeapLang/Audit.lean:188:0: CerberusHeapLang export pins: 120 trio-exact
info: CerberusHeapLang/Audit.lean:188:0: CerberusHeapLang axiom sweep: 1155 theorems bounded by the trio
info: CerberusHeapLang/Audit.lean:188:0: CerberusHeapLang banned-axiom sweep: 1949 constants of every kind checked; sorryAx/ofReduceBool/ofReduceNat absent from all cones
Build completed successfully (444 jobs).
```

**The trust base is exactly three things** ([USER 2026-09-02]): the two
capped builds with their in-build axiom sweeps — (1) the repository
root package `RefinedCerberus` (`scripts/capped lake build` from the
repository root; its `RefinedCerberus/Audit.lean` sweeps the port's
own modules, which do not import this package), and (2) THIS package,
`cerberus-heaplang` (the command above; `CerberusHeapLang/Audit.lean`)
— plus the banned proof-method grep (`native_decide`/`bv_decide`/
`ofReduce*`) over both trees. This package's claims rest on its own
build alone; the root build is in the gate runner because the runner
is repository-wide (`scripts/test_unit.sh` gates 2 and 3). Everything
else in `scripts/test_unit.sh` is a SPEEDBUMP — a claim-point report
that catches honest drift, not a gate designed to survive an adversary:
the capability manifest is regenerated and diffed (a `Frag` constructor
without a mapped, exhibit-consumed rule is a red row), and the import
direction semantics → heap → rules → adequacy → clients is grepped.
`scripts/test_unit.sh --fast` runs the trust base only (intermediate
commits); the full run is for claim points. Auditors are briefed by
`../docs/AUDIT-BRIEF.md`.

Ask the kernel yourself (from `cerberus-heaplang/`):

```bash
../scripts/capped ~/.elan/bin/lake env lean --stdin <<'EOF'
import CerberusHeapLang
#print axioms CerberusHeapLang.project_triple
#print axioms CerberusHeapLang.project_triple_alloc
#print axioms CerberusHeapLang.struct_create_store_adequacy
#print axioms CerberusHeapLang.list_reverse_certified
#print axioms CerberusHeapLang.fib_certified_total
#print axioms CerberusHeapLang.exhibitA_prod
#print axioms CerberusHeapLang.list_reverse_certified_production
EOF
```

Every line must read `depends on axioms: [propext, Classical.choice,
Quot.sound]`; `sorryAx` anywhere is a failure. The statement surfaces of
the pinned exports are recorded in the committed signature snapshots
under `docs/` (`scripts/signature_snapshot.lean`, on demand): an
internals-only slice must leave them byte-identical.

## Registered divergences and seams

Open seams and deliberate divergences, each with its discharge path
and its home. Closed findings of the 2026-09-01 re-audit (R-01, R-02,
R-04 … R-11) are recorded once, in the closure table of the arc plan
(Records, below), not repeated here.

| Divergence / seam | Discharge / path | Home |
|---|---|---|
| Fuel side condition (no fuel parametricity): partial statements carry `esize e + n ≤ lemDefaultFuel`; production statements `k + 2 ≤ lemDefaultFuel` | a fuel-irrelevance theorem for `get_ctx`, or graceful driver exhaustion, would remove it | `Soundness.lean` header (FUEL HONESTY); `ProdEntry.lean` header |
| The tag-definition environment is an explicit parameter of the heap predicates and rules (`pointsToCell tds …`, `M.tagDefs`); the demos state footprints at `fmapEmpty`, which is what the synthetic file's `drive fmapEmpty` passes | by design ([AGENT 2026-09-02], DECISIONS.md: a program-wide constant of the language instance, as Caesium's global environment); struct/union layouts become expressible without restatement | `Heap.lean` header |
| Memory orders accepted arbitrarily (`Step.store`/`wp_store` at any `memory_order`) | mirror-true: the sequential driver drops `mo` (Driver.lean:273) | `Step.lean` |
| R-03 residual: the engine round is classified two-sidedly wherever the mirror steps (`step_iff_cerberusRound`); at mirror-STUCK configurations the engine's refusal is classified for store/load/create/case only (`cerberusRound_refused_*`); the other rows' refusal channels are `failwithI` panics (opaque constants — a kernel classification is impossible, not merely unproved), save's EVAL round, or the memop ND fork | per-row refusal theorems where a non-panic channel exists; panic channels stay one-sided unless the semantics repo replaces `failwithI` with value-level errors | `Round.lean` header; closure table |
| `Ewseq` at binder patterns, `Ecase`'s EVAL arm, pure exits beyond `PEsym`, the memop family beyond `PtrEq` and `eqPtrval`'s differing-provenance fork, the symbol-binder beta at annotated values | mechanical per-construct extensions (dischargeStep arm + Step rule + rule at each stratum); the fork is a real `msum` (CerbMem.lean:1753) | `Step.lean` header; `Soundness.lean` memop arm |
| Arrays are ONE allocation, not a ∗ of per-element cells: the engine bounds-checks against the pointer's provenance allocation and `arrayShiftPtrval` preserves provenance — C's object model | forcing fact about Cerberus; per-element structure lives in the invariant + decode premises | `ArrayExhibit.lean` header |
| Metadata at a fraction as the exclusivity anchor; persistent stratum instead of a liveness token (no `kill`) | named mover: the kill arc adds the donor's `alloc_alive`/freeable split and moves the anchor | `Heap.lean` header |
| REMOVE-ANNOT value protocol; canonical-annotation subrelation | deliberate, engine-faithful readout composition | `Step.lean` header |

**Deferred design experiment — parametric semantics interfaces.**
DEFERRED, possibly permanently ([USER 2026-09-02], DECISIONS.md): a
measured inventory of what each rule proof depends on in `Step` and the
memory state, and a draft memory/environment/control interface. Not
adopted — with one instance the interface relocates the same proofs
behind a class, and RefinedC itself proves memory rules by inversion.
The rules are proved directly against `Step` and `CerbMem.MemState`.
Re-open only for a second memory-model instance or a type layer needing
an abstract memory contract. Record: the parametric-semantics spike
note (Records, below); the inventory script
`scripts/parametric_inventory.lean` stays as an on-demand instrument.

## The modules

In import order, one line each (the walkthrough reads them in the same
order):

| Module | Contents | Headline |
|---|---|---|
| `Step.lean` | the fragment's mirror small-step over the engine's generated AST/state types, indexed by the explicit `MachineCtx`; hand-written, zero authority until certified | `Step`, `MachineCtx` |
| `EnvLaws.lean` | lawfulness of the engine's symbol order (`Std.TransCmp`), `SymFrame`, lookup-after-add | `envAdd_lookup` |
| `Heap.lean` | the split ghost carrier (per-byte heap, per-allocation metadata heap, allocator cursor) coupled to the real `MemState` by `CohG`; views, cells, points-to, the persistent stratum, `allocCap`; the `storeM`/`loadM`/`allocateObject` success seams | `pointsToCell` (`↦c[tds]`), `pointsToView`, `allocMeta`, `allocCap`, `storeM_success`, `loadM_success` |
| `Lang.lean` | the iris-lean `Language` instance over `Step`; no `Language.Context` (falsified by `Erun`); the `SpikeGF` ghost functors | `instance : Language CoreRt Mem Empty CoreRVal` |
| `Rules.lean` | the base stratum: the two small axioms at the raw WP (generic in `M` and `ρ`), the readout combinator, the value dichotomy of an annot-wrapped term | `wp_store`, `wp_load`, `stateInterp_readout` |
| `Wps.lean` | the partial label-context judgment as a guarded fixpoint; its rule set incl. `wps_create`, statement-level framing, `blockSpecs_intro`; the Löb collapse into the base WP | `wps`, `wps_seq`, `wps_create`, `blockSpecs_intro`, `wps_frame_labels`, `wps_sound` |
| `Wpt.lean` | the total judgment by recursion on the budget; variant-indexed label preconditions with the mandatory back-edge decrease; the total rule set incl. `wpt_create`; collapse into Iris TotalWeakestPre | `wpt`, `wpt_run`, `wpt_create`, `blockSpecsT_intro`, `wpt_frame_labels`, `wpt_sound` |
| `Soundness.lean` | the boundary module: per-construct certification of `Step` against `step_ctx` + the driver's discharge (`dischargeStep`); the fragment cone `Frag`; the unified step-match at any context | `Frag`, `engine_step_matchU`, `Decomp.step_factor` |
| `Round.lean` | the engine-facing one-round relation and its exhaustive classification | `CerberusRound`, `cerberusRound_classify`, `step_iff_cerberusRound` |
| `Adequacy.lean` | `driveU`/`drive`/`driveJ`; Iris adequacy with the ghost state constructed; the allocation-aware launch; the semantic triples; THE TWO PROJECTIONS (footprint-only and allocating) and the pure-consequence lemmas; the public readouts | `project_triple`, `MemTripleU`, `project_triple_alloc`, `MemTripleU_alloc`, `semantic_triple_soundU`, `engine_adequacyU`, `launchResources`, `cellOwn_readout` |
| `TotalAdequacy.lean` | termination over the unified relation (`twp_total` as-is) and the generic measure→drive-fuel simulation on the size potential `pot`; allocation-aware variants | `wpt_strongly_normalizing`, `wpt_engine_boundU`, `wpt_engine_boundJ`, `wpt_engine_boundU_alloc` |
| `API.lean` | THE PUBLIC SURFACE as one import; the public/internal table | the header table |
| `Examples/Layout.lean` | example support, not logic: `intTy`, the 5/6/7 values and byte images, canned exhibit shapes | `intTy`, `sevenBytes` |
| `Examples/ReadinessSmoke.lean` | the readiness smoke test: a two-field object predicate and its rules from the API alone | `twoField`, `twoField_create` |
| `Exhibit.lean`, `LoopExhibit.lean`, `FibExhibit.lean`, `DivergeExhibit.lean`, `ArrayExhibit.lean`, `StructExhibit.lean`, `AllocExhibit.lean`, `ListRevExhibit.lean`, `TreeRotExhibit.lean`, `CaseExhibit.lean`, `WseqExhibit.lean` | the exhibits (table above) | — |
| `DriverCollapse.lean` | the production scheduler/ND/readout collapsed onto the drive loop, proved from the driver's own round functions | `loop_step_frag`, `driver2_done`, `finalize_done` |
| `ProdLoop.lean` | the total judgment drives the production driver's own per-thread loop | `wpt_driver_done`, `wpt_driver_done_alloc` |
| `ProdEntry.lean` | the cold start from the shipped `initial_driver_state`; the pipeline theorem; the registration ties | `prod_run_eqJ`, `fib_labeledAt_production`, `counter_loop_certified_registration` |
| `ProdExhibit.lean`, `ProdLoopExhibit.lean` | the production-lane exports (table above) | `exhibitA_prod`, `*_production` |
| `Audit.lean` | the in-build axiom gate: exact export pins, the exhaustive bound, the banned-axiom sweep | the sweeps |

## Records

History and provenance live in dated files, not here. Rulings:
`../docs/DECISIONS.md` (append-only, [USER]/[AGENT] tagged). The arc
that produced the current tree and its finding-by-finding closure
table: `docs/2026-09-01_alloc-arc-plan.md` (charter: the 2026-09-01
skeptical re-audit, `../docs/2026-09-01_cerberus-heaplang-skeptical-re-audit.md`).
Slice records, newest first: `docs/2026-09-02_qa2-notes.md` (the
quality audit's pruning/restatement slice: the dead production island
and the consumerless names retired with their zero-consumer traces,
the base stratum demoted, the statement cosmetics), `docs/2026-09-02_qa1-notes.md`
(the spec generalizations within the frozen fragment),
`docs/2026-09-02_quality-audit.md` (the audit), `docs/2026-09-02_p6.1-notes.md` (the
fresh-eyes review's findings closed: the allocating projection, the
exhaustive hypothesis column, the measured kernel-opaque list, the
configuration answer), `docs/2026-09-02_p6-fresh-eyes-review.md` (the
review), `docs/2026-09-02_p6-notes.md` (the documentation rewrite),
`2026-09-02_projection-notes.md`, `2026-09-02_p5-notes.md`,
`2026-09-02_p4-notes.md`, `2026-09-02_parametric-semantics-spike.md`,
`2026-09-02_repin-notes.md`, `2026-09-02_p3.5-notes.md`,
`2026-09-01_p{0,1,2,3}-notes.md`, the foundations-arc phase notes, and
the founding report `2026-08-30_spike-report.md`. Statement-surface
snapshots: `docs/*-signatures-*.txt`.

---

Built by AI agents (Claude, Anthropic) under the direction and review
of Mike Dodds.
