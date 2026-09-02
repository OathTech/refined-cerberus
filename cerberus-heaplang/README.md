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
Core: `store`/`load`/`create` actions (evaluated operands, and the
operand-evaluation form the engine dispatches when "the operands are
not all values"), the `PtrEq` memop, strong sequencing `Esseq` at the
wildcard, `Specified`-binder and plain-symbol-binder patterns, weak
sequencing `Ewseq` at the wildcard, `Esave` at any initializers within
the evaluator's fuel, `Eif`, the context-discarding jump `Erun`,
value-scrutinee `Ecase`, `PEsym`-shaped pure exits,
`PEval`/`PEsym`/integer-`PEop`/`PEarray_shift` operands, and the
run-time annotation residue. The per-construct authority is the
inductive `Frag` (Soundness.lean), the premise of every adequacy
theorem; the generated [capability manifest](docs/CAPABILITY_MANIFEST.md)
lists one row per `Frag` constructor with the rule covering it and the
exhibit modules whose proofs consume that rule (18 rows).

**Pure operands carry their own static fuel bound.** The engine's
pure-expression evaluator is fuelled at the same budget as its redex
search (`step_eval_pexpr`/`pull_constrained` draw from
`lemDefaultFuel`), so every `Frag` constructor that evaluates a pure
operand — `if_` (the guard), `run` (the jump arguments), `save` (the
initializers), `load_op`/`memop_op`/`store_op` (the operands the engine
evaluates before dispatching the action) — carries the static premise
`peDepth pe ≤ lemDefaultFuel` per operand, where `peDepth`
(Soundness.lean) is the operand's syntactic depth (1 at a value or a
symbol, `1 + max` at `PEop`/`PEarray_shift`); the three
operand-evaluation constructors also restrict their operands to the
sub-grammar `PePure` the mirror evaluator covers (values, symbols,
`PEop` binops, `PEarray_shift`), while for `if_`/`run`/`save` the grammar
is enforced by the rule's `evalPexpr … = some …` premise
(`evalPexpr_shape`: success implies membership). Verbatim, the premises
of `Frag.store_op`: `(hp2 : PePure pe2) (hp3 : PePure pe3) (hd2 : peDepth
pe2 ≤ lemDefaultFuel) (hd3 : peDepth pe3 ≤ lemDefaultFuel)`. Like the
`pot` bounds below, this bound is `rfl` for every authored program
(`peDepth_sym_le`, `peDepth_val_le`) and never mentions the run length;
unlike them it lives inside `Frag`, so it appears on no exhibit as a
separate hypothesis.

**Every node of a fragment program carries the empty static annotation
list.** Each `Frag` constructor, and each redex spelling it ranges over
(`storeRedex`, `loadRedex`, `createRedex`, `loadOpRedex`,
`storeOpRedex`, `memopRedex`, `pureRedex`, `saveRedex`, `ifRedex`,
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

**Deliberately not here.** `kill`/free (no dispose rule, hence no
liveness token — allocation metadata is immutable); procedures (no call
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
`list_reverse_certified_production` (ProdLoopExhibit.lean). Their
execution function is the shipped `CerbND.runND (drive fmapEmpty false
file args) (initial_driver_state sup file fs).1`, the composite the
cerberus-lean executable runs, applied to the authored program wrapped
by `prodFile` (the synthetic one-procedure file); no package-defined
driver appears in their statements, and they carry no termination
hypothesis (only the explicit in-budget bounds `hfuel` where the step
count depends on an input). These four are THE root-of-trust exports of this package —
the closed shipped-driver statements. They are reached through
`prod_run_eqJ` (ProdEntry.lean), which is generic collapse machinery
rather than a closed statement: its delivery premise `DriverDoneAt`
(ProdLoop.lean) and its label tie `LabeledAt` are package-defined, and
the four statements discharge them.

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
Iris precondition is footprint ownership ∗ `allocCap M.tagDefs reqs`
(the capacity every `create` consumes, walkthrough §3.2, §4) and whose
conclusion is `MemTripleU_alloc`: `MemTripleU` with the launch premise
`LaunchCoh M.tagDefs σ (P ∪ R) reqs` in place of `Sat` — `Sat` plus
allocator health (every id from the engine's `nextAllocId` up is
unallocated and not dead, the footprint sits at or above the downward
cursor `lastAddress`, the plan `reqs` fits the actual cursor, cursor
`≤ 2^64`). The premise genuinely differs (a memory can carry the
footprint with its cursor on top of it), so the allocating triple is a
separate definition; `MemTripleU` implies `MemTripleU_alloc` at every
plan (`MemTripleU_alloc_of_MemTripleU`). The production cold-start
memory satisfies it (`prodMem₀_launchCoh`, ProdEntry.lean);
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
| `struct_wps_views`, `cell_read_shared_wps`, `struct_x_read_persist_wps`, `struct_create_store_wps` (StructExhibit.lean) | the view/fraction/persistence laws as clients; allocate-then-initialize from `allocCap` alone (Iris-level triples) | — (Iris) | all: `{hlc GF} [SpikeGS hlc GF] {M Ls} loc ann`; `_views`: `mo mo' bty id a b0 b1 b2 b3`, the three field lengths, `ev0 evs`; `cell_read_shared`: `pv mo bs bs' ρ`, `htrap`; `_x_read_persist`: `mo id a q dqb ρ`; `_create_store`: `aprov alignN pref mo pbty vbty ev0 evs`, `SymFrame ev0`, `∀ x, resolveExtern M.extern x = x` |
| `struct_create_store_adequacy`, `struct_create_store_adequacy_prodMem₀` (StructExhibit.lean) | allocate-then-initialize as `MemTripleU_alloc spikeCtx spikeEnv prog ∅ [⟨8, structTy⟩] ψ`, an instance of `project_triple_pure_alloc`; `_prodMem₀` fixes the memory to the production cold start | `driveU spikeCtx` — PROVISIONAL | `{GF} [SpikeGpreS GF]`, `loc ann pref mo pbty vbty`; `_prodMem₀` adds `n aids` |
| `alloc_two_creates_wps`, `alloc_create_wpt`, `alloc_create_launch_smoke` (AllocExhibit.lean) | the allocation rules' local consumers; a bare `create` from the cold-start memory delivers a pointer at drive length 2 | `driveU spikeCtx` — PROVISIONAL | `_wps`: `{hlc GF} [SpikeGS hlc GF] {M Ls} al₁ al₂ pref₁ pref₂ bty ev0 evs`; `_wpt`: `{hlc GF} [SpikeGS hlc GF] {M Ls} al pref ρ`; `_launch_smoke`: `pref aids` |
| `list_reverse_certified`, `list_reverse_demo`, `list_reverse_certified_total` (ListRevExhibit.lean) | in-place reversal of a seeded chain next to an arbitrary disjoint frame — same allocation ids in reversed order, footprint equality on the maps, frame verbatim, at every drive length; total at `13 * ns.length + 7`; the demo fixes a 3-node chain | `driveU (procCtx …)` — PROVISIONAL | `loc ann ra mo pbty cbty bbty nbty ubty sbty`, `ns head m₀`, `hseed : SeedChain m₀ head ns`, `R`, `hR : m₀ ##ₘ R`, `σ₀`, `hcoh : Sat fmapEmpty σ₀ (m₀ ∪ R)`; `_certified` adds `nsteps aids`, `_total` adds `aids`; `_demo` replaces `ns head m₀ hseed` by the 3-node constants |
| `tree_rotate_certified`, `tree_rotate_certified_total` (TreeRotExhibit.lean) | binary-tree right rotation at the same statement shape; total at drive length 19 | `driveU spikeCtx` — PROVISIONAL | `loc ann mo xbty ybty bbty ubty`, `idx idy vx vy ta tb tc px m₀`, `hseed : SeedTree m₀ px (.node idx vx (.node idy vy ta tb) tc)`, `R`, `hR`, `σ₀`, `hcoh`; `_certified` adds `sbty`, `n aids`; `_total` adds `aids` |
| `case_certified`, `wseq_certified` (CaseExhibit.lean, WseqExhibit.lean) | the `Ecase`/`Ewseq` consumers | `driveU spikeCtx` — PROVISIONAL | `{GF} [SpikeGpreS GF]`, `v` resp. `v1 v2`, `σ₀ n aids` |
| `diverge_total_unprovable` (DivergeExhibit.lean) | the negative test: a total derivation for the self-jump loop is `False` | — | `{GF} [SpikeGpreS GF]`, `ra σ₀ m₀`, `hcoh : Coh fmapEmpty σ₀ m₀`, and the statement's own quantifiers `Ls Ψ k` and the derivation from `m₀`'s cell ownership |
| `exhibitA_prod` (ProdExhibit.lean) | the production run of `lets p = create(4,int) in lets _ = store(int, p, 7) in load(int, p)` is the singleton `Active` execution delivering 7, the final memory holding 7's image at the program's own cell | shipped pipeline — ROOT OF TRUST | `sup fs args` |
| `fib_certified_production`, `counter_loop_certified_production`, `list_reverse_certified_production` (ProdLoopExhibit.lean) | the loop programs on the shipped pipeline; counter and reversal bind their engine-created cells and enter their loops through `save` with live initializers | shipped pipeline — ROOT OF TRUST | fib: `sup ra n sbty ibty abty bbty`, `0 ≤ n`, `2 * n.toNat + 6 ≤ lemDefaultFuel`, `fs args`; counter: `sup ra mo bty xbty cbty sbty n`, `0 ≤ n`, `6 * n.toNat + 8 ≤ lemDefaultFuel`, `fs args`; reversal: `sup ra mo bty sbty pbty cbty bbty nbty ubty fs args` |
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
   (`ShippedRefusal`: ILLTYPED / KILL / FORK / PANIC) or one of the
   four registered gaps (`OpenRound`; the register below), so the logic
   is SOUND and COMPLETE for the fragment up to those gaps. The
   remaining vocabulary
   is the pure readout predicates (`Sat`/`CellCoh`, `SeedChain`,
   `SeedTree`, `readBytesFrom`) and the authored programs. iris-lean
   appears only inside the kernel-checked proof terms and contributes
   no axiom: every export's axiom set is exactly `propext`,
   `Classical.choice`, `Quot.sound` (`Audit.lean`). For these
   statements iris-lean is checked, not trusted.
2. **The reusable rules are stated in Iris.** `pointsToCell`,
   `cellOwn`, `allocCap`, the WP and BI connectives, and `CohG` (which,
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
| Mirror completeness holds UP TO FOUR REGISTERED GAPS (`OpenRound`, Round.lean; `frag_round_complete`): (a) the LETS-ANNOT beta at the symbol binder (`lets x = {A}v in e`) — the engine's tau succeeds, no `Step.sseq_sym_annot` rule; (b) a load/store ACTION_EVAL whose pointer operand evaluates to a non-pointer value — the engine's evaluation round succeeds into the ill-typed action it reports ILLTYPED on next; (c) operand evaluation outside the mirror evaluator `evalPexpr` (unbound symbols, binops outside the mirrored eight or at non-integer operands, the non-`PePure` pure language of `if_`/`run`/`save` initializers) — the engine's own evaluator decides; (d) a jump at a context without a current procedure. Everywhere else a mirror-stuck fragment configuration is an engine refusal in the engine's vocabulary (`ShippedRefusal`: ILLTYPED `[Step_error2 msg]`, KILL `NDkilled r` from the shipped `advance_step`, FORK ≥ 2 `CerbND.runND` executions, PANIC the engine's own `failwithI`) | (a) the mechanical rule + its `Step.sseq_inv` ripple; (b) generalize `Frag.load`/`Frag.store`'s pointer slot and `Step.load_eval`/`store_eval` to any value; (c) a mirror evaluator complete relative to `eval_pexpr_aux2` on the fragment's operand grammar, or a recorded grammar narrowing; (d) by design (every shipped thread in a procedure body has a current procedure) | `Round.lean` (`OpenRound`); `ARCHITECTURE.md` §2, §7; `docs/2026-09-02_mirror-completeness-notes.md` |
| Freshness is footprint-relative: `LaunchCoh` constrains TRACKED cells only (`id_lt`, `addr_lo`), so a `create` (`wps_create`/`wpt_create`) is fresh from the logical footprint, not from untracked allocations an arbitrary concrete state may hold below the cursor (`allocateObject` scans no ranges); every owned cell is protected; the production cold-start state `prodMem₀` contains only the allocator-created errno allocation and no dead allocations (`prodMem₀_allocations`, `prodMem₀_deadAllocations`), and `prodMem₀_launchCoh` proves `LaunchCoh` for the empty footprint and any fitting plan — no global well-formedness theorem exists yet | a global memory well-formedness invariant (`MemWF`: id discipline, live/dead consistency, range disjointness of all live allocations, cursor bounds) with its initialization proof, in the launch premise and the state interpretation, registered for the malloc/free arc; "globally well formed" is reserved for it | `Adequacy.lean` (`LaunchCoh` section), `Heap.lean` header; walkthrough §4 |
| Arrays are one allocation, not a ∗ of per-element cells: the engine bounds-checks against the pointer's provenance allocation and `arrayShiftPtrval` preserves provenance | forcing fact about Cerberus; per-element structure lives in the invariant + decode premises | `ArrayExhibit.lean` |
| Allocation metadata at a fraction as the exclusivity anchor; a persistent stratum instead of a liveness token (no `kill`) | the dispose rule adds the donor's `alloc_alive`/freeable split and moves the anchor | `Heap.lean` header |
| Allocation capacity is an ordered plan (`allocCap reqs`), not an additive resource: it cannot be split across ∗, only weakened to a prefix (`allocCap_weaken`) | an additive byte budget as a derived face (walkthrough §4) | `Heap.lean`; walkthrough §4 |
| Read-only allocations cannot be described: `CellCoh.alloc`/`MetaCoh.alloc` fix `isReadonly = .IsWritable` and `MetaCell` records no read-only flag, so a fractional `pointsToCell` still asserts a writable allocation | a read-only flag in `MetaCell`, with writability demanded by the store rule only | `Heap.lean` |
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
`Classical.choice`, `Quot.sound` (`Audit.lean`: 139 export pins; every
theorem of every module bounded). "Frag" = the fragment `Frag` at a
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
        │    COMPLETE up to four registered gaps: frag_round_complete
        │      mirror stuck ⇒ ShippedRefusal (ILLTYPED/KILL/FORK/PANIC) ∨ OpenRound
        │      (cerberusRound_classify: value_done/value_annot/step/refused/open_)
        ▼
   iris-lean Language instance over Step   (Lang.lean: instance Language CoreRt
     Mem Empty CoreRVal; NO Language.Context — Erun discards its context)
        ▼
   state interpretation + raw resources   (Heap.lean: SpikeState / CohG over the
     real MemState; bytesOwn, metaOwn, cursorOwn → pointsToView, cellOwn,
     pointsToCell, allocMeta, locInBounds, allocCap)
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
    wp_strong_adequacy_gen, ghost state      engine_step_matchU discharges one engine
    CONSTRUCTED by genHeap_init;             step per budget unit; no Iris adequacy in
    launchResources under LaunchCoh mints    the cone; wpt_sound is the Iris collapse)
    the cursor and grants allocCap)
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
     list_reverse_certified_production)                          [∀ sup fs args]
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
(`wps_create`/`wpt_create` from `allocCap`); frame across back edges
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
manifest reports the fragment rows), except three kept as laws of the
logic: `allocMeta_agree`, `allocCap_weaken`, and the raw-WP `wp_load`
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
carrier, the allocator cursor and its introduction `allocCap_intro`
(clients receive `allocCap` from the launchers), `Step`/Soundness/
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
info: CerberusHeapLang/Audit.lean:216:0: CerberusHeapLang export pins: 139 trio-exact
info: CerberusHeapLang/Audit.lean:216:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (N swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:216:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (M constants of every kind swept, internal details included — count informational, environment-dependent)
Build completed successfully (… jobs).
```

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
| `Heap.lean` | the split ghost carrier (per-byte heap, per-allocation metadata heap, allocator cursor) coupled to the real `MemState` by `CohG`; views, cells, points-to, the persistent stratum, `allocCap`; the `storeM`/`loadM`/`allocateObject` success lemmas | `pointsToCell`, `pointsToView`, `allocMeta`, `allocCap`, `storeM_success`, `loadM_success` |
| `Lang.lean` | the iris-lean `Language` instance over `Step`; no `Language.Context` (falsified by `Erun`); the ghost functors | `instance : Language CoreRt Mem Empty CoreRVal` |
| `Rules.lean` | the atomic step specifications and their lifting to the raw WP; `wp_store`, `wp_load`; the readout combinator | `AtomicStep`, `store_atomic`, `wp_of_atomic`, `wp_store`, `stateInterp_readout` |
| `Wps.lean` | the partial label-context judgment as a guarded fixpoint; its rule set; statement-level framing; the Löb collapse into the raw WP | `wps`, `wps_seq`, `wps_create`, `blockSpecs_intro`, `wps_frame_labels`, `wps_sound` |
| `Wpt.lean` | the total judgment by recursion on the budget; variant-indexed label preconditions with the mandatory back-edge decrease; collapse into Iris `TotalWeakestPre` | `wpt`, `wpt_run`, `wpt_create`, `blockSpecsT_intro`, `wpt_frame_labels`, `wpt_sound` |
| `Soundness.lean` | the boundary module: the per-construct engine equations of `Step` against `step_ctx` (`step_ctx_*`), the fragment `Frag`, the decomposition `Decomp`; the discharge device `dischargeStep`/`outcomesU` and its step match (`outcomesU_of_step`, the `driveU` lane's device) | `Frag`, `Decomp.step_factor`, `step_ctx_store` |
| `Round.lean` | the shipped engine round (one iteration of the driver's thread loop, in the driver's own vocabulary), the certification `engine_step_matchU`, mirror completeness per redex root and its assembly, the exhaustive classification, the shipped refusal vocabulary and the registered gaps | `CerberusRound`, `engine_step_matchU`, `frag_round_complete`, `complete_*`, `cerberusRound_classify`, `ShippedRefusal`, `OpenRound` |
| `Potential.lean` | the step-monotone size potential `pot` — the static fuel bound | `pot`, `Frag.esize_le_pot`, `Frag.pot_step_bound` |
| `Adequacy.lean` | the drive `driveU`; Iris adequacy with the ghost state constructed; the allocation-aware launch; the triples; the projections and the pure-consequence lemmas | `project_triple_pure`, `MemTripleU`, `project_triple_pure_alloc`, `MemTripleU_alloc`, `engine_adequacyU` |
| `TotalAdequacy.lean` | the budget-to-drive-length simulation on `pot` | `wpt_engine_boundU`, `wpt_engine_boundU_alloc` |
| `API.lean` | the public surface as one import; the public/internal table | the header table |
| `Examples/Layout.lean`, `Examples/ReadinessSmoke.lean` | example support (`intTy`, byte images); the two-field object predicate and its rules from the API alone | `twoField`, `twoField_create` |
| `Examples/MirrorCoverage.lean` | mirror-level coverage witnesses proved directly against `Step` (the mixed `store` operand shapes) — a semantic regression module, NOT a client; the only other direct `Step` use outside the semantics layer is the negative test `DivergeExhibit.lean` (its header states the exception) | `store_sym_lit_step`, `store_lit_sym_step` |
| `Exhibit.lean`, `LoopExhibit.lean`, `FibExhibit.lean`, `DivergeExhibit.lean`, `ArrayExhibit.lean`, `StructExhibit.lean`, `AllocExhibit.lean`, `ListRevExhibit.lean`, `TreeRotExhibit.lean`, `CaseExhibit.lean`, `WseqExhibit.lean` | the exhibits (table above) | — |
| `DriverCollapse.lean` | the production scheduler/ND/readout collapsed onto the drive loop, proved from the driver's own round functions | `loop_step_frag`, `driver2_done`, `finalize_done` |
| `ProdLoop.lean` | the total judgment drives the production driver's per-thread loop | `wpt_driver_done`, `wpt_driver_done_alloc` |
| `ProdEntry.lean` | the cold start from the shipped `initial_driver_state`; the pipeline theorem; the registration ties | `prod_run_eqJ`, `fib_labeledAt_production` |
| `ProdExhibit.lean`, `ProdLoopExhibit.lean` | the production statements (table above) | `exhibitA_prod`, `*_production` |
| `Audit.lean` | the in-build axiom check: exact export pins, the exhaustive bound, the banned-axiom sweep — internal details included, the whole package | the sweeps |

## Records

History, provenance and process live in dated files, not here.
Rulings: `../docs/DECISIONS.md` (append-only, `[USER]`/`[AGENT]`
tagged). The audit and review record of the current tree, newest
first: `docs/2026-09-02_audit-response-4-notes.md` (the response to
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
review, A-), `docs/2026-09-02_pr2-notes.md` (the first review's
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
