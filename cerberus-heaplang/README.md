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
the operand-evaluation forms), the `PtrEq` memop, strong sequencing
`Esseq` at wildcard, `Specified`-binder and plain-symbol-binder
patterns, weak sequencing `Ewseq` at wildcard, `Esave`/`Eif`/the
context-discarding `Erun`, value-scrutinee `Ecase`, `PEsym`-shaped pure
exits, `PEval`/`PEsym`/integer-`PEop`/`PEarray_shift` operands, and the
run-time annotation residue. The per-construct authority is the
inductive `Frag` (Soundness.lean) — the adequacy premise — and the
generated [capability manifest](docs/CAPABILITY_MANIFEST.md) lists one
row per `Frag` constructor with the rule covering it and the exhibit
modules whose proofs consume that rule (18 rows, 0 red). Value-scrutinee
`Ecase` and wildcard `Ewseq` have rules at the partial stratum only
(`wps_case_value`, `wps_wseq`); every other construct has rules at both
strata.

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
- `Eunseq`, the memop family beyond `PtrEq` (and `PtrEq`'s
  differing-provenance nondeterministic fork), `Ecase` on a non-value
  scrutinee, `Ewseq` at binder patterns, pure exits beyond `PEsym`:
  each is a fail-closed ABSENCE of a mirror step, not a rule with a
  hidden assumption.
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

for P and Q "just memory + pure properties". The theorem that realizes
it is `project_triple` (Adequacy.lean): ANY Iris triple with a
concrete-map precondition and an ARBITRARY Iris postcondition projects
to the boring triple `MemTripleU` over engine states. Symbol by symbol:

| Shape | In the tree |
|---|---|
| `s` | `σ : Mem` = the engine's `CerbMem.MemState`, arbitrary outside the footprint |
| `s \|= P` | `Sat M.tagDefs σ (P ∪ R)` — `Sat` = `Coh` (Heap.lean): every footprint cell live, writable, in bounds, exactly those bytes, pairwise disjoint; `R` is the arbitrary rest, returned to the post (the frame, built into `MemTripleU`) |
| `prog` | `(e, ρ)` at a machine context `M`; `M.thread e ρ` is the engine's `thread_state` |
| `core_exec(prog, s) ~~> term` | `driveU M aids n (M.thread e ρ) σ` — the iterated `{step_ctx → dischargeStep}` round of the sequential driver, for every action-id supply `aids` and every fuel `n` within the engine's own `get_ctx` budget (`esize e + n ≤ lemDefaultFuel`, likewise for every registered label body) |
| `term = some(s')` | `driveU … = .done v σ'`; the two other conjuncts, `≠ .killed r` (no undefined behaviour, no error kill) and `≠ .stuck` (no refusal, no off-protocol step); `.more` (fuel exhaustion) is unconstrained — partial correctness |
| `s' \|= Q` | `post R v σ'` — for `project_triple`, every pure `ψ` that `Q w ∗ cells(R) ∗ metaInterp mm ∗ byteInterp mb` entails under any coupling witness `CohG σ' mm mb mk`; the pure-consequence lemmas (`cellOwn_consequence`, `pointsToCell_consequence`, `cells_consequence`, `sep_/or_/exists_/pure_consequence`) turn this into `CellCoh σ' i c` facts about the final memory |

`SemTripleU` (footprint post `Q : CellMap`, `Sat σ' (Q ∪ R)`) is the
cells-shaped instance (`SemTripleU_iff_Mem`, definitional);
`semantic_triple_soundU` is `project_triple` at that post; `SemTriple`
is its fixed-profile instance (`SemTriple_iff_U`); `drive`/`driveJ` are
`driveU` at the straight-line/proc-carrying contexts.

**The production lane.** For closed programs the execution function in
the statement is the shipped pipeline itself — `CerbND.runND
(Driver.drive …) (initial_driver_state sup file fs).1` — reached from the
same logic through the generic driver collapse (`wpt_driver_done_alloc`
→ `prod_run_eqJ`). The statements quantify over the file-system state,
argv and the entry's symbol supply `sup` (the fragment never reads it).

**The exhibits** (every one pinned trio-exact in `Audit.lean`; Lane:
`drive`/`driveJ` = the driver's round loop projected to (thread,
memory), `production` = the shipped pipeline; hypotheses beyond the
seeded footprint and the engine's own fuel budget are listed):

| Theorem (file) | Says | Lane | Hypotheses |
|---|---|---|---|
| `exhibitA_semantic`, `exhibitA_engine`, `exhibitA_total` (Exhibit.lean) | store 7 then load: never kills; delivers `Specified(7)`; the total form is an unconditional `.done` equation at fuel 6 | drive | seeded cell |
| `exhibitB_semantic`, `exhibitB_engine` (Exhibit.lean) | THE FRAME: `⦃x ↦ - ∗ y ↦ a⦄ store(x,7) ⦃x ↦ 7 ∗ y ↦ a⦄` over engine configurations, `y` and all unnamed rest verbatim | drive | seeded cells |
| `exhibitC_semantic`, `exhibitC_engine` (Exhibit.lean) | sequenced stores to disjoint cells both land | drive | seeded cells |
| `counter_loop_certified`, `counter_loop_certified_irrelevant_binding` (LoopExhibit.lean) | the first loop: save/guard/store/back edge, final bytes data-dependent; run from an entry frame with an unrelated binding | driveJ | seeded cell |
| `fib_certified`, `fib_certified_total`, `fib_terminates` (FibExhibit.lean) | iterative fib delivers `fib n`; TOTAL: `driveJ … (2·n+4) … = .done (fib n) σ₀` with no fuel hypothesis; strong normalization | driveJ | `0 ≤ n` |
| `array_sum_certified` (ArrayExhibit.lean) | array walk with real pointer arithmetic delivers `vs.sum`, array preserved | driveJ | seeded one-allocation array, per-element decode facts |
| `struct_update_certified`, `struct_wps_views`, `cell_read_shared_wps`, `struct_x_read_persist_wps`, `struct_create_store_wps`, `struct_create_store_adequacy` (StructExhibit.lean) | two-field struct update; the view/fraction/persistence laws as clients; allocate-then-initialize from `allocCap` alone, launched from the production cold-start memory | drive | seeded struct / plan |
| `alloc_two_creates_wps`, `alloc_create_wpt`, `alloc_create_launch_smoke` (AllocExhibit.lean) | the public allocation rules' local consumers; a bare create from the cold-start memory delivers a pointer at `driveU` fuel exactly 2 | driveU | plan |
| `list_reverse_certified`, `list_reverse_demo`, `list_reverse_certified_total`, `list_reverse_terminates` (ListRevExhibit.lean) | THE CANONICAL EXHIBIT: in-place reversal of a seeded chain next to an arbitrary disjoint frame — same allocation ids in reversed order, footprint equality on the maps, frame verbatim; TOTAL at the derived bound `13·|ns|+7`; termination; the demo instantiates a 3-node chain | driveJ | `SeedChain m₀ head ns`, `m₀ ##ₘ R` |
| `tree_rotate_certified`, `tree_rotate_certified_total` (TreeRotExhibit.lean) | the second client: binary-tree right rotation at the same statement shape, zero core-logic edits; total at constant budget 19 | drive | `SeedTree m₀ px t`, disjoint frame |
| `case_certified`, `wseq_certified` (CaseExhibit.lean, WseqExhibit.lean) | the `Ecase`/`Ewseq` rows' consumers | drive | — |
| `diverge_total_unprovable` (DivergeExhibit.lean) | THE NEGATIVE TEST: a total derivation for the self-jump loop is `False` — the mandatory back-edge decrease is what blocks it | — | — |
| `exhibitA_prod` (ProdExhibit.lean) | the production run of `lets p = create(4,int) in lets v = 7 in lets _ = store(p,v) in load(p)` is the singleton Active execution delivering 7, the final memory holding 7's image at the program's own cell (existential id/address); proof = one total judgment `progAProd_wpt` through the PUBLIC `wpt_create` | production | `fs`, `args`, `sup` only |
| `fib_certified_production`, `counter_loop_certified_production`, `list_reverse_certified_production` (ProdLoopExhibit.lean) | the loop programs on the shipped pipeline; the counter and reversal programs BIND their engine-created cells (`ctrProd_wpt`, `lrProd_wpt`: creates through `wpt_create`, the generic list logic consumed verbatim at existential ids) | production | `0 ≤ n` + fuel budget (fib, counter); `fs`, `args`, `sup` |
| `counter_loop_certified_registration` (ProdEntry.lean) | the counter loop with its label map DERIVED from the shipped registration (`collect_labeled_continuations_NEW`) | driveJ | as `counter_loop_certified` |

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
  workspace nor its lem runtime (`LemLib`) declares an axiom; the
  engine's kernel-opaque constants (`CerberusFresh`'s native
  `md5Hex`/`digestIO`, LemLib's `fuelExhausted` exhaustion leaf, the
  `failwithI` panic) enter no axiom cone and cannot be unfolded by any
  proof — the fuel side condition and the well-formedness premises
  below are how the package stays away from them.
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
  false for the fragment. Sequencing is therefore proved directly
  (`wp_sseq`, `wps_seq`, `wpt_seq`), and the label-context judgments
  `wps`/`wpt` carry jumps through per-label preconditions instead of a
  bind rule — the classical treatment of `goto`-like control.
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
trio (`Audit.lean`: 107 export pins, every theorem of every module
bounded). "Frag" = the fragment cone `Frag` at a `SeqWF` context with
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
   base WP rules   (Rules.lean: wp_store, wp_load, wp_sseq, triple_frame,
     triple_conseq, triple_seq — one unfolding against Step + real storeM/loadM)
        ▼
   statement judgments   (Wps.lean: wps = guarded fixpoint; wps_* rules,
     wps_create, blockSpecs_intro, wps_frame_labels; wps_sound ⇒ base WP  [Löb])
                         (Wpt.lean: wpt by recursion on the budget; wpt_* rules,
     wpt_create, blockSpecsT_intro, wpt_frame_labels; wpt_sound ⇒ Iris TWP)
        ▼
   Iris adequacy   (Adequacy.lean: spike_step_adequacy = wp_strong_adequacy_gen,
     ghost state CONSTRUCTED by genHeap_init; launchResources under LaunchCoh
     mints the cursor and grants allocCap;  TotalAdequacy.lean:
     wpt_strongly_normalizing = twp_total)                          [Frag; trio]
        ▼
   engine drive statements   (engine_adequacyU ⇒ driveU never kills/derails,
     readout at .done;  project_triple ⇒ MemTripleU;  semantic_triple_soundU ⇒
     SemTripleU;  wpt_engine_boundU/J(_alloc) ⇒ driveU … k = .done v σ')
                                                            [Frag + labels; trio]
        ▼
   generic driver collapse   (DriverCollapse.lean: loop_step_frag, prod_loop_done,
     driver2_done, finalize_done — proved from the driver's OWN round functions;
     ProdLoop.lean: wpt_driver_done(_alloc) ⇒ DriverDoneAt;
     ProdEntry.lean: prod_run_eqJ ⇒ runND (Driver.drive …) (initial_driver_state
     sup …).1 = [(Active dres, [], dst')])               [labels; k+2 ≤ fuel; trio]
        ▼
   whole-program production statements   (exhibitA_prod,
     fib_certified_production, counter_loop_certified_production,
     list_reverse_certified_production)                          [∀ sup fs args]
        ▼
   projection to boring statements   (project_triple: any Iris triple ⇒ MemTripleU
     whose post is every pure consequence of the Iris post at the final memory;
     *_consequence discharge it; SemTripleU_iff_Mem)

   future semantic types and automation sit here: above the raw rules
   (API.lean), below generated client proofs (Examples/ReadinessSmoke.lean)
```

What the diagram does NOT contain: a bridge to `relsemcore`; a C
frontend; any statement about `.more` (fuel exhaustion).

## The logic

One line per rule family (names are the theorems; the walkthrough §3
quotes the small axioms, frame, create, one loop rule and the total
judgment verbatim). Three strata: the base Iris WP over the runtime
tuple (Rules.lean), the partial label-context judgment `wps`
(Wps.lean), the total label-context judgment `wpt` (Wpt.lean).

| Family | Rules |
|---|---|
| Small axioms | `wp_store`, `wp_load` (base WP: cell ownership entails the WP, every UB arm of `storeM`/`loadM` excluded by the precondition); `wps_store`, `wps_load`, the typed-subrange forms `wps_load_at`/`wps_store_at`/`wps_load_cell_at`/`wps_store_cell_at`; `wpt_load_at`, `wpt_store_at`, `wpt_load_cell_at`, `wpt_store_cell_at`, `wpt_store_cell` |
| Allocation | `wps_create`, `wpt_create` (cost bound `2 ≤ k`): `allocCap (req :: rest)` buys one `create`; the continuation binds an EXISTENTIAL pointer with full ownership at the unspecified image, `allocCap rest`, and the pure bounds `0 < addrOf p < 2^64`; cursor-free statements |
| Frame | `triple_frame` (base); `wps_frame`, `wps_frame_labels` with `frameLs R Ls = fun l vs ρ => Ls l vs ρ ∗ R`, `blockSpecs_frame`, the whole-loop `wps_sound_frame`; `wpt_frame`, `wpt_frame_labels` (`frameLsT`), `blockSpecsT_frame` — the frame crosses every back edge through the framed label context |
| Consequence | `triple_conseq`; `wps_wand`, `wps_fupd` (postcondition-modality absorption); `wpt_mono`, `wpt_mono_k` (budgets are upper bounds), `wpt_mono_Ls` |
| Sequencing | `triple_seq`, `wp_sseq`; `wps_seq` (wildcard), `wps_seq_spec` (`Specified` binder), `wps_seq_sym` (symbol binder), `wps_wseq`; `wpt_seq`, `wpt_seq_spec`, `wpt_seq_sym` (budgets add) |
| Conditionals, case | `wps_if_true`, `wps_if_false`, `wps_case_value`; `wpt_if_true`, `wpt_if_false` |
| Loops (label context) | `wps_save` (block entry), `wps_run` (the jump: the label's precondition `Ls l vs ρ` suffices — tracking stops), `blockSpecs_intro` (every registered body re-establishes its precondition; no Löb — the one Löb is in `wps_sound`); total: `wpt_save`, `wpt_run` with the MANDATORY decrease `1 + m ≤ k` at the variant `m`, `blockSpecsT_intro` |
| The total judgment | `wpt M Ls k Ψ e ρ` by structural recursion on the step budget `k`; `wpt_sound` collapses it into iris-lean's `TotalWeakestPre`; `diverge_total_unprovable` is the negative test |
| Operands, memop, values | `wps_load_eval`, `wps_store_eval`, `wps_memop_eval`, `wps_memop_ptreq`; `wp_ofVal`, `wps_ofVal`, `wps_pure`, `wps_annot`, `wps_annot_reindex`; the `wpt_` counterparts |
| Assertion laws | `pointsToCell_fractional`/`_agree`/`_combine`; `pointsToView_split`/`_join`/`_fractional`/`_agree`/`_persist`/`_locInBounds`; `allocMeta_persistent`, `allocMeta_dup`, `allocMeta_agree`, `locInBounds_persistent`; `cellPtr_arrayShift` (provenance-preserving shift); `allocCap_weaken` |
| Environment seam | `SymFrame`, `envAdd_lookup` (EnvLaws.lean): lookup-after-add on any reachable frame, so invariants never pin a frame shape |

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
surface, answered by a new public lemma (as `cellOwn_readout`/
`pointsToCell_readout` were).

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
`sorryAx`/`ofReduceBool`/`ofReduceNat`. Expected tail:

```
info: CerberusHeapLang/Audit.lean:164:0: CerberusHeapLang export pins: 107 trio-exact
info: CerberusHeapLang/Audit.lean:164:0: CerberusHeapLang axiom sweep: 1184 theorems bounded by the trio
info: CerberusHeapLang/Audit.lean:164:0: CerberusHeapLang banned-axiom sweep: 2030 constants of every kind checked; sorryAx/ofReduceBool/ofReduceNat absent from all cones
Build completed successfully (444 jobs).
```

**The trust base is exactly three things** ([USER 2026-09-02]): the two
capped builds with their in-build axiom sweeps, plus the banned
proof-method grep (`native_decide`/`bv_decide`/`ofReduce*`). Everything
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
| Value-scrutinee `Ecase` and wildcard `Ewseq` at the partial stratum only | total-stratum rules when a total consumer appears (no-consumer rule) | `Wpt.lean` |
| Arrays are ONE allocation, not a ∗ of per-element cells: the engine bounds-checks against the pointer's provenance allocation and `arrayShiftPtrval` preserves provenance — C's object model | forcing fact about Cerberus; per-element structure lives in the invariant + decode premises | `ArrayExhibit.lean` header |
| Metadata at a fraction as the exclusivity anchor; persistent stratum instead of a liveness token (no `kill`) | named mover: the kill arc adds the donor's `alloc_alive`/freeable split and moves the anchor | `Heap.lean` header |
| `sem_triple_prod`/`prod_run_eq` (ProdEntry.lean): the conditioned generic production face for straight-line programs, whose `hpre`/`hterm` premises are operational drive equations; no consumer in the package since P2 (the allocating exports use `wpt_driver_done_alloc` → `prod_run_eqJ`) | retirement deletes an exported face — an operator decision, left open and visible | `ProdEntry.lean` docstring |
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
| `Rules.lean` | the base logic: small axioms, sequencing, frame, consequence, the readout combinator | `wp_store`, `wp_load`, `wp_sseq`, `triple_frame`, `triple_seq`, `stateInterp_readout` |
| `Wps.lean` | the partial label-context judgment as a guarded fixpoint; its rule set incl. `wps_create`, statement-level framing, `blockSpecs_intro`; the Löb collapse into the base WP | `wps`, `wps_seq`, `wps_create`, `blockSpecs_intro`, `wps_frame_labels`, `wps_sound` |
| `Wpt.lean` | the total judgment by recursion on the budget; variant-indexed label preconditions with the mandatory back-edge decrease; the total rule set incl. `wpt_create`; collapse into Iris TotalWeakestPre | `wpt`, `wpt_run`, `wpt_create`, `blockSpecsT_intro`, `wpt_frame_labels`, `wpt_sound` |
| `Soundness.lean` | the boundary module: per-construct certification of `Step` against `step_ctx` + the driver's discharge (`dischargeStep`); the fragment cone `Frag`; the unified step-match at any context | `Frag`, `engine_complete`, `engine_step_matchU`, `Decomp.step_factor` |
| `Round.lean` | the engine-facing one-round relation and its exhaustive classification | `CerberusRound`, `cerberusRound_classify`, `step_iff_cerberusRound` |
| `Adequacy.lean` | `driveU`/`drive`/`driveJ`; Iris adequacy with the ghost state constructed; the allocation-aware launch; the semantic triples; THE PROJECTION and the pure-consequence lemmas; the public readouts | `project_triple`, `MemTripleU`, `semantic_triple_soundU`, `engine_adequacyU`, `launchResources`, `cellOwn_readout` |
| `TotalAdequacy.lean` | termination over the unified relation (`twp_total` as-is) and the generic measure→drive-fuel simulation on the size potential `pot`; allocation-aware variants | `wpt_strongly_normalizing`, `wpt_engine_boundU`, `wpt_engine_boundJ`, `wpt_engine_boundU_alloc` |
| `API.lean` | THE PUBLIC SURFACE as one import; the public/internal table | the header table |
| `Examples/Layout.lean` | example support, not logic: `intTy`, the 5/6/7 values and byte images, canned exhibit shapes | `intTy`, `sevenBytes` |
| `Examples/ReadinessSmoke.lean` | the readiness smoke test: a two-field object predicate and its rules from the API alone | `twoField`, `twoField_create` |
| `Exhibit.lean`, `LoopExhibit.lean`, `FibExhibit.lean`, `DivergeExhibit.lean`, `ArrayExhibit.lean`, `StructExhibit.lean`, `AllocExhibit.lean`, `ListRevExhibit.lean`, `TreeRotExhibit.lean`, `CaseExhibit.lean`, `WseqExhibit.lean` | the exhibits (table above) | — |
| `DriverCollapse.lean` | the production scheduler/ND/readout collapsed onto the drive loop, proved from the driver's own round functions | `loop_step_frag`, `prod_loop_done`, `driver2_done`, `finalize_done` |
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
Slice records, newest first: `docs/2026-09-02_p6-notes.md` (this
documentation), `2026-09-02_projection-notes.md`, `2026-09-02_p5-notes.md`,
`2026-09-02_p4-notes.md`, `2026-09-02_parametric-semantics-spike.md`,
`2026-09-02_repin-notes.md`, `2026-09-02_p3.5-notes.md`,
`2026-09-01_p{0,1,2,3}-notes.md`, the foundations-arc phase notes, and
the founding report `2026-08-30_spike-report.md`. Statement-surface
snapshots: `docs/*-signatures-*.txt`.

---

Built by AI agents (Claude, Anthropic) under the direction and review
of Mike Dodds.
