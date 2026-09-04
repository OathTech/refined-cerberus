# cerberus-heaplang — the architecture, normatively

What this package is, what it proves, what it trusts, and how to read
one of its theorems. Every claim is about the tree at this revision and
carries a `file:line` cite into `CerberusHeapLang/*.lean`, the pinned
semantics workspace `.cerberus-ws/lean_frontend/` (cerberus-lean
`f95ef8d9c`, `../scripts/semantics-pin.env`), or a script. The
[README](README.md) carries the exhibits table, the register of
limitations and the build recipe; the [walkthrough](docs/WALKTHROUGH.md)
quotes the definitions at length. The history of how the package got
here is not in this document: it is in the dated records under `docs/`,
indexed by `docs/2026-09-04_architecture-history-archive.md`. Rulings
are cited with their `[USER date]`/`[AGENT date]` tag and live in
`../docs/DECISIONS.md`; open items are numbered in
`../docs/KNOWN-OPEN-ITEMS.md` ("KOI").

**Glossary** (house terms, each used in exactly this sense):

- *the engine* — the cerberus-lean Lean port of Cerberus Core at the
  pin: the generated `step_ctx`, the memory operations `loadM`/`storeM`/
  `allocateObject`/`allocateRegion`/`killM`, and the shipped driver.
- *the shipped driver* — the generated driver, unmodified: the per-thread
  loop `drive_nonmemory_steps_aux2_lemFuel` (generated `Driver.lean:346`),
  the scheduler `driver2`, and the composite
  `CerbND.runND (drive fmapEmpty false file args) (initial_driver_state sup file fs).1`.
- *`Frag`* — the fragment of Core this package covers, a predicate on
  Core expressions (`Soundness.lean:4149`).
- *the mirror* — `Step`, the hand-written fuel-free small-step relation
  Iris reasons over (`Step.lean:1456`); a proof device with no semantic
  authority.
- *a round* — one iteration of the shipped per-thread loop.
- *PCALL, RETURN, PROGRAM-DONE* — the engine's own round names
  (`reduction: …` in generated `Core_reduction.lean`, `step_ctx`): a
  procedure call, a return to the caller, the value at the empty stack.
- *the collapse* — a theorem taking a judgment of the logic to a
  statement with no logic in it (into iris-lean's WP, or into a fact
  about the shipped loop).
- *a lane* — a chain of lemmas from a judgment to a fact about the
  shipped driver (a partial lane and a total lane).
- *a profile* — the fixed context and entry control an exhibit is
  stated at: `spikeCtx`/`spikeCtl` (no current procedure, the default
  file; `Step.lean:3355`, `:3331`), `procCtx rs`/`procCtl p` (a run state
  with registered labels, in procedure `p`; `:3363`, `:3336`), or the
  production profile `prodCtx`/`prodCtl` (`ProdEntry.lean:580`, `:567`).
- *seeded* — an exhibit whose initial memory holds pre-existing cells
  (premise `hcoh : Coh …`); the cold start never does, so it has no
  shipped-pipeline form.
- *a closed shipped-driver statement* (*production statement*) — a
  theorem whose execution function is the shipped composite applied to
  an authored program wrapped as a synthetic file, with a pure
  conclusion about the delivered `driver_result`: *the root of trust*.
- *the trio* — the three classical axioms `propext`, `Classical.choice`,
  `Quot.sound`; *trio-exact* means an axiom set equal to it (§3).
- *speedbump* — a claim-point check that catches honest drift, not a
  trust gate ([USER 2026-09-02], DECISIONS "SPEEDBUMPS, NOT ADVERSARIAL
  GATES").

## 1. The object

**The semantics.** The only semantics is the engine. Every exported
execution theorem is a statement about the engine's own functions: the
closed statements through the shipped composite, the generic ones
through the shipped per-thread loop at every fuel (§2.4). Nothing here
has semantic authority of its own; a disagreement between any
definition here and the engine is a defect here ([USER 2026-08-29],
CLAUDE.md "TRUST ARCHITECTURE"). The engine is trusted as a policy
decision, not proved (§3).

**The fragment.** `Frag e` (`Soundness.lean:4149`) has 23 constructors
(`:4150`–`:4314`), by kind. The value `val_pure`. Memory: `store`/
`load`/`create`/`kill`/`alloc` at evaluated operands, and the `_op`
forms of `store`/`load`/`kill`/`alloc` at operands in the covered pure
grammar `PePure`. `PePure` (`:2007`) is values, symbols, the eight
mirrored binops and array shifts. Sequencing: `sseq`, `sseq_spec`,
`sseq_sym`, `wseq`. Control: `annot`, the labels `save`/`run`, `if_`,
`case_value`, `pure_sym`. The `PtrEq` memop: `memop_vals`/`memop_op`. The
procedure call: `call`. The plain-symbol binder's head is restricted to
the bare-value producers `BareHead` (`:3981`: a literal, `create`,
`alloc`, the `PtrEq` memop, a call). Two facts a reader must know first:

- *It is annotation-free* (`Soundness.lean:4129`–`:4147`): every node is
  `Expr []`, so located Core — in particular every Core program the
  Cerberus C front end elaborates — is outside `Frag`. The reason: the
  engine's `step_ctx` reads a source location off a located redex and
  rewrites the thread's `current_loc`. This package keeps that field
  immutable in `MachineCtx.currentLoc`, so a located node would falsify
  the certification equation. The programs proved here are authored
  Core. (The mover, named there: make `current_loc` live state.)
- *It is declared as exactly what the mirror covers* ([USER 2026-09-02],
  DECISIONS "THE BOUNDARY IS FAIL-CLOSED"): a shape without a mirror
  rule is outside `Frag`. Inside `Frag` the completeness theorem (§2.2)
  dispatches over every constructor, so an engine success without a
  mirror step is an undischargeable obligation, never a silent gap.
  Concurrency, function pointers (`Eccall`), external C calls and the
  `Impl` call are outside (KOI B8; §6).

**Configurations and the mirror.** A configuration is
`Config := CoreExpr × EnvStack × Ctl × Mem` (`Step.lean:400`): the
expression, the environment stack, the thread's live control and the
engine's memory state. The two hand-written records:

- `Ctl := ⟨κ, proc, execLoc⟩` (`:371`–`:374`) — call stack, current
  procedure, execution location: the three `thread_state` fields the
  engine's PCALL and RETURN rounds write.
- `MachineCtx` (`:405`–`:413`), the immutable context; its eight fields
  are `tagDefs`, `file`, `extern`, `tid`, `parent`, `errno`,
  `currentLoc` and `runState`.

In the mirror `Step M` (`:1456`), `Step.call` (`:2047`) pushes
`(ctl.proc, ctx)`, the context computed by the syntactic search
`callRedex?` (`:703`), and `Step.ret`/`Step.ret_annot` (`:2079`, `:2096`)
pop it. Every other rule threads the control unchanged
(`Step.ctl_cases`, `:2250`). `Step` is the `primStep` of the iris-lean
`Language` instance (`Lang.lean:58`).

**The two judgments.** `wps M p Ls Θ Ψ e ρ` (`Wps.lean:301`) is the
partial judgment: a guarded fixpoint over iris-lean's WP whose
pre-functional `wps.pre` (`:217`) has four clauses. Value. Jump redex:
the label specification `Ls : LabelSpec` (`:113`) at the target's
arguments. Call redex: the procedure specification table `Θ : ProcSpec`
(`:129`) — the callee's precondition now, the caller's continuation at
every return meeting the postcondition a step later. Step.
`wpt M p Ls Θ k Ψ e ρ` (`Wpt.lean:200`) is the total judgment, by
well-founded recursion on a step budget `k`. A jump must decrease the
budget, `⌜1 + m ≤ k⌝` (`:167`). A call splits it, `1 + m + k' ≤ k`
(`:172`): the call round, the callee including its return, the
continuation. Both judgments are stated at the top invariant mask `⊤`
(21 sites in `Wps.lean`, 26 in `Wpt.lean`). The raw-WP layer of
`Rules.lean` is mask-generic — `AtomicStep` (`:194`), `wp_of_atomic`
(`:210`), `wp_store` (`:1584`), `wp_load` (`:1614`), `spike_wp_wand`
(`:1676`) — the two statement judgments are not. This is classical
sequential separation logic: no invariants, no mask-polymorphic
composition. Masks are Iris's device for sharing; their generalisation
belongs to the RefinedC arc, not to this demo ([USER 2026-09-04]: "The
demo should be the best possible version of Reynolds/O'Hearn … Fancy
logic features aren't needed for that purpose"; KOI B11).

**"Reynolds/O'Hearn over Core" means:** the assertions are the classical
points-to family over the engine's own memory state (§2.1). The rules
are the classical local rules — store, load at any fraction, budgeted
allocate, dispose, frame (CLAIMS C10). The judgments are sequential,
partial or total. A proved triple's meaning is a fact about the
engine's thread-level execution (§4, the ruled reading).

## 2. What is proved

### 2.1 The rules

The small axioms are proved once as atomic step specifications
`AtomicStep` (`Rules.lean:194`) against `Step` and the engine's real
memory operations. Objects: `store_atomic` (`:264`), `load_atomic`
(`:365`), `create_atomic` (`:991`), `kill_atomic` (`:1204`). Typed
sub-range: `loadAt_atomic`/`storeAt_atomic` (`:557`/`:648`). Dynamic
regions: `alloc_atomic`/`free_atomic` (`:1316`/`:1502`), and typed access
`regionLoadAt_atomic`/`regionStoreAt_atomic` (`:767`/`:863`). They are
lifted by `wp_of_atomic` (`:210`), `wps_of_atomic` (`Wps.lean:345`) and
`wpt_of_atomic` (`Wpt.lean:664`); every memory rule of either judgment
is a corollary (the list: API.lean, "Statement judgment"). The region
access rules hold at any type at any in-bounds offset because the
engine's check at an untyped allocation is type-blind. That check is the
dead list, the record, bounds, writability, and `isAtomicMemberAccess`
(generated `CerbMem.lean:1949`; used in `loadM`/`storeM` at
`:2003`/`:2067`), which is `false` at `alloc.ty = none`. The assertions
are the ghost-state bundles of `Heap.lean`. Cells: `pointsToCell`
(`:2749`), the sub-range view `pointsToView` (`:2714`), the whole-cell
bundle `cellOwn` (`:2734`), `readonlyCell` (`:3683`). Regions:
`regionOwn`/`regionView`/`typedRegionView` (`:3319`/`:3310`/`:3481`). Dead
tokens: `deadObj`/`deadRegion` (`:3783`/`:3793`). Allocation capacity:
the ∗-splittable `allocBudget` (`:2464`; split law `:2475`).

Structural rules, by kind. Frame across back edges and calls:
`wps_frame_labels`/`wpt_frame_labels` (`Wps.lean:701`, `Wpt.lean:563`).
Loops: `blockSpecs_intro`/`blockSpecsT_intro` (`Wps.lean:3195`,
`Wpt.lean:2975`). Procedures: `procSpecs_intro`/`procSpecsT_intro`
(`Wps.lean:3287`, `Wpt.lean:3032`) — every declared body verified once
assuming the table, Hoare's rule for recursive procedures, no Löb in the
introduction. Calls: `wps_call`/`wps_call_root` (`Wps.lean:417`/`:473`),
`wpt_call`/`wpt_call_root` (`Wpt.lean:726`/`:758`). There is no raw-WP
sequencing rule: at a populated label map it is false, because a jump
discards the sequencing context (`Rules.lean:35`–`:44`).

The collapses. `wps_sound_cps` (`Wps.lean:3440`) is the one Löb
induction, in continuation-passing form over the ambient control; its
call case runs the callee under `procSpecs` and returns into the
caller's continuation (`wp_ret`/`wp_ret_annot`, `:3326`/`:3367`).
`wps_sound`/`wps_sound_empty` (`:3637`/`:3657`) are its entry-control
faces into iris-lean's WP. `wpt_sound_cps` (`Wpt.lean:3173`, strong
induction on the budget) with `wpt_sound`/`wpt_sound_empty`
(`:3382`/`:3400`) collapse into iris-lean's total WP. Their consumers,
exactly (non-comment occurrences, every package module):

| Collapse | Consumed by (the Iris-level readouts) |
|---|---|
| `wps_sound` | `Examples/CallSmoke.lean:330`, `FibRecExhibit.lean:648`, `EvenOddExhibit.lean:501` |
| `wps_sound_empty` | Exhibit (`:349`, `:701`), StructExhibit (`:199`, `:830`), CaseExhibit (`:143`), LoopExhibit (`:391`), FibExhibit (`:402`), ArrayExhibit (`:592`), WseqExhibit (`:107`), ListRevExhibit (`:1434`), TwoLabelExhibit (`:531`) |
| `wpt_sound` | the pinned export `cs_twp_readout` (`Examples/CallSmoke.lean:455`, at `:461`) |

No shipped-driver statement consumes any of them: the driver lanes
(§2.4) run their own inductions.

### 2.2 The mirror's certification and completeness

`CerberusRound M c c'` (`Round.lean:195`) is one round in the driver's
own vocabulary. At every driver state embedding the context and the
configuration `c`: the engine's step list is a singleton, it is
advanceable, and the shipped `advance_step` on it is one active
wakeup-free transition to the state embedding `c'`. It is stated at the
loop body, with no fuel dependency (loop-level reading
`CerberusRound.loop_step`, `:965`). The certification is

```lean
theorem engine_step_matchU {M : MachineCtx}
    {e e' : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    {ρ' : EnvStack} {ctl ctl' : Ctl} {σ σ' : Mem}
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel)
    (hs : Step M (e, ev0 :: evs, ctl, σ) (e', ρ', ctl', σ')) :
    CerberusRound M (e, ev0 :: evs, ctl, σ) (e', ρ', ctl', σ') := by      -- Round.lean:1010
```

— on `Frag`, at a cons-shaped environment, at any control and successor
control, with the static size bound, and no well-formedness premise;
`step_iff_cerberusRound` (`:1598`) is two-sided under the hypothesis
that a mirror step exists.

Completeness is the other direction, per constructor.
`frag_round_complete` (`:5369`): at every non-value `Frag` configuration
the mirror steps, or the round is a classified refusal, or the
configuration is in the residual. The refusals (`ShippedRefusal`, `:214`)
are stated in the engine's vocabulary. `error`: the step list is
`[Step_error2 msg]`. `killed`: `advance_step` returns `NDkilled r`.
`fork`: `CerbND.runND` delivers at least two executions. The `panic`
family: the engine's own `failwithI`. `error_next`: a success round into
an ill-typed next round. The residual (`OpenRound`, `:357`) has two arms.
`eval_uncovered`: an operand containing a leaf the engine's evaluator
accepts where the mirror evaluator does not (a `Proc`-named unbound
symbol, a binop at two floats, `OpEq` at two ctypes). The classifier
`evalClass` answers `.uncovered` at the first such leaf and claims
nothing about the whole operand. `run_surplus`: a jump with more
arguments than parameters whose surplus does not evaluate. One lemma per
redex root carries the classification (`complete_store` … `complete_ret`,
`:2300`–`:5351`). `cerberusRound_classify` (`:5476`; premises `SeqWF`,
`ctl.κ = []`) sorts every well-sized `Frag` configuration into
`value_done`/`value_annot`/`step`/`refused`/`open_` (`RoundClass`, `:1631`).
Every operand the classifier rejects is a proved engine kill; operands
it leaves uncovered are not characterised, so the residual is a
superset of the engine-accepted shapes (KOI B7).

Two engine-round bridges exist by design (KOI B12). `engine_step_matchU`
certifies the mirror; the adequacy lanes consume the production-profile
round `loop_step_frag`/`loop_step_frag'` (`DriverCollapse.lean:2118`/
`:2024`), proved independently per redex (`Round.lean:141`–`:153`). No
adequacy export consumes `CerberusRound`, `engine_step_matchU`,
`cerberusRound_classify` or `frag_round_complete`. The hand-written
discharge `dischargeStep`/`outcomesU` (Soundness.lean) is a proof device
of Round.lean's classification — unpinned, bounded by the sweep, in no
export's statement.

### 2.3 The negative result

The total judgment is not vacuously satisfiable. `dg_loop_exhausts`
(`DivergeExhibit.lean:126`): on the self-jump body `dgBody` (`:69`) the
shipped per-thread loop exhausts at every fuel — its only value is the
kill `CerbND.fuelExhaustedKill`. Hence `diverge_total_unprovable`
(`:172`): any derivation `⊢ blockSpecsT … ∗ wpt … k Ψ (dgBody ra) …`, at
any footprint, ghost functors, label context, postcondition and budget,
entails `False`. The self-jump loop has no total derivation, and the
statement is false, not merely unprovable (CLAIMS C5).

### 2.4 Adequacy to the shipped driver, in both lanes

Both lanes are stated over the shipped per-thread loop
`drive_nonmemory_steps_aux2_lemFuel` (generated `Driver.lean:346`), from
any driver state holding the configuration at a live control. The
shipped `drive_nonmemory_steps_aux2` is its instance at
`CerbFuel.driverFuel` (`CerbND.lean:396`–`:397`, `rfl`). Both lanes
iterate the shipped round `loop_step_frag`/`loop_step_frag'`.

**The partial lane** (`Adequacy.lean`). `spike_step_adequacy` (`:568`;
`_alloc` `:667`) is iris-lean's `wp_strong_adequacy_gen` with the ghost
state constructed. `engine_adequacy` (`:1278`; `_alloc` `:1344`) turns it
into the engine fact `DriverSafeCtl M th₀ e ρ ctl σ ψ` (`:932`, read in
§4: exhaustion or PROGRAM-DONE with the readout, at EVERY fuel, no other
outcome). Its ties are `LabeledProcs` for the callees
(`DriverCollapse.lean:2178`) and `CtlTied` for the procedures already on
the control (`:2205`). The mirror suffices because `NotStuck` supplies a
mirror step at every reachable configuration and `loop_step_frag'` makes
it the loop's unique next iteration: `drive_safe_aux` (`:1079`), an
unpinned fuel induction under the control invariant `ControlOk` (`:800`).
Its premise `MachineCtx.FragProcs` (`:767`: every declared procedure body
in `Frag` with its static bound) lets it follow the engine into a callee
and back. Fuel 0 is the exhaustion kill (`loop_zero_exhausts`,
`DriverCollapse.lean:2246`); fuel 1 at a delivered value is the
exhaustion of the drain iteration (`loop_step_done_exhaust`, `:2257`);
fuel ≥ 2 there is PROGRAM-DONE (`loop_step_done`, `:392`).

**The total lane** (`ProdLoop.lean`). `wpt_driver_cps` (`:609`) is the
budget induction in continuation-passing form over the ambient control,
the driver-level twin of `wpt_sound_cps`. It concludes the pure delivery
fact `DriverDoneCtl M₀ th₀ e ρ ctl σ ψ k` (`:456`). That fact: from any
driver state holding the configuration at `ctlThread th₀ e ρ ctl`, with
the file tie and the whole-file registration tie, the loop returns
PROGRAM-DONE for a value satisfying `ψ` within `k + 2` iterations. The
call case applies the hypothesis to the callee at the pushed control
with the continuation budget added; every round is `loop_step_frag`
(`driverDoneCtl_step`, `:537`). The launcher is `wpt_driver_done_procs`
(`:799`; a populated table, the entry control `⟨[], some p, ℓ⟩` of a
declared procedure).
It is the route of `fib_rec_certified_production` (`main` calls `fib`,
which calls itself twice) and `even_odd_certified_production`
(`even`/`odd` call each other under a symbol-dependent table; three
procedures). The single-procedure lane `DriverDoneAt`/
`wpt_driver_aux`/`wpt_driver_done(_alloc)` (`:56`/`:175`/`:290`/`:358`), at
the empty table, is the route of the seven one-procedure statements.

**The projection** (`Adequacy.lean`). `project_triple_pure` (`:1605`)
takes an Iris triple to the Iris-free `MemTriple M ctl ρ e P ψ`
(`:1518`). Input: a triple whose precondition is footprint ownership and
whose framed post pure-entails `ψ R w.val σ'` under the coupling
invariant. Output: memory splits as `P ⊎ R`, and from any driver state
holding the configuration the shipped loop at every fuel exhausts or
delivers `(v, σ')` with `ψ R v σ'`. `project_triple_pure_alloc` (`:1743`)
is the allocating twin (`allocBudget B` in the precondition;
`MemTriple_alloc`, `:1669`, under `LaunchCoh … B`, `:422`). The one
Iris-shaped hypothesis `hpost` names `CohG`/`metaInterp`/`byteInterp` —
the documented exception (API.lean header). It is discharged only
through the public `*_consequence` lemmas (`:1909`–`:2007`), which
deliver the pure memory view `CellCoh` (`Heap.lean:358`), `Sat`
(`Adequacy.lean:1415`) and `DeadAt` (`:1900`). A positive exhibit names
none of the internals (§5, the boundary check).

**The closed forms over the shipped pipeline** (`ProdEntry.lean`). The
authored program is wrapped as a synthetic file — one procedure by
`prodFile` (`:125`), `main` plus declared procedures by `prodFileWith`
(`:544`; `prodFile e = prodFileWith [] e` is `rfl`, `:549`). The total
pipeline theorem `prod_run_eqJ_procs` (`:716`; one-procedure form
`prod_run_eqJ`, `:402`) turns a `DriverDoneCtl` at the production
profile into the shipped composite's result. Its bound:
`k + 2 ≤ CerbFuel.driverFuel`. The partial pipeline theorem
`prod_run_safe_procs` (`:768`) turns a `DriverSafeCtl` there into a fact
at every `fuel` about
`CerbND.runND (CerbND.drive_lemFuel fuel fmapEmpty false (prodFileWith procs e) args) (initial_driver_state …).1`.
That is exactly one execution: `nd_status.Killed dst'
CerbND.fuelExhaustedKill`, or `nd_status.Active dres` with the
postcondition. The shipped `drive` is the instance at
`fuel := CerbFuel.driverFuel` (`CerbND.lean:467`, `rfl`).

### 2.5 The nine closed shipped-driver statements

Each has the execution function
`CerbND.runND (_root_.drive fmapEmpty false F args) ((initial_driver_state sup F fs).1)`,
`F` the wrapped program, and concludes `= [(nd_status.Active dres, [], dst')]`
with a pure readout on `dres`/`dst'`. None carries a termination
hypothesis. Where the certified round count depends on an input, the
in-budget bound is an explicit premise against the name the semantics
exports for this purpose (`CerbFuel.driverFuel = 100000000`, generated
`CerbFuel.lean:71`). All nine are pinned trio-exact (§3).

| Statement | File:line | Input-dependent premises beyond the program's metadata |
|---|---|---|
| `exhibitA_prod` | `ProdExhibit.lean:264` | none |
| `fib_certified_production` | `ProdLoopExhibit.lean:75` | `hn : 0 ≤ n`, `hfuel : 2 * n.toNat + 6 ≤ CerbFuel.driverFuel` |
| `counter_loop_certified_production` | `ProdLoopExhibit.lean:620` | `hn`, `hfuel : 6 * n.toNat + 8 ≤ CerbFuel.driverFuel` |
| `list_reverse_certified_production` | `ProdLoopExhibit.lean:1435` | none |
| `dispose_list_certified_production` | `DisposeExhibit.lean:1479` | none |
| `region_loop_certified_production` | `RegionLoopExhibit.lean:633` | `hcost : 0 < regionCost al sz`, `hn`, `hB : n.toNat * regionCost al sz ≤ headroom prodMem₀.lastAddress`, `hfuel : 7 * n.toNat + 5 ≤ CerbFuel.driverFuel` |
| `malloc_list_certified_production` | `MallocListExhibit.lean:1654` | `hn`, `hB : n.toNat * (15 + max al.toNat 1) ≤ 281474976710647`, `hfuel : 25 * n.toNat + 9 ≤ CerbFuel.driverFuel` |
| `fib_rec_certified_production` | `FibRecExhibit.lean:865` | `hn`, `hfuel : fibRounds n.toNat + 4 ≤ CerbFuel.driverFuel` |
| `even_odd_certified_production` | `EvenOddExhibit.lean:721` | `hn`, `hfuel : 3 * n.toNat + 6 ≤ CerbFuel.driverFuel` |

Package definitions in these statements, exactly — beyond the authored
program and its wrapper (`prodFile`/`prodFileWith`), read off the nine
statement texts:

| Statement | In the conclusion | In a premise |
|---|---|---|
| `exhibitA_prod` | `sevenVal`, `sevenBytes`, `intTy` (`Examples/Layout.lean:57`, `:65`, `:50`); the readout `CellCoh` (`Heap.lean:358`) | — |
| `fib_certified_production` | `ivVal` (`LoopExhibit.lean:63`), `fibSpec` (`FibExhibit.lean:60`) | — |
| `counter_loop_certified_production` | `intUndefBytes` (`AllocExhibit.lean:88`), `sevenBytes`, `intTy`, `CellCoh` | — |
| `list_reverse_certified_production` | `ptrVal` (`ListRevExhibit.lean:466`), `SeedChain` (`:1210`), the footprint type `CellMap` (`Adequacy.lean:1407`), the readout `Sat` (`:1415`) | — |
| `dispose_list_certified_production` | engine fields only | — |
| `region_loop_certified_production` | engine fields only | `regionCost`, `headroom`, `prodMem₀` (`Heap.lean:2322`, `:2267`, `ProdEntry.lean:212`); at zero cost the statement would be vacuous, which `hcost` excludes |
| `malloc_list_certified_production` | engine fields only | none — the budget premise is in engine vocabulary, bridged inside the proof (`ml_budget_bridge`, `:1626`) |
| `fib_rec_certified_production` | `ivVal`, `fibSpec` | `fibRounds` (`FibRecExhibit.lean:450`: `fibRounds 0 = fibRounds 1 = 3`, `fibRounds (n+2) = fibRounds (n+1) + fibRounds n + 9`; closed form `fibRounds n + 9 = 12 · fibSpec (n+1)`, `:470`) |
| `even_odd_certified_production` | `ivVal` | — |

Beside them, two closed PARTIAL forms consume `prod_run_safe_procs`:
`fib_rec_certified` (`FibRecExhibit.lean:814`) and `even_odd_certified`
(`EvenOddExhibit.lean:673`) — every `n ≥ 0`, at every `drive_lemFuel`
fuel, no budget bound.

### 2.6 The memory invariant

`MemWF σ` (`Heap.lean:1583`) is the global memory well-formedness
invariant: ten fields, each an engine fact with a `CerbMem.lean` cite.
Allocation-id discipline: `live_lt`, `dead_lt`, `live_dead`. Pairwise
range disjointness of all live allocations: `disj`. Cursor and size
bounds: `cursor_lo`, `size_nonneg`, `la_wf`, `la_pos : 0 < lastAddress`
(`la_pos` [AGENT 2026-09-03], DECISIONS "KILL/FREE K3 LANDED"). The
dynamic-address facts: `dyn_lo`, `dyn_disj`. It is a field of the state
interpretation `CohG` (`:2632`, under cursor presence) and of the launch
premise `LaunchCoh` (`Adequacy.lean:422`). `prodMem₀_memWF`
(`ProdEntry.lean:243`) is the cold-start instance; `create_fresh_global`
(`Heap.lean:1801`) is "fresh means fresh in the concrete allocation
model". Every memory operation of the fragment has its preservation
theorem: `MemWF.loadM` (`:1817`), `MemWF.storeM` (either locking mode,
`:1877`), `MemWF.allocateObject` (any initializer, `:1898`),
`MemWF.allocateRegion` (`:1937`), `MemWF.killM` (both arms, `:2010`).

## 3. What is trusted

**The trust base.** (i) The Lean kernel and the trio (`Audit.lean:159`–
`:160`). (ii) iris-lean, as DEFINITIONS: the WP, the BI connectives and
the ghost theory appear only inside kernel-checked proof terms and
contribute no axiom; the closed statements' texts are Iris-free. (iii)
The pinned cerberus-lean semantics (`f95ef8d9c`) as the semantics of
Core: a policy decision, sampled by differential validation against the
OCaml oracle, not proved (README "What you are asked to take on faith").
The pinned tree declares no `axiom` and contains no `sorry`:
`grep -rn '(sorry'` over the primed `generated/*.lean` is empty and the
build log has no `declaration uses sorry` (README "The trust story";
`docs/2026-09-03_repin-fuel-notes.md`).

**What the build checks** (`Audit.lean`, the last import of the library
root, elaborated by every `lake build`). Every pinned export exists, is
a theorem, and has axiom set EXACTLY the trio (`:615`–`:616`; 402 pins at
this revision, `docs/2026-09-04_h1-notes.md` §8). Every theorem of every
`CerberusHeapLang.*` module, internal details included, is bounded by
the trio (`:617`–`:636`). `sorryAx`/`ofReduceBool`/`ofReduceNat` reach no
constant of any kind (`:637`–`:653`). Precision: "exactly the trio" is
the pinned exports' property. A few public-named lemmas have SUB-trio
cones and are deliberately unpinned, bounded by the sweep:
`fibRounds_closed` (`[propext, Quot.sound]`); `regionCost_pos`,
`freshBase_*`, `runND_killed` (no axioms; `:354`–`:356`, `:380`–`:384`,
`:523`–`:525`, `:552`–`:553`). Kernel-only proof methods:
no `native_decide`, `bv_decide` or `ofReduce*` anywhere (gate 1,
`../scripts/test_unit.sh:28`).

**The declared boundary is empty** ("There is no declared boundary
axiom", `Audit.lean:45`). What is NOT trusted: the mirror `Step`, the
judgments, the discharge devices, the collapse lemmas. They are proof
devices, none of which appears in the statement of any pinned export
([USER 2026-09-02], CLAUDE.md "The referent of every export is the
genuine semantics"). No hand-written driver loop, scheduler or discharge
function occurs in any export's statement. The closed statements name
the shipped composite; the generic statements name
`drive_nonmemory_steps_aux2_lemFuel`, `runOne`, `driver_state` and the
engine's result types. No export carries an interim label.

## 4. How to read an export

**A production statement** — `fib_certified_production`
(`ProdLoopExhibit.lean:75`), verbatim:

```lean
theorem fib_certified_production (sup : Nat) (ra : core_run_annotation) (n : Int)
    (sbty ibty abty bbty : core_base_type) (hn : 0 ≤ n)
    (hfuel : 2 * n.toNat + 6 ≤ CerbFuel.driverFuel)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND
          (_root_.drive fmapEmpty false
            (prodFile (fibProg ra n sbty ibty abty bbty)) args)
          ((initial_driver_state sup
            (prodFile (fibProg ra n sbty ibty abty bbty)) fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = ivVal (fibSpec n.toNat) ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
```

For every symbol supply `sup`, file-system state `fs`, command line
`args` and choice of the program's metadata (`ra`, the base types),
running the shipped Cerberus driver on the file whose `main` is the
iterative-fib program at input `n ≥ 0` yields exactly one execution. It
delivers the value `fib n`, not blocked, with empty stdout and stderr.
The one premise beyond `n ≥ 0` is `hfuel`: the certified round count
`2n + 6` fits the shipped driver's fixed loop budget
`CerbFuel.driverFuel = 10^8`. No hypothesis about termination, memory
well-formedness or the driver's internals appears: the cold-start
memory `prodMem₀` satisfies the global invariant by theorem
(`prodMem₀_memWF`, `ProdEntry.lean:243`). In `drive fmapEmpty false`,
`false` is the shipped driver's own sequential mode: the generated
`drive` fails with "CONCURRENCY IS BROKEN" at `true` (`Driver.lean:530`).
`fmapEmpty` is the wrapped file's tag-definition table, empty — the
`htd` narrowing of KOI B4 (below).

**A thread-level statement** — `counter_loop_certified`
(`LoopExhibit.lean:427`), a seeded exhibit, verbatim (`loc ann ra mo bty
xbty` are section variables, leading binders in the machine-printed
signature):

```lean
theorem counter_loop_certified
    (sbty : core_base_type) (idx addr : Int) (bs0 : List CerbMem.AbsByte)
    (n : Int) (hn : 0 ≤ n)
    (σ₀ : Mem)
    (hcoh : Coh fmapEmpty σ₀ ((Iris.Std.PartialMap.singleton idx
      (SpikeCell.mk addr intTy bs0)) : SpikeHeapF SpikeCell)) :
    let prog := loopProg loc ann ra mo bty xbty sbty (cellPtr idx addr) n
    let rs := loopRS loc ann ra mo bty xbty (cellPtr idx addr)
    DriverSafeCtl (procCtx rs) (procThread loopProcSym prog [fmapEmpty]) prog [fmapEmpty]
      (procCtl loopProcSym) σ₀ (fun v σ' =>
        v = Vunit ∧ ∃ bs',
          ((n = 0 ∧ bs' = bs0) ∨ (0 < n ∧ bs' = (sevenBytes fmapEmpty))) ∧
          CellCoh fmapEmpty σ' idx ⟨addr, intTy, bs'⟩) := by
```

Read through `DriverSafeCtl` (`Adequacy.lean:932`). Take any driver
state `dst`, accumulator `acc` and fuel `fl`. Let `dst`'s single thread
hold the program at the entry control of procedure `loopProcSym` over
`σ₀`, with empty extern, the context's file and the registration ties.
Then
`runOne (drive_nonmemory_steps_aux2_lemFuel fl fmapEmpty acc [0]) dst` is
either the exhaustion kill or PROGRAM-DONE with a value and a final
memory satisfying the readout. The readout: `Vunit`, and the cell at
`addr` holding its original bytes (`n = 0`) or the image of `7`
(`n > 0`). The premise `hcoh` says `σ₀` holds one live writable `int`
cell at `(idx, addr)` with bytes `bs0` (`Coh`, `Heap.lean:386`; `CellCoh`,
`:358`): the seeded footprint, which is why the statement is about the
per-thread loop and not the composite. The thread-level fact is the
meaning of the triple (below), and its ∀ `fl` is real run-length content.

**The premises every generic adequacy theorem carries** (`engine_adequacy`,
`Adequacy.lean:1278`–`:1296`; `project_triple_pure`, `:1605`–`:1613`;
`wpt_driver_cps`, `ProdLoop.lean:609`–`:620`; `wpt_driver_done_procs`,
`:799`–`:809`), and what each means:

- `htd : M.tagDefs = fmapEmpty`, `hex : M.extern = fmapEmpty` — no
  struct/union tag definitions and no extern indirection in any proved
  configuration; this matches the production driver's
  `drive fmapEmpty false …` (KOI B4).
- `hκ : ctl.κ = []` — the entry control has an empty call stack (the
  value arm selects PROGRAM-DONE over RETURN, `Round.lean:1661`).
- `hfrag : Frag e`, `hQf`, `hPf : M.FragProcs` — the program, every
  registered label body and every declared procedure body are in the
  fragment (`Adequacy.lean:767`).
- `hpot : pot e ≤ lemDefaultFuel`, `hQpot`, `FragProcs.potBound` — THE
  STATIC FUEL PREMISE. `pot` (`Potential.lean:43`) is a step-monotone
  size potential on terms. The engine's pure-expression evaluator and
  context search are fuelled at LemLib's constant
  `lemDefaultFuel = 1000000` (`.lake/packages/LemLib/lean-lib/LemLib.lean:56`).
  These premises keep every reachable term's size under it independently
  of the run length. Together with the loop budget
  `CerbFuel.driverFuel = 10^8` this is KOI A1: two constants baked into
  the port. They are ruled a defect of the cerberus-lean semantics, and
  the fix — fuel as a quantifiable parameter — is asked of the
  cerberus-lean team ([USER 2026-09-03], DECISIONS "FUEL IS A DEFECT IN
  THE CERBERUS-LEAN SEMANTICS"). When it lands, the consumer restatement
  makes these premises and the production `hfuel`s fuel-parametric
  (`../docs/2026-09-04_review-of-fuel-parameter-design.md` §5).
- `hcl : th₀.current_loc = M.currentLoc` — the thread's location field
  equals the context's (the annotation-free fragment never rewrites it,
  §1).
- `hcoh`/`hl : LaunchCoh …` — the seeded footprint, or, for allocating
  programs, the footprint plus the global memory well-formedness
  invariant `MemWF` (§2.6) and the budget fit `B ≤ headroom σ.lastAddress`
  (`Adequacy.lean:422`–`:432`).
- `hwp` — the Iris derivation: the footprint's ownership entails the WP
  (or `procSpecsT ∗ blockSpecsT ∗ wpt …`) at the top mask.

**The ruled reading** ([USER 2026-09-03], DECISIONS "FUEL IS A DEFECT…",
where the Reynolds/O'Hearn reading is fixed). The triple's semantics is
the THREAD-level statement — `DriverSafeCtl`, the single-thread loop at
every fuel. The shipped driver has two fuelled loops, the outer scheduler
`driver2` and the inner single-thread loop. [USER 2026-09-03], verbatim
from the register (`../docs/DECISIONS.md:1753`–`:1756`, in the entry
"F1 RANGE AUDIT"; the later entry "FUEL IS A DEFECT…" re-quotes it with
an ellipsis at `:1823`):

> "the outer loop is the 'scheduler' loop and the inner loop is the
> 'single threaded' loop. And for our logic, which (for now) is
> sequential, the scheduler is degenerate, we never see schedule
> changes."

Consequences. The `fuel` of the closed partial forms
(`prod_run_safe_procs`, `fib_rec_certified`, `even_odd_certified`) is
threaded to `driver2` only. The reason: `new_drive_core_threads` calls
the per-thread loop through its fixed-budget wrapper (generated
`Driver.lean:355`–`:358`). That quantifier is therefore true but does no
run-length work (KOI A2); the run-length content is the ∀ `fl` of
`DriverSafeCtl`. The closed forms' singleton EQUATION
`runND … = [(st, [], dst')]` is the sequential strengthening of the
intended "for every outcome in the run's outcome list" meaning, the form
that survives concurrency (KOI B5). The scheduler becomes live only
under concurrency or external C calls, both outside `Frag`.

## 5. The instruments, and what green establishes

The trust base is gates 1–2 of `../scripts/test_unit.sh` (`:28`, `:39`):
the banned-methods grep and the capped build that elaborates
`Audit.lean` (§3). Everything else is a speedbump ([USER 2026-09-02]).
Three run in the full gate; one instrument is on demand.

- **The rule-use and classification manifest**
  (`scripts/capability_manifest.lean` → `docs/CAPABILITY_MANIFEST.md`,
  regenerated and diffed at `test_unit.sh:47`). Its rows are the
  engine-SUCCESS variants of every `Frag` constructor, a hand-maintained
  table read off `Frag`, `Step` and the engine's memory-operation arms.
  Each row is classified RULE, RULE-TOTAL-UNDEMONSTRATED, PARTIAL-ONLY,
  NO-RULE or OUT-OF-SCOPE. At this revision (the manifest's tail line):
  23 constructors, 50 rows — 30 RULE, 0 RULE-TOTAL-UNDEMONSTRATED, 0
  PARTIAL-ONLY, 15 NO-RULE, 5 OUT-OF-SCOPE, 0 red, 18 consumer modules.
  What green establishes is stated exactly by the generated, gate-diffed
  header (`docs/CAPABILITY_MANIFEST.md:8`–`:26`, "WHAT GREEN ESTABLISHES,
  EXACTLY"). In short: the table covers every `Frag` constructor and
  names no stale one; every named theorem exists; every RULE/PARTIAL-ONLY
  rule is in a listed consumer's proof-term cone; the classification is
  complete and exact; every claim-matrix name exists. Not established:
  exhaustiveness of the table over the engine's success shapes (a
  reviewed reading); a NO-RULE or OUT-OF-SCOPE row is a stated absence,
  not coverage.
- **One module classification** (`scripts/module_classes.tsv`, pure data,
  reprinted at the head of the manifest; ten classes, the vocabulary in
  its header, `engine-mirror-test` reserved with no member). The
  manifest's consumer set is `positive-client` ∪ `declared-smoke` (18
  modules: the sixteen program exhibits, `Examples.CallSmoke`,
  `Examples.ReadinessSmoke`). The production wrappers and the negative
  test are not consumers. Fail-hard behaviour (TSV header lines 8–11):
  the two Lean instruments fail on a package module absent from the
  list; all three instruments fail on a classified module absent from
  the build or a class outside the vocabulary.
- **The import-direction check** (`test_unit.sh:65`): no module of class
  `core` imports an exhibit, example or production module.
- **The client-boundary check** (`../scripts/boundary_check.sh`,
  `test_unit.sh:88`). After stripping comments, a `positive-client`/
  `declared-smoke`/`example-support` module must not mention a logic
  internal. The internals: the coupling invariant and state
  interpretation (`CohG`, …); the judgment unfoldings (`wps.pre`, …);
  the mirror transition (`Step.<name>`); the engine's transition and
  driver definitions (`step_ctx`, `driver2`, …). The full pattern is
  `boundary_check.sh:46`. Text-based: it catches honest drift.
  Per-module allowances live in the TSV with their reason; there are
  ZERO at this revision (`BOUNDARY: 19 modules checked, 0 internals
  mention(s) in total, exit=0`, `docs/2026-09-04_h1-notes.md` §8). A
  malformed TSV row is red.
- **The claim matrix** (`docs/CLAIMS.md`, hand-written prose stated as
  such in its header). Per headline claim: exported theorems, kind,
  demonstrating exhibits, supported variants (manifest rows), known
  exclusions (KOI pointers), freshness check. The generator checks that
  every declaration a claim row names exists (11 rows, 90 names).
- **The parametric inventory** (`scripts/parametric_inventory.lean`) is
  ON DEMAND, not in the gate — [AGENT 2026-09-04] (DECISIONS AR5-manifest
  entry): the boundary check is its cheap gate twin, and a proof-term
  measurement without a verdict is not a check. Its configuration is
  fail-closed: a missing export seed or an unclassified module aborts
  the run (`parametric_inventory.lean:1`–`:16`).

## 6. What is not covered, and not claimed

Each item points at its register entry; none is hidden in a proof.

- **The fragment boundary.** Located (C-elaborated) Core, concurrency,
  function pointers (`Eccall`), external C calls, the `Impl` call —
  outside `Frag` (§1; KOI B8; CLAIMS "Not claimed").
  Five OUT-OF-SCOPE variants lie inside the fragment's constructors but
  outside the mirror (manifest OUT-OF-SCOPE rows): a jump with a
  non-evaluating surplus argument; `pure(x)` at a `Proc`-named unbound
  symbol; an annotated value at the plain-symbol binder. The other two:
  `PtrEq` at two concrete pointers of differing provenance (the engine
  forks); the `Impl` call.
- **The fifteen NO-RULE variants** — admitted by the fragment and the
  engine, covered by no rule, so a program exercising them is outside
  the logic (manifest NO-RULE rows; KOI B14, A3). By constructor:

  | Constructor | NO-RULE variants |
  |---|---|
  | `store` (3) | the locking store `Store0 true`; a store through a union-member pointer; a whole-object store at an atomic-typed allocation |
  | `load` (3) | a load at a read-only object (the atomic specification `load_atomic_readonly` exists, no statement-level rule); a load through a union-member pointer; a whole-object load at an atomic-typed allocation |
  | `create` (3) | a zero-size type; an atomic type; a type whose unspecified image is not decode-inert |
  | `kill` (4) | the static kill of a live region; `free(NULL)`; `free` of a created object whose base sits in `dynamicAddrs` (the upstream `dynamic_addrs` collision, KOI A3); a kill of either kind through a union-member pointer |
  | `alloc` (1) | the zero-cost `alloc` (`n ≤ 0 ∧ al ≤ 1`) |
  | `memop_vals` (1) | `PtrEq` at an `SD_Id`-named function pointer against a concrete pointer (the one arm reading `funptrmap`) |

- **Masks.** Both judgments are fixed at `⊤`; the generalisation is a
  RefinedC-arc item ([USER 2026-09-04]; §1; KOI B11).
- **The fuel constants** `lemDefaultFuel`/`CerbFuel.driverFuel` (§4; KOI
  A1, a ruled semantics defect, fix pending upstream); the outer-fuel
  quantifier (KOI A2); the singleton equation (KOI B5).
- **Empty tag definitions and extern** in every proved configuration
  (§4; KOI B4).
- **The mirror-completeness residual.** `OpenRound`'s two arms are
  characterised, not closed (§2.2; movers at `Round.lean:357`–`:400` and
  in `EvalClass.lean`'s header). `Frag.case_value` carries `hbsz`, not a
  theorem but a membership premise: the selected branch's `esize` is
  bounded by the case node's (`Soundness.lean:4296`). The client
  discharges it per program — `rfl` for authored programs
  (`caseProg_select`, `CaseExhibit.lean:68`) (KOI B7).
- **Statement-shape limitations.** Seeded exhibits have no cold-start
  form (KOI B3). The straight-line exhibits sit at the no-procedure
  profile `spikeCtx`/`spikeCtl`, a thread state the shipped driver never
  parks `main` in (it parks it at `current_proc_opt := some main_sym`,
  generated `Driver.lean:530`). This is admitted because the round needs
  the current procedure only at a jump (`loop_step_frag'`'s `hjmp`,
  `DriverCollapse.lean:2035`; `CtlTied.noproc`, `:2213`) (KOI B2). Six
  any-memory total equations have no twins, and tree rotation has no
  shipped-pipeline statement (KOI B1). `fib_rec_certified_production`'s
  bound has one unit of slack; nothing claims tightness (KOI B6).
- **Two engine-round bridges** by design (§2.2; KOI B12).
- **Deferred parametric semantics interfaces**: the rules are proved
  directly against `Step` and the memory state ([USER 2026-09-02]
  deferral, KOI B9; `docs/2026-09-02_parametric-semantics-spike.md`).
- **The instruments' limits**: the variant table is a reviewed reading
  (§5); the boundary check is text-based, its comment stripper is not
  string-literal-aware (KOI C11) and its allowances are per-module (KOI
  C12); the claim matrix is prose, as its own header states (CLAIMS.md).

## 7. The acceptance-goals ledger

The three acceptance goals ([USER 2026-09-02], DECISIONS "THE DEMO'S
ACCEPTANCE GOALS", verbatim: "a generic logic with adequacy over the
shipped driver, a complete logic for the fragment, a globally
well-formed allocator model"), with their status at this revision:

- **Goal 1 — generic adequacy over the shipped driver: CLOSED**, by
  `project_triple_pure`/`MemTriple` and `prod_run_safe_procs` (§2.4);
  the exclusions are §6's (seeded exhibits, the outer-fuel quantifier).
  Record: `docs/2026-09-03_f1-notes.md`.
- **Goal 2 — mirror completeness for the fragment: CLOSED fail-closed on
  the declared fragment**, by `frag_round_complete`/`cerberusRound_classify`
  (§2.2); the residuals and the carried `hbsz` are §6's item (KOI B7).
  Record: `docs/2026-09-02_fragment-closure-notes.md`.
- **Goal 3 — a global memory well-formedness invariant: CLOSED**, by
  `MemWF`, its cold-start instance and its preservation theorems for
  every memory operation of the fragment (§2.6). Record:
  `docs/2026-09-03_kill-free-arc-record.md`.

Not a goal of the demo ([USER 2026-09-02], same ruling): covering all of
Core. What remains open is §6's list, each item with its KOI number. The
records of the arcs that closed the goals are indexed in
`docs/2026-09-04_architecture-history-archive.md`.
