# cerberus-heaplang — the architecture, normatively

What this package is, what it proves, what it trusts, and how to read
one of its theorems. Every claim is about the tree at this revision and
carries a `file:line` cite into `CerberusHeapLang/*.lean`, the pinned
semantics workspace `../.cerberus-ws/lean_frontend/` (cerberus-lean
`f95ef8d9c`, `../scripts/semantics-pin.env`), or a script. The
[README](README.md) carries the exhibits table and the build recipe, and
gives each limitation its discharge or mover; §6 here lists the
limitations with their register numbers (the two overlap by design).
The [walkthrough](docs/WALKTHROUGH.md) quotes the definitions at
length. The history of how the package got here is not in this
document: it is in the dated records under `docs/`, indexed by
`docs/2026-09-04_architecture-history-archive.md`. Rulings
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
  Core expressions (`Soundness.lean:8069`).
- *the mirror* — `Step`, the hand-written fuel-free small-step relation
  Iris reasons over (`Step.lean:3841`); a proof device with no semantic
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
  file; `Step.lean:5464`, `:5440`), `procCtx rs`/`procCtl p` (a run state
  with registered labels, in procedure `p`; `:5472`, `:5445`), or the
  production profile `prodCtx`/`prodCtl` (`ProdEntry.lean:583`, `:568`).
- *seeded* — an exhibit whose initial memory holds pre-existing cells
  (premise `hcoh : Coh …`); the cold start never does, so it has no
  shipped-pipeline form.
- *a closed shipped-driver statement* (*production statement*) — a
  theorem whose execution function is the shipped composite applied to
  an authored program wrapped as a synthetic file, with a pure
  conclusion about the delivered `driver_result`: *the root of trust*.
- *the trio* — the three classical axioms `propext`, `Classical.choice`,
  `Quot.sound`; *trio-exact* means an axiom set equal to it (§3).
- *pinned* / *unpinned* — a theorem is pinned when `Audit.lean` lists it
  in `trioExports` and the build asserts its axiom set is exactly the
  trio; every other theorem is unpinned (§3).
- *the sweep* — `Audit.lean`'s check that every theorem of every package
  module has an axiom set within the trio (§3).
- *a tie* — a hypothesis of `DriverSafeCtl`/`DriverDoneCtl` fixing a
  field of the driver state from the configuration (`Adequacy.lean:948`–
  `:953`; `ProdLoop.lean:484`–`:488`). The ties: the thread, the memory,
  the extern table, the file, the registration predicate `LabeledProcs`
  and, in the partial fact only, the control's `CtlTied`; the thread tie
  carries the live source location since E1 (`ctlThread`), and the
  run-state supplies are tied to the control inside `MachineCtx.Embeds`
  (Round.lean; E5's t4/t5/t6 production theorems carry `600 ≤ sup`).
- *a readout* — the pure conclusion about a delivered result, `ψ v σ'` on
  the value and the final memory; by extension an exhibit lemma that
  reads it off an Iris conclusion (`*_readout`).
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

**The fragment.** `Frag e` (`Soundness.lean:9368`) has 29 constructors
(`:8070`–`:8286`; dialect arc E4), by kind. The value `val_pure`. Memory:
`store`/`load`/`create`/`kill`/`alloc` at evaluated operands, and the
`_op` forms of `store`/`load`/`kill`/`alloc`/`create` (the last E1) at
operands in the covered pure grammar `PePure`. `PePure` (`:3254`) is
values, symbols, the eight mirrored binops, array shifts, the constructor
constants `Ivalignof`/`Ivsizeof`/`Unspecified` at a literal ctype (E1/E2)
and — E2 — the mirrored constructors `Specified(e)`/tuples at covered
operands, `case` at a covered scrutinee and covered branch bodies, `not`,
the pure `if`, `undef(UB)`. Sequencing: `sseq`, `sseq_spec`, `sseq_sym`,
`sseq_tuple`, `wseq`, `wseq_sym`, `wseq_tuple` — the plain-symbol and
flat-tuple binders at ANY fragment head (E1/E2). Control: `annot`,
`bound` (E1), the labels `save`/`run`, `if_`, `case_value`, `pure_op`
(the pure round at any covered non-value operand, E2). The `PtrEq`
memop: `memop_vals`/`memop_op`. The procedure call: `call`. The
unsequenced node: `unseq` (E4). Two facts a reader must know first:

- *It is annotated, and the source location is live state* (E1;
  `Soundness.lean:7987`–`:8068`, the `Frag` header): every node carries
  its static annotation list. The engine's `step_ctx` reads a source
  location off a located redex and rewrites the thread's `current_loc`;
  that field is the control's `curLoc` (`Ctl`, Step.lean), written by
  every general-arm round (`ctl.upd a`). Located Core — the Cerberus C
  front end's output — is inside the fragment's reach as far as its
  constructs are admitted (E1: annotations, `bound`, `Ivalignof`; E2: the
  loaded-value currency, the tuple/weak binders; E3: the C `int`
  arithmetic `__conv_int__`/`catch_exceptional_condition_<op>`/`wrapI_<op>`
  through the engine's generated `mk_*` functions, `Ivmin`/`Ivmax`, ctype
  equality, `/\\`/`\\/`, `is_unsigned` at a leaf, and the standard-library
  `PEcall` unfolded through the FILE OBJECT — `evalPexpr` reads `M.file`'s
  `stdlib` exactly as `call_function` does, under a static per-callee
  inlining budget `stdBudget` keyed by the callee's printed name; `PePure`
  gains `convInt`/`wrapI`/`catchExc`/`isUnsigned`/`call`; E4: `unseq` —
  the sequential driver's last-reducible-component order under the
  `Cunseq` frame and the completion into the annotated tuple, with
  ccall-free components — and the annotated-tuple weak binder); t1's
  `main` transcribed VERBATIM is in `Frag` (`CorpusE0.t1Main_frag`, the
  kernel-decided walk `CorpusE0.t1_uncovered_none`, `Examples/CorpusE0.lean`)
  and certified end to end (`t1_certified_production`, CorpusT1Exhibit.lean;
  E4, `docs/2026-09-05_e4-notes.md`). E5, slice 1: the NEGATIVE-ACTION
  round `neg(store …)` under a `bound` (`Step.neg_bound` — the engine's
  exclusion-id and fresh-symbol draws are WRITERS on the control's
  `Ctl.sup`, tied to the driver's run state at every round), the excluded
  store `Eexcluded n (store …)` (`Step.excluded_store`/`_eval`), `case` at a
  non-value scrutinee, and `nd` (classified as the scheduler FORK, no
  rule) are mirrored and classified. E5's next checkpoint proves the
  negative-assignment and excluded-store rules at both strata, and uses
  their total faces to certify t5_ifelse at budget 88, returning
  Specified(1) through the shipped driver (`CorpusT5Exhibit`). Its premise
  `600 ≤ sup` is a sufficient floor, not a necessary one (the composite
  delivers the same result at `sup = 0`, measured at the L1 landing,
  `docs/2026-09-07_l1-landing-notes.md`). The same protocol now
  certifies t6_switch at budget 78, returning Specified(20), through
  its five engine-registered label continuations (`CorpusT6Exhibit`).
  t4_while is now certified at budget 915, returning Specified(10),
  through a decreasing while-label invariant and the emitted exit/return
  path (`CorpusT4Exhibit`; `docs/2026-09-06_e5-t4-loop.md`). All three
  carry the sufficient floor `600 ≤ sup` and the library fragment described
  in §2.5. E5 landed as L1 of `docs/2026-09-07_landing-charter.md` (record
  `docs/2026-09-07_l1-landing-notes.md`); its full range audit
  (8eeaf92..the L1 head) is owed at the L1 merge boundary. The `bound` rules
  `wps_bound`/`wpt_bound` now REQUIRE a negative-free body within the fuel
  (`negFree`, `pot`), the congruence being unsound otherwise
  (`docs/2026-09-05_e5-notes.md` §3).
- *It is declared as exactly what the mirror covers* ([USER 2026-09-02],
  DECISIONS "THE BOUNDARY IS FAIL-CLOSED"): a shape without a mirror
  rule is outside `Frag`. Inside `Frag` the completeness theorem (§2.2)
  dispatches over every constructor, so an engine success without a
  mirror step is an undischargeable obligation, never a silent gap.
  Concurrency, function pointers (`Eccall`), external C calls and the
  `Impl` call are outside (KOI B8; §6).

**Configurations and the mirror.** A configuration is
`Config := CoreExpr × EnvStack × Ctl × Mem` (`Step.lean:923`): the
expression, the environment stack, the thread's live control and the
engine's memory state. The two hand-written records:

- `Ctl := ⟨κ, proc, execLoc, curLoc, sup⟩` (`Step.lean:700`–`:728`) —
  call stack, current procedure, execution location (the three
  `thread_state` fields the engine's PCALL and RETURN rounds write),
  the current source location (E1: written by every general-arm round)
  and the run state's two supplies `RunSup` (`:672`; E5's negative
  actions draw from both).
- `MachineCtx` (`:820`–`:830`), the immutable context; its seven fields
  are `tagDefs`, `file`, `extern`, `tid`, `parent`, `errno` and
  `runState` (the mirror reads its labels; the judgments also read
  `runState.sym_supply` as the lower bound on fresh symbols. The live
  supplies are `Ctl.sup`). Seeded `procCtx` normalizes both supplies to
  zero; production contexts retain the explicit initial supply. This
  seeded-profile normalisation is ACCEPTED as an inert limitation ([USER
  2026-09-07], the landing charter's R3; KNOWN-OPEN-ITEMS B18 — lift when a
  seeded exhibit needs a non-zero supply).

In the mirror `Step M` (`:3841`), `Step.call` (`:4443`) pushes
`(ctl.proc, ctx)`, the context computed by the syntactic search
`callRedex?` (`:1418`), and `Step.ret`/`Step.ret_annot` (`:4462`, `:4474`)
pop it. Every other rule threads `κ`/`proc`/`execLoc` unchanged and
writes the location, `ctl.upd a` (`Step.ctl_cases`, `:3769`). `Step` is
the `primStep` of the iris-lean
`Language` instance (`Lang.lean:58`).

**The two judgments.** `wps M p Ls Θ Ψ e ρ` (`Wps.lean:316`) is the
partial judgment: a guarded fixpoint over iris-lean's WP whose
pre-functional `wps.pre` (`:228`) has four clauses. Value. Jump redex:
the label specification `Ls : LabelSpec` (`:113`) at the target's
arguments. Call redex: the procedure specification table `Θ : ProcSpec`
(`:129`) — the callee's precondition now, the caller's continuation at
every return meeting the postcondition a step later. Step.
`wpt M p Ls Θ k Ψ e ρ` (`Wpt.lean:202`) is the total judgment, by
well-founded recursion on a step budget `k`. A jump must decrease the
budget, `⌜1 + m ≤ k⌝` (`:167`). A call splits it, `1 + m + k' ≤ k`
(`:172`): the call round, the callee including its return, the
continuation. Both judgments are stated at the top invariant mask `⊤`
(19 code sites in `Wps.lean`, 26 in `Wpt.lean`, docstring mentions
excluded; DERIVED by grep). The raw-WP layer of
`Rules.lean` is mask-generic — `AtomicStep` (`:220`), `wp_of_atomic`
(`:236`), `wp_store` (`:1719`), `wp_load` (`:1750`), `spike_wp_wand`
(`:1812`) — the two statement judgments are not. This is classical
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
`AtomicStep` (`Rules.lean:220`) against `Step` and the engine's real
memory operations. Objects: `store_atomic` (`:293`), `load_atomic`
(`:500`), `create_atomic` (`:1126`), `kill_atomic` (`:1339`). Typed
sub-range: `loadAt_atomic`/`storeAt_atomic` (`:692`/`:783`). Dynamic
regions: `alloc_atomic`/`free_atomic` (`:1451`/`:1637`), and typed access
`regionLoadAt_atomic`/`regionStoreAt_atomic` (`:902`/`:998`). They are
lifted by `wp_of_atomic` (`:236`), `wps_of_atomic` (`Wps.lean:377`) and
`wpt_of_atomic` (`Wpt.lean:679`); every memory rule of either judgment
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
`wps_frame_labels`/`wpt_frame_labels` (`Wps.lean:728`, `Wpt.lean:567`).
Loops: `blockSpecs_intro`/`blockSpecsT_intro` (`Wps.lean:4315`,
`Wpt.lean:4113`). Procedures: `procSpecs_intro`/`procSpecsT_intro`
(`Wps.lean:4407`, `Wpt.lean:4170`) — every declared body verified once
assuming the table, Hoare's rule for recursive procedures, no Löb in the
introduction. Calls: `wps_call`/`wps_call_root` (`Wps.lean:450`/`:500`),
`wpt_call`/`wpt_call_root` (`Wpt.lean:742`/`:771`). There is no raw-WP
sequencing rule: at a populated label map it is false, because a jump
discards the sequencing context (`Rules.lean:35`–`:44`).

The collapses. `wps_sound_cps` (`Wps.lean:4562`) is the one Löb
induction, in continuation-passing form over the ambient control; its
call case runs the callee under `procSpecs` and returns into the
caller's continuation (`wp_ret`/`wp_ret_annot`, `:4409`/`:4451`).
`wps_sound`/`wps_sound_empty` (`:4755`/`:4777`) are its entry-control
faces into iris-lean's WP. `wpt_sound_cps` (`Wpt.lean:4308`, strong
induction on the budget) with `wpt_sound`/`wpt_sound_empty`
(`:4516`/`:4536`) collapse into iris-lean's total WP. Their consumers,
exactly (non-comment occurrences in every package module outside the
defining module and `Audit.lean`'s pin list):

| Collapse | Consumed by (the Iris-level readouts) |
|---|---|
| `wps_sound` | `Examples/CallSmoke.lean:329`, `FibRecExhibit.lean:642`, `EvenOddExhibit.lean:496` |
| `wps_sound_empty` | Exhibit (`:349`, `:701`), StructExhibit (`:199`, `:830`), CaseExhibit (`:143`), LoopExhibit (`:393`), FibExhibit (`:405`), ArrayExhibit (`:595`), WseqExhibit (`:107`), ListRevExhibit (`:1437`), TwoLabelExhibit (`:535`) |
| `wpt_sound` | the pinned export `cs_twp_readout` (`Examples/CallSmoke.lean:451`, at `:457`) |

No shipped-driver statement consumes any of them: the driver lanes
(§2.4) run their own inductions.

### 2.2 The mirror's certification and completeness

`CerberusRound M c c'` (`Round.lean:205`) is one round in the driver's
own vocabulary. At every driver state embedding the context and the
configuration `c`: the engine's step list is `s :: post` — HEAD form
since E4: at a reducible `unseq` the engine's list has one entry per
reducible component, last-first (`get_ctx_unseq_aux`), and the shipped
loop reads its head; the singleton reading is a theorem for value arenas,
root redexes and `Cunseq`-free decompositions (`step_ctx_singleton_of_root`,
`Decomp.get_ctx_single`) — the head `s` is advanceable, and the shipped
`advance_step` on it is one active transition to the state embedding
`c'`. Active means `NDactive NOWAKEUP`: no other thread is woken. It is
stated at the loop body, with no fuel dependency (loop-level reading
`CerberusRound.loop_step`, `:1045`). The certification is

```lean
theorem engine_step_matchU {M : MachineCtx}
    {e e' : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    {ρ' : EnvStack} {ctl ctl' : Ctl} {σ σ' : Mem}
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel)
    (hs : Step M (e, ev0 :: evs, ctl, σ) (e', ρ', ctl', σ')) :
    CerberusRound M (e, ev0 :: evs, ctl, σ) (e', ρ', ctl', σ') := by      -- Round.lean:1111
```

— on `Frag`, at a cons-shaped environment, at any control and successor
control, with the static size bound, and no well-formedness premise;
`step_iff_cerberusRound` (`:1880`) is two-sided under the hypothesis
that a mirror step exists.

Completeness is the other direction, per constructor.
`frag_round_complete` (`:7701`): at every non-value `Frag` configuration
the mirror steps, or the round is a classified refusal, or the
configuration is in the residual. The refusals (`ShippedRefusal`, `:225`)
are stated in the engine's vocabulary. `error`: the step list is
`[Step_error2 msg]`. `killed`: `advance_step` returns `NDkilled r`.
`fork`: `CerbND.runND` delivers at least two executions. The `panic`
family: the engine's own `failwithI`, LemLib's kernel-opaque failure
(not the `panic!` arms of §3). `error_next`: a success round into
an ill-typed next round. The residual (`OpenRound`, `:371`) has two arms.
`eval_uncovered`: an operand whose outcome the classifier `evalClass`
does not decide. Its members: a leaf the engine's evaluator accepts
where the mirror evaluator does not (a `Proc`-named unbound symbol, a
binop at two floats, a comparison at symbolic integers — `OpEq` at two
ctypes was a member until E3 mirrored `ctypeEqual`), since E3 a std.core
call whose body exceeds its static budget `stdBudget` (the engine unfolds
and continues, the mirror stops; reached by no transcribed std.core
function), since E4 the same leaves at an operand of the focused
component under a `Cunseq` frame (`operandsOfU`; no new leaf), and —
since E2 — shapes the
engine does NOT accept but whose refusal the classifier does not
certify: a `case` matching no pattern (the engine's opaque `failwithI`
PANIC), `undef(<<UB088>>)` (its location is the call-location
parameter), a constructor dispatch failure (an engine KILL), a
constructor operand list whose first failing operand is an undef
followed by another failure (the engine's Exception-first
`except_sequence`), and a `case` whose selected branch the mirror's
depth guard rejects. The classifier answers `.uncovered` and claims
nothing about the whole operand (`EvalClass.lean`'s header lists the
members; `docs/2026-09-05_fragment-closure-e2-notes.md`). `run_surplus`: a jump with more
arguments than parameters whose surplus does not evaluate. One lemma per
redex root carries the classification (`complete_store` … `complete_ret`,
`Round.lean:2719`–`:6484`). `cerberusRound_classify` (`Round.lean:7839`; premises `SeqWF`,
`ctl.κ = []`) sorts every well-sized `Frag` configuration into
`value_done`/`value_annot`/`step`/`refused`/`open_` (`RoundClass`, `Round.lean:1925`).
Every operand the classifier rejects is a proved engine kill; operands
it leaves uncovered are not characterised, so the residual is a
superset of the engine-accepted shapes (KOI B7).

Two engine-round bridges exist by design (KOI B12). `engine_step_matchU`
certifies the mirror; the adequacy lanes consume the production-profile
round `loop_step_frag`/`loop_step_frag'` (`DriverCollapse.lean:2447`/
`:2351`), proved independently per redex (`Round.lean:144`–`:156`). No
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
state constructed. `engine_adequacy` (`:1304`; `_alloc` `:1408`) turns it
into the engine fact `DriverSafeCtl M th₀ e ρ ctl σ ψ` (`:945`, read in
§4: exhaustion or PROGRAM-DONE with the readout, at EVERY fuel, no other
outcome). Its ties are `LabeledProcs` for the callees
(`DriverCollapse.lean:2769`) and `CtlTied` for the procedures already on
the control (`:2796`). The mirror suffices because `NotStuck` supplies a
mirror step at every reachable configuration and `loop_step_frag'` makes
it the loop's unique next iteration: `drive_safe_aux` (`Adequacy.lean:1101`), an
unpinned fuel induction under the control invariant `ControlOk` (`Adequacy.lean:800`).
Its premise `MachineCtx.FragProcs` (`Adequacy.lean:767`: every declared procedure body
in `Frag` with its static bound) lets it follow the engine into a callee
and back. Fuel 0 is the exhaustion kill (`loop_zero_exhausts`,
`DriverCollapse.lean:2580`). Fuel 1 at a delivered value is the
exhaustion of the drain iteration, the loop's last pass over the
emptied thread list (`loop_step_done_exhaust`, `:2850`); fuel ≥ 2 there
is PROGRAM-DONE (`loop_step_done`, `:395`).

**The total lane** (`ProdLoop.lean`). `wpt_driver_cps` (`:646`) is the
budget induction in continuation-passing form over the ambient control,
the driver-level twin of `wpt_sound_cps`. It concludes the pure delivery
fact `DriverDoneCtl M₀ th₀ e ρ ctl σ ψ k` (`:481`). That fact: from any
driver state holding the configuration at `ctlThread th₀ e ρ ctl`, with
the file tie and the whole-file registration tie, the loop returns
PROGRAM-DONE for a value satisfying `ψ` within `k + 2` iterations. The
call case applies the hypothesis to the callee at the pushed control
with the continuation budget added; every round is `loop_step_frag`
(`driverDoneCtl_step`, `:567`). The launcher is `wpt_driver_done_procs`
(`:853`; a populated table, the entry control `⟨[], some p, ℓ, lc, sp⟩`
of a declared procedure).
It is the route of `fib_rec_certified_production` (`main` calls `fib`,
which calls itself twice) and `even_odd_certified_production`
(`even`/`odd` call each other under a symbol-dependent table; three
procedures). The single-procedure lane `DriverDoneAt`/
`wpt_driver_aux`/`wpt_driver_done(_alloc)` (`:58`/`:185`/`:313`/`:381`), at
the empty table, is the route of the eleven one-procedure statements
(seven authored examples and the four emitted corpus programs in §2.5).

**The projection** (`Adequacy.lean`). `project_triple_pure` (`:1669`)
takes an Iris triple to the Iris-free `MemTriple M ctl ρ e P ψ`
(`:1582`). Input: a triple whose precondition is footprint ownership and
whose framed post pure-entails `ψ R w.val σ'` under the coupling
invariant. Output: memory splits as `P ⊎ R`, and from any driver state
holding the configuration the shipped loop at every fuel exhausts or
delivers `(v, σ')` with `ψ R v σ'`. `project_triple_pure_alloc` (`:1769`)
is the allocating twin (`allocBudget B` in the precondition;
`MemTriple_alloc`, `:1682`, under `LaunchCoh … B`, `:422`). The one
Iris-shaped hypothesis `hpost` names `CohG`/`metaInterp`/`byteInterp` —
the documented exception (API.lean header). It is discharged only
through the public `*_consequence` lemmas (`:1935`–`:2033`), which
deliver the pure memory view `CellCoh` (`Heap.lean:358`), `Sat`
(`Adequacy.lean:1479`) and `DeadAt` (`:1964`). A positive exhibit names
none of the internals (§5, the boundary check).

**The closed forms over the shipped pipeline** (`ProdEntry.lean`). The
authored program is wrapped as a synthetic file — one procedure by
`prodFile` (`:125`), `main` plus declared procedures by `prodFileWith`
(`:545`; `prodFile e = prodFileWith [] e` is `rfl`, `:550`). The total
pipeline theorem `prod_run_eqJ_procs` (`:738`; one-procedure form
`prod_run_eqJ`, `:402`) turns a `DriverDoneCtl` at the production
profile into the shipped composite's result. Its bound:
`k + 2 ≤ CerbFuel.driverFuel`. The partial pipeline theorem
`prod_run_safe_procs` (`:790`) turns a `DriverSafeCtl` there into a fact
at every `fuel` about
`CerbND.runND (CerbND.drive_lemFuel fuel fmapEmpty false (prodFileWith procs e) args) (initial_driver_state …).1`.
That is exactly one execution: `nd_status.Killed dst'
CerbND.fuelExhaustedKill`, or `nd_status.Active dres` with the
postcondition. The shipped `drive` is the instance at
`fuel := CerbFuel.driverFuel` (`CerbND.lean:467`, `rfl`).

### 2.5 The thirteen closed shipped-driver statements

Each has the execution function
`CerbND.runND (_root_.drive fmapEmpty false F args) ((initial_driver_state sup F fs).1)`,
`F` the wrapped program, and concludes `= [(nd_status.Active dres, [], dst')]`
with a pure readout on `dres`/`dst'`. None carries a termination
hypothesis. Where the certified round count depends on an input, the
in-budget bound is an explicit premise against the name the semantics
exports for this purpose (`CerbFuel.driverFuel = 100000000`, generated
`CerbFuel.lean:71`). All thirteen are pinned trio-exact (§3). The tenth,
`t1_certified_production` (E4), is the first over an EMITTED program:
`../docs/corpus-e0/t1.c`'s `main` as the Cerberus C front end emits it,
transcribed verbatim (`Examples/CorpusE0.lean:960`, tied to
`../docs/corpus-e0/t1.annot.core` by the corpus skeleton speedbump, §5). Its
file object is `prodFileLib stdlibE3 [] t1Main` (`ProdEntry.lean:856`): a
SYNTHETIC file whose `stdlib` is the transcribed THREE-function std.core
fragment `stdlibE3` (`StdCore.lean:153`: `is_representable_integer`,
`conv_int`, `conv_loaded_int`, checked constructor for constructor against
the pinned std.core source) with `impl0 = ∅` — behaviour-equal to the
pipeline's `--nolibc` file only on programs that reach those three
functions and no `Impl` constant. The consequence, measured (E3 audit
D-6): `conv_loaded_int('signed int', Specified(INT_MAX+1))` classifies
`.kill` on this file where the pipeline's file WRAPS through the impl
function (KOI A7; the whole `core_file` as the statement's object is the
named target, not done). The count thirteen follows the README and CLAIMS:
the nine pre-dialect statements, t1, t4, t5 and t6; the dialect arc's three closed
statements over its synthetic exhibits — `exhibitA_prod_e1`
(`EmittedAExhibit.lean:297`), `exhibitB_prod_e2` (`EmittedBExhibit.lean:672`),
`exhibitC_prod_e3` (`EmittedCExhibit.lean:731`) — have the same execution
function and are pinned, and are listed with their exhibits in the README
table rather than counted here.

| Statement | File:line | Input-dependent premises beyond the program's metadata |
|---|---|---|
| `exhibitA_prod` | `ProdExhibit.lean:264` | none |
| `fib_certified_production` | `ProdLoopExhibit.lean:75` | `hn : 0 ≤ n`, `hfuel : 2 * n.toNat + 6 ≤ CerbFuel.driverFuel` |
| `counter_loop_certified_production` | `ProdLoopExhibit.lean:622` | `hn`, `hfuel : 6 * n.toNat + 8 ≤ CerbFuel.driverFuel` |
| `list_reverse_certified_production` | `ProdLoopExhibit.lean:1439` | none |
| `dispose_list_certified_production` | `DisposeExhibit.lean:1479` | none |
| `region_loop_certified_production` | `RegionLoopExhibit.lean:635` | `hcost : 0 < regionCost al sz`, `hn`, `hB : n.toNat * regionCost al sz ≤ headroom prodMem₀.lastAddress`, `hfuel : 7 * n.toNat + 5 ≤ CerbFuel.driverFuel` |
| `malloc_list_certified_production` | `MallocListExhibit.lean:1658` | `hn`, `hB : n.toNat * (15 + max al.toNat 1) ≤ 281474976710647`, `hfuel : 25 * n.toNat + 9 ≤ CerbFuel.driverFuel` |
| `fib_rec_certified_production` | `FibRecExhibit.lean:852` | `hn`, `hfuel : fibRounds n.toNat + 4 ≤ CerbFuel.driverFuel` |
| `even_odd_certified_production` | `EvenOddExhibit.lean:710` | `hn`, `hfuel : 3 * n.toNat + 6 ≤ CerbFuel.driverFuel` |
| `t1_certified_production` | `CorpusT1Exhibit.lean:803` | none (the file is `prodFileLib stdlibE3 [] t1Main`, above) |
| `t5_certified_production` | `CorpusT5Exhibit.lean:548` | `hsup : 600 ≤ sup` — a sufficient floor, not necessary (the composite delivers the same value at `sup = 0`, measured); same library-fragment file boundary as t1 |
| `t6_certified_production` | `CorpusT6Exhibit.lean:618` | `hsup : 600 ≤ sup` (sufficient, not necessary, as above); same library-fragment file boundary as t1 |
| `t4_certified_production` | `CorpusT4Exhibit.lean:1429` | `hsup : 600 ≤ sup` (sufficient, not necessary, as above); same library-fragment file boundary as t1 |

Package definitions in these statements, exactly — beyond the authored
program and its wrapper (`prodFile`/`prodFileWith`/`prodFileLib`), read
off the thirteen statement texts:

| Statement | In the conclusion | In a premise |
|---|---|---|
| `exhibitA_prod` | `sevenVal`, `sevenBytes`, `intTy` (`Examples/Layout.lean:57`, `:65`, `:50`); the readout `CellCoh` (`Heap.lean:358`) | — |
| `fib_certified_production` | `ivVal` (`LoopExhibit.lean:63`), `fibSpec` (`FibExhibit.lean:60`) | — |
| `counter_loop_certified_production` | `intUndefBytes` (`AllocExhibit.lean:88`), `sevenBytes`, `intTy`, `CellCoh` | — |
| `list_reverse_certified_production` | `ptrVal` (`ListRevExhibit.lean:466`), `SeedChain` (`:1213`), the footprint type `CellMap` (`Adequacy.lean:1471`), the readout `Sat` (`:1479`) | — |
| `dispose_list_certified_production` | engine fields only | — |
| `region_loop_certified_production` | engine fields only | `regionCost`, `headroom`, `prodMem₀` (`Heap.lean:2322`, `:2267`, `ProdEntry.lean:212`); at zero cost the statement would be vacuous, which `hcost` excludes |
| `malloc_list_certified_production` | engine fields only | none — the budget premise is in engine vocabulary, bridged inside the proof (`ml_budget_bridge`, `MallocListExhibit.lean:1630`) |
| `fib_rec_certified_production` | `ivVal`, `fibSpec` | `fibRounds` (`FibRecExhibit.lean:450`: `fibRounds 0 = fibRounds 1 = 3`, `fibRounds (n+2) = fibRounds (n+1) + fibRounds n + 9`; closed form `fibRounds n + 9 = 12 · fibSpec (n+1)`, `:470`) |
| `even_odd_certified_production` | `ivVal` | — |
| `t1_certified_production` | `lint` (`IntRules.lean:69`: the loaded `Specified` integer value); `stdlibE3` (`StdCore.lean:153`) and `t1Main` (`Examples/CorpusE0.lean:1061`) inside the file object | — |
| `t5_certified_production` | `lint`, `stdlibE3` and `CorpusE0.t5Main` inside the file object | — |
| `t6_certified_production` | `lint`, `stdlibE3` and `CorpusE0.t6Main` inside the file object | — |
| `t4_certified_production` | `lint`, `stdlibE3` and `CorpusE0.t4Main` inside the file object | — |

Beside them, two closed PARTIAL forms consume `prod_run_safe_procs`:
`fib_rec_certified` (`FibRecExhibit.lean:803`) and `even_odd_certified`
(`EvenOddExhibit.lean:662`) — every `n ≥ 0`, at every `drive_lemFuel`
fuel, no budget bound.

### 2.6 The memory invariant

`MemWF σ` (`Heap.lean:1583`) is the global memory well-formedness
invariant: ten fields, each an engine fact with a `CerbMem.lean` cite.
Allocation-id discipline: `live_lt`, `dead_lt`, `live_dead`. Pairwise
range disjointness of all live allocations: `disj`. Cursor and size
bounds: `cursor_lo`, `size_nonneg`, `la_wf`, `la_pos : 0 < lastAddress`
(`la_pos` [AGENT 2026-09-03], DECISIONS "KILL/FREE K3 LANDED"). The
dynamic-address facts: `dyn_lo`, `dyn_disj`. It is a field of the state
interpretation `CohG` (`Heap.lean:2632`, under cursor presence) and of the launch
premise `LaunchCoh` (`Adequacy.lean:422`). `prodMem₀_memWF`
(`ProdEntry.lean:243`) is the cold-start instance; `create_fresh_global`
(`Heap.lean:1801`) is "fresh means fresh in the concrete allocation
model". Every memory operation of the fragment has its preservation
theorem: `MemWF.loadM` (`:1817`), `MemWF.storeM` (either locking mode,
`:1877`), `MemWF.allocateObject` (any initializer, `:1898`),
`MemWF.allocateRegion` (`:1937`), `MemWF.killM` (both arms, `:2010`).

## 3. What is trusted

**The trust base.** (i) The Lean kernel and the trio (`Audit.lean:213`–
`:214`). (ii) iris-lean, as DEFINITIONS: the WP, the BI connectives and
the ghost theory appear only inside kernel-checked proof terms and
contribute no axiom; the closed statements' texts are Iris-free. (iii)
The pinned cerberus-lean semantics (`f95ef8d9c`) as the semantics of
Core: a policy decision, sampled by differential validation against the
OCaml oracle, not proved (README "What you are asked to take on faith").
It is a pin, not the mainline; the queued re-pin and its one
exported-text change (`killM_killed_inv`) are KOI A6. The pinned tree
declares no `axiom` and contains no `sorry`: `grep -rn '(sorry'` over the
primed `generated/*.lean` is empty and the build log has no `declaration
uses sorry` (README "The trust story"; `docs/2026-09-03_repin-fuel-notes.md`).

**The `panic!` arms.** The pinned tree does contain `panic!` arms: 61
in the hand-written seams, 40 of them in `CerbMem.lean` (e.g.
`sizeofCtype` at `Void`, generated `CerbMem.lean:380`), none in
lem-generated code (counts DERIVED, `grep -c 'panic!'` less comment
lines; the `generated/` directory holds byte-identical copies of the
hand-written seams named in `handwritten_copy.manifest`, which is why a
seam file is cited as generated `CerbMem.lean`). Fifty-four of them mirror an OCaml `assert false`/`failwith` arm,
where the OCaml run aborts; seven are Lean-side guards with no OCaml
abort behind them (the five `CerbFS.lean` refusals at the file-system
model's boundary, `CerbFS.lean:47`; `CerbTags.lean:34`;
`CoreParser.lean:2097`). The kernel reads `panic!` as the return type's
`Inhabited` default (`= default` by `rfl`, generated
`CerbMem.lean:1127`–`:1132`). A theorem about `drive` is therefore about
the Lean definition, which on a state reaching such an arm continues
where the OCaml faults. The rules' premises keep proved programs away
from them (`create_atomic`'s `hsz : 0 < sizeofCtype …`, `Rules.lean:1000`;
the NO-RULE `create` rows, §6). No theorem states that an export's run
reaches none, and the sweep cannot see one (a term, not an axiom).
Owner: cerberus-lean's typed-failure-outcomes pass (KOI A5). This is
distinct from §2.2's `panic` family: LemLib's `failwithI`/
`fuelExhaustedWith` are `opaque`
(`.lake/packages/LemLib/lean-lib/LemLib.lean:173`, `:187`), so the kernel
has no equation for them and a theorem holds at every value they take.

**What the build checks** (`Audit.lean`, the last import of the library
root, elaborated by every `lake build`). Every pinned export exists, is
a theorem, and has axiom set EXACTLY the trio. The t4 production
checkpoint has 896 exact pins: E4's 652, E5 slice 1's 60, the second
slice/t5's 67, t6's 39 and t4's 78 (derived breakdown; individual
measurements in the E5 records, latest `docs/2026-09-06_e5-t4-loop.md`).
Every theorem of every `CerberusHeapLang.*` module, internal details
included, is bounded by the trio. `sorryAx`/`ofReduceBool`/`ofReduceNat`
reach no constant of any kind. Precision: "exactly the trio" is the pinned exports' property;
every other theorem's cone is bounded by the trio, by the sweep. The
public-named lemmas with SUB-trio cones are therefore unpinned, as
`Audit.lean`'s comments record them (among them `fibRounds_closed`,
`regionCost_pos` and the `freshBase_*` bounds with `[propext,
Quot.sound]`; the four `∈`/`contains` bridge lemmas `mem_contains_int`,
`contains_cons_int`, `contains_cons_ne_int`, `int_beq_eq_true`;
`Decomp.get_ctx_rebuild_action` with `[Quot.sound, propext]`;
`Decomp.callRedex?_inv`, `callRedex?_some`, `pot_plug_call_le`,
`callRedex?_none_of_jumpRedex?_some`; and, since E2, the evaluator
bridge `pull_bridge`). The `BareHead` lemmas are gone with `BareHead`
(E1). E3 adds 80 pins (589 at the combined head: E3's 80 plus the E2 audit's
`unspec_bytes`; `docs/2026-09-05_e3-notes.md` §9) and leaves unpinned, with sub-trio cones, the `rfl`/`decide` facts of
StdCore/IntRules and CorpusE0's kernel-decided walk (listed in
`Audit.lean`'s E3 paragraph). E4 removes 1 (`CorpusE0.t1_unseq_not_frag`,
false since `Frag.unseq`) and adds 62 (650; `docs/2026-09-05_e4-notes.md`
§8), leaving unpinned the sub-trio `rfl`/`simp` facts at the new
constructors (listed in `Audit.lean`'s E4 paragraph); the E4 range
audit's R-1 adds `unseq_focus_round`/`unseq_vals_round` (652; the E4
split is 64 trio-exact / 91 sub-trio). E5 slice 1 adds 60 (712; measured
over its 184 new theorems: 60 trio-exact, 124 sub-trio, listed unpinned
in `Audit.lean`'s E5 paragraph — the `negRedex?`/`negFree`/`pot`/`esize`
`rfl`/`simp` facts and the `*.eq_def` equation lemmas).
`regionCost_eq`, `runND_killed` and, since the E2 audit fixes,
`unspec_paddingByte` have no axioms (`:440`, `:733`–`:734`). Kernel-only proof methods: no `native_decide`, `bv_decide`
or `ofReduce*` anywhere (gate 1, `../scripts/test_unit.sh:28`).

**The declared boundary is empty** ("There is no declared boundary
axiom", `Audit.lean:45`). What is NOT trusted: the mirror `Step`, the
judgments, the discharge devices, the collapse lemmas. They are proof
devices, none of which appears in the statement of any pinned export
([USER 2026-09-02], CLAUDE.md "The referent of every export is the
genuine semantics"). No hand-written driver loop, scheduler or discharge
function occurs in any export's statement. The closed statements name
the shipped composite; the generic statements name
`drive_nonmemory_steps_aux2_lemFuel`, `runOne`, `driver_state` and the
engine's result types.

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
(`LoopExhibit.lean:429`), a seeded exhibit, verbatim (`loc ann ra mo bty
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

Read through `DriverSafeCtl` (`Adequacy.lean:945`). Take any driver
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
`Adequacy.lean:1304`–`:1316`; `project_triple_pure`, `:1631`–`:1643`;
`wpt_driver_cps`, `ProdLoop.lean:642`–`:655`; `wpt_driver_done_procs`,
`:843`–`:856`), and what each means:

- `htd : M.tagDefs = fmapEmpty`, `hex : M.extern = fmapEmpty` — no
  struct/union tag definitions and no extern indirection in any proved
  configuration; this matches the production driver's
  `drive fmapEmpty false …` (KOI B4).
- `hκ : ctl.κ = []` — the entry control has an empty call stack (the
  value arm selects PROGRAM-DONE over RETURN, `shipped_done`,
  `Round.lean:1955`).
- `hfrag : Frag e`, `hQf`, `hPf : M.FragProcs` — the program, every
  registered label body and every declared procedure body are in the
  fragment (`Adequacy.lean:767`).
- `hpot : pot e ≤ lemDefaultFuel`, `hQpot`, `FragProcs.potBound` — THE
  STATIC FUEL PREMISE. `pot` (`Potential.lean:44`) is a step-monotone
  size potential on terms; it dominates §2.2's round-level measure
  `esize` (`Frag.esize_le_pot : esize e ≤ pot e`, `:172`), so this premise
  discharges the certification's `hsz`. The engine's pure-expression
  evaluator and context search are fuelled at LemLib's constant
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
- `hcoh`/`hl : LaunchCoh …` — the seeded footprint, or, for allocating
  programs, the footprint plus the global memory well-formedness
  invariant `MemWF` (§2.6) and the budget fit `B ≤ headroom σ.lastAddress`
  (`Adequacy.lean:422`–`:430`).
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
The manifest, the import-direction check and the boundary check run in
the full gate (the claim matrix's name check rides in the manifest run);
the inventory is on demand; the module classification is the data all of
them read.

- **The rule-use and classification manifest**
  (`scripts/capability_manifest.lean` → `docs/CAPABILITY_MANIFEST.md`,
  regenerated and diffed at `test_unit.sh:47`). Its rows are the
  engine-SUCCESS variants of every `Frag` constructor, a hand-maintained
  table read off `Frag`, `Step` and the engine's memory-operation arms.
  Each row distinguishes rules consumed at both strata, a proved rule
  with one stratum still undemonstrated, partial-only support, no rule,
  or an out-of-scope shape. The generated report's tail is the current
  census. E5's seven new rule rows are RULE-PARTIAL-UNDEMONSTRATED:
  t5 and t4 consume the total faces; no partial corpus derivation consumes
  their twins yet. These include the exact whole-cell read-footprint
  face used by t4's unsequenced addition. The report checks both facts
  and requires a row update when the missing consumer appears.
  What green establishes is stated exactly by the generated, gate-diffed
  header (`docs/CAPABILITY_MANIFEST.md:8`–`:26`, "WHAT GREEN ESTABLISHES,
  EXACTLY"). Not established:
  exhaustiveness of the table over the engine's success shapes (a
  reviewed reading); a NO-RULE or OUT-OF-SCOPE row is a stated absence,
  not coverage.
- **One module classification** (`scripts/module_classes.tsv`, pure data,
  reprinted at the head of the manifest; ten classes, the vocabulary in
  its header, `engine-mirror-test` reserved with no member). The
  manifest's consumer set is `positive-client` ∪ `declared-smoke` (22
  modules: the twenty program exhibits — `EmittedAExhibit`,
  `EmittedBExhibit`, `EmittedCExhibit` and `CorpusT1Exhibit` among them —
  `Examples.CallSmoke`, `Examples.ReadinessSmoke`). The production wrappers and the negative
  test are not consumers. Fail-hard behaviour (TSV header lines 8–11):
  the two Lean instruments fail on a package module absent from the
  list; all three instruments fail on a classified module absent from
  the build or a class outside the vocabulary.
- **The import-direction check** (`test_unit.sh:76`): no module of class
  `core` imports an exhibit, example or production module.
- **The client-boundary check** (`../scripts/boundary_check.sh`,
  `test_unit.sh:99`). After stripping comments, a `positive-client`/
  `declared-smoke`/`example-support` module must not mention a logic
  internal. The internals: the coupling invariant and state
  interpretation (`CohG`, …); the judgment unfoldings (`wps.pre`, …);
  the mirror transition (`Step.<name>`); the engine's transition and
  driver definitions (`step_ctx`, `driver2`, …). The full pattern is
  `boundary_check.sh:46`. Text-based: it catches honest drift.
  Per-module allowances live in the TSV with their reason; there are
  ZERO at this revision (`BOUNDARY: 24 modules checked, 0 internals
  mention(s) in total, exit=0`, `docs/2026-09-05_e4-notes.md` §11, the
  gate at the E4 head). A
  malformed TSV row is red.
- **The claim matrix** (`docs/CLAIMS.md`, hand-written prose stated as
  such in its header). Per headline claim: exported theorems, kind,
  demonstrating exhibits, supported variants (manifest rows), known
  exclusions (KOI pointers), freshness check. The generator checks that
  every declaration a claim row names exists and that every
  declaration-shaped backticked span of every cell is a constant, a listed
  vocabulary word or a RETIRED name carrying its `(retired …)` marker (14
  rows, 133 names in the theorem cell, 290 spans across every cell; planted
  both ways).
- **The parametric inventory** (`scripts/parametric_inventory.lean`) is
  ON DEMAND, not in the gate — [AGENT 2026-09-04] (DECISIONS "AR5-MANIFEST
  LANDED and COMBINED"): the boundary check is its cheap gate twin, and a proof-term
  measurement without a verdict is not a check. Its configuration is
  fail-closed: a missing export seed or an unclassified module aborts
  the run (`parametric_inventory.lean:1`–`:16`).

## 6. What is not covered, and not claimed

Each item points at its register entry; none is hidden in a proof.

- **The fragment boundary** is §1's (KOI B8; CLAIMS "Not claimed").
  Five OUT-OF-SCOPE variants lie inside the fragment's constructors but
  outside the mirror (manifest OUT-OF-SCOPE rows): a jump with a
  non-evaluating surplus argument; `pure(e)` at a covered operand the
  classifier does not decide — a leaf the engine evaluates but the
  mirror evaluator does not (a procedure-named symbol, a mirrored binop at two floats, a symbolic comparison; since E3 a std.core call over its `stdBudget`; `OpEq` at two ctypes is mirrored since E3), or an E2 shape the engine refuses but the
  classifier does not certify (a `case` matching no pattern, `UB088`, a
  constructor dispatch failure, an undef-then-raise constructor operand
  list, a branch the depth guard rejects) — the characterized residual
  `OpenRound.eval_uncovered` (§2.2); a `PEcall` at an `Impl` name
  (`<Integer.conv_nonrepresentable_signed_integer>`, reached by `conv_int`
  at a non-representable value — every file this package builds has an
  empty `impl` map, so the call is the engine's KILL; E3); `PtrEq` at two
  concrete pointers of differing provenance (the engine forks); the `Impl`
  procedure call `Eproc _ (Impl _) _`. (The pre-E1
  fifth — an annotated value at the plain-symbol binder, kept out by
  `BareHead` — is mirrored since E1 and ruled since t4's E5 condition.)
- **The twenty-four NO-RULE variants** — admitted by the fragment and the
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
  | `sseq_tuple`, `wseq_sym` (2) | the binder at an ANNOTATED head value `{A}v` (LETS-/LETW-ANNOT; mirrored since E1/E2, no statement rule). `sseq_sym` is ruled at both strata since t4's short-circuit condition, with a total client; `wseq_tuple` at an annotated tuple is RULE since E4, the shape reached by emitted `let weak (a, b) = unseq(…)`. |
  | `pure_op` (5, E3) | the emitted arithmetic and std.core leaves the mirror computes but no rule states: `catch_exceptional_condition_sub/_mul` (the `+` rule's shape, pending an exhibit), `_div/_rem_t/_shl/_shr` (the memory model's own divisor-zero/shift arms), `wrapI_<op>` (unsigned; the corpus is `int`), standalone `__conv_int__` (its non-representable arm is the impl-defined wrap `mk_conv_int` computes), standalone `conv_int`/`is_representable_integer` and their bodies' leaves (`Ivmin`/`Ivmax`, ctype `=`, `/\\`, `\\/`, `is_unsigned` at a leaf — reached inside the RULED `conv_loaded_int` unfolding). The `Impl`-name `PEcall` is the OUT-OF-SCOPE row above, not counted here |
  | `unseq` (2, E4) | the race: `unseq(v_1, …, v_n)` whose components' dynamic annotations RACE (`do_race`) — the engine's UB035 kill, mirrored as the classification `complete_unseq_vals` (`.killed`); no rule delivers a value there and `wpt_unseq_vals` requires `collectUnseq … = some _`; and a jump or a call reaching the root THROUGH the `Cunseq` frame (`run l(…)`/`pcall f(…)` as the focused component — mirrored, `Step.unseq_inv`'s run/call disjuncts, `wpt_jump_frame_unseq` carries the jump frame; no exhibit reaches one, so no rule face is demonstrated; E6/E7's consumer) |

- **Masks.** Both judgments are fixed at `⊤`; the generalisation is a
  RefinedC-arc item ([USER 2026-09-04]; §1; KOI B11).
- **The fuel constants** `lemDefaultFuel`/`CerbFuel.driverFuel` (§4; KOI
  A1, a ruled semantics defect, fix pending upstream); the outer-fuel
  quantifier (KOI A2); the singleton equation (KOI B5).
- **The engine's `panic!` arms** (§3; KOI A5, the typed-failure-outcomes
  pass upstream). A5 names `killM`'s dead-static-kill arm: at this pin
  that arm is a kill (generated `CerbMem.lean:1906`–`:1907`); the mainline's
  re-mirroring, which the re-pin brings, makes it a `panic!`. The pin's
  drift from the mainline is KOI A6.
- **Empty tag definitions and extern** in every proved configuration
  (§4; KOI B4).
- **The mirror-completeness residual.** `OpenRound`'s two arms are
  characterised, not closed (§2.2; movers at `Round.lean:371`–`:424` and
  in `EvalClass.lean`'s header). `Frag.case_value` carries `hbsz`, not a
  theorem but a membership premise: the selected branch's `esize` is
  bounded by the case node's (`Soundness.lean:8252`). The client
  discharges it per program — `rfl` for authored programs
  (`caseProg_select`, `CaseExhibit.lean:68`) (KOI B7).
- **Statement-shape limitations.** Seeded exhibits have no cold-start
  form (KOI B3). The straight-line exhibits sit at the no-procedure
  profile `spikeCtx`/`spikeCtl`, a thread state the shipped driver never
  parks `main` in (it parks it at `current_proc_opt := some main_sym`,
  generated `Driver.lean:530`). This is admitted because the round needs
  the current procedure only at a jump (`loop_step_frag'`'s `hjmp`,
  `DriverCollapse.lean:2362`; `CtlTied.noproc`, `:2804`) (KOI B2). Six
  any-memory total equations have no twins, and tree rotation has no
  shipped-pipeline statement (KOI B1). The round-count bounds of
  `fib_rec_certified_production`, `even_odd_certified_production` and
  `tl_wpt` carry disclosed slack; nothing claims tightness (KOI B6).
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
  Records: `docs/2026-09-02_fragment-closure-notes.md`, re-established
  after each dialect slice in `docs/2026-09-05_fragment-closure-e1-notes.md`,
  `docs/2026-09-05_fragment-closure-e2-notes.md`,
  `docs/2026-09-05_fragment-closure-e3-notes.md` and
  `docs/2026-09-05_fragment-closure-e4-notes.md`.
- **Goal 3 — a global memory well-formedness invariant: CLOSED**, by
  `MemWF`, its cold-start instance and its preservation theorems for
  every memory operation of the fragment (§2.6). Record:
  `docs/2026-09-03_kill-free-arc-record.md`.

Not a goal of the demo ([USER 2026-09-02], same ruling): covering all of
Core. What remains open is §6's list, each item with its KOI number. The
records of the arcs that closed the goals are indexed in
`docs/2026-09-04_architecture-history-archive.md`.
