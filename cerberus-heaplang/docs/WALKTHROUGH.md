# A walkthrough: this is the theorem, this is how to read it

For a reader who knows separation logic and roughly what Iris is, and
has never heard of Cerberus. Seven sections: the claim and one exhibit
(§1); the readout predicates (§2); the logic, rules quoted verbatim
(§3); the memory-model view (§4); the engine attachment (§5); the
in-build audit (§6); what is deliberately out (§7). Everything in a
`lean` block is quoted verbatim from
[`CerberusHeapLang/`](../CerberusHeapLang/) at this checkout, and every
claim names a theorem you can `grep`; no line numbers are given. Some
quoted declarations sit inside a Lean `section` whose `variable`s are
part of the statement without appearing on the theorem line; a line
"Section variables not shown" lists them by name. The machine-printed
statement of every constant, section variables included, is
[`2026-09-03_c4-signatures-post.txt`](2026-09-03_c4-signatures-post.txt).

**Cerberus** (Memarian, Sewell, et al.) is a semantics for C: it
elaborates C into a small typed functional intermediate language,
**Core**, and gives Core an executable operational semantics — an
interpreter with an explicit memory object model (allocations, byte
representations, pointer **provenance**: which allocation a pointer
derives from). The engine here is the Lean 4 port of that semantics
(cerberus-lean), generated from the same Lem model as the OCaml
implementation and differentially validated against it (README, "What
you are asked to take on faith"). This package puts a classical
separation logic over a fragment of Core, on iris-lean, and proves that
what the logic says is what the engine does — where "the engine" is,
precisely, the execution function named in each statement (§1.3): the
shipped driver's pipeline in the closed statements, the shipped driver's
own per-thread loop at every fuel in the generic ones. The normative
architecture statement is [`../ARCHITECTURE.md`](../ARCHITECTURE.md).

## 1. The claim, and one exhibit

### 1.1 The shape

The target: `s |= P && core_exec(prog, s) ~~> term ==> term = some(s')
&& s' |= Q`, for P and Q "just memory + pure properties". Its
realization is the triple over engine states (`Adequacy.lean`):

```lean
def MemTriple (M : MachineCtx) (ctl : Ctl) (ρ : EnvStack) (e : CoreExpr) (P : CellMap)
    (post : CellMap → value → Mem → Prop) : Prop :=
  ∀ (R : CellMap), P ##ₘ R →
  ∀ (σ : Mem), Sat M.tagDefs σ (Iris.Std.PartialMap.union P R) →
  ∀ (th₀ : thread_state), th₀.current_loc = M.currentLoc →
    DriverSafeCtl M th₀ e ρ ctl σ (fun v σ' => post R v σ')
```

`σ : Mem` is a real engine memory state (`CerbMem.MemState`); `Sat
M.tagDefs σ (P ∪ R)` is `s |= P` with the frame built in — `P` the
footprint (a finite map of allocation-rooted cells), `R` an arbitrary
disjoint rest (§2). `core_exec` is the SHIPPED driver's own per-thread
loop, through the driver-safety fact:

```lean
def DriverSafeCtl (M₀ : MachineCtx) (th₀ : thread_state) (e : CoreExpr) (ρ : EnvStack)
    (ctl : Ctl) (σ : Mem) (ψ : value → Mem → Prop) : Prop :=
  ∀ (dst : driver_state) (acc : Fmap thread_id (List core_step2)) (fl : Nat),
    dst.core_state0.thread_states = [(0, (none, ctlThread th₀ e ρ ctl))] →
    dst.layout_state = σ →
    dst.core_extern = fmapEmpty →
    dst.core_file = M₀.file →
    LabeledProcs M₀ dst.core_run_state0.labeled →
    CtlTied M₀ dst.core_run_state0.labeled ctl →
    (∃ dst' : driver_state,
      runOne (drive_nonmemory_steps_aux2_lemFuel fl fmapEmpty acc [0]) dst =
        (NDkilled CerbND.fuelExhaustedKill, dst')) ∨
    ∃ (v : value) (σfin : Mem) (ρfin : EnvStack) (pfin : Option sym) (ℓfin : exec_location)
      (rs' : core_run_state) (tr : List trace_event) (ctr : Nat),
      ψ v σfin ∧
      runOne (drive_nonmemory_steps_aux2_lemFuel fl fmapEmpty acc [0]) dst =
        (NDactive (fmapAddBy defaultCompare 0 [Step_done2 v] acc),
         { dst with
            core_state0 := { dst.core_state0 with thread_states :=
              [(0, (none, ctlThread th₀ (ofVal (.pure v)) ρfin ⟨[], pfin, ℓfin⟩))] },
            layout_state := σfin,
            core_run_state0 := rs', trace := tr, dr_step_counter := ctr })
```

`drive_nonmemory_steps_aux2_lemFuel` is the production driver's
per-thread loop (Driver.lean:346; the shipped `drive_nonmemory_steps_aux2`
is its instance at `CerbFuel.driverFuel`), `runOne` its one-layer
application to a driver state; `dst` is ANY driver state whose singleton
thread is `ctlThread th₀ e ρ ctl` — the driver's own `thread_state`
holding `(e, ρ)` at the control `ctl` over the immutables of some `th₀`
whose `current_loc` is the context's — at layout state `σ`, with the
context's file and the two registration ties (§1.3). The conclusion, at
EVERY fuel `fl`: the loop either EXHAUSTS — its value is the kill
`CerbND.fuelExhaustedKill`, the cerberus-lean fuel arc's out-of-fuel arm
(kernel-transparent: `CerbND.drive_nonmemory_steps_aux2_lemFuel_zero` is
`rfl`) — or returns `NDactive` with the PROGRAM-DONE singleton step map
for a value `v` at a final memory `σfin` with `ψ v σfin`, the final
thread at the empty call stack. Nothing else: no kill of any other
reason (no undefined behaviour, no error kill), no ILLTYPED refusal, no
off-protocol step. Exhaustion carries no obligation: partial
correctness. The fuel is unbounded; the triple carries no fuel premise.

**Over the same driver as the total lane.** Until the fuel-lane
restatement (2026-09-03) `MemTriple`'s predecessor was stated over a
package loop (`driveU`, the engine's `step_ctx` with a hand-written
discharge) and carried an interim label, because the shipped driver's
out-of-fuel arm was LemLib's kernel-opaque `fuelExhaustedWith` and no
theorem over all fuels could classify its outcomes; the cerberus-lean
fuel arc (pin `f95ef8d9c`; the request was
[`../../docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md`](../../docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md))
made the arm the transparent kill, and every statement of the partial
lane is now over the shipped loop — the same loop, thread shape and
registration ties the total lane's `DriverDoneCtl` (§1.3) uses. The
package loop is deleted (record: `2026-09-03_f1-notes.md`).

There is no Iris in `MemTriple`. The theorem that produces one from an
Iris triple is the headline of the partial lane:

```lean
theorem project_triple_pure {GF : BundledGFunctors} [SpikeGpreS GF]
    {M : MachineCtx} (htd : M.tagDefs = fmapEmpty) (hex : M.extern = fmapEmpty)
    {ctl : Ctl} (hκ : ctl.κ = [])
    (hQf : ∀ l params cont, lookupLabel (M.labelsAt ctl.proc) l = some (params, cont) →
      Frag cont)
    (hQpot : ∀ l params cont, lookupLabel (M.labelsAt ctl.proc) l = some (params, cont) →
      pot cont ≤ lemDefaultFuel)
    (hPf : M.FragProcs)
    {e : CoreExpr} (hfrag : Frag e) (hpot : pot e ≤ lemDefaultFuel)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value))
    (P : CellMap) (Q : ∀ [SpikeGS .hasLC GF], CoreRVal → IProp GF)
    (ψ : CellMap → value → Mem → Prop)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ P, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c)) ⊢
        WP (⟨e, ev0 :: evs, ctl, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ {{ w, Q w }})
    (hpost : ∀ [SpikeGS .hasLC GF] (w : CoreRVal) (R : CellMap) (σ' : Mem)
      (mm : SpikeHeapF MetaCell) (mb : SpikeHeapF CerbMem.AbsByte)
      (mk : SpikeHeapF AllocCursor), CohG σ' mm mb mk →
      iprop(Q w ∗ ([∗map] i ↦ c ∈ R, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c) ∗
        metaInterp mm ∗ byteInterp mb) ⊢ (⌜ψ R w.val σ'⌝ : IProp GF)) :
    MemTriple M ctl (ev0 :: evs) e P ψ := by
```

Hypotheses: empty tag definitions and extern (`htd`, `hex` — the
production driver runs `drive fmapEmpty false …`) and an empty-stack
entry control (`hκ : ctl.κ = []` — the thread's live control `Ctl` =
call stack, current procedure, execution location, calls arc C1; at a
general control the label map is read at `ctl.proc`, `M.labelsAt
ctl.proc`); the program, every registered label body and every declared
procedure body (`hPf : M.FragProcs`, since the raw WP does not exclude a
call) in the fragment `Frag`; the static fuel bounds `pot e ≤ lemDefaultFuel` and
`pot cont ≤ lemDefaultFuel` per registered body (`pot` is a
step-monotone size potential on terms, Potential.lean; `lemDefaultFuel =
10^6` is the engine's evaluator budget; both are `rfl` for authored
programs — §5 says why they exist, and names the second, operand-level
fuel bound `peDepth` that lives inside `Frag` itself); an Iris triple `hwp` — footprint
ownership entails the WP of the program with any Iris post `Q`; and
`hpost` — the framed Iris post pure-entails `ψ R w.val σ'` under any
coupling witness `CohG σ' …` for the final memory. Conclusion:
`MemTriple M ctl ρ e P ψ`, with no Iris in it. `hpost` is the one
Iris-shaped obligation a client meets; the pure-consequence lemmas
discharge it for the points-to shapes (`cellOwn_consequence`,
`pointsToCell_consequence`, `cellsOwn_consequence`, `cells_consequence`,
`pure_`/`sep_`/`or_`/`exists_consequence`), yielding `CellCoh σ' i c`
facts about the final memory. Beneath it sits the strongest-post form
`project_triple`; `SemTriple` is `MemTriple` at the cells-shaped post
(`SemTriple_iff_Mem`). The allocating twin `project_triple_pure_alloc`
adds `∗ allocBudget B` (§3.2) to `hwp` and concludes
`MemTriple_alloc`, whose launch premise `LaunchCoh` is `Sat` plus
allocator health (README, "The claim"); `struct_create_store_adequacy`
(StructExhibit.lean) is its worked instance.

### 1.2 The exhibit: in-place list reversal

**The program.** Written directly in Core (`ListRevExhibit.lean`),
pretty-printed:

```
save loop: (prev : ptr := NULL(node), cur : ptr := head) in
  lets b = memop(PtrEq, [cur, NULL(node)]) in
  if b then pure(prev)
  else
    lets Specified(n) = load(node*, array_shift(cur, long, 1)) in
    lets _ = store(node*, array_shift(cur, long, 1), prev) in
    run loop(cur, n)
```

`save` registers the label `loop` and runs the body; `run loop(cur, n)`
is the jump — it discards its evaluation context and restarts the
registered continuation. `lets` is Core's strong sequencing `Esseq`;
`store`/`load` go through the engine's memory model (`storeM`/`loadM`),
where a failed check is undefined behaviour and kills the execution;
`memop(PtrEq, …)` is the memory model's own provenance-aware pointer
equality (§4). Each node is one allocation of type `long[2]` (`nodeTy`):
value at offset 0, next pointer at offset 8. The body `lrBody` is a real
term of the engine's generated `CoreExpr`; locations, annotations,
base-type tags and the memory order are universally quantified.

**The production statement** (`ProdLoopExhibit.lean`): a self-contained
program that builds a two-node chain with the engine's own `create` and
then runs the loop above, on the shipped pipeline from the cold start.

```lean
theorem list_reverse_certified_production (sup : Nat) (ra : core_run_annotation)
    (mo : memory_order) (bty sbty pbty cbty bbty nbty ubty : core_base_type)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND
          (_root_.drive fmapEmpty false
            (prodFile (lrProdProg ra mo bty sbty pbty cbty bbty nbty ubty))
            args)
          ((initial_driver_state sup
            (prodFile (lrProdProg ra mo bty sbty pbty cbty bbty nbty ubty))
            fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      (∃ (i₁ i₂ : Int) (Q : CellMap) (p' : CerbMem.PointerValue),
        dres.dres_core_value = ptrVal p' ∧
        SeedChain Q p' [((i₂ : Int), (2 : Int)), (i₁, 1)] ∧
        Sat fmapEmpty dst'.layout_state Q) ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
```

No section variables. `CerbND.runND (_root_.drive …) (initial_driver_state
sup file fs).1` is exactly the composite the cerberus-lean executable
runs — this is a ROOT-OF-TRUST export, one of the nine closed
shipped-driver statements: the genuine driver, no package-defined loop
in the statement (the authored program enters wrapped by `prodFile`,
the synthetic one-procedure file). The theorem quantifies over nothing but the file-system state,
argv and the entry's symbol supply `sup` (the fragment never reads it):
the run is the singleton `Active` execution — an equation, so a total
statement — its delivered value heads a chain seeded as the reversed
list at existential allocation ids (the logic binds the pointers, the
engine picks them), and the final production memory satisfies that
footprint. No package loop, no `Step`, no Iris in the statement. The
general statement beneath it — any chain, any frame, any memory with
`Sat fmapEmpty σ₀ (m₀ ∪ R)`, from any driver state holding the
configuration, the shipped loop at every fuel — is
`list_reverse_certified` (README, "The exhibits"; `DriverSafeCtl`, §1.1).

**The Iris triple** it comes from. The representation predicate is plain
structural recursion, identity-indexed, no step-indexing:

```lean
def isList : CerbMem.PointerValue → List (Int × Int) → IProp GF
  | p, [] => iprop(⌜p = nullNode⌝)
  | p, nd :: ns => iprop(∃ (aN : Int) (q : CerbMem.PointerValue)
      (bs : List CerbMem.AbsByte),
      ⌜p = cellPtr nd.1 aN ∧ 0 < aN ∧ aN < 2 ^ 64 ∧ bs.length = 16 ∧
        nodeValDec fmapEmpty bs nd.2 ∧ nodeNextDec fmapEmpty bs q⌝ ∗
      cellOwn fmapEmpty nd.1 (.own 1) (SpikeCell.mk aN nodeTy bs) ∗ isList q ns)
```

Section variables not shown: `{hlc : HasLC} {GF : BundledGFunctors}
[SpikeGS hlc GF]`. The specification, at the partial judgment `wps`
(§3), with an arbitrary frame `RF` carried across every back edge by
the framed label context:

```lean
theorem lr_wps_frame (RF : IProp GF) (sbty : core_base_type)
    (head : CerbMem.PointerValue) :
    iprop(isList (GF := GF) head ns ∗ RF) ⊢
      wps (procCtx rs) (procCtl p) (frameLs RF (lrLs ns))
        (fun w ρ' => iprop(lrPost ns w ρ' ∗ RF))
        (lrProg loc ann ra mo sbty pbty cbty bbty nbty ubty head)
        [fmapEmpty] := by
  iintro ⟨HL, HF⟩
  ihave HW := lr_wps loc ann ra mo pbty cbty bbty nbty ubty ns p rs hQ sbty head $$ HL
  iapply wps_frame_labels RF _ _ $$ HW HF
```

Section variables not shown: `{hlc : HasLC} {GF : BundledGFunctors}
[SpikeGS hlc GF]`, `loc ann ra mo`, `pbty cbty bbty nbty ubty`, `ns`,
and — the load-bearing one — `(p : sym) (rs : core_run_state) (hQ :
LabeledAt rs p (lrQ loc ann ra mo pbty cbty bbty nbty ubty))`: the
triple holds at the machine context `procCtx rs`, entry control `procCtl
p`, whose label table is the loop's (`procCtx_labels hQ`), which is what
lets `wps_run` resolve
the jump. Read: `{ isList head ns ∗ RF } reverse { ret p'. isList p'
ns.reverse ∗ RF }`. The unframed proof `lr_wps` is textbook — invariant
`isList prev reversed ∗ isList cur rest` (`lrLs`), each construct
discharged by its own rule, `wps_run` at the back edge asking only for
the label's precondition, `blockSpecs_intro` assembling the registered
body's specification — and the frame is `wps_frame_labels` applied
once. `wps_sound_frame` collapses to the raw WP and `engine_adequacy`
lands the loop statement; `lrProd_wpt` proves the build-and-reverse
program at the total judgment and `wpt_driver_done_alloc` →
`prod_run_eqJ` supply the pipeline.

### 1.3 What "the engine" is in each statement

ONE execution function appears in exported statements, the shipped
Cerberus driver, in two forms. In the loop statements — `MemTriple`,
`MemTriple_alloc`, `SemTriple`, every `*_certified`, `*_engine`,
`*_semantic` — it is the driver's own per-thread loop
`drive_nonmemory_steps_aux2_lemFuel` (Driver.lean:346; the shipped
`drive_nonmemory_steps_aux2` is its instance at `CerbFuel.driverFuel`,
`CerbND.drive_nonmemory_steps_aux2_wrapper_defeq`), applied by `runOne`
to any driver state holding the configuration (`DriverSafeCtl`, §1.1),
at EVERY fuel. In the closed statements — `exhibitA_prod`,
`*_production`, and the partial `fib_rec_certified` — it is the shipped
pipeline `CerbND.runND (drive fmapEmpty false file args)
(initial_driver_state sup file fs).1`: for the total statements at the
shipped `drive`, for the partial one at every `fuel` of the semantics'
fuel-parametric mirror `CerbND.drive_lemFuel fuel` (`drive` is its
instance at `CerbFuel.driverFuel`, `CerbND.drive_wrapper_defeq`, `rfl`;
the mirror is produced upstream by copying the generated `drive` with its
one `driver2` call fuel-parameterized, and its sync with the generated
text is that `rfl`). Both lanes are proved by iterating the same shipped
round, `loop_step_frag` (DriverCollapse.lean): one iteration of the
production scheduler at a single-threaded fragment configuration is one
mirror step, stated at the LIVE control — the mirror's `ctl` is the
driver thread's `stack0`/`current_proc_opt`/`exec_loc`, call and return
rounds included — wherever the mirror `Step` steps; the total lane by
induction on the judgment's budget (`wpt_driver_aux`, `wpt_driver_cps` →
`prod_run_eqJ`, `prod_run_eqJ_procs`), the partial lane by induction on
the loop's fuel (`drive_safe_aux` → `engine_adequacy` →
`prod_run_safe_procs`), `NotStuck` supplying the mirror step at every
reachable configuration. Exhaustion is classified, not excluded: the
loop's out-of-fuel arm is the kernel-transparent kill
`CerbND.fuelExhaustedKill` (the cerberus-lean fuel arc, pin `f95ef8d9c`:
`CerbND.driver2_lemFuel_zero` and its ND-typed siblings, all `rfl`; the
drive cone's budget the citable `CerbFuel.driverFuel = 10^8`), so the
partial statements say "exhaustion or the postcondition" at every fuel
and the total ones deliver within `k + 2 ≤ CerbFuel.driverFuel`
iterations. MEASURED at the pin (`2026-09-03_f1-notes.md` §3):
`drive_lemFuel`'s `fuel` bounds the OUTER `driver2` rounds only —
`new_drive_core_threads` (Driver.lean:355) calls the per-thread loop
through its wrapper at the fixed budget — so at every `fuel ≥ 1` the
closed partial statement is the one about the shipped `drive`, and the
"however long the run" content lives in the loop-level `DriverSafeCtl`
(∀ `fl`).

**The two lanes, both on the shipped driver.** Every exported execution
theorem reaches the shipped engine; every public logical rule has a
kernel-checked adequacy path through the package mirror to the engine.
The nine production statements (`exhibitA_prod`,
`fib_certified_production`, `counter_loop_certified_production`,
`list_reverse_certified_production`,
`dispose_list_certified_production`,
`region_loop_certified_production`,
`malloc_list_certified_production`, `fib_rec_certified_production`) are
THE ROOT-OF-TRUST exports — the closed shipped-driver statements: the
genuine Cerberus driver, and nothing package-defined in the statement but
the authored program, its `prodFile`/`prodFileWith` wrapper, the pure
readout predicates, and — where the program allocates from a
size-dependent budget — the BUDGET side condition that the budget fits
the cold start, in the package's pure vocabulary for
`region_loop_certified_production` (`hB : n.toNat * regionCost al sz ≤
headroom prodMem₀.lastAddress`: its cost function, its headroom function,
its cold-start literal; with `hfuel : 7 * n.toNat + 5 ≤
CerbFuel.driverFuel`; a finding of the K4 range audit, disclosed) and in
ENGINE vocabulary for `malloc_list_certified_production` (`hB : n.toNat *
(15 + max al.toNat 1) ≤ 281474976710647`, with `hfuel : 25 * n.toNat + 9
≤ CerbFuel.driverFuel`) — never a driver, discharge or scheduler.
`prod_run_eqJ`/`prod_run_eqJ_procs` and the partial `prod_run_safe_procs`,
through which they are proved, are generic collapse machinery, not
closed statements: their delivery premises `DriverDoneAt`/`DriverDoneCtl`
resp. the driver-safety fact `DriverSafeCtl` and their registration ties
`LabeledAt`/`LabeledProcs` are package-defined, discharged by each
client. The partial closed statement `fib_rec_certified` — every `n ≥ 0`,
no budget bound, at every `drive_lemFuel` fuel — sits beside the nine, as does
`even_odd_certified` (EvenOddExhibit.lean, mutual recursion; H1b 2026-09-04).
The generic partial exports — `MemTriple`, `MemTriple_alloc`,
`SemTriple`, `project_triple`, `project_triple_pure`,
`project_triple_alloc`, `project_triple_pure_alloc`,
`semantic_triple_sound`, `semantic_frame`, `engine_adequacy`,
`engine_adequacy_alloc`, the two lemmas over those triples
(`SemTriple_iff_Mem`, `MemTriple_alloc_of_MemTriple`), and every exhibit
the README's table lists at the shipped loop — are loop-level facts:
every driver state holding the configuration, every fuel. Two honest
limits (README, "Registered divergences and limitations"): the seeded
exhibits (pre-seeded cells) have no cold-start form, and the straight-line
exhibits sit at the profile `spikeCtx`/`spikeCtl` — no current procedure,
a thread state the shipped driver never parks `main` in — admitted by the
loop-level fact because the shipped round needs the current procedure's
registration tie only at a jump (`loop_step_frag'`, `CtlTied.noproc`).
Until the fuel-lane restatement (2026-09-03) the partial lane was stated
over a package loop (`driveU`) around the engine's `step_ctx` and carried
an interim label; the request
(`../../docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md`)
asked the cerberus-lean team for a transparent, distinguished
fuel-exhaustion outcome in the driver monad; it landed (cerberus-lean
`f95ef8d9c`, `CerbND.fuelExhaustedKill`, `CerbND.drive_lemFuel`), is the
pinned semantics since 2026-09-03, and the package loop was deleted
with the restatement; no package-side driver was ever written to work
around the formerly opaque one.

## 2. The readout predicates

The trust claims, the differential-validation record, the Cerberus
configuration the statements pin, and the chain of theorems from the
engine to the exports are the README's "The trust story" and its trust
diagram. `Step`, the rules, the judgments and iris-lean are interior —
they occur in proofs, never in an exported conclusion — so a bug there
deprives us of proofs, not of the truth of what was proved. That is
relative to the readout predicates: a wrong `DriverSafeCtl`, `ctlThread`,
`CtlTied` or `Sat` would make a theorem true but about the wrong thing,
which is why they are printed here in full. `DriverSafeCtl` is printed in
§1.1; its driver-side vocabulary (DriverCollapse.lean):

```lean
def ctlThread (th₀ : thread_state) (e : CoreExpr) (ρ : EnvStack) (ctl : Ctl) : thread_state :=
  { th₀ with
    arena := e
    env := ρ
    stack0 := ctl.toStack
    current_proc_opt := ctl.proc
    exec_loc := ctl.execLoc }
```

```lean
def LabeledProcs (M₀ : MachineCtx) (lab : Fmap sym LabelMap) : Prop :=
  ∀ f params body, lookupProc M₀.file M₀.extern f = some (params, body) →
    fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2) f lab =
      some (M₀.labelsAt (some f))
```

```lean
def CtlTied (M₀ : MachineCtx) (lab : Fmap sym LabelMap) (ctl : Ctl) : Prop :=
  (∀ p, ctl.proc = some p →
    fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2) p lab =
      some (M₀.labelsAt (some p))) ∧
  ∀ pc ∈ ctl.κ, ∀ p, pc.1 = some p →
    fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2) p lab =
      some (M₀.labelsAt (some p))
```

`ctlThread` is the driver's own `thread_state` holding the
configuration: the arena, the env and the three control fields the
engine's PCALL/RETURN arms write (`stack0`, `current_proc_opt`,
`exec_loc`), over `th₀`'s `errno` and `current_loc`. `LabeledProcs` ties
the driver's run state to the context at every DECLARED procedure (what
`call_proc` reads), `CtlTied` at the current procedure and every
procedure saved on the call stack (what the jump reads,
`MachineCtx.labelsAt` — the engine's own two-level `labeled` lookup at
the extern-resolved current procedure); at a control with no current
procedure and an empty stack both are vacuous. `runOne` (Step.lean) is
`ndM`'s one-layer eliminator `match m with | ND f => f s`;
`drive_nonmemory_steps_aux2_lemFuel` is the generated driver's loop, not
a package definition. The footprint predicates:The footprint predicates:

```lean
structure Coh (tds : CerbTags.TagDefsMap) (σ : Mem) (m : SpikeHeapF SpikeCell) : Prop where
  cells : ∀ id c, get? m id = some c → CellCoh tds σ id c
  disj : ∀ id1 id2 c1 c2, id1 ≠ id2 → get? m id1 = some c1 →
    get? m id2 = some c2 → cellsDisjoint tds c1 c2
```

```lean
abbrev Sat (tds : CerbTags.TagDefsMap) (σ : Mem) (m : CellMap) : Prop := Coh tds σ m
```

A `SpikeCell` is `⟨addr, ty, bytes⟩`; `cellPtr id a` is the engine
pointer value `.PV (.Prov_some id) (.PVconcrete none a)`. `CellCoh tds σ
id c` (Heap.lean, six fields): allocation `id` is not dead; the
allocation table has it at base `c.addr`, size `sizeofCtype tds c.ty`,
type `c.ty`, writable; the type is non-atomic; `c.bytes` has that length
and `readBytesFrom σ c.addr … = c.bytes`; and the image decodes the same
at any union-member/function-pointer side tables (`dec_indep`).
`SeedChain m p ns` (ListRevExhibit.lean) is the pure image of `isList`:
one 16-byte `nodeTy` cell per node at the node's allocation id, whose
bytes decode by the engine's decoder to the node's value and the next
pointer. The only non-engine vocabulary in the exported statements is
these definitions, the authored programs, and iris-lean's finite-map
library (`Iris.Std.PartialMap.get?`/`union`/`##ₘ`).

## 3. The logic

Two label-context judgments over iris-lean's `WP` — the partial `wps`
and the total `wpt` — for programs with `save`/`run`, and beneath them
the small axioms at the raw `WP` over the runtime tuple `⟨e, ρ, M⟩ :
CoreRt` (expression, live environment stack, machine context), generic
in `M` and `ρ`. Frame, consequence and sequencing are stated at the
judgments: at the raw WP sequencing is false once labels are populated
— a jump discards the sequencing context.

### 3.1 The small axioms

```lean
theorem wp_store [SpikeGS hlc GF] {s : Stuckness} {E : CoPset} {M : MachineCtx}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (cv : value) (mo : memory_order)
    (mv : CerbMem.MemValue) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv = some mv)
    (hst : StorableAt M.tagDefs ty mv) :
    pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs ⊢
      WP (⟨storeExpr loc ann ty pv cv mo, ρ, M⟩ : CoreRt) @ s; E
        {{ w, ∃ fp, ⌜w = (⟨SpikeVal.annot [DA_pos [] fp] Vunit, ρ, M⟩ : CoreRVal)⌝ ∗
            pointsToCell M.tagDefs pv (.own 1) ty (CerbMem.memValueToBytes M.tagDefs [] mv).2 }} := by
```

Section variables not shown: `{hlc : HasLC} {GF : BundledGFunctors}`.
The classic `{p ↦ (ty, bs)} store(ty, p, v) {p ↦ (ty, bytes-of v)}`:
full ownership of the cell entails the WP of the store, whose post
returns the cell with its bytes replaced by the engine's own
serialization of `v` (`memValueToBytes`). Two deviations from the
textbook shape, both forced by the engine: the returned value is the
annotated unit `SpikeVal.annot [DA_pos [] fp] Vunit` (the engine's
continuation wraps the result in a dynamic annotation carrying the
footprint; `wps_store_plain`/`wpt_store_plain` hide it), and the typing
premises `hmv`/`hst`. It is a small axiom in the original sense: it
mentions only the cell the store touches.

**What "storable" means.** `hmv` says the Core value `cv` converts to a
memory value `mv` at the (non-atomic) type `ty` by the engine's own
`memValueFromValue`. `StorableAt M.tagDefs ty mv` (Heap.lean) has five
fields, each defeating one arm of the engine's store path:

- `compat : ctypeMemCompatible ty (typeofMval mv) = true` — excludes
  `storeM`'s non-UB kill "store with an ill-typed memory value"
  (`MerrOther`), checked before the pointer is examined;
- `fpm : ∀ fpm, (memValueToBytes tds fpm mv).1 = fpm` — serialization
  adds no function-pointer-table entries (`storeM` threads the table);
- `len : ∀ fpm, ((memValueToBytes tds fpm mv).2).length = sizeofCtype
  tds ty` — the image fills the cell's footprint exactly, so the cell
  can be re-read and neighbours are untouched;
- `bytes_fpm : ∀ fpm, (memValueToBytes tds fpm mv).2 = (memValueToBytes
  tds [] mv).2` — the image is independent of the state's current
  function-pointer table, at which `storeM` serializes;
- `stored_dec : ∀ lum fpm addr, reconstructValue tds lum fpm addr ty
  (memValueToBytes tds [] mv).2 = reconstructValue tds [] [] addr ty
  (memValueToBytes tds [] mv).2` — the stored image decodes
  independently of the union-member and function-pointer side tables,
  re-establishing the cell's `CellCoh.dec_indep` (§2).

All five are closed computations for scalar values (`rfl`). The typed
subrange rules (`wps_store_at`, `wps_store_cell_at`) take the four-field
face `StorableView` (`StorableAt.toView` forgets `stored_dec`). This is
the value-typing judgment of a type system in embryo. The load,
`wp_load`, is the same shape at any fraction `dq`, delivering the
engine's own decode of the cell (`loadedVal`) under `(htrap :
cellLoadTrap M.tagDefs ⟨addrOf pv, ty, bs⟩ = false)`, which excludes the
`_Bool` trap-representation kill — the one `loadM` failure ownership
alone cannot rule out.

**Proved once.** Both are corollaries of the mask-generic atomic step
specification (Rules.lean):

```lean
def AtomicStep [SpikeGS hlc GF] (M : MachineCtx) (e : CoreExpr) (ρ : EnvStack)
    (c : Nat) (P : IProp GF) (Q : SpikeVal → IProp GF) : Prop :=
  ∀ (E₁ E₂ : CoPset), E₂ ⊆ E₁ →
  ∀ (σ₁ : Mem) (ns : Nat) (obs : List Empty) (nt : Nat),
    iprop(P ∗ stateInterp σ₁ ns obs nt) ⊢
      iprop(|={E₁,E₂}=> (⌜PrimStep.Reducible ((⟨e, ρ, M⟩ : CoreRt), σ₁)⌝ ∗
        ∀ (r : CoreRt) (σ₂ : Mem) (eₜ : List CoreRt),
          ⌜((⟨e, ρ, M⟩ : CoreRt), σ₁) -<([] : List Empty)>-> (r, σ₂, eₜ)⌝ -∗
          |={E₂,E₁}=> (stateInterp σ₂ (ns + 1) obs nt ∗
            ∃ w : SpikeVal, ⌜r = (⟨ofVal w, ρ, M⟩ : CoreRt) ∧ eₜ = [] ∧
              deliveryCost w ≤ c⌝ ∗ Q w)))
```

Six specifications are proved directly against `Step`, each running the
real engine function inside the proof: `store_atomic`
(`storeM_success`), `load_atomic` (`loadM_success`),
`storeAt_atomic`/`loadAt_atomic` (typed subranges,
`storeM_at`/`loadM_at`), `create_atomic` (`allocateObject_success`),
`kill_atomic` (`killM_success` — the static dispose, kill/free arc K2;
§4, "The dispose rule").
Three lifting lemmas turn a specification into a rule: `wp_of_atomic`
(the raw WP, any stuckness and mask), `wps_of_atomic` (the partial
judgment; premise: the redex is not a jump), `wpt_of_atomic` (the total
judgment, at budget `c + 1 ≤ k`). Every memory rule of every judgment is
a corollary of one of the five.

**Program variables are not heap.** The Core environment `ρ :
EnvStack` — the engine's `thread_state.env`, a stack of frames `Fmap
sym value` — is a parameter of the judgments, not part of the assertion
language: Core's `let`-bindings are immutable, so there is nothing to
own. Consequently the conditional rule `wps_if` carries the guard's
verdict as a pure premise, `⌜evalPexpr M.tagDefs M.extern ρ g = some
(boolValue b)⌝ ∗ wps M Ls Ψ (bif b then e2 else e3) ρ ⊢ wps M Ls Ψ (Expr
a (Eif g e2 e3)) ρ` — the classical two-premise rule is a case split on
`b` outside the logic. What the logic knows about frames is `SymFrame`
(EnvLaws.lean: a frame reachable by the engine's `update_env` chains)
and the lookup law `envAdd_lookup`, so an invariant states "the frame
binds `x` to `v`" without pinning the frame's shape. One more
environment-side premise appears on a client (`struct_create_store_wps`):
`∀ x, resolveExtern M.extern x = x`. The engine resolves every `PEsym`
through the file's extern map with identity fallback (`resolveExtern`,
Step.lean, the evaluator's `PEsym` arm and `step_ctx`'s `Erun` arm), so
the premise says the program's symbols are not extern-redirected; at
`fmapEmpty` it is `rfl` (`resolveExtern_id_of_empty`).

### 3.2 Frame, consequence, allocation

At the raw WP the frame is iris-lean's own `wp_frame_r` and consequence
its `wp_mono`/`wp_wand`; the logic states them at the judgments, where
the frame must also cross back edges — which framing the label context
achieves:

```lean
abbrev frameLs (R : IProp GF) (Ls : LabelSpec GF) : LabelSpec GF :=
  fun l vs ρ => iprop(Ls l vs ρ ∗ R)
```

```lean
theorem wps_frame_labels {Ψ : SpikeVal → EnvStack → IProp GF} (R : IProp GF)
    (e : CoreExpr) (ρ : EnvStack) :
    wps M Ls Ψ e ρ ⊢
      iprop(R -∗ wps M (frameLs R Ls) (fun w ρ' => iprop(Ψ w ρ' ∗ R)) e ρ) := by
```

Section variables not shown (the same for every `wps_*` rule quoted
here): `{hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF] {M :
MachineCtx} {Ls : LabelSpec GF}`. Value exit: the frame joins the
postcondition; jump: it joins the label's precondition; step: Löb.
`wps_sound_frame` is the derived whole-loop form;
`wpt_frame_labels`/`frameLsT` are the total analogues (budget induction,
no Löb). Consequence: `wps_wand`, `wps_fupd`; `wpt_mono`, `wpt_mono_k`,
`wpt_mono_Ls`. Allocation:

```lean
theorem wps_create {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (aprov : CerbMem.Provenance) (alignN : Int) (ty : ctype)
    (pref : prefix0) (ρ : EnvStack)
    (hsz : 0 < CerbMem.sizeofCtype M.tagDefs ty) (hatom : atomicTy ty = false)
    (hinert : ∀ a : Int, decIndep M.tagDefs a ty
      (List.replicate (CerbMem.sizeofCtype M.tagDefs ty) undefByte)) :
    iprop(allocBudget (GF := GF) (allocCost M.tagDefs ty alignN) ∗
      (∀ p : CerbMem.PointerValue,
        (pointsToCell M.tagDefs p (.own 1) ty
            (List.replicate (CerbMem.sizeofCtype M.tagDefs ty) undefByte) ∗
          ⌜0 < addrOf p ∧ addrOf p < 2 ^ 64⌝) -∗
        Ψ (SpikeVal.pure (Vobject (OVpointer p))) ρ)) ⊢
      wps M Ls Ψ (createExpr loc ann (.IV aprov alignN) ty pref) ρ := by
```

The budget `allocCost ty alignN = sizeof ty + max(alignN, 1) − 1` buys
one `create` of `ty` at alignment `alignN` and is spent; the
continuation receives an existential fresh pointer with full whole-cell
ownership at the unspecified byte image and the pointer's
machine-address bounds. `hsz`: a real object type (positive size);
`hatom`: a non-atomic type; `hinert`: the unspecified image decodes
independently of the side tables (`rfl` for the exhibits' types).
Nothing in the statement names the allocator's cursor. `allocBudget` is
a genuine separation-logic resource — `allocBudget (a + b) ⊣⊢
allocBudget a ∗ allocBudget b` (`allocBudget_split`), so two components
can each own part of the capacity and allocate independently, in any
order; `wps_create_of_plan` is the plan-shaped reading (capacity for
`req :: rest` buys the head and returns capacity for the rest), derived
by the split law. `wpt_create` is the same at the total judgment with
the cost bound `2 ≤ k`. Why the budget has this cost, and what the
shape costs, is §4.

### 3.3 One loop rule, and the total judgment

The partial judgment `wps M p Ls Θ Ψ e ρ` — at the current procedure
`p : Option sym`, the label specification `Ls`, the procedure
specification table `Θ` (calls arc C3) — is a guarded fixpoint
(iris-lean's `fixpoint` over a contractive `wps.pre`) with four clauses
— value, jump redex, CALL redex, step. `Ls : LabelSpec GF` (`sym → List
value → EnvStack → IProp GF`) gives each registered label a precondition
over its argument values and the jump-time environment; `Θ : ProcSpec
GF` (`sym → List value → IProp GF × (value → IProp GF)`) gives each
procedure, per argument list, a precondition and a postcondition on the
delivered value. The jump rule `wps_run`: under `lookupLabel (M.labelsAt
p) l = some (params, cont)` and `evalPexprs M.tagDefs M.extern (ev0 ::
evs) pes = some vs`, `Ls l vs (ev0 :: evs) ⊢ wps M p Ls Θ Ψ (Expr a (Erun
ra l pes)) (ev0 :: evs)` — the label's precondition suffices and tracking
stops: a jump's postcondition is the label's business. The call rule
`wps_call_root` (the in-context form is `wps_call`): under `lookupProc
M.file M.extern f = some (params, body)`, `params.length = vs.length` and
`evalPexprs M.tagDefs M.extern ρ pes = some vs`,

```lean
    iprop((Θ f vs).1 ∗ (∀ (ret : value), (Θ f vs).2 ret -∗
        wps M p Ls Θ Ψ (Expr [] (Epure (Pexpr [] () (PEval ret)))) ρ)) ⊢
      wps M p Ls Θ Ψ (Expr a (Eproc ra (Sym f) pes)) ρ
```

— the table's precondition now, and the CALLER'S CONTINUATION at the
returned value, at the caller's own environment (RETURN pops the
callee's frame and plugs the value into the captured context; in
context the continuation is `apply_ctx ctx (pure ret)`). The loop rule
assembles the registered bodies' specifications with no Löb and no
mutual assumption:

```lean
theorem blockSpecs_intro {Ψ : SpikeVal → EnvStack → IProp GF}
    (h : ∀ l params cont vs ev0 evs,
      lookupLabel (M.labelsAt p) l = some (params, cont) →
      Ls l vs (ev0 :: evs) ⊢ wps (GF := GF) M p Ls Θ Ψ cont
        (bindArgs params vs (ev0 :: evs))) :
    ⊢ blockSpecs M p Ls Θ Ψ := by
```

and the procedure rule assembles the declared bodies' specifications the
same way — every body verified once, at every caller tail `ρ`
(`lookup_env` searches all frames, so the spec must hold for every tail;
a body whose reads are head-frame hits never sees it), ASSUMING the
table for every procedure, itself included (Hoare's rule for recursive
procedures; RefinedC's `typed_function` conjunction):

```lean
theorem procSpecs_intro (Lsₚ : sym → List value → LabelSpec GF)
    (hB : ∀ f params body vs, lookupProc M.file M.extern f = some (params, body) →
      params.length = vs.length →
      ⊢ blockSpecs (GF := GF) M (some f) (Lsₚ f vs) Θ (fun w _ => (Θ f vs).2 w.val))
    (hW : ∀ f params body vs (ρ : EnvStack),
      lookupProc M.file M.extern f = some (params, body) → params.length = vs.length →
      (Θ f vs).1 ⊢ wps (GF := GF) M (some f) (Lsₚ f vs) Θ (fun w _ => (Θ f vs).2 w.val) body
        (procEnv params vs :: ρ)) :
    ⊢ procSpecs M Θ := by
```

The one Löb induction lives in the collapse, now in CPS over the
ambient control (`wps_sound_cps`; RefinedC's `stmt_wp_def` shape):

```lean
theorem wps_sound_cps (p : Option sym) (Ls : LabelSpec GF) {Ψ : SpikeVal → EnvStack → IProp GF}
    (κ : List (Option sym × context)) (ℓ : exec_location) (e : CoreExpr) (ρ : EnvStack)
    (Φ : CoreRVal → IProp GF) :
    procSpecs M Θ ⊢
      iprop(blockSpecs M p Ls Θ Ψ -∗ wps M p Ls Θ Ψ e ρ -∗
        (∀ (ℓ' : exec_location) (w : SpikeVal) (ρ' : EnvStack), ⌜SameTail ρ ρ'⌝ -∗ Ψ w ρ' -∗
          WP (⟨ofVal w, ρ', ⟨κ, p, ℓ'⟩, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ {{ Φ }}) -∗
        WP (⟨e, ρ, ⟨κ, p, ℓ⟩, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ {{ Φ }})
```

— under the procedure and block specifications, the statement WP at any
call stack `κ` and execution location `ℓ` entails the base WP, given a
continuation `K` for the delivered value at a final env with the frames
below the head preserved (`SameTail`) and at any execution location
(RETURN does not restore it). Its call case runs the callee's body (from
`procSpecs`, at the pushed frame and control) with the continuation that
performs the RETURN (`wp_ret`/`wp_ret_annot`: the callee's final env is
`ev0' :: ρ`, so the caller's `ρ` comes back verbatim) and re-enters the
caller's continuation through the induction hypothesis — where the one
Löb and the frame stack meet. At the entry control `wps_sound`: `procSpecs
M Θ ∗ blockSpecs M ctl.proc Ls Θ Ψ ⊢ wps M ctl.proc Ls Θ Ψ e ρ -∗ WP ⟨e, ρ,
ctl, M⟩ @ NotStuck; ⊤ {{ w, Ψ w.w w.ρ }}` at `ctl.κ = []`, and at the
empty table (`wps_sound_empty`, no procedure specifications needed) the
pre-C3 statement verbatim.
This is the classical label-context treatment of `goto`-like control
(de Bruin-style label assumptions), and the reason no `wp_bind` is
needed: `Erun` discards its evaluation context, so a bind rule's frame
law is false for Core, and sequencing is proved directly (`wps_seq`,
`wps_seq_spec`, `wps_seq_sym`). One fragment premise deserves naming:
`Frag.case_value` (rule `wps_case_value`) carries `hbsz`, that the branch
`select_case` picks has `esize` bounded by the case node's. It is
carried rather than proved. The equation whose proof would discharge it
is `esize (subst_sym_expr x v e) = esize e` (with its mutual twin for
`esizeAlts`), true because `esize` inspects only expression constructors
and `subst_sym_expr` substitutes only into pure expressions; the
obstacle is that the engine's `subst_sym_expr` is `subst_sym_expr_lemFuel
lemDefaultFuel`, a fuel-indexed recursion over the whole generated Core
AST (`generic_expr`/`generic_pexpr`/patterns), so the proof is a
fuel-indexed induction over that mutual recursion — measured and not
attempted; the gap is registered (README, "Registered divergences and
limitations"). For authored programs `hbsz` is `rfl`.

**The total judgment** is defined by well-founded recursion on a step
budget (over every smaller budget — the call clause splits it), no
fixpoint, no ▷:

```lean
def wpt.pre [SpikeGS hlc GF] (M : MachineCtx) (p : Option sym) (Ls : LabelSpecT GF)
    (Θ : ProcSpecT GF) (k : Nat)
    (F : ∀ (k' : Nat), k' < k →
      (SpikeVal → EnvStack → IProp GF) → CoreExpr → EnvStack → IProp GF)
    (Ψ : SpikeVal → EnvStack → IProp GF) (e : CoreExpr) (ρ : EnvStack) :
    IProp GF :=
  match toVal e with
  | some w => iprop(⌜deliveryCost w ≤ k⌝ ∗ |={⊤}=> Ψ w ρ)
  | none =>
    match jumpRedex? e with
    | some lp =>
      iprop(|={⊤}=> ∃ (params : List (sym × core_base_type)) (cont : CoreExpr)
        (vs : List value) (ev0 : Fmap sym value) (evs : List (Fmap sym value))
        (m : Nat),
        ⌜ρ = ev0 :: evs⌝ ∗ ⌜lookupLabel (M.labelsAt p) lp.1 = some (params, cont)⌝ ∗
        ⌜evalPexprs M.tagDefs M.extern ρ lp.2 = some vs⌝ ∗
        ⌜1 + m ≤ k⌝ ∗ Ls lp.1 m vs ρ)
    | none =>
      match callRedex? e with
      | some q =>
        iprop(|={⊤}=> ∃ (params : List (sym × core_base_type)) (body : CoreExpr)
          (vs : List value) (m k' : Nat) (hb : 1 + m + k' ≤ k),
          ⌜lookupProc M.file M.extern q.2.1 = some (params, body)⌝ ∗
          ⌜params.length = vs.length⌝ ∗
          ⌜evalPexprs M.tagDefs M.extern ρ q.2.2 = some vs⌝ ∗
          (Θ q.2.1 m vs).1 ∗
          ∀ (ret : value), (Θ q.2.1 m vs).2 ret -∗
            F k' (by omega) Ψ (apply_ctx q.1 (Expr [] (Epure (Pexpr [] () (PEval ret))))) ρ)
      | none =>
        match hk : k with
        | 0 => iprop(⌜False⌝)
        | k' + 1 =>
          iprop(∀ (κ : List (Option sym × context)) (ℓ : exec_location)
            (σ₁ : Mem) (ns : Nat) (obs : List Empty) (nt : Nat),
            stateInterp σ₁ ns obs nt ={⊤,∅}=∗
            ⌜PrimStep.Reducible ((⟨e, ρ, ⟨κ, p, ℓ⟩, M⟩ : CoreRt), σ₁)⌝ ∗
            ∀ (r : CoreRt) (σ₂ : Mem) (eₜ : List CoreRt),
              ⌜((⟨e, ρ, ⟨κ, p, ℓ⟩, M⟩ : CoreRt), σ₁) -<([] : List Empty)>-> (r, σ₂, eₜ)⌝
                ={∅,⊤}=∗
              stateInterp σ₂ (ns + 1) obs nt ∗ F k' (by omega) Ψ r.e r.ρ)
```

```lean
def wpt [SpikeGS hlc GF] (M : MachineCtx) (p : Option sym) (Ls : LabelSpecT GF)
    (Θ : ProcSpecT GF) :
    Nat → (SpikeVal → EnvStack → IProp GF) → CoreExpr → EnvStack → IProp GF
  | k => wpt.pre M p Ls Θ k (fun k' _ => wpt M p Ls Θ k')
termination_by k => k
```

The call clause's budget split `1 + m + k' ≤ k` is one unit for the call
round, the callee's budget `m` (the table's index, `ProcSpecT`; the
callee's delivery cost IS its return protocol — 1 for a bare value, the
RETURN tau; 2 for an annotated one, REMOVE-ANNOT then RETURN), and the
continuation's `k'`.

Section variables not shown: `{hlc : HasLC} {GF : BundledGFunctors}`.
`LabelSpecT` preconditions carry a variant `m : Nat` (the Floyd variant
as a specification parameter), and the jump clause requires `1 + m ≤
k`: the target's budget plus the jump must fit the remaining budget.
Since a body is verified at budget `m` (`blockSpecsT`) and budgets only
shrink along steps, every back edge strictly decreases a well-founded
measure. The total jump rule is `wpt_run`, with `(hμ : 1 + m ≤ k)`; the
collapse is

```lean
theorem wpt_sound {Ψ : SpikeVal → EnvStack → IProp GF} {ctl : Ctl} (hκ : ctl.κ = [])
    (k : Nat) (e : CoreExpr) (ρ : EnvStack) :
    iprop(procSpecsT M Θ ∗ blockSpecsT M ctl.proc Ls Θ Ψ) ⊢
      iprop(wpt M ctl.proc Ls Θ k Ψ e ρ -∗
        WP (⟨e, ρ, ctl, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ [{ w, Ψ w.w w.ρ }]) := by
```

into iris-lean's `TotalWeakestPre` (`[{ … }]`) — the entry-control face
of `wpt_sound_cps`, the CPS collapse by strong induction on the budget
(a back edge lands in the target's variant budget, a call lands the
callee in `m` and the continuation in `k'`, both below `k` by the split)
— a metatheorem about the judgment (it is a sound total WP)
that no shipped-driver statement consumes (the pinned Iris-level readout
`cs_twp_readout`, `Examples/CallSmoke.lean:455`, does consume it): every
total export over the shipped driver goes through an engine
simulation directly — on the shipped driver, `wpt_driver_aux` (one
procedure) and its CPS twin `wpt_driver_cps` (ProdLoop.lean, calls arc
C4: the same induction as
`wpt_sound_cps`, concluding the pure delivery fact `DriverDoneCtl` at a
live control instead of an Iris TWP — the continuation budget ADDED, the
call case applying the hypothesis to the callee at the pushed control
and, after the RETURN round(s), to the caller's continuation; every round
the driver's own `loop_step_frag`) — and no Iris adequacy result lies in
any total export's cone. Deleting the decrease premise would let a diverging program
be derived: `diverge_total_unprovable` (DivergeExhibit.lean) records
that a total derivation for the self-jump loop is `False`, proved at the
engine — the SHIPPED loop on the self-jump exhausts at every fuel
(`dg_loop_exhausts`: each round is the self-step through the shipped
round `loop_step_frag_same`), contradicting the PROGRAM-DONE within `k +
2` iterations that `wpt_driver_done` would deliver (§5).

**What a procedure client supplies** (`FibRecExhibit.lean`, recursive
fib — calls arc C4): the procedures as a list for the synthetic file
`prodFileWith [(fib, [(n, nbty)], body)] (fib(n₀))` (ProdEntry.lean); the
production context `prodCtx file rs` at the production initial run state
`prodRS`, whose derived label fibers are computed from the shipped
registration (`collect_new_fr`, `rfl`: `fib`'s fiber holds its one `save`
label, `main`'s is empty) and whose whole-file tie `LabeledProcs` is
derived from them (`frCtx_labeledProcs`); `FragProcs` at both procedures
(`frCtx_fragProcs`); the specification tables `frSpec`/`frSpecT` —
`{⌜0 ≤ n⌝} fib(n) {ret. ⌜ret = fib n⌝}`, the total one with the budget
`fibRounds n ≤ m`; the body verified ONCE under the table, at every
caller tail (`frBody_wps`/`frBody_wpt`: the guard, the two calls by
`wps_call_root`/`wpt_call_root` — the table ASSUMED for the recursive
activations, Hoare's rule — each result bound at the plain-symbol binder
`wps_seq_sym`/`wpt_seq_sym`, the `save` of the sum, the PURE exit), the
procedure rule `procSpecs_intro`/`procSpecsT_intro`, `main` by the call
rule alone; then `engine_adequacy` at the production context and
`prod_run_safe_procs` for the partial closed statement
(`fib_rec_certified`: every `n ≥ 0`, at every `drive_lemFuel` fuel —
exhaustion or `fib n`) and, for the total production statement
(`fib_rec_certified_production`), `wpt_driver_done_procs` at the entry
control `prodCtl` → `prod_run_eqJ_procs`, with the in-budget hypothesis
`fibRounds n.toNat + 4 ≤ CerbFuel.driverFuel`.

**What a loop client supplies** (`LoopExhibit.lean`, the counter loop):
a `LabelMap` and a `core_run_state` whose `labeled` fiber at the
procedure symbol is that map (`loopQ`, `loopRS`); the machine context
`procCtx rs` (Step.lean) with the entry control `procCtl p`, whose label
table is derived from `rs` by `procCtx_labels (hQ : LabeledAt rs p Q) :
(procCtx rs).labelsAt (procCtl p).proc = Q` —
`LabeledAt` (Soundness.lean) is the engine's own lookup `fmapLookupBy
ordCompare p rs.labeled = some Q`; the Iris proof carries `hQ` as a
section `variable`, the engine face discharges it by computation
(`loopRS_labeledAt`), and the production statements derive it from the
shipped registration (`loop_labeledAt_production`, ProdEntry.lean); the
label specification (`loopLs`), the body verified once under it,
`blockSpecs_intro`, `wps_save` at entry, `wps_sound` to the raw WP; and
`engine_adequacy` (§5) — `counter_loop_certified` is exactly this
application.

## 4. The memory-model view

**What an assertion means.** Assertions are Iris propositions (`IProp
GF`) over three iris-lean `GenHeap`s — ghost state — coupled to the real
`MemState` by the invariant `CohG` inside the state interpretation. That
is Iris's resource semantics of assertions, not the Reynolds/O'Hearn
semantics of assertions as predicates on heaps. The direct
heap-predicate reading exists exactly where the projected triple exposes
it: on the precondition side the pure `Sat`/`CellCoh` (§2), from which
`project_triple_pure` mints the footprint's ghost ownership; on the
postcondition side the pure consequences of the Iris post under any
coupling witness (`hpost`). The three heaps (RefinedC's `ghost_state.v`
heap/allocs factorization is the reference): a per-byte heap, the ghost
fragment of the engine's bytemap (`bytesOwn`); a per-allocation metadata
heap (allocation id ↦ `MetaCell`: base, OPTIONAL type, size, and the
three flags `alive`, `readonly`, `dynamic` — K1), the provenance
authority — `loadM`/`storeM`/`killM` success is decided by the
allocation table, so byte content alone can never entail access success
(`metaOwn`); and a one-cell allocator-cursor heap (`lastAddress`,
`nextAllocId`, the two fields `allocateObject` reads and writes). `CohG
σ mm mb mk` couples byte cells to the bytemap, metadata cells field by
field to the allocation tables (`MetaCoh`: a live cell is a not-dead id
whose record is present and agrees on base, size, type and writability;
a dead cell is a dead id with its record erased — `killM` does both in
one update; the type is non-atomic; a dynamic cell's base is in
`dynamicAddrs`), pairwise range-disjoint, and the cursor, when present,
to the allocator fields. The two allocators' cells are named: `objCell
tds a ty alive readonly` (a `create`d object: `some ty`, layout size,
never dynamic) and `regionCell a n alive` (an `alloc`ated region:
untyped, `n` bytes, writable, dynamic). Assertions:

```lean
def cellOwn [SpikeGS hlc GF] (tds : CerbTags.TagDefsMap) (i : Int) (dq : DFrac) (c : SpikeCell) : IProp GF :=
  iprop(metaOwn i dq (metaOf tds c) ∗ bytesOwn c.addr dq c.bytes ∗
    ⌜c.bytes.length = CerbMem.sizeofCtype tds c.ty ∧
      decIndep tds c.addr c.ty c.bytes⌝)
```

```lean
def pointsToCell [SpikeGS hlc GF] (tds : CerbTags.TagDefsMap) (pv : CerbMem.PointerValue) (dq : DFrac)
    (ty : ctype) (bs : List CerbMem.AbsByte) : IProp GF :=
  iprop(∃ (id : Int) (a : Int),
    ⌜pv = cellPtr id a⌝ ∗ cellOwn tds id dq (SpikeCell.mk a ty bs))
```

`pointsToView tds id a aty off dqm dqb vty bs` owns one typed sub-range
of one allocation; `cellOwn` is the maximal view plus decode-inertness;
`pointsToCell` — written `pv ↦c[tds]{dq} ty ; bs` — is `cellOwn` at the
pointer's own provenance id and address (a real `PointerValue`, never a
bare address). Views split and join at ∗ (`pointsToView_split`/`_join`),
split by fraction for read-sharing (`pointsToView_fractional`), agree on
base and type (`pointsToView_agree`); the points-to obeys the textbook
fractional laws (`pointsToCell_fractional`, `pointsToCell_agree`,
`pointsToCell_combine`). ∗ has the right locality: byte ownership is
exclusive per absolute address, metadata ownership per allocation id
(`metaOwn_ne`), and `CohG.metas_disj` makes distinct ids range-disjoint.

**The `PtrEq` memop.** The engine's pointer comparison `eqPtrval` forks
nondeterministically on one arm — two concrete pointers with differing
provenance (a real `msum`). The mirror has no step for that arm and the
logic no rule: `Step.memop_ptreq` steps only when `applyMemM
(CerbMem.eqPtrval default pv1 pv2) σ = some (b, σ)`, and the rule
`wps_memop_ptreq` (`wpt_memop_ptreq`) asks the client for that
determinism as its premise `hres`. Comparing `cur` against `NULL` is not
a differing-provenance comparison of two concrete pointers: the null
arms fire before provenance is consulted, so `hres` is a computation
(`eqPtrval_cell_null`, `eqPtrval_null_cell`, `eqPtrval_null_null`, each
`rfl`). A comparison that could fork has no `hres` and therefore no
rule.

**The persistent stratum, and the liveness token.** Allocation
knowledge is the metadata cell at the discarded fraction (`allocMeta tds
id a aty := metaOwn id .discard (objCell tds a aty true false)`;
`locInBounds` adds the pure bound), with `Persistent` instances
(`allocMeta_persistent`, `locInBounds_persistent`); any view's metadata
fraction can be traded for it (`pointsToView_persist`). The liveness
token is the same cell's `alive` flag at the full fraction (RefinedC's
`al_alive` and `freeable`, collapsed into one cell because Cerberus
erases the allocation record on kill — there is no fact about a dead
allocation's range left to keep separately): every access bundle
carries `alive := true` (`pointsToCell_live` reads not-dead-and-present
off the coupling), and a kill will consume the cell at `.own 1` and
flip it to `false`, handing back at most the persistent DEAD cell
`deadObj tds id a ty := metaOwn id .discard (objCell tds a ty false
false)` (`deadObj_dead`: the id is in `deadAllocations`, its record
erased). Persisting is therefore final in both directions: `.own 1 ∗
.discard` is invalid, so holding `allocMeta` forecloses the kill — that
is why persistent live knowledge stays true forever — and
`deadObj_allocMeta_false` says dead and live persistent knowledge of one
id never coexist. The STATIC kill rule performs the update (K2, next
paragraph); the dynamic `free` rule performs the same update over the
region bundle (K3, "The allocation and free rules"). The bundles keep the metadata at
a fraction rather than persistent because full metadata ownership is
both the per-allocation exclusivity anchor the frame theorem needs
(`metaOwn_ne` → `bigSepM_own_disjoint`) and the thing a kill consumes.

**The dispose rule (kill/free arc K2).** `kill(static ty, p)` — Core's
`Kill (Static0 ty) pe`, C's end of automatic storage — consumes the
whole created object at full ownership and hands back the unit value
and, at most, the persistent dead cell; classically `{p ↦ -} kill(p)
{emp}`:

```lean
theorem wps_kill {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (kind : kill_kind)
    (pv : CerbMem.PointerValue) (ty : ctype) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (hstatic : is_dynamic kind = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs ∗
      ((∃ (id a : Int), ⌜pv = cellPtr id a⌝ ∗ deadObj M.tagDefs id a ty) -∗
        Ψ (SpikeVal.pure Vunit) ρ)) ⊢
      wps M Ls Ψ (killExpr loc ann kind pv) ρ
```

`wps_kill_emp` drops the dead cell (`pointsToCell … (.own 1) ty bs ∗ Ψ
(.pure Vunit) ρ ⊢ wps … (killExpr …) ρ`); `wpt_kill`/`wpt_kill_emp`
are the same at budget `2 ≤ k` (one kill step plus the bare unit's
delivery — the engine's continuation is `mk_value_e Vunit`, so unlike
store/load there is no footprint annotation and no `_plain` form is
needed); `wps_kill_eval`/`wpt_kill_eval` are the operand forms
(`kill(static ty, x)` at a symbol). All are corollaries of one atomic
specification, `kill_atomic` (Rules.lean), proved against the real
`killM` (`killM_success`, Heap.lean): the points-to's `cellPtr` shape
and the coupling put the pointer AT THE BASE of a live record of that
id, so every kill arm — null/function/other-provenance (UB179a), dead
(UB179b), the non-UB out-of-bound — is passed, and the engine checks
nothing about bytes, type or size (the `Static0 ty` payload is
discarded by `step_action`, so the kill type is unrelated to the cell's
type by design). The ghost step is the metadata update to `alive :=
false` (`metaHeap_update`, RefinedC's `alloc_alive_kill`) followed by
`metaOwn_persist`; the byte fragments are DROPPED — sound because
`killM` leaves the bytemap alone (`CohG.bytes` is about `σ.bytemap`)
and addresses are never reused (`lastAddress` only descends), so the
stale ghost bytes stay coupled (`CohG.kill`; `MemWF.kill` is the
invariant's preservation). `hstatic`: the static kill over the OBJECT
bundle — the dynamic `free(p)` is the next paragraph's rule over the
REGION bundle, and `free` of a created object is UB179a whenever its
base is not in `dynamicAddrs` — which the engine does NOT guarantee for
a created object (a zero-size region can push a created base onto
`dynamicAddrs`, the K0 range audit's scenario), so the logic takes an allocation's
origin from the metadata cell's `dynamic` flag, never from
`dynamicAddrs`. Consumers: `alloc_create_kill_wps` (AllocExhibit.lean,
§6) and THE EXHIBIT (DisposeExhibit.lean, K4): dispose-a-list over
ListRevExhibit's created nodes — `dl_wps` (`{isList head ns} dispose {ret
unit. deadNodes ns}`), `dl_wps_emp` (the textbook `{isList head ns}
dispose {emp}`), `dl_wpt` at the derived budget `12 * ns.length + 6` and
the production statement
`dispose_list_certified_production` (build two nodes with `create`s,
dispose them; two distinct allocation ids dead and erased — the proof
witnesses them as the two nodes, the statement names no node).

**The allocation and free rules (kill/free arc K3).** `alloc(al, n)` —
Core's `Alloc0`, C's `malloc` — and `free(p)` — `Kill Dynamic0` — are
the classical cons/dispose pair. `alloc` spends the budget
`regionCost al n = n.toNat + max al 1 − 1` (the region's RAW size —
`allocateRegion` pads nothing and admits `n = 0`, CerbMem.lean:1538 —
plus the alignment slack, exactly `allocCost`'s arithmetic) and
delivers an existential fresh region pointer with the whole untyped,
writable, DYNAMIC region at full ownership and its address bounds:

```lean
theorem wps_alloc {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (aprov sprov : CerbMem.Provenance) (alignN sizeN : Int)
    (pref : prefix0) (ρ : EnvStack)
    (hcost : 0 < regionCost alignN sizeN) :
    iprop(allocBudget (GF := GF) (regionCost alignN sizeN) ∗
      (∀ (id a : Int),
        (regionOwn id a sizeN.toNat (.own 1) (List.replicate sizeN.toNat undefByte) ∗
          ⌜0 < a ∧ a + (sizeN.toNat : Int) ≤ 2 ^ 64⌝) -∗
        Ψ (SpikeVal.pure (Vobject (OVpointer (cellPtr id a)))) ρ)) ⊢
      wps M Ls Ψ (allocExpr loc ann (.IV aprov alignN) (.IV sprov sizeN) pref) ρ
```

`free` consumes the region at full ownership and hands back the unit
value and, at most, the persistent dead region; classically `{p ↦
region} free(p) {emp}`:

```lean
theorem wps_free {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (kind : kill_kind)
    (id a : Int) (n : Nat) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (hdyn : is_dynamic kind = true) :
    iprop(regionOwn (GF := GF) id a n (.own 1) bs ∗
      (deadRegion id a n -∗ Ψ (SpikeVal.pure Vunit) ρ)) ⊢
      wps M Ls Ψ (killExpr loc ann kind (cellPtr id a)) ρ
```

`wps_free_emp` drops the dead region; `wpt_alloc`/`wpt_free`/
`wpt_free_emp` are the same at budget `2 ≤ k` (one step plus the bare
value's delivery — both continuations are `mk_value_e`, no footprint
annotation); `wps_alloc_eval`/`wpt_alloc_eval` are the alloc operand
forms (`alloc(al, n)` at a symbol), and the free operand form is the
kind-generic `wps_kill_eval`/`wpt_kill_eval`. Both are corollaries of
one atomic specification each — `alloc_atomic`, `free_atomic`
(Rules.lean) — proved against the real `allocateRegion`
(`allocateRegion_success`) and `killM` at `isDynamic = true`
(`killM_success_dynamic`). Three things carry the weight. (a) The
out-of-memory arm is excluded by the SAME coupling inequality as
`create`'s, now at every size: the cursor is positive (`MemWF.la_pos`,
the tenth component of the invariant — both cursor writers guard
`alignedAddr ≠ 0`), so `regionCost ≤ headroom` gives a nonzero fresh
base even for `n = 0` (`freshBase_ne_zero_of_cost'`; the K2.5 range
audit found exactly that this needs `0 < lastAddress` or `0 < size`). The
premise `0 < regionCost` is what makes the budget FORCE a cursor cell —
a zero-cost fragment (`alloc(al, 0)` at `al ≤ 1`) is the unit and
witnesses nothing; every positive size qualifies (`regionCost_pos`).
(b) `free`'s soundness spends "this allocation is dynamic" exactly once,
at `killM`'s dynamic check `!st.dynamicAddrs.contains alloc.base`
(:1573, UB179a when it fails): the region cell's `dynamic = true` is
coupled to `a ∈ dynamicAddrs` (`MetaCoh.dynamic`, `regionOwn_facts`),
crossed to the engine's Bool by `mem_contains_int`. The flag comes from
the cell `alloc` minted, never from the list (the K0 range audit's scenario). (c)
The ghost steps are `create`'s and `kill`'s: mint the region cell and
bytes, spend the budget (`CohG.alloc` re-establishes the coupling —
`MemWF.allocateRegion` inside it); flip to dead and discard
(`CohG.kill`, stated at any live cell since K2). What has NO rule, by
decision (README "Scope, exactly"): the engine-accepted STATIC kill of
a region (`kill_atomic` is over `pointsToCell`, `free_atomic` over
`regionOwn`; the fragment admits and classifies the round), `free` of a
created object, `free(NULL)`, and the zero-cost `alloc`. Also with NO
rule, by ABSENCE rather than decision (K4's finding, README "Scope,
exactly" (iv)): a load or store THROUGH a region pointer — the access
rules are over the object bundles, and `loadM_live`/`storeM_live` (the
memM seams, stated at any metadata cell) are what a region access rule
would consume. Consumers: `alloc_free_wps` (AllocExhibit.lean, §6) and
THE EXHIBIT (RegionLoopExhibit.lean, K4): `n` regions from one linear
budget — `rl_wps`/`rl_wpt` (`{allocBudget (n.toNat * regionCost al sz)}
rl(n) {emp}`, the budget the LOOP INVARIANT, split per iteration by
`allocBudget_split`, spent by `wps_alloc`, returned by `wps_free_emp`;
total at `7 * n.toNat + 3`) and `region_loop_certified_production` (under `hB : n.toNat *
regionCost al sz ≤ headroom prodMem₀.lastAddress` and `hfuel : 7 *
n.toNat + 5 ≤ CerbFuel.driverFuel`; no readout of the final table — the
regions are freed through the `_emp` faces). The rule-free absence
this paragraph named at K4 — a load or store THROUGH a region pointer —
is closed by K5, next paragraph.

**The region access rules (kill/free arc K5).** A region is untyped in
the engine (`allocateRegion` records `ty := none`) and the engine's
typed access path is TYPE-BLIND at such an allocation: `loadM`/`storeM`
check the dead list (load, CerbMem.lean:1645), the record's presence
(:1648/:1719), `isInBounds` against the record's SIZE (:1475),
writability (store, :1725) and `isAtomicMemberAccess`, which at
`alloc.ty = none` is `false` (:1619) — no effective-type check, no
alignment check. So `malloc`'d memory is read and written at ANY type at
ANY in-bounds offset, and the rules say exactly that. The TYPED REGION
VIEW is `pointsToView` at the region cell:

```lean
def typedRegionView (tds : CerbTags.TagDefsMap) (id a : Int) (n off : Nat) (dqm dqb : DFrac)
    (vty : ctype) (bs : List CerbMem.AbsByte) : IProp GF :=
  iprop(metaOwn id dqm (regionCell a n true) ∗
    ⌜off + CerbMem.sizeofCtype tds vty ≤ n ∧ bs.length = CerbMem.sizeofCtype tds vty⌝ ∗
    bytesOwn (a + (off : Int)) dqb bs)
```

with `typedRegionView_regionView` (it IS the untyped `regionView` at a
type-length image), `typedRegionView_split`/`_join` (a region as a struct
of typed fields; `pointsToView_split`/`_join` under the substitution) and
`regionOwn_carve`/`_uncarve` (a typed subrange out of / back into
whole-region ownership, the metadata whole). THE RULES are the object
rules' proofs with `regionCell a n true` for `objCell tds a aty true
false` and `n` for `sizeofCtype tds aty`, through the same seams
`loadM_live`/`storeM_live` (`alive := true`, `readonly := false`, bounds
against `n`):

```lean
theorem regionLoadAt_atomic [SpikeGS hlc GF] {M : MachineCtx}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (n off : Nat) (vty : ctype)
    (mo : memory_order) (dqm dqb : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    (hdec : ∀ lum fpm, CerbMem.reconstructValue M.tagDefs lum fpm (a + (off : Int))
      vty bs = mv)
    (htrap : loadTrapV vty mv = false) :
    AtomicStep M (loadExpr loc ann vty (cellPtr id (a + (off : Int))) mo) ρ 2
      (typedRegionView M.tagDefs (GF := GF) id a n off dqm dqb vty bs)
      (fun w => iprop(∃ fp,
        ⌜w = SpikeVal.annot [DA_pos [] fp] ((valueFromMemValue mv).2)⌝ ∗
        typedRegionView M.tagDefs id a n off dqm dqb vty bs))
```

```lean
theorem regionStoreAt_atomic [SpikeGS hlc GF] {M : MachineCtx}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (n off : Nat) (vty : ctype)
    (cv : value) (mo : memory_order) (dqm : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ vty)) cv = some mv)
    (hst : StorableView M.tagDefs vty mv) :
    AtomicStep M (storeExpr loc ann vty (cellPtr id (a + (off : Int))) cv mo) ρ 2
      (typedRegionView M.tagDefs (GF := GF) id a n off dqm (.own 1) vty bs)
      (fun w => iprop(∃ fp, ⌜w = SpikeVal.annot [DA_pos [] fp] Vunit⌝ ∗
        typedRegionView M.tagDefs id a n off dqm (.own 1) vty
          (CerbMem.memValueToBytes M.tagDefs [] mv).2))
```

Faces: `wps_load_region_at`/`wps_store_region_at` (the typed view),
`wps_load_regionOwn_at`/`wps_store_regionOwn_at` (whole-region ownership
`regionOwn`, the image spliced — carve, the typed rule, uncarve), total
twins at budget 3; the operand forms are the pointer-generic
`wps_load_eval`/`wps_store_eval`. THE EXHIBIT (MallocListExhibit.lean):
the malloc'd linked list the arc chartered — one label, two phases
(`i > 0`: `alloc(al, 16)`, `store(long, q, i)`, `store(node*,
array_shift(q, long, 1), p)`, `run ml(i − 1, q)`; `i = 0`: null test,
`load(node*, array_shift(p, long, 1))`, `free(p)`, `run ml(0, nx)`),
invariant `allocBudget (i · regionCost al 16) ∗ isRegionList p ids ∗
deadRegions done` with `i + |ids| + |done| = n` and `(ids ++ done).Nodup`;
`ml_wps`/`ml_wpt` (`{allocBudget (n.toNat * regionCost al 16)} ml(n,
NULL) {ret unit. ∃ ids, |ids| = n.toNat ∧ ids.Nodup ∗ deadRegions ids}`,
total at `25 * n.toNat + 7`) and
`malloc_list_certified_production` (under `hB : n.toNat * (15 + max
al.toNat 1) ≤ 281474976710647` — the budget fits the cold start, in
ENGINE vocabulary — and `hfuel : 25 * n.toNat + 9 ≤ CerbFuel.driverFuel`; the
final memory has `n.toNat` DISTINCT allocation ids dead and erased,
witnessed by the proof as the freed nodes). DISTINCTNESS is stated, not
implied (K5.1, the K5 range audit's finding): `deadRegion` is persistent, so
without `ids.Nodup` each of these posts would be interderivable with
"some region is dead"; the `Nodup` is discharged at every `alloc` by the
public `regionOwn_ne`/`regionOwn_deadRegion_ne` (Heap.lean — the fresh
region at `.own 1` beside every live node and beside every dead one) and
carried by the invariant through every `free` (two dead regions have no
distinctness law — both are persistent). The counter field is stored
THROUGH the region but NOT tracked by `isRegionList` (the walk never
reads it; tracking it needs the signed-long decode round trip, not in
this tree). The dead-list readout goes through the public consequence
face `deadRegion_dead` under `stateInterp_readout`; the
single-allocation faces are the public
`deadObj_readout`/`deadRegion_readout` (K5, asked for by the K4 range audit).

**Read-only allocations.** `MetaCell.readonly` is coupled to
`Allocation.isReadonly` (`LiveCoh.alloc`: `al.isReadonly = .IsWritable
↔ mc.readonly = false`); `pointsToCell` fixes `readonly := false`, and
`readonlyCell tds pv dq ty bs` is the read-only points-to (`objCell …
true true`). Loads are supported verbatim — `loadM` never consults
writability — by `load_atomic_readonly` (Rules.lean); there is NO store
rule, and the reason is stated as an engine fact rather than absorbed:
`storeM_readonly_kills` — at a live read-only cell, an in-bounds
type-compatible `storeM` is `NDkilled (failReason (MerrWriteOnReadOnly
kind) loc)` (CerbMem.lean:1724-1725; UB033/UB064 by kind). A pointer is
never both (`readonlyCell_pointsToCell_false`). Honest qualification:
nothing in this fragment MINTS a `readonlyCell` — `create` is
`allocateObject … none none`, writable (`readonlyStatusForAlloc pref
none = .IsWritable`, CerbMem.lean:1490-1492), and the launch footprint
`CellCoh` pins `.IsWritable`; the bundle is the assertion vocabulary for
`create_readonly`/string literals when those constructs join the
fragment.

**Untyped regions.** `allocateRegion` (`Alloc0`, malloc) records no
type and pushes the base onto `dynamicAddrs` (CerbMem.lean:1544/:1548);
its cell is `regionCell a n true`, and `regionOwn id a n dq bs` /
`regionView id a n off dqm dqb bs` are the untyped analogues of
`pointsToCell`/`pointsToView` — split/join at any list decomposition
(`regionView_split`/`_join`, the bound against the region's size, no
layout so no `tds`), fractional (`regionOwn_fractional`), agreeing
(`regionOwn_agree`). `regionOwn_facts` reads off the coupling exactly
what `free` needs: not dead, record present at the base with the
region's size and `ty = none`, the bytes, and `a ∈ σ.dynamicAddrs` —
the dynamic check `killM` makes (:1573). The flag is coupled in ONE
direction only (`dynamic = true → base ∈ dynamicAddrs`): the K0 range
audit's scenario (a zero-size region minted at a created object's base)
puts a created base into `dynamicAddrs`, so the converse is not an
engine invariant, and `free` of a created object is state-dependent —
the `free` rule (K3) reads dynamic-ness from the cell, never from the
list. `alloc` (K3) mints `regionOwn` at `.own 1`; `free` consumes it.
Region loads and stores go through the generic live-cell seams
`loadM_live`/`storeM_live` (any optional type; the store demanding
`readonly = false`), of which the typed `loadM_at`/`storeM_at` are the
created-object instances and K5's `regionLoadAt_atomic`/
`regionStoreAt_atomic` the region instances (§4, "The region access
rules").

**Allocation capacity, and the failure policy.** Cerberus's allocator is
a deterministic downward cursor; a `create` that cannot be placed is a
kill ("out of memory", the `alignedAddr == 0` arm of `allocateObject`,
CerbMem.lean:1513) — a killed outcome, not a value. RefinedC models
allocation failure as a deliberate `AllocFailed` divergence (and Caesium
never refuses an allocation); this package does not import that
behaviour. Instead the capacity is a resource:

```lean
def allocBudget [SpikeGS hlc GF] (n : Nat) : IProp GF :=
  iOwn (E := (SpikeGS.budgetGS (hlc := hlc) (GF := GF)).elem)
    (SpikeGS.budgetGS (hlc := hlc) (GF := GF)).name (◯ (n : Credit))
```

the fragment `◯ n` of an authoritative (ℕ, +) — iris-lean's `Auth` over
`Credit := Nat` with the constant-core `CommMonoidLike` UCMRA, the very
camera its later credits use — so `allocBudget (a + b) ⊣⊢ allocBudget a
∗ allocBudget b` is `iOwn_op` (`allocBudget_split`). The authority `●
B` sits in the state interpretation under THE COUPLING INEQUALITY `B ≤
headroom lastAddress`, `headroom la := la − 1` (`budgetInterp`; the
cursor cell's fragment lives there too since K2.5 — no client owns the
cursor). One `create` of `ty` at alignment operand `al` spends
`allocCost tds ty al := sizeof ty + max(al, 1) − 1`. THE ENGINE BOUND
behind it, verbatim from `allocateObject` (CerbMem.lean:1509-1522):
`align := alignN.toNat.max 1`, `addrAfterSize := lastAddress − size`,
`alignedAddr := alignDown addrAfterSize.toNat align` with `alignDown n a
= n / a * a`, killed iff `alignedAddr == 0`, else `lastAddress :=
alignedAddr`. Hence (i) SUCCESS: `alignedAddr ≠ 0 ↔ size + align ≤
lastAddress ↔ allocCost ≤ headroom` (`freshBase_ne_zero_of_cost`), and
(ii) CONSUMPTION: the cursor descends by `size + (lastAddress − size) %
align ≤ allocCost`, so the headroom shrinks by at most the cost
(`headroom_freshBase`). `create_atomic` (Rules.lean) is the rule: a
fragment is at most the authority (`budgetAuth_bound`), the authority is
at most the headroom, so the cost fits and the kill arm is excluded;
after the step the authority has lost exactly the cost
(`budgetAuth_consume`) and the headroom at most the cost, so the
inequality is re-established. Client statements never name
`AllocCursor`, `lastAddress`, `nextAllocId`, `freshBase` or
`cursorOwn`. Clients receive the budget from the allocation-aware
launchers (`launchResources` under `LaunchCoh tds σ m B`, whose `budget`
field is `B ≤ headroom σ.lastAddress`; `budgetAuth_grant` mints `● B ∗
◯ B` from the empty authority) and may hold more than they spend
(`allocBudget_weaken`, `allocBudget_le`).

**Freshness is global: the memory well-formedness invariant.** The
allocation-aware launch premise `LaunchCoh tds σ m B` (Adequacy.lean)
is `coh` (the footprint, `Coh`), `wf` (the global invariant `MemWF σ`,
Heap.lean) and `budget` (the budget fits the cursor's headroom). `MemWF σ` is a pure
predicate on the engine's `MemState` alone — no ghost state, no
footprint — with ten components, each an engine fact of the concrete
allocator (the section header in Heap.lean carries the `CerbMem.lean`
cites): `live_lt`/`dead_lt` (every live or dead allocation id is below
`nextAllocId`), `live_dead` (live and dead ids are disjoint), `disj`
(all live allocations are pairwise range-disjoint), `cursor_lo` (every
live base is at or above the downward cursor `lastAddress`),
`size_nonneg` (sizes are non-negative — `allocateRegion` admits
`malloc(0)`, so positivity is not an engine fact), `la_wf` (the cursor
is below `2^64`), `la_pos` (the cursor is POSITIVE — K3, raised by the
K2.5 range audit: both cursor writers set `lastAddress := alignedAddr` only
past the `alignedAddr == 0 → out of memory` guard, the engine's initial
cursor is `0xFFFFFFFFFFFF` and the production cold start's is `errnoAddr =
0xFFFFFFFFFFF8`; without it `headroom` clamps to 0 at `lastAddress ≤
0` and a zero-size region would pass the budget yet be killed), and the
dynamic-address facts `dyn_lo` (every address
in `dynamicAddrs` is at or above the cursor) and `dyn_disj` (no dynamic
address lies strictly inside a live allocation). The same predicate is
a field of the state interpretation `CohG` under cursor presence
(`CohG.wf`), so it holds at every reachable state of an
allocation-aware run (`CohG.storeRange`, `CohG.create` preserve it).
Consequence: a `create` is fresh from EVERY live allocation of the
state, tracked by the logic or not — `create_fresh_global`: under
`MemWF σ` at `allocateObject_success`'s guards, the minted id is
neither live nor dead and the minted range ends at or below the base of
every live allocation. The production cold-start state satisfies the
invariant (`prodMem₀_memWF`: one allocation, `errno`, at the cursor;
nothing dead; no dynamic address), which is what `prodMem₀_launchCoh`
now supplies. Preservation by the fragment's memory operations is
proved for every active outcome — `MemWF.loadM`, `MemWF.storeM` (either
locking mode), `MemWF.allocateObject` (any initializer), `MemWF.killM`
(K2, both arms), and `MemWF.allocateRegion` (K3 — the last stated
obligation; every memory operation of the fragment now has its
preservation theorem, so acceptance goal 3 is closed). Two
honest qualifications.
(i) The cursor-free launches (`MetaByteOf.cohG`, from `Coh` alone) have
no `MemWF` premise: a non-allocating program owes nothing, and the
non-allocating exports' texts are unchanged — the invariant is carried
exactly where the allocator model is exercised. (ii) The dynamic-address
component is what the engine maintains, not the stronger "every dynamic
address is the base of a live allocation": `killM` never removes an
address from `dynamicAddrs` (it erases the record and marks the id dead,
CerbMem.lean:1576-1578), so after `alloc; free` the address remains.

**Why an additive budget, and what it costs (the design record of the
exact face).** Until K2.5 the capacity was an ORDERED PLAN — `allocCap
reqs := ∃ c, cursorOwn c ∗ ⌜PlanFits tds c reqs ∧ c.lastAddr ≤ 2^64⌝`,
the client owning the exclusive cursor cell with a proof that the
request list, run in order through the engine's own cursor update,
never hits the kill arm. It was exact (each fresh address is a function
of the exact sequence of preceding requests, and the plan tracked it)
but it was not a separation-logic resource: it could not be split
across ∗, it was weakened only to a prefix, and every allocating
specification threaded `rest` in order — so an allocating callee's
precondition could never be a prefix of its caller's plan. The budget
replaces it (the record: docs/2026-09-03_k2.5-notes.md). What changed
underneath: the authority moved from an exclusive `GenHeap` cell owned
by the client to an authoritative sum `● B` owned by the state
interpretation (the cursor cell stays, as the exact tracker `CohG.cursor`
and `MemWF.cursor_lo` need; its fragment is held by the interpretation),
and the coupling became an inequality, `B ≤ headroom lastAddress`. What
it costs, stated plainly: `allocCost` is the tightest ORDER-FREE bound,
conservative by up to `align − 1` bytes per allocation — a plan can fit
where the summed costs exceed the headroom (cursor 32, requests 16 bytes
at 16 then 8 at 8: the plan runs 32 → 16 → 8, the costs sum to 31 + 15 =
46 > 31), so the plan-launched and budget-launched statements are NOT
interderivable at the launch; a budget that fits never over-promises
(`freshBase_ne_zero_of_cost`). At any realistic cursor the slack is
irrelevant (the cold-start headroom is `2^48 − 9`); what is bought is the
classical shape — `allocBudget (a + b) ⊣⊢ allocBudget a ∗ allocBudget
b`, `{allocBudget (allocCost ty al)} create(al, ty) {∃ p. p ↦ −}`, and a
callee's precondition that is simply its own budget. The rule-level
direction IS derivable, up to one explicit premise:
`wps_create_of_plan`/`wpt_create_of_plan` are the former `allocCap (req
:: rest)` statements with the plan read as `allocBudget (planCost
reqs)`, proved from `wps_create`/`wpt_create` by the split law — under
the extra premise `hsz : 0 < sizeof req.ty`, which the old statement did
not carry explicitly because `PlanFits` implied it (its `advanceCursor`
guard); the literal old statement is not derivable as such, `allocCap`
being deleted. RefinedC offers no tiebreaker here (Caesium never
refuses an allocation).

## 5. The engine attachment

`Step M : Config → Config → Prop` with `Config := CoreExpr × EnvStack ×
Ctl × Mem` (Step.lean; the live control `Ctl` = call stack, current
procedure, execution location — written by exactly two rules, the call
and the return, calls arc C2) is a hand-written small-step relation over the engine's
generated types, each rule with a citation into the engine in its
docstring; it has zero authority. iris-lean runs it:

```lean
instance : Language CoreRt Mem Empty CoreRVal where
  primStep := fun p _obs q =>
    Step p.1.M (p.1.e, p.1.ρ, p.2) (q.1.e, q.1.ρ, q.2.1) ∧
      q.1.M = p.1.M ∧ q.2.2 = []
  toVal := toValRt
  ofVal := ofValRt
```

(the four laws elided): no observations, no forks, the machine context
pinned across steps; deliberately no `Language.Context` instance (§3.3).
`CerberusRound M c c'` (Round.lean) is ONE ITERATION OF THE SHIPPED
DRIVER'S THREAD LOOP, stated in the driver's own vocabulary: at every
driver state that embeds the context and the configuration
(`MachineCtx.Embeds` — the single thread `M.tid` holds `M.thread c.1
c.2.1 c.2.2.1` (arena, env, and the three control fields from the
configuration's `Ctl`), the memory is `c.2.2.2`, the file, extern map and run state are
`M`'s), the engine's step list read by the loop body is a singleton `s`,
`s` is advanceable, and the shipped `advance_step` on it is one active,
wakeup-free transition to the state embedding `c'`:

```lean
def CerberusRound (M : MachineCtx) (c c' : Config) : Prop :=
  ∀ dst : driver_state, M.Embeds dst c →
    ∃ s : core_step2,
      step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
        (M.parent, M.thread c.1 c.2.1 c.2.2.1) = [s] ∧
      can_advance s = true ∧
      ∃ (rs' : core_run_state) (tr : List trace_event) (ctr : Nat),
        rs'.labeled = dst.core_run_state0.labeled ∧
        runOne (advance_step M.tagDefs M.tid s) dst =
          (NDactive NOWAKEUP,
           { dst with
              core_state0 := update_thread_state M.tid (M.thread c'.1 c'.2.1) dst.core_state0,
              layout_state := c'.2.2,
              core_run_state0 := rs', trace := tr, dr_step_counter := ctr })
```

Every constant here is the engine's (`step_ctx`, `can_advance`,
`advance_step`, `update_thread_state`, the `ndM` types) or
context/embedding plumbing; `runOne` is the `ND` constructor's
eliminator (`match m with | ND f => f s` — the operation `nd_bind`
itself performs on its left argument), not a semantic definition. The
round has no fuel dependency: it is stated at the loop BODY, and its
loop-level reading `CerberusRound.loop_step` — `runOne
(drive_nonmemory_steps_aux2_lemFuel (fl+1) …) dst = runOne
(drive_nonmemory_steps_aux2_lemFuel fl …) dst'` — holds for every `fl`
(the same shipped continuation on both sides; no fuel-zero arm is ever
evaluated). The hand-written discharge `dischargeStep`/`outcomesU`
(Soundness.lean) is a PROOF DEVICE of this classification: no EXPORT's
statement mentions it — the lemmas that do (`stepDischarge_run` and its
siblings) are proof devices, unpinned and internal, bounded by the package
sweep but not exported (the trust rule of 2026-09-02); since the fuel-lane
restatement (2026-09-03) no adequacy lane consumes them — both lanes
iterate the shipped round `loop_step_frag` (the former unified step-match
`outcomesU_of_step` was deleted 2026-09-04, consumerless).

The certification theorem, on the fragment `Frag` at a cons-shaped
environment and `esize e ≤ lemDefaultFuel`:

```lean
theorem engine_step_matchU {M : MachineCtx}
    {e e' : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    {ρ' : EnvStack} {ctl ctl' : Ctl} {σ σ' : Mem}
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel)
    (hs : Step M (e, ev0 :: evs, ctl, σ) (e', ρ', ctl', σ')) :
    CerberusRound M (e, ev0 :: evs, ctl, σ) (e', ρ', ctl', σ') := by
```

Note the successor thread `M.thread e' ρ' ctl'`: the engine's successor
carries `M`'s immutable fields, `current_loc` included — which is why
the fragment is annotation-free (§7) — and the successor CONTROL: the
call round pushes the frame, the return round pops it, every other
round threads it (`Step.ctl_cases`; calls arc C2).
`cerberusRound_classify` (plus `hwf : M.SeqWF` and the empty-stack
control `hκ : ctl.κ = []`) sorts every `Frag` configuration into `value_done` (a
bare value; the engine's step list is PROGRAM-DONE, `[Step_done2 v]`),
`value_annot` (an annotated value; the round is the REMOVE-ANNOT tau to
the bare value, which the mirror's value protocol does not step — why a
global iff is the wrong shape), `step` (the mirror steps, and for every
`c''`, `Step M c c'' ↔ CerberusRound M c c''`), or `refused` (the mirror
is stuck at a non-value). Adequacy needs only the value and `step`
arms: the WP's `NotStuck` supplies a mirror step at every reachable
configuration, and there the shipped driver agrees exactly.

**What the certification is, precisely.** `engine_step_matchU` is
ONE-DIRECTIONAL: mirror step ⇒ shipped round. `step_iff_cerberusRound`
is two-sided under the hypothesis `∃ c', Step M c c'`. The completeness
direction is `frag_round_complete` (Round.lean): at every non-value
`Frag` configuration, the mirror steps, or the shipped round is a
classified refusal, or the configuration is in the two-arm residual:

```lean
theorem frag_round_complete {M : MachineCtx}
    {e : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {σ : Mem}
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel) (hnv : toVal e = none) :
    RoundComplete M (e, ev0 :: evs, ctl, σ)
-- i.e. (∃ c', Step M c c') ∨ ShippedRefusal M c ∨ OpenRound M c at c := (e, ev0 :: evs, ctl, σ)
```

The refusal vocabulary `ShippedRefusal` is the shipped driver's own:
ILLTYPED (the step list is `[Step_error2 msg]`), ILLTYPED AT DISTANCE
ONE (`error_next`: a successful round `CerberusRound M c c'` into a
configuration whose next step list is `[Step_error2 msg]` — the
load/store ACTION_EVAL at a non-pointer value), KILL (the shipped
`advance_step` returns `NDkilled r` for an engine `kill_reason` — the
memory kills arrive through `liftMem`'s `DErr_memory`, the pure
evaluator's exceptions through `liftCore_run` as `Other (DErr_core_run
err)`), FORK (the shipped runner `CerbND.runND` delivers at least two
executions — `eqPtrval`'s differing-provenance `msum`), PANIC (the
redex's monad, the successor's environment head, or the jump's
label-lookup key IS the engine's own `failwithI msg` — LemLib's opaque
rendering of OCaml `failwith`). One lemma per redex root carries the
classification (`complete_store`: ILLTYPED or `storeM`'s kill;
`complete_load`/`_create`: the memory kill; `complete_case`: the no-match
report; `complete_if`: the non-boolean-guard panic, or the evaluator's
kill; `complete_run`: the unregistered-label panic, or the evaluator's
kill at a zipped argument; `complete_run_noproc`: the no-current-
procedure panic; `complete_beta_spec`: the binding panic at a
non-`Specified` value; `complete_load_op`/`_store_op`: ILLTYPED at
distance one, or the evaluator's kill; `complete_save`/`_pure_sym`/
`_memop_op`: the evaluator's kill; `complete_memop_vals`: the fork and
the driver's INVALID-memop panic; the betas at the wildcard pattern, at
the plain-symbol binder — whose head is a bare-value producer,
`BareHead` — and the merge always step). The evaluator's kills are the
classifier `evalClass` (EvalClass.lean) answering `.kill err`: an
unbound symbol naming no procedure (`Unresolved_symbol`), a binop at
operands of mismatched kinds, an array shift at a non-(pointer,
integer) pair (`Illformed_program`), certified against the engine's
evaluator tower level by level exactly as the success bridge is.
`OpenRound` is the RESIDUAL, two arms each recording that the mirror is
stuck and carrying a mirror-side witness: `eval_uncovered` (an operand
in the covered grammar CONTAINING A LEAF the engine accepts where the
mirror evaluator does not evaluate — a symbol unbound in the environment
but naming a `Proc` of the file, a mirrored binop at two floats, `OpEq`
at two ctypes; `evalClass` answers `.uncovered` at the FIRST such leaf
and carries no engine claim, so the whole operand's outcome is NOT
characterized — the engine may succeed, kill on a later type error
(`f + 1` with `f` a `Proc`-named unbound symbol is `PePure`, classified
`.uncovered`, and killed as `Illformed_program … ill-typed PEop`;
2026-09-03 audit, by execution), or panic (a float guard under `Eif`);
so every operand the classifier REJECTS is a proved engine KILL,
operands it leaves UNCOVERED are not characterized, and the residual is
a SUPERSET of the engine-accepted shapes; the mover is `evalClass`
computing the engine's value at the three leaf shapes) and
`run_surplus` (a jump with more arguments than the label's parameters,
the zipped ones evaluating and a surplus one not). `cerberusRound_classify`
sorts every `Frag` configuration into `value_done` / `value_annot` /
`step` / `refused` (carrying its `ShippedRefusal`) / `open_` (carrying
its `OpenRound`). Hence the logic is SOUND (every proved-safe execution
is an engine execution) and COMPLETE for the declared fragment up to
the residual (§7): mirror steps iff the engine has a successful
deterministic round — with two disclosed exceptions to the iff, the
REMOVE-ANNOT value round (`value_annot`: an annotated value's annotation
is stripped by an engine round the mirror treats as a value step) and
`error_next` (an engine SUCCESS round into a configuration whose next
round is ILLTYPED, filed under refusals) — and every stuck configuration
is classified. What is established, in the words of the 2026-09-02 audit: "a sound Iris
program logic for the package's restricted relational mirror, with a
verified forward connection to successful Cerberus engine rounds on
proved-safe executions" — now with the backward classification of every
fragment refusal outside the gaps. The mirror's only reference is the
shipped round `CerberusRound`; no other relational semantics is
referenced or bridged, and none is needed for the root of trust, which
is the engine.

**Why the fuel premises exist.** The engine's redex search `get_ctx` is
fuel-bounded at `lemDefaultFuel` with an opaque exhaustion leaf, so
`engine_step_matchU` needs `esize e ≤ lemDefaultFuel` for the current
term. Along a step `esize` can grow by one, which would couple a drive
statement's premise to the drive length; the potential `pot`
(Potential.lean) bounds `esize` (`Frag.esize_le_pot`) and never
increases along a step except at a jump, where it resets to the
registered body's own potential (`Frag.pot_step_bound`). Hence the two
static premises `pot e ≤ lemDefaultFuel` and `pot cont ≤ lemDefaultFuel`
per registered body, and no bound on the drive length.

**The second fuel bound: pure operands.** The engine's pure-expression
evaluator is fuelled at the same budget (`step_eval_pexpr`,
`pull_constrained`), so the fragment carries a second static premise
family inside `Frag` itself: every constructor that evaluates a pure
operand — `Frag.if_` (the guard), `Frag.run` (the jump arguments),
`Frag.save` (the initializers), `Frag.load_op`/`Frag.memop_op`/
`Frag.store_op` (the operands the engine evaluates before dispatching
the action) — carries `peDepth pe ≤ lemDefaultFuel` per operand, where
`peDepth` (Soundness.lean) is the operand's syntactic depth: 1 at a value
or a symbol, `1 + max` of the children at `PEop`/`PEarray_shift`. The
three operand-evaluation constructors also require their operands to lie
in the sub-grammar `PePure` the mirror evaluator covers (values,
symbols, `PEop` binops, `PEarray_shift`); for `if_`/`run`/`save` the
grammar is enforced by the rule's `evalPexpr … = some …` premise instead
(`evalPexpr_shape`: success implies membership). Verbatim, `Frag.if_`
and the premises of `Frag.store_op`:

```lean
  | if_ {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
      (hdg : peDepth g ≤ lemDefaultFuel) :
      Frag e2 → Frag e3 → Frag (ifRedex g e2 e3)
```

```lean
      (hnv : valueFromPexprs [pe2, pe3] = none)
      (hp2 : PePure pe2) (hp3 : PePure pe3)
      (hd2 : peDepth pe2 ≤ lemDefaultFuel)
      (hd3 : peDepth pe3 ≤ lemDefaultFuel) :
      Frag (storeOpRedex loc ann ty pe2 pe3 mo)
```

Like `pot`, the bound is static — `rfl` for every authored program
(`peDepth_sym_le`, `peDepth_val_le`) — and never mentions the run length;
unlike `pot`, it lives inside `Frag`, so it appears on no exhibit as a
separate hypothesis. The two budgets are the engine's own: `get_ctx`
for the redex search (bounded by `pot`), `step_eval_pexpr` for the pure
operands (bounded by `peDepth`).

**Adequacy.** The Iris half (`spike_step_adequacy`) is
`wp_strong_adequacy_gen` with the ghost state constructed by
`genHeap_init` and the initial cells minted from `Coh`
(`spikeCells_alloc`; for allocating programs `launchResources` under
`LaunchCoh … B` also mints the cursor and grants the budget
`allocBudget B`). The engine
face, `engine_adequacy` (Adequacy.lean): for `Frag e₀` with `pot e₀ ≤
lemDefaultFuel` at a context with empty tag definitions and extern whose
registered label bodies and declared procedure bodies are in `Frag` with
their static bounds, `Coh M.tagDefs σ₀ m₀`, and an Iris proof that the
footprint cells entail the WP with the readout post `∀ σ' ns κs nt,
stateInterp σ' ns κs nt ={⊤, ∅}=∗ ⌜ψ w.val σ'⌝`: `DriverSafeCtl M th₀ e₀
(ev00 :: evs0) ctl σ₀ ψ` (§1.1) — from any driver state holding the
configuration, the shipped loop at every fuel exhausts or delivers with
`ψ` — by `drive_safe_aux`, the induction on the fuel: each iteration is
the shipped round `loop_step_frag'` (§5 above) at the mirror step
`NotStuck` supplies, through PCALL and RETURN under the control invariant
`ControlOk`, the env-depth invariant and the registration ties; fuel 0 is
the exhaustion kill (`loop_zero_exhausts`), a delivered value at fuel 1
is the drain iteration's exhaustion (`loop_step_done_exhaust`) and at
fuel ≥ 2 PROGRAM-DONE (`loop_step_done`); refusals contradict `NotStuck`,
and the value protocol composes REMOVE-ANNOT with PROGRAM-DONE.
`project_triple_pure` is this theorem plus `stateInterp_readout`
(Rules.lean) on the Iris post. The total half is the driver lane
(ProdLoop.lean): from `blockSpecsT M ctl.proc Ls emptyProcSpecT
(readoutPost ψ) ∗ wpt M ctl.proc Ls emptyProcSpecT k (readoutPost ψ) e₀
(ev00 :: evs0)`, `DriverDoneAt p Q th₀ e₀ (ev00 :: evs0) σ₀ ψ k` — the
shipped loop returns PROGRAM-DONE within `k + 2` iterations
(`wpt_driver_aux`, one shipped round `loop_step_frag_same` per budget
unit) — and, through calls, `wpt_driver_cps` → `DriverDoneCtl`. Both
faces (and the `_alloc` twins) are over the shipped loop; the closed
forms over the pipeline are §5's production entry.

**The production entry.** `DriverCollapse.lean` proves, from the
driver's own round functions (`driver2`, `new_drive_core_threads`,
`drive_nonmemory_steps_aux2`, `advance_step`, `perform_action_request2`,
`action_request_sequential2`, `runND`, `finalize`), that for a
single-threaded fragment configuration one production round is exactly
one drive round (`loop_step_frag`), that the whole driver computation is
a branch-free ND tree so `runND` yields the singleton execution
(`driver2_done`, `runND_active`), and that `finalize` reads the
delivered value back (`finalize_done`). `ProdLoop.lean`'s
`wpt_driver_done(_alloc)` drives the driver's per-thread loop by the
total judgment, one round per budget unit, concluding `DriverDoneAt`
(a package-defined delivery fact); `ProdEntry.lean`'s `prod_run_eqJ` —
generic collapse machinery with `DriverDoneAt` as its premise, not a
closed statement — starts from the shipped
`initial_driver_state` (memory `initialMemState`, `errno` allocated by
the real allocator — `prodMem₀` is derived through engine functions
only) and concludes `CerbND.runND (_root_.drive fmapEmpty false (prodFile
e) args) ((initial_driver_state sup (prodFile e) fs).1) =
[(nd_status.Active dres, [], dst')]` with `ψ dres.dres_core_value
dst'.layout_state`, under the label tie `LabeledAt` derived from the
shipped registration (`collect_labeled_continuations_NEW`;
`fib_labeledAt_production`, `loop_labeledAt_production`) and `k + 2 ≤
CerbFuel.driverFuel`, the shipped driver's own budget (10^8 since the
cerberus-lean fuel arc) for `k` rounds plus the done-recording and drain
iterations — below it the shipped driver's value is the kernel-transparent
kill `CerbND.fuelExhaustedKill`, about which these TOTAL statements say
nothing (§1.3). The theorems hold for every
supply `sup` because the fragment never reads it. These production
statements are the root-of-trust exports (§1.3).

## 6. Reading the audit

`CerberusHeapLang/Audit.lean` is the last import of the library root, so
`lake build` elaborates it and a failure is a red build. It asserts, in
order: (1) exact pins — every name in `trioExports` (312 theorems at the
time of writing, 2026-09-03: the
rules, the adequacy and collapse theorems, every exhibit, the
projections and the consequence lemmas) exists, is a theorem, and has
transitive axiom set equal to `[propext, Classical.choice, Quot.sound]`
— growth or shrinkage fails until the list is re-baselined in the same
commit with the reason; (2) the exhaustive sweep — every theorem of
every `CerberusHeapLang.*` module, internal details (private names,
proof and match auxiliaries, equation lemmas) included, is bounded by
those three axioms; (3) the banned-axiom sweep — no constant of any
kind, internal details included, carries `sorryAx`, `ofReduceBool` or
`ofReduceNat`. The scope is exact: until 2026-09-02 both sweeps
skipped internal-detail names, so a private `sorry` unused by any
pinned export passed the build; a planted one is now red
(`2026-09-02_audit-response-3-notes.md`). There is no declared boundary axiom:
neither the semantics workspace nor its lem runtime contains an
`axiom` declaration. Admissions in the pinned semantics tree: none
(measured 2026-09-03). Until the 2026-09-03 re-pin the pinned tree
carried one generated admission — two `(sorry : String)` terms in the
debug-log branch of `auxAddToRfLoad` in the generated concurrency model
(`Cmm_op.lean`), outside every export cone — which the fuel-arc head
`f95ef8d9c` closes; measured at this pin, `grep -rn '(sorry'` over the
primed `generated/*.lean` finds nothing and the build log contains no
`declaration uses sorry` (README "The trust story";
`2026-09-03_repin-fuel-notes.md`). The banned-axiom sweep stays in
force — `sorryAx` reaches no `CerberusHeapLang` constant — and
concurrency is out of scope here.
What the sweep does not certify: the scope qualifiers (parts of the statements),
the readout predicates' faithfulness (§2 — read them), coverage (the
capability manifest's job). The build command, its expected tail and
the `#print axioms` recipe are in the README, "How to build and verify".

## 7. What is deliberately out, and why

- **Procedure specifications.** The static dispose rule landed in K2
  and the dynamic `alloc`/`free` rules in K3 (§4); procedure
  specifications (incl. recursion) are the calls arc: C1 (2026-09-03)
  made the thread's control — call stack, current procedure, execution
  location — LIVE STATE (`Ctl`, the fourth configuration component); C2
  added the two rules that write it, `Step.call` (the PCALL round, the
  call redex's evaluation context CAPTURED on the stack) and `Step.ret`
  (the RETURN round, the value plugged back into it), certified them
  (`engine_step_matchU` at a free successor control; the two-procedure
  smoke rounds in `Examples/MirrorCoverage.lean`) and classified them
  (`complete_call`: `call_proc`'s two `Illformed_program` kills verbatim;
  `complete_ret`: a value under a frame always steps); C3 (2026-09-03)
  added the LOGIC: the specification table `ProcSpec`, the call clause of
  both judgments, the call rule (`wps_call_root`/`wpt_call_root`), the
  procedure rule (`procSpecs_intro` — Hoare's rule for recursive
  procedures, no Löb in the introduction) and the CPS collapse
  `wps_sound_cps` (§3.3; the one Löb ties back edges and calls alike),
  with the two-procedure smoke `Examples/CallSmoke.lean` through the
  partial lane at the shipped loop (`call_smoke_engine`; `FragProcs`
  discharged at two procedures); C4
  (2026-09-03) closed the arc: the plain-symbol binder binds a call's
  result (`BareHead.call`), the PRODUCTION lane goes through calls (the
  CPS driver induction `wpt_driver_cps` over the live-control delivery
  fact `DriverDoneCtl`, every PCALL/RETURN round the driver's own
  `loop_step_frag`; the `exec_loc`/`current_loc` tie at the production
  entry control `prodCtl`/`prodCtx`), the synthetic file takes declared
  procedures (`prodFileWith`, `prod_run_eqJ_procs`), and RECURSIVE FIB is
  the eighth root-of-trust statement (`fib_rec_certified_production`,
  §3.3); MUTUAL RECURSION is exhibited since 2026-09-04 (H1b,
  EvenOddExhibit.lean: `even`/`odd` under the symbol-dependent table,
  `even_odd_certified_production` the ninth root-of-trust statement).
  Still out, by design: function pointers (`Eccall`). (The total `driveU` lane at
  the empty table was deleted with the package loop in the fuel-lane
  restatement, 2026-09-03.) The remaining absences are structural, not
  hidden: the empty-stack entry control (`ctl.κ = []`) wherever a general
  control appears, `MachineCtx.SeqWF` (startup thread) as the round
  classification's premise, and — for the partial adequacy exports, whose
  NotStuck oracle is the raw WP — the procedure well-formedness premise
  `MachineCtx.FragProcs`.
- **The static kill of a region, `free` of a created object,
  `free(NULL)`, the zero-cost `alloc`.** In the fragment, mirrored and
  classified (`complete_kill`/`complete_alloc`), covered by no rule —
  raised by the K2 range audit, decided at K3 (README "Scope, exactly"):
  the rules are kind-specific over the object bundle (`kill_atomic`)
  and the region bundle (`free_atomic`); a program that disposes
  storage under the wrong kind is outside the logic by design.
- **Loads and stores through a region pointer — no longer out.** K4
  found them covered by no rule (an ABSENCE, not a decision); K5 added
  `regionLoadAt_atomic`/`regionStoreAt_atomic` over the typed region
  view through the seams `loadM_live`/`storeM_live` (§4, "The region
  access rules"; README "Scope, exactly" (iv) CLOSED), and the malloc'd
  LINKED list (MallocListExhibit.lean) is the exhibit. Kept in this list
  only so a reader of the K4-era text finds the closure here.
- **A program with TWO `save` labels — CLOSED 2026-09-04 (H1b,
  TwoLabelExhibit.lean: `two_label_certified`, `tl_wpt`; the label
  specification is label-dependent, no rule changed).** Until then every
  loop exhibit was single-label (the malloc'd list merges its two C loops into ONE Core
  label with two phases). The two-entry lookup law the two-label form
  needs is here since C4 — the β-generic `symAdd_lookup`/
  `symAdd_lookup_two` (EnvLaws), the C3 smoke's local law moved — so what
  remains is the exhibit (found by the K5 range audit; the law's
  comparator question measured at C4: the lookup reads the bucket head
  and the add comparator enters only as the captured `symOrd`).
- **Located Core.** Every node of a fragment program carries the empty
  static annotation list (`Expr []` in every `Frag` constructor and every
  redex spelling). The engine's `step_ctx` rewrites the thread's
  `current_loc` from a located annotation (`get_loc e_annots` in its
  general arm), and this package keeps `current_loc` in the immutable
  `MachineCtx` — so located Core, in particular all Core produced by the
  C elaborator, is outside `Frag`. Making `current_loc` live state is the
  mover (README, "Scope, exactly").
- **`Eunseq`.** Core's unsequenced composition is a semantic gap for a
  sequential logic.
- **The memop family beyond `PtrEq`**, and `PtrEq`'s
  differing-provenance nondeterministic fork: absences of a mirror step.
- **`Ecase` with a non-value scrutinee, `Ewseq` at binder patterns, pure
  exits beyond `PEsym`, the symbol-binder beta at annotated values**:
  mechanical per-construct extensions, each needing a `dischargeStep`
  arm, a `Step` rule and a rule at each judgment. Not a gap: the pure
  and annotation rules are stated at the empty annotation list `Expr []`
  — the mirror's values live there, and the annotation-generic forms are
  false.
- **Fuel parametricity.** The engine's `get_ctx` fuel is real (the
  interpreter bails past `10^6`), so the projection theorems carry the
  static `pot` premises and the production statements carry `k + 2 ≤
  CerbFuel.driverFuel` (the shipped driver's budget, 10^8 since the
  fuel arc).
- **A C frontend.** Programs enter as authored Core in a synthetic file
  (`prodFile`: one procedure; `prodFileWith`: `main` plus declared
  procedures).
- **The residual of mirror completeness** (`OpenRound`, §5;
  `2026-09-02_fragment-closure-notes.md`): an operand in the covered
  grammar containing a LEAF the engine accepts where the mirror
  evaluator does not evaluate (a procedure-named symbol, a mirrored
  binop at two floats, `OpEq` at two ctypes) — the classifier answers
  `.uncovered` at the first such leaf and carries no engine claim, so
  the whole operand's outcome is NOT characterized (it may succeed,
  kill, or panic; every operand the classifier REJECTS is a proved
  engine KILL, operands it leaves UNCOVERED are not characterized, the
  residual is a superset of the engine-accepted shapes) — and a jump
  with surplus arguments. Both are environment-, file- or
  label-map-dependent; the movers are `evalClass` computing the
  engine's value at the three leaf shapes (the characterization), a
  mirror evaluator complete relative to `eval_pexpr_aux2` on `PePure`
  (emptying the arm), and a prefix-evaluating `Step.run`. The four gaps registered on 2026-09-02
  were closed fail-closed the same day.
- **A partial CLOSED statement for the seeded and straight-line
  exhibits.** The partial lane is over the shipped driver's loop at every
  fuel (§1.3; the fuel-lane restatement of 2026-09-03), and the closed
  form over the pipeline exists for programs that run from the cold start
  (`prod_run_safe_procs`; `fib_rec_certified`); the seeded exhibits
  (pre-seeded cells) have no cold-start form, and the straight-line
  exhibits stay at the `spikeCtx` profile (a thread with no current
  procedure, admitted by the loop-level fact, never parked by the shipped
  driver). Movers: self-contained twins for the seeded programs;
  re-contexting the straight-line exhibits at the production context.
  Also: `drive_lemFuel`'s fuel bounds the outer `driver2` rounds only
  (measured, §1.3) — a loop-fuel-parametric closed statement would need
  the second upstream mirror recorded as available in the design review.
- **Parametric semantics interfaces.** Not adopted: the rules are proved
  directly against `Step` and the memory state, as RefinedC proves its
  memory rules by inversion.

Records — design history, decision provenance, the audits and reviews —
are the dated files under [`docs/`](.) (the README's "Records" section
lists the current ones) and `../../docs/DECISIONS.md`; the README carries
the claims surface, the trust diagram and the register of divergences
and limitations.
