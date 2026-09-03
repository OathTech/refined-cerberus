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
[`2026-09-02_pr3-C-signatures-post.txt`](2026-09-02_pr3-C-signatures-post.txt).

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
precisely, the execution function named in each statement (§1.3), and
where statements over the package's drive loop `driveU` carry the
label PROVISIONAL (§1.3) while the production statements over the
shipped driver are the root-of-trust exports. The normative
architecture statement is [`../ARCHITECTURE.md`](../ARCHITECTURE.md).

## 1. The claim, and one exhibit

### 1.1 The shape

The target: `s |= P && core_exec(prog, s) ~~> term ==> term = some(s')
&& s' |= Q`, for P and Q "just memory + pure properties". Its
realization is the triple over engine states (`Adequacy.lean`):

```lean
def MemTripleU (M : MachineCtx) (ρ : EnvStack) (e : CoreExpr) (P : CellMap)
    (post : CellMap → value → Mem → Prop) : Prop :=
  ∀ (R : CellMap), P ##ₘ R →
  ∀ (σ : Mem), Sat M.tagDefs σ (Iris.Std.PartialMap.union P R) →
  ∀ (n : Nat) (aids : Nat → Nat),
    (∀ r, driveU M aids n (M.thread e ρ) σ ≠ .killed r) ∧
    (driveU M aids n (M.thread e ρ) σ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem), driveU M aids n (M.thread e ρ) σ = .done v σ' →
      post R v σ')
```

`σ : Mem` is a real engine memory state (`CerbMem.MemState`); `Sat
M.tagDefs σ (P ∪ R)` is `s |= P` with the frame built in — `P` the
footprint (a finite map of allocation-rooted cells), `R` an arbitrary
disjoint rest (§2). `driveU M aids n (M.thread e ρ) σ` is `core_exec`:
`n` rounds of the engine's `step_ctx`, each followed by request
discharge, at every action-id supply `aids` (§1.3). The conclusion: the
engine never kills (no undefined behaviour, no error kill), never gets
stuck off-protocol, and whenever it delivers `.done v σ'`, `post R v
σ'`. Fuel exhaustion (`.more`) carries no obligation: partial
correctness. The drive length `n` is unbounded; the triple carries no
fuel premise.

**PROVISIONAL.** `MemTripleU` is stated over `driveU`, not over the
shipped driver, and so is every theorem below whose execution function
is `driveU` (§1.3 lists them). Each is PROVISIONAL in exactly this
sense: a sound fact about `driveU`, this package's loop around the
engine's `step_ctx`; not yet the root-of-trust statement, which is over
the shipped driver and awaits the cerberus-lean fuel-exhaustion outcome
([`../../docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md`](../../docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md));
restated with no other change when it lands. The root-of-trust exports
are the total-lane production statements (§1.2).

There is no Iris in `MemTripleU`. The theorem that produces one from an
Iris triple is the headline of the partial lane (PROVISIONAL, as its
conclusion is):

```lean
theorem project_triple_pure {GF : BundledGFunctors} [SpikeGpreS GF]
    {M : MachineCtx} (hwf : M.SeqWF)
    (hQf : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      Frag cont)
    (hQpot : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      pot cont ≤ lemDefaultFuel)
    {e : CoreExpr} (hfrag : Frag e) (hpot : pot e ≤ lemDefaultFuel)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value))
    (P : CellMap) (Q : ∀ [SpikeGS .hasLC GF], CoreRVal → IProp GF)
    (ψ : CellMap → value → Mem → Prop)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ P, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c)) ⊢
        WP (⟨e, ev0 :: evs, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ {{ w, Q w }})
    (hpost : ∀ [SpikeGS .hasLC GF] (w : CoreRVal) (R : CellMap) (σ' : Mem)
      (mm : SpikeHeapF MetaCell) (mb : SpikeHeapF CerbMem.AbsByte)
      (mk : SpikeHeapF AllocCursor), CohG σ' mm mb mk →
      iprop(Q w ∗ ([∗map] i ↦ c ∈ R, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c) ∗
        metaInterp mm ∗ byteInterp mb) ⊢ (⌜ψ R w.val σ'⌝ : IProp GF)) :
    MemTripleU M (ev0 :: evs) e P ψ := by
```

Hypotheses: a sequentially well-formed context (`SeqWF`: empty call
stack, startup thread); the program and every registered label body in
the fragment `Frag`; the static fuel bounds `pot e ≤ lemDefaultFuel` and
`pot cont ≤ lemDefaultFuel` per registered body (`pot` is a
step-monotone size potential on terms, Potential.lean; `lemDefaultFuel =
10^6` is the engine's evaluator budget; both are `rfl` for authored
programs — §5 says why they exist, and names the second, operand-level
fuel bound `peDepth` that lives inside `Frag` itself); an Iris triple `hwp` — footprint
ownership entails the WP of the program with any Iris post `Q`; and
`hpost` — the framed Iris post pure-entails `ψ R w.val σ'` under any
coupling witness `CohG σ' …` for the final memory. Conclusion:
`MemTripleU M ρ e P ψ`, with no Iris in it. `hpost` is the one
Iris-shaped obligation a client meets; the pure-consequence lemmas
discharge it for the points-to shapes (`cellOwn_consequence`,
`pointsToCell_consequence`, `cellsOwn_consequence`, `cells_consequence`,
`pure_`/`sep_`/`or_`/`exists_consequence`), yielding `CellCoh σ' i c`
facts about the final memory. Beneath it sits the strongest-post form
`project_triple`; `SemTripleU` is `MemTripleU` at the cells-shaped post
(`SemTripleU_iff_Mem`). The allocating twin `project_triple_pure_alloc`
adds `∗ allocCap M.tagDefs reqs` (§3.2) to `hwp` and concludes
`MemTripleU_alloc`, whose launch premise `LaunchCoh` is `Sat` plus
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
runs — this is a ROOT-OF-TRUST export, one of the four closed
shipped-driver statements: the genuine driver, no package-defined loop
in the statement (the authored program enters wrapped by `prodFile`,
the synthetic one-procedure file). The theorem quantifies over nothing but the file-system state,
argv and the entry's symbol supply `sup` (the fragment never reads it):
the run is the singleton `Active` execution — an equation, so a total
statement — its delivered value heads a chain seeded as the reversed
list at existential allocation ids (the logic binds the pointers, the
engine picks them), and the final production memory satisfies that
footprint. No `driveU`, no `Step`, no Iris in the statement. The general
drive statement beneath it — any chain, any frame, any memory with `Sat
fmapEmpty σ₀ (m₀ ∪ R)`, every drive length — is `list_reverse_certified`
(README, "The exhibits"); being over `driveU`, it is PROVISIONAL
(§1.1).

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
      wps (procCtx p rs) (frameLs RF (lrLs ns))
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
triple holds at the machine context `procCtx p rs` whose label table is
the loop's (`procCtx_labels hQ`), which is what lets `wps_run` resolve
the jump. Read: `{ isList head ns ∗ RF } reverse { ret p'. isList p'
ns.reverse ∗ RF }`. The unframed proof `lr_wps` is textbook — invariant
`isList prev reversed ∗ isList cur rest` (`lrLs`), each construct
discharged by its own rule, `wps_run` at the back edge asking only for
the label's precondition, `blockSpecs_intro` assembling the registered
body's specification — and the frame is `wps_frame_labels` applied
once. `wps_sound_frame` collapses to the raw WP and `engine_adequacyU`
lands the drive statement; `lrProd_wpt` proves the build-and-reverse
program at the total judgment and `wpt_driver_done_alloc` →
`prod_run_eqJ` supply the pipeline.

### 1.3 What "the engine" is in each statement

Two execution functions appear in exported statements, and they are not
the same object. In the drive statements — `MemTripleU`,
`MemTripleU_alloc`, `SemTripleU`, every `*_certified`, `*_total`,
`*_engine` — it is `driveU` (Adequacy.lean, printed in §2): this
package's definition of the sequential driver's round loop. Each round
calls the engine's own `step_ctx` and discharges the resulting request
with `dischargeStep` (Soundness.lean), a hand-written projection of the
driver's `action_request_sequential2` onto (thread state, memory) that
runs the real `storeM`/`loadM`/`allocateObject`. `driveU` is tied to the
shipped driver by `loop_step_frag` (DriverCollapse.lean): one round of
the production scheduler at a single-threaded fragment configuration is
one `driveU` round — but that theorem is stated at configurations where
the mirror `Step` steps, and it is consumed only by the total judgment
(`wpt_driver_done`, `wpt_driver_done_alloc` → `prod_run_eqJ`). No
partial-correctness statement about the shipped pipeline is proved, and
none can be by this route: when the production loop's fuel runs out its
value is LemLib's `fuelExhausted`, a wrapper around the kernel-opaque
constant `fuelExhaustedWith`, and nothing is provable about an opaque
constant's value. So the partial logic's "engine" is `driveU`:
`step_ctx` (the engine) plus `dischargeStep` (this package's projection,
a readout predicate you must read, §2). In the production statements —
`exhibitA_prod`, `*_production` — it is the shipped `CerbND.runND (drive
fmapEmpty false file args) (initial_driver_state sup file fs).1`, for
total statements only.

**The two lanes, labelled.** Every exported execution theorem is
either explicitly provisional over driveU or reaches the shipped
engine; every public logical rule has a kernel-checked adequacy path
through the package mirror to the engine. The four production
statements (`exhibitA_prod`, `fib_certified_production`,
`counter_loop_certified_production`,
`list_reverse_certified_production`) are THE ROOT-OF-TRUST exports —
the closed shipped-driver statements: the genuine Cerberus driver, and
nothing package-defined in the statement but the authored program, its
`prodFile` wrapper and the pure readout predicates. `prod_run_eqJ`,
through which they are proved, is generic collapse machinery, not a
closed statement: its delivery premise `DriverDoneAt` (ProdLoop.lean)
and its label tie `LabeledAt` are package-defined, discharged by each
of the four. Every statement over `driveU` — `MemTripleU`,
`MemTripleU_alloc`, `SemTripleU`, `project_triple`,
`project_triple_pure`, `project_triple_alloc`,
`project_triple_pure_alloc`, `semantic_triple_soundU`,
`semantic_frameU`, `engine_adequacyU`, `engine_adequacyU_alloc`,
`wpt_engine_boundU`, `wpt_engine_boundU_alloc`, and every exhibit the
README's table lists at `driveU` — is PROVISIONAL: a sound fact about
`driveU`, this package's loop around the engine's `step_ctx`; not yet
the root-of-trust statement, which is over the shipped driver and
awaits the cerberus-lean fuel-exhaustion outcome
(`../../docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md`);
restated with no other change when it lands. The request asks the
cerberus-lean team for a transparent, distinguished fuel-exhaustion
outcome in the driver monad; no package-side driver is written to work
around the opaque one.

## 2. The readout predicates

The trust claims, the differential-validation record, the Cerberus
configuration the statements pin, and the chain of theorems from the
engine to the exports are the README's "The trust story" and its trust
diagram. `Step`, the rules, the judgments and iris-lean are interior —
they occur in proofs, never in an exported conclusion — so a bug there
deprives us of proofs, not of the truth of what was proved. That is
relative to the readout predicates: a wrong `driveU`, `dischargeStep` or
`Sat` would make a theorem true but about the wrong thing, which is why
they are printed here in full.

```lean
inductive DriveResult : Type where
  /-- fuel ran out with the machine resting here (no claim is made) -/
  | more (th : thread_state) (σ : Mem)
  /-- PROGRAM-DONE: the engine delivered a value -/
  | done (v : value) (σ : Mem)
```

```lean
  | killed (r : kill_reason mem_error)
  /-- refusal (Step_error2 / ILLTYPED) or any off-protocol engine
      behavior -/
  | stuck
```

```lean
def stepOutcomes (M : MachineCtx) (aid : Nat) (th : thread_state)
    (σ : Mem) : List EngineOutcome :=
  (step_ctx M.tagDefs σ M.file M.extern M.tid (M.parent, th)).map
    (dischargeStep M.tagDefs aid M.runState σ)
```

```lean
def driveU (M : MachineCtx) (aids : Nat → Nat) :
    Nat → thread_state → Mem → DriveResult
  | 0, th, σ => .more th σ
  | n+1, th, σ =>
    match stepOutcomes M (aids 0) th σ with
    | [.next th' σ'] => driveU M (fun i => aids (i+1)) n th' σ'
    | [.done v] => .done v σ
    | [.killed r] => .killed r
    | _ => .stuck
```

(`driveU` is the referent of the PROVISIONAL lane only, §1.3; the
root-of-trust exports do not mention it. The `killed` constructor's
docstring, elided, enumerates the engine's
three kill reasons — undefined behaviour, the non-UB memory errors such
as an ill-typed store, and the Core-run layer's `Error`; "never kills"
excludes all three.) `dischargeStep` (Soundness.lean) is the sequential
driver's request discharge projected to (thread, memory), mirrored
function by function with citations into the engine in its header;
`aids` is the driver's per-step action-id supply, ∀-quantified because
the fragment never reads it. The footprint predicates:

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

Five specifications are proved directly against `Step`, each running the
real engine function inside the proof: `store_atomic`
(`storeM_success`), `load_atomic` (`loadM_success`),
`storeAt_atomic`/`loadAt_atomic` (typed subranges,
`storeM_at`/`loadM_at`), `create_atomic` (`allocateObject_success`).
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
    (aprov : CerbMem.Provenance) (req : AllocReq) (rest : List AllocReq)
    (pref : prefix0) (ρ : EnvStack)
    (hatom : atomicTy req.ty = false)
    (hinert : ∀ a : Int, decIndep M.tagDefs a req.ty
      (List.replicate (CerbMem.sizeofCtype M.tagDefs req.ty) undefByte)) :
    iprop(allocCap M.tagDefs (GF := GF) (req :: rest) ∗
      (∀ p : CerbMem.PointerValue,
        (pointsToCell M.tagDefs p (.own 1) req.ty
            (List.replicate (CerbMem.sizeofCtype M.tagDefs req.ty) undefByte) ∗
          allocCap M.tagDefs rest ∗
          ⌜0 < addrOf p ∧ addrOf p < 2 ^ 64⌝) -∗
        Ψ (SpikeVal.pure (Vobject (OVpointer p))) ρ)) ⊢
      wps M Ls Ψ (createExpr loc ann (.IV aprov req.align) req.ty pref) ρ := by
```

Capacity for the plan `req :: rest` buys one `create` of `req`; the
continuation receives an existential fresh pointer with full whole-cell
ownership at the unspecified byte image, the remaining capacity, and
the pointer's machine-address bounds. `hatom`: a non-atomic type;
`hinert`: the unspecified image decodes independently of the side
tables (`rfl` for the exhibits' types). Nothing in the statement names
the allocator's cursor. `wpt_create` is the same at the total judgment
with the cost bound `2 ≤ k`. Why `allocCap` has this shape, and what it
costs, is §4.

### 3.3 One loop rule, and the total judgment

The partial judgment `wps M Ls Ψ e ρ` is a guarded fixpoint (iris-lean's
`fixpoint` over a contractive `wps.pre`) with three clauses — value,
jump redex, step. `Ls : LabelSpec GF` (`sym → List value → EnvStack →
IProp GF`) gives each registered label a precondition over its argument
values and the jump-time environment. The jump rule `wps_run`: under
`lookupLabel M.labels l = some (params, cont)` and `evalPexprs M.tagDefs
M.extern (ev0 :: evs) pes = some vs`, `Ls l vs (ev0 :: evs) ⊢ wps M Ls Ψ
(Expr a (Erun ra l pes)) (ev0 :: evs)` — the label's precondition
suffices and tracking stops: a jump's postcondition is the label's
business. The loop rule assembles the registered bodies' specifications
with no Löb and no mutual assumption:

```lean
theorem blockSpecs_intro {Ψ : SpikeVal → EnvStack → IProp GF}
    (h : ∀ l params cont vs ev0 evs,
      lookupLabel M.labels l = some (params, cont) →
      Ls l vs (ev0 :: evs) ⊢ wps (GF := GF) M Ls Ψ cont
        (bindArgs params vs (ev0 :: evs))) :
    ⊢ blockSpecs M Ls Ψ := by
```

The one Löb induction lives in the collapse `wps_sound`: `blockSpecs M
Ls Ψ ⊢ wps M Ls Ψ e ρ -∗ WP ⟨e, ρ, M⟩ @ NotStuck; ⊤ {{ w, Ψ w.w w.ρ }}`.
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

**The total judgment** is defined by structural recursion on a step
budget, no fixpoint, no ▷:

```lean
def wpt.pre [SpikeGS hlc GF] (M : MachineCtx) (Ls : LabelSpecT GF)
    (k : Nat)
    (F : (SpikeVal → EnvStack → IProp GF) → CoreExpr → EnvStack → IProp GF)
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
        ⌜ρ = ev0 :: evs⌝ ∗ ⌜lookupLabel M.labels lp.1 = some (params, cont)⌝ ∗
        ⌜evalPexprs M.tagDefs M.extern ρ lp.2 = some vs⌝ ∗
        ⌜1 + m ≤ k⌝ ∗ Ls lp.1 m vs ρ)
    | none =>
      match k with
      | 0 => iprop(⌜False⌝)
      | _ + 1 =>
        iprop(∀ (σ₁ : Mem) (ns : Nat) (obs : List Empty) (nt : Nat),
          stateInterp σ₁ ns obs nt ={⊤,∅}=∗
          ⌜PrimStep.Reducible ((⟨e, ρ, M⟩ : CoreRt), σ₁)⌝ ∗
          ∀ (r : CoreRt) (σ₂ : Mem) (eₜ : List CoreRt),
            ⌜((⟨e, ρ, M⟩ : CoreRt), σ₁) -<([] : List Empty)>-> (r, σ₂, eₜ)⌝
              ={∅,⊤}=∗
            stateInterp σ₂ (ns + 1) obs nt ∗ F Ψ r.e r.ρ)
```

```lean
def wpt [SpikeGS hlc GF] (M : MachineCtx) (Ls : LabelSpecT GF) :
    Nat → (SpikeVal → EnvStack → IProp GF) → CoreExpr → EnvStack → IProp GF
  | 0 => wpt.pre M Ls 0 (fun _ _ _ => iprop(⌜False⌝))
  | k + 1 => wpt.pre M Ls (k + 1) (wpt M Ls k)
```

Section variables not shown: `{hlc : HasLC} {GF : BundledGFunctors}`.
`LabelSpecT` preconditions carry a variant `m : Nat` (the Floyd variant
as a specification parameter), and the jump clause requires `1 + m ≤
k`: the target's budget plus the jump must fit the remaining budget.
Since a body is verified at budget `m` (`blockSpecsT`) and budgets only
shrink along steps, every back edge strictly decreases a well-founded
measure. The total jump rule is `wpt_run`, with `(hμ : 1 + m ≤ k)`; the
collapse is

```lean
theorem wpt_sound {Ψ : SpikeVal → EnvStack → IProp GF} (k : Nat)
    (e : CoreExpr) (ρ : EnvStack) :
    blockSpecsT M Ls Ψ ⊢
      iprop(wpt M Ls k Ψ e ρ -∗
        WP (⟨e, ρ, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ [{ w, Ψ w.w w.ρ }]) := by
```

into iris-lean's `TotalWeakestPre` (`[{ … }]`), by strong induction on
the budget — a metatheorem about the judgment (it is a sound total WP)
that no export consumes: every total export goes through the engine
simulation `wpt_drive_aux` (§5) directly, and no Iris adequacy result
lies in any total export's cone. Deleting the decrease premise would let a diverging program
be derived: `diverge_total_unprovable` (DivergeExhibit.lean) records
that a total derivation for the self-jump loop is `False`, proved at the
engine — the loop's `driveU` rests in `.more` at every drive length
(`dg_driveU_more`), contradicting the `.done` equation
`wpt_engine_boundU` would deliver (§5).

**What a loop client supplies** (`LoopExhibit.lean`, the counter loop):
a `LabelMap` and a `core_run_state` whose `labeled` fiber at the
procedure symbol is that map (`loopQ`, `loopRS`); the machine context
`procCtx p rs` (Step.lean), whose label table is derived from `rs` by
`procCtx_labels (hQ : LabeledAt rs p Q) : (procCtx p rs).labels = Q` —
`LabeledAt` (Soundness.lean) is the engine's own lookup `fmapLookupBy
ordCompare p rs.labeled = some Q`; the Iris proof carries `hQ` as a
section `variable`, the engine face discharges it by computation
(`loopRS_labeledAt`), and the production statements derive it from the
shipped registration (`loop_labeledAt_production`, ProdEntry.lean); the
label specification (`loopLs`), the body verified once under it,
`blockSpecs_intro`, `wps_save` at entry, `wps_sound` to the raw WP; and
`engine_adequacyU` (§5) — `counter_loop_certified` is exactly this
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
heap (allocation id ↦ base, type, size), the provenance authority —
`loadM`/`storeM` success is decided by the allocation table, so byte
content alone can never entail access success (`metaOwn`); and a
one-cell allocator-cursor heap (`lastAddress`, `nextAllocId`, the two
fields `allocateObject` reads and writes). `CohG σ mm mb mk` couples
byte cells to the bytemap, metadata cells to live, writable, typed,
non-atomic, pairwise range-disjoint allocations, and the cursor, when
present, to the allocator fields. Assertions:

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

**The persistent stratum, and no liveness token.** Allocation knowledge
is the metadata cell at the discarded fraction (`allocMeta tds id a aty
:= metaOwn id .discard ⟨a, aty, sizeofCtype tds aty⟩`; `locInBounds`
adds the pure bound), with `Persistent` instances
(`allocMeta_persistent`, `locInBounds_persistent`); any view's metadata
fraction can be traded for it (`pointsToView_persist`). This is
admissible because metadata is immutable in the fragment — no rule
updates a metadata cell (nothing frees) — so there is no liveness token
to guard a deallocation that cannot happen. The bundles keep the
metadata at a fraction rather than persistent because full metadata
ownership is the per-allocation exclusivity anchor the frame theorem
needs (`metaOwn_ne` → `bigSepM_own_disjoint`); RefinedC's anchor is the
killable `alloc_alive`, and when `kill` joins the fragment the anchor
moves there.

**Read-only allocations cannot be described.** `CellCoh.alloc` and
`MetaCoh.alloc` fix `al.isReadonly = .IsWritable`, and `MetaCell`
records address, type and size but no read-only flag. So every
`pointsToCell`, at any fraction, asserts a writable allocation, and an
object the elaborator marks read-only cannot be the subject of any
assertion. A registered limitation; the mover is a read-only flag in
`MetaCell`, with writability demanded by the store rule only.

**Allocation capacity, and the failure policy.** An `AllocReq` is an
alignment operand and a C object type;

```lean
def allocCap [SpikeGS hlc GF] (tds : CerbTags.TagDefsMap) (reqs : List AllocReq) : IProp GF :=
  iprop(∃ c : AllocCursor, cursorOwn c ∗
    ⌜PlanFits tds c reqs ∧ c.lastAddr ≤ 2 ^ 64⌝)
```

Cerberus's allocator is a deterministic downward cursor; a `create` that
cannot be placed is a kill ("out of memory", the `alignedAddr == 0` arm
of `allocateObject`) — a killed outcome, not a value. RefinedC models
allocation failure as a deliberate `AllocFailed` divergence; this
package does not import that behaviour. Instead `allocCap reqs`
certifies that the finite request plan `reqs`, run in order, never hits
the kill arm: `PlanFits tds c reqs` runs the requests through
`advanceCursor`, whose guard is exactly `allocateObject_success`'s
premise pair (`0 < sizeofCtype tds ty`, `freshBase … ≠ 0`) and whose
update is exactly that theorem's state update — while hiding the cursor
(client statements never name `AllocCursor`, `lastAddress`,
`nextAllocId`, `freshBase` or `cursorOwn`). Clients receive capacity
from the allocation-aware launchers (`launchResources`, `LaunchCoh`) and
may stop early (`allocCap_weaken`), never reorder or skip
(`planFits_order_sensitive`: alignment rounding does not commute).

**Freshness is footprint-relative.** The allocation-aware launch
premise `LaunchCoh tds σ m reqs` (Adequacy.lean) constrains the TRACKED
cells only: `id_lt` (every tracked allocation id is below the engine's
`nextAllocId`), `fresh_alloc`/`fresh_dead` (ids from `nextAllocId` up
are absent from the live and dead tables), `addr_lo` (every tracked
cell sits at or above the downward cursor `lastAddress`), `plan` (the
plan fits the cursor). Neither `Coh` nor `LaunchCoh` says anything
about allocations the footprint does not track, and the engine's
`allocateObject` computes the fresh address from the cursor without
scanning existing allocation ranges. So a `create` is fresh from the
LOGICAL FOOTPRINT — every owned cell is tracked and protected by
`addr_lo`, which is what the create rules' soundness needs — and not
from untracked allocations an arbitrary concrete state may hold below
the cursor; `MemTripleU_alloc` quantifies over such states too, and
says nothing about their untracked storage, as a separation logic may.
The production cold-start state `prodMem₀` contains only the
allocator-created `errno` allocation and no dead allocations
(`prodMem₀_allocations`, `prodMem₀_deadAllocations`, ProdEntry.lean);
`prodMem₀_launchCoh` proves `LaunchCoh` for the empty footprint and any
fitting plan, and no more — there is no global well-formedness theorem
about it. A global memory well-formedness invariant (`MemWF`) —
allocation-id discipline, live/dead consistency, range disjointness of
ALL live allocations, cursor bounds — with its initialization proof
belongs to the launch premise and the state interpretation once
`kill`/free enters the fragment; "globally well formed" is reserved for
it, and it is registered for the malloc/free arc (README, "Registered
divergences and limitations").

**Why an ordered plan and not an additive budget.** The classical shape
would be an additive resource with a split law, `budget (s + t) ⊣⊢
budget s ∗ budget t`, letting two components each own part of the
capacity and allocate independently. It is sound here in a conservative
form: one `create` of `ty` at alignment `al` moves the cursor down by at
most `sizeof ty + al − 1` bytes (`freshBase la al size = alignDown (la −
size) al`), so a budget of the summed per-request costs guarantees
`freshBase ≠ 0`. It was weighed and not adopted, for one forcing fact
about the engine and one about the carrier. The engine's allocator is a
single monotone cursor, so the address of each fresh object is a
function of the exact sequence of preceding requests; the coupling
invariant tracks that cursor exactly (`CohG.cursor` equates the ghost
cursor with `⟨σ.lastAddress, σ.nextAllocId⟩`), and `create_atomic` is
proved by simulating `allocateObject`'s update step for step
(`advanceCursor` is that update on the cursor fields). An additive
budget tracks a bound on the cursor, not its value: it needs an
authoritative-sum ghost algebra (a total with splittable fragments) in
place of the exclusive `GenHeap` cell the cursor lives in, and a
coupling invariant stated as an inequality. The cost of the plan shape
is stated plainly: capacity is not a separation-logic resource in this
package — `allocCap reqs` cannot be split across ∗, it is weakened only
to a prefix (`allocCap_weaken`), and every allocating specification is
parametric in `rest` and threads the plan in order. An additive budget
as a derived, weaker face over the plan, sound by the bound above, is
registered as a future improvement (README, "Registered divergences and
limitations"); it is not a correction to anything proved.

## 5. The engine attachment

`Step M : CoreExpr × EnvStack × Mem → CoreExpr × EnvStack × Mem → Prop`
(Step.lean) is a hand-written small-step relation over the engine's
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
c.2.1`, the memory is `c.2.2`, the file, extern map and run state are
`M`'s), the engine's step list read by the loop body is a singleton `s`,
`s` is advanceable, and the shipped `advance_step` on it is one active,
wakeup-free transition to the state embedding `c'`:

```lean
def CerberusRound (M : MachineCtx) (c c' : Config) : Prop :=
  ∀ dst : driver_state, M.Embeds dst c →
    ∃ s : core_step2,
      step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
        (M.parent, M.thread c.1 c.2.1) = [s] ∧
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
(Soundness.lean) is a PROOF DEVICE of the `driveU` lane and appears in
no export's statement (the trust rule of 2026-09-02).

The certification theorem, on the fragment `Frag` at a cons-shaped
environment and `esize e ≤ lemDefaultFuel`:

```lean
theorem engine_step_matchU {M : MachineCtx}
    {e e' : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    {ρ' : EnvStack} {σ σ' : Mem}
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel)
    (hs : Step M (e, ev0 :: evs, σ) (e', ρ', σ')) :
    CerberusRound M (e, ev0 :: evs, σ) (e', ρ', σ') := by
```

Note the successor thread `M.thread e' ρ'`: the engine's successor
carries `M`'s immutable fields, `current_loc` included — which is why
the fragment is annotation-free (§7). `cerberusRound_classify` (plus
`hwf : M.SeqWF`) sorts every `Frag` configuration into `value_done` (a
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
    (∃ c', Step M (e, ev0 :: evs, σ) c') ∨
    ShippedRefusal M (e, ev0 :: evs, σ) ∨ OpenRound M (e, ev0 :: evs, σ)
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
`LaunchCoh` also mints the cursor and grants `allocCap`). The engine
face, `engine_adequacyU` (Adequacy.lean): for `Frag e₀` with `pot e₀ ≤
lemDefaultFuel` at a `SeqWF` context whose registered bodies are in
`Frag` with their static bounds, `Coh M.tagDefs σ₀ m₀`, and an Iris
proof that the footprint cells entail the WP with the readout post `∀ σ'
ns κs nt, stateInterp σ' ns κs nt ={⊤, ∅}=∗ ⌜ψ w.val σ'⌝`: for every `n`,
`driveU M aids n (M.thread e₀ (ev00 :: evs0)) σ₀` is never `.killed r`,
never `.stuck`, and `.done v σ'` implies `ψ v σ'` — by
`drive_classifyU`: every drive step is discharged by the device lemma
`outcomesU_of_step` (Soundness.lean; the shipped-round certification
`engine_step_matchU` is not consumed by this lane — §5 above),
refusals contradict `NotStuck`, and the value protocol
composes REMOVE-ANNOT with PROGRAM-DONE. `project_triple_pure` is this
theorem plus `stateInterp_readout` (Rules.lean) on the Iris post. The
total half, `wpt_engine_boundU` (TotalAdequacy.lean): from `blockSpecsT
M Ls (readoutPost ψ) ∗ wpt M Ls k (readoutPost ψ) e₀ (ev00 :: evs0)`, `∃
v σ', driveU M aids k (M.thread e₀ (ev00 :: evs0)) σ₀ = .done v σ' ∧ ψ v
σ' ∧ (stateInert e₀ = true ∧ StateInertLabels M → σ' = σ₀)` — the
judgment's budget is drive length, proved once by induction on the
budget with the device lemma `outcomesU_of_step` discharging one
`driveU` step per unit (`wpt_drive_aux`). Both faces, `engine_adequacyU` and
`wpt_engine_boundU` (and their `_alloc` twins), are over `driveU` and
therefore PROVISIONAL (§1.3).

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
lemDefaultFuel`, the production loop's own budget for `k` rounds plus
the done-recording and drain iterations — below it the production value
is the opaque `fuelExhausted` leaf (§1.3). The theorems hold for every
supply `sup` because the fragment never reads it. These production
statements are the root-of-trust exports (§1.3).

## 6. Reading the audit

`CerberusHeapLang/Audit.lean` is the last import of the library root, so
`lake build` elaborates it and a failure is a red build. It asserts, in
order: (1) exact pins — every name in `trioExports` (159 theorems at the
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
`axiom` declaration. The pinned semantics tree does contain one known
generated admission: two `(sorry : String)` terms in the debug-log
branch of `auxAddToRfLoad` in the generated concurrency model
(`Cmm_op.lean`), which Lean reports as `declaration uses sorry` during
the build. It is outside every current export cone — the banned-axiom
sweep establishes that `sorryAx` reaches no `CerberusHeapLang`
constant — and concurrency is out of scope here; it must be closed
upstream or separately bounded before any concurrency or whole-engine
claim is made on this semantics (reported to the cerberus-lean team,
`../../docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md`).
What the sweep does not certify: the scope qualifiers (parts of the statements),
the readout predicates' faithfulness (§2 — read them), coverage (the
capability manifest's job). The build command, its expected tail and
the `#print axioms` recipe are in the README, "How to build and verify".

## 7. What is deliberately out, and why

- **`kill`/free and procedures.** The classical logic's dispose rule and
  procedure specifications (incl. recursion) are the next two additions.
  Their absence is structural, not hidden: no liveness token exists
  because metadata is immutable (§4); `MachineCtx.SeqWF` (empty call
  stack) is a premise wherever a general context appears.
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
  lemDefaultFuel`.
- **A C frontend.** Programs enter as authored Core in a synthetic
  one-procedure file.
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
- **Partial correctness over the shipped driver.** The partial lane is
  stated over `driveU` and labelled PROVISIONAL (§1.3) until the
  cerberus-lean fuel-exhaustion request lands; no package-side driver
  works around the opaque fuel arm.
- **A global memory well-formedness invariant.** Freshness is
  footprint-relative (§4); the invariant is registered for the
  malloc/free arc.
- **Parametric semantics interfaces.** Not adopted: the rules are proved
  directly against `Step` and the memory state, as RefinedC proves its
  memory rules by inversion.

Records — design history, decision provenance, the audits and reviews —
are the dated files under [`docs/`](.) (the README's "Records" section
lists the current ones) and `../docs/DECISIONS.md`; the README carries
the claims surface, the trust diagram and the register of divergences
and limitations.
