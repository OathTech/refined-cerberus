# A walkthrough: this is the theorem, this is how to read it

For a reader who knows separation logic and roughly what Iris is, and
has never heard of Cerberus. Seven sections: the claim and one exhibit
read end to end (§1); the trust tiers (§2); the logic, rules quoted
verbatim (§3); the memory-model view (§4); how the logic is attached to
the engine (§5); what the in-build audit asserts (§6); what is
deliberately out (§7). Everything in a `lean` block is quoted verbatim
from [`CerberusHeapLang/`](../CerberusHeapLang/) at this checkout; every
claim names a theorem you can `grep`. One reading convention: several
quoted declarations sit inside a Lean `section` whose `variable`s are
part of the statement without appearing on the theorem line (Lean
adds them as leading binders). Wherever that is the case, a line
"Section variables not shown" under the quote lists them with the
file:line where they are declared — nothing else is hidden.

**Cerberus** (Memarian, Sewell, et al.) is a semantics for C: it
elaborates C into a small typed functional intermediate language,
**Core**, and gives Core an executable operational semantics — an
interpreter with an explicit memory object model (allocations, byte
representations, pointer **provenance**: which allocation a pointer
derives from, policing arithmetic and comparisons as the C standard
does). The engine here is the Lean 4 port of that semantics
(cerberus-lean), generated from the same Lem model as the OCaml
implementation and differentially validated against it (README, "What
you are asked to take on faith"). This package puts a classical
separation logic over a fragment of Core, on iris-lean, and proves that
what the logic says is what the engine does.

## 1. The claim, and one exhibit read end to end

### 1.1 The shape

The target ([USER 2026-09-02], verbatim): `s |= P && core_exec(prog, s)
~~> term ==> term = some(s') && s' |= Q`, for P and Q "just memory +
pure properties". Its realization is the boring triple over engine
states (`Adequacy.lean`):

```lean
def MemTripleU (M : MachineCtx) (ρ : EnvStack) (e : CoreExpr) (P : CellMap)
    (post : CellMap → value → Mem → Prop) : Prop :=
  ∀ (R : CellMap), P ##ₘ R →
  ∀ (σ : Mem), Sat M.tagDefs σ (Iris.Std.PartialMap.union P R) →
  ∀ (n : Nat) (aids : Nat → Nat), esize e + n ≤ lemDefaultFuel →
    (∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      esize cont + n ≤ lemDefaultFuel) →
    (∀ r, driveU M aids n (M.thread e ρ) σ ≠ .killed r) ∧
    (driveU M aids n (M.thread e ρ) σ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem), driveU M aids n (M.thread e ρ) σ = .done v σ' →
      post R v σ')
```

Read it against the shape. `σ : Mem` is a real engine memory state
(`CerbMem.MemState`); `Sat M.tagDefs σ (P ∪ R)` is `s |= P` with the
frame built in — `P` is the footprint (a finite map of allocation-rooted
cells), `R` an ARBITRARY disjoint rest, and `Sat` says the memory really
carries every cell (live, writable, in bounds, exactly those bytes,
pairwise disjoint — §2 prints it). `driveU M aids n (M.thread e ρ) σ`
is `core_exec`: the sequential driver's own round loop, `n` rounds of
`{step_ctx → dischargeStep}`, at every action-id supply `aids`. The
conclusion: the engine never kills (no undefined behaviour, no error
kill) and never gets stuck off-protocol; and whenever it delivers
(`.done v σ'`), `post R v σ'` — `s' |= Q` with `R` handed to the post
so the frame can be read back. Fuel exhaustion (`.more`) carries no
obligation: partial correctness. The fuel hypotheses are the engine's
own `get_ctx` budget (`lemDefaultFuel = 10^6`), for the program and for
every registered label body — an honest artifact of the interpreter,
stated rather than absorbed.

There is no Iris in `MemTripleU`. The theorem that produces one from an
Iris triple is THE PROJECTION:

```lean
theorem project_triple {GF : BundledGFunctors} [SpikeGpreS GF]
    {M : MachineCtx} (hwf : M.SeqWF)
    (hQf : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      Frag cont)
    {e : CoreExpr} (hfrag : Frag e) (ev0 : Fmap sym value) (evs : List (Fmap sym value))
    (P : CellMap) (Q : ∀ [SpikeGS .hasLC GF], CoreRVal → IProp GF)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ P, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c)) ⊢
        WP (⟨e, ev0 :: evs, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ {{ w, Q w }}) :
    MemTripleU M (ev0 :: evs) e P (fun R v σ' => ∀ ψ : Prop,
      (∀ [SpikeGS .hasLC GF] (w : CoreRVal), w.val = v →
        ∀ (mm : SpikeHeapF MetaCell) (mb : SpikeHeapF CerbMem.AbsByte)
          (mk : SpikeHeapF AllocCursor), CohG σ' mm mb mk →
        iprop(Q w ∗ ([∗map] i ↦ c ∈ R, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c) ∗
          metaInterp mm ∗ byteInterp mb) ⊢ (⌜ψ⌝ : IProp GF)) → ψ) := by
```

Hypotheses: a sequentially well-formed context (`SeqWF`: empty call
stack, startup thread), the program and every registered label body
inside the fragment `Frag`, and an Iris triple `hwp` — cell ownership
of the footprint entails the WP of the program with ANY Iris post `Q`.
Conclusion: the boring triple whose post is "every pure `ψ` that `Q w ∗
frame-cells ∗ interpretation` entails under any coupling witness
`CohG σ' …`". That obligation is the one place Iris vocabulary survives
in a projected statement, and clients never open it: the
pure-consequence lemmas discharge it for the points-to shapes
(`cellOwn_consequence`, `pointsToCell_consequence`,
`cellsOwn_consequence`, `cells_consequence`, and the combinators
`sep_`/`or_`/`exists_`/`pure_consequence`), turning it into `CellCoh σ'
i c` — bytes, allocation metadata and bounds of the final memory. The
cells-shaped triple `SemTripleU` (post = a footprint `Q` with `Sat σ'
(Q ∪ R)`) is `MemTripleU` at one particular post (`SemTripleU_iff_Mem`,
definitional), and `semantic_triple_soundU` — the older headline — is
`project_triple` at that post.

**The projection's exact scope: two theorems.** `project_triple`'s
precondition is footprint ownership ALONE — a client whose Iris
precondition also carries `allocCap` (every program that `create`s,
§3.3) cannot reach `MemTripleU` through it, because the launch that
grants `allocCap` needs more of the initial memory than `Sat`. The
allocating case is the second theorem:

```lean
def MemTripleU_alloc (M : MachineCtx) (ρ : EnvStack) (e : CoreExpr) (P : CellMap)
    (reqs : List AllocReq) (post : CellMap → value → Mem → Prop) : Prop :=
  ∀ (R : CellMap), P ##ₘ R →
  ∀ (σ : Mem), LaunchCoh M.tagDefs σ (Iris.Std.PartialMap.union P R) reqs →
  ∀ (n : Nat) (aids : Nat → Nat), esize e + n ≤ lemDefaultFuel →
    (∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      esize cont + n ≤ lemDefaultFuel) →
    (∀ r, driveU M aids n (M.thread e ρ) σ ≠ .killed r) ∧
    (driveU M aids n (M.thread e ρ) σ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem), driveU M aids n (M.thread e ρ) σ = .done v σ' →
      post R v σ')
```

```lean
theorem project_triple_alloc {GF : BundledGFunctors} [SpikeGpreS GF]
    {M : MachineCtx} (hwf : M.SeqWF)
    (hQf : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      Frag cont)
    {e : CoreExpr} (hfrag : Frag e) (ev0 : Fmap sym value) (evs : List (Fmap sym value))
    (P : CellMap) (reqs : List AllocReq) (Q : ∀ [SpikeGS .hasLC GF], CoreRVal → IProp GF)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ P, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c) ∗
        allocCap M.tagDefs reqs) ⊢
        WP (⟨e, ev0 :: evs, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ {{ w, Q w }}) :
    MemTripleU_alloc M (ev0 :: evs) e P reqs (fun R v σ' => ∀ ψ : Prop,
      (∀ [SpikeGS .hasLC GF] (w : CoreRVal), w.val = v →
        ∀ (mm : SpikeHeapF MetaCell) (mb : SpikeHeapF CerbMem.AbsByte)
          (mk : SpikeHeapF AllocCursor), CohG σ' mm mb mk →
        iprop(Q w ∗ ([∗map] i ↦ c ∈ R, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c) ∗
          metaInterp mm ∗ byteInterp mb) ⊢ (⌜ψ⌝ : IProp GF)) → ψ) := by
```

Read against `project_triple`: the Iris precondition gains
`allocCap M.tagDefs reqs` (the capacity for the finite request plan
`reqs`); the conclusion is `MemTripleU_alloc`, which is `MemTripleU`
with ONE change — the launch premise `LaunchCoh M.tagDefs σ (P ∪ R)
reqs` (Adequacy.lean) in place of `Sat M.tagDefs σ (P ∪ R)`. `LaunchCoh`
is `Sat` (its `coh` field) plus the allocator-health facts that make
`create` safe: every allocation id from the engine's `nextAllocId`
upwards is unallocated and not dead, every footprint cell sits at or
above the downward cursor `lastAddress`, the plan fits the actual
`⟨lastAddress, nextAllocId⟩` (`PlanFits`), and `lastAddress ≤ 2^64`.
None of that follows from `Sat` — a memory can carry the footprint
with its allocator cursor sitting on top of those very cells — which
is why the allocating triple is a separate definition rather than
`MemTripleU` with a side condition. The frame `R` is built in exactly
as before; the postcondition is the same "every pure consequence of
`Q w ∗ frame-cells`". `MemTripleU` implies `MemTripleU_alloc` at every
plan (`MemTripleU_alloc_of_MemTripleU`): the allocating triple is the
weaker conclusion, paid for by the stronger launch premise. So, the
scope in one sentence: the ARBITRARY Iris postcondition is the general
part of both theorems; the precondition is either footprint cells
(`project_triple`) or footprint cells ∗ `allocCap reqs`
(`project_triple_alloc`) — no other precondition shape is projected
(fractional cells, views and persistent metadata are first traded for
whole cells by the assertion laws, §4).

**How an allocating program gets a boring triple, concretely.** State
the plan, prove the Iris triple from `allocCap` with `wps_create`/
`wpt_create`, and launch from a memory whose `LaunchCoh` you can
prove — for closed programs that is the production cold-start memory
`prodMem₀` (`prodMem₀_launchCoh reqs`, ProdEntry.lean, needs only
`PlanFits` for your plan, a closed arithmetic fact). The worked
instance is `struct_create_store_adequacy` (StructExhibit.lean): `lets
p = create(8, long[2]) in lets v = 5 in store(int, p, v)` at footprint
`∅`, frame `∅`, plan `[⟨8, structTy⟩]`; it is `project_triple_alloc` at
`spikeCtx` with the Iris post of `struct_create_store_wps`, the
projected obligation discharged by `exists_consequence` ∘
`sep_consequence` ∘ `pointsToCell_consequence`, concluding that the
engine never kills, never derails, and any delivered `(v, σ')` has
`v = Vunit` with the initialized struct at an existential id/address
in `σ'`. Its statement is the `MemTripleU_alloc` body unfolded at that
profile — as the loop exhibits (`list_reverse_certified`, …) state
the `MemTripleU` body unfolded at theirs; only `exhibitA/B/C_semantic`
are stated as `SemTriple` values.

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

`save` registers the label `loop` with its parameters and runs the
body; `run loop(cur, n)` is the jump — it DISCARDS its evaluation
context and restarts the registered continuation (the loop's back
edge). `lets pat = e1 in e2` is Core's strong sequencing `Esseq`, with
a symbol, a wildcard, or a `Specified(n)` pattern (loads return
`Specified(v)` or `Unspecified`). `store`/`load` go through the engine's
memory model (`storeM`/`loadM`: liveness, bounds, writability, type
checks, byte serialization) — a failed check is undefined behaviour and
the engine KILLS the execution; the logic's job is to prove that cannot
happen. `memop(PtrEq, …)` is the memory model's own provenance-aware
pointer equality — the null test uses it, no flags smuggled in (how
the rule stays clear of the comparison's differing-provenance
nondeterministic fork: §4, "The `PtrEq` memop").
`array_shift(p, long, 1)` advances `p` by one `long` inside the same
allocation, provenance preserved. Each node is ONE allocation of type
`long[2]` (`nodeTy`): value at offset 0, next pointer at offset 8; NULL
is the engine's null pointer (eight zero bytes; the round trip is proved
against the engine's serializer). The registered body `lrBody`
(ListRevExhibit.lean) is a real term of the engine's generated
expression type `CoreExpr`; metadata the exhibit does not care about
(locations, annotations, base-type tags, the memory order) is
universally quantified.

**The production statement** (`ProdLoopExhibit.lean`): a self-contained
program that BUILDS a two-node chain with the engine's own `create` and
then runs the loop above, on the SHIPPED pipeline from the cold start.

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

No section variables: every binder of this theorem is on the theorem
line. `CerbND.runND (_root_.drive …) (initial_driver_state sup file fs).1`
is exactly the composite the cerberus-lean executable runs (`_root_.drive`
is the ENGINE's driver entry, hence the `_root_`). The theorem
quantifies over nothing but the file-system state, argv and the entry's
symbol supply `sup` (the fragment never reads it): the run IS the
singleton Active execution, its delivered value heads a chain seeded as
the REVERSED list `[(i₂,2),(i₁,1)]` at EXISTENTIAL allocation ids —
the logic binds the pointers, the engine picks them — and the final
production memory (`dst'.layout_state`) satisfies that footprint. No
`drive`, no `Step`, no Iris in the statement.

**The drive-lane statement** underneath it, `list_reverse_certified`
(ListRevExhibit.lean), is the general one — any chain, any frame. Its
hypotheses: `ns : List (Int × Int)` pairs each node's ALLOCATION ID with
its value; `m₀ : CellMap` is a chain footprint for `ns` from `head`
(`SeedChain m₀ head ns`, §2); `R : CellMap` is an arbitrary footprint
with `m₀ ##ₘ R`; `σ₀ : Mem` is any engine memory with `Sat fmapEmpty σ₀
(m₀ ∪ R)`; `hlib : CerbLocation.isLibraryLocation loc = false` (the
action location is not a library location — a constructor argument of
`Frag.store/load/create`, the frozen well-formedness the README
registers); the engine's fuel budget as the pair `6 + nsteps ≤
lemDefaultFuel`, `5 + nsteps ≤ lemDefaultFuel` (program and label body);
and, as section variables not on the theorem line
(ListRevExhibit.lean:1153-1154), the metadata `loc ann ra mo` and the
base-type tags `pbty cbty bbty nbty ubty`, all universally quantified.
Its conclusion: `driveJ rs aids
nsteps (procThread lrProcSym prog [fmapEmpty]) σ₀` is never `.killed r`,
never `.stuck`, and whenever it is `.done v σ'` there are `p'` and `Q`
with `v = ptrVal p'`, `SeedChain Q p' ns.reverse`, `∀ k, (get? Q
k).isSome ↔ (get? m₀ k).isSome`, `Q ##ₘ R` and `Sat fmapEmpty σ' (Q ∪
R)`. That is: driving the engine (`driveJ` = `driveU` at the
proc-carrying context with the label map) never kills or derails, and
any delivered value is a pointer heading a footprint seeded as
`ns.reverse` — the SAME allocation ids in reversed order, each node still
carrying its own value (in-place, literally: only the next fields
moved); the footprint-equality conjunct pins the node set on the actual
maps (nothing allocated, nothing leaked); and the frame comes back
VERBATIM. `list_reverse_certified_total` has the same conclusion as an
unconditional `.done` equation at fuel `13 * ns.length + 7`, no fuel
hypotheses (it keeps `hlib` and the same section variables);
`list_reverse_terminates` is strong normalization of the Iris relation
(no `hlib`, no fuel); `list_reverse_demo` instantiates a 3-node chain
with every DECODE side condition (`nodeValDec`/`nodeNextDec` of the
seeded bytes) by `rfl` — it still carries `hlib`, the fuel pair and
the arbitrary frame `R`.

**The Iris triple** it comes from. The representation predicate is
plain structural recursion, identity-indexed, no step-indexing:

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
[SpikeGS hlc GF]` (ListRevExhibit.lean:395). And the specification, at
the statement judgment `wps` (§3), with an arbitrary frame `RF` carried
across every back edge by the framed label context:

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

Section hypotheses not shown (ListRevExhibit.lean:885-893): `{hlc : HasLC}
{GF : BundledGFunctors} [SpikeGS hlc GF]`, the metadata `loc ann ra mo`,
the base types `pbty cbty bbty nbty ubty`, the node list `ns`, and —
the load-bearing one — `(p : sym) (rs : core_run_state) (hQ : LabeledAt
rs p (lrQ loc ann ra mo pbty cbty bbty nbty ubty))`: the Iris triple
holds at the machine context `procCtx p rs` whose label table IS the
loop's (`lrQ` maps the label `loop` to its parameters and body), not
at a context-generic `M`. That tie is what lets `wps_run` stop
tracking at the back edge (the jump resolves against `M.labels`, and
`procCtx_labels hQ : (procCtx p rs).labels = lrQ …` makes the lookup
compute). §3.5 shows how a client builds `rs` and discharges `hQ`.

Read: `{ isList head ns ∗ RF } reverse { ret p'. isList p' ns.reverse ∗
RF }`. The unframed proof `lr_wps` is textbook: loop invariant `isList
prev reversed ∗ isList cur rest` with `ns = reversed.reverse ++ rest`
(`lrLs`, the per-label precondition), each construct discharged by its
own rule — `wps_save` at entry, `wps_seq_sym` + `wps_memop_eval` +
`wps_memop_ptreq` for the null test, `wps_if_true`/`wps_if_false`,
`wps_seq_spec` + `wps_load_eval` + `wps_load_cell_at` (the typed
sub-range load, wrapped as `wps_load_node_field`) for the next-field
load, `wps_seq` + `wps_store_eval` + `wps_store_cell_at`
(`wps_store_node_field`) for the store, `wps_pure` at the exit,
`wps_run` at the back edge (which only asks for the label's
precondition), `blockSpecs_intro` to assemble the registered body's
specification; the frame is then `wps_frame_labels` applied once. The
path to the engine: `wps_sound_frame` collapses to the base WP,
`engine_adequacyJ` lands the drive-lane statement; for the production
theorem, `lrProd_wpt` proves the whole build-and-reverse program at the
TOTAL judgment (`wpt_create` twice from a two-request `allocCap` plan,
the generic subrange stores through the bound pointers, then the loop
proof consumed verbatim at the existential ids via `wpt_mono_Ls`), and
`wpt_driver_done_alloc` → `prod_run_eqJ` supply every pipeline arrow.

## 2. The trust tiers

**Two trust claims** ([USER 2026-09-02], DECISIONS.md). (1) The
closed-program exports — `MemTripleU`/`SemTripleU` instances, the
`*_certified` and `*_production` theorems — have Iris-free statements:
their referents are cerberus-lean's semantics plus the pure readout
predicates below. iris-lean appears only inside kernel-checked proof
terms and contributes no axiom (`Audit.lean` pins every export's cone
to `propext`, `Classical.choice`, `Quot.sound`): for these statements it
is CHECKED, not trusted. (2) The reusable rules are stated in Iris
assertions; that must-read set — the specification idiom — is the one
sense in which iris-lean is in the trust base: definitions to read, not
axioms to accept.

**The arrows, in order** (the README's trust diagram; every theorem
trio-exact):

1. The engine's `step_ctx` and the driver's request discharge are the
   semantics. `CerberusRound M aid` (Round.lean) names one discharged
   round as a relation; `Step M` (Step.lean) is the hand-written
   mirror. `engine_step_matchU`: wherever the mirror steps on the
   fragment, the engine's round is exactly that step;
   `step_iff_cerberusRound`: two-sided; `cerberusRound_classify`: every
   `Frag` configuration is a bare value (PROGRAM-DONE), an annotated
   value (REMOVE-ANNOT), a two-sided step, or mirror-stuck.
2. `instance : Language CoreRt Mem Empty CoreRVal` (Lang.lean) runs
   `Step` as iris-lean's primitive step.
3. `SpikeState` (Heap.lean) is the state interpretation over the real
   `MemState`, coupled by `CohG` to three ghost heaps; the assertions
   are built on them (§4).
4. `wp_store`, `wp_load`, … (Rules.lean): one WP unfolding against
   `Step`, with the real `storeM`/`loadM` run inside the proof.
5. `wps`/`wpt` (Wps.lean, Wpt.lean) and their rule sets; `wps_sound`
   (Löb) and `wpt_sound` (budget induction) collapse them into the base
   WP and Iris `TotalWeakestPre`.
6. Partial lane: `spike_step_adequacy` = iris-lean's
   `wp_strong_adequacy_gen` with the ghost state CONSTRUCTED
   (`genHeap_init`), `launchResources` under `LaunchCoh` minting the
   allocator cursor and granting `allocCap`. Total lane: NO Iris
   adequacy in the cone — the drive equations are proved by budget
   induction against the engine (`wpt_drive_aux`: `engine_step_matchU`
   discharges one engine step per budget unit, §5); iris-lean's
   `twp_total` feeds only `wpt_strongly_normalizing`.
7. `engine_adequacyU` (and `engine_adequacyU_alloc`, launched through
   `launchResources`) → `driveU` never kills/derails, readout at
   `.done`; `project_triple` → `MemTripleU`; `project_triple_alloc` →
   `MemTripleU_alloc`; `wpt_engine_boundU/J`, `wpt_engine_boundU_alloc`
   → `driveU … k = .done v σ'` unconditionally.
8. `loop_step_frag`, `driver2_done`, `finalize_done`
   (DriverCollapse.lean), `wpt_driver_done(_alloc)` (ProdLoop.lean),
   `prod_run_eqJ` (ProdEntry.lean): the shipped scheduler, ND monad and
   readout collapsed onto the drive, proved from the driver's own round
   functions.
9. The production exports, then the projection back to boring
   statements.

**What you take on faith**: the Lean kernel; that cerberus-lean's
generated definitions are the semantics you care about (the
differential validation against the OCaml oracle — the README's "What
you are asked to take on faith" carries the lanes and the pointer to
the authoritative record); and the pure readout predicates below.

**Under which Cerberus configuration.** Cerberus is switch-configured
(PNVI variants, strict pointer arithmetic, CHERI, …) and mode-
configured (random/exhaustive scheduling, concurrency), and the Lean
port declares those reads as KERNEL-OPAQUE constants (`opaque … ` with
`@[implemented_by]` bodies: `CerbGlobal.has_switch`, `is_PNVI`,
`is_CHERI`, `has_strict_pointer_arith`, `current_execution_mode`,
`using_concurrency`, … in generated/CerbGlobal.lean:113-144;
`CerberusImpl.typeof_enum`/`register_enum` for the implementation's
enum typing, CerberusImpl.lean:67/237). A kernel-opaque constant enters
no axiom cone and cannot be unfolded by any proof, so a theorem whose
cone contains one holds for EVERY value of it. What the statements pin
and the tree shows (measured — the README's trust story lists every
opaque constant reached by the 120 export cones, at the time of writing): the tag-definition
environment is `fmapEmpty` and concurrency is OFF (`_root_.drive
fmapEmpty false …` in every production statement — `drive tagDefs
with_concurrency file args`, Driver.lean:518; `spikeCtx`/`procCtx`/
`rsCtx` carry `tagDefs = fmapEmpty`); the Lean `CerbMem` reads NO
`CerbGlobal` constant (0 references), so `loadM`/`storeM`/
`allocateObject`/`eqPtrval` are switch-independent by construction —
the memory model the exports are about is the un-switched one the
OCaml oracle is validated against; the only configuration read on a
proved path, the driver's `current_execution_mode`, is discharged by
`cases` on the opaque test in `driver2_done` (DriverCollapse.lean:929-985,
`cases hmode` at :967: both scheduler branches reduce to the same
singleton pick); `has_switch`/`is_CHERI`/`using_concurrency` are in the
production-lane cones only through the shipped driver's code
(`core_thread_step2`'s procedure-call arm, `Core_run_aux`'s
concurrency-annotation helpers, `Ctype`'s pointer-size branch), on
paths the single-threaded fragment run never takes. Consequence: every
export holds under every switch setting and every execution mode, at
empty tag definitions, single-threaded. The remaining kernel-opaque
leaves in the cones — LemLib's `fuelExhaustedWith` (the `get_ctx`
budget's exhaustion sentinel) and `failwithI` (the panic channel),
`CerberusFresh.digest` — are what the fuel side condition and the
well-formedness premises keep out of range: a proof can never unfold
them, so the statements are arranged never to need to.

**Why a wrong mirror or a wrong logic cannot make a false statement
provable.** `Step`, the rules, the judgments and iris-lean are INTERIOR:
they occur in proofs and interior hypotheses, never in an exported
conclusion, and the adequacy theorems close them off. A bug there
deprives us of proofs, not of the truth of what was proved. The two
honest caveats: this is relative to the readout predicates (a wrong
`driveU` or `Sat` would make a theorem true but about the wrong thing —
which is why they are printed here), and it is fail-open for COVERAGE
(a missing mirror case makes rules silently dead, not false — which is
why the capability manifest reports per-construct coverage rather than
trusting prose).

**The readout predicates**, in full:

```lean
inductive DriveResult : Type where
  /-- fuel ran out with the machine resting here (no claim is made) -/
  | more (th : thread_state) (σ : Mem)
  /-- PROGRAM-DONE: the engine delivered a value -/
  | done (v : value) (σ : Mem)
  /-- the engine killed. `kill_reason mem_error` (Nondeterminism.lean:54)
      has three constructors. `Undef0 loc ubs` — undefined behaviour:
      from the memory model, a `mem_error` mapped through
      `undefinedFromMem_error` (Mem_common.lean:392) by `failReason`
      (CerbMem.lean:1439) — null/no-provenance/out-of-bounds/dead/
      outside-lifetime/atomic-member access, the `_Bool` trap
      representation on load, a store to a read-only allocation
      (`loadM` CerbMem.lean:1621-1664, `storeM` :1667-1730) — or from
      the Core-run layer's own `Undef` result (`liftCore_run`,
      Driver.lean:245-247). `Other err` — the non-UB memory errors: a
      store with an ill-typed memory value (`MerrOther`, :1702) and
      function-pointer access (`MerrAccess _ FunctionPtr`). `Error0 loc
      msg` — the Core-run layer's `Error` result (`liftCore_run`, same
      lines; never produced by `loadM`/`storeM`). "Never kills" below
      excludes ALL THREE, not only UB. -/
  | killed (r : kill_reason mem_error)
  /-- refusal (Step_error2 / ILLTYPED) or any off-protocol engine
      behavior -/
  | stuck

def stepOutcomes (M : MachineCtx) (aid : Nat) (th : thread_state)
    (σ : Mem) : List EngineOutcome :=
  (step_ctx M.tagDefs σ M.file M.extern M.tid (M.parent, th)).map
    (dischargeStep M.tagDefs aid M.runState σ)

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

`drive` is `driveU spikeCtx` (the straight-line profile) and `driveJ rs`
is `driveU (rsCtx rs)` (the proc-carrying profile at run state `rs`);
`procThread p e ρ` is the thread literal with current procedure `p`.

`step_ctx` is the engine's step function; `dischargeStep`
(Soundness.lean) is the sequential driver's request discharge
(`action_request_sequential2`, Driver.lean:273) projected to (thread,
memory), mirrored function by function with file:line citations; `aids`
is the driver's per-step action-id supply, ∀-quantified because the
fragment never reads it. The footprint predicates:

```lean
structure SpikeCell where
  addr : Int
  ty : ctype
  bytes : List CerbMem.AbsByte

def cellPtr (id : Int) (a : Int) : CerbMem.PointerValue :=
  .PV (.Prov_some id) (.PVconcrete none a)

structure Coh (tds : CerbTags.TagDefsMap) (σ : Mem) (m : SpikeHeapF SpikeCell) : Prop where
  cells : ∀ id c, get? m id = some c → CellCoh tds σ id c
  disj : ∀ id1 id2 c1 c2, id1 ≠ id2 → get? m id1 = some c1 →
    get? m id2 = some c2 → cellsDisjoint tds c1 c2

abbrev Sat (tds : CerbTags.TagDefsMap) (σ : Mem) (m : CellMap) : Prop := Coh tds σ m
```

`CellCoh tds σ id c` (Heap.lean, six fields) says: allocation `id` is
not dead; the allocation table has it at base `c.addr`, size
`sizeofCtype tds c.ty`, type `c.ty`, writable; the type is non-atomic;
`c.bytes` has that length and `readBytesFrom σ c.addr … = c.bytes`; and
the image decodes the same at any union-member/function-pointer side
tables. The chain footprint of §1.2:

```lean
def SeedChain : SpikeHeapF SpikeCell → CerbMem.PointerValue →
    List (Int × Int) → Prop
  | m, p, [] => m = (∅ : SpikeHeapF SpikeCell) ∧ p = nullNode
  | m, p, nd :: ns => ∃ (aN : Int) (q : CerbMem.PointerValue)
      (bs : List CerbMem.AbsByte) (m' : SpikeHeapF SpikeCell),
      p = cellPtr nd.1 aN ∧ 0 < aN ∧ aN < 2 ^ 64 ∧ bs.length = 16 ∧
      nodeValDec fmapEmpty bs nd.2 ∧ nodeNextDec fmapEmpty bs q ∧
      ((Iris.Std.PartialMap.singleton nd.1 (SpikeCell.mk aN nodeTy bs) :
        SpikeHeapF SpikeCell)) ##ₘ m' ∧
      m = Iris.Std.PartialMap.union
        (Iris.Std.PartialMap.singleton nd.1 (SpikeCell.mk aN nodeTy bs)) m' ∧
      SeedChain m' q ns
```

`nodeValDec`/`nodeNextDec` say the node's byte ranges decode — by the
ENGINE's decoder — to the value resp. the next pointer. The only
non-engine vocabulary left in the exported statements is these
definitions, the authored programs, and iris-lean's finite-map library
(`Iris.Std.PartialMap.get?`/`union`/`##ₘ` — the type of footprint
maps, not program-logic machinery).

## 3. The logic

Two label-context judgments over iris-lean's `WP` — the partial `wps`
and the total `wpt` — for programs with `save`/`run`, and beneath them
the base stratum: the two small axioms `wp_store`/`wp_load` stated at
the raw `WP` over the runtime tuple `⟨e, ρ, M⟩ : CoreRt` (expression,
live environment stack, machine context), generic in `M` and `ρ`. The
statement strata restate the small axioms with the label context and
prove them the same way; frame, consequence and sequencing are stated
there (§3.2), because at the raw WP sequencing is false once labels
are populated — a jump discards the sequencing context.

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

Section variables not shown: `{hlc : HasLC} {GF : BundledGFunctors}`
(Rules.lean:112; the instance `[SpikeGS hlc GF]` is on the line). The
classic `{p ↦ (ty, bs)} store(ty, p, v) {p ↦ (ty, bytes-of v)}`:
full ownership of the cell entails the WP of the store, whose post
returns the cell with its bytes replaced by the engine's own
serialization of `v` (`memValueToBytes`). The precondition excludes
undefined behaviour — `storeM` has a dozen kill arms (dead allocation,
out of bounds, ill-typed, atomic member, …) and ownership plus the two
typing premises defeats every one, which is what makes "the engine
never kills" provable downstream. It is a small axiom in the original
sense: it mentions only the cell the store touches. The load:

`wp_load` (Rules.lean) is the same shape at any fraction `dq` —
`pointsToCell M.tagDefs pv dq ty bs ⊢ WP ⟨loadExpr loc ann ty pv mo, ρ, M⟩
@ s; E {{ w, ∃ fp, ⌜w = ⟨SpikeVal.annot [DA_pos [] fp] (loadedVal M.tagDefs
pv ty bs), ρ, M⟩⌝ ∗ pointsToCell M.tagDefs pv dq ty bs }}` under `(htrap :
cellLoadTrap M.tagDefs ⟨addrOf pv, ty, bs⟩ = false)` — delivering the
engine's own decode of the cell (`loadedVal`); `htrap` excludes the `_Bool` trap-representation kill,
the one `loadM` failure ownership alone cannot rule out. Both are
proved, not assumed: one WP unfolding against `Step`, running the real
`storeM`/`loadM` under the coupling invariant. The statement-stratum
forms (`wps_store`, `wps_load`, the typed-subrange `wps_load_at`/
`wps_store_at` over views, and the `wpt_` counterparts) reuse the same
engine seams (`storeM_success`, `loadM_success`).

### 3.2 Frame and consequence

At the raw WP the frame is iris-lean's own `wp_frame_r` and
consequence its `wp_mono`/`wp_wand`; the logic states them where the
programs live, at the statement strata. There the frame must also
cross back edges, which is what framing the LABEL CONTEXT achieves:

```lean
abbrev frameLs (R : IProp GF) (Ls : LabelSpec GF) : LabelSpec GF :=
  fun l vs ρ => iprop(Ls l vs ρ ∗ R)

theorem wps_frame_labels {Ψ : SpikeVal → EnvStack → IProp GF} (R : IProp GF)
    (e : CoreExpr) (ρ : EnvStack) :
    wps M Ls Ψ e ρ ⊢
      iprop(R -∗ wps M (frameLs R Ls) (fun w ρ' => iprop(Ψ w ρ' ∗ R)) e ρ) := by
```

Section variables not shown (Wps.lean:120, 197-198; the same for every
`wps_*` rule quoted here): `{hlc : HasLC} {GF : BundledGFunctors}
[SpikeGS hlc GF] {M : MachineCtx} {Ls : LabelSpec GF}` — the rules are
generic in the machine context and the label specification. Value
exit: the frame joins the postcondition; jump: it joins the
label's precondition; step: Löb. `blockSpecs_frame` frames the block
specifications the same way and `wps_sound_frame` is the derived
whole-loop form; `wpt_frame_labels`/`frameLsT`/`blockSpecsT_frame` are
the total analogues (budget induction, no Löb). This is how the list
and tree exhibits get their arbitrary frame `R` without mentioning it
in the invariant. Consequence at the strata: `wps_wand`, `wps_fupd`;
`wpt_mono`, `wpt_mono_k`, `wpt_mono_Ls`.

### 3.3 Allocation

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

(Section variables as in §3.2.) Capacity for the plan `req :: rest`
buys one `create` of `req`; the
continuation receives an EXISTENTIAL fresh pointer with full whole-cell
ownership at the unspecified byte image, the remaining capacity, and
the pointer's pure machine-address bounds. Nothing in the statement
names the allocator's cursor. `wpt_create` is the same at the total
stratum with the derived cost bound `2 ≤ k`. Why `allocCap` exists at
all — the allocation-failure policy — is §4.

### 3.4 One loop rule, and the total judgment

The partial judgment `wps M Ls Ψ e ρ` is a guarded fixpoint (iris-lean's
own `fixpoint` over a contractive `wps.pre`) with THREE clauses — value,
jump redex, step. `Ls : LabelSpec GF` (`sym → List value → EnvStack →
IProp GF`) gives each registered label a precondition over its argument
values and the jump-time environment. The jump rule:

`wps_run` (Wps.lean): under `(hl : lookupLabel M.labels l = some (params,
cont))` and `(hvs : evalPexprs M.tagDefs M.extern (ev0 :: evs) pes = some
vs)`, `Ls l vs (ev0 :: evs) ⊢ wps M Ls Ψ (Expr a (Erun ra l pes)) (ev0 ::
evs)`. The label resolves, the arguments evaluate (by the pure evaluator,
certified against the engine's), the label's precondition holds at
those values — and tracking STOPS: a jump's postcondition is the
label's business, so no postcondition clash forms. The loop rule
assembles the registered bodies' specifications with no Löb and no
mutual assumption:

```lean
theorem blockSpecs_intro {Ψ : SpikeVal → EnvStack → IProp GF}
    (h : ∀ l params cont vs ev0 evs,
      lookupLabel M.labels l = some (params, cont) →
      Ls l vs (ev0 :: evs) ⊢ wps (GF := GF) M Ls Ψ cont
        (bindArgs params vs (ev0 :: evs))) :
    ⊢ blockSpecs M Ls Ψ := by
```

(Section variables as in §3.2. `blockSpecs M Ls Ψ` is the persistent
conjunction of those entailments over every registered label.) Each body's own back edges
discharge against `Ls` via `wps_run`. The one Löb induction lives in the
collapse `wps_sound`: `blockSpecs M Ls Ψ ⊢ wps M Ls Ψ e ρ -∗ WP ⟨e, ρ, M⟩
@ NotStuck; ⊤ {{ w, Ψ w.w w.ρ }}`.

This is the classical label-context treatment of `goto`-like control
(de Bruin-style label assumptions), and the reason no `wp_bind` is
needed: `Erun` discards its evaluation context, so a bind rule's frame
law is false for Core, and sequencing is proved directly (`wps_seq`,
`wps_seq_spec`, `wps_seq_sym` — the jump clause is Ψ-independent, so
sequencing is a transfer).

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

def wpt [SpikeGS hlc GF] (M : MachineCtx) (Ls : LabelSpecT GF) :
    Nat → (SpikeVal → EnvStack → IProp GF) → CoreExpr → EnvStack → IProp GF
  | 0 => wpt.pre M Ls 0 (fun _ _ _ => iprop(⌜False⌝))
  | k + 1 => wpt.pre M Ls (k + 1) (wpt M Ls k)
```

Section variables not shown: `{hlc : HasLC} {GF : BundledGFunctors}`
(Wpt.lean:69; the instance is on the line). `LabelSpecT` preconditions
carry a VARIANT `m : Nat` (the classical
Floyd variant as a specification parameter — heap-resident measures
such as a chain length enter through the invariant), and the jump
clause REQUIRES `1 + m ≤ k`: the target's budget plus the jump itself
must fit the remaining budget. Since a body is verified at budget `m`
(`blockSpecsT`: `Ls l m vs (ev0 :: evs) -∗ wpt M Ls m Ψ cont …`) and
budgets only shrink along steps, every back edge strictly decreases a
well-founded measure. The total jump rule is `wpt_run` with the extra
premise `(hμ : 1 + m ≤ k)`; the collapse is

```lean
theorem wpt_sound {Ψ : SpikeVal → EnvStack → IProp GF} (k : Nat)
    (e : CoreExpr) (ρ : EnvStack) :
    blockSpecsT M Ls Ψ ⊢
      iprop(wpt M Ls k Ψ e ρ -∗
        WP (⟨e, ρ, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ [{ w, Ψ w.w w.ρ }]) := by
```

Section variables not shown (Wpt.lean:69, 147-148; the same for every
`wpt_*` rule): `{hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
{M : MachineCtx} {Ls : LabelSpecT GF}`. Into iris-lean's `TotalWeakestPre` (`[{ … }]`), by strong induction on
the budget. Deleting the decrease premise makes that induction
unjustifiable and lets a diverging program be derived —
`diverge_total_unprovable` (DivergeExhibit.lean) records that a total
derivation for the self-jump loop is `False`. The same derivation
yields both halves of total correctness (§5): termination, and an
unconditional drive equation at the budget.

### 3.5 Writing a loop client: the context, the label tie, the side conditions

What a client must supply beyond the rules, with `LoopExhibit.lean`
(the counter loop) as the worked example; `ListRevExhibit.lean` and
`FibExhibit.lean` follow the same recipe.

1. **The label map and the run state.** A `LabelMap` maps each label
   symbol to `(params, body)`: `loopQ loc ann ra mo bty xbty c :=
   fmapAddBy symCmpL loopSym ([(xSym, xbty)], loopBody …) fmapEmpty`
   (LoopExhibit.lean:95). The engine keeps label maps per procedure in
   the run state's two-level `labeled` table, so the client builds a
   `core_run_state` whose fiber at its procedure symbol is that map:
   `loopRS … := { spikeRunState with labeled := fmapAddBy symCmpL
   loopProcSym (loopQ …) fmapEmpty }` (:103).
2. **The machine context and the tie `hQ`.** The rules are generic in
   `M : MachineCtx`; a loop client works at the jump profile `procCtx p
   rs` (Step.lean:1882 — current procedure `p`, run state `rs`, empty
   extern map, `tagDefs = fmapEmpty`). Its label table is DERIVED from
   `rs`: `procCtx_labels (hQ : LabeledAt rs p Q) : (procCtx p rs).labels
   = Q` (Step.lean:1925), where `LabeledAt rs p Q` (Soundness.lean:2694)
   is the engine's own lookup `fmapLookupBy ordCompare p rs.labeled =
   some Q`. The Iris section therefore carries `variable (p : sym) (rs :
   core_run_state) (hQ : LabeledAt rs p (loopQ …))` and `include hQ`
   (LoopExhibit.lean:218-238); every `wps_run`/`wps_save` obligation
   `lookupLabel (procCtx p rs).labels l = some …` is closed by `rw
   [procCtx_labels hQ]` and then computes (:274, :314). At the engine
   face `hQ` is DISCHARGED, not assumed: `loopRS_labeledAt : LabeledAt
   (loopRS …) loopProcSym (loopQ …)` (:138) is a lookup computation
   (`fmapLookupBy_addBy_empty`, `if_pos (by decide +kernel)`), and
   `engine_adequacyJ` takes it as its first argument (:462-463). For the
   production lane the tie is derived from the SHIPPED registration
   instead (`loop_labeledAt_production`, ProdEntry.lean:536 — the label
   map `collect_labeled_continuations_NEW` computes from the synthetic
   file), so nothing about labels is hypothesized there.
3. **The label specification and the block proof.** `Ls : LabelSpec GF`
   gives each label its precondition over the jump-time argument values
   and environment (`loopLs`, :232: counter `i ∈ [0, n]`, any reachable
   `SymFrame`, the cell's two states). The body is verified once under
   `Ls` (`wps_run` at the back edge asks only for `Ls loop [i+1] ρ`);
   `blockSpecs_intro` assembles the registered bodies; `wps_save` enters
   the loop; the whole is collapsed by `wps_sound` (or the framed
   `wps_sound_frame`) into the base WP the adequacy theorems consume.
4. **The two decode side conditions.** `wps_load_at`'s `hdec : ∀ lum
   fpm, CerbMem.reconstructValue M.tagDefs lum fpm (a + off) vty bs = mv`
   (Wps.lean:1854) says the bytes decode — by the ENGINE's decoder, at
   any union-member/function-pointer side tables — to `mv`; for a
   scalar cell whose bytes are a concrete image it is `rfl`
   (`fun _ _ => rfl`, as `five_reconstruct`, StructExhibit.lean:340), and
   for symbolic bytes it is carried as a hypothesis (the array
   exhibit's `hdec`, ArrayExhibit.lean:647). `wps_create`'s `hinert : ∀ a,
   decIndep M.tagDefs a req.ty (List.replicate (sizeofCtype …) undefByte)`
   (Wps.lean:2508) is the same independence for the unspecified image
   of the new cell (`decIndep`, Heap.lean:1479 — `CellCoh`'s `dec_indep`
   field, Heap.lean:311-322, explains what it buys); for the scalar and
   array types of the exhibits it is `structTy_decIndep`/`intTy_decIndep`
   — `fun _ _ => rfl` in substance. `wps_load_at`'s `htrap : loadTrapV
   vty mv = false` excludes the `_Bool` trap representation, `rfl` for
   any non-`_Bool` value.
5. **The engine face.** `engine_adequacyJ hQ hQf e ev0 evs σ₀ m₀ hfrag
   hcoh ψ hwp n aids hfuel hQsz` (Adequacy.lean) lands `driveJ rs … ≠
   .killed / ≠ .stuck / .done ⇒ ψ` — `counter_loop_certified`
   (LoopExhibit.lean:438) is exactly this application, with `hQf`/`hQsz`
   (each registered body in `Frag`, within fuel) discharged from the
   one-label map by `loopQ_inv`. Its statement is the `MemTripleU` body
   at the profile `procCtx loopProcSym (loopRS …)`, unfolded.

## 4. The memory-model view

The ghost carrier is the donor-shaped split (RefinedC's
`ghost_state.v` heap/allocs factorization), three iris-lean `GenHeap`s
over the real `MemState`:

- a per-BYTE heap (absolute address ↦ `AbsByte`) — the ghost fragment
  of the engine's own bytemap; `bytesOwn a dq bs` is a byte range at
  fraction `dq`, splitting at any list decomposition (`bytesOwn_append`)
  and any fraction sum (`bytesOwn_fractional`), agreeing on contents
  (`bytesOwn_agree`);
- a per-ALLOCATION metadata heap (allocation id ↦ base, type, size) —
  the provenance/metadata authority: `loadM`/`storeM` success is decided
  by the allocation table, so byte content alone can never entail
  access success; `metaOwn id dq ⟨a, aty, size⟩`;
- a one-cell ALLOCATOR-CURSOR heap (`lastAddress`, `nextAllocId` — the
  two fields `allocateObject` reads and writes).

The state interpretation couples them to the memory by `CohG σ mm mb mk`
(byte cells to the bytemap; metadata cells to live, writable, typed,
non-atomic, pairwise range-disjoint allocations; the cursor, when
present, to the allocator fields plus the allocator-health facts the
create rule needs). Assertions:

```lean
def cellOwn [SpikeGS hlc GF] (tds : CerbTags.TagDefsMap) (i : Int) (dq : DFrac) (c : SpikeCell) : IProp GF :=
  iprop(metaOwn i dq (metaOf tds c) ∗ bytesOwn c.addr dq c.bytes ∗
    ⌜c.bytes.length = CerbMem.sizeofCtype tds c.ty ∧
      decIndep tds c.addr c.ty c.bytes⌝)

def pointsToCell [SpikeGS hlc GF] (tds : CerbTags.TagDefsMap) (pv : CerbMem.PointerValue) (dq : DFrac)
    (ty : ctype) (bs : List CerbMem.AbsByte) : IProp GF :=
  iprop(∃ (id : Int) (a : Int),
    ⌜pv = cellPtr id a⌝ ∗ cellOwn tds id dq (SpikeCell.mk a ty bs))
```

`pointsToView tds id a aty off dqm dqb vty bs` owns one typed sub-range
of one allocation — `metaOwn id dqm ⟨a, aty, sizeof aty⟩ ∗ ⌜off + sizeof
vty ≤ sizeof aty ∧ bs.length = sizeof vty⌝ ∗ bytesOwn (a + off) dqb bs`
(metadata knowledge at fraction `dqm`, the range's bytes at `dqb`);
`cellOwn` is
the MAXIMAL view (offset 0, view type = allocation type) plus the
image's decode-inertness; `pointsToCell` — written `pv ↦c[tds]{dq} ty ;
bs` — is `cellOwn` at the pointer's own provenance id and address (the
pointer is a real `PointerValue` carrying its provenance, never an
address). Views split and join at real ∗ (`pointsToView_split`/`_join`),
split by fraction for read-sharing (`pointsToView_fractional`), agree on
base and type (`pointsToView_agree`); the points-to obeys the textbook
fractional laws (`pointsToCell_fractional`, `pointsToCell_agree`,
`pointsToCell_combine`). Every one of these has a client in
`StructExhibit.lean`.

**The `PtrEq` memop, and how the null test avoids the provenance
fork.** The engine's pointer comparison `eqPtrval` (CerbMem.lean:1766)
is deterministic on every arm except one: two concrete pointers with
DIFFERING provenance fork nondeterministically (`msum "pointer
equality" [("using provenance", false); ("ignoring provenance", addr
equality)]`, CerbMem.lean:1788 — a real `NDnd`, enumerated by both
exhaustive runners). The mirror has no step for that arm, and the
logic has no rule for it: `Step.memop_ptreq` (Step.lean:1173) steps
only when `applyMemM (CerbMem.eqPtrval default pv1 pv2) σ = some (b,
σ)` — a single-layer, state-preserving, deterministic verdict — and
`applyMemM` answers `none` on the fork (fail-closed absence, the
README's divergence register). Accordingly the rule
`wps_memop_ptreq` (Wps.lean:1503-1509; `wpt_memop_ptreq`, Wpt.lean:685)
asks the CLIENT for that determinism as its premise `hres : ∀ σ : Mem,
applyMemM (CerbMem.eqPtrval default pv1 pv2) σ = some (b, σ)`. Comparing
`cur` (`Prov_some id`) against `NULL` is not a differing-provenance
comparison of two concrete pointers: the null arms `(PVnull, _) | (_,
PVnull) → false` (CerbMem.lean:1768-1769) fire before provenance is
consulted, so `hres` is a computation — `eqPtrval_cell_null`,
`eqPtrval_null_cell`, `eqPtrval_null_null` (Heap.lean:207-218, each
`rfl`) discharge it at the fragment's three null-test shapes. A
comparison that could fork has no `hres` and therefore no rule.

**The persistent stratum, and no liveness token.** Allocation
knowledge is the metadata cell at the DISCARDED fraction:

```lean
def allocMeta (tds : CerbTags.TagDefsMap) (id a : Int) (aty : ctype) : IProp GF :=
  metaOwn id .discard ⟨a, aty, CerbMem.sizeofCtype tds aty⟩

def locInBounds (tds : CerbTags.TagDefsMap) (id a : Int) (aty : ctype) (off n : Nat) :
    IProp GF :=
  iprop(allocMeta tds id a aty ∗ ⌜off + n ≤ CerbMem.sizeofCtype tds aty⌝)
```

with `Persistent` instances (`allocMeta_persistent`,
`locInBounds_persistent`) as the persistence law; any view's metadata
fraction can be traded for it (`pointsToView_persist`), and a
persistent-metadata view yields its bounds knowledge for free
(`pointsToView_locInBounds`). This is admissible because METADATA IS
IMMUTABLE in the fragment — no rule updates a metadata cell (nothing
frees) — so there is no liveness token to guard a deallocation that
cannot happen. The bundles keep the metadata at a FRACTION rather than
persistent because full metadata ownership is the per-allocation
exclusivity anchor the frame theorem needs (`metaOwn_ne` →
`bigSepM_own_disjoint`); the donor's anchor is the killable
`alloc_alive`. Named mover: when `kill` joins the fragment, the metadata
heap gains the donor's `alloc_alive`/freeable split and the anchor
moves there.

**The tag-definition environment** `tds : CerbTags.TagDefsMap` is an
explicit parameter of every predicate whose footprint depends on type
layout (and of the engine's own memory functions — `sizeofCtype`,
`memValueToBytes`, `loadM`, `storeM`, `allocateObject` take it as a
leading argument). It is a program-wide constant of the language
instance, as Caesium's global environment is in RefinedC; the rules
supply `M.tagDefs`, the demos state footprints at `fmapEmpty` (their
synthetic files have no tag definitions), and `CohG` computes no layout
(the ghost metadata records the engine's own `Allocation.size`).

**Allocation capacity, and the failure policy.**

```lean
structure AllocReq where
  align : Int
  ty : ctype

def allocCap [SpikeGS hlc GF] (tds : CerbTags.TagDefsMap) (reqs : List AllocReq) : IProp GF :=
  iprop(∃ c : AllocCursor, cursorOwn c ∗
    ⌜PlanFits tds c reqs ∧ c.lastAddr ≤ 2 ^ 64⌝)
```

Cerberus's allocator is a deterministic downward cursor; a `create`
that cannot be placed is a KILL ("out of memory", the `alignedAddr == 0`
arm of `allocateObject`, CerbMem.lean:1479) — a refused/killed driver
outcome, not a value. RefinedC models allocation failure as a
deliberate `AllocFailed` divergence; this package does NOT import that
behaviour ([USER 2026-09-01] via the charter: inventing RefinedC
behaviour and calling it Cerberus soundness is the named anti-pattern).
Instead `allocCap reqs` certifies that the finite request plan `reqs`,
run IN ORDER, never hits the kill arm: `PlanFits tds c reqs` runs the
requests through `advanceCursor`, whose guard is exactly
`allocateObject_success`'s premise pair (`0 < sizeofCtype tds ty`,
`freshBase … ≠ 0`) and whose update is exactly that theorem's state
update — while hiding the cursor: client
statements never name `AllocCursor`, `lastAddress`, `nextAllocId`,
`freshBase` or `cursorOwn`. Clients receive capacity from the
allocation-aware launchers (`launchResources`, `LaunchCoh`) and may stop
early (`allocCap_weaken`), never reorder or skip (`planFits_order_sensitive`).

## 5. The engine attachment

**The mirror and the language instance.** `Step M : CoreExpr × EnvStack
× Mem → CoreExpr × EnvStack × Mem → Prop` (Step.lean) is a hand-written
small-step relation over the engine's generated types, each rule with a
file:line cite into the engine; it has zero authority. iris-lean runs
it:

```lean
instance : Language CoreRt Mem Empty CoreRVal where
  primStep := fun p _obs q =>
    Step p.1.M (p.1.e, p.1.ρ, p.2) (q.1.e, q.1.ρ, q.2.1) ∧
      q.1.M = p.1.M ∧ q.2.2 = []
  toVal := toValRt
  ofVal := ofValRt
```

(the four laws elided): no observations, no forks, the machine context
pinned across steps. There is deliberately NO `Language.Context`
instance (§3.4).

**The reference relation and the certification.** `CerberusRound M aid
c c'` (Round.lean) holds when the engine's discharged behaviour list at
`c` — one `step_ctx` call, every step discharged by the sequential
driver's protocol — is the singleton successful-next to `c'`:

```lean
def CerberusRound (M : MachineCtx) (aid : Nat) (c c' : Config) : Prop :=
  outcomesU M aid c.1 c.2.1 c.2.2 = [.next (M.thread c'.1 c'.2.1) c'.2.2]
```

The certification theorems, on the fragment cone `Frag` at a `SeqWF`
context with a cons-shaped environment and `esize e ≤ lemDefaultFuel`:

```lean
theorem engine_step_matchU {M : MachineCtx} (aid : Nat)
    {e e' : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    {ρ' : EnvStack} {σ σ' : Mem}
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel)
    (hs : Step M (e, ev0 :: evs, σ) (e', ρ', σ')) :
    outcomesU M aid e (ev0 :: evs) σ =
      [.next (M.thread e' ρ') σ'] := by
```

`cerberusRound_classify` (same hypotheses plus `hwf : M.SeqWF`)
concludes `RoundClass M aid (e, ev0 :: evs, σ)`, which has four arms: `value_done` (a bare value; the round is
PROGRAM-DONE), `value_annot` (an annotated value; the round is
REMOVE-ANNOT, which the mirror's value protocol does not step — why a
global iff is the wrong shape), `step` (the mirror steps, and for every
`c''`, `Step M c c'' ↔ CerberusRound M aid c c''`), `refused` (the
mirror is stuck at a non-value). Adequacy needs only the value and
`step` arms: the WP's `NotStuck` supplies a mirror step at every
reachable configuration, and there the engine agrees exactly. The
honest residual: at mirror-STUCK configurations the engine's refusal is
classified for store/load/create/case (`cerberusRound_refused_*`); the
other rows' refusal channels are `failwithI` panics (opaque constants —
a kernel classification is impossible), save's EVAL round, or the memop
fork (README, "Registered divergences and seams").

**Adequacy.** The Iris half (`spike_step_adequacy`) is
`wp_strong_adequacy_gen` with the ghost state CONSTRUCTED by
`genHeap_init` — nothing assumed pre-allocated — and the initial cells
minted from `Coh` (`spikeCells_alloc`; for allocating programs
`launchResources` under `LaunchCoh` also mints the cursor at the real
`⟨lastAddress, nextAllocId⟩` and grants `allocCap`). The engine face:

`engine_adequacyU` (Adequacy.lean): at a `SeqWF` context whose
registered label bodies are in `Frag`, for `Frag e₀`, `Coh M.tagDefs σ₀
m₀`, and an Iris proof `hwp` that the footprint cells entail the WP of
`⟨e₀, ev00 :: evs0, M⟩` with the readout post `∀ σ' ns κs nt, stateInterp
σ' ns κs nt ={⊤, ∅}=∗ ⌜ψ w.val σ'⌝`, under the fuel bounds `esize e₀ + n ≤
lemDefaultFuel` (and per label body): `driveU M aids n (M.thread e₀ (ev00
:: evs0)) σ₀` is never `.killed r`, never `.stuck`, and `.done v σ'`
implies `ψ v σ'`. Its proof: every drive step is `engine_step_matchU`'s unique engine
behaviour; Step-matched behaviours stay inside the WP-covered cone,
refusals contradict `NotStuck`, and the value protocol composes
REMOVE-ANNOT with PROGRAM-DONE. `project_triple` is this theorem plus
`stateInterp_readout` (Rules.lean — the ONE open/close of the state
interpretation) on the Iris post. The total half:

`wpt_engine_boundU` (TotalAdequacy.lean): with the same context
hypotheses, `pot e₀ ≤ lemDefaultFuel` (and per label body), `Coh
M.tagDefs σ₀ m₀`, and an Iris proof that the footprint cells entail
`blockSpecsT M Ls (readoutPost ψ) ∗ wpt M Ls k (readoutPost ψ) e₀ (ev00 ::
evs0)`: `∃ v σ', driveU M aids k (M.thread e₀ (ev00 :: evs0)) σ₀ = .done v
σ' ∧ ψ v σ' ∧ (stateInert e₀ = true ∧ StateInertLabels M → σ' = σ₀)`.
The judgment's budget IS drive fuel: a total derivation at `k` gives an
unconditional `.done` equation at fuel `k`, proved once by induction on
the budget with `engine_step_matchU` discharging one engine step per
unit (`wpt_drive_aux`). The fuel side conditions are on the
step-monotone size potential `pot` (not on the run length), so the
exported equations are unconditional in the loop count; the
state-inert conjunct pins fib's final memory to the initial one. The
other half, `wpt_strongly_normalizing`, is iris-lean's `twp_total`
consumed as-is — strong normalization of the thread-pool relation.
`_alloc` variants launch through `launchResources`.

**The production entry.** `DriverCollapse.lean` proves, from the
driver's OWN round functions (`driver2`, `new_drive_core_threads`,
`drive_nonmemory_steps_aux2`, `advance_step`, `perform_action_request2`,
`action_request_sequential2`, `runND`, `finalize`), that for a
single-threaded fragment configuration one production round is exactly
one drive round (`loop_step_frag`), that the whole driver computation is
a branch-free ND tree so `runND` yields the singleton execution
(`driver2_done`, `runND_active`), and that `finalize` reads the
delivered value back (`finalize_done`). `ProdLoop.lean`'s
`wpt_driver_done(_alloc)` drives the driver's per-thread loop by the
total judgment, one round per budget unit, concluding `DriverDoneAt`.
`ProdEntry.lean` starts from the SHIPPED `initial_driver_state` (memory
`initialMemState`, `errno` allocated by the real allocator — `prodMem₀`
is derived through engine functions only) and composes:

```lean
theorem prod_run_eqJ (sup : Nat) (e : CoreExpr) {Q : LabelMap}
    (hQe : LabeledAt ((initial_core_run_state sup
      (collect_labeled_continuations_NEW (prodFile e))).1) mainSym Q)
    (ψ : value → Mem → Prop) (k : Nat)
    (hdd : DriverDoneAt mainSym Q (prodThread e) e [fmapEmpty] prodMem₀ ψ k)
    (hfl : k + 2 ≤ lemDefaultFuel)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive fmapEmpty false (prodFile e) args)
          ((initial_driver_state sup (prodFile e) fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      ψ dres.dres_core_value dst'.layout_state ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
```

`LabeledAt` ties the label map to what the shipped registration
(`collect_labeled_continuations_NEW` over the synthetic file) computes
— derived, not hypothesized (`fib_labeledAt_production`,
`loop_labeledAt_production`, the per-program `*_labeledAt`). The
SUPPLY QUANTIFIER: since the cerberus-lean effect-retirement arc the
entry is pure and supply-threaded, `initial_driver_state : Nat → file →
fs_state → driver_state × Nat`, seeding `sym_supply` from `sup`; the
shipped `Main` passes one concrete stream, the theorems hold for every
`sup` because the fragment never reads it. The simplest production
export:

`exhibitA_prod (sup : Nat) (fs : CerbFS.FsState) (args : List String)`
(ProdExhibit.lean) concludes, for `progAProd` = `lets p = create(4, int) in lets _ =
store(int, p, 7) in load(int, p)`, that `CerbND.runND (_root_.drive
fmapEmpty false (prodFile progAProd) args) ((initial_driver_state sup
(prodFile progAProd) fs).1) = [(nd_status.Active dres, [], dst')]` with
`dres.dres_core_value = sevenVal` and `∃ i a, CellCoh fmapEmpty
dst'.layout_state i ⟨a, intTy, sevenBytes fmapEmpty⟩` (plus not blocked,
empty stdout/stderr): one total judgment `progAProd_wpt`
(PUBLIC `wpt_create` from `allocCap [⟨4, intTy⟩]`, then the generic heap
rules) through `wpt_driver_done_alloc` → `prod_run_eqJ`. Absent from the
statement: everything of ours except the program, the wrapper file
`prodFile`, and the value/byte constants.

## 6. Reading the audit

`CerberusHeapLang/Audit.lean` is the last import of the library root,
so `lake build` elaborates it and a failure is a red build. It asserts,
in order: (1) EXACT PINS — every name in `trioExports` (120 theorems
at the time of writing: the rules, the adequacy and collapse theorems,
every exhibit, the two projections and the consequence lemmas)
exists, is a theorem, and has
transitive axiom set EQUAL to `[propext, Classical.choice, Quot.sound]`
— growth or shrinkage fails until the list is re-baselined in the same
commit with the reason; (2) THE EXHAUSTIVE SWEEP — every theorem of
every `CerberusHeapLang.*` module is BOUNDED by the trio; (3) THE
BANNED-AXIOM SWEEP — no constant of any kind carries `sorryAx`,
`ofReduceBool` or `ofReduceNat`. There is no declared boundary axiom:
the semantics workspace and its lem runtime declare none.

What the sweep does NOT certify: the scope qualifiers (they are parts
of the statements), the readout predicates' faithfulness (§2 — read
them), coverage (the capability manifest's job, a speedbump). Together
with the banned proof-method grep (`native_decide`/`bv_decide`/
`ofReduce*`, `scripts/test_unit.sh` gate 1), the builds ARE the trust
base ([USER 2026-09-02]) — "the two capped builds" are the repository
root package `RefinedCerberus` (gate 2, its own `Audit.lean`; it does
not import this package) and this package `cerberus-heaplang` (gate 3);
this package's claims rest on gate 3 alone. Everything else in the
gate runner is a report that catches honest drift.

Check it yourself, from the repository root (offline):

```bash
scripts/setup-cerberus-dep.sh        # once: the pinned semantics workspace
cd cerberus-heaplang
../scripts/capped ~/.elan/bin/lake build
```

Expected tail (linter warnings from the dependency's `generated/*`
precede it; `capped` prints nothing on success — an `UNCAPPED` warning
means a broken environment, stop). The three counts are those at the
time of writing (QA-2); the build prints the current values, and the
pin count moves with every slice that adds or retires an export:

```
info: CerberusHeapLang/Audit.lean:188:0: CerberusHeapLang export pins: 120 trio-exact
info: CerberusHeapLang/Audit.lean:188:0: CerberusHeapLang axiom sweep: 1155 theorems bounded by the trio
info: CerberusHeapLang/Audit.lean:188:0: CerberusHeapLang banned-axiom sweep: 1949 constants of every kind checked; sorryAx/ofReduceBool/ofReduceNat absent from all cones
Build completed successfully (444 jobs).
```

The README's "How to build and verify" has the `#print axioms` recipe;
every line must end `depends on axioms: [propext, Classical.choice,
Quot.sound]`. A from-scratch build of the package's 444 jobs takes
minutes to tens of minutes; a replay from cache about a second.

## 7. What is deliberately out, and why

- **`kill`/free and procedures.** The classical logic's dispose rule
  and procedure specifications (incl. recursion) are the next two
  arcs, after an audit round ([USER 2026-09-02]: the feature set is
  frozen until quality is strong). Their absence is structural, not
  hidden: no liveness token exists because metadata is immutable
  (§4); `MachineCtx.SeqWF` (empty call stack) is a premise wherever a
  general context appears.
- **`Eunseq`.** Core's unsequenced composition is a semantic gap for a
  sequential logic; it is on the extension package's list, not the
  demo's.
- **The memop family beyond `PtrEq`**, and `PtrEq`'s
  differing-provenance nondeterministic fork (a real `msum` in the
  engine): fail-closed absences of a mirror step.
- **`Ecase`'s EVAL arm (a non-value scrutinee), `Ewseq` at binder
  patterns, pure exits beyond `PEsym`, the symbol-binder beta at
  annotated values**: mechanical per-construct extensions, each
  needing a `dischargeStep` arm, a `Step` rule and a rule at each
  stratum. Not on this list, because it is not a gap: the pure and
  annotation rules are stated at the empty annotation list `Expr []`
  — the mirror's values live there (the canonical-annotation protocol
  D3), and the annotation-generic forms are FALSE (QA-1).
- **Fuel parametricity.** The engine's `get_ctx` fuel is real (the
  interpreter bails past `10^6`), so partial statements carry the
  budget hypotheses and total statements are stated at a derived bound.
- **A C frontend.** Programs enter as authored Core in a synthetic
  one-procedure file; the elaborator from C is not in the chain.
- **A bridge to the semantics repo's `relsemcore` spine.** Not
  imported, not claimed; this package's reference relation is
  `CerberusRound`.
- **Parametric semantics interfaces.** A design experiment, DEFERRED
  possibly permanently ([USER 2026-09-02]): the rules are proved
  directly against `Step` and the memory state, as the donor does
  (README, "Deferred design experiment").
- **Extensions in this tree.** Derisking of value-indexed cells, struct
  fields, symbolic execution, `Eunseq`, the pointer-operation family
  happens on a COPY in a sibling package ([USER 2026-09-02]); the demo
  stays classical separation logic over Core, and grows only by more
  classical examples written against `API.lean`.

Design records, decision provenance and history: the dated files
under [`docs/`](.) and `../docs/DECISIONS.md`; the README carries the
claims surface, the trust diagram and the divergence register.
