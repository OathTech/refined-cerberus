# Professor review 2 — `cerberus-heaplang` at 757f73d

Reviewer: a new examiner, in persona (programming-languages professor; Reynolds/O'Hearn separation logic and Iris). Read-only review of the artifact as it stands at head `757f73d`: `README.md`, `docs/WALKTHROUGH.md`, `CerberusHeapLang/API.lean`, then Heap, Rules, Wps, Wpt, Step, Soundness, Round, Potential, Adequacy, TotalAdequacy, DriverCollapse, ProdLoop, ProdEntry, the exhibits, `Examples/ReadinessSmoke.lean`, `Audit.lean`. The previous review (`2026-09-02_professor-review-1.md`, B+) and the two response records were read for orientation only; every judgment below is my own against the tree. Every quotation is verbatim from the tree; declarations are cited by name and file (the documents carry no line numbers, deliberately, and I follow them). I did not run `lake build` (a build was running). After it finished I ran `#print axioms` on sixteen constants (§Q3). Where I could not verify a claim I say so.

The standard applied is the authors' own: "a relatively small Reynolds/O'Hearn style logic … over a synthetic fragment of core"; "just the things you'd need for classical separation logic, over cerberus core"; "The actual logic itself must be pristine, enough to make Reynolds and O'Hearn weep with joy"; exports of the shape `s ⊨ P ∧ core_exec(prog, s) ⇝ term ⇒ term = some s' ∧ s' ⊨ Q` with P/Q "just memory + pure properties". Dispose and procedures are deferred by ruling and are not graded.

## 1. Summary judgment

This is now a separation logic I would put in front of a class. The small axioms are proved once each, as atomic step specifications that run the real `storeM`/`loadM`/`allocateObject` inside the proof, and lifted to three judgments by three short lemmas; the frame rule is derived, and derived where it is hard — across `save`/`run` back edges through a framed label context, by one Löb induction at the partial judgment and one budget induction at the total one; the headline theorem `project_triple_pure` has a conclusion with no Iris in it, and the boring triple `MemTripleU` carries no fuel premise — the partial-correctness exports now speak about every run of every length, which last time they did not; the total judgment is a genuine variant with an honest step budget and a correct negative test proved at the engine; the mirror `Step` is certified against the engine's own `step_ctx` on the fragment in the direction adequacy needs, the residual is stated in the module that owns it, and the fragment's most consequential restriction — every node annotation-free, forced by `step_ctx`'s `current_loc` rewrite, which I verified in the generated code — is now on the first page. The trust story says exactly what is proved: `driveU` for the partial statements, the shipped `runND (drive …) (initial_driver_state …)` for the total production statements, no partial statement about the shipped pipeline and the reason (an opaque fuel leaf, which I verified). Every export I sampled has axiom set `[propext, Classical.choice, Quot.sound]`. What keeps this from a full A is residue, not defect: two premises that the authors themselves say are dischargeable or provable are still carried by every client (`hlib` on every memory exhibit, `hbsz` inside `Frag.case_value`); a third premise family (the pure evaluator's fuel bound `peDepth pe ≤ lemDefaultFuel` and the operand sub-grammar `PePure`, both inside `Frag`) is not named in either front document, which claim to state the fragment "exactly"; allocation capacity is still an ordered plan rather than a ∗-splittable resource — now honestly argued, but the classical face is promised rather than delivered; and several in-code module headers that the walkthrough sends the reader to contradict the current tree. None of these touches the statement of a main result.

## 2. The seven questions

### Q1. Is this a separation logic in the Reynolds/O'Hearn sense?

**Assertions and their heap semantics.** Assertions are `IProp GF` over three iris-lean `GenHeap`s coupled to the real `CerbMem.MemState` by

```
structure CohG (σ : Mem) (mm : SpikeHeapF MetaCell)
    (mb : SpikeHeapF CerbMem.AbsByte) (mk : SpikeHeapF AllocCursor) : Prop where
  metas : ∀ id mc, get? mm id = some mc → MetaCoh σ id mc
  metas_disj : ∀ i j mci mcj, i ≠ j → get? mm i = some mci →
    get? mm j = some mcj → metaDisjoint mci mcj
  bytes : ∀ k b, get? mb k = some b → byteAt σ k = b
  …
```
(Heap.lean), with the state interpretation `iprop(∃ mm mb mk, ⌜CohG σ mm mb mk⌝ ∗ metaInterp mm ∗ byteInterp mb ∗ cursorInterp mk)` (`SpikeState`). So assertions have Iris's resource semantics; the direct heap-predicate reading exists exactly where the projected triple exposes it — `Sat`/`CellCoh` on the pre side, the pure consequences on the post side. The walkthrough now says precisely this (§4 "What an assertion means": "That is Iris's resource semantics of assertions, not the Reynolds/O'Hearn semantics of assertions as predicates on heaps"), which is the honest sentence I would have demanded. The points-to,

```
def pointsToCell [SpikeGS hlc GF] (tds : CerbTags.TagDefsMap) (pv : CerbMem.PointerValue) (dq : DFrac)
    (ty : ctype) (bs : List CerbMem.AbsByte) : IProp GF :=
  iprop(∃ (id : Int) (a : Int),
    ⌜pv = cellPtr id a⌝ ∗ cellOwn tds id dq (SpikeCell.mk a ty bs))
```
(Heap.lean), is indexed by a real `PointerValue` carrying provenance — correct for Cerberus, where `loadM`/`storeM` dispatch on the allocation, not the address. ∗ has the right locality: byte ownership is exclusive per absolute address, metadata per allocation id (`metaOwn_ne`), and `CohG.metas_disj` makes distinct ids range-disjoint. The textbook laws are all present: `pointsToCell_fractional` (`pv ↦{q₁+q₂} ⊣⊢ pv ↦{q₁} ∗ pv ↦{q₂}`), `pointsToCell_agree`, `pointsToCell_combine`, the view algebra `pointsToView_split/_join/_fractional/_agree/_persist`, and `allocMeta_persistent`. Grade: A.

**Frame.** Derived, not assumed, at every level. At the raw WP it is iris-lean's `wp_frame_r`. At the partial judgment:

```
abbrev frameLs (R : IProp GF) (Ls : LabelSpec GF) : LabelSpec GF :=
  fun l vs ρ => iprop(Ls l vs ρ ∗ R)
```
```
theorem wps_frame_labels {Ψ : SpikeVal → EnvStack → IProp GF} (R : IProp GF)
    (e : CoreExpr) (ρ : EnvStack) :
    wps M Ls Ψ e ρ ⊢
      iprop(R -∗ wps M (frameLs R Ls) (fun w ρ' => iprop(Ψ w ρ' ∗ R)) e ρ) := by
  iloeb as IH generalizing %e %ρ
```
(Wps.lean) — value exit: the frame joins the post; jump: it joins the label's precondition; step: Löb. The total twin `wpt_frame_labels` (Wpt.lean) is by induction on the budget. `blockSpecs_frame`/`blockSpecsT_frame` frame the body specifications, and `wps_sound_frame` is the whole-loop form. The exhibits use it as a frame rule should be used: `lr_wps` proves the reversal invariant unframed, `lr_wps_frame` adds an arbitrary `RF` once. At the boring level the frame is built into the definition of the triple (the `∀ R, P ##ₘ R → …` in `MemTripleU`, with `R` handed to the post), and `semantic_frameU` moves a named frame across a cells-shaped triple. Grade: A.

**Small axiom — store.** Proved once as an atomic step specification:

```
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
```
theorem store_atomic [SpikeGS hlc GF] {M : MachineCtx}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (cv : value) (mo : memory_order)
    (mv : CerbMem.MemValue) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv = some mv)
    (hst : StorableAt M.tagDefs ty mv) :
    AtomicStep M (storeExpr loc ann ty pv cv mo) ρ 2
      (pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs)
      (fun w => iprop(∃ fp, ⌜w = SpikeVal.annot [DA_pos [] fp] Vunit⌝ ∗
        pointsToCell M.tagDefs pv (.own 1) ty (CerbMem.memValueToBytes M.tagDefs [] mv).2))
```
(Rules.lean). The proof opens the interpretation, runs the real `storeM` through `storeM_success` (Heap.lean: `applyMemM (CerbMem.storeM tds loc c.ty false (cellPtr id c.addr) mv) σ = some (.FP .W c.addr (CerbMem.sizeofCtype tds c.ty), CerbMem.writeBytesTo σ c.addr (CerbMem.memValueToBytes tds [] mv).2)`), inverts the mirror step, updates the byte heap, and re-establishes `CohG` by `CohG.storeRange`. It is small: only the written cell is mentioned; full ownership is required. The raw-WP face `wp_store` and the judgment faces `wps_store`/`wpt_store` are each a few lines through `wp_of_atomic`/`wps_of_atomic`/`wpt_of_atomic`. Deviations from `{p ↦ -} [p] := v {p ↦ v}`: the returned value is the annotated unit `SpikeVal.annot [DA_pos [] fp] Vunit` (engine-forced: the continuation `Expr [] (Eannot [DA_pos [] fp] …)` is what `step_action` builds; hidden by `wps_store_plain`/`wpt_store_plain` under annotation-insensitivity), and the typing premises `hmv`/`hst`. `StorableAt`'s five fields are now listed in the walkthrough with the engine arm each defeats (§3.1 "What 'storable' means"), and they are `rfl` for scalars (`zero_storable`, ProdEntry.lean). Grade: A.

**Small axiom — load.** `load_atomic` at any fraction `dq`, premise `htrap : cellLoadTrap M.tagDefs ⟨addrOf pv, ty, bs⟩ = false`, post `SpikeVal.annot [DA_pos [] fp] (loadedVal M.tagDefs pv ty bs)` with the cell returned unchanged; `loadedVal` is the engine's own decode. The `_Bool` trap premise is engine-forced and explained. The typed-subrange twins `loadAt_atomic`/`storeAt_atomic` over `pointsToView` are the same shape, and `wps_load_cell_at`/`wps_store_cell_at` are derived from them by split/join (the derivation is duplicated at the two judgments — acknowledged in the response record; it is plumbing, not axioms). Grade: A.

**Small axiom — allocate.**

```
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
      wps M Ls Ψ (createExpr loc ann (.IV aprov req.align) req.ty pref) ρ
```
(Wps.lean), derived from `create_atomic` (Rules.lean), which runs the real `allocateObject` via `allocateObject_success` and re-establishes `CohG` by `CohG.create`. This is not `{emp} x := cons(-) {x ↦ -}`, and it cannot be: `allocateObject` has an out-of-memory kill arm (`freshBase … ≠ 0` is the guard in `allocateObject_success`), so some capacity accounting is forced. The shape chosen — an ordered plan over an exclusive cursor,

```
def allocCap [SpikeGS hlc GF] (tds : CerbTags.TagDefsMap) (reqs : List AllocReq) : IProp GF :=
  iprop(∃ c : AllocCursor, cursorOwn c ∗
    ⌜PlanFits tds c reqs ∧ c.lastAddr ≤ 2 ^ 64⌝)
```
(Heap.lean) — is now argued in the walkthrough (§4 "Why an ordered plan and not an additive budget"), the additive alternative is weighed and its soundness sketched, and the cost is stated in plain words: "capacity is not a separation-logic resource in this package — `allocCap reqs` cannot be split across ∗, it is weakened only to a prefix (`allocCap_weaken`)". I accept the argument as far as it goes: the coupling invariant tracks the cursor exactly (`CohG.cursor`), and the exact-cursor `create_atomic` is the natural theorem to prove against `allocateObject`. But the public rule hides the address (`∀ p`), so an additive byte budget as a derived face over the plan is exactly what a classical logic wants and is not delivered. Forced deviation, now justified, with the classical face registered but absent. Grade: A-.

**Sequencing.**

```
theorem wps_seq {Ψ : SpikeVal → EnvStack → IProp GF}
    (a pa : List annot) (bty : core_base_type) (e1 e2 : CoreExpr)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    wps M Ls (fun w ρ' => wps M Ls
        (fun u ρ'' => Ψ (SpikeVal.mergeInto w u) ρ'') e2 ρ') e1 (ev0 :: evs) ⊢
      wps M Ls Ψ (Expr a (Esseq (Pattern pa (CaseBase (none, bty))) e1 e2))
        (ev0 :: evs)
```
(Wps.lean), with `wps_seq_spec` (the `Specified` binder, delivering `update_env (specPat …)`), `wps_seq_sym` (plain symbol binder), `wps_wseq`, and the `wpt_` twins at budget `k1 + k2`. The bind shape is right. `mergeInto` is the engine's annotation residue (LETS-ANNOT wraps the continuation), the cons-shaped environment is forced by `update_env`'s panic on the empty stack; both are documented. The absence of a `Language.Context` instance is correctly argued (Lang.lean: `Erun` discards the frame, so `Context.primStep_fill` is false) and sequencing is proved directly by Löb / budget induction. Grade: A-.

**Conditional.**

```
theorem wps_if {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (g : generic_pexpr Unit sym) (e2 e3 : CoreExpr) (ρ : EnvStack) (b : Bool) :
    iprop(⌜evalPexpr M.tagDefs M.extern ρ g = some (boolValue b)⌝ ∗
      wps M Ls Ψ (bif b then e2 else e3) ρ) ⊢
      wps M Ls Ψ (Expr a (Eif g e2 e3)) ρ
```
(Wps.lean), `wps_if_true`/`wps_if_false` derived. The environment is a parameter of the judgment, not assertion language — the walkthrough now says so in one sentence ("Program variables are not heap") and explains why the guard is a pure premise. Correct for Core's immutable `let`-bindings. Grade: A-.

**Loops.** Label-context treatment: `wps_run` consults only the label's precondition,

```
theorem wps_run {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (ra : core_run_annotation) (l : sym)
    (pes : List (generic_pexpr Unit sym))
    {params : List (sym × core_base_type)} {cont : CoreExpr}
    {vs : List value} (ev0 : Fmap sym value) (evs : List (Fmap sym value))
    (hl : lookupLabel M.labels l = some (params, cont))
    (hvs : evalPexprs M.tagDefs M.extern (ev0 :: evs) pes = some vs) :
    Ls l vs (ev0 :: evs) ⊢
      wps M Ls Ψ (Expr a (Erun ra l pes)) (ev0 :: evs)
```
; `blockSpecs_intro` assembles the bodies' specifications with no Löb; the one Löb is in

```
theorem wps_sound {Ψ : SpikeVal → EnvStack → IProp GF} (e : CoreExpr)
    (ρ : EnvStack) :
    blockSpecs M Ls Ψ ⊢
      iprop(wps M Ls Ψ e ρ -∗
        WP (⟨e, ρ, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤
          {{ w, Ψ w.w w.ρ }})
```
(Wps.lean). This is the de Bruin-style treatment of `save`/`run`, and it is clean. The block entry `wps_save` covers both engine arms (literal and live-variable initializers). Grade: A.

**Consequence.** `wps_wand`, `wps_fupd`, `wps_mono_Ls`; `wpt_mono`, `wpt_mono_k` (budgets are upper bounds), `wpt_mono_Ls`, `wpt_fupd`. Grade: A.

**On the lifting shape.** The previous examiner asked for `WP … ⊢ wps …`. The authors argue it is unprovable (iris-lean's `wp.pre` places `▷` after the step's update, `wps.pre` before the `∀` over steps, and `|={∅}=> ▷ P ⊢ ▷ |={∅}=> P` is not a law) and chose a mask-generic atomic step specification as the common ancestor of all three judgments. I checked `wps.pre` (Wps.lean: `… ={⊤,∅}=∗ ⌜Reducible⌝ ∗ ▷ ∀ r σ₂ eₜ, ⌜step⌝ -∗ £ 1 ={∅,⊤}=∗ …`) and the argument holds. The chosen shape is not a workaround; it is the better design — `AtomicStep` is exactly what the proofs establish before packaging, and it is mask-generic where `wps_sound` is not. Accepted on the merits.

### Q2. Is the semantics genuinely Cerberus's?

**The mirror and its certification.** `Step M` (Step.lean) is hand-written over the engine's generated types, each rule with a citation, and explicitly "zero authority". The certification theorem:

```
theorem engine_step_matchU {M : MachineCtx} (aid : Nat)
    {e e' : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    {ρ' : EnvStack} {σ σ' : Mem}
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel)
    (hs : Step M (e, ev0 :: evs, σ) (e', ρ', σ')) :
    outcomesU M aid e (ev0 :: evs) σ =
      [.next (M.thread e' ρ') σ']
```
(Soundness.lean): a mirror step at a `Frag` configuration with a cons-shaped environment and `esize` within the engine's `get_ctx` fuel implies that the engine's discharged behaviour list is exactly that step. One direction, on the fragment. The reference relation is

```
def CerberusRound (M : MachineCtx) (aid : Nat) (c c' : Config) : Prop :=
  outcomesU M aid c.1 c.2.1 c.2.2 = [.next (M.thread c'.1 c'.2.1) c'.2.2]
```
(Round.lean), the graph of one discharged `step_ctx` round; `step_iff_cerberusRound` is two-sided where the mirror steps (it follows from the singleton shape, i.e. mirror determinism — it adds no engine content, and the header does not pretend otherwise); `cerberusRound_classify` sorts every well-sized `Frag` configuration into `value_done`/`value_annot`/`step`/`refused`, with the `refused` arm saying nothing about the engine except for store/load/create/case (`cerberusRound_refused_*`). The Round.lean header states the residual exactly: "the `refused` arm says nothing about the ENGINE's behavior at a mirror-stuck configuration — the engine may kill, report ILLTYPED, produce an off-fragment form, or PANIC (`failwithI`, an OPAQUE constant …)". For adequacy this direction suffices and the argument (`drive_classifyU`: `NotStuck` supplies a mirror step; the engine agrees) is correct.

**Which execution function.** In the drive statements it is

```
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
with `stepOutcomes … = (step_ctx …).map (dischargeStep …)` (Adequacy.lean): the engine's `step_ctx` plus this package's projection `dischargeStep` of the sequential driver's discharge. The README now says this where it matters ("The trust story", claim 1: "it is `driveU` (Adequacy.lean): this package's definition of the sequential driver's round loop … tied to the shipped driver by `loop_step_frag` … but only at configurations where the mirror `Step` steps … No partial-correctness statement about the shipped pipeline is proved, and none can be by this route"), and the walkthrough has a dedicated §1.3. I did not verify `dischargeStep` line by line against `Driver.lean`'s `action_request_sequential2`; what I can say is that its success arm is certified against the shipped driver by a theorem, `loop_step_frag` (DriverCollapse.lean, hypothesis `(hs : Step M₀ (e, ev0 :: evs, dst.layout_state) (e', ρ', σ'))`), which is the arm every proved path uses — and that "never kills" at the engine means the real `storeM`/`loadM`/`allocateObject` returned `NDactive`, a fact about the engine regardless of how the killed arm is spelled. The production statements use the shipped composite `CerbND.runND (_root_.drive fmapEmpty false (prodFile e) args) ((initial_driver_state sup (prodFile e) fs).1)` (ProdEntry.lean `prod_run_eqJ`), total only. The reason no partial production statement exists is real: I checked LemLib — `@[implemented_by fuelExhaustedWithImpl] opaque fuelExhaustedWith {α : Type} (msg : String) (witness : α) : α := witness`, `def fuelExhausted {α : Type} (witness : α) : α := fuelExhaustedWith "lem: fuel exhausted" witness` — and the generated `Driver.lean`'s fuelled loops bottom out in `| 0 => (fuelExhausted (ND (fun st => (NDkilled (Undef0 …`. Nothing about an `opaque` constant's value is provable, so the claim is exact.

**Re-definitions posing as the semantics.** None found. `evalPexpr` (Step.lean) is a hand-written pure evaluator over `PEval`/`PEsym`/integer `PEop`/`PEarray_shift`, certified against the engine's `full_eval_pexpr` tower (`full_eval_bridge`, Soundness.lean); it is interior to `Step`, so an error there loses proofs, not truth. `Sat`/`Coh`/`CellCoh`, `SeedChain`, `SeedTree`, `readBytesFrom` are readout predicates, printed in walkthrough §2 as they should be.

**The fragment, stated honestly and exactly.** `Frag` (Soundness.lean) is the authority and is readable. The annotation-free restriction is now on the first page of the README with its forcing fact, and I verified the forcing fact in the pinned generated `Core_reduction.lean`, `step_ctx`'s general arm: `let maybe_loc := get_loc e_annots; let th_st := match maybe_loc with | none => th_st | some loc1 => (if CerbLocation.isLibraryLocation loc1 then th_st else { th_st with current_loc := loc1 })` — against `MachineCtx.thread … current_loc := M.currentLoc` and `engine_step_matchU`'s conclusion `M.thread e' ρ'`. Located Core is outside `Frag`; the documents say so and name the mover. Good.

One exactness gap remains. `Frag` carries a second fuel-premise family that neither front document names:

```
  | if_ {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
      (hdg : peDepth g ≤ lemDefaultFuel) :
      Frag e2 → Frag e3 → Frag (ifRedex g e2 e3)
  | run {ra : core_run_annotation} {l : sym}
      {pes : List (generic_pexpr Unit sym)}
      (hdep : ∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel) :
      Frag (runRedex ra l pes)
  …
  | store_op {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {ty : ctype} {pe2 pe3 : generic_pexpr Unit sym} {mo : memory_order}
      (hlib : CerbLocation.isLibraryLocation loc = false)
      (hnv : valueFromPexprs [pe2, pe3] = none)
      (hp2 : PePure pe2) (hp3 : PePure pe3)
      (hd2 : peDepth pe2 ≤ lemDefaultFuel)
      (hd3 : peDepth pe3 ≤ lemDefaultFuel) :
      Frag (storeOpRedex loc ann ty pe2 pe3 mo)
```
(Soundness.lean). `peDepth` bounds the pure evaluator's own fuelled layers (`step_eval_pexpr`/`pull_constrained`), and `PePure` is the operand sub-grammar the mirror evaluator covers. `grep peDepth README.md docs/WALKTHROUGH.md` returns nothing; the README's "Scope, exactly" names the operand grammar ("`PEval`/`PEsym`/integer-`PEop`/`PEarray_shift` operands") and hints once ("`Esave` at any initializers within the evaluator's fuel"), and the walkthrough's "Why the fuel premises exist" (§5) discusses only `get_ctx` and `pot`. A reader who trusts the walkthrough's account of fuel would not know there is a second budget. For authored programs the premise is `rfl` (`peDepth_sym_le`, `peDepth_val_le`), and it is inside `Frag`, so the exhibits' hypothesis columns are not wrong — but "exactly" means naming it.

### Q3. Do the exports say what the documents say?

**The headline.** The boring triple:

```
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
(Adequacy.lean). No fuel premise; `n` unbounded; `Sat` is `Coh` by `abbrev`. This is the target shape with the frame built in. The theorem that produces it:

```
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
    MemTripleU M (ev0 :: evs) e P ψ
```
The conclusion contains no Iris. The two Iris-shaped hypotheses are the specification (`hwp`) and the pure-consequence obligation (`hpost`), which the `*_consequence` lemmas discharge for the points-to shapes; `struct_create_store_adequacy` is a genuine instance of the `_alloc` twin, and I read its proof. `project_triple` (the strongest-post form) sits beneath it, as it should. The exports match the documents: I read the statements of `exhibitA/B/C_semantic`, `exhibitA/B/C_engine`, `exhibitA_total`, `counter_loop_certified`, `counter_loop_certified_irrelevant_binding`, `fib_certified`, `fib_certified_total`, `array_sum_certified`, `struct_update_certified`, `struct_create_store_wps`, `struct_create_store_adequacy(_prodMem₀)`, `alloc_two_creates_wps`, `alloc_create_wpt`, `alloc_create_launch_smoke`, `list_reverse_certified`, `list_reverse_certified_total`, `tree_rotate_certified(_total)`, `case_certified`, `wseq_certified`, `diverge_total_unprovable`, `exhibitA_prod`, `fib_certified_production`, `counter_loop_certified_production`, `list_reverse_certified_production`, `counter_loop_certified_registration`, and checked the README's "Hypotheses, exhaustively" column against them (`list_reverse_certified` also against the machine-printed snapshot `2026-09-02_pr1-B-signatures-post.txt (byte-identical to the former 2026-09-02_pr1-C-signatures-post.txt, deduplicated 2026-09-02)`): the column is exact in every case I checked, section variables included. The walkthrough's quoted `list_reverse_certified_production` is verbatim.

**iris-lean absent from closed-program statements.** Yes for every drive and production statement. The three mirror-only termination theorems the previous examiner objected to are gone (deleted, not relabelled), and the negative test is re-proved at the engine:

```
theorem dg_driveU_more (ra : core_run_annotation) (σ₀ : Mem) :
    ∀ (k : Nat) (aids : Nat → Nat),
      driveU (procCtx dgProcSym (dgRS ra)) aids k
        ((procCtx dgProcSym (dgRS ra)).thread (dgBody ra) [fmapEmpty]) σ₀ =
      .more ((procCtx dgProcSym (dgRS ra)).thread (dgBody ra) [fmapEmpty]) σ₀
```
(DivergeExhibit.lean), so `diverge_total_unprovable` contradicts the `.done` equation `wpt_engine_boundU` would give. Correct, and better than before.

**Axiom cone.** Verified directly after the build finished, from `cerberus-heaplang/` via `../scripts/capped ~/.elan/bin/lake env lean --stdin`: `project_triple_pure`, `project_triple_pure_alloc`, `struct_create_store_adequacy`, `list_reverse_certified`, `list_reverse_certified_total`, `fib_certified_total`, `exhibitA_prod`, `list_reverse_certified_production`, `engine_step_matchU`, `wps_sound`, `wpt_sound`, `diverge_total_unprovable`, `store_atomic`, `create_atomic`, `wps_frame_labels`, `cerberusRound_classify` — every one `depends on axioms: [propext, Classical.choice, Quot.sound]`. `Audit.lean`'s `trioExports` has 116 entries (counted), matching the README's "116 trio-exact". The design of the sweep (exact pins, exhaustive bound, banned-axiom sweep over every constant kind) is sound; the tree's `decide +kernel` uses are kernel reduction, not `ofReduceBool`, and the sweep would catch the latter. The claim holds.

### Q4. Are the premises justified and explained?

- **Fuel / potential.** The partial statements now carry the static premises `pot e ≤ lemDefaultFuel` and `pot cont ≤ lemDefaultFuel` per registered body, with `Frag.esize_le_pot` and `Frag.pot_step_bound` (Potential.lean) doing the work; `MemTripleU` itself carries none. The walkthrough explains why they exist (§5) and that they are `rfl` for authored programs. Justified and explained. The production statements carry `k + 2 ≤ lemDefaultFuel` for the certified step count (e.g. `fib_certified_production`'s `hfuel : 2 * n.toNat + 6 ≤ lemDefaultFuel` for `k = 2 * n.toNat + 4`) — honest, and explained by the opaque leaf.
- **The pure evaluator's fuel (`peDepth`) and operand grammar (`PePure`).** Justified (the engine's `step_eval_pexpr` is fuelled; Soundness.lean says so in its evaluator section) but not explained in either front document (Q2). Unclarity.
- **Tag environment.** `M.tagDefs` is an explicit parameter of every layout-dependent predicate; the statements pin `fmapEmpty`. Explained (Heap.lean header; README register row) and correct as a design: the environment is a program-wide constant.
- **`Frag`.** Explained as "the per-construct authority", with the capability manifest (18 rows, 0 red) as the coverage instrument. Fine.
- **Label well-formedness.** `SeqWF` (empty stack, startup thread) is a premise wherever a general context appears and is discharged at both profiles (`spikeCtx_wf`, `procCtx_wf`); `LabeledAt` is derived from the shipped registration in the production statements (`fib_labeledAt_production`, `loop_labeledAt_production`, `prod_run_eqJ`'s `hQe`). Nothing hand-built enters the production label plumbing. Good.
- **Annotation protocol.** The `Expr []` restriction and the run-time `Eannot` residue are explained; the `_plain` forms hide the annotated unit for annotation-insensitive posts. Fine.
- **Storability.** Five fields, each with the engine arm it defeats; `StorableView` for subranges. Explained (Q1).
- **`allocCap` / `LaunchCoh` / launch coherence.**

  ```
  structure LaunchCoh (tds : CerbTags.TagDefsMap) (σ : Mem) (m : SpikeHeapF SpikeCell)
      (reqs : List AllocReq) : Prop where
    coh : Coh tds σ m
    id_lt : ∀ i c, get? m i = some c → i < σ.nextAllocId
    fresh_alloc : ∀ id : Int, σ.nextAllocId ≤ id → σ.allocations.get? id = none
    fresh_dead : ∀ id : Int, σ.nextAllocId ≤ id → σ.deadAllocations.contains id = false
    addr_lo : ∀ i c, get? m i = some c → σ.lastAddress ≤ c.addr
    plan : PlanFits tds ⟨σ.lastAddress, σ.nextAllocId⟩ reqs
    la_wf : σ.lastAddress ≤ 2 ^ 64
  ```
  (Adequacy.lean). Why `Sat` does not imply it is well argued ("a memory can carry the footprint and still have its allocator cursor sitting on top of those cells"), `MemTripleU_alloc_of_MemTripleU` records the direction that does hold, and the production cold start discharges it through engine functions only (`prodMem₀_launchCoh`, ProdEntry.lean). Justified and explained.
- **`hlib : CerbLocation.isLibraryLocation loc = false`.** A constructor argument of `Frag.store/load/create/load_op/store_op`, hence a hypothesis of every memory exhibit. The authors state, correctly, that it is dischargeable on the success path (`storeM`/`loadM` use `loc` only in kill payloads; `allocateObject` takes none) and explain why they stopped: the refusal-classification lemmas in Round.lean carry the location in the `.killed` payload, so removing it means restating the `step_ctx_*` equations with the `loc'` conditional. That is a real cost, and the register says so plainly. It is nonetheless a dischargeable premise still pushed onto every client: sloppiness, honestly labelled.
- **`hbsz : ∀ e', select_case subst_sym_expr cval pats = some e' → esize e' ≤ esize (caseRedex …)`.** Explained (walkthrough §3.3, CaseExhibit.lean header): provable in principle by the whole-AST induction, `rfl` for authored programs, carried rather than proved. Same verdict.
- **`hex : ∀ x, resolveExtern M.extern x = x` and `SymFrame ev0`** on `struct_create_store_wps`. Named in the exhibits table; `SymFrame` is explained in §3.1; the extern premise is not explained anywhere in the front documents (it is the engine's `PEsym` redirection through the extern map, identity at `fmapEmpty`). Minor.

### Q5. Total and partial correctness; the total budget

Partial: `wps` is a guarded fixpoint of a contractive `wps.pre` (Wps.lean), adequacy via `wp_strong_adequacy_gen` with the ghost state constructed (`spike_step_adequacy`), `.more` unconstrained (`DriveOk`), drive length unbounded. Correct.

Total: `wpt` by structural recursion on the budget, `LabelSpecT GF := sym → Nat → List value → EnvStack → IProp GF` carrying a variant, and the jump clause

```
    | some lp =>
      iprop(|={⊤}=> ∃ (params : List (sym × core_base_type)) (cont : CoreExpr)
        (vs : List value) (ev0 : Fmap sym value) (evs : List (Fmap sym value))
        (m : Nat),
        ⌜ρ = ev0 :: evs⌝ ∗ ⌜lookupLabel M.labels lp.1 = some (params, cont)⌝ ∗
        ⌜evalPexprs M.tagDefs M.extern ρ lp.2 = some vs⌝ ∗
        ⌜1 + m ≤ k⌝ ∗ Ls lp.1 m vs ρ)
```
(Wpt.lean) demanding the strict decrease. The engine face,

```
theorem wpt_engine_boundU … (k : Nat)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i
          (.own 1) c)) ⊢
        iprop(blockSpecsT M Ls (readoutPost ψ) ∗
          wpt M Ls k (readoutPost ψ) e₀ (ev00 :: evs0)))
    (aids : Nat → Nat) :
    ∃ v σ', driveU M aids k (M.thread e₀ (ev00 :: evs0)) σ₀ = .done v σ' ∧
      ψ v σ' ∧ (stateInert e₀ = true ∧ StateInertLabels M → σ' = σ₀)
```
(TotalAdequacy.lean), is proved by `wpt_drive_aux`: strong induction on the budget with `engine_step_matchU` discharging one engine step per unit. The budget is drive length — a stronger statement than classical total correctness asks for (a step count, not just a variant) and honestly so: the client must exhibit it (`fib_certified_total` at `2 * n.toNat + 4`, `list_reverse_certified_total` at `13 * ns.length + 7`, `tree_rotate_certified_total` at `19`). `diverge_total_unprovable` is a correct negative test at the engine. Note for the record: the collapse into Iris's `TotalWeakestPre`,

```
theorem wpt_sound {Ψ : SpikeVal → EnvStack → IProp GF} (k : Nat)
    (e : CoreExpr) (ρ : EnvStack) :
    blockSpecsT M Ls Ψ ⊢
      iprop(wpt M Ls k Ψ e ρ -∗
        WP (⟨e, ρ, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ [{ w, Ψ w.w w.ρ }])
```
(Wpt.lean), is proved and pinned but consumed by no export — every total export goes through `wpt_drive_aux` directly, and the trust diagram says so ("no Iris adequacy in the cone; wpt_sound is the Iris collapse"). It is a legitimate metatheorem (the judgment is a sound total WP), not dead weight, but the walkthrough should say in one clause that it is not on any export's path. Both halves are properly handled.

### Q6. Claimed-not-proved; proved-not-claimed; documentation precision

**Claimed and not proved.** I found none in the front documents. Every theorem named in README and WALKTHROUGH exists with the stated shape; every Lean block I compared is verbatim (the response record reports a mechanical check of all 26 blocks; I compared `MemTripleU`, `project_triple_pure`, `list_reverse_certified_production`, `isList`, `lr_wps_frame`, `driveU`, `Coh`, `Sat`, `wp_store`, `AtomicStep`, `frameLs`, `wps_frame_labels`, `wps_create`, `blockSpecs_intro`, `wpt.pre`, `wpt`, `wpt_sound`, `cellOwn`, `pointsToCell`, `allocCap`, the `Language` instance, `CerberusRound`, `engine_step_matchU` by eye against the sources — all match). The README's "proves every rule against that engine" is accurate in the sense the trust story then makes precise. The walkthrough's opening — "proves that what the logic says is what the engine does — where 'the engine' is, precisely, the execution function named in each statement (§1.3)" — is hedged exactly right.

**Proved and not load-bearing.** `wpt_sound` (above); `rsCtx` (Step.lean) is consumerless — acknowledged in the response record as a later retirement; `wps_frame` (value-channel frame, superseded by `wps_frame_labels`) is kept with two consumers; `engine_complete_loadU`/`_createU` and the `cerberusRound_refused_*` family are the honest per-row refusal classifications and earn their place; `SemTripleU`/`ProvenTripleU`/`semantic_triple_soundU`/`semantic_frameU` are the cells-shaped instance (`SemTripleU_iff_Mem` is `Iff.rfl`) used by the Exhibit.lean triples — one definitional instance, acceptable. The triple/drive multiplicity the previous examiner complained of is gone: one drive, one triple with one launch-premise variant, one cells-shaped instance.

**Documentation precision.** Both front documents are now in the standard vocabulary of the field (I found no `QA-1`/`P6.1`/`R-03`/`[USER …]`/"lane"/"slice" outside the README's "Records" section), carry no line numbers, cite by name, and hedge where hedging is due. The exhibits table's hypothesis column is exact (Q3). Length: README 520 lines, WALKTHROUGH 929; the authors report honestly that the earlier brief asked for roughly half and explain what bounds further cutting. My judgment: the WALKTHROUGH's length is justified — 201 of its lines are verbatim Lean and the rest is explanation the previous examiner asked to be added; the README is still long because it says several things twice (the trust story repeats walkthrough §1.3/§5; "The logic" table repeats API.lean's header; the modules table repeats both), and could lose its "The logic" table to API.lean without loss. Not a defect; a recommendation.

Two precision defects, both in-code, both material because the walkthrough directs the reader to module headers ("`Soundness.lean` header ('FUEL HONESTY')", "Round.lean header", "`Heap.lean` header", "`Step.lean` header"):

1. Headers that contradict the current tree. `AllocExhibit.lean` header: "It is NOT the P2 whole-program conversion: the headline allocating exhibits (ProdExhibit/ProdLoopExhibit) still cross the driver operationally (R-02) and their rewrite through `wps_create`/`wpt_create` is the next phase." — false at this head (`exhibitA_prod`, `list_reverse_certified_production` go through `wpt_create` and `wpt_driver_done_alloc`). `ProdEntry.lean`, the S4 section header: "HONEST RESIDUAL (recorded, slice notes): the full production-face `.done` equation for a LOOP run (the driver2 collapse at a proc-carrying thread with a populated label map) is not established this slice" — false (`fib_certified_production`, `counter_loop_certified_production`, `list_reverse_certified_production`). `Step.lean` header note 3: "`CoreRt`/`CoreRVal` carry `lbl : LabelMap`" and `Wps.lean` header: "carried in the runtime tuple (`CoreRt.lbl`)" — `CoreRt` is `⟨e, ρ, M⟩` and the label map is `M.labels`, derived. A reader sent to a header to learn a design fact must not find the opposite of the tree.
2. The module headers remain saturated with the process vocabulary purged from the front documents ("alloc arc P4.1", "R-05 closure", "QA-1/H-1", "S1b DRIFT TEST", "D14", "D19", "D26", "charter P1.4"). The previous examiner's fix 7 named only the two front documents, and the authors met it; but the front documents point into these headers, and the reader they are written for has no glossary.

### Q7. Alignment with the academic goal; scope creep; multiplicity

The logic proper (Heap, Rules, Wps, Wpt, Potential, EnvLaws, Lang: about 9,600 lines) is a classical separation logic over Core in the Reynolds/O'Hearn sense, with the label-context treatment of control as the right generalization for `save`/`run`. The certification (Step, Soundness, Round: about 6,900 lines) and the production collapse (DriverCollapse, ProdLoop, ProdEntry: about 2,500 lines) are the engineering the goal demands — the exports must be about the real semantics, and without them the logic would be about a mirror. Nothing beyond classical separation logic has crept in: no invariants, no ghost-state API exposed to clients, no automation, no type system (the `ReadinessSmoke` two-field object is a client of the public rules and shows the API is sufficient without opening the ghost state — a good test, well scoped). Multiplicity is now what the design needs and no more: two judgments (partial and total — both are classical SL, and the total one is what makes the production statements equations), one drive, one triple with its launch variant and its cells-shaped instance, two live context profiles and one dead one. The allocation-capacity shape is the one place where a non-classical shape stands, now argued rather than merely adopted.

## 3. Required fixes and recommended improvements

### Required

1. **Front documents (README "Scope, exactly" and/or WALKTHROUGH §5 "Why the fuel premises exist"): name the second fuel-premise family.** `Frag.if_`, `Frag.run`, `Frag.save`, `Frag.load_op`, `Frag.memop_op`, `Frag.store_op` carry `peDepth pe ≤ lemDefaultFuel` (and `PePure pe`) for their pure operands; neither document mentions `peDepth`. Satisfying sentence, placed next to the `pot` explanation: "Pure operands are drawn from the sub-grammar `PePure` (values, symbols, integer/boolean binops, `array_shift`) and carry their own static evaluator-fuel bound `peDepth pe ≤ lemDefaultFuel` inside `Frag` (the engine's `step_eval_pexpr` is fuelled at the same budget); it is `rfl` for every authored program and never mentions the run length."

2. **In-code headers that contradict the tree.** Delete or correct: `AllocExhibit.lean` header ("still cross the driver operationally … is the next phase"); `ProdEntry.lean` S4 section header ("HONEST RESIDUAL … is not established this slice"); `Step.lean` header note 3 and `Wps.lean` header ("`lbl : LabelMap`", "`CoreRt.lbl`"). Satisfying state: no header sentence about the current tree that a theorem in the tree refutes; historical remarks, if kept, are marked as history in one word.

3. **Discharge `hlib`.** The premise is dischargeable on every proved path (the authors' own finding). Satisfying statement: `Frag.store/load/create/load_op/store_op` without `hlib`; the `step_ctx_store/load/create` equations restated with the engine's own `loc' := if isLibraryLocation loc then th.current_loc else loc` in the request payload; the `cerberusRound_refused_*` lemmas quantifying over that `loc'`; and `hlib` gone from every `*_certified`/`*_total`/`*_adequacy` statement. Since it is a constructor argument of `Frag`, no lemma can remove it from clients without the Round.lean edit; if the authors judge that edit not worth it for this demo, the register row that already records the finding must be joined by one sentence at the head of the README's exhibits table naming `hlib` as the one client hypothesis known to be dischargeable — the table's header currently describes `hlib` but does not say this.

4. **Prove `hbsz`, or state its provability precisely.** `esize (subst_sym_expr x v e) = esize e` (with the mutual `esizeAlts`) is the lemma; `esize` inspects only expression constructors and `subst_sym_expr` substitutes only into pure expressions. Satisfying statement: that lemma, and `Frag.case_value` without `hbsz`. If not proved: the walkthrough's sentence "provable in principle by an induction over the generated Core AST's mutual recursion" should name the exact equation to be proved, as above, so the reader can judge the size of the gap.

### Recommended

- **Deliver the additive capacity face.** A derived `allocBudget b := ∃ reqs, allocCap reqs ∗ ⌜cost reqs ≤ b⌝`-style predicate will not split; the real face needs an authoritative-sum algebra for the cursor bound (the `Auth` functor is already in `SpikeGF`) and a coupling inequality `c.lastAddr ≤ σ.lastAddress`. With it, `allocBudget (s + t) ⊣⊢ allocBudget s ∗ allocBudget t` and a `wps_create` consuming `sizeof ty + align − 1` would give the classical allocation axiom's shape. The walkthrough's §4 argument would then become the design record of the exact face, which is where it belongs.
- **Say that `wpt_sound` is off every export's path** (one clause in walkthrough §3.3 or §5), so nobody mistakes the Iris total WP for part of the trust story.
- **Retire `rsCtx`** (consumerless) and the stale `spikeThread`/`procThread` duplicates of `M.thread` if nothing but the exhibits' statements use them (I did not check the latter).
- **Purge process vocabulary from the module headers the walkthrough points to** (at minimum Heap, Rules, Wps, Wpt, Step, Soundness, Round, Adequacy, TotalAdequacy), or stop pointing to them and say the same things in the walkthrough.
- **Explain `hex : ∀ x, resolveExtern M.extern x = x`** in one sentence where `SymFrame` is explained (§3.1): the engine resolves every `PEsym` through the extern map with identity fallback; at `fmapEmpty` the premise is `rfl`.
- **README**: drop "The logic" table in favour of a pointer to API.lean's header (which is the same table, maintained once), and let the trust story cite walkthrough §1.3 instead of restating it. This alone would take the README below 450 lines without loss.
- **Read-only allocations** (`CellCoh.alloc` fixes `al.isReadonly = .IsWritable`): the register row and mover are right; when `MetaCell` gains the flag, only the store rule should demand writability.

## 4. The grade

**A-.**

What separates this from an A: nothing in the statements of the main results — those are now right — but the residue a pristine logic would not carry: two premises the authors themselves know to be dischargeable or provable are still on every client (`hlib` on every memory exhibit, `hbsz` inside `Frag.case_value`); a third premise family (`peDepth`/`PePure`) is absent from documents that claim to state the fragment exactly; allocation capacity is still not a ∗-resource, the classical face being promised in the register rather than delivered; and module headers that the walkthrough sends its reader to assert things the tree refutes. Fix required items 1–4 and deliver the additive capacity face, and I would sign an A without reservation.
