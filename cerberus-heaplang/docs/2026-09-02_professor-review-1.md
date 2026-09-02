# Professor review 1 — `cerberus-heaplang` at 9717836

Reviewer: in persona, a programming-languages professor; read-only review of the artifact (theorems + the two front documents). Every quotation below is verbatim from the tree at head 9717836, with file:line. Axiom cones of the headline exports were checked directly with `#print axioms` after the running build finished (all `[propext, Classical.choice, Quot.sound]`); nothing else was executed. Where I could not verify a claim I say so.

## 1. Summary judgment

This is real work, and it is sound as far as I can see: the small axioms for store and load are proved against the engine's own `storeM`/`loadM` under a coupling invariant on the real `MemState`; the frame rule is derived, not assumed, and it is derived where it is hard — across back edges, through a framed label context; the total judgment is a genuine well-founded budget, its adequacy is a genuine induction against the engine's step function, and the negative test is correct; the whole stack is kernel-checked to the classical trio. Nobody should call this "a big pile of garbage". But the authors asked to be judged against "pristine, enough to make Reynolds and O'Hearn weep with joy", and against that standard the artifact is not there yet. The headline projection theorem does not produce a boring triple — Iris survives in its conclusion; the partial-correctness statements carry a fuel premise coupled to the *run length* although the tree already contains the lemma that makes it run-length independent, so "partial correctness" is not partial correctness for long runs; the drive-lane "engine" is a hand-written projection of the driver whose relation to the shipped driver is certified only along the total lane, and the front matter overstates this; the fragment is silently restricted to annotation-free Core nodes by a design choice (locations in the immutable context) that is never stated; the small axioms are proved three times over rather than once and lifted; there are four triple notions and three drive notions where one of each would do; and the two front documents are long, saturated with project-process jargon, and carry file:line citations most of which are stale. None of these is a soundness problem. All of them are the difference between a pristine logic and a very good engineering artifact wrapped around an engine.

## 2. The seven questions

### Q1. Is this a separation logic in the Reynolds/O'Hearn sense?

**Assertions and their heap semantics.** Assertions are `IProp GF` over three iris-lean `GenHeap`s (per-byte, per-allocation metadata, allocator cursor) coupled to the real memory by

```
structure CohG (σ : Mem) (mm : SpikeHeapF MetaCell)
    (mb : SpikeHeapF CerbMem.AbsByte) (mk : SpikeHeapF AllocCursor) : Prop where
  metas : ∀ id mc, get? mm id = some mc → MetaCoh σ id mc
  metas_disj : ∀ i j mci mcj, i ≠ j → get? mm i = some mci →
    get? mm j = some mcj → metaDisjoint mci mcj
  bytes : ∀ k b, get? mb k = some b → byteAt σ k = b
  ...
```
(Heap.lean:1458-1476), with `stateInterp σ _ _ _ := iprop(∃ mm mb mk, ⌜CohG σ mm mb mk⌝ ∗ metaInterp mm ∗ byteInterp mb ∗ cursorInterp mk)` (Heap.lean:1480-1482). The points-to is

```
def pointsToCell [SpikeGS hlc GF] (tds : CerbTags.TagDefsMap) (pv : CerbMem.PointerValue) (dq : DFrac)
    (ty : ctype) (bs : List CerbMem.AbsByte) : IProp GF :=
  iprop(∃ (id : Int) (a : Int),
    ⌜pv = cellPtr id a⌝ ∗ cellOwn tds id dq (SpikeCell.mk a ty bs))
```
(Heap.lean:1538-1541). So the heap semantics of assertions is Iris's resource semantics, and the "direct" heap reading exists only for the pure predicates `Coh`/`Sat`/`CellCoh` (Heap.lean:319-350) on the pre side and for "every pure consequence" on the post side. That is legitimate for an Iris instantiation; it is not the Reynolds/O'Hearn semantics of assertions as heap predicates, and the front documents should say so in one sentence instead of implying equivalence. The per-byte carrier gives ∗ the right locality: byte ownership is exclusive per absolute address, metadata ownership is exclusive per allocation id (`metaOwn_ne`, Heap.lean:2301-2303), and `CohG.metas_disj` makes distinct ids range-disjoint. Good.

**Frame.** At the raw WP it is iris-lean's. At the statement judgment it is genuinely derived by Löb:

```
theorem wps_frame_labels {Ψ : SpikeVal → EnvStack → IProp GF} (R : IProp GF)
    (e : CoreExpr) (ρ : EnvStack) :
    wps M Ls Ψ e ρ ⊢
      iprop(R -∗ wps M (frameLs R Ls) (fun w ρ' => iprop(Ψ w ρ' ∗ R)) e ρ) := by
  iloeb as IH generalizing %e %ρ
```
(Wps.lean:402-406), with `frameLs R Ls = fun l vs ρ => iprop(Ls l vs ρ ∗ R)` (Wps.lean:395-396) and the total twin `wpt_frame_labels` (Wpt.lean:456). Framing the label context is exactly the right treatment for a `goto`-style logic; the exhibits then prove their invariants unframed and add the frame once (`lr_wps_frame`, ListRevExhibit.lean). At the boring level the frame is built into the triple's `R` quantifier (`MemTripleU`, Adequacy.lean:1166-1176) and `semantic_frameU` (Adequacy.lean:1602-1612) moves a named frame across. This is the strongest part of the work. Grade: A.

**Small axiom — store.**
```
theorem wp_store [SpikeGS hlc GF] {s : Stuckness} {E : CoPset} {M : MachineCtx}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (cv : value) (mo : memory_order)
    (mv : CerbMem.MemValue) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv = some mv)
    (hst : StorableAt M.tagDefs ty mv) :
    pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs ⊢
      WP (⟨storeExpr loc ann ty pv cv mo, ρ, M⟩ : CoreRt) @ s; E
        {{ w, ∃ fp, ⌜w = (⟨SpikeVal.annot [DA_pos [] fp] Vunit, ρ, M⟩ : CoreRVal)⌝ ∗
            pointsToCell M.tagDefs pv (.own 1) ty (CerbMem.memValueToBytes M.tagDefs [] mv).2 }}
```
(Rules.lean:157-166). It is small: it mentions only the cell. Full ownership is required, as it must be. The proof runs the real `storeM` (`storeM_success`, Heap.lean:373-378) and the real `writeBytesTo`. Deviations from `{p ↦ -} [p] := v {p ↦ v}`: (i) the returned value is the annotated unit `SpikeVal.annot [DA_pos [] fp] Vunit` — engine-forced (the engine's continuation is `Expr [] (Eannot [DA_pos [] fp] …)`, Step.lean:1022-1023) and papered over by `wps_store_plain` under `AnnotInsensitive Ψ` (Wpt.lean:2357-2358); (ii) the two typing premises `hmv`/`hst`. `StorableAt` (Heap.lean:173-187) has five fields (`compat`, `fpm`, `len`, `bytes_fpm`, `stored_dec`), each cited to the engine arm it defeats; they are "rfl" for scalars. This is the RefinedC `v ◁ᵥ ty` obligation in embryo, and it is justified; but the walkthrough (§3.1) calls them "the two typing premises" and never lists the five fields — a reader must open Heap.lean to learn what "storable" means. Grade: A- (the shape is right; the exposition of the side condition is thin).

**Small axiom — load.** `wp_load` (Rules.lean:265-274) at any fraction `dq`, premise `htrap : cellLoadTrap M.tagDefs ⟨addrOf pv, ty, bs⟩ = false`, post `loadedVal M.tagDefs pv ty bs` (the engine's own decode). Correct and small. The `_Bool` trap premise is engine-forced and explained. Grade: A.

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
(Wps.lean:2655-2669), with
```
def allocCap [SpikeGS hlc GF] (tds : CerbTags.TagDefsMap) (reqs : List AllocReq) : IProp GF :=
  iprop(∃ c : AllocCursor, cursorOwn c ∗
    ⌜PlanFits tds c reqs ∧ c.lastAddr ≤ 2 ^ 64⌝)
```
(Heap.lean:2072-2074). This is not `{emp} x := cons(-) {x ↦ -}`. The classical axiom presupposes allocation cannot fail; Cerberus's allocator is a deterministic downward cursor with an out-of-memory kill (`allocateObject_success`, Heap.lean:1035-1053, guard `freshBase … ≠ 0`), so *some* capacity accounting is forced. What is not forced is the *shape* chosen: an ordered request plan owned through an exclusive cursor, with weakening only to prefixes (`allocCap_weaken`, Heap.lean:2095-2096) and no split law (`planFits_order_sensitive`, Heap.lean:1355-1358 is offered as the justification). Consequence: capacity is not a separation-logic resource — it cannot be split across ∗ and handed to two components; every allocating specification must be parametric in `rest` and thread the plan sequentially. An additive byte budget (`budget (s + a) ⊣⊢ budget s ∗ budget a`, sound because `alignDown((la − s), al) ≥ la − s − al + 1`) would restore the classical shape at the cost of a slightly conservative bound. The README's "Allocation capacity, and the failure policy" (walkthrough §4) argues against RefinedC's `AllocFailed` and for `allocCap`, but never considers the additive alternative. Grade: B. Forced deviation, under-argued design.

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
(Wps.lean:732-738), plus `wps_seq_spec`/`wps_seq_sym` for the two binder patterns and the `wpt_` twins with `k1 + k2`. The bind shape is right; `mergeInto` is the engine's annotation residue (LETS-ANNOT wraps the continuation); the cons-shaped environment is forced by `update_env`'s panic on an empty stack (Step.lean:1072-1078). The absence of a `Language.Context` instance is correctly argued (Lang.lean:81-89: `Erun` discards its context, so `Context.primStep_fill` is false) and sequencing is proved directly by Löb. Grade: A-.

**Conditional.**
```
theorem wps_if {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (g : generic_pexpr Unit sym) (e2 e3 : CoreExpr) (ρ : EnvStack) (b : Bool) :
    iprop(⌜evalPexpr M.tagDefs M.extern ρ g = some (boolValue b)⌝ ∗
      wps M Ls Ψ (bif b then e2 else e3) ρ) ⊢
      wps M Ls Ψ (Expr a (Eif g e2 e3)) ρ
```
(Wps.lean:1021-1025). Because the environment is a parameter of the judgment rather than part of the assertion, the guard's verdict is a pure fact of `ρ`, and the classical two-premise rule is recovered by a case split outside the logic. Acceptable for Core's immutable `let`-bindings; the walkthrough should say explicitly that program variables are not heap and are not in the assertion language. Grade: A-.

**Loops.** Label-context treatment: `wps_run` (Wps.lean:229-238) consults only `Ls l vs (ev0 :: evs)`; `blockSpecs` (Wps.lean:2716-2722) is the persistent conjunction of body specifications; `blockSpecs_intro` (Wps.lean:2731-2736) needs no Löb; the one Löb is in
```
theorem wps_sound {Ψ : SpikeVal → EnvStack → IProp GF} (e : CoreExpr)
    (ρ : EnvStack) :
    blockSpecs M Ls Ψ ⊢
      iprop(wps M Ls Ψ e ρ -∗
        WP (⟨e, ρ, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤
          {{ w, Ψ w.w w.ρ }})
```
(Wps.lean:2796-2801). This is the correct de Bruin-style treatment of Core's `save`/`run` and it is clean. Grade: A.

**Consequence.** `wps_wand` (Wps.lean:256-259), `wpt_mono`/`wpt_mono_k` (Wpt.lean:268-270, 192-194). Fine. Grade: A.

**A structural complaint that cuts across all of the above.** The memory rules exist at three strata and are proved three times: `wp_store` (Rules.lean:157), `wps_store` (Wps.lean:1758), `wpt_store` (Wpt.lean:2237), each an ~80-line unfolding against `Step` with the same `storeM_success` inside; likewise load, `_at`, `_cell_at`, `_plain`, create — twelve memory rules per stratum. The README admits it: "the statement strata restate them with the label context and prove them the same way, directly against `Step`" (README.md:430-432). A lifting lemma (`WP` of a one-step-to-value expression entails `wps`/`wpt` of it) would make every stratum rule a one-line corollary of the raw one, and would make the base stratum load-bearing instead of the admitted near-dead weight ("the raw-WP `wp_load` (the exhibits consume its statement-stratum twin …)", README.md:457-460). A pristine logic proves each small axiom once.

### Q2. Is the semantics genuinely Cerberus's?

**What is proved, in which direction.**
```
theorem engine_step_matchU {M : MachineCtx} (aid : Nat)
    {e e' : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    {ρ' : EnvStack} {σ σ' : Mem}
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel)
    (hs : Step M (e, ev0 :: evs, σ) (e', ρ', σ')) :
    outcomesU M aid e (ev0 :: evs) σ =
      [.next (M.thread e' ρ') σ']
```
(Soundness.lean:3843-3849): mirror step ⇒ the engine's discharged round is exactly that step (one direction, on `Frag`, cons env, within `esize` fuel). `step_iff_cerberusRound` (Round.lean:114-118) is the two-sided form *at configurations where the mirror steps* — it follows from the singleton shape, i.e. from mirror determinism, and adds no engine content. `cerberusRound_classify` (Round.lean:161-164) sorts every `Frag` configuration into `value_done`/`value_annot`/`step`/`refused`; the `refused` arm says nothing about the engine except for store/load/create/case (`cerberusRound_refused_*`, Round.lean:305-348). The Round.lean header is admirably honest about this ("THE RESIDUAL, stated honestly", Round.lean:61-75). For adequacy this direction suffices, and the argument (`drive_classifyU`, Adequacy.lean:794-849: `NotStuck` supplies a mirror step; the engine agrees) is correct.

**Where the semantics is a re-definition rather than the engine.** Two places, one disclosed and one overstated.

(a) `dischargeStep` (Soundness.lean:145-223) is a hand-written projection of the driver's request discharge (`action_request_sequential2`, `liftCore_run`, `perform_memop_request2`), and `driveU` (Adequacy.lean:137-145) is a hand-written iteration of `{step_ctx → dischargeStep}`. Every drive-lane export — `MemTripleU`, `SemTripleU`, every `*_certified`, `project_triple` — is a statement about `driveU`, i.e. about `step_ctx` (engine) plus `dischargeStep` (theirs). The README's trust story lists `driveU`/`dischargeStep` among "the pure readout predicates … A wrong definition here would make a theorem true but irrelevant" (README.md:286-293). Good. But the same document's trust claim (1) says of the closed-program exports: "Their referents are cerberus-lean's semantics — `step_ctx` and the driver's request discharge in the drive lanes" (README.md:190-193). In the drive lanes the referent is not the driver's request discharge; it is `dischargeStep`. The relation between `dischargeStep` and the shipped driver is established only along the *total* lane, by `loop_step_frag` (DriverCollapse.lean:1147-1170), and only for configurations where the mirror steps. There is no partial-correctness statement about the shipped pipeline anywhere (every `*_production` theorem is a total `.done`/`Active` equation, ProdEntry.lean:347-361 and its three consumers). The DriverCollapse header explains why (DriverCollapse.lean:83-89: at insufficient fuel the production value is the opaque `fuelExhausted` leaf, so nothing is provable), and that is a real forcing fact about the port — but it means the partial logic's "engine" is `driveU`, and the front matter must say exactly that.

(b) `evalPexpr` (Step.lean:620) is a hand-written pure evaluator, certified against the engine's (`full_eval_bridge` etc., Soundness.lean:1619-1925). It is interior to `Step`, so its wrongness could only lose proofs. Fine.

**Is the fragment stated honestly and exactly?** Almost. `Frag` (Soundness.lean:3018-3098) is exact and readable, and the capability manifest is a good instrument. But every composite constructor demands the *empty static annotation list*: `Frag.sseq … : Frag (Expr [] (Esseq …))`, `Frag.annot : Frag (Expr [] (Eannot ds b))`, and `saveRedex`/`ifRedex`/`caseRedex`/`runRedex` are all `Expr [] …` (Soundness.lean:458-473); so are `storeRedex`/`loadRedex`/`createRedex` (Soundness.lean:275-293). The front documents mention `Expr []` only for the pure and annotation *rules* — "the pure and annotation rules … are stated at the empty annotation list `Expr []` because that is where the mirror's values live" (README.md:69-74) — and never state that *every node of every program in the fragment is annotation-free*. That restriction has a forcing fact the documents do not name: `step_ctx` reads `get_loc e_annots` and rewrites the thread's `current_loc` from a located annotation (Core_reduction.lean:484: `let th_st := match maybe_loc with | none => th_st | some loc1 => (if CerbLocation.isLibraryLocation loc1 then th_st else { th_st with current_loc := loc1 })`), whereas this package keeps `currentLoc` in the immutable `MachineCtx` (Step.lean:334-345) and pins it across steps (`M.thread e' ρ'` in `engine_step_matchU`). A located node would falsify the match. Since every Core program produced by the C elaborator is located, this is the single most consequential scope restriction in the package, and it is undocumented. That is an exactness failure.

### Q3. Do the exports say what the documents say?

**The boring-triple shape.** The target: `s ⊨ P ∧ core_exec(prog, s) ⇝ term ⇒ term = some s' ∧ s' ⊨ Q`, P and Q boring. The realization:
```
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
(Adequacy.lean:1166-1176). This *definition* is boring and matches the shape. The theorem that produces it does not:
```
theorem project_triple {GF : BundledGFunctors} [SpikeGpreS GF]
    {M : MachineCtx} (hwf : M.SeqWF)
    ...
    MemTripleU M (ev0 :: evs) e P (fun R v σ' => ∀ ψ : Prop,
      (∀ [SpikeGS .hasLC GF] (w : CoreRVal), w.val = v →
        ∀ (mm : SpikeHeapF MetaCell) (mb : SpikeHeapF CerbMem.AbsByte)
          (mk : SpikeHeapF AllocCursor), CohG σ' mm mb mk →
        iprop(Q w ∗ ([∗map] i ↦ c ∈ R, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c) ∗
          metaInterp mm ∗ byteInterp mb) ⊢ (⌜ψ⌝ : IProp GF)) → ψ)
```
(Adequacy.lean:1207-1221). The postcondition of the "boring triple" is a second-order quantification over Iris entailments containing `SpikeGS`, `CohG`, `metaInterp`, `byteInterp`, `cellOwn` and `⊢`. The README concedes this ("That obligation is the one place Iris vocabulary survives in a projected statement", WALKTHROUGH.md:96-98) and calls `CohG` "an opaque token a client never opens" (README.md:201-203). A token in the *conclusion* of the headline theorem is not opaque to the reader who must decide what the theorem means. The genuinely boring corollary — hypothesis: the Iris post pure-entails `ψ`; conclusion: `MemTripleU M ρ e P ψ` for a pure `ψ : CellMap → value → Mem → Prop` — is what every exhibit proves by hand (e.g. `struct_create_store_adequacy`'s discharge, StructExhibit.lean:842-853) and is not stated as a theorem. It should be the headline; `project_triple` as written is its strongest-post form and belongs one level down.

**"Iris-free statements; referents are cerberus-lean's semantics."** True for `MemTripleU`-shaped exports modulo the `driveU`/`dischargeStep` point above. Not true for the two `*_terminates` exhibits and the theorem behind them:
```
theorem wpt_strongly_normalizing {GF : BundledGFunctors} [SpikeGpreS GF]
    {M : MachineCtx}
    ...
    Relation.StronglyNormalizing Language.ErasedStep
      ([(⟨e₀, ρ₀, M⟩ : CoreRt)], σ₀)
```
(TotalAdequacy.lean:1063-1074; `list_reverse_terminates`, ListRevExhibit.lean:2074-2083; `fib_terminates`, FibExhibit.lean:667-671). `Language.ErasedStep` is the iris-lean thread-pool relation over `Step` — the hand-written mirror. These are theorems about the mirror, exported under the "termination" heading of the exhibits table (README.md:172, 178) with no fuel or `hlib` hypotheses precisely because they never touch the engine. Since `Step ⊆ engine round` is only available under `Frag`+fuel, the statements cannot even be transported. They are either dead weight (the `.done` equations at explicit fuel already imply engine termination) or mislabelled.

**Axiom cone.** Verified directly: `project_triple`, `project_triple_alloc`, `struct_create_store_adequacy`, `list_reverse_certified`, `list_reverse_certified_total`, `list_reverse_terminates`, `fib_certified_total`, `exhibitA_prod`, `list_reverse_certified_production`, `engine_step_matchU`, `wps_sound`, `wpt_sound`, `diverge_total_unprovable` all report `[propext, Classical.choice, Quot.sound]`. The Audit.lean mechanism (Audit.lean:188-238: exact pins, exhaustive bound, banned-axiom sweep over every constant) is sound in design. The claim holds.

**Production statements.** `list_reverse_certified_production` (quoted in WALKTHROUGH.md:236-254) and `prod_run_eqJ` (ProdEntry.lean:347-361) are exactly as described: `CerbND.runND (_root_.drive fmapEmpty false (prodFile e) args) ((initial_driver_state sup (prodFile e) fs).1) = [(nd_status.Active dres, [], dst')]`. The file wrapper `prodFile` (ProdEntry.lean:116-128) is synthetic, as disclosed. The cold-start memory `prodMem₀` (ProdEntry.lean:203-204) is derived through engine functions. This lane says what the documents say.

**Exhibits table vs statements.** Spot-checked `list_reverse_certified` (ListRevExhibit.lean:1455-1481), `list_reverse_certified_total` (2011-2029), `fib_certified_total` (FibExhibit.lean:623-628), `tree_rotate_certified_total` (TreeRotExhibit.lean:1424-1438), `counter_loop_certified` (LoopExhibit.lean:424-446), `exhibitB_semantic` (Exhibit.lean:391-395), `struct_create_store_adequacy` (StructExhibit.lean:803-820), `alloc_create_launch_smoke` (AllocExhibit.lean:162-168), `diverge_total_unprovable` (DivergeExhibit.lean:120-133) against the README's hypothesis column: all match, including the section-variable line citations (ListRevExhibit.lean:1153-1154, FibExhibit.lean:436-437, etc.). The hypothesis column is the best-executed piece of documentation in the package.

### Q4. Are the side conditions and premises justified and explained?

- **`esize e + n ≤ lemDefaultFuel` (and per label body).** Explained (Soundness.lean:54-64 "FUEL HONESTY"; README "Registered divergences"). But it is *not* the engine's own budget; it is a conservative bound derived from `Frag.esize_step_bound` (Soundness.lean:3560-3566: `esize e' ≤ esize e + 1 ∨ …jump reset…`), which couples the premise to the number of drive steps `n`. The tree already contains the sharper fact for the total lane:
  ```
  theorem Frag.pot_step_bound {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack}
      {σ : Mem} {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
      (hf : Frag e) (hs : Step M (e, ρ, σ) (e', ρ', σ')) :
      pot e' ≤ pot e ∨
      ∃ l pes params cont, jumpRedex? e = some (l, pes) ∧
        lookupLabel M.labels l = some (params, cont) ∧ e' = cont
  ```
  (TotalAdequacy.lean:199-205) with `Frag.esize_le_pot` (TotalAdequacy.lean:120). With these, `drive_classifyU` can carry `pot e ≤ lemDefaultFuel` (static, run-length independent) instead of `esize e + n ≤ lemDefaultFuel`. As stated, `list_reverse_certified` (`hfuel : 6 + nsteps ≤ lemDefaultFuel`) says nothing about reversing a list of more than about 77,000 nodes, while `list_reverse_certified_total` at fuel `13 * ns.length + 7` (ListRevExhibit.lean:2011-2029) has no such limit. A partial-correctness theorem that is weaker than the total one on long runs is an inverted result, and the premise that causes it is dischargeable from lemmas already in the tree. This is exactly "premises that could be discharged but are pushed onto the client".

- **`hlib : CerbLocation.isLibraryLocation loc = false`** (a constructor argument of `Frag.store/load/create`, Soundness.lean:3020-3031). Explained as the engine's `loc'` redirection (Step.lean:991-996). But `storeM` uses `loc` only in `let fail_ (err : mem_error) := (NDkilled (failReason err loc), st)` (generated CerbMem.lean:1667-1669), i.e. only in kill payloads; on the active path, and for the active/killed *classification*, the result is loc-independent. A lemma `applyMemM (storeM tds l ty lk pv mv) σ = applyMemM (storeM tds l' ty lk pv mv) σ` (and for `loadM`, `allocateObject`) would discharge `hlib` entirely and remove it from every exhibit's hypothesis list. Dischargeable premise pushed onto the client.

- **`Frag`**, **`SeqWF`**, **the tag environment `M.tagDefs`**, **cons-shaped `ev0 :: evs`**, **`StorableAt`/`hmv`**, **`htrap`**, **`hdec`/`hinert`**, **`allocCap`/`LaunchCoh`/`PlanFits`**, **`hex : ∀ x, resolveExtern M.extern x = x`**, **`AnnotInsensitive`**: each is explained somewhere in README/WALKTHROUGH §3.5/§4 with a forcing fact, and each forcing fact I checked (`update_env` panic on `[]`, Core_aux; `allocateObject`'s `alignedAddr == 0` kill; `_Bool` trap arm; `current_execution_mode` opaque) is real. `LaunchCoh` (Adequacy.lean:435-449) and why `Sat` does not imply it (a memory can carry the footprint with its cursor on top of it) is well argued (Adequacy.lean:1239-1262). `StorableAt`'s five fields are not explained in the walkthrough (see Q1).

- **`Frag.case_value`'s `hbsz : ∀ e', select_case subst_sym_expr cval pats = some e' → esize e' ≤ esize (caseRedex …)`** (Soundness.lean:3091-3092). `esize` ignores pure expressions (Soundness.lean:254-261), and `subst_sym_expr` substitutes into pure expressions, so this looks provable rather than assumable; CaseExhibit.lean:17-27 explains why `hbr` cannot be a closure lemma but does not address `hbsz`. Unexplained premise.

- **The label tie `hQ : LabeledAt rs p Q`** and its production derivation `loop_labeledAt_production`: explained and, in the production lane, derived rather than assumed (ProdEntry.lean:414-464). Good.

### Q5. Total and partial correctness; is the budget honest?

Partial: `wps` is a guarded fixpoint (Wps.lean:134-189), adequacy via `wp_strong_adequacy_gen` with the ghost state constructed (`spike_step_adequacy`, Adequacy.lean:587-609), `.more` unconstrained (`DriveOk`, Adequacy.lean:767-771). Correct, modulo the fuel-coupling complaint in Q4.

Total: `wpt` is defined by structural recursion on the budget with no fixpoint (Wpt.lean:111-145, quoted in WALKTHROUGH §3.4); `LabelSpecT GF := sym → Nat → List value → EnvStack → IProp GF` (Wpt.lean:77-78) carries a variant; the jump clause demands `⌜1 + m ≤ k⌝ ∗ Ls lp.1 m vs ρ` and `blockSpecsT` (Wpt.lean:2640-2647) verifies each body at its own variant `m`. `wpt_sound` (Wpt.lean:2691-2695) collapses into iris-lean's `TotalWeakestPre` by strong induction on `k`; `wpt_engine_boundU` (TotalAdequacy.lean:921-939) delivers `∃ v σ', driveU M aids k (M.thread e₀ (ev00 :: evs0)) σ₀ = .done v σ' ∧ ψ v σ' ∧ (stateInert e₀ = true ∧ StateInertLabels M → σ' = σ₀)` by induction on the budget against `engine_step_matchU`, with the run-length-independent `pot` premise. The budget is a real termination argument (a `Nat` variant that is simultaneously a step bound), not smuggled: the client must exhibit it (`13 * ns.length + 7`, `2 * n.toNat + 4`), which is more than classical total correctness asks (a well-founded variant, not a step count) and correspondingly more informative. `diverge_total_unprovable` (DivergeExhibit.lean:120-133) is a correct negative test via `dg_not_normalizing`. Both halves are properly handled. The only blemish is the one in Q3: the "logical half" `wpt_strongly_normalizing` is about the mirror, and is redundant given the cost half.

### Q6. Claimed but not proved; proved but not claimed; documentation precision

Claimed-and-overreaching: the trust-claim wording about drive-lane referents (Q2a); the `*_terminates` labelling (Q3); the walkthrough's opening sentence "proves that what the logic says is what the engine does" (WALKTHROUGH.md:27-28) is true for the total production lane and true-modulo-`dischargeStep` elsewhere.

Dead weight: `SemTriple`, `ProvenTriple`, `semantic_triple_sound`, `semantic_frame` ("Kept in its historical spelling", Adequacy.lean:1093-1094) alongside `SemTripleU`/`ProvenTripleU`/`MemTripleU`/`MemTripleU_alloc`; `drive`/`driveJ` alongside `driveU` (Adequacy.lean:163-164, 1685-1687); three machine-context profiles `spikeCtx`/`procCtx`/`rsCtx` (Step.lean:2103-2120) with exhibits scattered across them; the raw `wp_load` (admitted consumerless, README.md:457-460); `wps_frame` (value-channel-only frame, Wps.lean:371-374, superseded by `wps_frame_labels`); the two `*_terminates` theorems. Four names for the boring triple is not pristine.

Documentation precision. The README hypothesis table is exact. But: (i) both front documents are saturated with process vocabulary that has no meaning to the intended reader ("QA-1", "QA-2", "P6.1", "R-03", "S1b", "D3", "arc", "slice", "plant-tested", "trio-exact", "lane", "seam", "speedbump", "[USER 2026-09-02]" on nearly every page); (ii) the WALKTHROUGH's in-text file:line citations are mostly stale — checked: `wps_memop_ptreq` cited "Wps.lean:1503-1509" is at 1619; `wpt_memop_ptreq` "Wpt.lean:685" is at 859; `Step.memop_ptreq` "Step.lean:1173" is at 1373; `eqPtrval_cell_null` "Heap.lean:207-218" is at 223-233; `wps_load_at`'s `hdec` "Wps.lean:1854" is at 2010-2018; `wps_create`'s `hinert` "Wps.lean:2508" is at 2655-2661; `decIndep` "Heap.lean:1479" is at 1495; `CellCoh.dec_indep` "Heap.lean:311-322" is at 319-338; `procCtx` "Step.lean:1882" is at 2111; `procCtx_labels` "Step.lean:1925" is at 2154; `LabeledAt` "Soundness.lean:2694" is at 1945; `driver2_done`/`cases hmode` "DriverCollapse.lean:929-985 … :967" is at 525ff/563 (also in README.md:276-277); `loop_labeledAt_production` "ProdEntry.lean:536" is at 435 (also README.md:305 vicinity); `counter_loop_certified` "LoopExhibit.lean:438" is at 424; the README's "`Frag.store/load/create`, Soundness.lean:3585-3597" (README.md:162) is at 3020-3031. A document whose stated convention is "every claim names a theorem you can `grep`" (WALKTHROUGH.md:9-10) must not ship with line numbers that are wrong; either drop them (names suffice) or generate them. (iii) Both documents are far too long for their purpose (README 657 lines, WALKTHROUGH 1258 lines) because they narrate history rather than describe the artifact.

### Q7. Alignment with the academic goal

The logic proper (Heap, Rules, Wps, Wpt: ~8,700 lines) is a classical separation logic over Core in the Reynolds/O'Hearn sense, with the label-context treatment of control being the right generalization for `save`/`run`. The certification (Step, Soundness, Round: ~6,900 lines) and the production collapse (DriverCollapse, ProdLoop, ProdEntry: ~2,500 lines) are engineering around an engine, but they are the engineering the goal demands — the exports must be about the real semantics, and the production lane is what makes at least the total exports literally about the shipped pipeline. Scope has not crept in features (dispose and procedures are deferred as ruled; nothing beyond classical SL is present). Scope has crept in *multiplicity*: two full rule sets that duplicate every proof, four triple notions, three drive notions, three context profiles. The "logic" is at risk of becoming an artifact around an engine not because of what it contains but because of how many times it contains it. The allocation-capacity design (Q1) is the one place where a non-classical shape has been adopted without the alternative being weighed.

## 3. Required fixes

Each: location; what is wrong; what satisfies me.

1. **Adequacy.lean, `MemTripleU`/`MemTripleU_alloc`/`SemTripleU`/`engine_adequacyU`/`drive_classifyU` (Adequacy.lean:794-812, 858-880, 1075-1086, 1166-1176, 1271-1281).** The partial-correctness fuel premise `esize e + n ≤ lemDefaultFuel` (and `esize cont + n ≤ lemDefaultFuel` per label) is coupled to the drive length `n`, making the partial statements vacuous on long runs while the total statements are not. Satisfying statement: `MemTripleU` with the premises `pot e ≤ lemDefaultFuel` and `∀ l params cont, lookupLabel M.labels l = some (params, cont) → pot cont ≤ lemDefaultFuel`, quantifying `∀ (n : Nat)` with no fuel bound on `n`; `drive_classifyU` re-proved with `Frag.pot_step_bound` and `Frag.esize_le_pot` in place of `Frag.esize_step_bound`; every `*_certified` restated accordingly (the `hfuel`/`hfuel2` hypotheses become the static `pot` facts, which are `rfl`-closed for the authored programs).

2. **Adequacy.lean:1207-1221 and 1304-1319, `project_triple`/`project_triple_alloc`.** The conclusion of the headline "boring triple" theorem contains Iris (`SpikeGS`, `CohG`, `metaInterp`, `byteInterp`, `cellOwn`, `⊢`). Satisfying statement — the boring corollary, stated and pinned in Audit.lean and made the headline in both front documents:
   ```
   theorem project_triple_pure … (ψ : CellMap → value → Mem → Prop)
     (hpost : ∀ [SpikeGS .hasLC GF] (w : CoreRVal) (R : CellMap) (σ' : Mem)
        (mm : SpikeHeapF MetaCell) (mb : SpikeHeapF CerbMem.AbsByte) (mk : SpikeHeapF AllocCursor),
        CohG σ' mm mb mk →
        iprop(Q w ∗ ([∗map] i ↦ c ∈ R, cellOwn M.tagDefs i (.own 1) c) ∗ metaInterp mm ∗ byteInterp mb)
          ⊢ (⌜ψ R w.val σ'⌝ : IProp GF)) :
     MemTripleU M (ev0 :: evs) e P ψ
   ```
   (and the `_alloc` twin), with the exhibits' readouts rewritten as its instances. `project_triple` as it stands may remain as the strongest-post lemma beneath it.

3. **README.md "Scope, exactly" (README.md:30-50) and WALKTHROUGH.md §7 (WALKTHROUGH.md:1214-1253); Soundness.lean `Frag` header.** The fragment is restricted to programs every one of whose nodes carries the empty static annotation list (`Expr []` in every `Frag` constructor and every `*Redex`, Soundness.lean:275-293, 458-473, 3018-3098), and the forcing fact is undocumented. Satisfying sentence, in "Scope, exactly": "Every node of a fragment program carries the empty static annotation list (`Expr []`): `step_ctx` rewrites the thread's `current_loc` from a located annotation (Core_reduction.lean, `get_loc e_annots`), and this package keeps `current_loc` in the immutable `MachineCtx`, so located Core — in particular all Core produced by the C elaborator — is outside `Frag`. Making `current_loc` live state is the named mover."

4. **README.md:190-199 (trust claim 1), WALKTHROUGH.md:27-28, 370-376.** The drive-lane exports' referent is described as "the driver's request discharge"; it is `dischargeStep`, a hand-written projection certified against the shipped driver only along the total lane (`loop_step_frag`). Satisfying sentence, placed where the trust claim is made: "In the drive lanes the execution function is `driveU`, this package's definition of the sequential driver's round loop over the engine's `step_ctx`; it is tied to the shipped driver by `loop_step_frag` only along mirror steps, and no partial-correctness statement about the shipped pipeline is proved (the production driver's fuel-exhaustion leaf is opaque, so none can be). The production lane's referent is the shipped `runND ∘ Driver.drive ∘ initial_driver_state`, for total statements only."

5. **TotalAdequacy.lean:1063-1074 `wpt_strongly_normalizing`; ListRevExhibit.lean:2074-2083 `list_reverse_terminates`; FibExhibit.lean:667-671 `fib_terminates`; README.md exhibits table rows for them.** These are theorems about the mirror relation `Step` (via `Language.ErasedStep`), listed as closed-program exports under a trust claim whose referents are "cerberus-lean's semantics". Satisfying resolution: either delete the three (the `.done` equations at explicit fuel already imply engine termination) or move them out of the exports table into a clearly labelled "facts about the interior relation" list with the sentence "these theorems are about `Step`, not the engine, and cannot be transported to it".

6. **WALKTHROUGH.md and README.md, all in-text `File.lean:NNN` citations.** Most are stale (list in Q6). Satisfying resolution: remove line numbers from both front documents and cite by declaration name only, or generate the citations mechanically at build time. Do not ship a document whose convention is "you can grep it" with numbers that grep refutes.

7. **README.md and WALKTHROUGH.md, throughout.** Process vocabulary (`QA-1`, `QA-2`, `P6.1`, `R-03`, `S1b`, `D3`, `[USER 2026-09-02]`, "arc", "slice", "lane", "seam", "speedbump", "plant-tested", "trio-exact") appears on nearly every page of documents addressed to "a reader who knows separation logic and roughly what Iris is, and has never heard of Cerberus". Satisfying resolution: the two front documents describe the artifact as it is, in the standard vocabulary of the field, with every process reference moved to the dated records; a reader who has never seen this project's issue tracker must be able to read both without a glossary.

8. **Rules.lean / Wps.lean / Wpt.lean, the memory rules.** Each small axiom is proved three times (`wp_store` Rules.lean:157, `wps_store` Wps.lean:1758, `wpt_store` Wpt.lean:2237; likewise load, `_at`, `_cell_at`, create), by repeating the same ~80-line unfolding against `Step`. Satisfying statements: lifting lemmas of the form
   ```
   theorem wps_of_wp_atomic (hnv : toVal e = none) (hnj : jumpRedex? e = none)
     (hatom : ∀ ρ σ e' ρ' σ', Step M (e, ρ, σ) (e', ρ', σ') → (toVal e').isSome) :
     WP (⟨e, ρ, M⟩ : CoreRt) @ NotStuck; ⊤ {{ w, Ψ w.w w.ρ }} ⊢ wps M Ls Ψ e ρ
   ```
   and its `wpt` twin at budget `1 + deliveryCost`, with every `wps_*`/`wpt_*` memory rule derived from the corresponding raw-WP rule in a few lines. One proof per small axiom.

## 4. Recommended improvements

- **Allocation capacity as an additive resource.** Replace the ordered plan `allocCap reqs` with a byte budget `allocBudget b` satisfying `allocBudget (s + t) ⊣⊢ allocBudget s ∗ allocBudget t`, with `wps_create` consuming `sizeof ty + align − 1` (sound by `alignDown((la − s), al) ≥ la − s − al + 1`); if the plan shape is kept, the README's "Allocation capacity, and the failure policy" must say why the additive alternative was rejected and state plainly that capacity cannot be split across ∗.
- **Discharge `hlib`.** Prove `applyMemM (storeM tds l …) σ = applyMemM (storeM tds l' …) σ` (and for `loadM`, `allocateObject`) and drop `isLibraryLocation loc = false` from `Frag.store/load/create` and every exhibit.
- **Prove or explain `Frag.case_value`'s `hbsz`.** `esize` ignores pure expressions; `subst_sym_expr` substitutes into pure expressions; the bound should be a lemma.
- **Collapse the triple and drive vocabulary.** One boring triple (`MemTripleU`, with `_alloc` as its launch-premise variant), one drive (`driveU`), one context profile; retire `SemTriple`, `ProvenTriple`, `semantic_triple_sound`, `semantic_frame`, `drive`, `driveJ`, `spikeCtx`/`rsCtx` duplication, `wps_frame`, the consumerless `wp_load` (or give it a consumer via fix 8).
- **Make `current_loc` live state** (part of the runtime tuple, as `env` is) so that located Core enters `Frag`; this is the mover for fix 3.
- **Walkthrough §3.1**: list `StorableAt`'s five fields with their engine arms; say in one sentence that program variables (`lets` bindings) are not heap and not in the assertion language, so the conditional rule carries the guard's verdict as a pure fact of `ρ`.
- **Walkthrough §4**: one sentence that assertions have Iris's resource semantics, and that the only direct heap-predicate reading is the pure `Sat`/`CellCoh` on the pre side and the pure consequences on the post side.
- **Metadata should record `isReadonly`** rather than `CellCoh.alloc` fixing `al.isReadonly = .IsWritable` (Heap.lean:321-323): a fractional `pointsToCell` currently still asserts a writable allocation, so read-only objects cannot be described at all.
- **Shorten both front documents** by at least half once the process narrative is moved out; the README's exhibits table and trust diagram are the parts worth keeping verbatim.

## 5. Grade

**B+.**

What separates this from an A-: the headline theorem's conclusion is not the boring triple it is advertised as, and the partial-correctness exports carry a run-length-coupled fuel premise that the tree's own lemmas already discharge — two defects in the *statements* of the main results, which for a logic whose entire purpose is the exported statement are not cosmetic; everything else on the required list is presentation and hygiene that a pristine logic would not have.
