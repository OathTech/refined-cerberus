/-
CerberusHeapLang.LoopExhibit — THE FIRST LOOP EXHIBIT: a counter
loop through the REAL engine end-to-end. The simplest program with
a back edge, and the template every later loop exhibit follows
(fib, array-sum, list-reverse).

THE PROGRAM (authored Core, all metadata quantified):

    save loop: (x : integer := n) in
      if (x > 0) then
        lets _ = store(int, c, Specified 7) in run loop(x - 1)
      else pure(Unit)

- Esave entry binds the counter; Eif's BIG-STEP guard is the real
  `x > 0` through the certified pure evaluator; the back edge is a
  REAL context-discarding Erun with the computed argument `x - 1`;
  the body stores through the certified store rule under the loop.
- The label map `Q` is the singleton registering `loop ↦
  ([(x, integer)], body)`; the run state ties it at the current
  procedure (`LabeledAt` — the donor's `⌜Q = f_code⌝`).
- VERIFIED via the per-label invariant rule (`blockSpecs_intro` — no
  Löb) + `wps_sound` (the one Löb) and EXPORTED through the
  jump-profile engine adequacy (`engine_adequacyJ`): the CONCLUSION
  quantifies over engine objects only — driveJ from the
  proc-carrying thread never kills, never derails, and a delivered
  value is `Vunit` with the cell's final bytes pinned by the
  data-dependent post (`n = 0` → untouched; `0 < n` → the stored
  image). Partial correctness with in-budget fuel hypotheses (the
  variant route past them is demonstrated by `fib_certified_total`,
  FibExhibit.lean).

THE ENV-FRAME SEAM (alloc arc P4.3, R-08 — the representation
accident REMOVED): the per-label invariant carries the reachable-frame
predicate `SymFrame` (EnvLaws.lean) and every lookup goes through THE
LOOKUP LAW `envAdd_lookup`, exactly as the later exhibits do. The
former exact-shape pin `IsXFrame` (a one-node `Fmap` tree at `xSym`)
is gone; the entry environment is ANY reachable frame over any tail,
and the irrelevant-binding tests (`loop_wps_irrelevant_binding`,
`counter_loop_certified_irrelevant_binding`) run the loop from a frame
carrying an unrelated binding — a configuration no exact-shape pin
could have matched, so the proof cannot regress to map equality.
-/
import CerberusHeapLang.Adequacy
import CerberusHeapLang.Wps
import CerberusHeapLang.EnvLaws
import CerberusHeapLang.Wpt
import CerberusHeapLang.TotalAdequacy

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Map

/-! ## The program -/

def loopSym : sym := Symbol "" 101 SD_None
def xSym : sym := Symbol "" 102 SD_None
def loopProcSym : sym := Symbol "" 103 SD_None
/-- An unrelated symbol for the irrelevant-binding tests (R-08). -/
def ySym : sym := Symbol "" 104 SD_None

/-- Core mathematical-integer value. -/
def ivVal (i : Int) : value := Vobject (OVinteger (CerbMem.integerIval i))

/-- The guard `x > 0`. -/
def guardPe : generic_pexpr Unit sym :=
  Pexpr [] () (PEop binop.OpGt (Pexpr [] () (PEsym xSym))
    (Pexpr [] () (PEval (ivVal 0))))

/-- The back-edge argument `x - 1`. -/
def decPe : generic_pexpr Unit sym :=
  Pexpr [] () (PEop binop.OpSub (Pexpr [] () (PEsym xSym))
    (Pexpr [] () (PEval (ivVal 1))))

/-- The registered loop body. -/
def loopBody (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (mo : memory_order) (bty : core_base_type)
    (c : CerbMem.PointerValue) : CoreExpr :=
  Expr [] (Eif guardPe
    (sseqExpr bty (storeExpr loc ann intTy c sevenVal mo)
      (Expr [] (Erun ra loopSym [decPe])))
    (ofVal (.pure Vunit)))

/-- The whole program: the save entry binding `x := n`. -/
def loopProg (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (mo : memory_order) (bty xbty : core_base_type)
    (sbty : core_base_type) (c : CerbMem.PointerValue) (n : Int) : CoreExpr :=
  Expr [] (Esave (loopSym, sbty)
    [(xSym, ((xbty, (none : Option (ctype × pass_by_value_or_pointer))),
      Pexpr [] () (PEval (ivVal n))))]
    (loopBody loc ann ra mo bty c))

/-- The label map: `loop` registered with the sseq-extended body
    (which at this top-level program IS the save body — the
    registration discipline's collect on a trailing-position save). -/
def loopQ (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (mo : memory_order) (bty xbty : core_base_type)
    (c : CerbMem.PointerValue) : LabelMap :=
  fmapAddBy symCmpL loopSym
    ([(xSym, xbty)], loopBody loc ann ra mo bty c) fmapEmpty

/-- The run state carrying the two-level `labeled` tie at the
    current procedure. -/
def loopRS (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (mo : memory_order) (bty xbty : core_base_type)
    (c : CerbMem.PointerValue) : core_run_state :=
  { spikeRunState with
      labeled := fmapAddBy symCmpL loopProcSym
        (loopQ loc ann ra mo bty xbty c) fmapEmpty }

section LoopFacts

variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (mo : memory_order) (bty xbty : core_base_type)
  (c : CerbMem.PointerValue)

/-- The label resolves. -/
theorem loopQ_lookup :
    lookupLabel (loopQ loc ann ra mo bty xbty c) loopSym =
      some ([(xSym, xbty)], loopBody loc ann ra mo bty c) := by
  unfold lookupLabel loopQ
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

/-- The singleton map's ONLY entry (any successful lookup returns
    it). -/
theorem loopQ_inv {l : sym} {params : List (sym × core_base_type)}
    {cont : CoreExpr}
    (h : lookupLabel (loopQ loc ann ra mo bty xbty c) l = some (params, cont)) :
    params = [(xSym, xbty)] ∧ cont = loopBody loc ann ra mo bty c := by
  unfold lookupLabel loopQ at h
  rw [fmapLookupBy_addBy_empty] at h
  split at h
  · obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
    exact ⟨h1.symm ▸ rfl, h2.symm ▸ rfl⟩
  · cases h

/-- The Q↔labeled tie holds of the exhibit's run state. -/
theorem loopRS_labeledAt :
    LabeledAt (loopRS loc ann ra mo bty xbty c) loopProcSym
      (loopQ loc ann ra mo bty xbty c) := by
  unfold LabeledAt loopRS
  show fmapLookupBy _ _ (fmapAddBy symCmpL loopProcSym _ fmapEmpty) = _
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

/-! ## The env frames: any reachable frame, through THE LOOKUP LAW -/

/-- The counter's binding is found in the head frame, whatever else
    the frame holds (`envAdd_lookup`, the lookup-after-add law over
    reachable frames). -/
theorem lookup_env_x {f : Fmap sym value} (hf : SymFrame f) (v : value)
    (rest : List (Fmap sym value)) :
    lookup_env (a := value) xSym (envAdd xSym v f :: rest) = some v :=
  lookup_env_head (by rw [envAdd_lookup hf symCmpK, if_pos (by decide +kernel)]) rest

/-! ## Evaluation facts at any reachable frame -/

theorem guard_eval {f : Fmap sym value} (hf : SymFrame f) (i : Int)
    (rest : List (Fmap sym value)) :
    evalPexpr fmapEmpty fmapEmpty (envAdd xSym (ivVal i) f :: rest) guardPe =
      some (boolValue (decide (0 < i))) := by
  unfold guardPe
  rw [evalPexpr_op]
  rw [show evalPexpr fmapEmpty fmapEmpty (envAdd xSym (ivVal i) f :: rest)
      (Pexpr [] () (PEsym xSym)) = some (ivVal i) from by
      rw [evalPexpr_sym_empty]; exact lookup_env_x hf (ivVal i) rest]
  show evalBinop binop.OpGt (ivVal i) (ivVal 0) = _
  unfold evalBinop ivVal
  show (CerbMem.ltIval (CerbMem.integerIval 0)
    (CerbMem.integerIval i)).map boolValue = _
  rfl

theorem dec_eval {f : Fmap sym value} (hf : SymFrame f) (i : Int)
    (rest : List (Fmap sym value)) :
    evalPexprs fmapEmpty fmapEmpty (envAdd xSym (ivVal i) f :: rest) [decPe] =
      some [ivVal (i - 1)] := by
  rw [evalPexprs_cons]
  rw [show evalPexpr fmapEmpty fmapEmpty (envAdd xSym (ivVal i) f :: rest) decPe =
      some (ivVal (i - 1)) from by
    unfold decPe
    rw [evalPexpr_op]
    rw [show evalPexpr fmapEmpty fmapEmpty (envAdd xSym (ivVal i) f :: rest)
        (Pexpr [] () (PEsym xSym)) = some (ivVal i) from by
        rw [evalPexpr_sym_empty]; exact lookup_env_x hf (ivVal i) rest]
    rfl]
  rfl

end LoopFacts

/-! ## The binding computations at the concrete parameter list -/

theorem bindArgs_x (b : core_base_type) (v : value) (f : Fmap sym value)
    (rest : List (Fmap sym value)) :
    bindArgs [(xSym, b)] [v] (f :: rest) = envAdd xSym v f :: rest := by
  show update_env (mk_sym_pat xSym b) v (f :: rest) = _
  rw [update_env_cons, update_env_aux_sym]

theorem bindSave_x (xbty : core_base_type) (n : Int)
    (f : Fmap sym value) (rest : List (Fmap sym value)) :
    bindSaveParams
      [(xSym, ((xbty, (none : Option (ctype × pass_by_value_or_pointer))),
        Pexpr [] () (PEval (ivVal n))))] [ivVal n] (f :: rest) =
      envAdd xSym (ivVal n) f :: rest := by
  show update_env (mk_sym_pat xSym xbty) (ivVal n) (f :: rest) = _
  rw [update_env_cons, update_env_aux_sym]

/-! ## The Iris layer: invariant, body, block specs, entry, WP -/

section LoopIris

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (mo : memory_order) (bty xbty : core_base_type)
  (c : CerbMem.PointerValue) (n : Int) (bs0 : List CerbMem.AbsByte)
-- S1b: the wps judgment is indexed by the MACHINE CONTEXT; the
-- exhibit works at the jump-profile instance `procCtx p rs` with the
-- label map tied by the honest `LabeledAt` link (`procCtx_labels`).
variable (p : sym) (rs : core_run_state)
  (hQ : LabeledAt rs p (loopQ loc ann ra mo bty xbty c))

/-- The postcondition: unit value; the cell untouched iff the loop
    never ran (data-dependent). -/
abbrev loopPost : SpikeVal → EnvStack → IProp GF := fun w _ =>
  iprop(⌜w.val = Vunit⌝ ∗
    ((⌜n = 0⌝ ∗ pointsToCell fmapEmpty c (.own 1) intTy bs0) ∨
     (⌜0 < n⌝ ∗ pointsToCell fmapEmpty c (.own 1) intTy (sevenBytes fmapEmpty))))

/-- THE PER-LABEL INVARIANT: the argument is the counter `i ∈ [0, n]`;
    the env is ANY reachable frame (`SymFrame`) over any tail; the
    cell is the entry bytes before the first iteration and the stored
    image after. -/
abbrev loopLs : LabelSpec GF := fun _ vs ρ =>
  (iprop(∃ (i : Int) (f : Fmap sym value) (rest : List (Fmap sym value)),
    ⌜vs = [ivVal i] ∧ 0 ≤ i ∧ i ≤ n ∧ ρ = f :: rest ∧ SymFrame f⌝ ∗
    ((⌜i = n⌝ ∗ pointsToCell fmapEmpty c (.own 1) intTy bs0) ∨
     (⌜i < n⌝ ∗ pointsToCell fmapEmpty c (.own 1) intTy (sevenBytes fmapEmpty)))) : IProp GF)

include hQ

/-- The loop body verifies at any reachable counter frame (the shared
    lemma behind both the block spec and the entry). -/
theorem loop_body_wps (i : Int) (f : Fmap sym value)
    (rest : List (Fmap sym value)) (hf : SymFrame f)
    (h0 : 0 ≤ i) (hin : i ≤ n) :
    iprop(((⌜i = n⌝ ∗ pointsToCell (procCtx p rs).tagDefs (GF := GF) c (.own 1) intTy bs0) ∨
      (⌜i < n⌝ ∗ pointsToCell (procCtx p rs).tagDefs c (.own 1) intTy (sevenBytes (procCtx p rs).tagDefs)))) ⊢
      wps (procCtx p rs) (loopLs c n bs0)
        (loopPost c n bs0) (loopBody loc ann ra mo bty c)
        (envAdd xSym (ivVal i) f :: rest) := by
  rw [show (loopBody loc ann ra mo bty c) =
    Expr [] (Eif guardPe
      (sseqExpr bty (storeExpr loc ann intTy c sevenVal mo)
        (Expr [] (Erun ra loopSym [decPe])))
      (ofVal (.pure Vunit))) from rfl]
  by_cases hpos : 0 < i
  · -- guard TRUE: store then jump at i - 1
    iintro Hcell
    iapply wps_if_true [] guardPe _ _ _
      (by rw [procCtx_extern, guard_eval hf i rest, decide_eq_true hpos]; rfl)
    rw [show (sseqExpr bty (storeExpr loc ann intTy c sevenVal mo)
        (Expr [] (Erun ra loopSym [decPe]))) =
      Expr [] (Esseq (Pattern [] (CaseBase (none, bty)))
        (storeExpr loc ann intTy c sevenVal mo)
        (Expr [] (Erun ra loopSym [decPe]))) from rfl]
    iapply wps_seq
    -- the cell is owned either way; store the image
    icases Hcell with (⟨%hieq, Hc⟩ | ⟨%hlt, Hc⟩) <;>
      (iapply wps_store loc ann intTy c sevenVal mo sevenMval _ _
        seven_encodes (seven_storable _)
       isplitl [Hc]
       · iexact Hc
       iintro %fp Hc
       iapply wps_run [] ra loopSym [decPe] _ _
         (by rw [procCtx_labels hQ]
             exact loopQ_lookup loc ann ra mo bty xbty c)
         (dec_eval hf i rest)
       iexists (i - 1), (envAdd xSym (ivVal i) f), rest
       isplit
       · ipureintro
         exact ⟨rfl, by omega, by omega, rfl, hf.add _ _⟩
       iright
       isplit
       · ipureintro; omega
       rw [show (sevenBytes (procCtx p rs).tagDefs) = (CerbMem.memValueToBytes (procCtx p rs).tagDefs [] sevenMval).2 from rfl]
       iexact Hc)
  · -- guard FALSE: exit with the final cell state
    have hz : i = 0 := by omega
    subst hz
    iintro Hcell
    iapply wps_if_false [] guardPe _ _ _
      (by rw [procCtx_extern, guard_eval hf 0 rest,
        decide_eq_false hpos]; rfl)
    iapply wps_ofVal (.pure Vunit)
    unfold loopPost
    isplit
    · ipureintro; rfl
    icases Hcell with (⟨%hieq, Hc⟩ | ⟨%hlt, Hc⟩)
    · ileft
      isplit
      · ipureintro; omega
      · iexact Hc
    · iright
      isplit
      · ipureintro; omega
      · iexact Hc

/-- THE BLOCK SPECIFICATION, by the per-label invariant rule (NO
    Löb — the back edge discharged against the invariant at `i-1`
    through the jump clause). -/
theorem loop_blockSpecs :
    ⊢ blockSpecs (GF := GF) (procCtx p rs)
      (loopLs c n bs0) (loopPost c n bs0) := by
  refine blockSpecs_intro fun l params cont vs ev0 evs hl => ?_
  rw [procCtx_labels hQ] at hl
  obtain ⟨rfl, rfl⟩ := loopQ_inv loc ann ra mo bty xbty c hl
  iintro ⟨%i, %f, %rest, %hpure, Hcell⟩
  obtain ⟨rfl, h0, hin, hρ, hf⟩ := hpure
  obtain ⟨rfl, rfl⟩ : f = ev0 ∧ rest = evs := by
    have h1 := congrArg (fun l => l.head?) hρ
    have h2 := congrArg (fun l => l.tail) hρ
    simp at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  rw [bindArgs_x]
  iapply loop_body_wps loc ann ra mo bty xbty c n bs0 p rs hQ i f rest hf
    h0 hin $$ Hcell

/-- The whole program's statement WP from ANY reachable entry frame
    `f` over any tail (alloc arc P4.3: the entry environment is no
    longer the fixed `[fmapEmpty]`). -/
theorem loop_wps (hn : 0 ≤ n) (sbty : core_base_type)
    (f : Fmap sym value) (hf : SymFrame f) (rest : List (Fmap sym value)) :
    pointsToCell (procCtx p rs).tagDefs (GF := GF) c (.own 1) intTy bs0 ⊢
      wps (procCtx p rs) (loopLs c n bs0)
        (loopPost c n bs0)
        (loopProg loc ann ra mo bty xbty sbty c n) (f :: rest) := by
  iintro Hc
  rw [show (loopProg loc ann ra mo bty xbty sbty c n) =
    Expr [] (Esave (loopSym, sbty)
      [(xSym, ((xbty, (none : Option (ctype × pass_by_value_or_pointer))),
        Pexpr [] () (PEval (ivVal n))))]
      (loopBody loc ann ra mo bty c)) from rfl]
  iapply wps_save [] (loopSym, sbty) _ _ f rest
    (cvals := [ivVal n]) rfl
  rw [bindSave_x]
  iapply loop_body_wps loc ann ra mo bty xbty c n bs0 p rs hQ n f rest
    hf hn (by omega)
  ileft
  isplit
  · ipureintro; rfl
  · iexact Hc

/-- THE IRRELEVANT-BINDING TEST (R-08): the loop verifies from an
    entry frame carrying an unrelated binding `y ↦ junk`. No
    exact-shape pin of the frame could match this configuration; the
    proof goes through the lookup law alone. -/
theorem loop_wps_irrelevant_binding (hn : 0 ≤ n) (sbty : core_base_type)
    (junk : value) :
    pointsToCell (procCtx p rs).tagDefs (GF := GF) c (.own 1) intTy bs0 ⊢
      wps (procCtx p rs) (loopLs c n bs0)
        (loopPost c n bs0)
        (loopProg loc ann ra mo bty xbty sbty c n)
        [envAdd ySym junk fmapEmpty] :=
  loop_wps loc ann ra mo bty xbty c n bs0 p rs hQ hn sbty
    (envAdd ySym junk fmapEmpty) (symFrame_empty.add _ _) []

omit hQ in
/-- The per-value readout of the loop postcondition. -/
theorem loop_readout_val (w : CoreRVal) :
    loopPost (GF := GF) c n bs0 w.w w.ρ ⊢
      iprop(∀ (σ' : Mem) (ns : Nat) (κs : List Empty) (nt : Nat),
        stateInterp σ' ns κs nt ={⊤, ∅}=∗
          ⌜w.val = Vunit ∧ ∃ bs',
            ((n = 0 ∧ bs' = bs0) ∨ (0 < n ∧ bs' = (sevenBytes fmapEmpty))) ∧
            ∃ i a, c = cellPtr i a ∧ CellCoh fmapEmpty σ' i ⟨a, intTy, bs'⟩⌝) := by
  rw [show (loopPost (GF := GF) c n bs0 w.w w.ρ) =
    (iprop(⌜SpikeVal.val w.w = Vunit⌝ ∗
      ((⌜n = 0⌝ ∗ pointsToCell fmapEmpty c (.own 1) intTy bs0) ∨
       (⌜0 < n⌝ ∗ pointsToCell fmapEmpty c (.own 1) intTy (sevenBytes fmapEmpty)))) : IProp GF)
    from rfl]
  iintro ⟨%hval, Hd⟩
  icases Hd with (⟨%hn0, Hcell⟩ | ⟨%hpos, Hcell⟩)
  · ihave Hro := pointsToCell_readout fmapEmpty c (.own 1) intTy bs0 $$ Hcell
    iintro %σ' %ns %κs %nt Hσ
    imod Hro $$ %σ' %ns %κs %nt Hσ with %hfact
    imodintro
    ipureintro
    exact ⟨hval, bs0, .inl ⟨hn0, rfl⟩, hfact⟩
  · ihave Hro := pointsToCell_readout fmapEmpty c (.own 1) intTy (sevenBytes fmapEmpty) $$ Hcell
    iintro %σ' %ns %κs %nt Hσ
    imod Hro $$ %σ' %ns %κs %nt Hσ with %hfact
    imodintro
    ipureintro
    exact ⟨hval, (sevenBytes fmapEmpty), .inr ⟨hpos, rfl⟩, hfact⟩

/-- The base-WP face with the engine readout (what `engine_adequacyJ`
    consumes), from any reachable entry frame over any tail. -/
theorem loop_wp_readout (hn : 0 ≤ n) (sbty : core_base_type)
    (f : Fmap sym value) (hf : SymFrame f) (rest : List (Fmap sym value)) :
    pointsToCell (procCtx p rs).tagDefs (GF := GF) c (.own 1) intTy bs0 ⊢
      WP (⟨loopProg loc ann ra mo bty xbty sbty c n, f :: rest,
          procCtx p rs⟩ : CoreRt) @ Stuckness.NotStuck; ⊤
        {{ w, iprop(∀ (σ' : Mem) (ns : Nat) (κs : List Empty) (nt : Nat),
          stateInterp σ' ns κs nt ={⊤, ∅}=∗
            ⌜w.val = Vunit ∧ ∃ bs',
              ((n = 0 ∧ bs' = bs0) ∨ (0 < n ∧ bs' = (sevenBytes (procCtx p rs).tagDefs))) ∧
              ∃ i a, c = cellPtr i a ∧ CellCoh (procCtx p rs).tagDefs σ' i ⟨a, intTy, bs'⟩⌝) }} := by
  refine ((loop_wps loc ann ra mo bty xbty c n bs0 p rs hQ hn sbty f hf rest).trans ?_)
  refine (BI.emp_sep.2.trans (BI.sep_mono
    ((loop_blockSpecs loc ann ra mo bty xbty c n bs0 p rs hQ).trans
      (wps_sound (loopProg loc ann ra mo bty xbty sbty c n) (f :: rest)))
    .rfl)).trans ?_
  refine BI.wand_elim_left.trans ?_
  exact wp_mono fun w => loop_readout_val c n bs0 w

end LoopIris

/-! ## THE END-TO-END CERTIFIED-LOOP THEOREM (engine vocabulary
only in the conclusion) -/

section LoopDrive

variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (mo : memory_order) (bty xbty : core_base_type)
  (c : CerbMem.PointerValue)

/-- The body is in the certified extended cone. -/
theorem loopBody_fragJ (hlib : CerbLocation.isLibraryLocation loc = false) :
    Frag (loopBody loc ann ra mo bty c) := by
  refine .if_ (by decide +kernel) (.sseq (.store hlib) (.run ?_))
    (.val_pure Vunit)
  intro pe hpe
  simp at hpe
  subst hpe
  exact (by decide +kernel : peDepth decPe ≤ lemDefaultFuel)

/-- THE EXHIBIT: driving the REAL engine ({step_ctx → sequential
    discharge} at the proc-carrying thread, the label map tied
    through `core_run_state.labeled`) on the authored counter loop,
    from ANY memory whose seeded cell footprint is satisfied: the
    engine never kills (no UB), never derails, and any delivered
    value is `Vunit` with the cell's final bytes decided by the
    loop's data: untouched for `n = 0`, the stored image for
    `0 < n`. Partial correctness; the two fuel hypotheses are the
    engine's own budgets (the R3-interim in-budget form). -/
theorem counter_loop_certified
    (sbty : core_base_type) (idx addr : Int) (bs0 : List CerbMem.AbsByte)
    (n : Int) (hn : 0 ≤ n)
    (hlib : CerbLocation.isLibraryLocation loc = false)
    (σ₀ : Mem)
    (hcoh : Coh fmapEmpty σ₀ ((Iris.Std.PartialMap.singleton idx
      (SpikeCell.mk addr intTy bs0)) : SpikeHeapF SpikeCell))
    (nsteps : Nat) (aids : Nat → Nat)
    (hfuel : 4 + nsteps ≤ lemDefaultFuel)
    (hfuel2 : 3 + nsteps ≤ lemDefaultFuel) :
    let prog := loopProg loc ann ra mo bty xbty sbty (cellPtr idx addr) n
    let rs := loopRS loc ann ra mo bty xbty (cellPtr idx addr)
    (∀ r, driveJ rs aids nsteps
      (procThread loopProcSym prog [fmapEmpty]) σ₀ ≠ .killed r) ∧
    (driveJ rs aids nsteps
      (procThread loopProcSym prog [fmapEmpty]) σ₀ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem),
      driveJ rs aids nsteps
        (procThread loopProcSym prog [fmapEmpty]) σ₀ = .done v σ' →
      v = Vunit ∧ ∃ bs',
        ((n = 0 ∧ bs' = bs0) ∨ (0 < n ∧ bs' = (sevenBytes fmapEmpty))) ∧
        ∃ i a, cellPtr idx addr = cellPtr i a ∧
          CellCoh fmapEmpty σ' i ⟨a, intTy, bs'⟩) := by
  intro prog rs
  refine engine_adequacyJ (GF := SpikeGF)
    (loopRS_labeledAt loc ann ra mo bty xbty (cellPtr idx addr))
    (fun l params cont hl => by
      obtain ⟨-, rfl⟩ := loopQ_inv loc ann ra mo bty xbty _ hl
      exact loopBody_fragJ loc ann ra mo bty _ hlib)
    prog fmapEmpty [] σ₀ _
    (.save (loopBody_fragJ loc ann ra mo bty _ hlib)) hcoh
    (fun v σ' => v = Vunit ∧ ∃ bs',
      ((n = 0 ∧ bs' = bs0) ∨ (0 < n ∧ bs' = (sevenBytes fmapEmpty))) ∧
      ∃ i a, cellPtr idx addr = cellPtr i a ∧ CellCoh fmapEmpty σ' i ⟨a, intTy, bs'⟩)
    ?_ nsteps aids
    (by rw [show esize prog = 4 from rfl]; omega)
    (fun l params cont hl => by
      obtain ⟨-, rfl⟩ := loopQ_inv loc ann ra mo bty xbty _ hl
      rw [show esize (loopBody loc ann ra mo bty (cellPtr idx addr)) = 3
        from rfl]
      omega)
  intro inst
  refine .trans ?_ (loop_wp_readout loc ann ra mo bty xbty (cellPtr idx addr)
    n bs0 loopProcSym rs
    (loopRS_labeledAt loc ann ra mo bty xbty (cellPtr idx addr)) hn sbty
    fmapEmpty symFrame_empty [])
  refine (BigSepM.bigSepM_singleton).1.trans ?_
  iintro Hpt
  iapply (pointsToCell_cellOwn_iff fmapEmpty _ _ _ _).mpr
  iexists idx, addr
  isplit
  · ipureintro; rfl
  · iexact Hpt

/-- THE IRRELEVANT-BINDING TEST AT THE ENGINE (R-08): the same
    conclusion when the proc-carrying thread is launched with an entry
    frame carrying an unrelated binding `y ↦ junk` — the engine's own
    `update_env`/`lookup_env` on a frame that no exact-shape pin could
    describe. -/
theorem counter_loop_certified_irrelevant_binding
    (sbty : core_base_type) (idx addr : Int) (bs0 : List CerbMem.AbsByte)
    (n : Int) (hn : 0 ≤ n) (junk : value)
    (hlib : CerbLocation.isLibraryLocation loc = false)
    (σ₀ : Mem)
    (hcoh : Coh fmapEmpty σ₀ ((Iris.Std.PartialMap.singleton idx
      (SpikeCell.mk addr intTy bs0)) : SpikeHeapF SpikeCell))
    (nsteps : Nat) (aids : Nat → Nat)
    (hfuel : 4 + nsteps ≤ lemDefaultFuel)
    (hfuel2 : 3 + nsteps ≤ lemDefaultFuel) :
    let prog := loopProg loc ann ra mo bty xbty sbty (cellPtr idx addr) n
    let rs := loopRS loc ann ra mo bty xbty (cellPtr idx addr)
    let ρ₀ : EnvStack := [envAdd ySym junk fmapEmpty]
    (∀ r, driveJ rs aids nsteps
      (procThread loopProcSym prog ρ₀) σ₀ ≠ .killed r) ∧
    (driveJ rs aids nsteps
      (procThread loopProcSym prog ρ₀) σ₀ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem),
      driveJ rs aids nsteps
        (procThread loopProcSym prog ρ₀) σ₀ = .done v σ' →
      v = Vunit ∧ ∃ bs',
        ((n = 0 ∧ bs' = bs0) ∨ (0 < n ∧ bs' = (sevenBytes fmapEmpty))) ∧
        ∃ i a, cellPtr idx addr = cellPtr i a ∧
          CellCoh fmapEmpty σ' i ⟨a, intTy, bs'⟩) := by
  intro prog rs ρ₀
  refine engine_adequacyJ (GF := SpikeGF)
    (loopRS_labeledAt loc ann ra mo bty xbty (cellPtr idx addr))
    (fun l params cont hl => by
      obtain ⟨-, rfl⟩ := loopQ_inv loc ann ra mo bty xbty _ hl
      exact loopBody_fragJ loc ann ra mo bty _ hlib)
    prog (envAdd ySym junk fmapEmpty) [] σ₀ _
    (.save (loopBody_fragJ loc ann ra mo bty _ hlib)) hcoh
    (fun v σ' => v = Vunit ∧ ∃ bs',
      ((n = 0 ∧ bs' = bs0) ∨ (0 < n ∧ bs' = (sevenBytes fmapEmpty))) ∧
      ∃ i a, cellPtr idx addr = cellPtr i a ∧ CellCoh fmapEmpty σ' i ⟨a, intTy, bs'⟩)
    ?_ nsteps aids
    (by rw [show esize prog = 4 from rfl]; omega)
    (fun l params cont hl => by
      obtain ⟨-, rfl⟩ := loopQ_inv loc ann ra mo bty xbty _ hl
      rw [show esize (loopBody loc ann ra mo bty (cellPtr idx addr)) = 3
        from rfl]
      omega)
  intro inst
  refine .trans ?_ (loop_wp_readout loc ann ra mo bty xbty (cellPtr idx addr)
    n bs0 loopProcSym rs
    (loopRS_labeledAt loc ann ra mo bty xbty (cellPtr idx addr)) hn sbty
    (envAdd ySym junk fmapEmpty) (symFrame_empty.add _ _) [])
  refine (BigSepM.bigSepM_singleton).1.trans ?_
  iintro Hpt
  iapply (pointsToCell_cellOwn_iff fmapEmpty _ _ _ _).mpr
  iexists idx, addr
  isplit
  · ipureintro; rfl
  · iexact Hpt

end LoopDrive

/-! ## THE TOTAL LANE (foundations Phase 5 — the counter loop joins
the total stratum so its PRODUCTION export can ride the total-driven
driver simulation): the fib pattern with a heap effect — the loop
body's variant budget is `5·i + 2` (per iteration: guard 1 + store 3
+ jump 1; exit: guard 1 + delivery 1), the back edge discharges the
judgment's MANDATORY decrease by arithmetic. -/

section LoopTotal

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (mo : memory_order) (bty xbty : core_base_type)
  (c : CerbMem.PointerValue) (n : Int) (bs0 : List CerbMem.AbsByte)
variable (p : sym) (rs : core_run_state)
  (hQ : LabeledAt rs p (loopQ loc ann ra mo bty xbty c))

/-- The variant-indexed label context: the partial invariant plus the
    variant pin (the loop body's budget at counter `i`). -/
abbrev loopLsT : LabelSpecT GF := fun _ m vs ρ =>
  (iprop(∃ (i : Int) (f : Fmap sym value) (rest : List (Fmap sym value)),
    ⌜vs = [ivVal i] ∧ 0 ≤ i ∧ i ≤ n ∧ m = 5 * i.toNat + 2 ∧
      ρ = f :: rest ∧ SymFrame f⌝ ∗
    ((⌜i = n⌝ ∗ pointsToCell fmapEmpty c (.own 1) intTy bs0) ∨
     (⌜i < n⌝ ∗ pointsToCell fmapEmpty c (.own 1) intTy (sevenBytes fmapEmpty)))) : IProp GF)

include hQ

/-- The loop body meets its variant budget at any reachable counter
    frame. -/
theorem loop_body_wpt (i : Int) (f : Fmap sym value)
    (rest : List (Fmap sym value)) (hf : SymFrame f)
    (h0 : 0 ≤ i) (hin : i ≤ n) :
    iprop(((⌜i = n⌝ ∗ pointsToCell (procCtx p rs).tagDefs (GF := GF) c (.own 1) intTy bs0) ∨
      (⌜i < n⌝ ∗ pointsToCell (procCtx p rs).tagDefs c (.own 1) intTy (sevenBytes (procCtx p rs).tagDefs)))) ⊢
      wpt (procCtx p rs) (loopLsT c n bs0)
        (5 * i.toNat + 2)
        (loopPost c n bs0) (loopBody loc ann ra mo bty c)
        (envAdd xSym (ivVal i) f :: rest) := by
  rw [show (loopBody loc ann ra mo bty c) =
    Expr [] (Eif guardPe
      (sseqExpr bty (storeExpr loc ann intTy c sevenVal mo)
        (Expr [] (Erun ra loopSym [decPe])))
      (ofVal (.pure Vunit))) from rfl]
  by_cases hpos : 0 < i
  · -- guard TRUE: store (3) then jump (1 + the target's budget)
    rw [show 5 * i.toNat + 2 = (5 * (i - 1).toNat + 6) + 1 by omega]
    iintro Hcell
    iapply wpt_if_true [] guardPe _ _ _
      (by rw [procCtx_extern, guard_eval hf i rest, decide_eq_true hpos]; rfl)
    rw [show (sseqExpr bty (storeExpr loc ann intTy c sevenVal mo)
        (Expr [] (Erun ra loopSym [decPe]))) =
      Expr [] (Esseq (Pattern [] (CaseBase (none, bty)))
        (storeExpr loc ann intTy c sevenVal mo)
        (Expr [] (Erun ra loopSym [decPe]))) from rfl,
      show 5 * (i - 1).toNat + 6 =
        3 + ((5 * (i - 1).toNat + 2) + 1) by omega]
    iapply wpt_seq
    icases Hcell with (⟨%hieq, Hc⟩ | ⟨%hlt, Hc⟩) <;>
      (iapply wpt_store_cell loc ann intTy c sevenVal mo sevenMval _ _
        (by omega) seven_encodes (seven_storable _)
       isplitl [Hc]
       · iexact Hc
       iintro %fp Hc
       iapply wpt_run [] ra loopSym [decPe] _ _ (5 * (i - 1).toNat + 2)
         (by rw [procCtx_labels hQ]
             exact loopQ_lookup loc ann ra mo bty xbty c)
         (dec_eval hf i rest)
         (by omega)
       iexists (i - 1), (envAdd xSym (ivVal i) f), rest
       isplit
       · ipureintro
         exact ⟨rfl, by omega, by omega, rfl, rfl, hf.add _ _⟩
       iright
       isplit
       · ipureintro; omega
       rw [show (sevenBytes (procCtx p rs).tagDefs) = (CerbMem.memValueToBytes (procCtx p rs).tagDefs [] sevenMval).2 from rfl]
       iexact Hc)
  · -- guard FALSE: exit with the final cell state (guard + delivery)
    have hz : i = 0 := by omega
    subst hz
    iintro Hcell
    rw [show 5 * (0 : Int).toNat + 2 = 1 + 1 by omega]
    iapply wpt_if_false [] guardPe _ _ _
      (by rw [procCtx_extern, guard_eval hf 0 rest,
        decide_eq_false hpos]; rfl)
    iapply wpt_ofVal (.pure Vunit) _ (Nat.le_refl 1)
    unfold loopPost
    isplit
    · ipureintro; rfl
    icases Hcell with (⟨%hieq, Hc⟩ | ⟨%hlt, Hc⟩)
    · ileft
      isplit
      · ipureintro; omega
      · iexact Hc
    · iright
      isplit
      · ipureintro; omega
      · iexact Hc

/-- THE TOTAL BLOCK SPECIFICATION for the counter loop. -/
theorem loop_blockSpecsT :
    ⊢ blockSpecsT (GF := GF) (procCtx p rs)
      (loopLsT c n bs0) (loopPost c n bs0) := by
  refine blockSpecsT_intro fun l params cont vs ev0 evs m hl => ?_
  rw [procCtx_labels hQ] at hl
  obtain ⟨rfl, rfl⟩ := loopQ_inv loc ann ra mo bty xbty c hl
  iintro ⟨%i, %f, %rest, %hpure, Hcell⟩
  obtain ⟨rfl, h0, hin, rfl, hρ, hf⟩ := hpure
  obtain ⟨rfl, rfl⟩ : f = ev0 ∧ rest = evs := by
    have h1 := congrArg (fun l => l.head?) hρ
    have h2 := congrArg (fun l => l.tail) hρ
    simp at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  rw [bindArgs_x]
  iapply loop_body_wpt loc ann ra mo bty xbty c n bs0 p rs hQ i f rest hf
    h0 hin $$ Hcell

/-- The whole program's total judgment at budget `5·n + 3`, from ANY
    reachable entry frame over any tail. -/
theorem loop_wpt (hn : 0 ≤ n) (sbty : core_base_type)
    (f : Fmap sym value) (hf : SymFrame f) (rest : List (Fmap sym value)) :
    pointsToCell (procCtx p rs).tagDefs (GF := GF) c (.own 1) intTy bs0 ⊢
      wpt (procCtx p rs) (loopLsT c n bs0)
        (5 * n.toNat + 3) (loopPost c n bs0)
        (loopProg loc ann ra mo bty xbty sbty c n) (f :: rest) := by
  iintro Hc
  rw [show (loopProg loc ann ra mo bty xbty sbty c n) =
    Expr [] (Esave (loopSym, sbty)
      [(xSym, ((xbty, (none : Option (ctype × pass_by_value_or_pointer))),
        Pexpr [] () (PEval (ivVal n))))]
      (loopBody loc ann ra mo bty c)) from rfl,
    show 5 * n.toNat + 3 = (5 * n.toNat + 2) + 1 by omega]
  iapply wpt_save [] (loopSym, sbty) _ _ f rest
    (cvals := [ivVal n]) rfl
  rw [bindSave_x]
  iapply loop_body_wpt loc ann ra mo bty xbty c n bs0 p rs hQ n f rest
    hf hn (by omega)
  ileft
  isplit
  · ipureintro; rfl
  · iexact Hc

/-- The irrelevant-binding test at the total stratum. -/
theorem loop_wpt_irrelevant_binding (hn : 0 ≤ n) (sbty : core_base_type)
    (junk : value) :
    pointsToCell (procCtx p rs).tagDefs (GF := GF) c (.own 1) intTy bs0 ⊢
      wpt (procCtx p rs) (loopLsT c n bs0)
        (5 * n.toNat + 3) (loopPost c n bs0)
        (loopProg loc ann ra mo bty xbty sbty c n)
        [envAdd ySym junk fmapEmpty] :=
  loop_wpt loc ann ra mo bty xbty c n bs0 p rs hQ hn sbty
    (envAdd ySym junk fmapEmpty) (symFrame_empty.add _ _) []

omit hQ in
/-- The postcondition entails the engine readout (the launch-facing
    face — the SpikeVal-indexed form of `loop_readout_val`). -/
theorem loopPost_to_readout :
    ∀ (w : SpikeVal) (ρ' : EnvStack), loopPost (GF := GF) c n bs0 w ρ' ⊢
      readoutPost (fun v σ' => v = Vunit ∧ ∃ bs',
        ((n = 0 ∧ bs' = bs0) ∨ (0 < n ∧ bs' = (sevenBytes fmapEmpty))) ∧
        ∃ i a, c = cellPtr i a ∧ CellCoh fmapEmpty σ' i ⟨a, intTy, bs'⟩) w ρ' :=
  fun w ρ' => loop_readout_val c n bs0 (⟨w, ρ', spikeCtx⟩ : CoreRVal)

end LoopTotal

end CerberusHeapLang
