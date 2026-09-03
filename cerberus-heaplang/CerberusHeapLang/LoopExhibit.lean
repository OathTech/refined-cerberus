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
  engine adequacy at the proc-carrying context (`engine_adequacyU`):
  the CONCLUSION quantifies over engine objects only — `driveU` from the
  proc-carrying thread never kills, never derails, and a delivered
  value is `Vunit` with the cell's final bytes pinned by the
  data-dependent post (`n = 0` → untouched; `0 < n` → the stored
  image). Partial correctness at EVERY drive length: the statement
  carries no fuel hypothesis (the static `pot` bounds are discharged
  inside the proof); the total form of the same shape is
  `fib_certified_total`, FibExhibit.lean.

THE ENVIRONMENT: the per-label invariant carries the reachable-frame
predicate `SymFrame` (EnvLaws.lean) and every lookup goes through THE
LOOKUP LAW `envAdd_lookup`, exactly as the later exhibits do — no
frame-shape pin. The entry environment is ANY reachable frame over any
tail, and the irrelevant-binding tests (`loop_wps_irrelevant_binding`,
`counter_loop_certified_irrelevant_binding`) run the loop from a frame
carrying an unrelated binding — a configuration no exact-shape pin
could match, so the proof cannot regress to map equality.
-/
import CerberusHeapLang.API
import CerberusHeapLang.Examples.Layout

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
-- exhibit works at the jump-profile instance `procCtx rs` (entry control
-- `procCtl p`: empty stack, in procedure `p`; calls arc C1) with the
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
    iprop(((⌜i = n⌝ ∗ pointsToCell (procCtx rs).tagDefs (GF := GF) c (.own 1) intTy bs0) ∨
      (⌜i < n⌝ ∗ pointsToCell (procCtx rs).tagDefs c (.own 1) intTy (sevenBytes (procCtx rs).tagDefs)))) ⊢
      wps (procCtx rs) (procCtl p) (loopLs c n bs0)
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
       rw [show (sevenBytes (procCtx rs).tagDefs) = (CerbMem.memValueToBytes (procCtx rs).tagDefs [] sevenMval).2 from rfl]
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
    ⊢ blockSpecs (GF := GF) (procCtx rs) (procCtl p)
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
    pointsToCell (procCtx rs).tagDefs (GF := GF) c (.own 1) intTy bs0 ⊢
      wps (procCtx rs) (procCtl p) (loopLs c n bs0)
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

omit hQ in
/-- The per-value readout of the loop postcondition. -/
theorem loop_readout_val (w : CoreRVal) :
    loopPost (GF := GF) c n bs0 w.w w.ρ ⊢
      iprop(∀ (σ' : Mem) (ns : Nat) (κs : List Empty) (nt : Nat),
        stateInterp σ' ns κs nt ={⊤, ∅}=∗
          ⌜w.val = Vunit ∧ ∃ bs',
            ((n = 0 ∧ bs' = bs0) ∨ (0 < n ∧ bs' = (sevenBytes fmapEmpty))) ∧
            ∃ i a, c = cellPtr i a ∧ CellCoh fmapEmpty σ' i ⟨a, intTy, bs'⟩⌝) :=
  -- the projection's Iris half over the pure-consequence lemmas
  -- (Adequacy.lean): pure ∗ (pure ∗ ↦ ∨ pure ∗ ↦), then the pure reshaping
  stateInterp_readout fun _ _ _ _ hG =>
    (sep_consequence (pure_consequence _) (or_consequence
      (sep_consequence (pure_consequence _)
        (pointsToCell_consequence hG fmapEmpty c (.own 1) intTy bs0))
      (sep_consequence (pure_consequence _)
        (pointsToCell_consequence hG fmapEmpty c (.own 1) intTy
          (sevenBytes fmapEmpty))))).trans
    (BI.pure_mono fun ⟨hval, h⟩ => ⟨hval, h.elim
      (fun ⟨hn0, hc⟩ => ⟨bs0, .inl ⟨hn0, rfl⟩, hc⟩)
      (fun ⟨hpos, hc⟩ => ⟨sevenBytes fmapEmpty, .inr ⟨hpos, rfl⟩, hc⟩)⟩)

/-- The base-WP face with the engine readout (what `engine_adequacyU`
    consumes), from any reachable entry frame over any tail. -/
theorem loop_wp_readout (hn : 0 ≤ n) (sbty : core_base_type)
    (f : Fmap sym value) (hf : SymFrame f) (rest : List (Fmap sym value)) :
    pointsToCell (procCtx rs).tagDefs (GF := GF) c (.own 1) intTy bs0 ⊢
      WP (⟨loopProg loc ann ra mo bty xbty sbty c n, f :: rest,
          procCtl p, procCtx rs⟩ : CoreRt) @ Stuckness.NotStuck; ⊤
        {{ w, iprop(∀ (σ' : Mem) (ns : Nat) (κs : List Empty) (nt : Nat),
          stateInterp σ' ns κs nt ={⊤, ∅}=∗
            ⌜w.val = Vunit ∧ ∃ bs',
              ((n = 0 ∧ bs' = bs0) ∨ (0 < n ∧ bs' = (sevenBytes (procCtx rs).tagDefs))) ∧
              ∃ i a, c = cellPtr i a ∧ CellCoh (procCtx rs).tagDefs σ' i ⟨a, intTy, bs'⟩⌝) }} := by
  refine ((loop_wps loc ann ra mo bty xbty c n bs0 p rs hQ hn sbty f hf rest).trans ?_)
  refine (BI.emp_sep.2.trans (BI.sep_mono
    ((loop_blockSpecs loc ann ra mo bty xbty c n bs0 p rs hQ).trans
      (wps_sound (ctl := procCtl p) rfl (loopProg loc ann ra mo bty xbty sbty c n) (f :: rest)))
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
theorem loopBody_fragJ :
    Frag (loopBody loc ann ra mo bty c) := by
  refine .if_ (PePure.of_isPePure rfl) (by decide +kernel)
    (.sseq (.store) (.run (PePure.all_of_isPePure rfl) ?_))
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
    `0 < n`. Partial correctness at EVERY drive length (the engine's
    static get_ctx budget is discharged inside the proof). -/
theorem counter_loop_certified
    (sbty : core_base_type) (idx addr : Int) (bs0 : List CerbMem.AbsByte)
    (n : Int) (hn : 0 ≤ n)
    (σ₀ : Mem)
    (hcoh : Coh fmapEmpty σ₀ ((Iris.Std.PartialMap.singleton idx
      (SpikeCell.mk addr intTy bs0)) : SpikeHeapF SpikeCell))
    (nsteps : Nat) (aids : Nat → Nat) :
    let prog := loopProg loc ann ra mo bty xbty sbty (cellPtr idx addr) n
    let rs := loopRS loc ann ra mo bty xbty (cellPtr idx addr)
    (∀ r, driveU (procCtx rs) aids nsteps
      (procThread loopProcSym prog [fmapEmpty]) σ₀ ≠ .killed r) ∧
    (driveU (procCtx rs) aids nsteps
      (procThread loopProcSym prog [fmapEmpty]) σ₀ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem),
      driveU (procCtx rs) aids nsteps
        (procThread loopProcSym prog [fmapEmpty]) σ₀ = .done v σ' →
      v = Vunit ∧ ∃ bs',
        ((n = 0 ∧ bs' = bs0) ∨ (0 < n ∧ bs' = (sevenBytes fmapEmpty))) ∧
        CellCoh fmapEmpty σ' idx ⟨addr, intTy, bs'⟩) := by
  intro prog rs
  have hlbl : (procCtx rs).labelsAt (procCtl loopProcSym).proc = _ :=
    procCtx_labels (loopRS_labeledAt loc ann ra mo bty xbty (cellPtr idx addr))
  obtain ⟨h1, h2, h3⟩ := engine_adequacyU (GF := SpikeGF)
    (M := procCtx rs) (procCtx_wf _) (ctl := procCtl loopProcSym) rfl
    (fun l params cont hl => by
      rw [hlbl] at hl
      obtain ⟨-, rfl⟩ := loopQ_inv loc ann ra mo bty xbty _ hl
      exact loopBody_fragJ loc ann ra mo bty _)
    (fun l params cont hl => by
      rw [hlbl] at hl
      obtain ⟨-, rfl⟩ := loopQ_inv loc ann ra mo bty xbty _ hl
      exact Nat.le_trans (loopBody_fragJ loc ann ra mo bty _).pot_le_two
        (by rw [show esize (loopBody loc ann ra mo bty (cellPtr idx addr)) = 3 from rfl,
          show lemDefaultFuel = 999999 + 1 from rfl]; omega))
    prog fmapEmpty [] σ₀ _
    (.save (saveParams_pure_of_vals rfl) (saveParams_depth_of_vals rfl) (loopBody_fragJ loc ann ra mo bty _))
    (Nat.le_trans (Frag.pot_le_two (e := prog) (.save (saveParams_pure_of_vals rfl) (saveParams_depth_of_vals rfl)
        (loopBody_fragJ loc ann ra mo bty _)))
      (by rw [show esize prog = 4 from rfl, show lemDefaultFuel = 999999 + 1 from rfl]; omega))
    hcoh
    (fun v σ' => v = Vunit ∧ ∃ bs',
      ((n = 0 ∧ bs' = bs0) ∨ (0 < n ∧ bs' = (sevenBytes fmapEmpty))) ∧
      ∃ i a, cellPtr idx addr = cellPtr i a ∧ CellCoh fmapEmpty σ' i ⟨a, intTy, bs'⟩)
    (by
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
      · iexact Hpt)
    nsteps aids
  refine ⟨h1, h2, fun v σ' hd => ?_⟩
  obtain ⟨hv, bs', hbs, i, a, heq, hc⟩ := h3 v σ' hd
  obtain ⟨rfl, rfl⟩ := cellPtr_inj heq
  exact ⟨hv, bs', hbs, hc⟩

/-- THE IRRELEVANT-BINDING TEST AT THE ENGINE (R-08): the same
    conclusion when the proc-carrying thread is launched with an entry
    frame carrying an unrelated binding `y ↦ junk` — the engine's own
    `update_env`/`lookup_env` on a frame that no exact-shape pin could
    describe. -/
theorem counter_loop_certified_irrelevant_binding
    (sbty : core_base_type) (idx addr : Int) (bs0 : List CerbMem.AbsByte)
    (n : Int) (hn : 0 ≤ n) (junk : value)
    (σ₀ : Mem)
    (hcoh : Coh fmapEmpty σ₀ ((Iris.Std.PartialMap.singleton idx
      (SpikeCell.mk addr intTy bs0)) : SpikeHeapF SpikeCell))
    (nsteps : Nat) (aids : Nat → Nat) :
    let prog := loopProg loc ann ra mo bty xbty sbty (cellPtr idx addr) n
    let rs := loopRS loc ann ra mo bty xbty (cellPtr idx addr)
    let ρ₀ : EnvStack := [envAdd ySym junk fmapEmpty]
    (∀ r, driveU (procCtx rs) aids nsteps
      (procThread loopProcSym prog ρ₀) σ₀ ≠ .killed r) ∧
    (driveU (procCtx rs) aids nsteps
      (procThread loopProcSym prog ρ₀) σ₀ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem),
      driveU (procCtx rs) aids nsteps
        (procThread loopProcSym prog ρ₀) σ₀ = .done v σ' →
      v = Vunit ∧ ∃ bs',
        ((n = 0 ∧ bs' = bs0) ∨ (0 < n ∧ bs' = (sevenBytes fmapEmpty))) ∧
        CellCoh fmapEmpty σ' idx ⟨addr, intTy, bs'⟩) := by
  intro prog rs ρ₀
  have hlbl : (procCtx rs).labelsAt (procCtl loopProcSym).proc = _ :=
    procCtx_labels (loopRS_labeledAt loc ann ra mo bty xbty (cellPtr idx addr))
  obtain ⟨h1, h2, h3⟩ := engine_adequacyU (GF := SpikeGF)
    (M := procCtx rs) (procCtx_wf _) (ctl := procCtl loopProcSym) rfl
    (fun l params cont hl => by
      rw [hlbl] at hl
      obtain ⟨-, rfl⟩ := loopQ_inv loc ann ra mo bty xbty _ hl
      exact loopBody_fragJ loc ann ra mo bty _)
    (fun l params cont hl => by
      rw [hlbl] at hl
      obtain ⟨-, rfl⟩ := loopQ_inv loc ann ra mo bty xbty _ hl
      exact Nat.le_trans (loopBody_fragJ loc ann ra mo bty _).pot_le_two
        (by rw [show esize (loopBody loc ann ra mo bty (cellPtr idx addr)) = 3 from rfl,
          show lemDefaultFuel = 999999 + 1 from rfl]; omega))
    prog (envAdd ySym junk fmapEmpty) [] σ₀ _
    (.save (saveParams_pure_of_vals rfl) (saveParams_depth_of_vals rfl) (loopBody_fragJ loc ann ra mo bty _))
    (Nat.le_trans (Frag.pot_le_two (e := prog) (.save (saveParams_pure_of_vals rfl) (saveParams_depth_of_vals rfl)
        (loopBody_fragJ loc ann ra mo bty _)))
      (by rw [show esize prog = 4 from rfl, show lemDefaultFuel = 999999 + 1 from rfl]; omega))
    hcoh
    (fun v σ' => v = Vunit ∧ ∃ bs',
      ((n = 0 ∧ bs' = bs0) ∨ (0 < n ∧ bs' = (sevenBytes fmapEmpty))) ∧
      ∃ i a, cellPtr idx addr = cellPtr i a ∧ CellCoh fmapEmpty σ' i ⟨a, intTy, bs'⟩)
    (by
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
      · iexact Hpt)
    nsteps aids
  refine ⟨h1, h2, fun v σ' hd => ?_⟩
  obtain ⟨hv, bs', hbs, i, a, heq, hc⟩ := h3 v σ' hd
  obtain ⟨rfl, rfl⟩ := cellPtr_inj heq
  exact ⟨hv, bs', hbs, hc⟩

end LoopDrive

end CerberusHeapLang
