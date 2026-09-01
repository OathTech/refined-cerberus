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

THE ENV-FRAME SEAM (recorded finding): the engine env frames are
LemLib `Fmap`s (TreeMap-backed); add/lookup at a CONCRETE key on
CONCRETELY-STRUCTURED frames reduces definitionally, and this
exhibit's per-label invariant PINS the frame structure (`IsXFrame` —
the env-indexed `LabelSpec`'s purpose). Generic map lawfulness
(lookup-after-add on arbitrary frames) is deliberately NOT assumed
here; EnvLaws.lean proves it, and the later exhibits (fib onward)
use it instead of frame-shape pins.
-/
import CerberusHeapLang.Adequacy
import CerberusHeapLang.Wps
import CerberusHeapLang.EnvLaws

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Map

/-! ## The program -/

def loopSym : sym := Symbol "" 101 SD_None
def xSym : sym := Symbol "" 102 SD_None
def loopProcSym : sym := Symbol "" 103 SD_None

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

/-! ## The env frames (the concrete-structure invariant) -/

/-- The exhibit's head-frame shape: a one-node tree at `xSym`
    holding `v` (sequence/counter bookkeeping quantified). Every
    reachable frame of the loop has this shape — the env-indexed
    label invariant pins it, which is what makes all evaluator
    lookups definitional. -/
def IsXFrame (m : Fmap sym value) (v : value) : Prop :=
  ∃ (sq ctr : Nat) (bySeq : Std.TreeMap Nat (sym × value)),
    m = Fmap.mk (lemCmpToOrd symCmpK)
      ((Std.TreeMap.empty (cmp := lemCmpToOrd symCmpK)).insert xSym
        [(sq, xSym, v)])
      bySeq ctr

theorem isXFrame_add_empty (v : value) :
    IsXFrame (envAdd xSym v fmapEmpty) v :=
  ⟨0, 1, _, rfl⟩

theorem isXFrame_lookup {m : Fmap sym value} {v : value}
    (h : IsXFrame m v) : fmapLookupBy symCmpK xSym m = some v := by
  obtain ⟨sq, ctr, bySeq, rfl⟩ := h
  unfold fmapLookupBy
  dsimp only
  rw [treeMap_get?_insert_empty]
  rw [if_pos (by decide +kernel : lemCmpToOrd symCmpK xSym xSym = .eq)]

theorem isXFrame_add {m : Fmap sym value} {w : value}
    (h : IsXFrame m w) (v : value) :
    IsXFrame (envAdd xSym v m) v := by
  obtain ⟨sq, ctr, bySeq, rfl⟩ := h
  exact ⟨ctr, ctr + 1, _, rfl⟩

/-! ## Evaluation facts at pinned frames -/

theorem lookup_env_xframe {f : Fmap sym value} {v : value}
    (h : IsXFrame f v) (rest : List (Fmap sym value)) :
    lookup_env (a := value) xSym (f :: rest) = some v := by
  unfold lookup_env
  rw [show (fmapLookupBy (@mapKeyCompare sym _) xSym f) =
    fmapLookupBy symCmpK xSym f from rfl, isXFrame_lookup h]

theorem guard_eval {f : Fmap sym value} {i : Int}
    (h : IsXFrame f (ivVal i)) (rest : List (Fmap sym value)) :
    evalPexpr fmapEmpty (f :: rest) guardPe = some (boolValue (decide (0 < i))) := by
  unfold guardPe
  rw [evalPexpr_op]
  rw [show evalPexpr fmapEmpty (f :: rest) (Pexpr [] () (PEsym xSym)) =
    some (ivVal i) from by
      rw [evalPexpr_sym_empty]; exact lookup_env_xframe h rest]
  show evalBinop binop.OpGt (ivVal i) (ivVal 0) = _
  unfold evalBinop ivVal
  show (CerbMem.ltIval (CerbMem.integerIval 0)
    (CerbMem.integerIval i)).map boolValue = _
  rfl

theorem dec_eval {f : Fmap sym value} {i : Int}
    (h : IsXFrame f (ivVal i)) (rest : List (Fmap sym value)) :
    evalPexprs fmapEmpty (f :: rest) [decPe] = some [ivVal (i - 1)] := by
  rw [evalPexprs_cons]
  rw [show evalPexpr fmapEmpty (f :: rest) decPe = some (ivVal (i - 1)) from by
    unfold decPe
    rw [evalPexpr_op]
    rw [show evalPexpr fmapEmpty (f :: rest) (Pexpr [] () (PEsym xSym)) =
      some (ivVal i) from by
        rw [evalPexpr_sym_empty]; exact lookup_env_xframe h rest]
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

/-- Frames on which one more counter-bind lands in the pinned shape
    (every reachable base frame of the loop). -/
def XReady (f : Fmap sym value) : Prop :=
  ∀ v', IsXFrame (envAdd xSym v' f) v'

theorem xready_empty : XReady fmapEmpty := fun v' => isXFrame_add_empty v'

theorem xready_step {f : Fmap sym value} {v : value}
    (h : XReady f) : XReady (envAdd xSym v f) :=
  fun v' => isXFrame_add (h v) v'

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
    ((⌜n = 0⌝ ∗ pointsToCell c (.own 1) intTy bs0) ∨
     (⌜0 < n⌝ ∗ pointsToCell c (.own 1) intTy sevenBytes)))

/-- THE PER-LABEL INVARIANT (env-indexed — it pins the reachable
    frame shape, which is what makes the evaluator facts
    definitional): the argument is the counter `i ∈ [0, n]`; the
    env is a pinned frame over any tail; the cell is the entry bytes
    before the first iteration and the stored image after. -/
abbrev loopLs : LabelSpec GF := fun _ vs ρ =>
  (iprop(∃ (i : Int) (f : Fmap sym value) (rest : List (Fmap sym value)),
    ⌜vs = [ivVal i] ∧ 0 ≤ i ∧ i ≤ n ∧ ρ = f :: rest ∧ XReady f⌝ ∗
    ((⌜i = n⌝ ∗ pointsToCell c (.own 1) intTy bs0) ∨
     (⌜i < n⌝ ∗ pointsToCell c (.own 1) intTy sevenBytes))) : IProp GF)

include hQ

/-- The loop body verifies at any pinned counter frame (the shared
    lemma behind both the block spec and the entry). -/
theorem loop_body_wps (i : Int) (f : Fmap sym value)
    (rest : List (Fmap sym value)) (hxr : XReady f)
    (h0 : 0 ≤ i) (hin : i ≤ n) :
    iprop(((⌜i = n⌝ ∗ pointsToCell (GF := GF) c (.own 1) intTy bs0) ∨
      (⌜i < n⌝ ∗ pointsToCell c (.own 1) intTy sevenBytes))) ⊢
      wps (procCtx p rs) (loopLs c n bs0)
        (loopPost c n bs0) (loopBody loc ann ra mo bty c)
        (envAdd xSym (ivVal i) f :: rest) := by
  have hf' : IsXFrame (envAdd xSym (ivVal i) f) (ivVal i) := hxr (ivVal i)
  rw [show (loopBody loc ann ra mo bty c) =
    Expr [] (Eif guardPe
      (sseqExpr bty (storeExpr loc ann intTy c sevenVal mo)
        (Expr [] (Erun ra loopSym [decPe])))
      (ofVal (.pure Vunit))) from rfl]
  by_cases hpos : 0 < i
  · -- guard TRUE: store then jump at i - 1
    iintro Hcell
    iapply wps_if_true [] guardPe _ _ _
      (by rw [procCtx_extern, guard_eval hf' rest, decide_eq_true hpos]; rfl)
    rw [show (sseqExpr bty (storeExpr loc ann intTy c sevenVal mo)
        (Expr [] (Erun ra loopSym [decPe]))) =
      Expr [] (Esseq (Pattern [] (CaseBase (none, bty)))
        (storeExpr loc ann intTy c sevenVal mo)
        (Expr [] (Erun ra loopSym [decPe]))) from rfl]
    iapply wps_seq
    -- the cell is owned either way; store the image
    icases Hcell with (⟨%hieq, Hc⟩ | ⟨%hlt, Hc⟩) <;>
      (iapply wps_store loc ann intTy c sevenVal mo sevenMval _ _
        seven_encodes seven_storable
       isplitl [Hc]
       · iexact Hc
       iintro %fp Hc
       iapply wps_run [] ra loopSym [decPe] _ _
         (by rw [procCtx_labels hQ]
             exact loopQ_lookup loc ann ra mo bty xbty c)
         (dec_eval hf' rest)
       iexists (i - 1), (envAdd xSym (ivVal i) f), rest
       isplit
       · ipureintro
         exact ⟨rfl, by omega, by omega, rfl, xready_step hxr⟩
       iright
       isplit
       · ipureintro; omega
       rw [show sevenBytes = (CerbMem.memValueToBytes [] sevenMval).2 from rfl]
       iexact Hc)
  · -- guard FALSE: exit with the final cell state
    have hz : i = 0 := by omega
    subst hz
    iintro Hcell
    iapply wps_if_false [] guardPe _ _ _
      (by rw [procCtx_extern, guard_eval hf' rest,
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
  obtain ⟨rfl, h0, hin, hρ, hxr⟩ := hpure
  obtain ⟨rfl, rfl⟩ : f = ev0 ∧ rest = evs := by
    have h1 := congrArg (fun l => l.head?) hρ
    have h2 := congrArg (fun l => l.tail) hρ
    simp at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  rw [bindArgs_x]
  iapply loop_body_wps loc ann ra mo bty xbty c n bs0 p rs hQ i f rest hxr
    h0 hin $$ Hcell

/-- The whole program's statement WP from the entry env. -/
theorem loop_wps (hn : 0 ≤ n) (sbty : core_base_type) :
    pointsToCell (GF := GF) c (.own 1) intTy bs0 ⊢
      wps (procCtx p rs) (loopLs c n bs0)
        (loopPost c n bs0)
        (loopProg loc ann ra mo bty xbty sbty c n) [fmapEmpty] := by
  iintro Hc
  rw [show (loopProg loc ann ra mo bty xbty sbty c n) =
    Expr [] (Esave (loopSym, sbty)
      [(xSym, ((xbty, (none : Option (ctype × pass_by_value_or_pointer))),
        Pexpr [] () (PEval (ivVal n))))]
      (loopBody loc ann ra mo bty c)) from rfl]
  iapply wps_save [] (loopSym, sbty) _ _ fmapEmpty []
    (cvals := [ivVal n]) rfl
  rw [bindSave_x]
  iapply loop_body_wps loc ann ra mo bty xbty c n bs0 p rs hQ n fmapEmpty []
    xready_empty hn (by omega)
  ileft
  isplit
  · ipureintro; rfl
  · iexact Hc

omit hQ in
/-- Single-cell readout (the `cells_readout` shape at one cell):
    ownership at the end pins the final MemState's cell. -/
theorem cell_readout (pv : CerbMem.PointerValue) (ty : ctype)
    (bs : List CerbMem.AbsByte) :
    pointsToCell (GF := GF) pv (.own 1) ty bs ⊢
      iprop(∀ (σ' : Mem) (ns : Nat) (κs : List Empty) (nt : Nat),
        stateInterp σ' ns κs nt ={⊤, ∅}=∗
          ⌜∃ i a, pv = cellPtr i a ∧ CellCoh σ' i ⟨a, ty, bs⟩⌝) := by
  -- Phase-4 tidy: the state-interpretation open/close lives in the
  -- core combinator (stateInterp_readout); this module supplies only
  -- the coupling-conditional extraction (cellOwn_cellCoh).
  exact stateInterp_readout (fun σ' mm mb mk HG => by
    iintro ⟨Hpt, Hmi, Hbi⟩
    icases (pointsToCell_cellOwn_iff pv (.own 1) ty bs).mp $$ Hpt with
      ⟨%i, %a, %Hpv, Hcell⟩
    ihave %Hcc : ⌜CellCoh σ' i ⟨a, ty, bs⟩ ∧ Iris.Std.PartialMap.get? mm i =
        some (metaOf (⟨a, ty, bs⟩ : SpikeCell))⌝ $$ [Hmi Hbi Hcell]
    · iapply cellOwn_cellCoh HG i (.own 1) ⟨a, ty, bs⟩ $$ [$Hmi $Hbi $Hcell]
    ipureintro
    exact ⟨i, a, Hpv, Hcc.1⟩)

omit hQ in
/-- The per-value readout of the loop postcondition. -/
theorem loop_readout_val (w : CoreRVal) :
    loopPost (GF := GF) c n bs0 w.w w.ρ ⊢
      iprop(∀ (σ' : Mem) (ns : Nat) (κs : List Empty) (nt : Nat),
        stateInterp σ' ns κs nt ={⊤, ∅}=∗
          ⌜w.val = Vunit ∧ ∃ bs',
            ((n = 0 ∧ bs' = bs0) ∨ (0 < n ∧ bs' = sevenBytes)) ∧
            ∃ i a, c = cellPtr i a ∧ CellCoh σ' i ⟨a, intTy, bs'⟩⌝) := by
  rw [show (loopPost (GF := GF) c n bs0 w.w w.ρ) =
    (iprop(⌜SpikeVal.val w.w = Vunit⌝ ∗
      ((⌜n = 0⌝ ∗ pointsToCell c (.own 1) intTy bs0) ∨
       (⌜0 < n⌝ ∗ pointsToCell c (.own 1) intTy sevenBytes))) : IProp GF)
    from rfl]
  iintro ⟨%hval, Hd⟩
  icases Hd with (⟨%hn0, Hcell⟩ | ⟨%hpos, Hcell⟩)
  · ihave Hro := cell_readout c intTy bs0 $$ Hcell
    iintro %σ' %ns %κs %nt Hσ
    imod Hro $$ %σ' %ns %κs %nt Hσ with %hfact
    imodintro
    ipureintro
    exact ⟨hval, bs0, .inl ⟨hn0, rfl⟩, hfact⟩
  · ihave Hro := cell_readout c intTy sevenBytes $$ Hcell
    iintro %σ' %ns %κs %nt Hσ
    imod Hro $$ %σ' %ns %κs %nt Hσ with %hfact
    imodintro
    ipureintro
    exact ⟨hval, sevenBytes, .inr ⟨hpos, rfl⟩, hfact⟩

/-- The base-WP face with the engine readout (what `engine_adequacyJ`
    consumes). -/
theorem loop_wp_readout (hn : 0 ≤ n) (sbty : core_base_type) :
    pointsToCell (GF := GF) c (.own 1) intTy bs0 ⊢
      WP (⟨loopProg loc ann ra mo bty xbty sbty c n, [fmapEmpty],
          procCtx p rs⟩ : CoreRt) @ Stuckness.NotStuck; ⊤
        {{ w, iprop(∀ (σ' : Mem) (ns : Nat) (κs : List Empty) (nt : Nat),
          stateInterp σ' ns κs nt ={⊤, ∅}=∗
            ⌜w.val = Vunit ∧ ∃ bs',
              ((n = 0 ∧ bs' = bs0) ∨ (0 < n ∧ bs' = sevenBytes)) ∧
              ∃ i a, c = cellPtr i a ∧ CellCoh σ' i ⟨a, intTy, bs'⟩⌝) }} := by
  refine ((loop_wps loc ann ra mo bty xbty c n bs0 p rs hQ hn sbty).trans ?_)
  refine (BI.emp_sep.2.trans (BI.sep_mono
    ((loop_blockSpecs loc ann ra mo bty xbty c n bs0 p rs hQ).trans
      (wps_sound (loopProg loc ann ra mo bty xbty sbty c n) [fmapEmpty]))
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
theorem counter_loop_certified {GF : BundledGFunctors} [SpikeGpreS GF]
    (sbty : core_base_type) (idx addr : Int) (bs0 : List CerbMem.AbsByte)
    (n : Int) (hn : 0 ≤ n)
    (hlib : CerbLocation.isLibraryLocation loc = false)
    (σ₀ : Mem)
    (hcoh : Coh σ₀ ((Iris.Std.PartialMap.singleton idx
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
        ((n = 0 ∧ bs' = bs0) ∨ (0 < n ∧ bs' = sevenBytes)) ∧
        ∃ i a, cellPtr idx addr = cellPtr i a ∧
          CellCoh σ' i ⟨a, intTy, bs'⟩) := by
  intro prog rs
  refine engine_adequacyJ (GF := GF)
    (loopRS_labeledAt loc ann ra mo bty xbty (cellPtr idx addr))
    (fun l params cont hl => by
      obtain ⟨-, rfl⟩ := loopQ_inv loc ann ra mo bty xbty _ hl
      exact loopBody_fragJ loc ann ra mo bty _ hlib)
    prog fmapEmpty [] σ₀ _
    (.save (loopBody_fragJ loc ann ra mo bty _ hlib)) hcoh
    (fun v σ' => v = Vunit ∧ ∃ bs',
      ((n = 0 ∧ bs' = bs0) ∨ (0 < n ∧ bs' = sevenBytes)) ∧
      ∃ i a, cellPtr idx addr = cellPtr i a ∧ CellCoh σ' i ⟨a, intTy, bs'⟩)
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
    (loopRS_labeledAt loc ann ra mo bty xbty (cellPtr idx addr)) hn sbty)
  refine (BigSepM.bigSepM_singleton).1.trans ?_
  iintro Hpt
  iapply (pointsToCell_cellOwn_iff _ _ _ _).mpr
  iexists idx, addr
  isplit
  · ipureintro; rfl
  · iexact Hpt

end LoopDrive

end CerberusHeapLang
