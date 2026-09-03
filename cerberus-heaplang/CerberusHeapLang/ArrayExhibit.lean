/-
CerberusHeapLang.ArrayExhibit — the ARRAY-SUM walk end-to-end: real
pointer arithmetic through the engine's memory model.

THE PROGRAM (authored Core; metadata quantified):

    save loop: (i := 0, acc := 0, p := base) in
      if (i < n) then
        lets Specified(x) = load(int, p) in
          run loop(i + 1, acc + x, array_shift(p, int, 1))
      else pure(acc)

- REAL POINTER ARITHMETIC: the loop-carried pointer advances by
  `array_shift` through the certified evaluator's PEarray_shift arm
  (the engine's own `arrayShiftPtrval`).
- The load's pointer operand is a SYMBOL: the operand-evaluation rule
  (`wps_load_eval`) takes the engine's ACTION_EVAL step into the
  canonical load redex; the typed sub-range rule `wps_load_cell_at`
  then reads the element slice of the array cell.
- The loaded `Specified` value is unwrapped by the Specified-binder
  sequencing rule (`wps_seq_spec` — Core's own binding-pattern
  mechanism), so `acc + x` is plain integer arithmetic.
- THE INVARIANT is index-partitioned over the VALUE list:
  `acc = (vs.take i).sum ∧ p = base + i·|int|`, carrying the array
  cell's ownership; the conclusion is `⌜result = vs.sum⌝` WITH THE
  ARRAY PRESERVED (the final memory still carries the seeded bytes).

REGISTERED DIVERGENCE from the textbook `∗_{i<n} base+i·|int| ↦ vs[i]`
pre-state phrasing — a forcing fact about Cerberus: in this ghost
model a cell IS an allocation (`CellCoh` ties the ghost key to the
allocation id), and the concrete memory model's loads resolve the
pointer's PROVENANCE allocation and bounds-check against it (loadM,
generated/CerbMem.lean:1586-1631), while `arrayShiftPtrval` PRESERVES
provenance (CerbMem.lean:1127-1142) — so a pointer walked by real
arithmetic can never legally cross into a sibling allocation: an
n-allocation "array" is not walkable, in the ENGINE, by construction
(exactly C's object model). The array is therefore ONE allocation —
one ghost cell holding the concatenated element images — and the
per-element structure lives in the index-partitioned invariant and
the per-element decode premises (`hdec`). The heap-side footprint is
still delivered through the big-sep machinery ([∗map] over the seeded
cell map).
-/
import CerberusHeapLang.API
import CerberusHeapLang.Examples.Layout
import CerberusHeapLang.FibExhibit

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Map

/-! ## Facts about the int layout and pointer arithmetic -/

theorem intTy_size {tds : CerbTags.TagDefsMap} : CerbMem.sizeofCtype tds intTy = 4 := rfl

/-- One int-element shift of a fragment pointer — the ENGINE's own
    arithmetic (`arrayShiftPtrval` at concrete provenance/address
    shape: provenance PRESERVED, address advanced by |int|). -/
theorem arrayShift_cellPtr {tds : CerbTags.TagDefsMap} (id p : Int) :
    CerbMem.arrayShiftPtrval tds (cellPtr id p) intTy (CerbMem.integerIval 1) =
      cellPtr id (p + 4) := by
  rw [cellPtr_arrayShift tds id p intTy 1 (fun _ h => by unfold intTy at h; cases h),
    intTy_size]
  exact congrArg (cellPtr id) (by omega)

/-- The mirror evaluator's shift at the concrete shapes. -/
theorem evalArrayShift_ptr_one (id a : Int) :
    evalArrayShift fmapEmpty intTy (Vobject (OVpointer (cellPtr id a))) (ivVal 1) =
      some (Vobject (OVpointer (cellPtr id (a + 4)))) := by
  show some (Vobject (OVpointer (CerbMem.arrayShiftPtrval fmapEmpty (cellPtr id a)
    intTy (CerbMem.integerIval 1)))) = _
  rw [arrayShift_cellPtr]

/-- The delivered value of an integer mem-value. -/
theorem valueFromMemValue_int (ety : integerType) (iv : CerbMem.IntegerValue) :
    (valueFromMemValue (CerbMem.MemValue.MVinteger ety iv)).2 =
      Vloaded (LVspecified (OVinteger iv)) := rfl

/-- Partial-sum step. -/
theorem take_sum_succ (vs : List Int) (i : Nat) (h : i < vs.length) :
    (vs.take (i + 1)).sum = (vs.take i).sum + vs[i] := by
  rw [List.take_add_one]
  rw [List.getElem?_eq_getElem h]
  rw [List.sum_append]
  simp

/-! ## The program -/

def arrISym : sym := Symbol "" 301 SD_None
def arrAccSym : sym := Symbol "" 302 SD_None
def arrPSym : sym := Symbol "" 303 SD_None
def arrXSym : sym := Symbol "" 304 SD_None
def arrLoopSym : sym := Symbol "" 305 SD_None
def arrProcSym : sym := Symbol "" 306 SD_None

/-- The guard `i < n`. -/
def arrGuard (n : Int) : generic_pexpr Unit sym :=
  Pexpr [] () (PEop binop.OpLt (Pexpr [] () (PEsym arrISym))
    (Pexpr [] () (PEval (ivVal n))))

/-- Back-edge argument `i + 1`. -/
def arrIncPe : generic_pexpr Unit sym :=
  Pexpr [] () (PEop binop.OpAdd (Pexpr [] () (PEsym arrISym))
    (Pexpr [] () (PEval (ivVal 1))))

/-- Back-edge argument `acc + x`. -/
def arrAccXPe : generic_pexpr Unit sym :=
  Pexpr [] () (PEop binop.OpAdd (Pexpr [] () (PEsym arrAccSym))
    (Pexpr [] () (PEsym arrXSym)))

/-- Back-edge argument `array_shift(p, int, 1)` — REAL pointer
    arithmetic. -/
def arrShiftPe : generic_pexpr Unit sym :=
  Pexpr [] () (PEarray_shift (Pexpr [] () (PEsym arrPSym)) intTy
    (Pexpr [] () (PEval (ivVal 1))))

/-- The exit expression `pure(acc)`. -/
def arrExitPe : generic_pexpr Unit sym := Pexpr [] () (PEsym arrAccSym)

/-- The load `load(int, p)` — the pointer operand is a SYMBOL (the
    ACTION_EVAL shape). -/
def arrLoadE (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (mo : memory_order) : CoreExpr :=
  loadOpRedex loc ann intTy (Pexpr [] () (PEsym arrPSym)) mo

/-- The registered loop body. -/
def arrBody (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (mo : memory_order) (xbty : core_base_type) (n : Int) : CoreExpr :=
  Expr [] (Eif (arrGuard n)
    (Expr [] (Esseq (specPat [] [] arrXSym xbty)
      (arrLoadE loc ann mo)
      (Expr [] (Erun ra arrLoopSym [arrIncPe, arrAccXPe, arrShiftPe]))))
    (Expr [] (Epure arrExitPe)))

/-- The save-parameter list (`i := 0, acc := 0, p := base`). -/
def arrParams (ibty accbty pbty : core_base_type) (base : CerbMem.PointerValue) :
    List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)) :=
  [(arrISym, ((ibty, none), Pexpr [] () (PEval (ivVal 0)))),
   (arrAccSym, ((accbty, none), Pexpr [] () (PEval (ivVal 0)))),
   (arrPSym, ((pbty, none), Pexpr [] () (PEval (Vobject (OVpointer base)))))]

/-- The whole program. -/
def arrProg (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (mo : memory_order) (sbty ibty accbty pbty xbty : core_base_type)
    (base : CerbMem.PointerValue) (n : Int) : CoreExpr :=
  Expr [] (Esave (arrLoopSym, sbty) (arrParams ibty accbty pbty base)
    (arrBody loc ann ra mo xbty n))

/-- The label map. -/
def arrQ (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (mo : memory_order) (ibty accbty pbty xbty : core_base_type)
    (n : Int) : LabelMap :=
  fmapAddBy symCmpL arrLoopSym
    ([(arrISym, ibty), (arrAccSym, accbty), (arrPSym, pbty)],
      arrBody loc ann ra mo xbty n)
    fmapEmpty

/-- The run state carrying the two-level `labeled` tie. -/
def arrRS (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (mo : memory_order) (ibty accbty pbty xbty : core_base_type)
    (n : Int) : core_run_state :=
  { spikeRunState with
      labeled := fmapAddBy symCmpL arrProcSym
        (arrQ loc ann ra mo ibty accbty pbty xbty n) fmapEmpty }

section ArrFacts

variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (mo : memory_order) (ibty accbty pbty xbty : core_base_type) (n : Int)

theorem arrQ_lookup :
    lookupLabel (arrQ loc ann ra mo ibty accbty pbty xbty n) arrLoopSym =
      some ([(arrISym, ibty), (arrAccSym, accbty), (arrPSym, pbty)],
        arrBody loc ann ra mo xbty n) := by
  unfold lookupLabel arrQ
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

theorem arrQ_inv {l : sym} {params : List (sym × core_base_type)}
    {cont : CoreExpr}
    (h : lookupLabel (arrQ loc ann ra mo ibty accbty pbty xbty n) l =
      some (params, cont)) :
    params = [(arrISym, ibty), (arrAccSym, accbty), (arrPSym, pbty)] ∧
      cont = arrBody loc ann ra mo xbty n := by
  unfold lookupLabel arrQ at h
  rw [fmapLookupBy_addBy_empty] at h
  split at h
  · obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
    exact ⟨h1.symm ▸ rfl, h2.symm ▸ rfl⟩
  · cases h

theorem arrRS_labeledAt :
    LabeledAt (arrRS loc ann ra mo ibty accbty pbty xbty n) arrProcSym
      (arrQ loc ann ra mo ibty accbty pbty xbty n) := by
  unfold LabeledAt arrRS
  show fmapLookupBy _ _ (fmapAddBy symCmpL arrProcSym _ fmapEmpty) = _
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

end ArrFacts

/-! ## The frames (SymFrame + the lookup law — no shape pins) -/

/-- The frame after the jump/save bindings (i, acc, p). -/
def arrFrame (vi vacc vp : value) (f : Fmap sym value) : Fmap sym value :=
  envAdd arrPSym vp (envAdd arrAccSym vacc (envAdd arrISym vi f))

/-- The frame after additionally binding the loaded x. -/
def arrFrameX (vx vi vacc vp : value) (f : Fmap sym value) : Fmap sym value :=
  envAdd arrXSym vx (arrFrame vi vacc vp f)

theorem arrFrame_symFrame {f : Fmap sym value} (hf : SymFrame f)
    (vi vacc vp : value) : SymFrame (arrFrame vi vacc vp f) :=
  ((hf.add _ _).add _ _).add _ _

theorem arrFrameX_symFrame {f : Fmap sym value} (hf : SymFrame f)
    (vx vi vacc vp : value) : SymFrame (arrFrameX vx vi vacc vp f) :=
  (arrFrame_symFrame hf _ _ _).add _ _

section ArrLookups

variable {f : Fmap sym value} (hf : SymFrame f) (vx vi vacc vp : value)

include hf

theorem arrFrame_lookup_i :
    fmapLookupBy symCmpK arrISym (arrFrame vi vacc vp f) = some vi := by
  unfold arrFrame
  rw [envAdd_lookup ((hf.add _ _).add _ _) symCmpK,
    if_neg (by decide +kernel),
    envAdd_lookup (hf.add _ _) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup hf symCmpK, if_pos (by decide +kernel)]

theorem arrFrame_lookup_acc :
    fmapLookupBy symCmpK arrAccSym (arrFrame vi vacc vp f) = some vacc := by
  unfold arrFrame
  rw [envAdd_lookup ((hf.add _ _).add _ _) symCmpK,
    if_neg (by decide +kernel),
    envAdd_lookup (hf.add _ _) symCmpK, if_pos (by decide +kernel)]

theorem arrFrame_lookup_p :
    fmapLookupBy symCmpK arrPSym (arrFrame vi vacc vp f) = some vp := by
  unfold arrFrame
  rw [envAdd_lookup ((hf.add _ _).add _ _) symCmpK,
    if_pos (by decide +kernel)]

theorem arrFrameX_lookup_x :
    fmapLookupBy symCmpK arrXSym (arrFrameX vx vi vacc vp f) = some vx := by
  unfold arrFrameX
  rw [envAdd_lookup (arrFrame_symFrame hf _ _ _) symCmpK,
    if_pos (by decide +kernel)]

theorem arrFrameX_lookup_i :
    fmapLookupBy symCmpK arrISym (arrFrameX vx vi vacc vp f) = some vi := by
  unfold arrFrameX
  rw [envAdd_lookup (arrFrame_symFrame hf _ _ _) symCmpK,
    if_neg (by decide +kernel), arrFrame_lookup_i hf]

theorem arrFrameX_lookup_acc :
    fmapLookupBy symCmpK arrAccSym (arrFrameX vx vi vacc vp f) = some vacc := by
  unfold arrFrameX
  rw [envAdd_lookup (arrFrame_symFrame hf _ _ _) symCmpK,
    if_neg (by decide +kernel), arrFrame_lookup_acc hf]

theorem arrFrameX_lookup_p :
    fmapLookupBy symCmpK arrPSym (arrFrameX vx vi vacc vp f) = some vp := by
  unfold arrFrameX
  rw [envAdd_lookup (arrFrame_symFrame hf _ _ _) symCmpK,
    if_neg (by decide +kernel), arrFrame_lookup_p hf]

end ArrLookups

/-! ## Binding computations -/

theorem bindSave_arr (ibty accbty pbty : core_base_type)
    (base : CerbMem.PointerValue) (f : Fmap sym value)
    (rest : List (Fmap sym value)) :
    bindSaveParams (arrParams ibty accbty pbty base)
        [ivVal 0, ivVal 0, Vobject (OVpointer base)] (f :: rest) =
      arrFrame (ivVal 0) (ivVal 0) (Vobject (OVpointer base)) f :: rest := by
  show update_env (mk_sym_pat arrPSym pbty) (Vobject (OVpointer base))
    (update_env (mk_sym_pat arrAccSym accbty) (ivVal 0)
      (update_env (mk_sym_pat arrISym ibty) (ivVal 0) (f :: rest))) = _
  rw [update_env_cons, update_env_aux_sym, update_env_cons,
    update_env_aux_sym, update_env_cons, update_env_aux_sym]
  rfl

theorem bindArgs_arr (ibty accbty pbty : core_base_type)
    (v1 v2 v3 : value) (f : Fmap sym value)
    (rest : List (Fmap sym value)) :
    bindArgs [(arrISym, ibty), (arrAccSym, accbty), (arrPSym, pbty)]
        [v1, v2, v3] (f :: rest) =
      arrFrame v1 v2 v3 f :: rest := by
  show update_env (mk_sym_pat arrPSym pbty) v3
    (update_env (mk_sym_pat arrAccSym accbty) v2
      (update_env (mk_sym_pat arrISym ibty) v1 (f :: rest))) = _
  rw [update_env_cons, update_env_aux_sym, update_env_cons,
    update_env_aux_sym, update_env_cons, update_env_aux_sym]
  rfl

/-! ## Evaluation facts -/

section ArrEval

variable {f : Fmap sym value} (hf : SymFrame f)
  (i : Nat) (acc : Int) (vp : value) (rest : List (Fmap sym value))

include hf

theorem arr_guard_eval (n : Int) :
    evalPexpr fmapEmpty fmapEmpty (arrFrame (ivVal i) (ivVal acc) vp f :: rest)
        (arrGuard n) = some (boolValue (decide ((i : Int) < n))) := by
  unfold arrGuard
  rw [evalPexpr_op]
  rw [show evalPexpr fmapEmpty fmapEmpty (arrFrame (ivVal i) (ivVal acc) vp f :: rest)
      (Pexpr [] () (PEsym arrISym)) = some (ivVal i) from by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (arrFrame_lookup_i hf _ _ _) rest]
  show evalBinop binop.OpLt (ivVal i) (ivVal n) = _
  rfl

theorem arr_p_eval :
    evalPexpr fmapEmpty fmapEmpty (arrFrame (ivVal i) (ivVal acc) vp f :: rest)
        (Pexpr [] () (PEsym arrPSym)) = some vp := by
  rw [evalPexpr_sym_empty]
  exact lookup_env_head (arrFrame_lookup_p hf _ _ _) rest

theorem arr_args_eval (x : Int) (id a : Int) :
    evalPexprs fmapEmpty fmapEmpty (arrFrameX (ivVal x) (ivVal i) (ivVal acc)
        (Vobject (OVpointer (cellPtr id a))) f :: rest)
        [arrIncPe, arrAccXPe, arrShiftPe] =
      some [ivVal ((i : Int) + 1), ivVal (acc + x),
        Vobject (OVpointer (cellPtr id (a + 4)))] := by
  have hi : evalPexpr fmapEmpty fmapEmpty (arrFrameX (ivVal x) (ivVal i) (ivVal acc)
      (Vobject (OVpointer (cellPtr id a))) f :: rest)
      (Pexpr [] () (PEsym arrISym)) = some (ivVal i) := by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (arrFrameX_lookup_i hf _ _ _ _) rest
  have hacc : evalPexpr fmapEmpty fmapEmpty (arrFrameX (ivVal x) (ivVal i) (ivVal acc)
      (Vobject (OVpointer (cellPtr id a))) f :: rest)
      (Pexpr [] () (PEsym arrAccSym)) = some (ivVal acc) := by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (arrFrameX_lookup_acc hf _ _ _ _) rest
  have hx : evalPexpr fmapEmpty fmapEmpty (arrFrameX (ivVal x) (ivVal i) (ivVal acc)
      (Vobject (OVpointer (cellPtr id a))) f :: rest)
      (Pexpr [] () (PEsym arrXSym)) = some (ivVal x) := by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (arrFrameX_lookup_x hf _ _ _ _) rest
  have hp : evalPexpr fmapEmpty fmapEmpty (arrFrameX (ivVal x) (ivVal i) (ivVal acc)
      (Vobject (OVpointer (cellPtr id a))) f :: rest)
      (Pexpr [] () (PEsym arrPSym)) =
      some (Vobject (OVpointer (cellPtr id a))) := by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (arrFrameX_lookup_p hf _ _ _ _) rest
  rw [evalPexprs_cons]
  rw [show evalPexpr fmapEmpty fmapEmpty (arrFrameX (ivVal x) (ivVal i) (ivVal acc)
      (Vobject (OVpointer (cellPtr id a))) f :: rest) arrIncPe =
      some (ivVal ((i : Int) + 1)) from by
    unfold arrIncPe
    rw [evalPexpr_op, hi]
    rfl]
  rw [evalPexprs_cons]
  rw [show evalPexpr fmapEmpty fmapEmpty (arrFrameX (ivVal x) (ivVal i) (ivVal acc)
      (Vobject (OVpointer (cellPtr id a))) f :: rest) arrAccXPe =
      some (ivVal (acc + x)) from by
    unfold arrAccXPe
    rw [evalPexpr_op, hacc, hx]
    rfl]
  rw [evalPexprs_cons]
  rw [show evalPexpr fmapEmpty fmapEmpty (arrFrameX (ivVal x) (ivVal i) (ivVal acc)
      (Vobject (OVpointer (cellPtr id a))) f :: rest) arrShiftPe =
      some (Vobject (OVpointer (cellPtr id (a + 4)))) from by
    unfold arrShiftPe
    rw [evalPexpr_array_shift, hp]
    show evalArrayShift fmapEmpty intTy (Vobject (OVpointer (cellPtr id a)))
      (ivVal 1) = _
    exact evalArrayShift_ptr_one id a]
  rfl

theorem arr_exit_eval :
    evalPexpr fmapEmpty fmapEmpty (arrFrame (ivVal i) (ivVal acc) vp f :: rest)
        arrExitPe = some (ivVal acc) := by
  show evalPexpr fmapEmpty fmapEmpty _ (Pexpr [] () (PEsym arrAccSym)) = _
  rw [evalPexpr_sym_empty]
  exact lookup_env_head (arrFrame_lookup_acc hf _ _ _) rest

end ArrEval

/-! ## The Iris layer: the index-partitioned invariant -/

section ArrIris

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (mo : memory_order) (ibty accbty pbty xbty : core_base_type)
  (vs : List Int) (id a : Int) (aty : ctype) (bs : List CerbMem.AbsByte)

/-- The postcondition: the delivered value is the list sum AND the
    array cell is preserved. -/
abbrev arrPost : SpikeVal → EnvStack → IProp GF := fun w _ =>
  iprop(⌜w.val = ivVal vs.sum⌝ ∗
    cellOwn fmapEmpty id (.own 1) (SpikeCell.mk a aty bs))

/-- THE INDEX-PARTITIONED INVARIANT: at iteration `i` the
    accumulator is the sum of the first `i` elements and the pointer
    sits at element `i`; the array cell rides through owned and
    untouched. -/
abbrev arrLs : LabelSpec GF := fun _ args ρ =>
  (iprop(∃ (i : Nat) (f : Fmap sym value) (rest : List (Fmap sym value)),
    ⌜args = [ivVal i, ivVal ((vs.take i).sum),
        Vobject (OVpointer (cellPtr id (a + ((4 * i : Nat) : Int))))] ∧
      i ≤ vs.length ∧ ρ = f :: rest ∧ SymFrame f⌝ ∗
    cellOwn fmapEmpty id (.own 1) (SpikeCell.mk a aty bs)) : IProp GF)

variable (p : sym) (rs : core_run_state)
  (hQ : LabeledAt rs p (arrQ loc ann ra mo ibty accbty pbty xbty vs.length))
variable (hsz : vs.length * 4 ≤ CerbMem.sizeofCtype fmapEmpty aty)
  (ety : integerType)
  (hdec : ∀ (i : Nat) (hi : i < vs.length),
    ∀ (lum : List (Int × identifier)) (fpm : CerbMem.Funptrmap),
    CerbMem.reconstructValue fmapEmpty lum fpm (a + ((4 * i : Nat) : Int)) intTy
        ((bs.drop (4 * i)).take (CerbMem.sizeofCtype fmapEmpty intTy)) =
      CerbMem.MemValue.MVinteger ety (CerbMem.integerIval vs[i]))

include hQ hsz hdec

omit hQ hsz hdec in
/-- ARRAY ELEMENT LOAD — the exhibit's layout instance of the GENERIC
    typed-subrange rule (`wps_load_cell_at` at element type `intTy`,
    offset `4 * i`): an ordinary CLIENT lemma, not a logic extension
    (F-04). The trap premise is `rfl` (int is not _Bool); the decode
    premise is the exhibit's per-element seeded-image fact. -/
theorem wps_arr_elem_load {M' : MachineCtx} {p' : Option sym} {Ls' : LabelSpec GF} {Θ' : ProcSpec GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc' : CerbLocation.Loc) (ann' : core_run_annotation)
    (aty' : ctype) (id' a' : Int) (i : Nat) (mo' : memory_order)
    (dq : DFrac) (bs' : List CerbMem.AbsByte) (ρ : EnvStack)
    {mv : CerbMem.MemValue}
    (hbound : 4 * i + CerbMem.sizeofCtype M'.tagDefs intTy ≤ CerbMem.sizeofCtype M'.tagDefs aty')
    (hdec : ∀ lum fpm, CerbMem.reconstructValue M'.tagDefs lum fpm (a' + ((4 * i : Nat) : Int))
      intTy ((bs'.drop (4 * i)).take (CerbMem.sizeofCtype M'.tagDefs intTy)) = mv)
    (htrap : loadTrapV intTy mv = false) :
    iprop(cellOwn M'.tagDefs (GF := GF) id' dq (SpikeCell.mk a' aty' bs') ∗
      (∀ fp, cellOwn M'.tagDefs id' dq (SpikeCell.mk a' aty' bs') -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] ((valueFromMemValue mv).2)) ρ)) ⊢
      wps M' p' Ls' Θ' Ψ (loadExpr loc' ann' intTy
        (cellPtr id' (a' + ((4 * i : Nat) : Int))) mo') ρ :=
  wps_load_cell_at loc' ann' id' a' aty' (4 * i) intTy mo' dq bs' ρ
    hbound hdec htrap

/-- The loop body verifies at any invariant frame. -/
theorem arr_body_wps (i : Nat) (f : Fmap sym value)
    (rest : List (Fmap sym value)) (hf : SymFrame f)
    (hin : i ≤ vs.length) :
    iprop(cellOwn (procCtx rs).tagDefs (GF := GF) id (.own 1) (SpikeCell.mk a aty bs)) ⊢
      wps (procCtx rs) (some p)
        (arrLs vs id a aty bs) emptyProcSpec
        (arrPost vs id a aty bs)
        (arrBody loc ann ra mo xbty vs.length)
        (arrFrame (ivVal i) (ivVal ((vs.take i).sum))
          (Vobject (OVpointer (cellPtr id (a + ((4 * i : Nat) : Int))))) f
          :: rest) := by
  rw [show arrBody loc ann ra mo xbty vs.length = Expr [] (Eif
    (arrGuard vs.length)
    (Expr [] (Esseq (specPat [] [] arrXSym xbty)
      (arrLoadE loc ann mo)
      (Expr [] (Erun ra arrLoopSym [arrIncPe, arrAccXPe, arrShiftPe]))))
    (Expr [] (Epure arrExitPe))) from rfl]
  by_cases hlt : i < vs.length
  · -- load element i, unwrap, jump at i+1
    iintro Hpt
    iapply wps_if_true [] (arrGuard vs.length) _ _ _
      (by rw [procCtx_extern, arr_guard_eval hf i _ _ rest vs.length,
        decide_eq_true (by exact_mod_cast hlt)]; rfl)
    iapply wps_seq_spec [] [] [] arrXSym xbty
    rw [show arrLoadE loc ann mo =
      loadOpRedex loc ann intTy (Pexpr [] () (PEsym arrPSym)) mo from rfl]
    iapply wps_load_eval loc ann intTy (Pexpr [] () (PEsym arrPSym)) mo _
      rfl (arr_p_eval hf i _ _ rest)
    iapply wps_arr_elem_load loc ann aty id a i mo (.own 1) bs _
      (by rw [intTy_size]; show 4 * i + 4 ≤ CerbMem.sizeofCtype fmapEmpty aty; omega)
      (hdec i hlt) rfl
    isplitl [Hpt]
    · iexact Hpt
    iintro %fp Hpt
    iexists (OVinteger (CerbMem.integerIval vs[i]))
    isplit
    · ipureintro
      rw [valueFromMemValue_int]
      rfl
    rw [update_env_spec]
    rw [show envAdd arrXSym (Vobject (OVinteger (CerbMem.integerIval vs[i])))
        (arrFrame (ivVal i) (ivVal ((vs.take i).sum))
          (Vobject (OVpointer (cellPtr id (a + ((4 * i : Nat) : Int))))) f) =
      arrFrameX (ivVal vs[i]) (ivVal i) (ivVal ((vs.take i).sum))
        (Vobject (OVpointer (cellPtr id (a + ((4 * i : Nat) : Int))))) f
      from rfl]
    iapply wps_run [] ra arrLoopSym [arrIncPe, arrAccXPe, arrShiftPe] _ _
      (by rw [procCtx_labels hQ]
          exact arrQ_lookup loc ann ra mo ibty accbty pbty xbty vs.length)
      (arr_args_eval hf i _ rest vs[i] id (a + ((4 * i : Nat) : Int)))
    iexists (i + 1),
      (arrFrameX (ivVal vs[i]) (ivVal i) (ivVal ((vs.take i).sum))
        (Vobject (OVpointer (cellPtr id (a + ((4 * i : Nat) : Int))))) f),
      rest
    isplitr [Hpt]
    · ipureintro
      refine ⟨?_, by omega, rfl, arrFrameX_symFrame hf _ _ _ _⟩
      rw [take_sum_succ vs i hlt]
      rw [show ((i : Int) + 1) = (((i + 1 : Nat)) : Int) by omega]
      rw [show a + ((4 * i : Nat) : Int) + 4 =
        a + ((4 * (i + 1) : Nat) : Int) by omega]
    · iexact Hpt
  · -- exit: i = vs.length, deliver the sum with the array preserved
    have hz : i = vs.length := by omega
    iintro Hpt
    iapply wps_if_false [] (arrGuard vs.length) _ _ _
      (by rw [procCtx_extern, arr_guard_eval hf i _ _ rest vs.length,
        decide_eq_false (by exact_mod_cast hlt)]; rfl)
    iapply wps_pure arrExitPe _ rfl (arr_exit_eval hf i _ _ rest)
    isplit
    · ipureintro
      show ivVal ((vs.take i).sum) = ivVal vs.sum
      rw [hz, List.take_length]
    · iexact Hpt

/-- THE BLOCK SPECIFICATION. -/
theorem arr_blockSpecs :
    ⊢ blockSpecs (GF := GF)
      (procCtx rs) (some p)
      (arrLs vs id a aty bs) emptyProcSpec (arrPost vs id a aty bs) := by
  refine blockSpecs_intro fun l params cont args ev0 evs hl => ?_
  rw [procCtx_labels hQ] at hl
  obtain ⟨rfl, rfl⟩ := arrQ_inv loc ann ra mo ibty accbty pbty xbty
    vs.length hl
  iintro ⟨%i, %f, %rest, %hpure, Hpt⟩
  obtain ⟨rfl, hin, hρ, hf⟩ := hpure
  obtain ⟨rfl, rfl⟩ : f = ev0 ∧ rest = evs := by
    have h1 := congrArg (fun l => l.head?) hρ
    have h2 := congrArg (fun l => l.tail) hρ
    simp at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  rw [bindArgs_arr]
  iapply arr_body_wps loc ann ra mo ibty accbty pbty xbty vs id a aty bs
    p rs hQ hsz ety hdec i f rest hf hin $$ Hpt

/-- The whole program's statement WP from the entry env. -/
theorem arr_wps (sbty : core_base_type) :
    iprop(cellOwn (procCtx rs).tagDefs (GF := GF) id (.own 1) (SpikeCell.mk a aty bs)) ⊢
      wps (procCtx rs) (some p)
        (arrLs vs id a aty bs) emptyProcSpec (arrPost vs id a aty bs)
        (arrProg loc ann ra mo sbty ibty accbty pbty xbty
          (cellPtr id a) vs.length) [fmapEmpty] := by
  rw [show arrProg loc ann ra mo sbty ibty accbty pbty xbty
      (cellPtr id a) vs.length =
    Expr [] (Esave (arrLoopSym, sbty)
      (arrParams ibty accbty pbty (cellPtr id a))
      (arrBody loc ann ra mo xbty vs.length)) from rfl]
  iintro Hpt
  iapply wps_save [] (arrLoopSym, sbty) _ _ fmapEmpty []
    (cvals := [ivVal 0, ivVal 0, Vobject (OVpointer (cellPtr id a))]) rfl
  rw [bindSave_arr]
  have h := arr_body_wps (GF := GF) loc ann ra mo ibty accbty pbty xbty
    vs id a aty bs p rs hQ hsz ety hdec 0 fmapEmpty [] symFrame_empty
    (by omega)
  rw [show a + ((4 * 0 : Nat) : Int) = a by omega] at h
  rw [show ivVal ((0 : Nat) : Int) = ivVal 0 from rfl] at h
  rw [show (vs.take 0).sum = 0 from rfl] at h
  iapply h $$ Hpt

/-- The base-WP face with the engine readout (value + the preserved
    array cell in the final memory). -/
theorem arr_wp_readout (sbty : core_base_type) :
    iprop(cellOwn (procCtx rs).tagDefs (GF := GF) id (.own 1) (SpikeCell.mk a aty bs)) ⊢
      WP (⟨arrProg loc ann ra mo sbty ibty accbty pbty xbty
            (cellPtr id a) vs.length, [fmapEmpty],
          procCtl p, procCtx rs⟩ : CoreRt)
        @ Stuckness.NotStuck; ⊤
        {{ w, iprop(∀ (σ' : Mem) (ns : Nat) (κs : List Empty) (nt : Nat),
          (stateInterp σ' ns κs nt : IProp GF) ={⊤, ∅}=∗
            ⌜CoreRVal.val w = ivVal vs.sum ∧
              CellCoh (procCtx rs).tagDefs σ' id ⟨a, aty, bs⟩⌝) }} := by
  refine (arr_wps loc ann ra mo ibty accbty pbty xbty vs id a aty bs
    p rs hQ hsz ety hdec sbty).trans ?_
  refine (BI.emp_sep.2.trans (BI.sep_mono
    ((arr_blockSpecs loc ann ra mo ibty accbty pbty xbty vs id a aty bs
      p rs hQ hsz ety hdec).trans
      (wps_sound_empty (ctl := procCtl p) rfl (arrProg loc ann ra mo sbty ibty accbty pbty xbty
        (cellPtr id a) vs.length) [fmapEmpty]))
    .rfl)).trans ?_
  refine BI.wand_elim_left.trans ?_
  -- the projection's Iris half (`stateInterp_readout`) over the
  -- pure-consequence lemmas (Adequacy.lean) — no state-interpretation
  -- opening in this module.
  exact wp_mono fun w => stateInterp_readout fun _ _ _ _ hG =>
    sep_consequence (pure_consequence _)
      (cellOwn_consequence hG (procCtx rs).tagDefs id (.own 1) ⟨a, aty, bs⟩)

omit hQ hsz hdec in
/-- The label bodies are in the certified cone. -/
theorem arrBody_fragJ
    (n : Int) : Frag (arrBody loc ann ra mo xbty n) := by
  refine .if_ (PePure.of_isPePure rfl) (by
      rw [show peDepth (arrGuard n) = 2 from rfl,
        show lemDefaultFuel = 999999 + 1 from rfl]
      omega)
    (.sseq_spec (.load_op rfl (.sym _ _) (by
        rw [show peDepth (Pexpr ([] : List annot) ()
          (PEsym arrPSym)) = 1 from rfl,
          show lemDefaultFuel = 999999 + 1 from rfl]
        omega))
      (.run (PePure.all_of_isPePure rfl) ?_))
    .pure_sym
  intro pe hpe
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
  rcases hpe with rfl | rfl | rfl <;>
    (rw [show lemDefaultFuel = 999999 + 1 from rfl]
     first
      | (rw [show peDepth arrIncPe = 2 from rfl]; omega)
      | (rw [show peDepth arrAccXPe = 2 from rfl]; omega)
      | (rw [show peDepth arrShiftPe = 2 from rfl]; omega))

end ArrIris

/-! ## THE ACCEPTANCE THEOREM (engine vocabulary only in the
conclusion) -/

section ArrDrive

variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (mo : memory_order) (ibty accbty pbty xbty : core_base_type)

/-- ARRAY-SUM, END TO END: driving the REAL engine on the authored
    array-walk loop — real pointer arithmetic, interior loads of the
    seeded array allocation, the Specified-binder unwrap — from any
    memory carrying the seeded array cell, from any driver state holding
    the proc-carrying thread: the shipped loop at every fuel exhausts or
    delivers, never kills otherwise, never derails, and any delivered
    value IS `vs.sum`, with the ARRAY PRESERVED in the final memory
    (`CellCoh` at the original bytes). Partial correctness at every
    fuel. -/
theorem array_sum_certified
    (sbty : core_base_type) (vs : List Int) (id a : Int)
    (aty : ctype) (bs : List CerbMem.AbsByte)
    (hsz : vs.length * 4 ≤ CerbMem.sizeofCtype fmapEmpty aty)
    (ety : integerType)
    (hdec : ∀ (i : Nat) (hi : i < vs.length),
      ∀ (lum : List (Int × identifier)) (fpm : CerbMem.Funptrmap),
      CerbMem.reconstructValue fmapEmpty lum fpm (a + ((4 * i : Nat) : Int)) intTy
          ((bs.drop (4 * i)).take (CerbMem.sizeofCtype fmapEmpty intTy)) =
        CerbMem.MemValue.MVinteger ety (CerbMem.integerIval vs[i]))
    (σ₀ : Mem)
    (hcoh : Coh fmapEmpty σ₀ ((Iris.Std.PartialMap.singleton id
      (SpikeCell.mk a aty bs)) : SpikeHeapF SpikeCell)) :
    let prog := arrProg loc ann ra mo sbty ibty accbty pbty xbty
      (cellPtr id a) vs.length
    let rs := arrRS loc ann ra mo ibty accbty pbty xbty vs.length
    DriverSafeCtl (procCtx rs) (procThread arrProcSym prog [fmapEmpty]) prog [fmapEmpty]
      (procCtl arrProcSym) σ₀
      (fun v σ' => v = ivVal vs.sum ∧ CellCoh fmapEmpty σ' id ⟨a, aty, bs⟩) := by
  intro prog rs
  have hlbl : (procCtx rs).labelsAt (procCtl arrProcSym).proc = _ :=
    procCtx_labels (arrRS_labeledAt loc ann ra mo ibty accbty pbty xbty vs.length)
  refine engine_adequacy (GF := SpikeGF)
    (M := procCtx rs) rfl rfl (ctl := procCtl arrProcSym) rfl
    (fun l params cont hl => by
      rw [hlbl] at hl
      obtain ⟨-, rfl⟩ := arrQ_inv loc ann ra mo ibty accbty pbty xbty
        vs.length hl
      exact arrBody_fragJ loc ann ra mo xbty vs.length)
    (fun l params cont hl => by
      rw [hlbl] at hl
      obtain ⟨-, rfl⟩ := arrQ_inv loc ann ra mo ibty accbty pbty xbty
        vs.length hl
      exact Nat.le_trans (arrBody_fragJ loc ann ra mo xbty vs.length).pot_le_two
        (by rw [show esize (arrBody loc ann ra mo xbty vs.length) = 3 from rfl,
          show lemDefaultFuel = 999999 + 1 from rfl]; omega))
    (procCtx_fragProcs _)
    prog fmapEmpty [] σ₀ _
    (.save (saveParams_pure_of_vals rfl) (saveParams_depth_of_vals rfl) (arrBody_fragJ loc ann ra mo xbty vs.length))
    (Nat.le_trans (Frag.pot_le_two (e := prog) (.save (saveParams_pure_of_vals rfl) (saveParams_depth_of_vals rfl)
        (arrBody_fragJ loc ann ra mo xbty vs.length)))
      (by rw [show esize prog = 4 from rfl, show lemDefaultFuel = 999999 + 1 from rfl]; omega))
    hcoh
    (fun v σ' => v = ivVal vs.sum ∧ CellCoh fmapEmpty σ' id ⟨a, aty, bs⟩)
    ?_ (th₀ := procThread arrProcSym prog [fmapEmpty]) rfl
  intro inst
  refine .trans ?_ (arr_wp_readout loc ann ra mo ibty accbty pbty xbty
    vs id a aty bs arrProcSym rs
    (arrRS_labeledAt loc ann ra mo ibty accbty pbty xbty vs.length)
    hsz ety hdec sbty)
  exact (BigSepM.bigSepM_singleton).1

end ArrDrive

end CerberusHeapLang
