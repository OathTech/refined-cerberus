/-
CerberusHeapLang.DisposeExhibit — DISPOSE A LIST: the classical
Reynolds/O'Hearn `{list p} dispose(p) {emp}` on the real engine
(kill/free arc K4, the first exhibit).

THE PROGRAM (authored Core — walk a linked list of CREATED nodes and
`kill(static node, ·)` each; the loop variable is the remaining chain):

    save dl: (cur : ptr := head) in
      lets b = memop(PtrEq, [cur, NULL(node)]) in
      if b then unit
      else
        lets Specified(n) = load(node*, array_shift(cur, long, 1)) in
        lets _ = kill(static node, cur) in
        run dl(n)

THE NODE, THE NULL, THE PREDICATE are ListRevExhibit.lean's verbatim
(`nodeTy`, `nullNode`, `isList p ns` — the IDENTITY-INDEXED list of
created nodes, one `cellOwn … (.own 1)` per node): nothing about lists
is re-stated here; this module only DISPOSES what that module builds.

THE RULES CONSUMED (all public, API.lean): `wps_kill`/`wpt_kill` (K2 —
THE DISPOSE RULE, at the node cell reassembled as `pointsToCell … (.own
1)` through `pointsToCell_cellOwn_iff`), `wps_kill_eval`/`wpt_kill_eval`
(the operand form at the bound symbol), the node-field load client rule
(`wps_load_node_field`/`wpt_load_node_field`, ListRevExhibit —
`wps_load_cell_at` at `nodePtrTy`), `wps_seq`/`wpt_seq` (the wild binder
for the kill's unit), `wps_seq_spec`, `wps_seq_sym`, `wps_memop_eval` +
`wps_memop_ptreq`, `wps_if_true`/`wps_if_false`, `wps_ofVal` (the exit
IS the unit value), `wps_run`, `wps_save_vals`/`wpt_save_vals`, and the
label-context rules (`blockSpecs_intro`, `wps_frame_labels`,
`blockSpecs_frame`; total twins). No `Step.*`, no per-step drive
equations, no state-interpretation opening outside the ONE sanctioned
readout combinator `stateInterp_readout`.

THE STATEMENTS. Partial: `dl_wps` —
`isList head ns ⊢ wps … (dlPost ns) (dlProg … head) [fmapEmpty]` where
`dlPost ns w _ := ⌜w = .pure Vunit⌝ ∗ deadNodes ns` (the persistent dead
cell of EVERY node of the list: `deadNodes ns := [∗] nd ∈ ns, ∃ a,
deadObj nd.1 a nodeTy`); `dl_wps_emp` is the textbook face `{isList head
ns} dispose {emp}` (the dead knowledge dropped). Total: `dl_wpt` at the
DERIVED budget `dlCost |ns| + 1 = 12·|ns| + 6` (12 per node: null test 3
+ if 1 + next-field load 4 + kill 3 + jump 1; exit 5: null test 3 + if 1
+ unit delivery 1; entry 1). Both by the label-context loop with the
invariant `deadNodes done ∗ isList cur rest`, `ns = done ++ rest`, the
variant the remaining chain's length; frame theorems by the generic
statement frame rules. Engine-facing: `dispose_list_certified_total`
(the `driveU` lane, PROVISIONAL as every `driveU` export — API.lean
header): from any memory carrying the seeded chain next to an arbitrary
disjoint frame `R`, the engine DELIVERS `Vunit` at exactly `12·|ns| + 6`
drive steps, EVERY node's id is in `deadAllocations` with its record
erased (`killM`'s effect, CerbMem.lean:1576-1578), and the frame is
returned verbatim (`Sat σ' R`). PRODUCTION: `dispose_list_certified_production`
— the shipped pipeline (`runND ∘ drive ∘ initial_driver_state`) on the
self-contained file that BUILDS a two-node list with `create`s (the
list-reverse production's prefix `lrProdPrefix`, verbatim) and then
disposes it, is EXACTLY ONE Active execution delivering `Vunit` whose
final memory has two DISTINCT allocation ids dead with their records
erased (the proof witnesses them as the two created nodes; the statement
itself names no node — the K4 range audit's M-2).

WHAT IS AND IS NOT READ OFF (honest): the logic's resources speak for
the nodes it owned — `deadObj` per node — so the readout is per-id
("this id is dead and erased"); nothing speaks for the WHOLE dead list
or the WHOLE allocation table (the design note's `deadAllocations = [1]`
is not derivable through the public rules — AllocExhibit's K2 note), so
"no live node remains" is stated as "each of the created ids is dead",
which, with the ids distinct, is what the program did.
-/
import CerberusHeapLang.ProdLoopExhibit

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Map

/-! ## THE PROGRAM (authored Core) -/

def dlBSym : sym := Symbol "" 601 SD_None
def dlCurSym : sym := Symbol "" 602 SD_None
def dlNSym : sym := Symbol "" 603 SD_None
def dlLoopSym : sym := Symbol "" 604 SD_None
def dlProcSym : sym := Symbol "" 605 SD_None

/-- The null test: `memop(PtrEq, [cur, NULL(node)])`. -/
def dlMemopE : CoreExpr :=
  memopRedex PtrEq [Pexpr [] () (PEsym dlCurSym), Pexpr [] () (PEval nullVal)]

/-- `load(node*, array_shift(cur, long, 1))` — n := cur->next. -/
def dlLoadE (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (mo : memory_order) : CoreExpr :=
  loadOpRedex loc ann nodePtrTy (lrShiftPe dlCurSym) mo

/-- `kill(static node, cur)` — THE DISPOSE at the bound symbol. -/
def dlKillE (loc : CerbLocation.Loc) (ann : core_run_annotation) : CoreExpr :=
  killOpRedex loc ann (Static0 nodeTy) (Pexpr [] () (PEsym dlCurSym))

/-- The exit: the unit value. -/
def dlExit : CoreExpr := Expr [] (Epure (Pexpr [] () (PEval Vunit)))

/-- The else branch: load next, dispose the node, jump with n. -/
def dlElse (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (mo : memory_order) (nbty ubty : core_base_type) : CoreExpr :=
  Expr [] (Esseq (specPat [] [] dlNSym nbty)
    (dlLoadE loc ann mo)
    (Expr [] (Esseq (Pattern [] (CaseBase (none, ubty)))
      (dlKillE loc ann)
      (Expr [] (Erun ra dlLoopSym [Pexpr [] () (PEsym dlNSym)])))))

/-- The registered loop body. -/
def dlBody (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (mo : memory_order) (bbty nbty ubty : core_base_type) : CoreExpr :=
  Expr [] (Esseq (symPat [] dlBSym bbty)
    dlMemopE
    (Expr [] (Eif (Pexpr [] () (PEsym dlBSym))
      dlExit
      (dlElse loc ann ra mo nbty ubty))))

/-- The save parameter (`cur := head`). -/
def dlParams (cbty : core_base_type) (head : CerbMem.PointerValue) :
    List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)) :=
  [(dlCurSym, ((cbty, none), Pexpr [] () (PEval (ptrVal head))))]

/-- The whole program. -/
def dlProg (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (mo : memory_order) (sbty cbty bbty nbty ubty : core_base_type)
    (head : CerbMem.PointerValue) : CoreExpr :=
  Expr [] (Esave (dlLoopSym, sbty) (dlParams cbty head)
    (dlBody loc ann ra mo bbty nbty ubty))

/-- The label map. -/
def dlQ (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (mo : memory_order) (cbty bbty nbty ubty : core_base_type) : LabelMap :=
  fmapAddBy symCmpL dlLoopSym
    ([(dlCurSym, cbty)], dlBody loc ann ra mo bbty nbty ubty)
    fmapEmpty

/-- The run state carrying the two-level `labeled` tie. -/
def dlRS (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (mo : memory_order) (cbty bbty nbty ubty : core_base_type) :
    core_run_state :=
  { spikeRunState with
      labeled := fmapAddBy symCmpL dlProcSym
        (dlQ loc ann ra mo cbty bbty nbty ubty) fmapEmpty }

section DlFacts

variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (mo : memory_order) (cbty bbty nbty ubty : core_base_type)

theorem dlQ_lookup :
    lookupLabel (dlQ loc ann ra mo cbty bbty nbty ubty) dlLoopSym =
      some ([(dlCurSym, cbty)], dlBody loc ann ra mo bbty nbty ubty) := by
  unfold lookupLabel dlQ
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

theorem dlQ_inv {l : sym} {params : List (sym × core_base_type)}
    {cont : CoreExpr}
    (h : lookupLabel (dlQ loc ann ra mo cbty bbty nbty ubty) l =
      some (params, cont)) :
    params = [(dlCurSym, cbty)] ∧
      cont = dlBody loc ann ra mo bbty nbty ubty := by
  unfold lookupLabel dlQ at h
  rw [fmapLookupBy_addBy_empty] at h
  split at h
  · obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
    exact ⟨h1.symm ▸ rfl, h2.symm ▸ rfl⟩
  · cases h

theorem dlRS_labeledAt :
    LabeledAt (dlRS loc ann ra mo cbty bbty nbty ubty) dlProcSym
      (dlQ loc ann ra mo cbty bbty nbty ubty) := by
  unfold LabeledAt dlRS
  show fmapLookupBy _ _ (fmapAddBy symCmpL dlProcSym _ fmapEmpty) = _
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

end DlFacts

/-! ## Frames and lookups -/

/-- The frame after the loop binding (cur). -/
def dlFrame (vc : value) (f : Fmap sym value) : Fmap sym value :=
  envAdd dlCurSym vc f

/-- ... after additionally binding the null-test boolean. -/
def dlFrameB (vb vc : value) (f : Fmap sym value) : Fmap sym value :=
  envAdd dlBSym vb (dlFrame vc f)

/-- ... after additionally binding the loaded next pointer. -/
def dlFrameN (vn vb vc : value) (f : Fmap sym value) : Fmap sym value :=
  envAdd dlNSym vn (dlFrameB vb vc f)

theorem dlFrame_symFrame {f : Fmap sym value} (hf : SymFrame f)
    (vc : value) : SymFrame (dlFrame vc f) :=
  hf.add _ _

theorem dlFrameB_symFrame {f : Fmap sym value} (hf : SymFrame f)
    (vb vc : value) : SymFrame (dlFrameB vb vc f) :=
  (dlFrame_symFrame hf _).add _ _

theorem dlFrameN_symFrame {f : Fmap sym value} (hf : SymFrame f)
    (vn vb vc : value) : SymFrame (dlFrameN vn vb vc f) :=
  (dlFrameB_symFrame hf _ _).add _ _

section DlLookups

variable {f : Fmap sym value} (hf : SymFrame f) (vn vb vc : value)

include hf

theorem dlFrame_lookup_cur :
    fmapLookupBy symCmpK dlCurSym (dlFrame vc f) = some vc := by
  unfold dlFrame
  rw [envAdd_lookup hf symCmpK, if_pos (by decide +kernel)]

theorem dlFrameB_lookup_b :
    fmapLookupBy symCmpK dlBSym (dlFrameB vb vc f) = some vb := by
  unfold dlFrameB
  rw [envAdd_lookup (dlFrame_symFrame hf _) symCmpK, if_pos (by decide +kernel)]

theorem dlFrameB_lookup_cur :
    fmapLookupBy symCmpK dlCurSym (dlFrameB vb vc f) = some vc := by
  unfold dlFrameB
  rw [envAdd_lookup (dlFrame_symFrame hf _) symCmpK,
    if_neg (by decide +kernel), dlFrame_lookup_cur hf]

theorem dlFrameN_lookup_n :
    fmapLookupBy symCmpK dlNSym (dlFrameN vn vb vc f) = some vn := by
  unfold dlFrameN
  rw [envAdd_lookup (dlFrameB_symFrame hf _ _) symCmpK, if_pos (by decide +kernel)]

theorem dlFrameN_lookup_cur :
    fmapLookupBy symCmpK dlCurSym (dlFrameN vn vb vc f) = some vc := by
  unfold dlFrameN
  rw [envAdd_lookup (dlFrameB_symFrame hf _ _) symCmpK,
    if_neg (by decide +kernel), dlFrameB_lookup_cur hf]

end DlLookups

/-! ## Binding computations -/

theorem bindSave_dl (cbty : core_base_type) (head : CerbMem.PointerValue)
    (f : Fmap sym value) (rest : List (Fmap sym value)) :
    bindSaveParams (dlParams cbty head) [ptrVal head] (f :: rest) =
      dlFrame (ptrVal head) f :: rest := by
  show update_env (mk_sym_pat dlCurSym cbty) (ptrVal head) (f :: rest) = _
  rw [update_env_cons, update_env_aux_sym]
  rfl

theorem bindArgs_dl (cbty : core_base_type) (v : value) (f : Fmap sym value)
    (rest : List (Fmap sym value)) :
    bindArgs [(dlCurSym, cbty)] [v] (f :: rest) = dlFrame v f :: rest := by
  show update_env (mk_sym_pat dlCurSym cbty) v (f :: rest) = _
  rw [update_env_cons, update_env_aux_sym]
  rfl

theorem bindSym_dl (bbty : core_base_type) (vb vc : value)
    (f : Fmap sym value) (rest : List (Fmap sym value)) :
    update_env (symPat [] dlBSym bbty) vb (dlFrame vc f :: rest) =
      dlFrameB vb vc f :: rest := by
  rw [update_env_cons]
  show update_env_aux (mk_sym_pat dlBSym bbty) vb (dlFrame vc f) :: rest = _
  rw [update_env_aux_sym]
  rfl

/-! ## Evaluation facts at the bound frames -/

section DlEval

variable {f : Fmap sym value} (hf : SymFrame f) (rest : List (Fmap sym value))

theorem dl_memop_operands_nonvalue :
    valueFromPexprs [Pexpr ([] : List annot) () (PEsym dlCurSym),
      Pexpr [] () (PEval nullVal)] = none := rfl

include hf

theorem dl_cur_eval (vc : value) :
    evalPexpr fmapEmpty fmapEmpty (dlFrame vc f :: rest)
      (Pexpr [] () (PEsym dlCurSym)) = some vc := by
  rw [evalPexpr_sym_empty]
  exact lookup_env_head (dlFrame_lookup_cur hf _) rest

theorem dl_guard_eval (vb vc : value) :
    evalPexpr fmapEmpty fmapEmpty (dlFrameB vb vc f :: rest)
      (Pexpr [] () (PEsym dlBSym)) = some vb := by
  rw [evalPexpr_sym_empty]
  exact lookup_env_head (dlFrameB_lookup_b hf _ _) rest

/-- The load's shifted operand: `array_shift(cur, long, 1)` at a node
    pointer — +8 within the allocation (the engine's own arithmetic). -/
theorem dl_shift_eval_B (vb : value) (id aN : Int) :
    evalPexpr fmapEmpty fmapEmpty (dlFrameB vb (ptrVal (cellPtr id aN)) f :: rest)
      (lrShiftPe dlCurSym) = some (ptrVal (cellPtr id (aN + 8))) := by
  unfold lrShiftPe
  rw [evalPexpr_array_shift]
  rw [show evalPexpr fmapEmpty fmapEmpty (dlFrameB vb (ptrVal (cellPtr id aN)) f :: rest)
      (Pexpr [] () (PEsym dlCurSym)) = some (ptrVal (cellPtr id aN)) from by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (dlFrameB_lookup_cur hf _ _) rest]
  show evalArrayShift fmapEmpty longTy (Vobject (OVpointer (cellPtr id aN))) (ivVal 1) = _
  exact evalArrayShift_long_one id aN

/-- The kill's operand: `cur`, after n is bound. -/
theorem dl_kill_operand_eval (vn vb vc : value) :
    evalPexpr fmapEmpty fmapEmpty (dlFrameN vn vb vc f :: rest)
      (Pexpr [] () (PEsym dlCurSym)) = some vc := by
  rw [evalPexpr_sym_empty]
  exact lookup_env_head (dlFrameN_lookup_cur hf _ _ _) rest

theorem dl_args_eval (vn vb vc : value) :
    evalPexprs fmapEmpty fmapEmpty (dlFrameN vn vb vc f :: rest)
      [Pexpr [] () (PEsym dlNSym)] = some [vn] := by
  rw [evalPexprs_cons]
  rw [show evalPexpr fmapEmpty fmapEmpty (dlFrameN vn vb vc f :: rest)
      (Pexpr ([] : List annot) () (PEsym dlNSym)) = some vn from by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (dlFrameN_lookup_n hf _ _ _) rest]
  rfl

end DlEval

/-! ## THE DEAD LIST: persistent knowledge that every node was disposed -/

section DeadNodes

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]

/-- The dead cells of a node list: for each node, `deadObj` at its
    allocation id (SOME base — the address is not part of the list's
    identity), the node type. Structural recursion, as `isList`. -/
def deadNodes : List (Int × Int) → IProp GF
  | [] => iprop(emp)
  | nd :: ns => iprop((∃ a : Int, deadObj fmapEmpty nd.1 a nodeTy) ∗ deadNodes ns)

@[simp] theorem deadNodes_nil : deadNodes (GF := GF) [] = iprop(emp) := rfl

theorem deadNodes_cons (nd : Int × Int) (ns : List (Int × Int)) :
    deadNodes (GF := GF) (nd :: ns) =
      iprop((∃ a : Int, deadObj fmapEmpty nd.1 a nodeTy) ∗ deadNodes ns) := rfl

/-- The dead list splits at ++ (the invariant's back edge appends the
    disposed node to the done part). -/
theorem deadNodes_append (l₁ l₂ : List (Int × Int)) :
    deadNodes (GF := GF) (l₁ ++ l₂) ⊣⊢ iprop(deadNodes l₁ ∗ deadNodes l₂) := by
  induction l₁ with
  | nil =>
    rw [List.nil_append, deadNodes_nil]
    exact BI.emp_sep.symm
  | cons nd l₁ ih =>
    rw [List.cons_append, deadNodes_cons, deadNodes_cons]
    exact (BI.sep_congr_right ih).trans BI.sep_assoc.symm

end DeadNodes

/-! ## THE INVARIANT AND THE TEXTBOOK PROOF (partial stratum) -/

section DlIris

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (mo : memory_order) (cbty bbty nbty ubty : core_base_type)
  (ns : List (Int × Int))
variable (p : sym) (rs : core_run_state)
  (hQ : LabeledAt rs p (dlQ loc ann ra mo cbty bbty nbty ubty))

/-- The postcondition: the unit value, and every node of the list dead. -/
abbrev dlPost : SpikeVal → EnvStack → IProp GF := fun w _ =>
  iprop(⌜w = SpikeVal.pure Vunit⌝ ∗ deadNodes ns)

/-- THE LOOP INVARIANT: `deadNodes done ∗ isList cur rest` with
    `ns = done ++ rest`, over any reachable frame. UNFRAMED — the
    frame comes by the generic label-context frame rule. -/
abbrev dlLs : LabelSpec GF := fun _ args ρ =>
  iprop(∃ (done rest' : List (Int × Int)) (pCur : CerbMem.PointerValue)
      (f : Fmap sym value) (renv : List (Fmap sym value)),
    ⌜args = [ptrVal pCur] ∧ ns = done ++ rest' ∧ ρ = f :: renv ∧ SymFrame f⌝ ∗
    deadNodes done ∗ isList pCur rest')

include hQ

/-- The loop body verifies at any invariant frame — each construct by
    its rule; THE DISPOSE is `wps_kill` at the node's cell reassembled
    as a points-to (`pointsToCell_cellOwn_iff`). -/
theorem dl_body_wps (done rest' : List (Int × Int))
    (pCur : CerbMem.PointerValue) (f : Fmap sym value)
    (renv : List (Fmap sym value)) (hf : SymFrame f)
    (hxs : ns = done ++ rest') :
    iprop(deadNodes (GF := GF) done ∗ isList pCur rest') ⊢
      wps (procCtx rs) (some p) (dlLs ns) emptyProcSpec (dlPost ns) (dlBody loc ann ra mo bbty nbty ubty)
        (dlFrame (ptrVal pCur) f :: renv) := by
  rw [show dlBody loc ann ra mo bbty nbty ubty =
    Expr [] (Esseq (symPat [] dlBSym bbty) dlMemopE
      (Expr [] (Eif (Pexpr [] () (PEsym dlBSym)) dlExit
        (dlElse loc ann ra mo nbty ubty)))) from rfl]
  iintro ⟨HD, HC⟩
  cases rest' with
  | nil =>
    -- cur == NULL: the test answers true, the exit delivers unit, and
    -- every node is in the done part.
    rw [isList_nil]
    icases HC with %hnull
    subst hnull
    iapply wps_seq_sym
    rw [show dlMemopE = memopRedex PtrEq
      [Pexpr [] () (PEsym dlCurSym), Pexpr [] () (PEval nullVal)] from rfl]
    iapply wps_memop_eval PtrEq _ _ _
      dl_memop_operands_nonvalue (dl_cur_eval hf renv _) rfl
    rw [show memopRedex PtrEq [Pexpr [] () (PEval (ptrVal nullNode)),
        Pexpr [] () (PEval nullVal)] =
      memopPtrEqVals (Vobject (OVpointer nullNode))
        (Vobject (OVpointer nullNode)) from rfl]
    iapply wps_memop_ptreq nullNode nullNode _
      (fun σ => eqPtrval_null_null nodeTy nodeTy σ)
    iexists (boolValue true)
    isplit
    · ipureintro
      rfl
    rw [bindSym_dl]
    iapply wps_if_true [] (Pexpr [] () (PEsym dlBSym)) _ _ _
      (by rw [procCtx_extern, dl_guard_eval hf renv (boolValue true) _]; rfl)
    rw [show dlExit = ofVal (SpikeVal.pure Vunit) from rfl]
    iapply wps_ofVal (SpikeVal.pure Vunit) _
    isplit
    · ipureintro
      rfl
    rw [show ns = done by rw [hxs]; simp]
    iexact HD
  | cons nd vs =>
    -- cur is a node: test false; load next; DISPOSE the node; jump with n.
    rw [isList_cons]
    icases HC with ⟨%aN, %q, %bs, %hfacts, Hpt, HT⟩
    obtain ⟨rfl, h0, h1, hlen, hval, hnext⟩ := hfacts
    iapply wps_seq_sym
    rw [show dlMemopE = memopRedex PtrEq
      [Pexpr [] () (PEsym dlCurSym), Pexpr [] () (PEval nullVal)] from rfl]
    iapply wps_memop_eval PtrEq _ _ _
      dl_memop_operands_nonvalue (dl_cur_eval hf renv _) rfl
    rw [show memopRedex PtrEq [Pexpr [] () (PEval (ptrVal (cellPtr nd.1 aN))),
        Pexpr [] () (PEval nullVal)] =
      memopPtrEqVals (Vobject (OVpointer (cellPtr nd.1 aN)))
        (Vobject (OVpointer nullNode)) from rfl]
    iapply wps_memop_ptreq (cellPtr nd.1 aN) nullNode _
      (fun σ => eqPtrval_cell_null nd.1 aN nodeTy σ)
    iexists (boolValue false)
    isplit
    · ipureintro
      rfl
    rw [bindSym_dl]
    iapply wps_if_false [] (Pexpr [] () (PEsym dlBSym)) _ _ _
      (by rw [procCtx_extern, dl_guard_eval hf renv (boolValue false) _]; rfl)
    rw [show dlElse loc ann ra mo nbty ubty =
      Expr [] (Esseq (specPat [] [] dlNSym nbty)
        (dlLoadE loc ann mo)
        (Expr [] (Esseq (Pattern [] (CaseBase (none, ubty)))
          (dlKillE loc ann)
          (Expr [] (Erun ra dlLoopSym [Pexpr [] () (PEsym dlNSym)])))))
      from rfl]
    iapply wps_seq_spec
    rw [show dlLoadE loc ann mo =
      loadOpRedex loc ann nodePtrTy (lrShiftPe dlCurSym) mo from rfl]
    iapply wps_load_eval loc ann nodePtrTy (lrShiftPe dlCurSym) mo _
      rfl (dl_shift_eval_B hf renv _ nd.1 aN)
    rw [show cellPtr nd.1 (aN + 8) = cellPtr nd.1 (aN + ((8 : Nat) : Int))
      from rfl]
    iapply wps_load_node_field (M := procCtx rs) (p := some p) (Θ := emptyProcSpec) loc ann nd.1 aN 8 mo (.own 1) bs _
      (by rw [nodeTy_size]; omega)
      (fun lum fpm => hnext lum fpm _)
    isplitl [Hpt]
    · iexact Hpt
    iintro %fp Hpt
    iexists (OVpointer q)
    isplit
    · ipureintro
      show (valueFromMemValue (.MVpointer nodeTy q)).2 = _
      rw [valueFromMemValue_ptr]
    rw [update_env_spec]
    rw [show envAdd dlNSym (Vobject (OVpointer q))
        (dlFrameB (boolValue false) (ptrVal (cellPtr nd.1 aN)) f) =
      dlFrameN (ptrVal q) (boolValue false) (ptrVal (cellPtr nd.1 aN)) f from rfl]
    iapply wps_seq
    rw [show dlKillE loc ann = killOpRedex loc ann (Static0 nodeTy)
      (Pexpr [] () (PEsym dlCurSym)) from rfl]
    iapply wps_kill_eval loc ann (Static0 nodeTy) _ _ rfl (pv := cellPtr nd.1 aN)
      (by rw [procCtx_extern]; exact dl_kill_operand_eval hf renv _ _ _)
    iapply wps_kill loc ann (Static0 nodeTy) (cellPtr nd.1 aN) nodeTy bs _ rfl
    isplitl [Hpt]
    · iapply (pointsToCell_cellOwn_iff _ _ _ _ _).mpr
      iexists nd.1, aN
      isplit
      · ipureintro
        rfl
      · iexact Hpt
    iintro ⟨%id, %a, %hpv, Hd⟩
    obtain ⟨hid, ha⟩ := cellPtr_inj hpv
    subst hid
    subst ha
    iapply wps_run [] ra dlLoopSym [Pexpr [] () (PEsym dlNSym)] _ _
      (by rw [procCtx_labels hQ]
          exact dlQ_lookup loc ann ra mo cbty bbty nbty ubty)
      (dl_args_eval hf renv _ _ _)
    iexists (done ++ [nd]), vs, q,
      (dlFrameN (ptrVal q) (boolValue false) (ptrVal (cellPtr nd.1 aN)) f), renv
    isplit
    · ipureintro
      refine ⟨rfl, ?_, rfl, dlFrameN_symFrame hf _ _ _⟩
      rw [hxs]
      simp
    isplitl [HD Hd]
    · -- the DISPOSED node joins the done part
      iapply (deadNodes_append done [nd]).2
      isplitl [HD]
      · iexact HD
      · rw [deadNodes_cons, deadNodes_nil]
        isplitl [Hd]
        · iexists aN
          iexact Hd
        · itrivial
    · iexact HT

/-- THE BLOCK SPECIFICATION (per-label invariant rule). -/
theorem dl_blockSpecs :
    ⊢ blockSpecs (GF := GF) (procCtx rs) (some p) (dlLs ns) emptyProcSpec (dlPost ns) := by
  refine blockSpecs_intro fun l params cont args env0 envs hl => ?_
  rw [procCtx_labels hQ] at hl
  obtain ⟨rfl, rfl⟩ := dlQ_inv loc ann ra mo cbty bbty nbty ubty hl
  iintro ⟨%done, %rest', %pCur, %f, %renv, %hpure, HD, HC⟩
  obtain ⟨rfl, hxs, hρ, hf⟩ := hpure
  obtain ⟨rfl, rfl⟩ : f = env0 ∧ renv = envs := by
    have h1 := congrArg (fun l => l.head?) hρ
    have h2 := congrArg (fun l => l.tail) hρ
    simp at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  rw [bindArgs_dl]
  iapply dl_body_wps loc ann ra mo cbty bbty nbty ubty ns p rs hQ
    done rest' pCur f renv hf hxs
  isplitl [HD]
  · iexact HD
  · iexact HC

/-- DISPOSE A LIST, the statement judgment: `{isList head ns} dispose(head)
    {ret unit. deadNodes ns}` — from the whole list alone, the program
    delivers unit and the persistent dead cell of every node. -/
theorem dl_wps (sbty : core_base_type) (head : CerbMem.PointerValue) :
    isList (GF := GF) head ns ⊢
      wps (procCtx rs) (some p) (dlLs ns) emptyProcSpec (dlPost ns)
        (dlProg loc ann ra mo sbty cbty bbty nbty ubty head) [fmapEmpty] := by
  rw [show dlProg loc ann ra mo sbty cbty bbty nbty ubty head =
    Expr [] (Esave (dlLoopSym, sbty) (dlParams cbty head)
      (dlBody loc ann ra mo bbty nbty ubty)) from rfl]
  iintro HL
  iapply wps_save [] (dlLoopSym, sbty) _ _ fmapEmpty [] (cvals := [ptrVal head]) rfl
  rw [bindSave_dl]
  iapply dl_body_wps loc ann ra mo cbty bbty nbty ubty ns p rs hQ [] ns
    head fmapEmpty [] symFrame_empty (by simp)
  isplitr [HL]
  · rw [deadNodes_nil]
    itrivial
  · iexact HL

/-- THE TEXTBOOK FACE: `{isList head ns} dispose(head) {emp}` — the dead
    knowledge dropped (affinity). -/
theorem dl_wps_emp (sbty : core_base_type) (head : CerbMem.PointerValue) :
    isList (GF := GF) head ns ⊢
      wps (procCtx rs) (some p) (dlLs ns) emptyProcSpec (fun w _ => iprop(⌜w = SpikeVal.pure Vunit⌝))
        (dlProg loc ann ra mo sbty cbty bbty nbty ubty head) [fmapEmpty] := by
  iintro HL
  ihave HW := dl_wps loc ann ra mo cbty bbty nbty ubty ns p rs hQ sbty head $$ HL
  iapply wps_wand _ _ $$ HW
  iintro %w %ρ' ⟨%hw, -⟩
  ipureintro
  exact hw

/-- The block specifications at the framed label context. -/
theorem dl_blockSpecs_frame (RF : IProp GF) :
    ⊢ blockSpecs (GF := GF) (procCtx rs) (some p) (frameLs RF (dlLs ns)) emptyProcSpec
      (fun w ρ' => iprop(dlPost ns w ρ' ∗ RF)) :=
  (dl_blockSpecs loc ann ra mo cbty bbty nbty ubty ns p rs hQ).trans
    (blockSpecs_frame RF)

/-- `{isList head ns ∗ RF} dispose(head) {unit ∗ deadNodes ns ∗ RF}` — the
    frame carried across every back edge by the framed label context. -/
theorem dl_wps_frame (RF : IProp GF) (sbty : core_base_type)
    (head : CerbMem.PointerValue) :
    iprop(isList (GF := GF) head ns ∗ RF) ⊢
      wps (procCtx rs) (some p) (frameLs RF (dlLs ns)) emptyProcSpec
        (fun w ρ' => iprop(dlPost ns w ρ' ∗ RF))
        (dlProg loc ann ra mo sbty cbty bbty nbty ubty head) [fmapEmpty] := by
  iintro ⟨HL, HF⟩
  ihave HW := dl_wps loc ann ra mo cbty bbty nbty ubty ns p rs hQ sbty head $$ HL
  iapply wps_frame_labels RF _ _ $$ HW HF

end DlIris

/-! ## The certified cone membership -/

section DlFrag

variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (mo : memory_order) (bbty nbty ubty : core_base_type)

/-- The label body is in the certified cone: the kill is `Frag.kill_op`
    at the bound symbol (either kind since K3; here `Static0 nodeTy`). -/
theorem dlBody_fragJ : Frag (dlBody loc ann ra mo bbty nbty ubty) := by
  have hb : BareHead (memopRedex PtrEq
      [Pexpr [] () (PEsym dlCurSym), Pexpr [] () (PEval nullVal)]) :=
    .memop_op rfl (.sym _ _) (.val _ _)
      (by rw [show peDepth (Pexpr ([] : List annot) () (PEsym dlCurSym)) = 1
          from rfl, show lemDefaultFuel = 999999 + 1 from rfl]; omega)
      (by rw [show peDepth (Pexpr ([] : List annot) () (PEval nullVal)) = 1
          from rfl, show lemDefaultFuel = 999999 + 1 from rfl]; omega)
  refine .sseq_sym hb hb.frag
    (.if_ (PePure.of_isPePure rfl) (by
        rw [show peDepth (Pexpr ([] : List annot) () (PEsym dlBSym)) = 1
          from rfl, show lemDefaultFuel = 999999 + 1 from rfl]
        omega)
      (.val_pure Vunit)
      (.sseq_spec
        (.load_op rfl
          (.arrayShift [] longTy (.sym _ _) (.val _ _))
          (by rw [show peDepth (lrShiftPe dlCurSym) = 2 from rfl,
            show lemDefaultFuel = 999999 + 1 from rfl]; omega))
        (.sseq
          (.kill_op rfl (.sym [] dlCurSym)
            (by rw [show peDepth (Pexpr ([] : List annot) () (PEsym dlCurSym)) = 1
                from rfl, show lemDefaultFuel = 999999 + 1 from rfl]; omega))
          (.run (PePure.all_of_isPePure rfl) (by
            intro pe hpe
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
            subst hpe
            rw [show peDepth (Pexpr ([] : List annot) () (PEsym dlNSym)) = 1 from rfl,
              show lemDefaultFuel = 999999 + 1 from rfl]
            omega)))))

theorem dlBody_pot : pot (dlBody loc ann ra mo bbty nbty ubty) = 6 := rfl

theorem dlProg_pot (sbty cbty : core_base_type) (head : CerbMem.PointerValue) :
    pot (dlProg loc ann ra mo sbty cbty bbty nbty ubty head) = 7 := rfl

end DlFrag

/-! ## THE TOTAL LANE: the variant is the remaining chain's length -/

/-- The derived per-label-entry step budget at remaining length r:
    12 per node (null test 3 + if 1 + next-field load 4 + kill 3 + jump
    1), exit 5 (null test 3 + if 1 + unit delivery 1). -/
def dlCost (r : Nat) : Nat := 12 * r + 5

theorem dlCost_zero : dlCost 0 = 3 + (1 + 1) := rfl

theorem dlCost_succ (r : Nat) : dlCost (r + 1) = 3 + (1 + (4 + (3 + (1 + dlCost r)))) := by
  unfold dlCost
  omega

section DlTotal

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (mo : memory_order) (cbty bbty nbty ubty : core_base_type)
  (ns : List (Int × Int))
variable (p : sym) (rs : core_run_state)
  (hQ : LabeledAt rs p (dlQ loc ann ra mo cbty bbty nbty ubty))

/-- The variant-indexed label context: the partial invariant plus the
    variant pin `m = dlCost rest'.length`. -/
abbrev dlLsT : LabelSpecT GF := fun _ m args ρ =>
  iprop(∃ (done rest' : List (Int × Int)) (pCur : CerbMem.PointerValue)
      (f : Fmap sym value) (renv : List (Fmap sym value)),
    ⌜args = [ptrVal pCur] ∧ ns = done ++ rest' ∧ m = dlCost rest'.length ∧
      ρ = f :: renv ∧ SymFrame f⌝ ∗
    deadNodes done ∗ isList pCur rest')

include hQ

/-- The loop body meets its variant budget at any invariant frame — the
    same derivation as `dl_body_wps`, at the total stratum. -/
theorem dl_body_wpt (done rest' : List (Int × Int))
    (pCur : CerbMem.PointerValue) (f : Fmap sym value)
    (renv : List (Fmap sym value)) (hf : SymFrame f)
    (hxs : ns = done ++ rest') :
    iprop(deadNodes (GF := GF) done ∗ isList pCur rest') ⊢
      wpt (procCtx rs) (some p) (dlLsT ns) emptyProcSpecT (dlCost rest'.length)
        (dlPost ns) (dlBody loc ann ra mo bbty nbty ubty)
        (dlFrame (ptrVal pCur) f :: renv) := by
  rw [show dlBody loc ann ra mo bbty nbty ubty =
    Expr [] (Esseq (symPat [] dlBSym bbty) dlMemopE
      (Expr [] (Eif (Pexpr [] () (PEsym dlBSym)) dlExit
        (dlElse loc ann ra mo nbty ubty)))) from rfl]
  iintro ⟨HD, HC⟩
  cases rest' with
  | nil =>
    rw [isList_nil]
    icases HC with %hnull
    subst hnull
    rw [show dlCost ([] : List (Int × Int)).length = 3 + (1 + 1) from rfl]
    iapply wpt_seq_sym
    rw [show dlMemopE = memopRedex PtrEq
      [Pexpr [] () (PEsym dlCurSym), Pexpr [] () (PEval nullVal)] from rfl,
      show (3 : Nat) = 2 + 1 from rfl]
    iapply wpt_memop_eval PtrEq _ _ _
      dl_memop_operands_nonvalue (dl_cur_eval hf renv _) rfl
    rw [show memopRedex PtrEq [Pexpr [] () (PEval (ptrVal nullNode)),
        Pexpr [] () (PEval nullVal)] =
      memopPtrEqVals (Vobject (OVpointer nullNode))
        (Vobject (OVpointer nullNode)) from rfl]
    iapply wpt_memop_ptreq nullNode nullNode _ (by omega)
      (fun σ => eqPtrval_null_null nodeTy nodeTy σ)
    iexists (boolValue true)
    isplit
    · ipureintro
      rfl
    rw [bindSym_dl]
    iapply wpt_if_true [] (Pexpr [] () (PEsym dlBSym)) _ _ _
      (by rw [procCtx_extern, dl_guard_eval hf renv (boolValue true) _]; rfl)
    rw [show dlExit = ofVal (SpikeVal.pure Vunit) from rfl]
    iapply wpt_ofVal (SpikeVal.pure Vunit) _ (Nat.le_refl 1)
    isplit
    · ipureintro
      rfl
    rw [show ns = done by rw [hxs]; simp]
    iexact HD
  | cons nd vs =>
    rw [isList_cons]
    icases HC with ⟨%aN, %q, %bs, %hfacts, Hpt, HT⟩
    obtain ⟨rfl, h0, h1, hlen, hval, hnext⟩ := hfacts
    rw [show (nd :: vs).length = vs.length + 1 from rfl, dlCost_succ]
    iapply wpt_seq_sym
    rw [show dlMemopE = memopRedex PtrEq
      [Pexpr [] () (PEsym dlCurSym), Pexpr [] () (PEval nullVal)] from rfl,
      show (3 : Nat) = 2 + 1 from rfl]
    iapply wpt_memop_eval PtrEq _ _ _
      dl_memop_operands_nonvalue (dl_cur_eval hf renv _) rfl
    rw [show memopRedex PtrEq [Pexpr [] () (PEval (ptrVal (cellPtr nd.1 aN))),
        Pexpr [] () (PEval nullVal)] =
      memopPtrEqVals (Vobject (OVpointer (cellPtr nd.1 aN)))
        (Vobject (OVpointer nullNode)) from rfl]
    iapply wpt_memop_ptreq (cellPtr nd.1 aN) nullNode _ (by omega)
      (fun σ => eqPtrval_cell_null nd.1 aN nodeTy σ)
    iexists (boolValue false)
    isplit
    · ipureintro
      rfl
    rw [bindSym_dl]
    rw [show 1 + (4 + (3 + (1 + dlCost vs.length))) =
      (4 + (3 + (1 + dlCost vs.length))) + 1 by omega]
    iapply wpt_if_false [] (Pexpr [] () (PEsym dlBSym)) _ _ _
      (by rw [procCtx_extern, dl_guard_eval hf renv (boolValue false) _]; rfl)
    rw [show dlElse loc ann ra mo nbty ubty =
      Expr [] (Esseq (specPat [] [] dlNSym nbty)
        (dlLoadE loc ann mo)
        (Expr [] (Esseq (Pattern [] (CaseBase (none, ubty)))
          (dlKillE loc ann)
          (Expr [] (Erun ra dlLoopSym [Pexpr [] () (PEsym dlNSym)])))))
      from rfl]
    iapply wpt_seq_spec
    rw [show dlLoadE loc ann mo =
      loadOpRedex loc ann nodePtrTy (lrShiftPe dlCurSym) mo from rfl,
      show (4 : Nat) = 3 + 1 from rfl]
    iapply wpt_load_eval loc ann nodePtrTy (lrShiftPe dlCurSym) mo _
      rfl (dl_shift_eval_B hf renv _ nd.1 aN)
    rw [show cellPtr nd.1 (aN + 8) = cellPtr nd.1 (aN + ((8 : Nat) : Int))
      from rfl]
    iapply wpt_load_node_field (M := procCtx rs) (p := some p) (Θ := emptyProcSpecT) loc ann nd.1 aN 8 mo (.own 1) bs _
      (by omega)
      (by rw [nodeTy_size]; omega)
      (fun lum fpm => hnext lum fpm _)
    isplitl [Hpt]
    · iexact Hpt
    iintro %fp Hpt
    iexists (OVpointer q)
    isplit
    · ipureintro
      show (valueFromMemValue (.MVpointer nodeTy q)).2 = _
      rw [valueFromMemValue_ptr]
    rw [update_env_spec]
    rw [show envAdd dlNSym (Vobject (OVpointer q))
        (dlFrameB (boolValue false) (ptrVal (cellPtr nd.1 aN)) f) =
      dlFrameN (ptrVal q) (boolValue false) (ptrVal (cellPtr nd.1 aN)) f from rfl]
    iapply wpt_seq
    rw [show dlKillE loc ann = killOpRedex loc ann (Static0 nodeTy)
      (Pexpr [] () (PEsym dlCurSym)) from rfl,
      show (3 : Nat) = 2 + 1 from rfl]
    iapply wpt_kill_eval loc ann (Static0 nodeTy) _ _ rfl (pv := cellPtr nd.1 aN)
      (by rw [procCtx_extern]; exact dl_kill_operand_eval hf renv _ _ _)
    iapply wpt_kill loc ann (Static0 nodeTy) (cellPtr nd.1 aN) nodeTy bs _
      (Nat.le_refl 2) rfl
    isplitl [Hpt]
    · iapply (pointsToCell_cellOwn_iff _ _ _ _ _).mpr
      iexists nd.1, aN
      isplit
      · ipureintro
        rfl
      · iexact Hpt
    iintro ⟨%id, %a, %hpv, Hd⟩
    obtain ⟨hid, ha⟩ := cellPtr_inj hpv
    subst hid
    subst ha
    iapply wpt_run [] ra dlLoopSym [Pexpr [] () (PEsym dlNSym)] _ _
      (dlCost vs.length)
      (by rw [procCtx_labels hQ]
          exact dlQ_lookup loc ann ra mo cbty bbty nbty ubty)
      (dl_args_eval hf renv _ _ _)
      (by omega)
    iexists (done ++ [nd]), vs, q,
      (dlFrameN (ptrVal q) (boolValue false) (ptrVal (cellPtr nd.1 aN)) f), renv
    isplit
    · ipureintro
      refine ⟨rfl, ?_, rfl, rfl, dlFrameN_symFrame hf _ _ _⟩
      rw [hxs]
      simp
    isplitl [HD Hd]
    · iapply (deadNodes_append done [nd]).2
      isplitl [HD]
      · iexact HD
      · rw [deadNodes_cons, deadNodes_nil]
        isplitl [Hd]
        · iexists aN
          iexact Hd
        · itrivial
    · iexact HT

/-- The body at the FRAMED label context (what the production statement
    instantiates). -/
theorem dl_body_wpt_frame (RF : IProp GF) (done rest' : List (Int × Int))
    (pCur : CerbMem.PointerValue) (f : Fmap sym value)
    (renv : List (Fmap sym value)) (hf : SymFrame f)
    (hxs : ns = done ++ rest') :
    iprop((deadNodes (GF := GF) done ∗ isList pCur rest') ∗ RF) ⊢
      wpt (procCtx rs) (some p) (frameLsT RF (dlLsT ns)) emptyProcSpecT (dlCost rest'.length)
        (fun w ρ' => iprop(dlPost ns w ρ' ∗ RF)) (dlBody loc ann ra mo bbty nbty ubty)
        (dlFrame (ptrVal pCur) f :: renv) :=
  (BI.sep_mono ((dl_body_wpt loc ann ra mo cbty bbty nbty ubty ns p rs hQ
      done rest' pCur f renv hf hxs).trans (wpt_frame_labels RF _ _ _)) .rfl).trans
    BI.wand_elim_left

/-- THE TOTAL BLOCK SPECIFICATION for the dispose loop. -/
theorem dl_blockSpecsT :
    ⊢ blockSpecsT (GF := GF) (procCtx rs) (some p) (dlLsT ns) emptyProcSpecT (dlPost ns) := by
  refine blockSpecsT_intro fun l params cont args env0 envs m hl => ?_
  rw [procCtx_labels hQ] at hl
  obtain ⟨rfl, rfl⟩ := dlQ_inv loc ann ra mo cbty bbty nbty ubty hl
  iintro ⟨%done, %rest', %pCur, %f, %renv, %hpure, HD, HC⟩
  obtain ⟨rfl, hxs, rfl, hρ, hf⟩ := hpure
  obtain ⟨rfl, rfl⟩ : f = env0 ∧ renv = envs := by
    have h1 := congrArg (fun l => l.head?) hρ
    have h2 := congrArg (fun l => l.tail) hρ
    simp at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  rw [bindArgs_dl]
  iapply dl_body_wpt loc ann ra mo cbty bbty nbty ubty ns p rs hQ
    done rest' pCur f renv hf hxs
  isplitl [HD]
  · iexact HD
  · iexact HC

/-- DISPOSE A LIST, the total judgment at budget `dlCost |ns| + 1`:
    `{isList head ns} dispose(head) {ret unit. deadNodes ns}` with
    termination. -/
theorem dl_wpt (sbty : core_base_type) (head : CerbMem.PointerValue) :
    isList (GF := GF) head ns ⊢
      wpt (procCtx rs) (some p) (dlLsT ns) emptyProcSpecT (dlCost ns.length + 1) (dlPost ns)
        (dlProg loc ann ra mo sbty cbty bbty nbty ubty head) [fmapEmpty] := by
  rw [show dlProg loc ann ra mo sbty cbty bbty nbty ubty head =
    Expr [] (Esave (dlLoopSym, sbty) (dlParams cbty head)
      (dlBody loc ann ra mo bbty nbty ubty)) from rfl]
  iintro HL
  iapply wpt_save_vals [] (dlLoopSym, sbty) _ _ fmapEmpty [] (cvals := [ptrVal head]) rfl
  rw [bindSave_dl]
  iapply dl_body_wpt loc ann ra mo cbty bbty nbty ubty ns p rs hQ [] ns
    head fmapEmpty [] symFrame_empty (by simp)
  isplitr [HL]
  · rw [deadNodes_nil]
    itrivial
  · iexact HL

/-- The total block specifications at the framed label context. -/
theorem dl_blockSpecsT_frame (RF : IProp GF) :
    ⊢ blockSpecsT (GF := GF) (procCtx rs) (some p) (frameLsT RF (dlLsT ns)) emptyProcSpecT
      (fun w ρ' => iprop(dlPost ns w ρ' ∗ RF)) :=
  (dl_blockSpecsT loc ann ra mo cbty bbty nbty ubty ns p rs hQ).trans
    (blockSpecsT_frame RF)

/-- The framed total judgment: the frame rides through every back edge,
    the budget is untouched. -/
theorem dl_wpt_frame (RF : IProp GF) (sbty : core_base_type)
    (head : CerbMem.PointerValue) :
    iprop(isList (GF := GF) head ns ∗ RF) ⊢
      wpt (procCtx rs) (some p) (frameLsT RF (dlLsT ns)) emptyProcSpecT (dlCost ns.length + 1)
        (fun w ρ' => iprop(dlPost ns w ρ' ∗ RF))
        (dlProg loc ann ra mo sbty cbty bbty nbty ubty head) [fmapEmpty] := by
  iintro ⟨HL, HF⟩
  ihave HW := dl_wpt loc ann ra mo cbty bbty nbty ubty ns p rs hQ sbty head $$ HL
  iapply wpt_frame_labels RF _ _ _ $$ HW HF

end DlTotal

/-! ## THE READOUT: the dead list reads out as engine table facts -/

section DlReadout

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]

/-- The engine-facing dead fact of one id: in `deadAllocations`, record
    erased (`killM`, CerbMem.lean:1576-1578). -/
def DeadAt (σ : Mem) (id : Int) : Prop :=
  σ.deadAllocations.contains id = true ∧ σ.allocations.get? id = none

/-- A pure consequence is kept alongside its source (pure facts are
    persistent; `IProp` is affine). -/
theorem keep_pure {P : IProp GF} {φ : Prop} (h : P ⊢ (⌜φ⌝ : IProp GF)) :
    P ⊢ iprop(⌜φ⌝ ∗ P) :=
  (BI.and_intro h .rfl).trans BI.persistent_and_sep.1

/-- One dead cell's readout, the metadata interpretation returned. -/
theorem deadObj_dead_keep {σ : Mem} {mm : SpikeHeapF MetaCell}
    {mb : SpikeHeapF CerbMem.AbsByte} {mk : SpikeHeapF AllocCursor}
    (hG : CohG σ mm mb mk) (id a : Int) (ty : ctype) :
    iprop(metaInterp (GF := GF) mm ∗ deadObj fmapEmpty id a ty) ⊢
      iprop(⌜DeadAt σ id⌝ ∗ metaInterp mm) :=
  (keep_pure (deadObj_dead fmapEmpty hG id a ty)).trans
    (BI.sep_mono_right BI.sep_elim_left)

/-- Every node of the dead list is dead in the real state. -/
theorem deadNodes_dead {σ : Mem} {mm : SpikeHeapF MetaCell}
    {mb : SpikeHeapF CerbMem.AbsByte} {mk : SpikeHeapF AllocCursor}
    (hG : CohG σ mm mb mk) :
    ∀ ns : List (Int × Int),
    iprop(metaInterp (GF := GF) mm ∗ deadNodes ns) ⊢
      iprop(⌜∀ nd ∈ ns, DeadAt σ nd.1⌝ ∗ metaInterp mm)
  | [] => by
    rw [deadNodes_nil]
    iintro ⟨Hmi, -⟩
    isplitr [Hmi]
    · ipureintro
      intro _ h
      nomatch h
    · iexact Hmi
  | nd :: ns => by
    rw [deadNodes_cons]
    iintro ⟨Hmi, ⟨%a, Hd⟩, Hrest⟩
    ihave H1 : iprop(⌜DeadAt σ nd.1⌝ ∗ metaInterp (GF := GF) mm) $$ [Hmi Hd]
    · iapply deadObj_dead_keep hG nd.1 a nodeTy
      isplitl [Hmi]
      · iexact Hmi
      · iexact Hd
    icases H1 with ⟨%h1, Hmi⟩
    ihave H2 : iprop(⌜∀ x ∈ ns, DeadAt σ x.1⌝ ∗ metaInterp (GF := GF) mm) $$ [Hmi Hrest]
    · iapply deadNodes_dead hG ns
      isplitl [Hmi]
      · iexact Hmi
      · iexact Hrest
    icases H2 with ⟨%h2, Hmi⟩
    isplitr [Hmi]
    · ipureintro
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h1
      · exact h2 x hx
    · iexact Hmi

end DlReadout

section DlReadoutLC

variable {GF : BundledGFunctors} [SpikeGS .hasLC GF]

/-- THE READOUT (through the one sanctioned combinator
    `stateInterp_readout`): the dispose postcondition with a cell-map
    frame entails the engine-facing conclusion — unit delivered, every
    node id dead with its record erased, the frame's cells intact. -/
theorem dlPost_readout (ns : List (Int × Int)) (R : CellMap) :
    ∀ (w : SpikeVal) (ρ' : EnvStack),
    iprop(dlPost (hlc := .hasLC) (GF := GF) ns w ρ' ∗ lrCellFrame R) ⊢
      readoutPost (fun v σ' => v = Vunit ∧ (∀ nd ∈ ns, DeadAt σ' nd.1) ∧
        Coh fmapEmpty σ' R) w ρ' := by
  intro w ρ'
  have haux : iprop(deadNodes (hlc := .hasLC) (GF := GF) ns ∗ lrCellFrame R) ⊢
      readoutPost (GF := GF) (fun v σ' => v = Vunit ∧ (∀ nd ∈ ns, DeadAt σ' nd.1) ∧
        Coh fmapEmpty σ' R) (SpikeVal.pure Vunit) ρ' :=
    stateInterp_readout (Φ := iprop(deadNodes ns ∗ lrCellFrame R))
      (ψ := fun σ' => Vunit = Vunit ∧ (∀ nd ∈ ns, DeadAt σ' nd.1) ∧ Coh fmapEmpty σ' R)
      (fun σ mm mb mk hG => by
        iintro ⟨⟨HD, HF⟩, Hmi, Hbi⟩
        ihave H1 : iprop(⌜∀ nd ∈ ns, DeadAt σ nd.1⌝ ∗ metaInterp (GF := GF) mm) $$ [Hmi HD]
        · iapply deadNodes_dead hG ns
          isplitl [Hmi]
          · iexact Hmi
          · iexact HD
        icases H1 with ⟨%hdead, Hmi⟩
        ihave %hcoh : ⌜Coh fmapEmpty σ R⌝ $$ [HF Hmi Hbi]
        · iapply cellsOwn_consequence (hG := hG) fmapEmpty R
          isplitl [HF]
          · iexact HF
          isplitl [Hmi]
          · iexact Hmi
          · iexact Hbi
        ipureintro
        exact ⟨rfl, hdead, hcoh⟩)
  iintro ⟨⟨%hw, HD⟩, HF⟩
  subst hw
  ihave H : readoutPost (GF := GF) (fun v σ' => v = Vunit ∧ (∀ nd ∈ ns, DeadAt σ' nd.1) ∧
      Coh fmapEmpty σ' R) (SpikeVal.pure Vunit) ρ' $$ [HD HF]
  · iapply haux
    isplitl [HD]
    · iexact HD
    · iexact HF
  iexact H

end DlReadoutLC

/-! ## THE ENGINE-FACING STATEMENT (the `driveU` lane — PROVISIONAL, as
every `driveU` export: API.lean header) -/

section DlExport

open Iris.Std.PartialMap

variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (mo : memory_order) (cbty bbty nbty ubty : core_base_type)

/-- DISPOSE A LIST, THE UNCONDITIONAL TOTAL ENGINE EQUATION: from any
    memory satisfying the seeded chain `m₀` next to an ARBITRARY disjoint
    frame footprint `R`, the engine's `driveU` at the DERIVED bound
    `12·|ns| + 6` DELIVERS `Vunit`, EVERY node id of the chain is in
    `deadAllocations` with its record erased (`killM`'s effect,
    CerbMem.lean:1576-1578), and the frame `R` is returned VERBATIM
    (`Sat σ' R`). A corollary of the total judgment through the generic
    simulation (`wpt_engine_boundU`): zero Step constructors. PROVISIONAL:
    stated over `driveU`. -/
theorem dispose_list_certified_total (sbty : core_base_type)
    (ns : List (Int × Int)) (head : CerbMem.PointerValue)
    (m₀ : CellMap) (hseed : SeedChain m₀ head ns)
    (R : CellMap) (hR : m₀ ##ₘ R)
    (σ₀ : Mem) (hcoh : Sat fmapEmpty σ₀ (Iris.Std.PartialMap.union m₀ R))
    (aids : Nat → Nat) :
    ∃ σ' : Mem,
      driveU (procCtx (dlRS loc ann ra mo cbty bbty nbty ubty)) aids
        (12 * ns.length + 6)
        (procThread dlProcSym
          (dlProg loc ann ra mo sbty cbty bbty nbty ubty head) [fmapEmpty]) σ₀ =
        .done Vunit σ' ∧
      (∀ nd ∈ ns, σ'.deadAllocations.contains nd.1 = true ∧
        σ'.allocations.get? nd.1 = none) ∧
      Sat fmapEmpty σ' R := by
  have hQ := dlRS_labeledAt loc ann ra mo cbty bbty nbty ubty
  have hk : dlCost ns.length + 1 = 12 * ns.length + 6 := by
    unfold dlCost
    omega
  rw [← hk]
  have hlbl := procCtx_labels hQ
  obtain ⟨v, σ', hdone, ⟨rfl, hdead, hsat⟩, -⟩ :=
    wpt_engine_boundU (GF := SpikeGF)
      (M := procCtx (dlRS loc ann ra mo cbty bbty nbty ubty)) (ctl := procCtl dlProcSym)
      (procCtx_wf _) rfl
      (fun l params cont hl => by
        rw [hlbl] at hl
        obtain ⟨-, rfl⟩ := dlQ_inv loc ann ra mo cbty bbty nbty ubty hl
        exact dlBody_fragJ loc ann ra mo bbty nbty ubty)
      (fun l params cont hl => by
        rw [hlbl] at hl
        obtain ⟨-, rfl⟩ := dlQ_inv loc ann ra mo cbty bbty nbty ubty hl
        rw [dlBody_pot, show lemDefaultFuel = 999999 + 1 from rfl]
        omega)
      (frameLsT (lrCellFrame R) (dlLsT ns))
      (dlProg loc ann ra mo sbty cbty bbty nbty ubty head)
      fmapEmpty [] σ₀ (Iris.Std.PartialMap.union m₀ R)
      (.save (saveParams_pure_of_vals rfl) (saveParams_depth_of_vals rfl)
        (dlBody_fragJ loc ann ra mo bbty nbty ubty))
      (by rw [dlProg_pot, show lemDefaultFuel = 999999 + 1 from rfl]; omega)
      hcoh
      (fun v σ' => v = Vunit ∧ (∀ nd ∈ ns, DeadAt σ' nd.1) ∧ Coh fmapEmpty σ' R)
      (dlCost ns.length + 1)
      (by
        intro inst
        refine ((BigSepM.bigSepM_union hR).1.trans
          (BI.sep_mono (seedChain_isList ns m₀ head hseed) .rfl)).trans ?_
        refine .trans BI.emp_sep.2 (BI.sep_mono ?_ ?_)
        · exact (dl_blockSpecsT_frame loc ann ra mo cbty bbty nbty ubty ns
            dlProcSym (dlRS loc ann ra mo cbty bbty nbty ubty) hQ
            (lrCellFrame R)).trans
            (blockSpecsT_mono (dlPost_readout ns R))
        · exact (dl_wpt_frame loc ann ra mo cbty bbty nbty ubty ns
              dlProcSym (dlRS loc ann ra mo cbty bbty nbty ubty) hQ
              (lrCellFrame R) sbty head).trans
              (wpt_mono (dlPost_readout ns R) _ _ _))
      aids
  exact ⟨σ', hdone, hdead, hsat⟩

end DlExport

/-! ## PRODUCTION: build a two-node list with `create`s, then dispose it

The build prefix is the list-reverse production's `lrProdPrefix` VERBATIM
(two creates, four field stores through the bound pointers); its proof is
restated here GENERICALLY in the continuation (`lrProdPrefix_wpt`: any
continuation verified from the built chain `isList n1 [(i₁,1),(i₂,2)]`
plus a pass-through resource `RF`), so that the dispose loop — and any
future consumer of a built list — enters through its `save`. -/

/-- The dispose loop's save parameter with its LIVE initializer:
    `cur := n1` (the program-bound head). -/
def dlProdParams (cbty : core_base_type) :
    List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)) :=
  [(dlCurSym, ((cbty, none), Pexpr [] () (PEsym lrN1Sym)))]

/-- The self-contained production dispose program: the build prefix
    continued by the dispose loop's `save`, entered with the live head. -/
def dlProdProg (ra : core_run_annotation) (mo : memory_order)
    (bty sbty cbty bbty nbty ubty : core_base_type) : CoreExpr :=
  lrProdPrefix ra mo bty
    (Expr [] (Esave (dlLoopSym, sbty) (dlProdParams cbty)
      (dlBody loc0 empty_annotation ra mo bbty nbty ubty)))

section DlProdEval

variable {f : Fmap sym value} (hf : SymFrame f) (v1 v2 : value)
  (rest : List (Fmap sym value))

include hf

/-- The save's initializer evaluates at the entry env to the
    program-bound head pointer. -/
theorem lrPFrame_save_params_dl (cbty : core_base_type) :
    evalPexprs fmapEmpty fmapEmpty (lrPFrame v1 v2 f :: rest)
        (saveParamPexprs (dlProdParams cbty)) = some [v1] := by
  show evalPexprs fmapEmpty fmapEmpty (lrPFrame v1 v2 f :: rest)
    [Pexpr [] () (PEsym lrN1Sym)] = _
  rw [evalPexprs_cons]
  rw [show evalPexpr fmapEmpty fmapEmpty (lrPFrame v1 v2 f :: rest)
      (Pexpr [] () (PEsym lrN1Sym)) = some v1 from by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (lrPFrame_lookup_n1 hf _ _) rest]
  rfl

end DlProdEval

theorem bindSaveParams_dlProd (cbty : core_base_type) (v1 : value)
    (f : Fmap sym value) (rest : List (Fmap sym value)) :
    bindSaveParams (dlProdParams cbty) [v1] (f :: rest) = dlFrame v1 f :: rest := by
  show update_env (mk_sym_pat dlCurSym cbty) v1 (f :: rest) = _
  rw [update_env_cons, update_env_aux_sym]
  rfl

theorem dlProdParams_depth (cbty : core_base_type) :
    ∀ pe ∈ saveParamPexprs (dlProdParams cbty), peDepth pe ≤ lemDefaultFuel := by
  intro pe hpe
  simp only [dlProdParams, saveParamPexprs, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hpe
  subst hpe
  exact peDepth_sym_le _ _

/-! ### Distinctness of the built nodes (read off the list predicate) -/

/-- A two-node seeded chain has two DISTINCT allocation ids (the cell
    maps are disjoint). -/
theorem seedChain_two_ne {m : SpikeHeapF SpikeCell} {p : CerbMem.PointerValue}
    {i₁ v₁ i₂ v₂ : Int} (hseed : SeedChain m p [(i₁, v₁), (i₂, v₂)]) : i₁ ≠ i₂ := by
  obtain ⟨aN, q, bs, m', -, -, -, -, -, -, hdisj, -, hseed'⟩ := hseed
  obtain ⟨aN₂, q₂, bs₂, m'', -, -, -, -, -, -, -, rfl, -⟩ := hseed'
  intro heq
  subst heq
  rcases (Iris.Std.PartialMap.disjoint_iff _ _).mp hdisj i₁ with h | h
  · rw [Iris.Std.LawfulPartialMap.get?_singleton_eq rfl] at h
    cases h
  · rw [get?_union', Iris.Std.LawfulPartialMap.get?_singleton_eq rfl] at h
    cases h

section DlProdIris

variable {GF : BundledGFunctors} [SpikeGS .hasLC GF]

/-- Two-node list: its ids are distinct (non-destructively, through
    `isList_to_cells`/`seedChain_isList`). -/
theorem isList_two_ne (p : CerbMem.PointerValue) (i₁ v₁ i₂ v₂ : Int) :
    isList (hlc := .hasLC) (GF := GF) p [(i₁, v₁), (i₂, v₂)] ⊢
      iprop(⌜i₁ ≠ i₂⌝ ∗ isList p [(i₁, v₁), (i₂, v₂)]) := by
  iintro HL
  ihave HC := isList_to_cells [(i₁, v₁), (i₂, v₂)] p $$ HL
  icases HC with ⟨%m, %hseed, Hm⟩
  isplitr [Hm]
  · ipureintro
    exact seedChain_two_ne hseed
  · iapply seedChain_isList _ m p hseed $$ Hm

variable (ra : core_run_annotation) (mo : memory_order)
  (p : sym) (rs : core_run_state)

/-- THE BUILD PREFIX, GENERIC IN ITS CONTINUATION: from the two-node
    budget (∗ any pass-through `RF`), the two creates (PUBLIC
    `wpt_create`; the bounds export feeds the node WF) and the four field
    stores (the generic typed-subrange rules at the bound pointers) build
    `isList n1 [(i₁,1),(i₂,2)]` at ENGINE-PICKED ids and hand it, with
    `RF`, to any continuation `k` verified at the prefix frame; the
    prefix costs 20 (2 + 2 + 4·4). The list-reverse production's
    `lrProd_wpt` is this derivation at its own continuation. -/
theorem lrProdPrefix_wpt {Ls : LabelSpecT GF} (bty : core_base_type)
    (k : CoreExpr) (kk : Nat) (ψ : value → Mem → Prop) (RF : IProp GF)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (hf : SymFrame ev0)
    (hk : ∀ (i₁ a₁ i₂ a₂ : Int), 0 < a₁ ∧ a₁ < 2 ^ 64 → 0 < a₂ ∧ a₂ < 2 ^ 64 →
      iprop(isList (hlc := .hasLC) (GF := GF) (cellPtr i₁ a₁)
          [((i₁ : Int), (1 : Int)), (i₂, 2)] ∗ RF) ⊢
        wpt (procCtx rs) (some p) Ls emptyProcSpecT kk (readoutPost ψ) k
          (lrPFrame (ptrVal (cellPtr i₁ a₁)) (ptrVal (cellPtr i₂ a₂)) ev0 :: evs)) :
    iprop(allocBudget (GF := GF)
        (allocCost (procCtx rs).tagDefs nodeTy 8 +
          allocCost (procCtx rs).tagDefs nodeTy 8) ∗ RF) ⊢
      wpt (procCtx rs) (some p) Ls emptyProcSpecT
        (2 + (2 + ((3 + 1) + ((3 + 1) + ((3 + 1) + ((3 + 1) + kk))))))
        (readoutPost ψ) (lrProdPrefix ra mo bty k) (ev0 :: evs) := by
  iintro ⟨Hcap, HF⟩
  rw [show lrProdPrefix ra mo bty k =
    Expr [] (Esseq (symPat [] lrN1Sym bty)
      (createExpr loc0 empty_annotation (.IV .Prov_none 8) nodeTy
        (PrefOther "lr-n1"))
      (Expr [] (Esseq (symPat [] lrN2Sym bty)
        (createExpr loc0 empty_annotation (.IV .Prov_none 8) nodeTy
          (PrefOther "lr-n2"))
        (Expr [] (Esseq (Pattern [] (CaseBase (none, bty)))
          (storeOpRedex loc0 empty_annotation longTy
            (Pexpr [] () (PEsym lrN1Sym)) (Pexpr [] () (PEval (longVal 1))) mo)
          (Expr [] (Esseq (Pattern [] (CaseBase (none, bty)))
            (storeOpRedex loc0 empty_annotation nodePtrTy
              (lrShiftPe lrN1Sym) (Pexpr [] () (PEsym lrN2Sym)) mo)
            (Expr [] (Esseq (Pattern [] (CaseBase (none, bty)))
              (storeOpRedex loc0 empty_annotation longTy
                (Pexpr [] () (PEsym lrN2Sym)) (Pexpr [] () (PEval (longVal 2))) mo)
              (Expr [] (Esseq (Pattern [] (CaseBase (none, bty)))
                (storeOpRedex loc0 empty_annotation nodePtrTy
                  (lrShiftPe lrN2Sym) (Pexpr [] () (PEval nullVal)) mo)
                k))))))))))) from rfl]
  iapply wpt_seq_sym
  icases (allocBudget_split _ _).1 $$ Hcap with ⟨Hcap, Hcap₂⟩
  iapply wpt_create loc0 empty_annotation .Prov_none 8 nodeTy
    (PrefOther "lr-n1") (ev0 :: evs) (Nat.le_refl 2)
    nodeTy_size_pos nodeTy_nonatomic nodeTy_decIndep_undef
  isplitl [Hcap]
  · iexact Hcap
  iintro %p₁ ⟨Hpt₁, %hb₁⟩
  iexists (Vobject (OVpointer p₁))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym lrN1Sym bty]
  iapply wpt_seq_sym
  iapply wpt_create loc0 empty_annotation .Prov_none 8 nodeTy
    (PrefOther "lr-n2") _ (Nat.le_refl 2)
    nodeTy_size_pos nodeTy_nonatomic nodeTy_decIndep_undef
  isplitl [Hcap₂]
  · iexact Hcap₂
  iintro %p₂ ⟨Hpt₂, %hb₂⟩
  iexists (Vobject (OVpointer p₂))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym lrN2Sym bty]
  rw [show envAdd lrN2Sym (Vobject (OVpointer p₂))
      (envAdd lrN1Sym (Vobject (OVpointer p₁)) ev0) =
    lrPFrame (ptrVal p₁) (ptrVal p₂) ev0 from rfl]
  icases (pointsToCell_cellOwn_iff (procCtx rs).tagDefs _ _ _ _).mp $$ Hpt₁
    with ⟨%i₁, %a₁, %hpv₁, Hcell₁⟩
  icases (pointsToCell_cellOwn_iff (procCtx rs).tagDefs _ _ _ _).mp $$ Hpt₂
    with ⟨%i₂, %a₂, %hpv₂, Hcell₂⟩
  subst hpv₁
  subst hpv₂
  rw [addrOf_cellPtr] at hb₁ hb₂
  -- store 1: node 1's value field
  iapply wpt_seq
  iapply wpt_store_eval loc0 empty_annotation longTy _ _ mo _ rfl
    (pv := cellPtr i₁ a₁) (cv := longVal 1)
    (by rw [procCtx_extern, evalPexpr_sym_empty]
        exact lookup_env_head (lrPFrame_lookup_n1 hf _ _) evs)
    rfl
  rw [show (storeExpr loc0 empty_annotation longTy (cellPtr i₁ a₁)
      (longVal 1) mo : CoreExpr) =
    storeExpr loc0 empty_annotation longTy
      (cellPtr i₁ (a₁ + ((0 : Nat) : Int))) (longVal 1) mo from by
    rw [show a₁ + ((0 : Nat) : Int) = a₁ from by omega]]
  iapply wpt_store_cell_at (mv := longMval 1) loc0 empty_annotation i₁
    a₁ nodeTy 0 longTy (longVal 1) mo nodeUndefBytes _ (Nat.le_refl 3) rfl
    (by rw [show CerbMem.sizeofCtype (procCtx rs).tagDefs longTy = 8 from rfl,
      show CerbMem.sizeofCtype (procCtx rs).tagDefs nodeTy = 16 from rfl]; omega)
    ⟨rfl, fun _ => rfl, fun _ => rfl, rfl⟩
    (fun lum fpm => nodeTy_dec_indep lum fpm a₁ _)
  isplitl [Hcell₁]
  · iexact Hcell₁
  iintro %fp1 Hcell₁
  -- store 2: node 1's next field := node 2
  iapply wpt_seq
  iapply wpt_store_eval loc0 empty_annotation nodePtrTy _ _ mo _ rfl
    (pv := cellPtr i₁ (a₁ + 8)) (cv := ptrVal (cellPtr i₂ a₂))
    (by rw [procCtx_extern]
        exact lrPFrame_shift_n1 hf (ptrVal (cellPtr i₂ a₂)) evs i₁ a₁)
    (by rw [procCtx_extern, evalPexpr_sym_empty]
        exact lookup_env_head (lrPFrame_lookup_n2 hf _ _) evs)
  rw [show (cellPtr i₁ (a₁ + 8)) = cellPtr i₁ (a₁ + ((8 : Nat) : Int))
    from rfl]
  iapply wpt_store_node_field loc0 empty_annotation i₁ a₁ 8
    (ptrVal (cellPtr i₂ a₂)) mo _ _ (Nat.le_refl 3)
    (node_ptr_encodes (cellPtr i₂ a₂))
    (by rw [show CerbMem.sizeofCtype (procCtx rs).tagDefs nodeTy = 16 from rfl]; omega)
    (by rw [node_ptr_img_cell]; exact ptrImg_cell_length i₂ a₂)
    (node_ptr_compat (cellPtr i₂ a₂)) (node_ptr_fpm_cell i₂ a₂)
    (node_ptr_bytes_cell i₂ a₂)
  isplitl [Hcell₁]
  · iexact Hcell₁
  iintro %fp2 Hcell₁
  -- store 3: node 2's value field
  iapply wpt_seq
  iapply wpt_store_eval loc0 empty_annotation longTy _ _ mo _ rfl
    (pv := cellPtr i₂ a₂) (cv := longVal 2)
    (by rw [procCtx_extern, evalPexpr_sym_empty]
        exact lookup_env_head (lrPFrame_lookup_n2 hf _ _) evs)
    rfl
  rw [show (storeExpr loc0 empty_annotation longTy (cellPtr i₂ a₂)
      (longVal 2) mo : CoreExpr) =
    storeExpr loc0 empty_annotation longTy
      (cellPtr i₂ (a₂ + ((0 : Nat) : Int))) (longVal 2) mo from by
    rw [show a₂ + ((0 : Nat) : Int) = a₂ from by omega]]
  iapply wpt_store_cell_at (mv := longMval 2) loc0 empty_annotation i₂
    a₂ nodeTy 0 longTy (longVal 2) mo nodeUndefBytes _ (Nat.le_refl 3) rfl
    (by rw [show CerbMem.sizeofCtype (procCtx rs).tagDefs longTy = 8 from rfl,
      show CerbMem.sizeofCtype (procCtx rs).tagDefs nodeTy = 16 from rfl]; omega)
    ⟨rfl, fun _ => rfl, fun _ => rfl, rfl⟩
    (fun lum fpm => nodeTy_dec_indep lum fpm a₂ _)
  isplitl [Hcell₂]
  · iexact Hcell₂
  iintro %fp3 Hcell₂
  -- store 4: node 2's next field := NULL
  iapply wpt_seq
  iapply wpt_store_eval loc0 empty_annotation nodePtrTy _ _ mo _ rfl
    (pv := cellPtr i₂ (a₂ + 8)) (cv := nullVal)
    (by rw [procCtx_extern]
        exact lrPFrame_shift_n2 hf (ptrVal (cellPtr i₁ a₁)) evs i₂ a₂)
    rfl
  rw [show (cellPtr i₂ (a₂ + 8)) = cellPtr i₂ (a₂ + ((8 : Nat) : Int))
    from rfl]
  iapply wpt_store_node_field loc0 empty_annotation i₂ a₂ 8
    nullVal mo _ _ (Nat.le_refl 3)
    (node_ptr_encodes nullNode)
    (by rw [show CerbMem.sizeofCtype (procCtx rs).tagDefs nodeTy = 16 from rfl]; omega)
    (by rw [node_ptr_img_null]; exact ptrImg_null_length)
    (node_ptr_compat nullNode) (fun _ => rfl) (fun _ => rfl)
  isplitl [Hcell₂]
  · iexact Hcell₂
  iintro %fp4 Hcell₂
  -- the continuation, the four stores' annotation residues absorbed
  iapply wpt_mono
    (fun w ρ' => ((readoutPost_annot_absorb ψ [DA_pos [] fp4] Vunit w ρ').trans
        (readoutPost_annot_absorb ψ [DA_pos [] fp3] Vunit _ ρ')).trans
       ((readoutPost_annot_absorb ψ [DA_pos [] fp2] Vunit _ ρ').trans
        (readoutPost_annot_absorb ψ [DA_pos [] fp1] Vunit _ ρ')))
    _ _ _
  iapply hk i₁ a₁ i₂ a₂ hb₁ hb₂
  isplitl [Hcell₁ Hcell₂]
  · -- isList (node 1) [(i₁,1),(i₂,2)]: the built chain, with the
    -- node-WF bounds from the PUBLIC create rule's export
    iapply isList_cons_intro i₁ a₁ (cellPtr i₂ a₂) (lrBuilt1 i₂ a₂) 1
      [(i₂, 2)] hb₁.1 hb₁.2 (lrBuilt1_len i₂ a₂) (lrBuilt1_valDec i₂ a₂)
      (lrBuilt1_nextDec i₂ a₂ hb₂.1 hb₂.2)
    isplitl [Hcell₁]
    · iexact Hcell₁
    iapply isList_cons_intro i₂ a₂ nullNode lrBuilt2 2 [] hb₂.1 hb₂.2
      lrBuilt2_len lrBuilt2_valDec lrBuilt2_nextDec
    isplitl [Hcell₂]
    · iexact Hcell₂
    · exact isList_nil_intro
  · iexact HF

/-- The engine-facing postcondition of the production dispose: unit,
    and two distinct allocation ids dead with their records erased (the
    proof's witnesses are the two nodes; the statement names none). -/
def ψD : value → Mem → Prop := fun v σ' =>
  v = Vunit ∧ ∃ i₁ i₂ : Int, i₁ ≠ i₂ ∧ DeadAt σ' i₁ ∧ DeadAt σ' i₂

/-- The production label spec: the GENERIC `dlLsT` at the two-node list
    `[(i₁,1),(i₂,2)]` with the ids existential and distinct, framed by the
    (empty) cell frame. -/
abbrev dlProdLsT : LabelSpecT GF := fun l m vs ρ =>
  iprop(∃ i₁ i₂ : Int, ⌜i₁ ≠ i₂⌝ ∗
    frameLsT (lrCellFrame (∅ : CellMap)) (dlLsT [((i₁ : Int), (1 : Int)), (i₂, 2)])
      l m vs ρ)

/-- The dispose postcondition at the two-node list reads out as `ψD`. -/
theorem dlProd_readout (i₁ i₂ : Int) (hne : i₁ ≠ i₂) (w : SpikeVal) (ρ' : EnvStack) :
    iprop(dlPost (hlc := .hasLC) (GF := GF) [((i₁ : Int), (1 : Int)), (i₂, 2)] w ρ' ∗
        lrCellFrame (∅ : CellMap)) ⊢
      readoutPost ψD w ρ' :=
  (dlPost_readout [((i₁ : Int), (1 : Int)), (i₂, 2)] (∅ : CellMap) w ρ').trans
    (readoutPost_mono (fun v σ' hv => ⟨hv.1, i₁, i₂, hne,
      hv.2.1 (i₁, 1) (by simp), hv.2.1 (i₂, 2) (by simp)⟩) w ρ')

variable (cbty bbty nbty ubty : core_base_type)
  (hQ : LabeledAt rs p (dlQ loc0 empty_annotation ra mo cbty bbty nbty ubty))

include hQ

/-- THE TOTAL BLOCK SPECIFICATION for the production dispose loop: the
    generic body theorem consumed verbatim at the unpacked ids. -/
theorem dlProd_blockSpecsT :
    ⊢ blockSpecsT (GF := GF) (procCtx rs) (some p) dlProdLsT emptyProcSpecT (readoutPost ψD) := by
  refine blockSpecsT_intro fun l params cont vs ev0 evs m hl => ?_
  rw [procCtx_labels hQ] at hl
  obtain ⟨rfl, rfl⟩ := dlQ_inv loc0 empty_annotation ra mo cbty bbty nbty ubty hl
  iintro ⟨%i₁, %i₂, %hne, HL⟩
  icases HL with ⟨⟨%done, %rest', %pCur, %f, %renv, %hpure, HD, HC⟩, HF⟩
  obtain ⟨rfl, hxs, rfl, hρ, hf⟩ := hpure
  obtain ⟨rfl, rfl⟩ : f = ev0 ∧ renv = evs := by
    have h1 := congrArg (fun l => l.head?) hρ
    have h2 := congrArg (fun l => l.tail) hρ
    simp at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  rw [bindArgs_dl]
  iapply wpt_mono (dlProd_readout i₁ i₂ hne) _ _ _
  iapply wpt_mono_Ls
    (Ls₁ := frameLsT (lrCellFrame (∅ : CellMap))
      (dlLsT [((i₁ : Int), (1 : Int)), (i₂, 2)]))
    (fun l' m' vs' ρ' => by
      iintro H
      iexists i₁, i₂
      isplit
      · ipureintro
        exact hne
      · iexact H)
    _ _ _
  iapply dl_body_wpt_frame loc0 empty_annotation ra mo cbty bbty nbty ubty
    [((i₁ : Int), (1 : Int)), (i₂, 2)] p rs hQ (lrCellFrame (∅ : CellMap))
    done rest' pCur f renv hf hxs
  isplitl [HD HC]
  · isplitl [HD]
    · iexact HD
    · iexact HC
  · iexact HF

/-- THE WHOLE PRODUCTION PROGRAM at the total judgment: the build prefix
    (generic lemma) continued by the dispose loop entered through its
    `save` with the live head. -/
theorem dlProd_wpt (bty sbty : core_base_type)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (hf : SymFrame ev0) :
    iprop(allocBudget (GF := GF)
        (allocCost (procCtx rs).tagDefs nodeTy 8 +
          allocCost (procCtx rs).tagDefs nodeTy 8)) ⊢
      wpt (procCtx rs) (some p) dlProdLsT emptyProcSpecT
        (2 + (2 + ((3 + 1) + ((3 + 1) + ((3 + 1) + ((3 + 1) +
          (dlCost 2 + saveEntryCost (dlProdParams cbty))))))))
        (readoutPost ψD)
        (dlProdProg ra mo bty sbty cbty bbty nbty ubty)
        (ev0 :: evs) := by
  iintro Hcap
  rw [show dlProdProg ra mo bty sbty cbty bbty nbty ubty =
    lrProdPrefix ra mo bty
      (Expr [] (Esave (dlLoopSym, sbty) (dlProdParams cbty)
        (dlBody loc0 empty_annotation ra mo bbty nbty ubty))) from rfl]
  iapply lrProdPrefix_wpt ra mo p rs bty _ _ ψD (BIBase.emp : IProp GF) ev0 evs hf
    (fun i₁ a₁ i₂ a₂ hb₁ hb₂ => by
      iintro ⟨HL, -⟩
      ihave HL2 := isList_two_ne (cellPtr i₁ a₁) i₁ 1 i₂ 2 $$ HL
      icases HL2 with ⟨%hne, HL⟩
      iapply wpt_save [] (dlLoopSym, sbty) (dlProdParams cbty) _ _ evs
        (cvals := [ptrVal (cellPtr i₁ a₁)])
        (by rw [procCtx_extern]
            exact lrPFrame_save_params_dl hf (ptrVal (cellPtr i₁ a₁))
              (ptrVal (cellPtr i₂ a₂)) evs cbty)
      rw [bindSaveParams_dlProd]
      iapply wpt_mono (dlProd_readout i₁ i₂ hne) _ _ _
      iapply wpt_mono_Ls
        (Ls₁ := frameLsT (lrCellFrame (∅ : CellMap))
          (dlLsT [((i₁ : Int), (1 : Int)), (i₂, 2)]))
        (fun l' m' vs' ρ' => by
          iintro H
          iexists i₁, i₂
          isplit
          · ipureintro
            exact hne
          · iexact H)
        _ _ _
      iapply dl_body_wpt_frame loc0 empty_annotation ra mo cbty bbty nbty ubty
        [((i₁ : Int), (1 : Int)), (i₂, 2)] p rs hQ (lrCellFrame (∅ : CellMap))
        ([] : List (Int × Int)) [((i₁ : Int), (1 : Int)), (i₂, 2)] (cellPtr i₁ a₁)
        (lrPFrame (ptrVal (cellPtr i₁ a₁)) (ptrVal (cellPtr i₂ a₂)) ev0)
        evs (lrPFrame_symFrame hf _ _) rfl
      isplitl [HL]
      · isplitr [HL]
        · rw [deadNodes_nil]
          itrivial
        · iexact HL
      · iapply (BigSepM.bigSepM_empty_intro
          (P := (BIBase.emp : IProp GF))
          (Φ := fun (i : Int) (c : SpikeCell) =>
            cellOwn (procCtx rs).tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c))
        itrivial)
  isplitl [Hcap]
  · iexact Hcap
  · itrivial

end DlProdIris

/-! ### Registration, cone membership, potentials -/

theorem dlProdProg_frag (ra : core_run_annotation) (mo : memory_order)
    (bty sbty cbty bbty nbty ubty : core_base_type) :
    Frag (dlProdProg ra mo bty sbty cbty bbty nbty ubty) :=
  lrProdPrefix_frag ra mo bty
    (.save (PePure.all_of_isPePure rfl) (dlProdParams_depth cbty)
      (dlBody_fragJ loc0 empty_annotation ra mo bbty nbty ubty))

theorem dlProdProg_pot (ra : core_run_annotation) (mo : memory_order)
    (bty sbty cbty bbty nbty ubty : core_base_type) :
    pot (dlProdProg ra mo bty sbty cbty bbty nbty ubty) = 13 := by
  unfold dlProdProg
  rw [lrProdPrefix_pot, pot_save, dlBody_pot]
  omega

/-- The dispose loop's save with the production initializer registers its
    body, at cushioned variable fuel (the `col_lrProdSave` twin). -/
theorem col_dlProdSave (m : Nat) (ra : core_run_annotation)
    (mo : memory_order) (sbty cbty bbty nbty ubty : core_base_type) :
    collect_saves_aux_lemFuel (m + 9) empty_saves
      (Expr [] (Esave (dlLoopSym, sbty) (dlProdParams cbty)
        (dlBody loc0 empty_annotation ra mo bbty nbty ubty))) =
      { tmp_acc := dlQ loc0 empty_annotation ra mo cbty bbty nbty ubty,
        closed_acc := fmapEmpty } := rfl

/-- The shipped registration computes the dispose loop's label map
    (the six prefix layers peeled one arm at a time, as `collect_new_lrProd`). -/
theorem collect_new_dlProd (ra : core_run_annotation) (mo : memory_order)
    (bty sbty cbty bbty nbty ubty : core_base_type) :
    collect_labeled_continuations_NEW
        (prodFile (dlProdProg ra mo bty sbty cbty bbty nbty ubty)) =
      fmapAddBy (fun (s1 s2 : sym) => ordCompare s1 s2) mainSym
        (dlQ loc0 empty_annotation ra mo cbty bbty nbty ubty)
        fmapEmpty := by
  rw [show collect_labeled_continuations_NEW
      (prodFile (dlProdProg ra mo bty sbty cbty bbty nbty ubty)) =
    fmapAddBy (fun (s1 s2 : sym) => ordCompare s1 s2) mainSym
      (collect_saves (dlProdProg ra mo bty sbty cbty bbty nbty ubty))
      fmapEmpty from rfl]
  rw [show collect_saves (dlProdProg ra mo bty sbty cbty bbty nbty ubty) =
      dlQ loc0 empty_annotation ra mo cbty bbty nbty ubty from by
    unfold collect_saves collect_saves_aux dlProdProg lrProdPrefix createExpr
      storeOpRedex
    rw [show lemDefaultFuel = 999999 + 1 from rfl, col_aux_sseq]
    rw [show (999999 : Nat) = 999998 + 1 from rfl, col_aux_action,
      col_aux_sseq]
    rw [show (999998 : Nat) = 999997 + 1 from rfl, col_aux_action,
      col_aux_sseq]
    rw [show (999997 : Nat) = 999996 + 1 from rfl, col_aux_action,
      col_aux_sseq]
    rw [show (999996 : Nat) = 999995 + 1 from rfl, col_aux_action,
      col_aux_sseq]
    rw [show (999995 : Nat) = 999994 + 1 from rfl, col_aux_action,
      col_aux_sseq]
    rw [show (999994 : Nat) = 999993 + 1 from rfl, col_aux_action]
    rw [show (999993 : Nat) = 999984 + 9 from rfl, col_dlProdSave]
    rfl]

theorem dlProd_labeledAt (sup : Nat) (ra : core_run_annotation) (mo : memory_order)
    (bty sbty cbty bbty nbty ubty : core_base_type) :
    LabeledAt ((initial_core_run_state sup (collect_labeled_continuations_NEW
        (prodFile (dlProdProg ra mo bty sbty cbty bbty nbty ubty)))).1)
      mainSym (dlQ loc0 empty_annotation ra mo cbty bbty nbty ubty) := by
  unfold LabeledAt
  rw [show ((initial_core_run_state sup (collect_labeled_continuations_NEW
      (prodFile (dlProdProg ra mo bty sbty cbty bbty nbty ubty)))).1).labeled =
    collect_labeled_continuations_NEW
      (prodFile (dlProdProg ra mo bty sbty cbty bbty nbty ubty))
    from rfl]
  rw [collect_new_dlProd]
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

/-! ### THE PRODUCTION EXPORT -/

/-- DISPOSE A LIST, PRODUCTION FORM (whole-program logic proof): running
    the SHIPPED pipeline cold on the self-contained file that BUILDS a
    two-node list (two `create`s through the PUBLIC `wpt_create`, four
    field stores) and DISPOSES it (the dispose loop, every node through
    the PUBLIC `wpt_kill`) is EXACTLY ONE Active execution delivering the
    unit value, and the final production memory has two DISTINCT
    allocation ids in `deadAllocations` with their records erased
    (`killM`'s effect, CerbMem.lean:1576-1578) — the proof witnesses them
    as the two created nodes; the statement itself names no node (the K4
    range audit's M-2). Cold start, shipped
    registration, termination from the total judgment; the pipeline arrows
    are `wpt_driver_done_alloc` → `prod_run_eqJ`. -/
theorem dispose_list_certified_production (sup : Nat) (ra : core_run_annotation)
    (mo : memory_order) (bty sbty cbty bbty nbty ubty : core_base_type)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND
          (_root_.drive fmapEmpty false
            (prodFile (dlProdProg ra mo bty sbty cbty bbty nbty ubty))
            args)
          ((initial_driver_state sup
            (prodFile (dlProdProg ra mo bty sbty cbty bbty nbty ubty))
            fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = Vunit ∧
      (∃ i₁ i₂ : Int, i₁ ≠ i₂ ∧
        (dst'.layout_state.deadAllocations.contains i₁ = true ∧
          dst'.layout_state.allocations.get? i₁ = none) ∧
        (dst'.layout_state.deadAllocations.contains i₂ = true ∧
          dst'.layout_state.allocations.get? i₂ = none)) ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
  have hQprod := dlProd_labeledAt sup ra mo bty sbty cbty bbty nbty ubty
  obtain ⟨dres, dst', heq, hψ, hbl, hout, herr⟩ :=
    prod_run_eqJ sup (dlProdProg ra mo bty sbty cbty bbty nbty ubty)
      hQprod ψD
      (2 + (2 + ((3 + 1) + ((3 + 1) + ((3 + 1) + ((3 + 1) +
        (dlCost 2 + saveEntryCost (dlProdParams cbty))))))))
      (wpt_driver_done_alloc (GF := SpikeGF)
        (M₀ := procCtx ((initial_core_run_state sup
          (collect_labeled_continuations_NEW
            (prodFile (dlProdProg ra mo bty sbty cbty bbty nbty ubty)))).1))
        rfl rfl (procCtx_labels hQprod) rfl rfl rfl rfl
        (fun l params cont hl => by
          rw [procCtx_labels hQprod] at hl
          obtain ⟨-, rfl⟩ := dlQ_inv loc0 empty_annotation ra mo cbty bbty nbty ubty hl
          exact dlBody_fragJ loc0 empty_annotation ra mo bbty nbty ubty)
        (fun l params cont hl => by
          rw [procCtx_labels hQprod] at hl
          obtain ⟨-, rfl⟩ := dlQ_inv loc0 empty_annotation ra mo cbty bbty nbty ubty hl
          rw [dlBody_pot, show lemDefaultFuel = 999999 + 1 from rfl]
          omega)
        dlProdLsT
        (dlProdProg ra mo bty sbty cbty bbty nbty ubty) fmapEmpty []
        prodMem₀ (∅ : SpikeHeapF SpikeCell)
        (allocCost fmapEmpty nodeTy 8 + allocCost fmapEmpty nodeTy 8)
        (dlProdProg_frag ra mo bty sbty cbty bbty nbty ubty)
        (by rw [dlProdProg_pot ra mo bty sbty cbty bbty nbty ubty,
            show lemDefaultFuel = 999999 + 1 from rfl]
            omega)
        (prodMem₀_launchCoh _ lr_two_node_budget_fits)
        ψD
        (2 + (2 + ((3 + 1) + ((3 + 1) + ((3 + 1) + ((3 + 1) +
          (dlCost 2 + saveEntryCost (dlProdParams cbty))))))))
        (by
          intro inst
          iintro ⟨-, Hcap⟩
          isplitr [Hcap]
          · iapply dlProd_blockSpecsT ra mo mainSym _ cbty bbty nbty ubty hQprod
          · iapply dlProd_wpt ra mo mainSym _ cbty bbty nbty ubty hQprod bty sbty
              fmapEmpty [] symFrame_empty $$ Hcap))
      (by rw [show dlCost 2 = 29 from rfl,
          show saveEntryCost (dlProdParams cbty) = 2 from rfl,
          show CerbFuel.driverFuel = 99999999 + 1 from rfl]
          omega)
      fs args
  refine ⟨dres, dst', heq, hψ.1, ?_, hbl, hout, herr⟩
  obtain ⟨i₁, i₂, hne, hd₁, hd₂⟩ := hψ.2
  exact ⟨i₁, i₂, hne, hd₁, hd₂⟩

end CerberusHeapLang
