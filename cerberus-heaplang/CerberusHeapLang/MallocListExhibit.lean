/-
CerberusHeapLang.MallocListExhibit — THE MALLOC'D LINKED LIST: build a
list of `n` `alloc`ated nodes from ONE linear budget, linking them by
TYPED STORES INTO THE REGIONS, then walk it and `free` every node
(kill/free arc K5 — the exhibit the arc chartered and K4 could not state).

THE PROGRAM (authored Core — ONE label, TWO PHASES told apart by the
counter: `i > 0` allocates, writes and links a node; `i = 0` walks and
frees):

    save ml: (i : int := n, p : ptr := NULL) in
      if i > 0 then
        lets q = alloc(al, 16) in
        lets _ = store(long, q, i) in
        lets _ = store(node*, array_shift(q, long, 1), p) in
        run ml(i - 1, q)
      else
        lets b = memop(PtrEq, [p, NULL(node)]) in
        if b then unit
        else
          lets Specified(nx) = load(node*, array_shift(p, long, 1)) in
          lets _ = free(p) in
          run ml(0, nx)

C's `for (i = n; i > 0; i--) { q = malloc(16); q->v = i; q->next = p;
p = q; } while (p) { nx = p->next; free(p); p = nx; }`, the two loops
merged into one Core label (a single `save` is the whole program's label
map; the two-label form needs a two-entry label-map lookup law this tree
does not have — EnvLaws has the singleton `fmapLookupBy_addBy_empty`).

THE NODE is a 16-byte REGION (`alloc(al, 16)`: untyped, dynamic), read
and written at ListRevExhibit's node layout — `long` value at offset 0,
`node*` next at offset 8 — through THE REGION ACCESS RULES (K5):
`wps_store_regionOwn_at` at `longTy`/offset 0 (the counter), at
`nodePtrTy`/offset 8 (the link), `wps_load_regionOwn_at` at
`nodePtrTy`/offset 8 (the walk). The value field is written but not
tracked by the predicate (the walk never reads it; tracking it would
need the signed-long decode round trip, not in this tree).

THE PREDICATE `isRegionList p ids` — the ids-indexed list of REGION
nodes: `[]` is the null encoding; `id :: ids` ∃-binds the node's base
`aN` (machine-address WF), the next pointer `q` and the 16-byte image
`bs` with its next-field decode fact `nodeNextDec fmapEmpty bs q`
(ListRevExhibit's), and owns `regionOwn id aN 16 (.own 1) bs ∗
isRegionList q ids`. `deadRegions ids` is the persistent dead knowledge
of the freed nodes. DISTINCTNESS (K5.1, the K5 audit's M-1): a fresh
node is distinct from every live node and from every dead one by the
public laws `regionOwn_ne`/`regionOwn_deadRegion_ne` (Heap.lean:
`metaOwn_ne` at the region bundles — `.own 1` beside any fraction, or
beside `.discard`, is one id twice), lifted over the two lists as
`regionOwn_isRegionList_ne`/`regionOwn_deadRegions_ne`; two dead ids
have no such law (both persistent), so their distinctness is CARRIED by
the invariant from the time they were live.

THE INVARIANT (one label, both phases): `allocBudget (i · regionCost al
16) ∗ isRegionList p ids ∗ deadRegions done` with `i + |ids| + |done| =
n` and `(ids ++ done).Nodup` — the capacity for `i` more nodes, the list
built so far, the nodes freed so far, all of them pairwise distinct. In the build phase the budget is SPLIT per iteration
(`allocBudget_split`) and the new node is consed onto the list; in the
free phase (`i = 0`) the head is freed (`wps_free`, its `deadRegion`
kept) and the tail is the new list.

THE RULES CONSUMED (all public, API.lean): `wps_alloc`/`wpt_alloc` (K3),
`wps_store_eval`/`wpt_store_eval` + `wps_store_regionOwn_at`/
`wpt_store_regionOwn_at` (K5, twice per node), `wps_load_eval`/
`wpt_load_eval` + `wps_load_regionOwn_at`/`wpt_load_regionOwn_at` (K5),
`wps_kill_eval`/`wpt_kill_eval` at `Dynamic0` + `wps_free`/`wpt_free`
(K3), `allocBudget_split` (K2.5), `wps_memop_eval` + `wps_memop_ptreq`,
`wps_if_true`/`wps_if_false`, `wps_seq`/`wps_seq_sym`/`wps_seq_spec`,
`wps_run`, `wps_ofVal`, `wps_save`/`wpt_save_vals`, the label-context
rules; total twins. The storability and decode facts of the stored
pointers are ListRevExhibit's (`node_ptr_*`, `reconstruct_ptrImg_*`).
No `Step.*`, no per-step drive equations, no state-interpretation
opening outside `stateInterp_readout` (the dead-list readout, through
the public consequence face `deadRegion_dead`).

THE STATEMENTS. `ml_wps`: `allocBudget (n.toNat * regionCost al 16) ⊢
wps … (mlPost n) (mlProg … n) [fmapEmpty]` with `mlPost n w _ := ⌜w =
.pure Vunit⌝ ∗ ∃ ids, ⌜ids.length = n.toNat ∧ ids.Nodup⌝ ∗ deadRegions
ids` — `n` DISTINCT nodes were allocated, written, linked, and every one
of them is dead (without `Nodup`, `deadRegion` being persistent, the post
would say only that SOME region is dead — the K5 audit's M-1).
`ml_wpt` at the DERIVED budget `mlCost n.toNat 0 + 1 = 25·n.toNat + 7`
(the variant `mlCost i k = 25·i + 13·k + 6`: a build step costs 12 and
trades one unit of `i` for one node, 25 − 13 = 12; a free step costs 13;
exit 6; entry 1). Engine-facing: `malloc_list_certified_total` (the
`driveU` lane, PROVISIONAL as every `driveU` export): from any memory
launching the empty footprint with the budget, the engine DELIVERS `Vunit`
at exactly `25·n.toNat + 7` drive steps with `n.toNat` DISTINCT
allocation ids dead and erased. PRODUCTION: `malloc_list_certified_production` — the
shipped pipeline on the self-contained file is EXACTLY ONE Active
execution delivering `Vunit` whose final memory has `n.toNat` DISTINCT
allocation ids in `deadAllocations` with their records erased (the proof witnesses
them as the freed nodes; the statement names no node — the K4 audit's
M-2 discipline), under the budget-fits-the-cold-start premise stated in
ENGINE vocabulary `hB : n.toNat * (15 + max al.toNat 1) ≤
281474976710647` (`= regionCost al 16` per node, `= headroom
prodMem₀.lastAddress`; the K4 audit's M-1: no package cost/headroom/
cold-start definition in the statement) and `hfuel : 25 * n.toNat + 9 ≤
CerbFuel.driverFuel` (the shipped driver's budget, 10^8).
-/
import CerberusHeapLang.DisposeExhibit

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Map

/-! ## THE PROGRAM (authored Core) -/

def mlISym : sym := Symbol "" 701 SD_None
def mlPSym : sym := Symbol "" 702 SD_None
def mlQSym : sym := Symbol "" 703 SD_None
def mlBSym : sym := Symbol "" 704 SD_None
def mlNSym : sym := Symbol "" 705 SD_None
def mlLoopSym : sym := Symbol "" 706 SD_None
def mlProcSym : sym := Symbol "" 707 SD_None

/-- The guard `i > 0`: build while positive. -/
def mlGuardPe : generic_pexpr Unit sym :=
  Pexpr [] () (PEop binop.OpGt (Pexpr [] () (PEsym mlISym))
    (Pexpr [] () (PEval (ivVal 0))))

/-- The build back-edge argument `i - 1`. -/
def mlDecPe : generic_pexpr Unit sym :=
  Pexpr [] () (PEop binop.OpSub (Pexpr [] () (PEsym mlISym))
    (Pexpr [] () (PEval (ivVal 1))))

/-- `alloc(al, 16)` — one node's region. -/
def mlAllocE (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (al : Int) (pref : prefix0) : CoreExpr :=
  allocExpr loc ann (.IV .Prov_none al) (.IV .Prov_none 16) pref

/-- `store(long, q, i)` — the value field := the counter. -/
def mlStoreValE (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (mo : memory_order) : CoreExpr :=
  storeOpRedex loc ann longTy (Pexpr [] () (PEsym mlQSym))
    (Pexpr [] () (PEsym mlISym)) mo

/-- `store(node*, array_shift(q, long, 1), p)` — q->next := p (the link). -/
def mlStoreNextE (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (mo : memory_order) : CoreExpr :=
  storeOpRedex loc ann nodePtrTy (lrShiftPe mlQSym)
    (Pexpr [] () (PEsym mlPSym)) mo

/-- The build phase: allocate, write the value, link, jump with `(i-1, q)`. -/
def mlBuild (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (mo : memory_order) (al : Int) (pref : prefix0)
    (qbty ubty : core_base_type) : CoreExpr :=
  Expr [] (Esseq (symPat [] mlQSym qbty) (mlAllocE loc ann al pref)
    (Expr [] (Esseq (Pattern [] (CaseBase (none, ubty))) (mlStoreValE loc ann mo)
      (Expr [] (Esseq (Pattern [] (CaseBase (none, ubty))) (mlStoreNextE loc ann mo)
        (Expr [] (Erun ra mlLoopSym [mlDecPe, Pexpr [] () (PEsym mlQSym)])))))))

/-- The null test: `memop(PtrEq, [p, NULL(node)])`. -/
def mlMemopE : CoreExpr :=
  memopRedex PtrEq [Pexpr [] () (PEsym mlPSym), Pexpr [] () (PEval nullVal)]

/-- `load(node*, array_shift(p, long, 1))` — nx := p->next. -/
def mlLoadE (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (mo : memory_order) : CoreExpr :=
  loadOpRedex loc ann nodePtrTy (lrShiftPe mlPSym) mo

/-- `free(p)` — `Kill Dynamic0` at the head. -/
def mlFreeE (loc : CerbLocation.Loc) (ann : core_run_annotation) : CoreExpr :=
  killOpRedex loc ann Dynamic0 (Pexpr [] () (PEsym mlPSym))

/-- The free phase: null test; exit with unit, or load next, free the
    head, jump with `(0, nx)`. -/
def mlFree (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (mo : memory_order) (bbty nbty ubty : core_base_type) : CoreExpr :=
  Expr [] (Esseq (symPat [] mlBSym bbty) mlMemopE
    (Expr [] (Eif (Pexpr [] () (PEsym mlBSym)) (ofVal (.pure Vunit))
      (Expr [] (Esseq (specPat [] [] mlNSym nbty) (mlLoadE loc ann mo)
        (Expr [] (Esseq (Pattern [] (CaseBase (none, ubty))) (mlFreeE loc ann)
          (Expr [] (Erun ra mlLoopSym
            [Pexpr [] () (PEval (ivVal 0)), Pexpr [] () (PEsym mlNSym)])))))))))

/-- The registered loop body: the phase test. -/
def mlBody (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (mo : memory_order) (al : Int) (pref : prefix0)
    (qbty bbty nbty ubty : core_base_type) : CoreExpr :=
  Expr [] (Eif mlGuardPe (mlBuild loc ann ra mo al pref qbty ubty)
    (mlFree loc ann ra mo bbty nbty ubty))

/-- The save parameters (`i := n`, `p := NULL`). -/
def mlParams (ibty pbty : core_base_type) (n : Int) :
    List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)) :=
  [(mlISym, ((ibty, none), Pexpr [] () (PEval (ivVal n)))),
   (mlPSym, ((pbty, none), Pexpr [] () (PEval nullVal)))]

/-- The whole program. -/
def mlProg (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (mo : memory_order) (al : Int) (pref : prefix0)
    (sbty ibty pbty qbty bbty nbty ubty : core_base_type) (n : Int) : CoreExpr :=
  Expr [] (Esave (mlLoopSym, sbty) (mlParams ibty pbty n)
    (mlBody loc ann ra mo al pref qbty bbty nbty ubty))

/-- The label map. -/
def mlQ (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (mo : memory_order) (al : Int) (pref : prefix0)
    (ibty pbty qbty bbty nbty ubty : core_base_type) : LabelMap :=
  fmapAddBy symCmpL mlLoopSym
    ([(mlISym, ibty), (mlPSym, pbty)], mlBody loc ann ra mo al pref qbty bbty nbty ubty)
    fmapEmpty

/-- The run state carrying the two-level `labeled` tie. -/
def mlRS (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (mo : memory_order) (al : Int) (pref : prefix0)
    (ibty pbty qbty bbty nbty ubty : core_base_type) : core_run_state :=
  { spikeRunState with
      labeled := fmapAddBy symCmpL mlProcSym
        (mlQ loc ann ra mo al pref ibty pbty qbty bbty nbty ubty) fmapEmpty }

section MlFacts

variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (mo : memory_order) (al : Int) (pref : prefix0)
  (ibty pbty qbty bbty nbty ubty : core_base_type)

theorem mlQ_lookup :
    lookupLabel (mlQ loc ann ra mo al pref ibty pbty qbty bbty nbty ubty) mlLoopSym =
      some ([(mlISym, ibty), (mlPSym, pbty)],
        mlBody loc ann ra mo al pref qbty bbty nbty ubty) := by
  unfold lookupLabel mlQ
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

theorem mlQ_inv {l : sym} {params : List (sym × core_base_type)}
    {cont : CoreExpr}
    (h : lookupLabel (mlQ loc ann ra mo al pref ibty pbty qbty bbty nbty ubty) l =
      some (params, cont)) :
    params = [(mlISym, ibty), (mlPSym, pbty)] ∧
      cont = mlBody loc ann ra mo al pref qbty bbty nbty ubty := by
  unfold lookupLabel mlQ at h
  rw [fmapLookupBy_addBy_empty] at h
  split at h
  · obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
    exact ⟨h1.symm ▸ rfl, h2.symm ▸ rfl⟩
  · cases h

theorem mlRS_labeledAt :
    LabeledAt (mlRS loc ann ra mo al pref ibty pbty qbty bbty nbty ubty) mlProcSym
      (mlQ loc ann ra mo al pref ibty pbty qbty bbty nbty ubty) := by
  unfold LabeledAt mlRS
  show fmapLookupBy _ _ (fmapAddBy symCmpL mlProcSym _ fmapEmpty) = _
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

end MlFacts

/-! ## Frames, lookups, bindings, evaluation -/

/-- The frame after the loop bindings (i, p). -/
def mlFrame (vi vp : value) (f : Fmap sym value) : Fmap sym value :=
  envAdd mlPSym vp (envAdd mlISym vi f)

/-- ... after additionally binding the fresh node pointer q (build). -/
def mlFrameQ (vq vi vp : value) (f : Fmap sym value) : Fmap sym value :=
  envAdd mlQSym vq (mlFrame vi vp f)

/-- ... after additionally binding the null-test boolean b (free). -/
def mlFrameB (vb vi vp : value) (f : Fmap sym value) : Fmap sym value :=
  envAdd mlBSym vb (mlFrame vi vp f)

/-- ... after additionally binding the loaded next pointer nx (free). -/
def mlFrameN (vn vb vi vp : value) (f : Fmap sym value) : Fmap sym value :=
  envAdd mlNSym vn (mlFrameB vb vi vp f)

theorem mlFrame_symFrame {f : Fmap sym value} (hf : SymFrame f) (vi vp : value) :
    SymFrame (mlFrame vi vp f) :=
  (hf.add _ _).add _ _

theorem mlFrameQ_symFrame {f : Fmap sym value} (hf : SymFrame f) (vq vi vp : value) :
    SymFrame (mlFrameQ vq vi vp f) :=
  (mlFrame_symFrame hf _ _).add _ _

theorem mlFrameB_symFrame {f : Fmap sym value} (hf : SymFrame f) (vb vi vp : value) :
    SymFrame (mlFrameB vb vi vp f) :=
  (mlFrame_symFrame hf _ _).add _ _

theorem mlFrameN_symFrame {f : Fmap sym value} (hf : SymFrame f) (vn vb vi vp : value) :
    SymFrame (mlFrameN vn vb vi vp f) :=
  (mlFrameB_symFrame hf _ _ _).add _ _

section MlLookups

variable {f : Fmap sym value} (hf : SymFrame f) (vn vb vq vi vp : value)

include hf

theorem mlFrame_lookup_p :
    fmapLookupBy symCmpK mlPSym (mlFrame vi vp f) = some vp := by
  unfold mlFrame
  rw [envAdd_lookup (hf.add _ _) symCmpK, if_pos (by decide +kernel)]

theorem mlFrame_lookup_i :
    fmapLookupBy symCmpK mlISym (mlFrame vi vp f) = some vi := by
  unfold mlFrame
  rw [envAdd_lookup (hf.add _ _) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup hf symCmpK, if_pos (by decide +kernel)]

theorem mlFrameQ_lookup_q :
    fmapLookupBy symCmpK mlQSym (mlFrameQ vq vi vp f) = some vq := by
  unfold mlFrameQ
  rw [envAdd_lookup (mlFrame_symFrame hf _ _) symCmpK, if_pos (by decide +kernel)]

theorem mlFrameQ_lookup_i :
    fmapLookupBy symCmpK mlISym (mlFrameQ vq vi vp f) = some vi := by
  unfold mlFrameQ
  rw [envAdd_lookup (mlFrame_symFrame hf _ _) symCmpK, if_neg (by decide +kernel),
    mlFrame_lookup_i hf]

theorem mlFrameQ_lookup_p :
    fmapLookupBy symCmpK mlPSym (mlFrameQ vq vi vp f) = some vp := by
  unfold mlFrameQ
  rw [envAdd_lookup (mlFrame_symFrame hf _ _) symCmpK, if_neg (by decide +kernel),
    mlFrame_lookup_p hf]

theorem mlFrameB_lookup_b :
    fmapLookupBy symCmpK mlBSym (mlFrameB vb vi vp f) = some vb := by
  unfold mlFrameB
  rw [envAdd_lookup (mlFrame_symFrame hf _ _) symCmpK, if_pos (by decide +kernel)]

theorem mlFrameB_lookup_p :
    fmapLookupBy symCmpK mlPSym (mlFrameB vb vi vp f) = some vp := by
  unfold mlFrameB
  rw [envAdd_lookup (mlFrame_symFrame hf _ _) symCmpK, if_neg (by decide +kernel),
    mlFrame_lookup_p hf]

theorem mlFrameN_lookup_n :
    fmapLookupBy symCmpK mlNSym (mlFrameN vn vb vi vp f) = some vn := by
  unfold mlFrameN
  rw [envAdd_lookup (mlFrameB_symFrame hf _ _ _) symCmpK, if_pos (by decide +kernel)]

theorem mlFrameN_lookup_p :
    fmapLookupBy symCmpK mlPSym (mlFrameN vn vb vi vp f) = some vp := by
  unfold mlFrameN
  rw [envAdd_lookup (mlFrameB_symFrame hf _ _ _) symCmpK, if_neg (by decide +kernel),
    mlFrameB_lookup_p hf]

end MlLookups

/-! ## Binding computations -/

theorem bindSave_ml (ibty pbty : core_base_type) (n : Int)
    (f : Fmap sym value) (rest : List (Fmap sym value)) :
    bindSaveParams (mlParams ibty pbty n) [ivVal n, nullVal] (f :: rest) =
      mlFrame (ivVal n) nullVal f :: rest := by
  show update_env (mk_sym_pat mlPSym pbty) nullVal
    (update_env (mk_sym_pat mlISym ibty) (ivVal n) (f :: rest)) = _
  rw [update_env_cons, update_env_aux_sym, update_env_cons, update_env_aux_sym]
  rfl

theorem bindArgs_ml (ibty pbty : core_base_type) (vi vp : value) (f : Fmap sym value)
    (rest : List (Fmap sym value)) :
    bindArgs [(mlISym, ibty), (mlPSym, pbty)] [vi, vp] (f :: rest) =
      mlFrame vi vp f :: rest := by
  show update_env (mk_sym_pat mlPSym pbty) vp
    (update_env (mk_sym_pat mlISym ibty) vi (f :: rest)) = _
  rw [update_env_cons, update_env_aux_sym, update_env_cons, update_env_aux_sym]
  rfl

theorem bindSym_ml (bbty : core_base_type) (vb vi vp : value)
    (f : Fmap sym value) (rest : List (Fmap sym value)) :
    update_env (symPat [] mlBSym bbty) vb (mlFrame vi vp f :: rest) =
      mlFrameB vb vi vp f :: rest := by
  rw [update_env_sym]
  rfl

/-! ## Evaluation facts at the bound frames -/

section MlEval

variable {f : Fmap sym value} (hf : SymFrame f) (rest : List (Fmap sym value))

theorem ml_memop_operands_nonvalue :
    valueFromPexprs [Pexpr ([] : List annot) () (PEsym mlPSym),
      Pexpr [] () (PEval nullVal)] = none := rfl

include hf

/-- The guard at the counter `i`: the engine's own `OpGt`, the boolean `0 < i`. -/
theorem ml_guard_eval (vp : value) (i : Int) :
    evalPexpr fmapEmpty fmapEmpty (mlFrame (ivVal i) vp f :: rest) mlGuardPe =
      some (boolValue (decide (0 < i))) := by
  unfold mlGuardPe
  rw [evalPexpr_op]
  rw [show evalPexpr fmapEmpty fmapEmpty (mlFrame (ivVal i) vp f :: rest)
      (Pexpr [] () (PEsym mlISym)) = some (ivVal i) from by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (mlFrame_lookup_i hf _ _) rest]
  show evalBinop binop.OpGt (ivVal i) (ivVal 0) = _
  unfold evalBinop ivVal
  show (CerbMem.ltIval (CerbMem.integerIval 0)
    (CerbMem.integerIval i)).map boolValue = _
  rfl

/-- The memop's head operand `p`. -/
theorem ml_p_eval (vi vp : value) :
    evalPexpr fmapEmpty fmapEmpty (mlFrame vi vp f :: rest)
      (Pexpr [] () (PEsym mlPSym)) = some vp := by
  rw [evalPexpr_sym_empty]
  exact lookup_env_head (mlFrame_lookup_p hf _ _) rest

theorem ml_q_eval (vq vi vp : value) :
    evalPexpr fmapEmpty fmapEmpty (mlFrameQ vq vi vp f :: rest)
      (Pexpr [] () (PEsym mlQSym)) = some vq := by
  rw [evalPexpr_sym_empty]
  exact lookup_env_head (mlFrameQ_lookup_q hf _ _ _) rest

theorem ml_i_eval_Q (vq vi vp : value) :
    evalPexpr fmapEmpty fmapEmpty (mlFrameQ vq vi vp f :: rest)
      (Pexpr [] () (PEsym mlISym)) = some vi := by
  rw [evalPexpr_sym_empty]
  exact lookup_env_head (mlFrameQ_lookup_i hf _ _ _) rest

theorem ml_p_eval_Q (vq vi vp : value) :
    evalPexpr fmapEmpty fmapEmpty (mlFrameQ vq vi vp f :: rest)
      (Pexpr [] () (PEsym mlPSym)) = some vp := by
  rw [evalPexpr_sym_empty]
  exact lookup_env_head (mlFrameQ_lookup_p hf _ _ _) rest

/-- The link store's address: `array_shift(q, long, 1)` at the fresh
    node pointer — +8 within the region (the engine's own arithmetic). -/
theorem ml_shift_q_eval (vi vp : value) (id a : Int) :
    evalPexpr fmapEmpty fmapEmpty (mlFrameQ (ptrVal (cellPtr id a)) vi vp f :: rest)
      (lrShiftPe mlQSym) = some (ptrVal (cellPtr id (a + 8))) := by
  unfold lrShiftPe
  rw [evalPexpr_array_shift]
  rw [show evalPexpr fmapEmpty fmapEmpty (mlFrameQ (ptrVal (cellPtr id a)) vi vp f :: rest)
      (Pexpr [] () (PEsym mlQSym)) = some (ptrVal (cellPtr id a)) from by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (mlFrameQ_lookup_q hf _ _ _) rest]
  show evalArrayShift fmapEmpty longTy (Vobject (OVpointer (cellPtr id a))) (ivVal 1) = _
  exact evalArrayShift_long_one id a

/-- The build back-edge arguments `(i - 1, q)`. -/
theorem ml_args_build_eval (vq : value) (i : Int) (vp : value) :
    evalPexprs fmapEmpty fmapEmpty (mlFrameQ vq (ivVal i) vp f :: rest)
      [mlDecPe, Pexpr [] () (PEsym mlQSym)] = some [ivVal (i - 1), vq] := by
  rw [evalPexprs_cons]
  rw [show evalPexpr fmapEmpty fmapEmpty (mlFrameQ vq (ivVal i) vp f :: rest)
      mlDecPe = some (ivVal (i - 1)) from by
    unfold mlDecPe
    rw [evalPexpr_op]
    rw [show evalPexpr fmapEmpty fmapEmpty (mlFrameQ vq (ivVal i) vp f :: rest)
        (Pexpr [] () (PEsym mlISym)) = some (ivVal i) from by
      rw [evalPexpr_sym_empty]
      exact lookup_env_head (mlFrameQ_lookup_i hf _ _ _) rest]
    rfl]
  rw [evalPexprs_cons]
  rw [show evalPexpr fmapEmpty fmapEmpty (mlFrameQ vq (ivVal i) vp f :: rest)
      (Pexpr ([] : List annot) () (PEsym mlQSym)) = some vq from by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (mlFrameQ_lookup_q hf _ _ _) rest]
  rfl

theorem ml_b_eval (vb vi vp : value) :
    evalPexpr fmapEmpty fmapEmpty (mlFrameB vb vi vp f :: rest)
      (Pexpr [] () (PEsym mlBSym)) = some vb := by
  rw [evalPexpr_sym_empty]
  exact lookup_env_head (mlFrameB_lookup_b hf _ _ _) rest

/-- The walk's load address: `array_shift(p, long, 1)` at the head. -/
theorem ml_shift_p_eval_B (vb vi : value) (id aN : Int) :
    evalPexpr fmapEmpty fmapEmpty (mlFrameB vb vi (ptrVal (cellPtr id aN)) f :: rest)
      (lrShiftPe mlPSym) = some (ptrVal (cellPtr id (aN + 8))) := by
  unfold lrShiftPe
  rw [evalPexpr_array_shift]
  rw [show evalPexpr fmapEmpty fmapEmpty (mlFrameB vb vi (ptrVal (cellPtr id aN)) f :: rest)
      (Pexpr [] () (PEsym mlPSym)) = some (ptrVal (cellPtr id aN)) from by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (mlFrameB_lookup_p hf _ _ _) rest]
  show evalArrayShift fmapEmpty longTy (Vobject (OVpointer (cellPtr id aN))) (ivVal 1) = _
  exact evalArrayShift_long_one id aN

/-- The free's operand `p`, after nx is bound. -/
theorem ml_p_eval_N (vn vb vi vp : value) :
    evalPexpr fmapEmpty fmapEmpty (mlFrameN vn vb vi vp f :: rest)
      (Pexpr [] () (PEsym mlPSym)) = some vp := by
  rw [evalPexpr_sym_empty]
  exact lookup_env_head (mlFrameN_lookup_p hf _ _ _ _) rest

/-- The free back-edge arguments `(0, nx)`. -/
theorem ml_args_free_eval (vn vb vi vp : value) :
    evalPexprs fmapEmpty fmapEmpty (mlFrameN vn vb vi vp f :: rest)
      [Pexpr [] () (PEval (ivVal 0)), Pexpr [] () (PEsym mlNSym)] =
      some [ivVal 0, vn] := by
  rw [evalPexprs_cons, evalPexpr_val, evalPexprs_cons]
  rw [show evalPexpr fmapEmpty fmapEmpty (mlFrameN vn vb vi vp f :: rest)
      (Pexpr ([] : List annot) () (PEsym mlNSym)) = some vn from by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (mlFrameN_lookup_n hf _ _ _ _) rest]
  rfl

end MlEval

/-! ## The stored values: storability and decode (the counter at `long`,
the link at `node*`) -/

/-- The counter, a Core integer value, encodes at `long`. -/
theorem longMval_encodes (v : Int) :
    memValueFromValue fmapEmpty (Ctype [] (unatomic_ longTy)) (ivVal v) =
      some (longMval v) := rfl

theorem longMval_compat (v : Int) :
    CerbMem.ctypeMemCompatible longTy (CerbMem.typeofMval (longMval v)) = true := rfl

theorem longMval_fpm (v : Int) (fpm : CerbMem.Funptrmap) :
    (CerbMem.memValueToBytes fmapEmpty fpm (longMval v)).1 = fpm := rfl

theorem longMval_bytes_fpm (v : Int) (fpm : CerbMem.Funptrmap) :
    (CerbMem.memValueToBytes fmapEmpty fpm (longMval v)).2 =
      (CerbMem.memValueToBytes fmapEmpty [] (longMval v)).2 := rfl

/-- The serialized `long` image is 8 bytes at ANY value (`intToBytes`
    at `sizeof long = 8`, CerbMem.lean:590-599). -/
theorem longMval_img_length (v : Int) :
    ((CerbMem.memValueToBytes fmapEmpty [] (longMval v)).2).length = 8 := by
  show ((CerbMem.intToBytes v 8).map
    (fun b => ({ prov := .Prov_none, copyOffset := none, value := b } : CerbMem.AbsByte))).length = 8
  rw [List.length_map, intToBytes_length]

theorem longMval_storable (v : Int) : StorableView fmapEmpty longTy (longMval v) :=
  ⟨longMval_compat v, longMval_fpm v, longMval_bytes_fpm v,
    by rw [longTy_size]; exact longMval_img_length v⟩

/-- The next-pointer values the build stores: the null, or a node pointer
    at a machine-WF address (what `isRegionList` pins for every head). -/
def NodePtrWF (p : CerbMem.PointerValue) : Prop :=
  p = nullNode ∨ ∃ id a : Int, p = cellPtr id a ∧ 0 < a ∧ a < 2 ^ 64

theorem nodePtr_storable {p : CerbMem.PointerValue} (h : NodePtrWF p) :
    StorableView fmapEmpty nodePtrTy (CerbMem.pointerMval nodeTy p) := by
  rcases h with rfl | ⟨id, a, rfl, -, -⟩
  · exact ⟨node_ptr_compat _, node_ptr_fpm_null, node_ptr_bytes_null,
      by rw [node_ptr_img_null, nodePtrTy_size]; exact ptrImg_null_length⟩
  · exact ⟨node_ptr_compat _, node_ptr_fpm_cell id a, node_ptr_bytes_cell id a,
      by rw [node_ptr_img_cell, nodePtrTy_size]; exact ptrImg_cell_length id a⟩

theorem nodePtr_img_length {p : CerbMem.PointerValue} (h : NodePtrWF p) :
    ((CerbMem.memValueToBytes fmapEmpty [] (CerbMem.pointerMval nodeTy p)).2).length = 8 := by
  have := (nodePtr_storable h).len
  rwa [nodePtrTy_size] at this

/-- The stored link reloads at `node*` as itself (ListRevExhibit's round
    trips `reconstruct_ptrImg_null`/`reconstruct_ptrImg_cell`). -/
theorem nodePtr_reconstruct {p : CerbMem.PointerValue} (h : NodePtrWF p)
    (lum : List (Int × identifier)) (fpm : CerbMem.Funptrmap) (ad : Int) :
    CerbMem.reconstructValue fmapEmpty lum fpm ad nodePtrTy
        (CerbMem.memValueToBytes fmapEmpty [] (CerbMem.pointerMval nodeTy p)).2 =
      .MVpointer nodeTy p := by
  rcases h with rfl | ⟨id, a, rfl, h0, h1⟩
  · rw [node_ptr_img_null]
    exact reconstruct_ptrImg_null lum fpm ad
  · rw [node_ptr_img_cell]
    exact reconstruct_ptrImg_cell id a h0 h1 lum fpm ad

/-! ## The built node image -/

/-- The fresh region's image (what `alloc(al, 16)` delivers). -/
abbrev regionUndef16 : List CerbMem.AbsByte := List.replicate 16 undefByte

/-- A built node: the counter at offset 0 (spliced first), the link at
    offset 8 (spliced second) over the fresh image. -/
abbrev mlBuilt (i : Int) (p : CerbMem.PointerValue) : List CerbMem.AbsByte :=
  spliceBytes 8 (CerbMem.memValueToBytes fmapEmpty [] (CerbMem.pointerMval nodeTy p)).2
    (spliceBytes 0 (CerbMem.memValueToBytes fmapEmpty [] (longMval i)).2 regionUndef16)

theorem mlBuilt_inner_len (i : Int) :
    (spliceBytes 0 (CerbMem.memValueToBytes fmapEmpty [] (longMval i)).2
      regionUndef16).length = 16 := by
  rw [spliceBytes_length _ _ _ (by rw [longMval_img_length]; decide)]
  rfl

theorem mlBuilt_len (i : Int) {p : CerbMem.PointerValue} (h : NodePtrWF p) :
    (mlBuilt i p).length = 16 := by
  rw [spliceBytes_length _ _ _ (by rw [nodePtr_img_length h, mlBuilt_inner_len]; decide)]
  exact mlBuilt_inner_len i

/-- The built node's next field decodes to the stored link. -/
theorem mlBuilt_nextDec (i : Int) {p : CerbMem.PointerValue} (h : NodePtrWF p) :
    nodeNextDec fmapEmpty (mlBuilt i p) p := by
  intro lum fpm ad
  rw [show ((mlBuilt i p).drop 8).take 8 =
      (CerbMem.memValueToBytes fmapEmpty [] (CerbMem.pointerMval nodeTy p)).2 from
    spliceBytes_next_slice _ _ (nodePtr_img_length h) (mlBuilt_inner_len i)]
  exact nodePtr_reconstruct h lum fpm ad

/-! ## THE PREDICATES: `isRegionList p ids` and `deadRegions ids` -/

section RegionList

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]

/-- What `alloc(al, 16)` delivers, at the literal size (the rule's post
    is at `sizeN.toNat`; `(16 : Int).toNat = 16` definitionally). -/
theorem regionOwn_alloc16 (id a : Int) :
    regionOwn (GF := GF) id a (Int.toNat 16) (.own 1)
        (List.replicate (Int.toNat 16) undefByte) ⊢
      regionOwn id a 16 (.own 1) regionUndef16 := .rfl

/-- THE MALLOC'D LIST, ids-indexed: `[]` is the null encoding; a node is
    a live 16-byte REGION at full ownership whose next field (offset 8,
    `node*`) decodes to the tail's head; machine-address WF per node. -/
def isRegionList : CerbMem.PointerValue → List Int → IProp GF
  | p, [] => iprop(⌜p = nullNode⌝)
  | p, id :: ids => iprop(∃ (aN : Int) (q : CerbMem.PointerValue)
      (bs : List CerbMem.AbsByte),
      ⌜p = cellPtr id aN ∧ 0 < aN ∧ aN < 2 ^ 64 ∧ bs.length = 16 ∧
        nodeNextDec fmapEmpty bs q⌝ ∗
      regionOwn id aN 16 (.own 1) bs ∗ isRegionList q ids)

@[simp] theorem isRegionList_nil (p : CerbMem.PointerValue) :
    isRegionList (GF := GF) p [] = iprop(⌜p = nullNode⌝) := rfl

theorem isRegionList_cons (p : CerbMem.PointerValue) (id : Int) (ids : List Int) :
    isRegionList (GF := GF) p (id :: ids) = iprop(∃ (aN : Int)
      (q : CerbMem.PointerValue) (bs : List CerbMem.AbsByte),
      ⌜p = cellPtr id aN ∧ 0 < aN ∧ aN < 2 ^ 64 ∧ bs.length = 16 ∧
        nodeNextDec fmapEmpty bs q⌝ ∗
      regionOwn id aN 16 (.own 1) bs ∗ isRegionList q ids) := rfl

theorem isRegionList_nil_intro : ⊢ isRegionList (GF := GF) nullNode [] := by
  rw [isRegionList_nil]
  ipureintro
  rfl

theorem isRegionList_cons_intro (id aN : Int) (q : CerbMem.PointerValue)
    (bs : List CerbMem.AbsByte) (ids : List Int)
    (h0 : 0 < aN) (h1 : aN < 2 ^ 64) (hlen : bs.length = 16)
    (hnext : nodeNextDec fmapEmpty bs q) :
    iprop(regionOwn (GF := GF) id aN 16 (.own 1) bs ∗ isRegionList q ids) ⊢
      isRegionList (cellPtr id aN) (id :: ids) := by
  rw [isRegionList_cons]
  iintro ⟨Hr, HL⟩
  iexists aN, q, bs
  isplit
  · ipureintro
    exact ⟨rfl, h0, h1, hlen, hnext⟩
  isplitl [Hr]
  · iexact Hr
  · iexact HL

/-- Every list head is a storable link: the null, or a node pointer at a
    WF address (read off the predicate, non-destructively via `keep_pure`). -/
theorem isRegionList_wf (p : CerbMem.PointerValue) (ids : List Int) :
    isRegionList (GF := GF) p ids ⊢ (⌜NodePtrWF p⌝ : IProp GF) := by
  cases ids with
  | nil =>
    rw [isRegionList_nil]
    iintro %h
    ipureintro
    exact Or.inl h
  | cons id ids =>
    rw [isRegionList_cons]
    iintro ⟨%aN, %q, %bs, %hf, -, -⟩
    ipureintro
    exact Or.inr ⟨id, aN, hf.1, hf.2.1, hf.2.2.1⟩

/-- A fully-owned live region is NONE of the list's nodes (K5.1: the
    public `regionOwn_ne` down the list; the pure fact read off
    non-destructively at the call sites via `keep_pure`). -/
theorem regionOwn_isRegionList_ne (id a : Int) (bs : List CerbMem.AbsByte) :
    ∀ (p : CerbMem.PointerValue) (ids : List Int),
    iprop(regionOwn (GF := GF) id a 16 (.own 1) bs ∗ isRegionList p ids) ⊢
      (⌜id ∉ ids⌝ : IProp GF)
  | _, [] => by
    iintro ⟨-, -⟩
    ipureintro
    exact fun h => nomatch h
  | p, id' :: ids => by
    rw [isRegionList_cons]
    iintro ⟨Hr, %aN, %q, %bs', -, Hr', HT⟩
    ihave H1 : iprop(⌜id ≠ id'⌝ ∗ (regionOwn (GF := GF) id a 16 (.own 1) bs ∗
        regionOwn id' aN 16 (.own 1) bs')) $$ [Hr Hr']
    · iapply keep_pure (regionOwn_ne id id' a aN 16 16 (.own 1) bs bs')
      isplitl [Hr]
      · iexact Hr
      · iexact Hr'
    icases H1 with ⟨%hne, Hr, -⟩
    ihave %hnotin : (⌜id ∉ ids⌝ : IProp GF) $$ [Hr HT]
    · iapply regionOwn_isRegionList_ne id a bs q ids
      isplitl [Hr]
      · iexact Hr
      · iexact HT
    ipureintro
    intro hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hne rfl
    · exact hnotin hmem

/-- The dead regions of an id list: for each, `deadRegion` at SOME base,
    16 bytes (the DisposeExhibit `deadNodes` shape, for regions). -/
def deadRegions : List Int → IProp GF
  | [] => iprop(emp)
  | id :: ids => iprop((∃ a : Int, deadRegion id a 16) ∗ deadRegions ids)

@[simp] theorem deadRegions_nil : deadRegions (GF := GF) [] = iprop(emp) := rfl

theorem deadRegions_cons (id : Int) (ids : List Int) :
    deadRegions (GF := GF) (id :: ids) =
      iprop((∃ a : Int, deadRegion id a 16) ∗ deadRegions ids) := rfl

/-- A fully-owned live region is NONE of the dead ones (K5.1: the public
    `regionOwn_deadRegion_ne` down the dead list). -/
theorem regionOwn_deadRegions_ne (id a : Int) (bs : List CerbMem.AbsByte) :
    ∀ ids : List Int,
    iprop(regionOwn (GF := GF) id a 16 (.own 1) bs ∗ deadRegions ids) ⊢
      (⌜id ∉ ids⌝ : IProp GF)
  | [] => by
    iintro ⟨-, -⟩
    ipureintro
    exact fun h => nomatch h
  | id' :: ids => by
    rw [deadRegions_cons]
    iintro ⟨Hr, ⟨%a', Hd⟩, HD⟩
    ihave H1 : iprop(⌜id ≠ id'⌝ ∗ (regionOwn (GF := GF) id a 16 (.own 1) bs ∗
        deadRegion id' a' 16)) $$ [Hr Hd]
    · iapply keep_pure (regionOwn_deadRegion_ne id id' a a' 16 16 bs)
      isplitl [Hr]
      · iexact Hr
      · iexact Hd
    icases H1 with ⟨%hne, Hr, -⟩
    ihave %hnotin : (⌜id ∉ ids⌝ : IProp GF) $$ [Hr HD]
    · iapply regionOwn_deadRegions_ne id a bs ids
      isplitl [Hr]
      · iexact Hr
      · iexact HD
    ipureintro
    intro hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hne rfl
    · exact hnotin hmem

/-- Every id of the dead list is dead in the real state — through the
    public consequence face `deadRegion_dead` (the metadata
    interpretation returned each time). -/
theorem deadRegions_dead {σ : Mem} {mm : SpikeHeapF MetaCell}
    {mb : SpikeHeapF CerbMem.AbsByte} {mk : SpikeHeapF AllocCursor}
    (hG : CohG σ mm mb mk) :
    ∀ ids : List Int,
    iprop(metaInterp (GF := GF) mm ∗ deadRegions ids) ⊢
      iprop(⌜∀ id ∈ ids, DeadAt σ id⌝ ∗ metaInterp mm)
  | [] => by
    rw [deadRegions_nil]
    iintro ⟨Hmi, -⟩
    isplitr [Hmi]
    · ipureintro
      intro _ h
      nomatch h
    · iexact Hmi
  | id :: ids => by
    rw [deadRegions_cons]
    iintro ⟨Hmi, ⟨%a, Hd⟩, Hrest⟩
    ihave H1 : iprop(⌜σ.deadAllocations.contains id = true ∧ σ.allocations.get? id = none⌝ ∗
        metaInterp (GF := GF) mm) $$ [Hmi Hd]
    · iapply (keep_pure (deadRegion_dead hG id a 16)).trans
        (BI.sep_mono_right BI.sep_elim_left)
      isplitl [Hmi]
      · iexact Hmi
      · iexact Hd
    icases H1 with ⟨%h1, Hmi⟩
    ihave H2 : iprop(⌜∀ x ∈ ids, DeadAt σ x⌝ ∗ metaInterp (GF := GF) mm) $$ [Hmi Hrest]
    · iapply deadRegions_dead hG ids
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

end RegionList

/-! ## The certified cone membership -/

section MlFrag

variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (mo : memory_order) (al : Int) (pref : prefix0)
  (qbty bbty nbty ubty : core_base_type)

/-- The label body is in the certified cone: the build phase is `alloc`
    (a `BareHead`) then two `store_op`s at `PePure` operands and a `run`;
    the free phase is the `PtrEq` memop head, the `if`, a `load_op`, a
    `kill_op` (dynamic kind) and a `run`. -/
theorem mlBody_frag : Frag (mlBody loc ann ra mo al pref qbty bbty nbty ubty) := by
  have hb : BareHead (memopRedex PtrEq
      [Pexpr [] () (PEsym mlPSym), Pexpr [] () (PEval nullVal)]) :=
    .memop_op rfl (.sym _ _) (.val _ _)
      (by rw [show peDepth (Pexpr ([] : List annot) () (PEsym mlPSym)) = 1
          from rfl, show lemDefaultFuel = 999999 + 1 from rfl]; omega)
      (by rw [show peDepth (Pexpr ([] : List annot) () (PEval nullVal)) = 1
          from rfl, show lemDefaultFuel = 999999 + 1 from rfl]; omega)
  refine .if_ (PePure.of_isPePure rfl)
    (by rw [show peDepth mlGuardPe = 2 from rfl,
      show lemDefaultFuel = 999999 + 1 from rfl]; omega)
    (.sseq_sym .alloc .alloc
      (.sseq
        (.store_op rfl (.sym [] mlQSym) (.sym [] mlISym)
          (by rw [show peDepth (Pexpr ([] : List annot) () (PEsym mlQSym)) = 1
              from rfl, show lemDefaultFuel = 999999 + 1 from rfl]; omega)
          (by rw [show peDepth (Pexpr ([] : List annot) () (PEsym mlISym)) = 1
              from rfl, show lemDefaultFuel = 999999 + 1 from rfl]; omega))
        (.sseq
          (.store_op rfl (.arrayShift [] longTy (.sym _ _) (.val _ _)) (.sym [] mlPSym)
            (by rw [show peDepth (lrShiftPe mlQSym) = 2 from rfl,
                show lemDefaultFuel = 999999 + 1 from rfl]; omega)
            (by rw [show peDepth (Pexpr ([] : List annot) () (PEsym mlPSym)) = 1
                from rfl, show lemDefaultFuel = 999999 + 1 from rfl]; omega))
          (.run (PePure.all_of_isPePure rfl) (by
            intro pe hpe
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
            rcases hpe with rfl | rfl
            · rw [show peDepth mlDecPe = 2 from rfl,
                show lemDefaultFuel = 999999 + 1 from rfl]
              omega
            · rw [show peDepth (Pexpr ([] : List annot) () (PEsym mlQSym)) = 1 from rfl,
                show lemDefaultFuel = 999999 + 1 from rfl]
              omega)))))
    (.sseq_sym hb hb.frag
      (.if_ (PePure.of_isPePure rfl) (by
          rw [show peDepth (Pexpr ([] : List annot) () (PEsym mlBSym)) = 1
            from rfl, show lemDefaultFuel = 999999 + 1 from rfl]
          omega)
        (.val_pure Vunit)
        (.sseq_spec
          (.load_op rfl
            (.arrayShift [] longTy (.sym _ _) (.val _ _))
            (by rw [show peDepth (lrShiftPe mlPSym) = 2 from rfl,
              show lemDefaultFuel = 999999 + 1 from rfl]; omega))
          (.sseq
            (.kill_op rfl (.sym [] mlPSym)
              (by rw [show peDepth (Pexpr ([] : List annot) () (PEsym mlPSym)) = 1
                  from rfl, show lemDefaultFuel = 999999 + 1 from rfl]; omega))
            (.run (PePure.all_of_isPePure rfl) (by
              intro pe hpe
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
              rcases hpe with rfl | rfl
              · exact peDepth_val_le _ _
              · rw [show peDepth (Pexpr ([] : List annot) () (PEsym mlNSym)) = 1 from rfl,
                  show lemDefaultFuel = 999999 + 1 from rfl]
                omega))))))

theorem mlBody_pot : pot (mlBody loc ann ra mo al pref qbty bbty nbty ubty) = 7 := rfl

theorem mlProg_pot (sbty ibty pbty : core_base_type) (n : Int) :
    pot (mlProg loc ann ra mo al pref sbty ibty pbty qbty bbty nbty ubty n) = 8 := rfl

theorem mlParams_depth (ibty pbty : core_base_type) (n : Int) :
    ∀ pe ∈ saveParamPexprs (mlParams ibty pbty n), peDepth pe ≤ lemDefaultFuel := by
  intro pe hpe
  simp only [mlParams, saveParamPexprs, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hpe
  rcases hpe with rfl | rfl
  · exact peDepth_val_le _ _
  · exact peDepth_val_le _ _

end MlFrag

/-! ## THE INVARIANT AND THE PROOF (partial stratum) -/

section MlIris

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (mo : memory_order) (al : Int) (pref : prefix0)
  (ibty pbty qbty bbty nbty ubty : core_base_type) (n : Int)
variable (p : sym) (rs : core_run_state)
  (hQ : LabeledAt rs p (mlQ loc ann ra mo al pref ibty pbty qbty bbty nbty ubty))

/-- The postcondition: the unit value, and `n.toNat` DISTINCT dead
    regions — every node the program allocated is freed (K5.1: `Nodup`;
    without it the persistent `deadRegions` would make the post say only
    that some region is dead). -/
abbrev mlPost : SpikeVal → EnvStack → IProp GF := fun w _ =>
  iprop(⌜w = SpikeVal.pure Vunit⌝ ∗
    ∃ ids : List Int, ⌜ids.length = n.toNat ∧ ids.Nodup⌝ ∗ deadRegions ids)

/-- THE LOOP INVARIANT (both phases): the capacity for `i` more nodes,
    the list built so far, the nodes freed so far — `i + |ids| + |done|
    = n`, all pairwise distinct (`(ids ++ done).Nodup`, K5.1). UNFRAMED. -/
abbrev mlLs : LabelSpec GF := fun _ args ρ =>
  iprop(∃ (i : Int) (pc : CerbMem.PointerValue) (ids done : List Int)
      (f : Fmap sym value) (renv : List (Fmap sym value)),
    ⌜args = [ivVal i, ptrVal pc] ∧ 0 ≤ i ∧
      i.toNat + ids.length + done.length = n.toNat ∧ (ids ++ done).Nodup ∧
      ρ = f :: renv ∧ SymFrame f⌝ ∗
    allocBudget (i.toNat * regionCost al 16) ∗ isRegionList pc ids ∗ deadRegions done)

include hQ

/-- The loop body at any invariant frame. BUILD (`i > 0`): the budget is
    SPLIT (`allocBudget_split`), `wps_alloc` mints the node region, TWO
    TYPED STORES INTO THE REGION write the counter (offset 0, `long`) and
    the link (offset 8, `node*`) through `wps_store_regionOwn_at`, the
    jump conses the node onto the list. FREE (`i = 0`): the null test
    decides; at a node, `wps_load_regionOwn_at` reads the next field,
    `wps_free` returns the region (its `deadRegion` kept), the jump
    continues with the tail. -/
theorem ml_body_wps (i : Int) (pc : CerbMem.PointerValue) (ids done : List Int)
    (f : Fmap sym value) (renv : List (Fmap sym value)) (hf : SymFrame f)
    (hi : 0 ≤ i) (hcnt : i.toNat + ids.length + done.length = n.toNat)
    (hnd : (ids ++ done).Nodup) :
    iprop(allocBudget (GF := GF) (i.toNat * regionCost al 16) ∗
        isRegionList pc ids ∗ deadRegions done) ⊢
      wps (procCtx p rs) (mlLs al n) (mlPost n)
        (mlBody loc ann ra mo al pref qbty bbty nbty ubty)
        (mlFrame (ivVal i) (ptrVal pc) f :: renv) := by
  rw [show mlBody loc ann ra mo al pref qbty bbty nbty ubty =
    Expr [] (Eif mlGuardPe (mlBuild loc ann ra mo al pref qbty ubty)
      (mlFree loc ann ra mo bbty nbty ubty)) from rfl]
  iintro ⟨Hcap, HL, HD⟩
  by_cases hpos : 0 < i
  · -- BUILD: one more node
    iapply wps_if_true [] mlGuardPe _ _ _
      (by rw [procCtx_extern, ml_guard_eval hf renv _ i, decide_eq_true hpos]; rfl)
    rw [show mlBuild loc ann ra mo al pref qbty ubty =
      Expr [] (Esseq (symPat [] mlQSym qbty) (mlAllocE loc ann al pref)
        (Expr [] (Esseq (Pattern [] (CaseBase (none, ubty))) (mlStoreValE loc ann mo)
          (Expr [] (Esseq (Pattern [] (CaseBase (none, ubty))) (mlStoreNextE loc ann mo)
            (Expr [] (Erun ra mlLoopSym [mlDecPe, Pexpr [] () (PEsym mlQSym)]))))))) from rfl]
    rw [show i.toNat * regionCost al 16 =
      regionCost al 16 + (i - 1).toNat * regionCost al 16 from by
        have : i.toNat = (i - 1).toNat + 1 := by omega
        rw [this, Nat.add_mul, Nat.one_mul, Nat.add_comm]]
    icases (allocBudget_split _ _).1 $$ Hcap with ⟨Hc, Hrest⟩
    ihave HL2 := keep_pure (isRegionList_wf pc ids) $$ HL
    icases HL2 with ⟨%hwf, HL⟩
    iapply wps_seq_sym
    rw [show mlAllocE loc ann al pref =
      allocExpr loc ann (.IV .Prov_none al) (.IV .Prov_none 16) pref from rfl]
    iapply wps_alloc loc ann .Prov_none .Prov_none al 16 pref _
      (regionCost_pos al 16 (by decide))
    isplitl [Hc]
    · iexact Hc
    iintro %id %a ⟨Hr, %hb⟩
    have ha1 : a < 2 ^ 64 := by
      have h := hb.2
      have e : ((Int.toNat (16 : Int) : Nat) : Int) = 16 := rfl
      omega
    ihave Hr16 : regionOwn id a 16 (.own 1) regionUndef16 $$ [Hr]
    · iapply regionOwn_alloc16 id a
      iexact Hr
    -- the fresh node is distinct from every live node and every dead one
    ihave HX : iprop(⌜id ∉ ids⌝ ∗ (regionOwn (GF := GF) id a 16 (.own 1) regionUndef16 ∗
        isRegionList pc ids)) $$ [Hr16 HL]
    · iapply keep_pure (regionOwn_isRegionList_ne id a regionUndef16 pc ids)
      isplitl [Hr16]
      · iexact Hr16
      · iexact HL
    icases HX with ⟨%hnotin, Hr16, HL⟩
    ihave HY : iprop(⌜id ∉ done⌝ ∗ (regionOwn (GF := GF) id a 16 (.own 1) regionUndef16 ∗
        deadRegions done)) $$ [Hr16 HD]
    · iapply keep_pure (regionOwn_deadRegions_ne id a regionUndef16 done)
      isplitl [Hr16]
      · iexact Hr16
      · iexact HD
    icases HY with ⟨%hnotin', Hr16, HD⟩
    iexists (Vobject (OVpointer (cellPtr id a)))
    isplit
    · ipureintro
      rfl
    rw [update_env_sym mlQSym qbty]
    rw [show envAdd mlQSym (Vobject (OVpointer (cellPtr id a))) (mlFrame (ivVal i) (ptrVal pc) f) =
      mlFrameQ (ptrVal (cellPtr id a)) (ivVal i) (ptrVal pc) f from rfl]
    -- store 1: the value field := the counter
    iapply wps_seq
    rw [show mlStoreValE loc ann mo = storeOpRedex loc ann longTy
      (Pexpr [] () (PEsym mlQSym)) (Pexpr [] () (PEsym mlISym)) mo from rfl]
    iapply wps_store_eval loc ann longTy _ _ mo _ rfl
      (pv := cellPtr id a) (cv := ivVal i)
      (by rw [procCtx_extern]; exact ml_q_eval hf renv _ _ _)
      (by rw [procCtx_extern]; exact ml_i_eval_Q hf renv _ _ _)
    rw [show (storeExpr loc ann longTy (cellPtr id a) (ivVal i) mo : CoreExpr) =
      storeExpr loc ann longTy (cellPtr id (a + ((0 : Nat) : Int))) (ivVal i) mo from by
      rw [show a + ((0 : Nat) : Int) = a from by omega]]
    iapply wps_store_regionOwn_at (mv := longMval i) loc ann id a 16 0 longTy (ivVal i) mo _ _
      (longMval_encodes i)
      (by rw [show CerbMem.sizeofCtype (procCtx p rs).tagDefs longTy = 8 from rfl]; omega)
      (longMval_storable i)
    isplitl [Hr16]
    · iexact Hr16
    iintro %fp1 Hr
    -- store 2: the next field := the previous head (the link)
    iapply wps_seq
    rw [show mlStoreNextE loc ann mo = storeOpRedex loc ann nodePtrTy
      (lrShiftPe mlQSym) (Pexpr [] () (PEsym mlPSym)) mo from rfl]
    iapply wps_store_eval loc ann nodePtrTy _ _ mo _ rfl
      (pv := cellPtr id (a + 8)) (cv := ptrVal pc)
      (by rw [procCtx_extern]; exact ml_shift_q_eval hf renv _ _ id a)
      (by rw [procCtx_extern]; exact ml_p_eval_Q hf renv _ _ _)
    rw [show cellPtr id (a + 8) = cellPtr id (a + ((8 : Nat) : Int)) from rfl]
    iapply wps_store_regionOwn_at (mv := CerbMem.pointerMval nodeTy pc) loc ann id a 16 8
      nodePtrTy (ptrVal pc) mo _ _ (node_ptr_encodes pc)
      (by rw [show CerbMem.sizeofCtype (procCtx p rs).tagDefs nodePtrTy = 8 from rfl]; omega)
      (nodePtr_storable hwf)
    isplitl [Hr]
    · iexact Hr
    iintro %fp2 Hr
    -- the jump: the node joins the list
    iapply wps_run [] ra mlLoopSym [mlDecPe, Pexpr [] () (PEsym mlQSym)] _ _
      (by rw [procCtx_labels hQ]
          exact mlQ_lookup loc ann ra mo al pref ibty pbty qbty bbty nbty ubty)
      (ml_args_build_eval hf renv _ i _)
    iexists (i - 1), (cellPtr id a), (id :: ids), done,
      (mlFrameQ (ptrVal (cellPtr id a)) (ivVal i) (ptrVal pc) f), renv
    isplit
    · ipureintro
      refine ⟨rfl, by omega, ?_, ?_, rfl, mlFrameQ_symFrame hf _ _ _⟩
      · simp only [List.length_cons]
        omega
      · rw [List.cons_append]
        exact List.nodup_cons.mpr ⟨List.not_mem_append hnotin hnotin', hnd⟩
    isplitl [Hrest]
    · iexact Hrest
    isplitl [Hr HL]
    · iapply isRegionList_cons_intro id a pc (mlBuilt i pc) ids hb.1 ha1
        (mlBuilt_len i hwf) (mlBuilt_nextDec i hwf)
      isplitl [Hr]
      · iexact Hr
      · iexact HL
    · iexact HD
  · -- FREE: i = 0
    have hi0 : i = 0 := by omega
    subst hi0
    iapply wps_if_false [] mlGuardPe _ _ _
      (by rw [procCtx_extern, ml_guard_eval hf renv _ 0]; rfl)
    rw [show mlFree loc ann ra mo bbty nbty ubty =
      Expr [] (Esseq (symPat [] mlBSym bbty) mlMemopE
        (Expr [] (Eif (Pexpr [] () (PEsym mlBSym)) (ofVal (.pure Vunit))
          (Expr [] (Esseq (specPat [] [] mlNSym nbty) (mlLoadE loc ann mo)
            (Expr [] (Esseq (Pattern [] (CaseBase (none, ubty))) (mlFreeE loc ann)
              (Expr [] (Erun ra mlLoopSym
                [Pexpr [] () (PEval (ivVal 0)), Pexpr [] () (PEsym mlNSym)]))))))))) from rfl]
    cases ids with
    | nil =>
      -- p == NULL: the list is exhausted; every node is in the done part
      rw [isRegionList_nil]
      icases HL with %hnull
      subst hnull
      iapply wps_seq_sym
      rw [show mlMemopE = memopRedex PtrEq
        [Pexpr [] () (PEsym mlPSym), Pexpr [] () (PEval nullVal)] from rfl]
      iapply wps_memop_eval PtrEq _ _ _
        ml_memop_operands_nonvalue (ml_p_eval hf renv _ _) rfl
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
      rw [bindSym_ml]
      iapply wps_if_true [] (Pexpr [] () (PEsym mlBSym)) _ _ _
        (by rw [procCtx_extern, ml_b_eval hf renv (boolValue true) _ _]; rfl)
      iapply wps_ofVal (SpikeVal.pure Vunit) _
      isplit
      · ipureintro
        rfl
      iexists done
      isplit
      · ipureintro
        simp only [List.length_nil] at hcnt
        rw [List.nil_append] at hnd
        exact ⟨by omega, hnd⟩
      · iexact HD
    | cons id ids =>
      -- p is a node: load next, FREE the node, continue with the tail
      rw [isRegionList_cons]
      icases HL with ⟨%aN, %q, %bs, %hfacts, Hr, HT⟩
      obtain ⟨rfl, h0, h1, hlen, hnext⟩ := hfacts
      iapply wps_seq_sym
      rw [show mlMemopE = memopRedex PtrEq
        [Pexpr [] () (PEsym mlPSym), Pexpr [] () (PEval nullVal)] from rfl]
      iapply wps_memop_eval PtrEq _ _ _
        ml_memop_operands_nonvalue (ml_p_eval hf renv _ _) rfl
      rw [show memopRedex PtrEq [Pexpr [] () (PEval (ptrVal (cellPtr id aN))),
          Pexpr [] () (PEval nullVal)] =
        memopPtrEqVals (Vobject (OVpointer (cellPtr id aN)))
          (Vobject (OVpointer nullNode)) from rfl]
      iapply wps_memop_ptreq (cellPtr id aN) nullNode _
        (fun σ => eqPtrval_cell_null id aN nodeTy σ)
      iexists (boolValue false)
      isplit
      · ipureintro
        rfl
      rw [bindSym_ml]
      iapply wps_if_false [] (Pexpr [] () (PEsym mlBSym)) _ _ _
        (by rw [procCtx_extern, ml_b_eval hf renv (boolValue false) _ _]; rfl)
      iapply wps_seq_spec
      rw [show mlLoadE loc ann mo =
        loadOpRedex loc ann nodePtrTy (lrShiftPe mlPSym) mo from rfl]
      iapply wps_load_eval loc ann nodePtrTy (lrShiftPe mlPSym) mo _
        rfl (by rw [procCtx_extern]; exact ml_shift_p_eval_B hf renv _ _ id aN)
      rw [show cellPtr id (aN + 8) = cellPtr id (aN + ((8 : Nat) : Int)) from rfl]
      iapply wps_load_regionOwn_at (M := procCtx p rs) loc ann id aN 16 8 nodePtrTy mo
        (.own 1) bs _
        (by rw [show CerbMem.sizeofCtype (procCtx p rs).tagDefs nodePtrTy = 8 from rfl]; omega)
        (fun lum fpm => hnext lum fpm _)
        rfl
      isplitl [Hr]
      · iexact Hr
      iintro %fp Hr
      iexists (OVpointer q)
      isplit
      · ipureintro
        show (valueFromMemValue (.MVpointer nodeTy q)).2 = _
        rw [valueFromMemValue_ptr]
      rw [update_env_spec]
      rw [show envAdd mlNSym (Vobject (OVpointer q))
          (mlFrameB (boolValue false) (ivVal 0) (ptrVal (cellPtr id aN)) f) =
        mlFrameN (ptrVal q) (boolValue false) (ivVal 0) (ptrVal (cellPtr id aN)) f from rfl]
      iapply wps_seq
      rw [show mlFreeE loc ann = killOpRedex loc ann Dynamic0
        (Pexpr [] () (PEsym mlPSym)) from rfl]
      iapply wps_kill_eval loc ann Dynamic0 _ _ rfl (pv := cellPtr id aN)
        (by rw [procCtx_extern]; exact ml_p_eval_N hf renv _ _ _ _)
      iapply wps_free loc ann Dynamic0 id aN 16 bs _ rfl
      isplitl [Hr]
      · iexact Hr
      iintro Hd
      iapply wps_run [] ra mlLoopSym
        [Pexpr [] () (PEval (ivVal 0)), Pexpr [] () (PEsym mlNSym)] _ _
        (by rw [procCtx_labels hQ]
            exact mlQ_lookup loc ann ra mo al pref ibty pbty qbty bbty nbty ubty)
        (ml_args_free_eval hf renv _ _ _ _)
      iexists 0, q, ids, (id :: done),
        (mlFrameN (ptrVal q) (boolValue false) (ivVal 0) (ptrVal (cellPtr id aN)) f), renv
      isplit
      · ipureintro
        refine ⟨rfl, Int.le_refl 0, ?_, ?_, rfl, mlFrameN_symFrame hf _ _ _ _⟩
        · simp only [List.length_cons] at hcnt ⊢
          omega
        · -- the freed head moves from the live list to the dead one
          exact (List.pairwise_middle (fun h => Ne.symm h)).mpr hnd
      isplitl [Hcap]
      · iexact Hcap
      isplitl [HT]
      · iexact HT
      · rw [deadRegions_cons]
        isplitl [Hd]
        · iexists aN
          iexact Hd
        · iexact HD

/-- THE BLOCK SPECIFICATION. -/
theorem ml_blockSpecs :
    ⊢ blockSpecs (GF := GF) (procCtx p rs) (mlLs al n) (mlPost n) := by
  refine blockSpecs_intro fun l params cont args env0 envs hl => ?_
  rw [procCtx_labels hQ] at hl
  obtain ⟨rfl, rfl⟩ := mlQ_inv loc ann ra mo al pref ibty pbty qbty bbty nbty ubty hl
  iintro ⟨%i, %pc, %ids, %done, %f, %renv, %hpure, Hcap, HL, HD⟩
  obtain ⟨rfl, hi, hcnt, hnd, hρ, hf⟩ := hpure
  obtain ⟨rfl, rfl⟩ : f = env0 ∧ renv = envs := by
    have h1 := congrArg (fun l => l.head?) hρ
    have h2 := congrArg (fun l => l.tail) hρ
    simp at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  rw [bindArgs_ml]
  iapply ml_body_wps loc ann ra mo al pref ibty pbty qbty bbty nbty ubty n p rs hQ
    i pc ids done f renv hf hi hcnt hnd
  isplitl [Hcap]
  · iexact Hcap
  isplitl [HL]
  · iexact HL
  · iexact HD

/-- THE MALLOC'D LIST (partial): `{allocBudget (n · regionCost al 16)}
    ml(n, NULL) {ret unit. ∃ ids, |ids| = n ∧ ids.Nodup ∗ deadRegions ids}`
    — `n` DISTINCT nodes allocated, written, linked, walked and freed. -/
theorem ml_wps (sbty : core_base_type) (hn : 0 ≤ n) :
    allocBudget (GF := GF) (n.toNat * regionCost al 16) ⊢
      wps (procCtx p rs) (mlLs al n) (mlPost n)
        (mlProg loc ann ra mo al pref sbty ibty pbty qbty bbty nbty ubty n) [fmapEmpty] := by
  rw [show mlProg loc ann ra mo al pref sbty ibty pbty qbty bbty nbty ubty n =
    Expr [] (Esave (mlLoopSym, sbty) (mlParams ibty pbty n)
      (mlBody loc ann ra mo al pref qbty bbty nbty ubty)) from rfl]
  iintro Hcap
  iapply wps_save [] (mlLoopSym, sbty) _ _ fmapEmpty [] (cvals := [ivVal n, nullVal]) rfl
  rw [bindSave_ml]
  rw [show (nullVal : value) = ptrVal nullNode from rfl]
  iapply ml_body_wps loc ann ra mo al pref ibty pbty qbty bbty nbty ubty n p rs hQ n
    nullNode [] [] fmapEmpty [] symFrame_empty hn (by simp) (by simp)
  isplitl [Hcap]
  · iexact Hcap
  isplitl []
  · rw [isRegionList_nil]
    ipureintro
    rfl
  · rw [deadRegions_nil]
    itrivial

end MlIris

/-! ## The readout: the post as engine table facts -/

section MlReadout

variable {GF : BundledGFunctors} [SpikeGS .hasLC GF]

/-- THE READOUT (through the one sanctioned combinator
    `stateInterp_readout`; the dead list through the public consequence
    face `deadRegion_dead`): unit delivered, and `n.toNat` DISTINCT
    allocation ids in `deadAllocations` with their records erased. -/
theorem mlPost_readout (n : Int) (w : SpikeVal) (ρ' : EnvStack) :
    mlPost (hlc := .hasLC) (GF := GF) n w ρ' ⊢
      readoutPost (fun v σ' => v = Vunit ∧
        ∃ ids : List Int, ids.length = n.toNat ∧ ids.Nodup ∧
          ∀ id ∈ ids, DeadAt σ' id) w ρ' := by
  have haux : iprop(∃ ids : List Int, ⌜ids.length = n.toNat ∧ ids.Nodup⌝ ∗
        deadRegions (hlc := .hasLC) (GF := GF) ids) ⊢
      readoutPost (GF := GF) (fun v σ' => v = Vunit ∧
        ∃ ids : List Int, ids.length = n.toNat ∧ ids.Nodup ∧ ∀ id ∈ ids, DeadAt σ' id)
        (SpikeVal.pure Vunit) ρ' :=
    stateInterp_readout
      (Φ := iprop(∃ ids : List Int, ⌜ids.length = n.toNat ∧ ids.Nodup⌝ ∗ deadRegions ids))
      (ψ := fun σ' => Vunit = Vunit ∧
        ∃ ids : List Int, ids.length = n.toNat ∧ ids.Nodup ∧ ∀ id ∈ ids, DeadAt σ' id)
      (fun σ mm mb mk hG => by
        iintro ⟨⟨%ids, %hlen, HD⟩, Hmi, -⟩
        ihave H1 : iprop(⌜∀ id ∈ ids, DeadAt σ id⌝ ∗ metaInterp (GF := GF) mm) $$ [Hmi HD]
        · iapply deadRegions_dead hG ids
          isplitl [Hmi]
          · iexact Hmi
          · iexact HD
        icases H1 with ⟨%hdead, -⟩
        ipureintro
        exact ⟨rfl, ids, hlen.1, hlen.2, hdead⟩)
  iintro ⟨%hw, HD⟩
  subst hw
  iapply haux
  iexact HD

end MlReadout

/-! ## THE TOTAL LANE: the variant weighs building over freeing -/

/-- The derived per-label-entry step budget at counter `i` and list
    length `k`: a build step costs 12 (guard 1 + alloc 2 + two stores
    4 + 4 + jump 1) and turns one unit of `i` into one node, so `i`
    weighs 25 = 12 + 13; a free step costs 13 (guard 1 + null test 3 +
    if 1 + load 4 + free 3 + jump 1); exit 6 (guard 1 + null test 3 + if
    1 + unit 1). -/
def mlCost (i k : Nat) : Nat := 25 * i + 13 * k + 6

section MlTotal

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (mo : memory_order) (al : Int) (pref : prefix0)
  (ibty pbty qbty bbty nbty ubty : core_base_type) (n : Int)
variable (p : sym) (rs : core_run_state)
  (hQ : LabeledAt rs p (mlQ loc ann ra mo al pref ibty pbty qbty bbty nbty ubty))

/-- The variant-indexed label context: the invariant plus the variant
    pin `m = mlCost i.toNat ids.length`. -/
abbrev mlLsT : LabelSpecT GF := fun _ m args ρ =>
  iprop(∃ (i : Int) (pc : CerbMem.PointerValue) (ids done : List Int)
      (f : Fmap sym value) (renv : List (Fmap sym value)),
    ⌜args = [ivVal i, ptrVal pc] ∧ 0 ≤ i ∧ m = mlCost i.toNat ids.length ∧
      i.toNat + ids.length + done.length = n.toNat ∧ (ids ++ done).Nodup ∧
      ρ = f :: renv ∧ SymFrame f⌝ ∗
    allocBudget (i.toNat * regionCost al 16) ∗ isRegionList pc ids ∗ deadRegions done)

include hQ

theorem ml_body_wpt (i : Int) (pc : CerbMem.PointerValue) (ids done : List Int)
    (f : Fmap sym value) (renv : List (Fmap sym value)) (hf : SymFrame f)
    (hi : 0 ≤ i) (hcnt : i.toNat + ids.length + done.length = n.toNat)
    (hnd : (ids ++ done).Nodup) :
    iprop(allocBudget (GF := GF) (i.toNat * regionCost al 16) ∗
        isRegionList pc ids ∗ deadRegions done) ⊢
      wpt (procCtx p rs) (mlLsT al n) (mlCost i.toNat ids.length) (mlPost n)
        (mlBody loc ann ra mo al pref qbty bbty nbty ubty)
        (mlFrame (ivVal i) (ptrVal pc) f :: renv) := by
  rw [show mlBody loc ann ra mo al pref qbty bbty nbty ubty =
    Expr [] (Eif mlGuardPe (mlBuild loc ann ra mo al pref qbty ubty)
      (mlFree loc ann ra mo bbty nbty ubty)) from rfl]
  iintro ⟨Hcap, HL, HD⟩
  by_cases hpos : 0 < i
  · -- BUILD
    rw [show mlCost i.toNat ids.length =
      (2 + ((3 + 1) + ((3 + 1) + (1 + mlCost (i - 1).toNat (ids.length + 1))))) + 1 from by
        unfold mlCost
        have : i.toNat = (i - 1).toNat + 1 := by omega
        omega]
    iapply wpt_if_true [] mlGuardPe _ _ _
      (by rw [procCtx_extern, ml_guard_eval hf renv _ i, decide_eq_true hpos]; rfl)
    rw [show mlBuild loc ann ra mo al pref qbty ubty =
      Expr [] (Esseq (symPat [] mlQSym qbty) (mlAllocE loc ann al pref)
        (Expr [] (Esseq (Pattern [] (CaseBase (none, ubty))) (mlStoreValE loc ann mo)
          (Expr [] (Esseq (Pattern [] (CaseBase (none, ubty))) (mlStoreNextE loc ann mo)
            (Expr [] (Erun ra mlLoopSym [mlDecPe, Pexpr [] () (PEsym mlQSym)]))))))) from rfl]
    rw [show i.toNat * regionCost al 16 =
      regionCost al 16 + (i - 1).toNat * regionCost al 16 from by
        have : i.toNat = (i - 1).toNat + 1 := by omega
        rw [this, Nat.add_mul, Nat.one_mul, Nat.add_comm]]
    icases (allocBudget_split _ _).1 $$ Hcap with ⟨Hc, Hrest⟩
    ihave HL2 := keep_pure (isRegionList_wf pc ids) $$ HL
    icases HL2 with ⟨%hwf, HL⟩
    iapply wpt_seq_sym
    rw [show mlAllocE loc ann al pref =
      allocExpr loc ann (.IV .Prov_none al) (.IV .Prov_none 16) pref from rfl]
    iapply wpt_alloc loc ann .Prov_none .Prov_none al 16 pref _ (Nat.le_refl 2)
      (regionCost_pos al 16 (by decide))
    isplitl [Hc]
    · iexact Hc
    iintro %id %a ⟨Hr, %hb⟩
    have ha1 : a < 2 ^ 64 := by
      have h := hb.2
      have e : ((Int.toNat (16 : Int) : Nat) : Int) = 16 := rfl
      omega
    ihave Hr16 : regionOwn id a 16 (.own 1) regionUndef16 $$ [Hr]
    · iapply regionOwn_alloc16 id a
      iexact Hr
    -- the fresh node is distinct from every live node and every dead one
    ihave HX : iprop(⌜id ∉ ids⌝ ∗ (regionOwn (GF := GF) id a 16 (.own 1) regionUndef16 ∗
        isRegionList pc ids)) $$ [Hr16 HL]
    · iapply keep_pure (regionOwn_isRegionList_ne id a regionUndef16 pc ids)
      isplitl [Hr16]
      · iexact Hr16
      · iexact HL
    icases HX with ⟨%hnotin, Hr16, HL⟩
    ihave HY : iprop(⌜id ∉ done⌝ ∗ (regionOwn (GF := GF) id a 16 (.own 1) regionUndef16 ∗
        deadRegions done)) $$ [Hr16 HD]
    · iapply keep_pure (regionOwn_deadRegions_ne id a regionUndef16 done)
      isplitl [Hr16]
      · iexact Hr16
      · iexact HD
    icases HY with ⟨%hnotin', Hr16, HD⟩
    iexists (Vobject (OVpointer (cellPtr id a)))
    isplit
    · ipureintro
      rfl
    rw [update_env_sym mlQSym qbty]
    rw [show envAdd mlQSym (Vobject (OVpointer (cellPtr id a))) (mlFrame (ivVal i) (ptrVal pc) f) =
      mlFrameQ (ptrVal (cellPtr id a)) (ivVal i) (ptrVal pc) f from rfl]
    -- store 1: the value field
    iapply wpt_seq
    rw [show mlStoreValE loc ann mo = storeOpRedex loc ann longTy
      (Pexpr [] () (PEsym mlQSym)) (Pexpr [] () (PEsym mlISym)) mo from rfl]
    iapply wpt_store_eval loc ann longTy _ _ mo _ rfl
      (pv := cellPtr id a) (cv := ivVal i)
      (by rw [procCtx_extern]; exact ml_q_eval hf renv _ _ _)
      (by rw [procCtx_extern]; exact ml_i_eval_Q hf renv _ _ _)
    rw [show (storeExpr loc ann longTy (cellPtr id a) (ivVal i) mo : CoreExpr) =
      storeExpr loc ann longTy (cellPtr id (a + ((0 : Nat) : Int))) (ivVal i) mo from by
      rw [show a + ((0 : Nat) : Int) = a from by omega]]
    iapply wpt_store_regionOwn_at (mv := longMval i) loc ann id a 16 0 longTy (ivVal i) mo _ _
      (Nat.le_refl 3) (longMval_encodes i)
      (by rw [show CerbMem.sizeofCtype (procCtx p rs).tagDefs longTy = 8 from rfl]; omega)
      (longMval_storable i)
    isplitl [Hr16]
    · iexact Hr16
    iintro %fp1 Hr
    -- store 2: the link
    iapply wpt_seq
    rw [show mlStoreNextE loc ann mo = storeOpRedex loc ann nodePtrTy
      (lrShiftPe mlQSym) (Pexpr [] () (PEsym mlPSym)) mo from rfl]
    iapply wpt_store_eval loc ann nodePtrTy _ _ mo _ rfl
      (pv := cellPtr id (a + 8)) (cv := ptrVal pc)
      (by rw [procCtx_extern]; exact ml_shift_q_eval hf renv _ _ id a)
      (by rw [procCtx_extern]; exact ml_p_eval_Q hf renv _ _ _)
    rw [show cellPtr id (a + 8) = cellPtr id (a + ((8 : Nat) : Int)) from rfl]
    iapply wpt_store_regionOwn_at (mv := CerbMem.pointerMval nodeTy pc) loc ann id a 16 8
      nodePtrTy (ptrVal pc) mo _ _ (Nat.le_refl 3) (node_ptr_encodes pc)
      (by rw [show CerbMem.sizeofCtype (procCtx p rs).tagDefs nodePtrTy = 8 from rfl]; omega)
      (nodePtr_storable hwf)
    isplitl [Hr]
    · iexact Hr
    iintro %fp2 Hr
    -- the jump
    iapply wpt_run [] ra mlLoopSym [mlDecPe, Pexpr [] () (PEsym mlQSym)] _ _
      (mlCost (i - 1).toNat (ids.length + 1))
      (by rw [procCtx_labels hQ]
          exact mlQ_lookup loc ann ra mo al pref ibty pbty qbty bbty nbty ubty)
      (ml_args_build_eval hf renv _ i _)
      (Nat.le_refl _)
    iexists (i - 1), (cellPtr id a), (id :: ids), done,
      (mlFrameQ (ptrVal (cellPtr id a)) (ivVal i) (ptrVal pc) f), renv
    isplit
    · ipureintro
      refine ⟨rfl, by omega, rfl, ?_, ?_, rfl, mlFrameQ_symFrame hf _ _ _⟩
      · simp only [List.length_cons]
        omega
      · rw [List.cons_append]
        exact List.nodup_cons.mpr ⟨List.not_mem_append hnotin hnotin', hnd⟩
    isplitl [Hrest]
    · iexact Hrest
    isplitl [Hr HL]
    · iapply isRegionList_cons_intro id a pc (mlBuilt i pc) ids hb.1 ha1
        (mlBuilt_len i hwf) (mlBuilt_nextDec i hwf)
      isplitl [Hr]
      · iexact Hr
      · iexact HL
    · iexact HD
  · -- FREE: i = 0
    have hi0 : i = 0 := by omega
    subst hi0
    rw [show mlFree loc ann ra mo bbty nbty ubty =
      Expr [] (Esseq (symPat [] mlBSym bbty) mlMemopE
        (Expr [] (Eif (Pexpr [] () (PEsym mlBSym)) (ofVal (.pure Vunit))
          (Expr [] (Esseq (specPat [] [] mlNSym nbty) (mlLoadE loc ann mo)
            (Expr [] (Esseq (Pattern [] (CaseBase (none, ubty))) (mlFreeE loc ann)
              (Expr [] (Erun ra mlLoopSym
                [Pexpr [] () (PEval (ivVal 0)), Pexpr [] () (PEsym mlNSym)]))))))))) from rfl]
    cases ids with
    | nil =>
      rw [show mlCost (Int.toNat 0) [].length = (3 + (1 + 1)) + 1 from rfl]
      iapply wpt_if_false [] mlGuardPe _ _ _
        (by rw [procCtx_extern, ml_guard_eval hf renv _ 0]; rfl)
      rw [isRegionList_nil]
      icases HL with %hnull
      subst hnull
      iapply wpt_seq_sym
      rw [show mlMemopE = memopRedex PtrEq
        [Pexpr [] () (PEsym mlPSym), Pexpr [] () (PEval nullVal)] from rfl]
      iapply wpt_memop_eval PtrEq _ _ _
        ml_memop_operands_nonvalue (ml_p_eval hf renv _ _) rfl
      rw [show memopRedex PtrEq [Pexpr [] () (PEval (ptrVal nullNode)),
          Pexpr [] () (PEval nullVal)] =
        memopPtrEqVals (Vobject (OVpointer nullNode))
          (Vobject (OVpointer nullNode)) from rfl]
      iapply wpt_memop_ptreq nullNode nullNode _ (Nat.le_refl 2)
        (fun σ => eqPtrval_null_null nodeTy nodeTy σ)
      iexists (boolValue true)
      isplit
      · ipureintro
        rfl
      rw [bindSym_ml]
      iapply wpt_if_true [] (Pexpr [] () (PEsym mlBSym)) _ _ _
        (by rw [procCtx_extern, ml_b_eval hf renv (boolValue true) _ _]; rfl)
      iapply wpt_ofVal (SpikeVal.pure Vunit) _ (Nat.le_refl 1)
      isplit
      · ipureintro
        rfl
      iexists done
      isplit
      · ipureintro
        simp only [List.length_nil] at hcnt
        rw [List.nil_append] at hnd
        exact ⟨by omega, hnd⟩
      · iexact HD
    | cons id ids =>
      rw [show mlCost (Int.toNat 0) (id :: ids).length =
        (3 + (((3 + 1) + ((2 + 1) + (1 + mlCost (Int.toNat 0) ids.length))) + 1)) + 1 from by
          unfold mlCost
          simp only [List.length_cons]
          omega]
      iapply wpt_if_false [] mlGuardPe _ _ _
        (by rw [procCtx_extern, ml_guard_eval hf renv _ 0]; rfl)
      rw [isRegionList_cons]
      icases HL with ⟨%aN, %q, %bs, %hfacts, Hr, HT⟩
      obtain ⟨rfl, h0, h1, hlen, hnext⟩ := hfacts
      iapply wpt_seq_sym
      rw [show mlMemopE = memopRedex PtrEq
        [Pexpr [] () (PEsym mlPSym), Pexpr [] () (PEval nullVal)] from rfl]
      iapply wpt_memop_eval PtrEq _ _ _
        ml_memop_operands_nonvalue (ml_p_eval hf renv _ _) rfl
      rw [show memopRedex PtrEq [Pexpr [] () (PEval (ptrVal (cellPtr id aN))),
          Pexpr [] () (PEval nullVal)] =
        memopPtrEqVals (Vobject (OVpointer (cellPtr id aN)))
          (Vobject (OVpointer nullNode)) from rfl]
      iapply wpt_memop_ptreq (cellPtr id aN) nullNode _ (Nat.le_refl 2)
        (fun σ => eqPtrval_cell_null id aN nodeTy σ)
      iexists (boolValue false)
      isplit
      · ipureintro
        rfl
      rw [bindSym_ml]
      iapply wpt_if_false [] (Pexpr [] () (PEsym mlBSym)) _ _ _
        (by rw [procCtx_extern, ml_b_eval hf renv (boolValue false) _ _]; rfl)
      iapply wpt_seq_spec
      rw [show mlLoadE loc ann mo =
        loadOpRedex loc ann nodePtrTy (lrShiftPe mlPSym) mo from rfl]
      iapply wpt_load_eval loc ann nodePtrTy (lrShiftPe mlPSym) mo _
        rfl (by rw [procCtx_extern]; exact ml_shift_p_eval_B hf renv _ _ id aN)
      rw [show cellPtr id (aN + 8) = cellPtr id (aN + ((8 : Nat) : Int)) from rfl]
      iapply wpt_load_regionOwn_at (M := procCtx p rs) loc ann id aN 16 8 nodePtrTy mo
        (.own 1) bs _ (Nat.le_refl 3)
        (by rw [show CerbMem.sizeofCtype (procCtx p rs).tagDefs nodePtrTy = 8 from rfl]; omega)
        (fun lum fpm => hnext lum fpm _)
        rfl
      isplitl [Hr]
      · iexact Hr
      iintro %fp Hr
      iexists (OVpointer q)
      isplit
      · ipureintro
        show (valueFromMemValue (.MVpointer nodeTy q)).2 = _
        rw [valueFromMemValue_ptr]
      rw [update_env_spec]
      rw [show envAdd mlNSym (Vobject (OVpointer q))
          (mlFrameB (boolValue false) (ivVal 0) (ptrVal (cellPtr id aN)) f) =
        mlFrameN (ptrVal q) (boolValue false) (ivVal 0) (ptrVal (cellPtr id aN)) f from rfl]
      iapply wpt_seq
      rw [show mlFreeE loc ann = killOpRedex loc ann Dynamic0
        (Pexpr [] () (PEsym mlPSym)) from rfl]
      iapply wpt_kill_eval loc ann Dynamic0 _ _ rfl (pv := cellPtr id aN)
        (by rw [procCtx_extern]; exact ml_p_eval_N hf renv _ _ _ _)
      iapply wpt_free loc ann Dynamic0 id aN 16 bs _ (Nat.le_refl 2) rfl
      isplitl [Hr]
      · iexact Hr
      iintro Hd
      iapply wpt_run [] ra mlLoopSym
        [Pexpr [] () (PEval (ivVal 0)), Pexpr [] () (PEsym mlNSym)] _ _
        (mlCost (Int.toNat 0) ids.length)
        (by rw [procCtx_labels hQ]
            exact mlQ_lookup loc ann ra mo al pref ibty pbty qbty bbty nbty ubty)
        (ml_args_free_eval hf renv _ _ _ _)
        (Nat.le_refl _)
      iexists 0, q, ids, (id :: done),
        (mlFrameN (ptrVal q) (boolValue false) (ivVal 0) (ptrVal (cellPtr id aN)) f), renv
      isplit
      · ipureintro
        refine ⟨rfl, Int.le_refl 0, rfl, ?_, ?_, rfl, mlFrameN_symFrame hf _ _ _ _⟩
        · simp only [List.length_cons] at hcnt ⊢
          omega
        · -- the freed head moves from the live list to the dead one
          exact (List.pairwise_middle (fun h => Ne.symm h)).mpr hnd
      isplitl [Hcap]
      · iexact Hcap
      isplitl [HT]
      · iexact HT
      · rw [deadRegions_cons]
        isplitl [Hd]
        · iexists aN
          iexact Hd
        · iexact HD

/-- THE TOTAL BLOCK SPECIFICATION. -/
theorem ml_blockSpecsT :
    ⊢ blockSpecsT (GF := GF) (procCtx p rs) (mlLsT al n) (mlPost n) := by
  refine blockSpecsT_intro fun l params cont args env0 envs m hl => ?_
  rw [procCtx_labels hQ] at hl
  obtain ⟨rfl, rfl⟩ := mlQ_inv loc ann ra mo al pref ibty pbty qbty bbty nbty ubty hl
  iintro ⟨%i, %pc, %ids, %done, %f, %renv, %hpure, Hcap, HL, HD⟩
  obtain ⟨rfl, hi, rfl, hcnt, hnd, hρ, hf⟩ := hpure
  obtain ⟨rfl, rfl⟩ : f = env0 ∧ renv = envs := by
    have h1 := congrArg (fun l => l.head?) hρ
    have h2 := congrArg (fun l => l.tail) hρ
    simp at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  rw [bindArgs_ml]
  iapply ml_body_wpt loc ann ra mo al pref ibty pbty qbty bbty nbty ubty n p rs hQ
    i pc ids done f renv hf hi hcnt hnd
  isplitl [Hcap]
  · iexact Hcap
  isplitl [HL]
  · iexact HL
  · iexact HD

/-- THE MALLOC'D LIST (total), at budget `mlCost n.toNat 0 + 1 = 25·n + 7`. -/
theorem ml_wpt (sbty : core_base_type) (hn : 0 ≤ n) :
    allocBudget (GF := GF) (n.toNat * regionCost al 16) ⊢
      wpt (procCtx p rs) (mlLsT al n) (mlCost n.toNat 0 + 1) (mlPost n)
        (mlProg loc ann ra mo al pref sbty ibty pbty qbty bbty nbty ubty n) [fmapEmpty] := by
  rw [show mlProg loc ann ra mo al pref sbty ibty pbty qbty bbty nbty ubty n =
    Expr [] (Esave (mlLoopSym, sbty) (mlParams ibty pbty n)
      (mlBody loc ann ra mo al pref qbty bbty nbty ubty)) from rfl]
  iintro Hcap
  iapply wpt_save_vals [] (mlLoopSym, sbty) _ _ fmapEmpty [] (cvals := [ivVal n, nullVal]) rfl
  rw [bindSave_ml]
  rw [show (nullVal : value) = ptrVal nullNode from rfl]
  rw [show mlCost n.toNat 0 = mlCost n.toNat ([] : List Int).length from rfl]
  iapply ml_body_wpt loc ann ra mo al pref ibty pbty qbty bbty nbty ubty n p rs hQ n
    nullNode [] [] fmapEmpty [] symFrame_empty hn (by simp) (by simp)
  isplitl [Hcap]
  · iexact Hcap
  isplitl []
  · rw [isRegionList_nil]
    ipureintro
    rfl
  · rw [deadRegions_nil]
    itrivial

end MlTotal

section MlTotalLC

variable {GF : BundledGFunctors} [SpikeGS .hasLC GF]
variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (mo : memory_order) (al : Int) (pref : prefix0)
  (ibty pbty qbty bbty nbty ubty : core_base_type) (n : Int)
variable (p : sym) (rs : core_run_state)
  (hQ : LabeledAt rs p (mlQ loc ann ra mo al pref ibty pbty qbty bbty nbty ubty))

include hQ

/-- The engine-facing postcondition: unit, and `n.toNat` DISTINCT dead ids. -/
abbrev ψML : value → Mem → Prop := fun v σ' =>
  v = Vunit ∧ ∃ ids : List Int, ids.length = n.toNat ∧ ids.Nodup ∧ ∀ id ∈ ids, DeadAt σ' id

/-- The block specifications at the engine readout (what the launches consume). -/
theorem ml_blockSpecsT_readout :
    ⊢ blockSpecsT (GF := GF) (procCtx p rs) (mlLsT al n) (readoutPost (ψML n)) :=
  (ml_blockSpecsT loc ann ra mo al pref ibty pbty qbty bbty nbty ubty n p rs hQ).trans
    (blockSpecsT_mono (mlPost_readout n))

/-- The whole program at the engine readout. -/
theorem ml_wpt_readout (sbty : core_base_type) (hn : 0 ≤ n) :
    allocBudget (GF := GF) (n.toNat * regionCost al 16) ⊢
      wpt (procCtx p rs) (mlLsT al n) (mlCost n.toNat 0 + 1) (readoutPost (ψML n))
        (mlProg loc ann ra mo al pref sbty ibty pbty qbty bbty nbty ubty n) [fmapEmpty] :=
  (ml_wpt loc ann ra mo al pref ibty pbty qbty bbty nbty ubty n p rs hQ sbty hn).trans
    (wpt_mono (mlPost_readout n) _ _ _)

end MlTotalLC

section MlExport

variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (mo : memory_order) (al : Int) (pref : prefix0)
  (sbty ibty pbty qbty bbty nbty ubty : core_base_type)

/-- THE MALLOC'D LIST, THE UNCONDITIONAL TOTAL ENGINE EQUATION: from any
    memory that launches the empty footprint with the budget `n.toNat *
    regionCost al 16` (`LaunchCoh`), the engine's `driveU` at the DERIVED
    bound `25·n.toNat + 7` DELIVERS `Vunit` and the final memory has
    `n.toNat` DISTINCT allocation ids in `deadAllocations` with their
    records erased — `n` nodes allocated, written, linked, walked and freed, no
    out-of-memory kill. A corollary of the total judgment through the
    generic simulation (`wpt_engine_boundU_alloc`). PROVISIONAL: stated
    over `driveU`. -/
theorem malloc_list_certified_total (n : Int) (hn : 0 ≤ n) (σ₀ : Mem)
    (hl : LaunchCoh fmapEmpty σ₀ (∅ : SpikeHeapF SpikeCell) (n.toNat * regionCost al 16))
    (aids : Nat → Nat) :
    ∃ σ' : Mem,
      driveU (procCtx mlProcSym (mlRS loc ann ra mo al pref ibty pbty qbty bbty nbty ubty)) aids
        (25 * n.toNat + 7)
        (procThread mlProcSym
          (mlProg loc ann ra mo al pref sbty ibty pbty qbty bbty nbty ubty n) [fmapEmpty]) σ₀ =
        .done Vunit σ' ∧
      ∃ ids : List Int, ids.length = n.toNat ∧ ids.Nodup ∧
        ∀ id ∈ ids, σ'.deadAllocations.contains id = true ∧ σ'.allocations.get? id = none := by
  have hQ := mlRS_labeledAt loc ann ra mo al pref ibty pbty qbty bbty nbty ubty
  have hk : mlCost n.toNat 0 + 1 = 25 * n.toNat + 7 := by
    unfold mlCost
    omega
  rw [← hk]
  have hlbl := procCtx_labels hQ
  obtain ⟨v, σ', hdone, ⟨rfl, hdead⟩, -⟩ :=
    wpt_engine_boundU_alloc (GF := SpikeGF)
      (M := procCtx mlProcSym (mlRS loc ann ra mo al pref ibty pbty qbty bbty nbty ubty))
      (procCtx_wf _ _)
      (fun l params cont hl => by
        rw [hlbl] at hl
        obtain ⟨-, rfl⟩ := mlQ_inv loc ann ra mo al pref ibty pbty qbty bbty nbty ubty hl
        exact mlBody_frag loc ann ra mo al pref qbty bbty nbty ubty)
      (fun l params cont hl => by
        rw [hlbl] at hl
        obtain ⟨-, rfl⟩ := mlQ_inv loc ann ra mo al pref ibty pbty qbty bbty nbty ubty hl
        rw [mlBody_pot, show lemDefaultFuel = 999999 + 1 from rfl]
        omega)
      (mlLsT al n)
      (mlProg loc ann ra mo al pref sbty ibty pbty qbty bbty nbty ubty n)
      fmapEmpty [] σ₀ (∅ : SpikeHeapF SpikeCell) (n.toNat * regionCost al 16)
      (.save (saveParams_pure_of_vals rfl) (saveParams_depth_of_vals rfl)
        (mlBody_frag loc ann ra mo al pref qbty bbty nbty ubty))
      (by rw [mlProg_pot, show lemDefaultFuel = 999999 + 1 from rfl]; omega)
      hl
      (ψML n)
      (mlCost n.toNat 0 + 1)
      (by
        intro inst
        iintro ⟨-, Hcap⟩
        isplitr [Hcap]
        · iapply ml_blockSpecsT_readout loc ann ra mo al pref ibty pbty qbty bbty nbty ubty n
            mlProcSym (mlRS loc ann ra mo al pref ibty pbty qbty bbty nbty ubty) hQ
        · iapply ml_wpt_readout loc ann ra mo al pref ibty pbty qbty bbty nbty ubty n
            mlProcSym (mlRS loc ann ra mo al pref ibty pbty qbty bbty nbty ubty) hQ sbty hn
            $$ Hcap)
      aids
  exact ⟨σ', hdone, hdead⟩

/-! ### Registration and the production statement -/

/-- The shipped registration computes the loop's label map (the save is
    the registration site and the entry). -/
theorem collect_new_ml (n : Int) :
    collect_labeled_continuations_NEW
        (prodFile (mlProg loc0 empty_annotation ra mo al pref sbty ibty pbty qbty bbty nbty
          ubty n)) =
      fmapAddBy (fun (s1 s2 : sym) => ordCompare s1 s2) mainSym
        (mlQ loc0 empty_annotation ra mo al pref ibty pbty qbty bbty nbty ubty) fmapEmpty := rfl

theorem ml_labeledAt (sup : Nat) (n : Int) :
    LabeledAt ((initial_core_run_state sup (collect_labeled_continuations_NEW
        (prodFile (mlProg loc0 empty_annotation ra mo al pref sbty ibty pbty qbty bbty nbty
          ubty n)))).1)
      mainSym (mlQ loc0 empty_annotation ra mo al pref ibty pbty qbty bbty nbty ubty) := by
  unfold LabeledAt
  rw [show ((initial_core_run_state sup (collect_labeled_continuations_NEW
      (prodFile (mlProg loc0 empty_annotation ra mo al pref sbty ibty pbty qbty bbty nbty
        ubty n)))).1).labeled =
    collect_labeled_continuations_NEW
      (prodFile (mlProg loc0 empty_annotation ra mo al pref sbty ibty pbty qbty bbty nbty
        ubty n))
    from rfl]
  rw [collect_new_ml]
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

/-- The budget side condition in ENGINE vocabulary equals the package's
    (`regionCost al 16 = 15 + max al.toNat 1` per node; `headroom
    prodMem₀.lastAddress = 281474976710647`). -/
theorem ml_budget_bridge (n : Int)
    (hB : n.toNat * (15 + max al.toNat 1) ≤ 281474976710647) :
    n.toNat * regionCost al 16 ≤ headroom prodMem₀.lastAddress := by
  rw [prodMem₀_lastAddress]
  have h1 : regionCost al 16 = 15 + max al.toNat 1 := by
    unfold regionCost
    show 16 + max al.toNat 1 - 1 = 15 + max al.toNat 1
    omega
  rw [h1]
  exact hB

/-- THE MALLOC'D LIST, PRODUCTION FORM: running the SHIPPED pipeline
    cold on the self-contained file is EXACTLY ONE Active execution
    delivering `Vunit` whose final memory has `n.toNat` DISTINCT
    allocation ids in `deadAllocations` with their records erased (`killM`'s effect,
    CerbMem.lean:1576-1578) — every `alloc` through the PUBLIC
    `wpt_alloc` from the split budget, every field write through the
    PUBLIC `wpt_store_regionOwn_at`, every next-field read through the
    PUBLIC `wpt_load_regionOwn_at`, every `free` through the PUBLIC
    `wpt_free`. The proof witnesses the dead ids as the freed nodes; the
    statement names no node. Premises: the budget fits the cold start, in
    ENGINE vocabulary (`hB`: per node `16 + max(al, 1) − 1` bytes of
    cursor descent, `281474976710647 = headroom` of the cold-start
    cursor; the bridge to the package's `regionCost`/`headroom` is
    `ml_budget_bridge`), and the in-fuel bound on the certified step count
    (`hfuel`). Cold start, shipped registration, termination from the
    total judgment; the pipeline arrows are `wpt_driver_done_alloc` →
    `prod_run_eqJ`. -/
theorem malloc_list_certified_production (sup : Nat) (n : Int) (hn : 0 ≤ n)
    (hB : n.toNat * (15 + max al.toNat 1) ≤ 281474976710647)
    (hfuel : 25 * n.toNat + 9 ≤ CerbFuel.driverFuel)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND
          (_root_.drive fmapEmpty false
            (prodFile (mlProg loc0 empty_annotation ra mo al pref sbty ibty pbty qbty bbty
              nbty ubty n))
            args)
          ((initial_driver_state sup
            (prodFile (mlProg loc0 empty_annotation ra mo al pref sbty ibty pbty qbty bbty
              nbty ubty n))
            fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = Vunit ∧
      (∃ ids : List Int, ids.length = n.toNat ∧ ids.Nodup ∧
        ∀ id ∈ ids, dst'.layout_state.deadAllocations.contains id = true ∧
          dst'.layout_state.allocations.get? id = none) ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
  have hQprod := ml_labeledAt ra mo al pref sbty ibty pbty qbty bbty nbty ubty sup n
  obtain ⟨dres, dst', heq, hψ, hbl, hout, herr⟩ :=
    prod_run_eqJ sup (mlProg loc0 empty_annotation ra mo al pref sbty ibty pbty qbty bbty
        nbty ubty n)
      hQprod (ψML n) (mlCost n.toNat 0 + 1)
      (wpt_driver_done_alloc (GF := SpikeGF)
        (M₀ := procCtx mainSym ((initial_core_run_state sup
          (collect_labeled_continuations_NEW
            (prodFile (mlProg loc0 empty_annotation ra mo al pref sbty ibty pbty qbty bbty
              nbty ubty n)))).1))
        rfl rfl (procCtx_labels hQprod) rfl rfl
        (fun l params cont hl => by
          rw [procCtx_labels hQprod] at hl
          obtain ⟨-, rfl⟩ := mlQ_inv loc0 empty_annotation ra mo al pref ibty pbty qbty bbty
            nbty ubty hl
          exact mlBody_frag loc0 empty_annotation ra mo al pref qbty bbty nbty ubty)
        (fun l params cont hl => by
          rw [procCtx_labels hQprod] at hl
          obtain ⟨-, rfl⟩ := mlQ_inv loc0 empty_annotation ra mo al pref ibty pbty qbty bbty
            nbty ubty hl
          rw [mlBody_pot, show lemDefaultFuel = 999999 + 1 from rfl]
          omega)
        (mlLsT al n)
        (mlProg loc0 empty_annotation ra mo al pref sbty ibty pbty qbty bbty nbty ubty n)
        fmapEmpty [] prodMem₀ (∅ : SpikeHeapF SpikeCell) (n.toNat * regionCost al 16)
        (.save (saveParams_pure_of_vals rfl) (saveParams_depth_of_vals rfl)
          (mlBody_frag loc0 empty_annotation ra mo al pref qbty bbty nbty ubty))
        (by rw [mlProg_pot, show lemDefaultFuel = 999999 + 1 from rfl]; omega)
        (prodMem₀_launchCoh _ (ml_budget_bridge al n hB))
        (ψML n)
        (mlCost n.toNat 0 + 1)
        (by
          intro inst
          iintro ⟨-, Hcap⟩
          isplitr [Hcap]
          · iapply ml_blockSpecsT_readout loc0 empty_annotation ra mo al pref ibty pbty qbty
              bbty nbty ubty n mainSym _ hQprod
          · iapply ml_wpt_readout loc0 empty_annotation ra mo al pref ibty pbty qbty bbty
              nbty ubty n mainSym _ hQprod sbty hn $$ Hcap))
      (by unfold mlCost; omega)
      fs args
  obtain ⟨hv, ids, hlen, hnd, hdead⟩ := hψ
  exact ⟨dres, dst', heq, hv, ⟨ids, hlen, hnd, fun id hid => hdead id hid⟩, hbl, hout, herr⟩

end MlExport

end CerberusHeapLang
