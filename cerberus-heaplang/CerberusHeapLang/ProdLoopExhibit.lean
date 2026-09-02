/-
CerberusHeapLang.ProdLoopExhibit — THE PRODUCTION LOOP THEOREMS
(Phase 5; audit F-05 closed): loop programs certified as equations
about the SHIPPED pipeline

  CerbND.runND (Driver.drive tagDefs false file args)
               (initial_driver_state sup file fs).1

from the COLD START — `initial_driver_state` (Driver.lean:446), the
production state constructor, nothing hand-built in the quantifiers;
`sup` is the entry's symbol supply (the supply-threaded C1 shape),
universally quantified — the fragment never reads it. The execution
function in every public statement here is the shipped runner: no
package `drive`/`driveJ` appears in any statement (the drive-lane
theorems remain as lemmas in their exhibit modules).

Every theorem here is trio-exact, pinned in Audit.lean (the former
`runEffectful` boundary was retired at the 2026-09-02 re-pin).

THE PIPELINE THEOREM (`prod_run_eqJ`, ProdEntry): `drive_after_setup`
(the cold-start prefix: spawn, main lookup, errno block, park) + a
`DriverDoneAt` delivery fact (ProdLoop — the total judgment driving
the driver's own per-thread loop, jump rounds included) +
`driver2_done`/`finalize_done` (DriverCollapse). The label map the
driver reads is EXACTLY what the shipped registration computes
(`collect_labeled_continuations_NEW` over the synthetic file), so
nothing is hand-built in the label plumbing either.

PROOF CLASSIFICATION (alloc arc P2 steps 4-5 — the R-02 conversion):
ALL THREE exports are WHOLE-PROGRAM LOGIC PROOFS. The two
heap-allocating programs BIND their engine-created pointers (the P2
pointer-flow design record, docs/2026-09-01_p2-notes.md), their
creates cross the PUBLIC `wpt_create` from abstract capacity plans
(one-request for the counter, two-request for the reversal), their
field stores cross the generic typed-subrange rules at the bound
pointers, and the loops ride the total statement judgment — the
reversal consuming the GENERIC list logic verbatim at the
engine-picked (existential) allocation ids, transported by
`wpt_mono_Ls`. The pipeline arrows are the generic
`wpt_driver_done_alloc` → `prod_run_eqJ`; the former handwritten
certified operational rounds (`Step.sseq_ctx (Step.create …)` +
`driverDone_step` chains) are DELETED — every `Step.*`/
`engineSteps_*`/`driveJ_step`/`driverDone_step` mention left in this
module is documentation of that deletion.
-/
import CerberusHeapLang.Examples.Layout
import CerberusHeapLang.ProdEntry
import CerberusHeapLang.ProdExhibit
import CerberusHeapLang.ProdLoop
import CerberusHeapLang.ListRevExhibit

set_option autoImplicit false

namespace CerberusHeapLang

open Lem_Basic_classes Lem_Maybe Lem_List
open Iris Iris.BI Iris.ProgramLogic
open scoped Iris.Std.PartialMap

/-! ## FIB ON THE SHIPPED PIPELINE — the first production loop
theorem (audit acceptance test 6: "at least one loop theorem
concludes directly about the shipped runND (Driver.drive ...)
computation"). -/

/-- FIB, PRODUCTION FORM: running the SHIPPED pipeline cold on the
    synthetic one-procedure file wrapping the authored iterative-fib
    loop program is EXACTLY ONE Active execution delivering
    `fib n` — a back-edge loop through the production scheduler, the
    label map computed by the shipped registration, termination from
    the total statement judgment (no step-count hypothesis; the one
    bound is the engine's own fuel budget, `lemDefaultFuel = 10^6`).
    No package drive/driveJ in the statement: the execution function
    is the shipped runner. -/
theorem fib_certified_production (sup : Nat) (ra : core_run_annotation) (n : Int)
    (sbty ibty abty bbty : core_base_type) (hn : 0 ≤ n)
    (hfuel : 2 * n.toNat + 6 ≤ lemDefaultFuel)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND
          (_root_.drive fmapEmpty false
            (prodFile (fibProg ra n sbty ibty abty bbty)) args)
          ((initial_driver_state sup
            (prodFile (fibProg ra n sbty ibty abty bbty)) fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = ivVal (fibSpec n.toNat) ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
  have hQprod := fib_labeledAt_production sup ra n sbty ibty abty bbty
  have h := prod_run_eqJ sup (fibProg ra n sbty ibty abty bbty) hQprod
    (fun v _ => v = ivVal (fibSpec n.toNat)) (2 * n.toNat + 4)
    (wpt_driver_done (GF := SpikeGF)
      (M₀ := procCtx mainSym ((initial_core_run_state sup
        (collect_labeled_continuations_NEW
          (prodFile (fibProg ra n sbty ibty abty bbty)))).1))
      rfl rfl (procCtx_labels hQprod) rfl rfl
      (fun l params cont hl => by
        rw [procCtx_labels hQprod] at hl
        obtain ⟨-, rfl⟩ := fibQ_inv ra n ibty abty bbty hl
        exact fibBody_fragJ ra n)
      (fun l params cont hl => by
        rw [procCtx_labels hQprod] at hl
        obtain ⟨-, rfl⟩ := fibQ_inv ra n ibty abty bbty hl
        rw [fibBody_pot, show lemDefaultFuel = 999999 + 1 from rfl]
        omega)
      (fibLsT n)
      (fibProg ra n sbty ibty abty bbty) fmapEmpty []
      prodMem₀ (∅ : SpikeHeapF SpikeCell)
      (.save (saveParams_depth_of_vals rfl) (fibBody_fragJ ra n))
      (by rw [fibProg_pot, show lemDefaultFuel = 999999 + 1 from rfl]; omega)
      (coh_empty prodMem₀)
      (fun v _ => v = ivVal (fibSpec n.toNat)) (2 * n.toNat + 4)
      (by
        intro inst
        refine .trans (BigSepM.bigSepM_empty).1 ?_
        refine .trans BI.emp_sep.2 (BI.sep_mono ?_ ?_)
        · exact (fib_blockSpecsT ra n ibty abty bbty mainSym _
            hQprod).trans
            (blockSpecsT_mono (fibPost_to_readout n))
        · exact (fib_wpt ra n ibty abty bbty mainSym _
            hQprod hn sbty).trans
            (wpt_mono (fibPost_to_readout n) _ _ _)))
    (by omega) fs args
  obtain ⟨dres, dst', heq, hval, hbl, hout, herr⟩ := h
  exact ⟨dres, dst', heq, hval, hbl, hout, herr⟩

/-! ## THE COUNTER LOOP ON THE SHIPPED PIPELINE — a HEAP-EFFECTING
loop from the cold start, WHOLE-PROGRAM LOGIC PROOF (alloc arc P2
step 4; the R-02 conversion). The program is SELF-CONTAINED and
BINDS its fresh cell (the P2 pointer-flow design record,
docs/2026-09-01_p2-notes.md): `lets p = create(4, int)`, then the
loop is ENTERED THROUGH ITS `save` with live-variable initializers,
`save loop(x := n, c := p) in …` (QA-1/H-1: the engine's Esave EVAL
arm evaluates `p` at entry — `wpt_save` at `evalPexprs … = some
cvals`), carrying the counter AND the bound pointer as loop
parameters; each iteration stores the constant 7 directly through the
POINTER PARAMETER, `store(int, c, 7)` (the mixed operand shape). The
`save` node is both the REGISTRATION site the shipped
`collect_labeled_continuations_NEW` reads and the entry. The pre-QA-1
form (a dummy-initialized `save` in an untaken sseq arm, entry by
`run` from outside it, and a per-iteration `lets s = 7` bind because
the mirrored store-EVAL arm required non-value operands) is recorded
in docs/2026-09-02_qa1-notes.md. The create crosses the logic through
the PUBLIC `wpt_create` from the one-request plan; the whole program
is ONE total judgment collapsed by the generic
`wpt_driver_done_alloc` → `prod_run_eqJ` — no `Step.*`,
`engineSteps_*`, `driveJ_step` or `driverDone_step` anywhere in this
module. -/

def ctrLoopSym : sym := Symbol "" 521 SD_None
def ctrXSym : sym := Symbol "" 522 SD_None
def ctrCSym : sym := Symbol "" 523 SD_None
def ctrPSym : sym := Symbol "" 524 SD_None

/-- The guard `x > 0`. -/
def ctrGuardPe : generic_pexpr Unit sym :=
  Pexpr [] () (PEop binop.OpGt (Pexpr [] () (PEsym ctrXSym))
    (Pexpr [] () (PEval (ivVal 0))))

/-- The back-edge argument `x - 1`. -/
def ctrDecPe : generic_pexpr Unit sym :=
  Pexpr [] () (PEop binop.OpSub (Pexpr [] () (PEsym ctrXSym))
    (Pexpr [] () (PEval (ivVal 1))))

/-- The registered loop body: `if x > 0 then (store(int, c, 7);
    run loop(x - 1, c)) else unit` — the constant stored directly
    through the pointer PARAMETER, the back edge re-passing it. -/
def ctrBody (ra : core_run_annotation) (mo : memory_order)
    (bty : core_base_type) : CoreExpr :=
  Expr [] (Eif ctrGuardPe
    (Expr [] (Esseq (Pattern [] (CaseBase (none, bty)))
      (storeOpRedex loc0 empty_annotation intTy
        (Pexpr [] () (PEsym ctrCSym)) (Pexpr [] () (PEval sevenVal)) mo)
      (Expr [] (Erun ra ctrLoopSym
        [ctrDecPe, Pexpr [] () (PEsym ctrCSym)]))))
    (ofVal (.pure Vunit)))

/-- The loop's save parameters with their LIVE initializers:
    `x := n` (the literal count), `c := p` (the program-bound pointer). -/
def ctrParams (xbty cbty : core_base_type) (n : Int) :
    List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)) :=
  [(ctrXSym, ((xbty, (none : Option (ctype × pass_by_value_or_pointer))),
    Pexpr [] () (PEval (ivVal n)))),
   (ctrCSym, ((cbty, (none : Option (ctype × pass_by_value_or_pointer))),
    Pexpr [] () (PEsym ctrPSym)))]

/-- The whole self-contained program:
    `lets p = create(4, int) in save loop(x := n, c := p) in body`. -/
def counterProdProg (ra : core_run_annotation) (mo : memory_order)
    (bty xbty cbty sbty : core_base_type) (n : Int) : CoreExpr :=
  Expr [] (Esseq (symPat [] ctrPSym bty)
    (createExpr loc0 empty_annotation (.IV .Prov_none 4) intTy
      (PrefOther "spike-x"))
    (Expr [] (Esave (ctrLoopSym, sbty) (ctrParams xbty cbty n)
      (ctrBody ra mo bty))))

/-- The label map the shipped registration computes. -/
def ctrQ (ra : core_run_annotation) (mo : memory_order)
    (bty xbty cbty : core_base_type) : LabelMap :=
  fmapAddBy symCmpL ctrLoopSym
    ([(ctrXSym, xbty), (ctrCSym, cbty)], ctrBody ra mo bty) fmapEmpty

section CtrFacts

variable (ra : core_run_annotation) (mo : memory_order)
  (bty xbty cbty : core_base_type)

theorem ctrQ_lookup :
    lookupLabel (ctrQ ra mo bty xbty cbty) ctrLoopSym =
      some ([(ctrXSym, xbty), (ctrCSym, cbty)], ctrBody ra mo bty) := by
  unfold lookupLabel ctrQ
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

theorem ctrQ_inv {l : sym} {params : List (sym × core_base_type)}
    {cont : CoreExpr}
    (h : lookupLabel (ctrQ ra mo bty xbty cbty) l = some (params, cont)) :
    params = [(ctrXSym, xbty), (ctrCSym, cbty)] ∧
      cont = ctrBody ra mo bty := by
  unfold lookupLabel ctrQ at h
  rw [fmapLookupBy_addBy_empty] at h
  split at h
  · obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
    exact ⟨h1.symm ▸ rfl, h2.symm ▸ rfl⟩
  · cases h

end CtrFacts

/-! ### Frames and evaluation facts (SymFrame — the EnvLaws law) -/

/-- The frame after the loop bindings (x, c). -/
def ctrFrame (vx vc : value) (f : Fmap sym value) : Fmap sym value :=
  envAdd ctrCSym vc (envAdd ctrXSym vx f)

theorem ctrFrame_symFrame {f : Fmap sym value} (hf : SymFrame f)
    (vx vc : value) : SymFrame (ctrFrame vx vc f) :=
  (hf.add _ _).add _ _

theorem ctrFrame_lookup_x {f : Fmap sym value} (hf : SymFrame f)
    (vx vc : value) :
    fmapLookupBy symCmpK ctrXSym (ctrFrame vx vc f) = some vx := by
  unfold ctrFrame
  rw [envAdd_lookup (hf.add _ _) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup hf symCmpK, if_pos (by decide +kernel)]

theorem ctrFrame_lookup_c {f : Fmap sym value} (hf : SymFrame f)
    (vx vc : value) :
    fmapLookupBy symCmpK ctrCSym (ctrFrame vx vc f) = some vc := by
  unfold ctrFrame
  rw [envAdd_lookup (hf.add _ _) symCmpK, if_pos (by decide +kernel)]

theorem bindArgs_ctr (xbty cbty : core_base_type) (v1 v2 : value)
    (f : Fmap sym value) (rest : List (Fmap sym value)) :
    bindArgs [(ctrXSym, xbty), (ctrCSym, cbty)] [v1, v2] (f :: rest) =
      ctrFrame v1 v2 f :: rest := by
  show update_env (mk_sym_pat ctrCSym cbty) v2
    (update_env (mk_sym_pat ctrXSym xbty) v1 (f :: rest)) = _
  rw [update_env_cons, update_env_aux_sym, update_env_cons,
    update_env_aux_sym]
  rfl

/-- The save entry binds the parameters exactly as the jump does. -/
theorem bindSaveParams_ctr (xbty cbty : core_base_type) (n : Int)
    (v1 v2 : value) (f : Fmap sym value) (rest : List (Fmap sym value)) :
    bindSaveParams (ctrParams xbty cbty n) [v1, v2] (f :: rest) =
      ctrFrame v1 v2 f :: rest := by
  show update_env (mk_sym_pat ctrCSym cbty) v2
    (update_env (mk_sym_pat ctrXSym xbty) v1 (f :: rest)) = _
  rw [update_env_cons, update_env_aux_sym, update_env_cons,
    update_env_aux_sym]
  rfl

section CtrEval

variable {f : Fmap sym value} (hf : SymFrame f)
  (rest : List (Fmap sym value))

include hf

theorem ctr_guard_eval (i : Int) (vc : value) :
    evalPexpr fmapEmpty fmapEmpty (ctrFrame (ivVal i) vc f :: rest) ctrGuardPe =
      some (boolValue (decide (0 < i))) := by
  unfold ctrGuardPe
  rw [evalPexpr_op]
  rw [show evalPexpr fmapEmpty fmapEmpty (ctrFrame (ivVal i) vc f :: rest)
      (Pexpr [] () (PEsym ctrXSym)) = some (ivVal i) from by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (ctrFrame_lookup_x hf _ _) rest]
  show evalBinop binop.OpGt (ivVal i) (ivVal 0) = _
  unfold evalBinop ivVal
  show (CerbMem.ltIval (CerbMem.integerIval 0)
    (CerbMem.integerIval i)).map boolValue = _
  rfl

theorem ctr_store_ptr_eval (vx vc : value) :
    evalPexpr fmapEmpty fmapEmpty (ctrFrame vx vc f :: rest)
        (Pexpr [] () (PEsym ctrCSym)) = some vc := by
  rw [evalPexpr_sym_empty]
  exact lookup_env_head (ctrFrame_lookup_c hf _ _) rest

theorem ctr_backedge_args_eval (i : Int) (vc : value) :
    evalPexprs fmapEmpty fmapEmpty (ctrFrame (ivVal i) vc f :: rest)
        [ctrDecPe, Pexpr [] () (PEsym ctrCSym)] =
      some [ivVal (i - 1), vc] := by
  rw [evalPexprs_cons]
  rw [show evalPexpr fmapEmpty fmapEmpty (ctrFrame (ivVal i) vc f :: rest)
      ctrDecPe = some (ivVal (i - 1)) from by
    unfold ctrDecPe
    rw [evalPexpr_op]
    rw [show evalPexpr fmapEmpty fmapEmpty (ctrFrame (ivVal i) vc f :: rest)
        (Pexpr [] () (PEsym ctrXSym)) = some (ivVal i) from by
      rw [evalPexpr_sym_empty]
      exact lookup_env_head (ctrFrame_lookup_x hf _ _) rest]
    rfl]
  rw [evalPexprs_cons]
  rw [show evalPexpr fmapEmpty fmapEmpty (ctrFrame (ivVal i) vc f :: rest)
      (Pexpr [] () (PEsym ctrCSym)) = some vc from by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (ctrFrame_lookup_c hf _ _) rest]
  rfl

/-- The save's initializers evaluate at the entry env: the literal
    count and the program-bound pointer. -/
theorem ctr_save_params_eval (xbty cbty : core_base_type) (n : Int) (vp : value) :
    evalPexprs fmapEmpty fmapEmpty (envAdd ctrPSym vp f :: rest)
        (saveParamPexprs (ctrParams xbty cbty n)) =
      some [ivVal n, vp] := by
  show evalPexprs fmapEmpty fmapEmpty (envAdd ctrPSym vp f :: rest)
    [Pexpr [] () (PEval (ivVal n)), Pexpr [] () (PEsym ctrPSym)] = _
  rw [evalPexprs_cons, evalPexpr_val]
  rw [evalPexprs_cons]
  rw [show evalPexpr fmapEmpty fmapEmpty (envAdd ctrPSym vp f :: rest)
      (Pexpr [] () (PEsym ctrPSym)) = some vp from by
    rw [evalPexpr_sym_empty]
    refine lookup_env_head ?_ rest
    rw [envAdd_lookup hf symCmpK, if_pos (by decide +kernel)]]
  rfl

end CtrEval

/-! ### The total lane: variant-indexed invariant, per-body budget,
block specification, whole-program judgment -/

/-- The derived per-label-entry step budget at counter value i:
    if 1 + store-operand eval 1 + store 3 + jump 1 per iteration;
    if 1 + unit delivery 1 at exit. -/
def ctrCost : Nat → Nat
  | 0 => 2
  | i + 1 => 6 + ctrCost i

theorem ctrCost_eq (i : Nat) : ctrCost i = 6 * i + 2 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [show ctrCost (i + 1) = 6 + ctrCost i from rfl, ih]
    omega

/-- The engine-facing postcondition: unit delivered, the final
    memory holding the fresh cell (existential id/address) with its
    bytes decided by the loop's data — the untouched fresh image for
    `n = 0`, the stored seven-image for `0 < n`. -/
def ψC (n : Int) : value → Mem → Prop := fun v σ' =>
  v = Vunit ∧ ∃ (i a : Int) (bs : List CerbMem.AbsByte),
    ((n = 0 ∧ bs = (intUndefBytes fmapEmpty)) ∨ (0 < n ∧ bs = (sevenBytes fmapEmpty))) ∧
    CellCoh fmapEmpty σ' i ⟨a, intTy, bs⟩

section CtrIris

variable {GF : BundledGFunctors} [SpikeGS .hasLC GF]
variable (ra : core_run_annotation) (mo : memory_order)
  (bty xbty cbty : core_base_type) (n : Int)

/-- The variant-indexed label context: the counter and the POINTER
    ride the jump arguments (the invariant reads the cell from the
    argument — no example constant anywhere), the cell's bytes are
    data-pinned, the variant is the derived per-entry budget. -/
abbrev ctrLsT : LabelSpecT GF := fun _ m vs ρ =>
  iprop(∃ (i : Int) (pptr : CerbMem.PointerValue)
      (bs : List CerbMem.AbsByte) (f : Fmap sym value)
      (rest : List (Fmap sym value)),
    ⌜vs = [ivVal i, ptrVal pptr] ∧ 0 ≤ i ∧ i ≤ n ∧ m = ctrCost i.toNat ∧
      ρ = f :: rest ∧ SymFrame f ∧
      ((i = n ∧ bs = (intUndefBytes fmapEmpty)) ∨ (i < n ∧ bs = (sevenBytes fmapEmpty)))⌝ ∗
    pointsToCell fmapEmpty pptr (.own 1) intTy bs)

variable (p : sym) (rs : core_run_state)
  (hQ : LabeledAt rs p (ctrQ ra mo bty xbty cbty))

include hQ

/-- The loop body meets its variant budget at any invariant frame. -/
theorem ctr_body_wpt (i : Int) (pptr : CerbMem.PointerValue)
    (bs : List CerbMem.AbsByte) (f : Fmap sym value)
    (rest : List (Fmap sym value)) (hf : SymFrame f)
    (h0 : 0 ≤ i) (hin : i ≤ n)
    (hbs : (i = n ∧ bs = (intUndefBytes fmapEmpty)) ∨ (i < n ∧ bs = (sevenBytes (procCtx p rs).tagDefs))) :
    iprop(pointsToCell (procCtx p rs).tagDefs (GF := GF) pptr (.own 1) intTy bs) ⊢
      wpt (procCtx p rs) (ctrLsT n) (ctrCost i.toNat)
        (readoutPost (ψC n)) (ctrBody ra mo bty)
        (ctrFrame (ivVal i) (ptrVal pptr) f :: rest) := by
  rw [show ctrBody ra mo bty =
    Expr [] (Eif ctrGuardPe
      (Expr [] (Esseq (Pattern [] (CaseBase (none, bty)))
        (storeOpRedex loc0 empty_annotation intTy
          (Pexpr [] () (PEsym ctrCSym)) (Pexpr [] () (PEval sevenVal)) mo)
        (Expr [] (Erun ra ctrLoopSym
          [ctrDecPe, Pexpr [] () (PEsym ctrCSym)]))))
      (ofVal (.pure Vunit))) from rfl]
  iintro Hpt
  by_cases hpos : 0 < i
  · -- guard TRUE: store 7 through the parameter, jump smaller
    rw [show ctrCost i.toNat =
        ((3 + 1) + (1 + ctrCost (i - 1).toNat)) + 1 from by
      rw [show i.toNat = (i - 1).toNat + 1 from by omega]
      show 6 + ctrCost (i - 1).toNat = _
      omega]
    iapply wpt_if_true [] ctrGuardPe _ _ _
      (by rw [procCtx_extern, ctr_guard_eval hf rest i (ptrVal pptr),
        decide_eq_true hpos]; rfl)
    iapply wpt_seq
    iapply wpt_store_eval loc0 empty_annotation intTy _ _ mo _ rfl
      (pv := pptr) (cv := sevenVal)
      (by rw [procCtx_extern]
          exact ctr_store_ptr_eval hf rest (ivVal i) (ptrVal pptr))
      rfl
    iapply wpt_store_cell loc0 empty_annotation intTy pptr sevenVal mo
      sevenMval bs _ (Nat.le_refl 3) seven_encodes (seven_storable _)
    isplitl [Hpt]
    · iexact Hpt
    iintro %fp Hpt
    iapply wpt_run [] ra ctrLoopSym [ctrDecPe, Pexpr [] () (PEsym ctrCSym)]
      _ _ (ctrCost (i - 1).toNat)
      (by rw [procCtx_labels hQ]
          exact ctrQ_lookup ra mo bty xbty cbty)
      (by rw [procCtx_extern]
          exact ctr_backedge_args_eval hf rest i (ptrVal pptr))
      (Nat.le_refl _)
    iexists (i - 1), pptr, (CerbMem.memValueToBytes (procCtx p rs).tagDefs [] sevenMval).2,
      (ctrFrame (ivVal i) (ptrVal pptr) f), rest
    isplit
    · ipureintro
      refine ⟨rfl, by omega, by omega, rfl, rfl,
        ctrFrame_symFrame hf _ _, ?_⟩
      right
      exact ⟨by omega, rfl⟩
    · iexact Hpt
  · -- guard FALSE (i = 0): deliver unit with the final cell readout
    have hz : i = 0 := by omega
    subst hz
    rw [show ctrCost (0 : Int).toNat = 1 + 1 from rfl]
    iapply wpt_if_false [] ctrGuardPe _ _ _
      (by rw [procCtx_extern, ctr_guard_eval hf rest 0 (ptrVal pptr),
        decide_eq_false hpos]; rfl)
    iapply wpt_ofVal (.pure Vunit) _ (by simp [deliveryCost])
    icases (pointsToCell_cellOwn_iff (procCtx p rs).tagDefs _ _ _ _).mp $$ Hpt
      with ⟨%id, %a, %hpv, Hcell⟩
    iintro %σ' %ns %κs %nt Hσ
    icases (stateInterp_iff σ' ns κs nt).mp $$ Hσ
      with ⟨%mm, %mb, %mk, %HG, Hmi, Hbi, Hki⟩
    ihave %Hcc : ⌜CellCoh (procCtx p rs).tagDefs σ' id ⟨a, intTy, bs⟩ ∧
        Iris.Std.PartialMap.get? mm id = some (metaOf (procCtx p rs).tagDefs
          (⟨a, intTy, bs⟩ : SpikeCell))⌝ $$ [Hmi Hbi Hcell]
    · iapply cellOwn_cellCoh (procCtx p rs).tagDefs HG id (.own 1) ⟨a, intTy, bs⟩
        $$ [$Hmi $Hbi $Hcell]
    iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
    ipureintro
    refine ⟨rfl, id, a, bs, ?_, Hcc.1⟩
    rcases hbs with ⟨heq, rfl⟩ | ⟨hlt, rfl⟩
    · exact .inl ⟨heq.symm, rfl⟩
    · exact .inr ⟨hlt, rfl⟩

/-- THE TOTAL BLOCK SPECIFICATION for the production counter loop. -/
theorem ctr_blockSpecsT :
    ⊢ blockSpecsT (GF := GF) (procCtx p rs) (ctrLsT n)
      (readoutPost (ψC n)) := by
  refine blockSpecsT_intro fun l params cont vs ev0 evs m hl => ?_
  rw [procCtx_labels hQ] at hl
  obtain ⟨rfl, rfl⟩ := ctrQ_inv ra mo bty xbty cbty hl
  iintro ⟨%i, %pptr, %bs, %f, %rest, %hpure, Hpt⟩
  obtain ⟨rfl, h0, hin, rfl, hρ, hf, hbs⟩ := hpure
  obtain ⟨rfl, rfl⟩ : f = ev0 ∧ rest = evs := by
    have h1 := congrArg (fun l => l.head?) hρ
    have h2 := congrArg (fun l => l.tail) hρ
    simp at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  rw [bindArgs_ctr]
  iapply ctr_body_wpt ra mo bty xbty cbty n p rs hQ i pptr bs f rest hf
    h0 hin hbs $$ Hpt

/-- THE WHOLE PROGRAM at the total judgment, from the abstract
    one-request capacity alone: create through the PUBLIC
    `wpt_create`, entry through the loop's `save` with its live
    initializers (`wpt_save` — EVAL then TAU, `saveEntryCost = 2`),
    then the body at its variant budget. -/
theorem ctrProd_wpt (sbty : core_base_type) (hn : 0 ≤ n)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value))
    (hf : SymFrame ev0) :
    iprop(allocCap (procCtx p rs).tagDefs (GF := GF) [⟨4, intTy⟩]) ⊢
      wpt (procCtx p rs) (ctrLsT n)
        (2 + (ctrCost n.toNat + saveEntryCost (ctrParams xbty cbty n)))
        (readoutPost (ψC n))
        (counterProdProg ra mo bty xbty cbty sbty n) (ev0 :: evs) := by
  iintro Hcap
  rw [show counterProdProg ra mo bty xbty cbty sbty n =
    Expr [] (Esseq (symPat [] ctrPSym bty)
      (createExpr loc0 empty_annotation (.IV .Prov_none 4) intTy
        (PrefOther "spike-x"))
      (Expr [] (Esave (ctrLoopSym, sbty) (ctrParams xbty cbty n)
        (ctrBody ra mo bty)))) from rfl]
  iapply wpt_seq_sym
  iapply wpt_create loc0 empty_annotation .Prov_none ⟨4, intTy⟩ []
    (PrefOther "spike-x") (ev0 :: evs) (Nat.le_refl 2) intTy_nonatomic
    (fun a => intTy_decIndep a _)
  isplitl [Hcap]
  · iexact Hcap
  iintro %pptr ⟨Hpt, -, -⟩
  iexists (Vobject (OVpointer pptr))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym ctrPSym bty]
  iapply wpt_save [] (ctrLoopSym, sbty) (ctrParams xbty cbty n) _ _ evs
    (cvals := [ivVal n, ptrVal pptr])
    (by rw [procCtx_extern]
        exact ctr_save_params_eval hf evs xbty cbty n (ptrVal pptr))
  rw [bindSaveParams_ctr]
  iapply ctr_body_wpt ra mo bty xbty cbty n p rs hQ n pptr (intUndefBytes fmapEmpty)
    (envAdd ctrPSym (Vobject (OVpointer pptr)) ev0) evs (hf.add _ _) hn
    (Int.le_refl n) (.inl ⟨rfl, rfl⟩)
  iexact Hpt

end CtrIris

/-! ### Registration, cone membership, potentials -/

theorem ctrBody_frag (ra : core_run_annotation) (mo : memory_order)
    (bty : core_base_type) : Frag (ctrBody ra mo bty) :=
  .if_
    (by rw [show peDepth ctrGuardPe = 2 from rfl,
      show lemDefaultFuel = 999999 + 1 from rfl]; omega)
    (.sseq
      (.store_op loc0_lib rfl (.sym [] ctrCSym) (.val [] sevenVal)
        (by rw [show peDepth (Pexpr ([] : List annot) ()
            (PEsym ctrCSym)) = 1 from rfl,
          show lemDefaultFuel = 999999 + 1 from rfl]; omega)
        (peDepth_val_le _ _))
      (.run (by
        intro pe hpe
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
        rcases hpe with rfl | rfl <;>
          (rw [show lemDefaultFuel = 999999 + 1 from rfl]
           first
            | (rw [show peDepth ctrDecPe = 2 from rfl]; omega)
            | (rw [show peDepth (Pexpr ([] : List annot) ()
                (PEsym ctrCSym)) = 1 from rfl]; omega)))))
    (frag_ofVal (.pure Vunit))

/-- The save's initializers are within the evaluator's fuel (a literal
    and a symbol, depth 1 each). -/
theorem ctrParams_depth (xbty cbty : core_base_type) (n : Int) :
    ∀ pe ∈ saveParamPexprs (ctrParams xbty cbty n), peDepth pe ≤ lemDefaultFuel := by
  intro pe hpe
  simp only [ctrParams, saveParamPexprs, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hpe
  rcases hpe with rfl | rfl
  · exact peDepth_val_le _ _
  · exact peDepth_sym_le _ _

theorem counterProdProg_frag (ra : core_run_annotation) (mo : memory_order)
    (bty xbty cbty sbty : core_base_type) (n : Int) :
    Frag (counterProdProg ra mo bty xbty cbty sbty n) :=
  .sseq_sym (.create loc0_lib)
    (.save (ctrParams_depth xbty cbty n) (ctrBody_frag ra mo bty))

theorem ctrBody_pot (ra : core_run_annotation) (mo : memory_order)
    (bty : core_base_type) : pot (ctrBody ra mo bty) = 4 := rfl

theorem counterProdProg_pot (ra : core_run_annotation) (mo : memory_order)
    (bty xbty cbty sbty : core_base_type) (n : Int) :
    pot (counterProdProg ra mo bty xbty cbty sbty n) = 6 := rfl

/-- The shipped registration computes the counter's label map (the
    save is the registration site and the entry). -/
theorem collect_new_ctrProd (ra : core_run_annotation) (mo : memory_order)
    (bty xbty cbty sbty : core_base_type) (n : Int) :
    collect_labeled_continuations_NEW
        (prodFile (counterProdProg ra mo bty xbty cbty sbty n)) =
      fmapAddBy (fun (s1 s2 : sym) => ordCompare s1 s2) mainSym
        (ctrQ ra mo bty xbty cbty) fmapEmpty := rfl

theorem ctrProd_labeledAt (sup : Nat) (ra : core_run_annotation) (mo : memory_order)
    (bty xbty cbty sbty : core_base_type) (n : Int) :
    LabeledAt ((initial_core_run_state sup (collect_labeled_continuations_NEW
        (prodFile (counterProdProg ra mo bty xbty cbty sbty n)))).1)
      mainSym (ctrQ ra mo bty xbty cbty) := by
  unfold LabeledAt
  rw [show ((initial_core_run_state sup (collect_labeled_continuations_NEW
      (prodFile (counterProdProg ra mo bty xbty cbty sbty n)))).1).labeled =
    collect_labeled_continuations_NEW
      (prodFile (counterProdProg ra mo bty xbty cbty sbty n)) from rfl]
  rw [collect_new_ctrProd]
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

/-! ### THE EXPORT -/

/-- THE COUNTER LOOP, PRODUCTION FORM (WHOLE-PROGRAM LOGIC PROOF —
    alloc arc P2 step 4): running the SHIPPED pipeline cold on the
    self-contained counter file is EXACTLY ONE Active execution
    delivering `Vunit`, with the program's own fresh cell's final
    bytes decided by the loop's data — the fresh unspecified image
    for `n = 0`, the stored seven-image for `0 < n` — at an
    EXISTENTIAL allocation id/address (the logic binds the pointer,
    the engine picks it). Cold start, shipped registration,
    termination from the total judgment; the create crosses the
    PUBLIC `wpt_create`; the pipeline arrows are the generic
    `wpt_driver_done_alloc` → `prod_run_eqJ`. -/
theorem counter_loop_certified_production (sup : Nat) (ra : core_run_annotation)
    (mo : memory_order) (bty xbty cbty sbty : core_base_type)
    (n : Int) (hn : 0 ≤ n)
    (hfuel : 6 * n.toNat + 8 ≤ lemDefaultFuel)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND
          (_root_.drive fmapEmpty false
            (prodFile (counterProdProg ra mo bty xbty cbty sbty n)) args)
          ((initial_driver_state sup
            (prodFile (counterProdProg ra mo bty xbty cbty sbty n)) fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = Vunit ∧
      (∃ (i a : Int) (bs' : List CerbMem.AbsByte),
        ((n = 0 ∧ bs' = (intUndefBytes fmapEmpty)) ∨ (0 < n ∧ bs' = (sevenBytes fmapEmpty))) ∧
        CellCoh fmapEmpty dst'.layout_state i ⟨a, intTy, bs'⟩) ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
  have hQprod := ctrProd_labeledAt sup ra mo bty xbty cbty sbty n
  have hQf : ∀ (l : sym) (params : List (sym × core_base_type))
      (cont : CoreExpr),
      lookupLabel (procCtx mainSym ((initial_core_run_state sup
        (collect_labeled_continuations_NEW
          (prodFile (counterProdProg ra mo bty xbty cbty sbty n)))).1)).labels
        l = some (params, cont) → Frag cont := by
    intro l params cont hl
    rw [procCtx_labels hQprod] at hl
    obtain ⟨-, rfl⟩ := ctrQ_inv ra mo bty xbty cbty hl
    exact ctrBody_frag ra mo bty
  obtain ⟨dres, dst', heq, hψ, hbl, hout, herr⟩ :=
    prod_run_eqJ sup (counterProdProg ra mo bty xbty cbty sbty n) hQprod
      (ψC n) (2 + (ctrCost n.toNat + saveEntryCost (ctrParams xbty cbty n)))
      (wpt_driver_done_alloc (GF := SpikeGF)
        (M₀ := procCtx mainSym ((initial_core_run_state sup
          (collect_labeled_continuations_NEW
            (prodFile (counterProdProg ra mo bty xbty cbty sbty n)))).1))
        rfl rfl (procCtx_labels hQprod) rfl rfl hQf
        (fun l params cont hl => by
          rw [procCtx_labels hQprod] at hl
          obtain ⟨-, rfl⟩ := ctrQ_inv ra mo bty xbty cbty hl
          rw [ctrBody_pot ra mo bty,
            show lemDefaultFuel = 999999 + 1 from rfl]
          omega)
        (ctrLsT n)
        (counterProdProg ra mo bty xbty cbty sbty n) fmapEmpty []
        prodMem₀ (∅ : SpikeHeapF SpikeCell) [⟨4, intTy⟩]
        (counterProdProg_frag ra mo bty xbty cbty sbty n)
        (by rw [counterProdProg_pot ra mo bty xbty cbty sbty n,
            show lemDefaultFuel = 999999 + 1 from rfl]
            omega)
        (prodMem₀_launchCoh [⟨4, intTy⟩] prod_one_int_plan_fits)
        (ψC n) (2 + (ctrCost n.toNat + saveEntryCost (ctrParams xbty cbty n)))
        (by
          intro inst
          iintro ⟨-, Hcap⟩
          isplitr [Hcap]
          · iapply ctr_blockSpecsT ra mo bty xbty cbty n mainSym _ hQprod
          · iapply ctrProd_wpt ra mo bty xbty cbty n mainSym _ hQprod sbty
              hn fmapEmpty [] symFrame_empty $$ Hcap))
      (by rw [show lemDefaultFuel = 999999 + 1 from rfl] at hfuel ⊢
          rw [ctrCost_eq, show saveEntryCost (ctrParams xbty cbty n) = 2 from rfl]
          omega)
      fs args
  exact ⟨dres, dst', heq, hψ.1, hψ.2, hbl, hout, herr⟩

/-! ## LIST REVERSAL ON THE SHIPPED PIPELINE — the flagship's
production instance, WHOLE-PROGRAM LOGIC PROOF (alloc arc P2 step 5;
the R-02 conversion). The program BUILDS its two-node chain with the
engine's own operations, ALL THROUGH THE LOGIC: two creates through
the PUBLIC `wpt_create` from a two-request plan (the fresh pointers
BOUND by the program — the P2 pointer-flow design record), four
field stores through the generic typed-subrange rules at the bound
pointers — the constants stored DIRECTLY (`store(long, n1, 1)`,
`store(node*, array_shift(n2, long, 1), NULL)`: QA-1/H-1, the mixed
operand shapes) — then the AUTHORED flagship loop ENTERED THROUGH ITS
`save` with live initializers, `save loop(prev := NULL, cur := n1)`
(`wpt_save` at `evalPexprs … = some cvals`). THE GENERIC LIST LOGIC IS
UNTOUCHED (the
charter's demand): `lrBody`/`lrQ`/`lrLsT`/`lr_body_wpt` are consumed
verbatim at the node list `[(i₁,1),(i₂,2)]` for the ENGINE-PICKED
allocation ids i₁ i₂ (existential — the production label spec wraps
the generic one in `∃ i₁ i₂`, transported by `wpt_mono_Ls`); the
exact cold-start pointers live only in the plan's boundary
evaluation (`lr_two_node_plan_fits`). The node-WF address bounds
`isList` demands come from the PUBLIC create rule's bounds export.
The `save` node is the registration site and the entry (the pre-QA-1
form — three constant binds, the save dummy-initialized in an untaken
outer-sseq arm, entry by `run` — is recorded in
docs/2026-09-02_qa1-notes.md). No `Step.*`, `engineSteps_*`,
`driveJ_step`, `driverDone_step` anywhere. -/

def lrN1Sym : sym := Symbol "" 531 SD_None
def lrN2Sym : sym := Symbol "" 532 SD_None

/-- Core loaded-long values/mvals for the value fields. -/
def longVal (v : Int) : value :=
  Vloaded (LVspecified (OVinteger (CerbMem.integerIval v)))

def longMval (v : Int) : CerbMem.MemValue :=
  CerbMem.integerValueMval (.Signed .Long) (CerbMem.integerIval v)

/-- The fresh node image. -/
abbrev nodeUndefBytes : List CerbMem.AbsByte :=
  List.replicate (CerbMem.sizeofCtype fmapEmpty nodeTy) undefByte

theorem nodeTy_nonatomic : atomicTy nodeTy = false := rfl

/-- The fresh node image's decode inertness at EVERY address (the
    public create rule's shape). -/
theorem nodeTy_decIndep_undef (a : Int) : decIndep fmapEmpty a nodeTy nodeUndefBytes :=
  fun lum fpm => nodeTy_dec_indep lum fpm a _

/-- The build prefix, continued by `k`: two creates (pointers BOUND),
    four field stores through the bound pointers with the constants
    stored directly (`store(long, n1, 1)`; `store(node*,
    array_shift(n1, long, 1), n2)`; `store(long, n2, 2)`;
    `store(node*, array_shift(n2, long, 1), NULL)`), then `k`. -/
def lrProdPrefix (ra : core_run_annotation) (mo : memory_order)
    (bty : core_base_type) (k : CoreExpr) : CoreExpr :=
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
              k)))))))))))

/-- The loop's save parameters with their LIVE initializers:
    `prev := NULL` (the literal), `cur := n1` (the program-bound head). -/
def lrProdParams (pbty cbty : core_base_type) :
    List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)) :=
  [(lrPrevSym, ((pbty, none), Pexpr [] () (PEval nullVal))),
   (lrCurSym, ((cbty, none), Pexpr [] () (PEsym lrN1Sym)))]

/-- The self-contained production reversal program: the build prefix
    continued by the loop's `save`, entered with the live initializers. -/
def lrProdProg (ra : core_run_annotation) (mo : memory_order)
    (bty sbty pbty cbty bbty nbty ubty : core_base_type) : CoreExpr :=
  lrProdPrefix ra mo bty
    (Expr [] (Esave (lrLoopSym, sbty) (lrProdParams pbty cbty)
      (lrBody loc0 empty_annotation ra mo bbty nbty ubty)))

/-! ### The prefix frame (two binds) and its evaluation facts -/

/-- The head frame after the two prefix binds. -/
def lrPFrame (v1 v2 : value) (f : Fmap sym value) : Fmap sym value :=
  envAdd lrN2Sym v2 (envAdd lrN1Sym v1 f)

theorem lrPFrame_symFrame {f : Fmap sym value} (hf : SymFrame f)
    (v1 v2 : value) : SymFrame (lrPFrame v1 v2 f) :=
  (hf.add _ _).add _ _

section LrPLookups

variable {f : Fmap sym value} (hf : SymFrame f) (v1 v2 : value)
  (rest : List (Fmap sym value))

include hf

theorem lrPFrame_lookup_n1 :
    fmapLookupBy symCmpK lrN1Sym (lrPFrame v1 v2 f) = some v1 := by
  unfold lrPFrame
  rw [envAdd_lookup (hf.add _ _) symCmpK,
    if_neg (by decide +kernel),
    envAdd_lookup hf symCmpK,
    if_pos (by decide +kernel)]

theorem lrPFrame_lookup_n2 :
    fmapLookupBy symCmpK lrN2Sym (lrPFrame v1 v2 f) = some v2 := by
  unfold lrPFrame
  rw [envAdd_lookup (hf.add _ _) symCmpK,
    if_pos (by decide +kernel)]

/-- The shifted next-field operands at the bound node pointers. -/
theorem lrPFrame_shift_n1 (i a : Int) :
    evalPexpr fmapEmpty fmapEmpty
        (lrPFrame (ptrVal (cellPtr i a)) v2 f :: rest)
        (lrShiftPe lrN1Sym) = some (ptrVal (cellPtr i (a + 8))) := by
  unfold lrShiftPe
  rw [evalPexpr_array_shift]
  rw [show evalPexpr fmapEmpty fmapEmpty (lrPFrame (ptrVal (cellPtr i a)) v2 f :: rest)
      (Pexpr [] () (PEsym lrN1Sym)) = some (ptrVal (cellPtr i a)) from by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (lrPFrame_lookup_n1 hf _ _) rest]
  show evalArrayShift fmapEmpty longTy (Vobject (OVpointer (cellPtr i a))) (ivVal 1) = _
  exact evalArrayShift_long_one i a

theorem lrPFrame_shift_n2 (i a : Int) :
    evalPexpr fmapEmpty fmapEmpty
        (lrPFrame v1 (ptrVal (cellPtr i a)) f :: rest)
        (lrShiftPe lrN2Sym) = some (ptrVal (cellPtr i (a + 8))) := by
  unfold lrShiftPe
  rw [evalPexpr_array_shift]
  rw [show evalPexpr fmapEmpty fmapEmpty (lrPFrame v1 (ptrVal (cellPtr i a)) f :: rest)
      (Pexpr [] () (PEsym lrN2Sym)) = some (ptrVal (cellPtr i a)) from by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (lrPFrame_lookup_n2 hf _ _) rest]
  show evalArrayShift fmapEmpty longTy (Vobject (OVpointer (cellPtr i a))) (ivVal 1) = _
  exact evalArrayShift_long_one i a

/-- The save's initializers evaluate at the entry env: the NULL literal
    and the program-bound head pointer. -/
theorem lrPFrame_save_params (pbty cbty : core_base_type) :
    evalPexprs fmapEmpty fmapEmpty (lrPFrame v1 v2 f :: rest)
        (saveParamPexprs (lrProdParams pbty cbty)) =
      some [ptrVal nullNode, v1] := by
  show evalPexprs fmapEmpty fmapEmpty (lrPFrame v1 v2 f :: rest)
    [Pexpr [] () (PEval nullVal), Pexpr [] () (PEsym lrN1Sym)] = _
  rw [evalPexprs_cons, evalPexpr_val]
  rw [evalPexprs_cons]
  rw [show evalPexpr fmapEmpty fmapEmpty (lrPFrame v1 v2 f :: rest)
      (Pexpr [] () (PEsym lrN1Sym)) = some v1 from by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (lrPFrame_lookup_n1 hf _ _) rest]
  rfl

end LrPLookups

/-- The save entry binds the parameters exactly as the jump does
    (`bindArgs_lr`). -/
theorem bindSaveParams_lrProd (pbty cbty : core_base_type)
    (v1 v2 : value) (f : Fmap sym value) (rest : List (Fmap sym value)) :
    bindSaveParams (lrProdParams pbty cbty) [v1, v2] (f :: rest) =
      lrFrame v1 v2 f :: rest := by
  show update_env (mk_sym_pat lrCurSym cbty) v2
    (update_env (mk_sym_pat lrPrevSym pbty) v1 (f :: rest)) = _
  rw [update_env_cons, update_env_aux_sym, update_env_cons,
    update_env_aux_sym]
  rfl

/-- The save's initializers are within the evaluator's fuel. -/
theorem lrProdParams_depth (pbty cbty : core_base_type) :
    ∀ pe ∈ saveParamPexprs (lrProdParams pbty cbty), peDepth pe ≤ lemDefaultFuel := by
  intro pe hpe
  simp only [lrProdParams, saveParamPexprs, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hpe
  rcases hpe with rfl | rfl
  · exact peDepth_val_le _ _
  · exact peDepth_sym_le _ _

/-! ### Byte-image facts for the built nodes (all concrete splices
over the fresh replicate image; addresses abstract) -/

/-- Node 1's built image: value 1 then next := node 2. -/
abbrev lrBuilt1 (i₂ a₂ : Int) : List CerbMem.AbsByte :=
  spliceBytes 8 (CerbMem.memValueToBytes fmapEmpty []
      (CerbMem.pointerMval nodeTy (cellPtr i₂ a₂))).2
    (spliceBytes 0 (CerbMem.memValueToBytes fmapEmpty [] (longMval 1)).2
      nodeUndefBytes)

/-- Node 2's built image: value 2 then next := NULL. -/
abbrev lrBuilt2 : List CerbMem.AbsByte :=
  spliceBytes 8 (CerbMem.memValueToBytes fmapEmpty []
      (CerbMem.pointerMval nodeTy nullNode)).2
    (spliceBytes 0 (CerbMem.memValueToBytes fmapEmpty [] (longMval 2)).2
      nodeUndefBytes)

theorem lrBuilt1_inner_len :
    (spliceBytes 0 (CerbMem.memValueToBytes fmapEmpty [] (longMval 1)).2
      nodeUndefBytes).length = 16 := by
  rw [spliceBytes_length _ _ _ (by decide)]
  decide

theorem lrBuilt2_inner_len :
    (spliceBytes 0 (CerbMem.memValueToBytes fmapEmpty [] (longMval 2)).2
      nodeUndefBytes).length = 16 := by
  rw [spliceBytes_length _ _ _ (by decide)]
  decide

theorem lrBuilt1_len (i₂ a₂ : Int) : (lrBuilt1 i₂ a₂).length = 16 := by
  rw [spliceBytes_length _ _ _ (by
    rw [node_ptr_img_cell, ptrImg_cell_length, lrBuilt1_inner_len]
    omega)]
  exact lrBuilt1_inner_len

theorem lrBuilt2_len : lrBuilt2.length = 16 := by
  rw [spliceBytes_length _ _ _ (by
    rw [node_ptr_img_null, ptrImg_null_length, lrBuilt2_inner_len]
    omega)]
  exact lrBuilt2_inner_len

theorem lrBuilt1_valDec (i₂ a₂ : Int) : nodeValDec fmapEmpty (lrBuilt1 i₂ a₂) 1 := by
  intro lum fpm ad
  rw [show ((lrBuilt1 i₂ a₂).drop 0).take 8 =
      ((spliceBytes 0 (CerbMem.memValueToBytes fmapEmpty [] (longMval 1)).2
        nodeUndefBytes).drop 0).take 8 from
    spliceBytes_value_slice _ _
      (by rw [node_ptr_img_cell]; exact ptrImg_cell_length i₂ a₂)
      lrBuilt1_inner_len]
  rfl

theorem lrBuilt2_valDec : nodeValDec fmapEmpty lrBuilt2 2 := by
  intro lum fpm ad
  rw [show (lrBuilt2.drop 0).take 8 =
      ((spliceBytes 0 (CerbMem.memValueToBytes fmapEmpty [] (longMval 2)).2
        nodeUndefBytes).drop 0).take 8 from
    spliceBytes_value_slice _ _
      (by rw [node_ptr_img_null]; exact ptrImg_null_length)
      lrBuilt2_inner_len]
  rfl

theorem lrBuilt1_nextDec (i₂ a₂ : Int) (h0 : 0 < a₂) (h1 : a₂ < 2 ^ 64) :
    nodeNextDec fmapEmpty (lrBuilt1 i₂ a₂) (cellPtr i₂ a₂) := by
  refine nodeNextDec_ptrImg_cell i₂ a₂ h0 h1 _ ?_
  rw [show ((lrBuilt1 i₂ a₂).drop 8).take 8 =
      (CerbMem.memValueToBytes fmapEmpty []
        (CerbMem.pointerMval nodeTy (cellPtr i₂ a₂))).2 from
    spliceBytes_next_slice _ _
      (by rw [node_ptr_img_cell]; exact ptrImg_cell_length i₂ a₂)
      lrBuilt1_inner_len]
  exact node_ptr_img_cell i₂ a₂

theorem lrBuilt2_nextDec : nodeNextDec fmapEmpty lrBuilt2 nullNode := by
  refine nodeNextDec_ptrImg_null _ ?_
  rw [show (lrBuilt2.drop 8).take 8 =
      (CerbMem.memValueToBytes fmapEmpty []
        (CerbMem.pointerMval nodeTy nullNode)).2 from
    spliceBytes_next_slice _ _
      (by rw [node_ptr_img_null]; exact ptrImg_null_length)
      lrBuilt2_inner_len]
  exact node_ptr_img_null

/-! ### The total lane: the production label spec wraps the GENERIC
list spec in an existential over the engine-picked ids -/

/-- The engine-facing postcondition: the delivered value heads a
    footprint seeded as the REVERSED two-node chain — the program's
    OWN engine-allocated nodes (existential ids), own values. -/
def ψL : value → Mem → Prop := fun v σ' =>
  ∃ (i₁ i₂ : Int) (Q : CellMap),
    (∃ p' : CerbMem.PointerValue, v = ptrVal p' ∧
      SeedChain Q p' ([((i₁ : Int), (1 : Int)), (i₂, 2)]).reverse) ∧
    Q ##ₘ (∅ : CellMap) ∧
    Coh fmapEmpty σ' (Iris.Std.PartialMap.union Q (∅ : CellMap))

section LrProdIris

variable {GF : BundledGFunctors} [SpikeGS .hasLC GF]

/-- The production label spec: the GENERIC `lrLsT` at the two-node
    list `[(i₁,1),(i₂,2)]`, the ids existential (engine-picked, bound
    by the whole-program derivation's create continuations), framed by
    the (empty) cell frame through the generic `frameLsT` (alloc arc
    P4.2 — the invariant itself is unframed). -/
abbrev lrProdLsT : LabelSpecT GF := fun l m vs ρ =>
  iprop(∃ i₁ i₂ : Int,
    frameLsT (lrCellFrame (∅ : CellMap)) (lrLsT [((i₁ : Int), (1 : Int)), (i₂, 2)])
      l m vs ρ)

variable (ra : core_run_annotation) (mo : memory_order)
  (pbty cbty bbty nbty ubty : core_base_type)
  (p : sym) (rs : core_run_state)
  (hQ : LabeledAt rs p (lrQ loc0 empty_annotation ra mo pbty cbty bbty
    nbty ubty))

include hQ

/-- THE TOTAL BLOCK SPECIFICATION for the production loop: the
    generic per-body theorem `lr_body_wpt` consumed VERBATIM at the
    unpacked ids, transported into the wrapped label spec by
    `wpt_mono_Ls` and into the production readout by `wpt_mono`. -/
theorem lrProd_blockSpecsT :
    ⊢ blockSpecsT (GF := GF) (procCtx p rs) lrProdLsT
      (readoutPost ψL) := by
  refine blockSpecsT_intro fun l params cont vs ev0 evs m hl => ?_
  rw [procCtx_labels hQ] at hl
  obtain ⟨rfl, rfl⟩ := lrQ_inv loc0 empty_annotation ra mo pbty cbty bbty
    nbty ubty hl
  iintro ⟨%i₁, %i₂, HL⟩
  icases HL with ⟨⟨%revd, %rest', %pPrev, %pCur, %f, %renv, %hpure, HP, HC⟩, HF⟩
  obtain ⟨rfl, hxs, rfl, hρ, hf⟩ := hpure
  obtain ⟨rfl, rfl⟩ : f = ev0 ∧ renv = evs := by
    have h1 := congrArg (fun l => l.head?) hρ
    have h2 := congrArg (fun l => l.tail) hρ
    simp at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  rw [bindArgs_lr]
  iapply wpt_mono
    (fun w ρ' => (lrPost_readout [((i₁ : Int), (1 : Int)), (i₂, 2)]
        (∅ : CellMap) w ρ').trans
      (readoutPost_mono (fun v σ' hv => ⟨i₁, i₂, hv⟩) w ρ'))
    _ _ _
  iapply wpt_mono_Ls
    (Ls₁ := frameLsT (lrCellFrame (∅ : CellMap))
      (lrLsT [((i₁ : Int), (1 : Int)), (i₂, 2)]))
    (fun l' m' vs' ρ' => by
      iintro H
      iexists i₁, i₂
      iexact H)
    _ _ _
  iapply lr_body_wpt_frame loc0 empty_annotation ra mo pbty cbty bbty nbty ubty
    [((i₁ : Int), (1 : Int)), (i₂, 2)] p rs hQ (lrCellFrame (∅ : CellMap))
    revd rest' pPrev pCur f renv hf hxs
  isplitl [HP HC]
  · isplitl [HP]
    · iexact HP
    · iexact HC
  · iexact HF

/-- THE WHOLE PROGRAM at the total judgment, from the abstract
    two-request capacity alone: the two creates through the PUBLIC
    `wpt_create` (bounds export feeding `isList`'s node WF), the four
    field stores through the generic typed-subrange rules at the
    BOUND pointers, the flagship loop entered by the registered jump
    with the built chain. -/
theorem lrProd_wpt (bty sbty : core_base_type)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value))
    (hf : SymFrame ev0) :
    iprop(allocCap (procCtx p rs).tagDefs (GF := GF) [⟨8, nodeTy⟩, ⟨8, nodeTy⟩]) ⊢
      wpt (procCtx p rs) lrProdLsT
        (2 + (2 + ((3 + 1) + ((3 + 1) + ((3 + 1) + ((3 + 1) +
          (lrCost 2 + saveEntryCost (lrProdParams pbty cbty))))))))
        (readoutPost ψL)
        (lrProdProg ra mo bty sbty pbty cbty bbty nbty ubty)
        (ev0 :: evs) := by
  iintro Hcap
  rw [show lrProdProg ra mo bty sbty pbty cbty bbty nbty ubty =
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
                (Expr [] (Esave (lrLoopSym, sbty) (lrProdParams pbty cbty)
                  (lrBody loc0 empty_annotation ra mo bbty nbty ubty))))))))))))))
    from rfl]
  iapply wpt_seq_sym
  iapply wpt_create loc0 empty_annotation .Prov_none ⟨8, nodeTy⟩
    [⟨8, nodeTy⟩] (PrefOther "lr-n1") (ev0 :: evs) (Nat.le_refl 2)
    nodeTy_nonatomic nodeTy_decIndep_undef
  isplitl [Hcap]
  · iexact Hcap
  iintro %p₁ ⟨Hpt₁, Hcap, %hb₁⟩
  iexists (Vobject (OVpointer p₁))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym lrN1Sym bty]
  iapply wpt_seq_sym
  iapply wpt_create loc0 empty_annotation .Prov_none ⟨8, nodeTy⟩
    [] (PrefOther "lr-n2") _ (Nat.le_refl 2)
    nodeTy_nonatomic nodeTy_decIndep_undef
  isplitl [Hcap]
  · iexact Hcap
  iintro %p₂ ⟨Hpt₂, -, %hb₂⟩
  iexists (Vobject (OVpointer p₂))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym lrN2Sym bty]
  -- the two binds assembled: the prefix frame
  rw [show envAdd lrN2Sym (Vobject (OVpointer p₂))
      (envAdd lrN1Sym (Vobject (OVpointer p₁)) ev0) =
    lrPFrame (ptrVal p₁) (ptrVal p₂) ev0 from rfl]
  icases (pointsToCell_cellOwn_iff (procCtx p rs).tagDefs _ _ _ _).mp $$ Hpt₁
    with ⟨%i₁, %a₁, %hpv₁, Hcell₁⟩
  icases (pointsToCell_cellOwn_iff (procCtx p rs).tagDefs _ _ _ _).mp $$ Hpt₂
    with ⟨%i₂, %a₂, %hpv₂, Hcell₂⟩
  subst hpv₁
  subst hpv₂
  rw [addrOf_cellPtr] at hb₁ hb₂
  -- store 1: node 1's value field (offset 0, through the bound
  -- pointer)
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
    (by rw [show CerbMem.sizeofCtype (procCtx p rs).tagDefs longTy = 8 from rfl,
      show CerbMem.sizeofCtype (procCtx p rs).tagDefs nodeTy = 16 from rfl]; omega)
    rfl (fun _ => rfl) (fun _ => rfl) rfl
    (fun lum fpm => nodeTy_dec_indep lum fpm a₁ _)
  isplitl [Hcell₁]
  · iexact Hcell₁
  iintro %fp1 Hcell₁
  -- store 2: node 1's next field (offset 8) := node 2
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
    (by rw [show CerbMem.sizeofCtype (procCtx p rs).tagDefs nodeTy = 16 from rfl]; omega)
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
    (by rw [show CerbMem.sizeofCtype (procCtx p rs).tagDefs longTy = 8 from rfl,
      show CerbMem.sizeofCtype (procCtx p rs).tagDefs nodeTy = 16 from rfl]; omega)
    rfl (fun _ => rfl) (fun _ => rfl) rfl
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
    (by rw [show CerbMem.sizeofCtype (procCtx p rs).tagDefs nodeTy = 16 from rfl]; omega)
    (by rw [node_ptr_img_null]; exact ptrImg_null_length)
    (node_ptr_compat nullNode) (fun _ => rfl) (fun _ => rfl)
  isplitl [Hcell₂]
  · iexact Hcell₂
  iintro %fp4 Hcell₂
  -- the loop's save, entered with the live initializers (prev := NULL,
  -- cur := n1): EVAL then TAU, then the generic body theorem at the
  -- built chain (the ids existential in the production label spec)
  iapply wpt_save [] (lrLoopSym, sbty) (lrProdParams pbty cbty) _ _ evs
    (cvals := [ptrVal nullNode, ptrVal (cellPtr i₁ a₁)])
    (by rw [procCtx_extern]
        exact lrPFrame_save_params hf (ptrVal (cellPtr i₁ a₁))
          (ptrVal (cellPtr i₂ a₂)) evs pbty cbty)
  rw [bindSaveParams_lrProd]
  -- the readout, with the four stores' annotation residues absorbed
  iapply wpt_mono
    (fun w ρ' => ((lrPost_readout [((i₁ : Int), (1 : Int)), (i₂, 2)]
        (∅ : CellMap) w ρ').trans
      (readoutPost_mono (fun v σ' hv => ⟨i₁, i₂, hv⟩) w ρ')).trans
      (((readoutPost_annot_absorb ψL [DA_pos [] fp4] Vunit w ρ').trans
        (readoutPost_annot_absorb ψL [DA_pos [] fp3] Vunit _ ρ')).trans
       ((readoutPost_annot_absorb ψL [DA_pos [] fp2] Vunit _ ρ').trans
        (readoutPost_annot_absorb ψL [DA_pos [] fp1] Vunit _ ρ'))))
    _ _ _
  iapply wpt_mono_Ls
    (Ls₁ := frameLsT (lrCellFrame (∅ : CellMap))
      (lrLsT [((i₁ : Int), (1 : Int)), (i₂, 2)]))
    (fun l' m' vs' ρ' => by
      iintro H
      iexists i₁, i₂
      iexact H)
    _ _ _
  iapply lr_body_wpt_frame loc0 empty_annotation ra mo pbty cbty bbty nbty ubty
    [((i₁ : Int), (1 : Int)), (i₂, 2)] p rs hQ (lrCellFrame (∅ : CellMap))
    ([] : List (Int × Int)) [((i₁ : Int), (1 : Int)), (i₂, 2)] nullNode
    (cellPtr i₁ a₁) (lrPFrame (ptrVal (cellPtr i₁ a₁)) (ptrVal (cellPtr i₂ a₂)) ev0)
    evs (lrPFrame_symFrame hf _ _) rfl
  -- the invariant at entry, then the (empty) cell frame
  isplitl [Hcell₁ Hcell₂]
  · isplitr [Hcell₁ Hcell₂]
    · -- isList NULL [] for prev
      exact isList_nil_intro
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
  · -- the empty frame
    iapply (BigSepM.bigSepM_empty_intro
      (P := (BIBase.emp : IProp GF))
      (Φ := fun (i : Int) (c : SpikeCell) =>
        cellOwn (procCtx p rs).tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c))
    itrivial

end LrProdIris

/-! ### Registration, cone membership, potentials, the plan -/

theorem lrProdPrefix_frag (ra : core_run_annotation) (mo : memory_order)
    (bty : core_base_type) {k : CoreExpr} (hk : Frag k) :
    Frag (lrProdPrefix ra mo bty k) :=
  .sseq_sym (.create loc0_lib)
    (.sseq_sym (.create loc0_lib)
      (.sseq
        (.store_op loc0_lib rfl (.sym [] lrN1Sym) (.val [] (longVal 1))
          (by rw [show peDepth (Pexpr ([] : List annot) ()
              (PEsym lrN1Sym)) = 1 from rfl,
            show lemDefaultFuel = 999999 + 1 from rfl]; omega)
          (peDepth_val_le _ _))
        (.sseq
          (.store_op loc0_lib rfl
            (.arrayShift [] longTy (.sym [] lrN1Sym) (.val [] (ivVal 1)))
            (.sym [] lrN2Sym)
            (by rw [show peDepth (lrShiftPe lrN1Sym) = 2 from rfl,
              show lemDefaultFuel = 999999 + 1 from rfl]; omega)
            (by rw [show peDepth (Pexpr ([] : List annot) ()
                (PEsym lrN2Sym)) = 1 from rfl,
              show lemDefaultFuel = 999999 + 1 from rfl]; omega))
          (.sseq
            (.store_op loc0_lib rfl (.sym [] lrN2Sym) (.val [] (longVal 2))
              (by rw [show peDepth (Pexpr ([] : List annot) ()
                  (PEsym lrN2Sym)) = 1 from rfl,
                show lemDefaultFuel = 999999 + 1 from rfl]; omega)
              (peDepth_val_le _ _))
            (.sseq
              (.store_op loc0_lib rfl
                (.arrayShift [] longTy (.sym [] lrN2Sym) (.val [] (ivVal 1)))
                (.val [] nullVal)
                (by rw [show peDepth (lrShiftPe lrN2Sym) = 2 from rfl,
                  show lemDefaultFuel = 999999 + 1 from rfl]; omega)
                (peDepth_val_le _ _))
              hk)))))

theorem lrProdProg_frag (ra : core_run_annotation) (mo : memory_order)
    (bty sbty pbty cbty bbty nbty ubty : core_base_type)
    (hlib : CerbLocation.isLibraryLocation loc0 = false) :
    Frag (lrProdProg ra mo bty sbty pbty cbty bbty nbty ubty) :=
  lrProdPrefix_frag ra mo bty
    (.save (lrProdParams_depth pbty cbty)
      (lrBody_fragJ loc0 empty_annotation ra mo bbty nbty ubty hlib))

theorem lrProdPrefix_pot (ra : core_run_annotation) (mo : memory_order)
    (bty : core_base_type) (k : CoreExpr) :
    pot (lrProdPrefix ra mo bty k) = 1 + max 2 (1 + max 2 (1 + max 2 (1 + max 2
      (1 + max 2 (1 + max 2 (pot k)))))) := by
  unfold lrProdPrefix createExpr storeOpRedex
  simp [pot]

theorem lrProdProg_pot (ra : core_run_annotation) (mo : memory_order)
    (bty sbty pbty cbty bbty nbty ubty : core_base_type) :
    pot (lrProdProg ra mo bty sbty pbty cbty bbty nbty ubty) = 13 := by
  unfold lrProdProg
  rw [lrProdPrefix_pot, pot_save, lrBody_pot]
  omega

/-! The registration computation, COMPOSITIONALLY (a whole-program
`rfl` hits kernel-whnf term duplication on the ten-node prefix spine
— the fuel-peeled per-arm equations rewrite layer by layer with
sharing; the save's own registration is one bounded-fuel `rfl`). -/

theorem col_aux_action {A : Type} (n : Nat) (st : collect_saves_state A)
    (a : List annot) (p : generic_paction A Unit sym) :
    collect_saves_aux_lemFuel (n + 1) st (Expr a (Eaction p)) = st := rfl

theorem col_aux_run {A : Type} (n : Nat) (st : collect_saves_state A)
    (a : List annot) (ra : A) (l : sym)
    (pes : List (generic_pexpr Unit sym)) :
    collect_saves_aux_lemFuel (n + 1) st (Expr a (Erun ra l pes)) = st := rfl

theorem col_aux_pure {A : Type} (n : Nat) (st : collect_saves_state A)
    (a : List annot) (pe : generic_pexpr Unit sym) :
    collect_saves_aux_lemFuel (n + 1) st (Expr a (Epure pe)) = st := rfl

theorem col_aux_ofVal_pure (n : Nat)
    (st : collect_saves_state core_run_annotation) (v : value) :
    collect_saves_aux_lemFuel (n + 1) st (ofVal (.pure v)) = st := rfl

theorem col_aux_sseq {A : Type} (n : Nat) (st : collect_saves_state A)
    (a : List annot) (pat : pattern) (e1 e2 : generic_expr A Unit sym) :
    collect_saves_aux_lemFuel (n + 1) st (Expr a (Esseq pat e1 e2)) =
      union_saves st (union_saves
        { collect_saves_aux_lemFuel n empty_saves e1 with
            tmp_acc := fmapMap (fun p => match p with
              | (syms, e) => (syms, Expr a (Esseq pat e e2)))
              (collect_saves_aux_lemFuel n empty_saves e1).tmp_acc }
        (collect_saves_aux_lemFuel n empty_saves e2)) := rfl

/-- The flagship loop program's saves, at cushioned variable fuel
    (the save registers its body; nothing else in the cone
    contributes). -/
theorem col_lrProg (m : Nat) (ann ra : core_run_annotation)
    (mo : memory_order) (sbty pbty cbty bbty nbty ubty : core_base_type)
    (pv : CerbMem.PointerValue) :
    collect_saves_aux_lemFuel (m + 9) empty_saves
      (lrProg loc0 ann ra mo sbty pbty cbty bbty nbty ubty pv) =
      { tmp_acc := lrQ loc0 ann ra mo pbty cbty bbty nbty ubty,
        closed_acc := fmapEmpty } := rfl

/-- The loop's save with the production initializers registers its
    body (the initializers are not read by the registration), at
    cushioned variable fuel — the `col_lrProg` twin. -/
theorem col_lrProdSave (m : Nat) (ra : core_run_annotation)
    (mo : memory_order) (sbty pbty cbty bbty nbty ubty : core_base_type) :
    collect_saves_aux_lemFuel (m + 9) empty_saves
      (Expr [] (Esave (lrLoopSym, sbty) (lrProdParams pbty cbty)
        (lrBody loc0 empty_annotation ra mo bbty nbty ubty))) =
      { tmp_acc := lrQ loc0 empty_annotation ra mo pbty cbty bbty nbty ubty,
        closed_acc := fmapEmpty } := rfl

/-- The shipped registration computes the flagship's label map (the
    save is the registration site and the entry): the six prefix layers
    peeled one arm at a time (each store registers nothing), the save's
    own registration one bounded-fuel `rfl`, the union tower closed by
    `rfl`. -/
theorem collect_new_lrProd (ra : core_run_annotation) (mo : memory_order)
    (bty sbty pbty cbty bbty nbty ubty : core_base_type) :
    collect_labeled_continuations_NEW
        (prodFile (lrProdProg ra mo bty sbty pbty cbty bbty nbty ubty)) =
      fmapAddBy (fun (s1 s2 : sym) => ordCompare s1 s2) mainSym
        (lrQ loc0 empty_annotation ra mo pbty cbty bbty nbty ubty)
        fmapEmpty := by
  rw [show collect_labeled_continuations_NEW
      (prodFile (lrProdProg ra mo bty sbty pbty cbty bbty nbty ubty)) =
    fmapAddBy (fun (s1 s2 : sym) => ordCompare s1 s2) mainSym
      (collect_saves (lrProdProg ra mo bty sbty pbty cbty bbty nbty ubty))
      fmapEmpty from rfl]
  rw [show collect_saves (lrProdProg ra mo bty sbty pbty cbty bbty nbty
      ubty) = lrQ loc0 empty_annotation ra mo pbty cbty bbty nbty ubty
      from by
    unfold collect_saves collect_saves_aux lrProdProg lrProdPrefix createExpr
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
    rw [show (999993 : Nat) = 999984 + 9 from rfl, col_lrProdSave]
    rfl]

theorem lrProd_labeledAt (sup : Nat) (ra : core_run_annotation) (mo : memory_order)
    (bty sbty pbty cbty bbty nbty ubty : core_base_type) :
    LabeledAt ((initial_core_run_state sup (collect_labeled_continuations_NEW
        (prodFile (lrProdProg ra mo bty sbty pbty cbty bbty nbty ubty)))).1)
      mainSym (lrQ loc0 empty_annotation ra mo pbty cbty bbty nbty ubty) := by
  unfold LabeledAt
  rw [show ((initial_core_run_state sup (collect_labeled_continuations_NEW
      (prodFile (lrProdProg ra mo bty sbty pbty cbty bbty nbty ubty)))).1).labeled =
    collect_labeled_continuations_NEW
      (prodFile (lrProdProg ra mo bty sbty pbty cbty bbty nbty ubty))
    from rfl]
  rw [collect_new_lrProd]
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

/-- The two-node plan fits the production cold-start cursor (closed
    allocator arithmetic — the boundary evaluation of the concrete
    plan; the exact cold-start pointers live HERE, not in the logic). -/
theorem lr_two_node_plan_fits :
    PlanFits fmapEmpty ⟨prodMem₀.lastAddress, prodMem₀.nextAllocId⟩
      [⟨8, nodeTy⟩, ⟨8, nodeTy⟩] := by
  rw [prodMem₀_lastAddress, prodMem₀_nextAllocId, PlanFits_cons_iff]
  refine ⟨⟨freshBase errnoAddr 8 (CerbMem.sizeofCtype fmapEmpty nodeTy), 1 + 1⟩,
    ?_, ?_⟩
  · rw [advanceCursor_mk, nodeTy_size]
    exact if_pos ⟨by decide, by decide⟩
  · rw [PlanFits_cons_iff]
    refine ⟨⟨freshBase (freshBase errnoAddr 8 (CerbMem.sizeofCtype fmapEmpty nodeTy))
      8 (CerbMem.sizeofCtype fmapEmpty nodeTy), 1 + 1 + 1⟩, ?_, PlanFits_nil fmapEmpty _⟩
    rw [advanceCursor_mk, nodeTy_size]
    exact if_pos ⟨by decide, by decide⟩

/-! ### THE EXPORT -/

/-- LIST REVERSAL, PRODUCTION FORM (WHOLE-PROGRAM LOGIC PROOF —
    alloc arc P2 step 5): running the SHIPPED pipeline cold on the
    self-contained two-node build-and-reverse file is EXACTLY ONE
    Active execution whose delivered value heads a footprint `Q`
    seeded as the REVERSED chain — the program's OWN engine-allocated
    nodes at EXISTENTIAL allocation ids (the logic binds the
    pointers, the engine picks them), own values, relinked in
    reversed order — with the final production memory satisfying `Q`.
    Cold start, shipped registration, termination from the total
    judgment; the creates cross the PUBLIC `wpt_create`; the generic
    list logic is consumed verbatim; the pipeline arrows are
    `wpt_driver_done_alloc` → `prod_run_eqJ`. -/
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
  have hQprod := lrProd_labeledAt sup ra mo bty sbty pbty cbty bbty nbty ubty
  obtain ⟨dres, dst', heq, hψ, hbl, hout, herr⟩ :=
    prod_run_eqJ sup (lrProdProg ra mo bty sbty pbty cbty bbty nbty ubty)
      hQprod ψL
      (2 + (2 + ((3 + 1) + ((3 + 1) + ((3 + 1) + ((3 + 1) +
        (lrCost 2 + saveEntryCost (lrProdParams pbty cbty))))))))
      (wpt_driver_done_alloc (GF := SpikeGF)
        (M₀ := procCtx mainSym ((initial_core_run_state sup
          (collect_labeled_continuations_NEW
            (prodFile (lrProdProg ra mo bty sbty pbty cbty bbty nbty
              ubty)))).1))
        rfl rfl (procCtx_labels hQprod) rfl rfl
        (fun l params cont hl => by
          rw [procCtx_labels hQprod] at hl
          obtain ⟨-, rfl⟩ := lrQ_inv loc0 empty_annotation ra mo pbty cbty
            bbty nbty ubty hl
          exact lrBody_fragJ loc0 empty_annotation ra mo bbty nbty ubty
            loc0_lib)
        (fun l params cont hl => by
          rw [procCtx_labels hQprod] at hl
          obtain ⟨-, rfl⟩ := lrQ_inv loc0 empty_annotation ra mo pbty cbty
            bbty nbty ubty hl
          rw [lrBody_pot, show lemDefaultFuel = 999999 + 1 from rfl]
          omega)
        lrProdLsT
        (lrProdProg ra mo bty sbty pbty cbty bbty nbty ubty) fmapEmpty []
        prodMem₀ (∅ : SpikeHeapF SpikeCell) [⟨8, nodeTy⟩, ⟨8, nodeTy⟩]
        (lrProdProg_frag ra mo bty sbty pbty cbty bbty nbty ubty loc0_lib)
        (by rw [lrProdProg_pot ra mo bty sbty pbty cbty bbty nbty ubty,
            show lemDefaultFuel = 999999 + 1 from rfl]
            omega)
        (prodMem₀_launchCoh [⟨8, nodeTy⟩, ⟨8, nodeTy⟩]
          lr_two_node_plan_fits)
        ψL
        (2 + (2 + ((3 + 1) + ((3 + 1) + ((3 + 1) + ((3 + 1) +
          (lrCost 2 + saveEntryCost (lrProdParams pbty cbty))))))))
        (by
          intro inst
          iintro ⟨-, Hcap⟩
          isplitr [Hcap]
          · iapply lrProd_blockSpecsT ra mo pbty cbty bbty nbty ubty
              mainSym _ hQprod
          · iapply lrProd_wpt ra mo pbty cbty bbty nbty ubty mainSym _
              hQprod bty sbty fmapEmpty [] symFrame_empty $$ Hcap))
      (by rw [show lrCost 2 = 32 from rfl,
          show saveEntryCost (lrProdParams pbty cbty) = 2 from rfl,
          show lemDefaultFuel = 999999 + 1 from rfl]
          omega)
      fs args
  refine ⟨dres, dst', heq, ?_, hbl, hout, herr⟩
  obtain ⟨i₁, i₂, Q, ⟨p', hval, hseed⟩, -, hcoh⟩ := hψ
  refine ⟨i₁, i₂, Q, p', hval, hseed, ?_⟩
  rw [show Iris.Std.PartialMap.union Q (∅ : CellMap) = Q from
    Iris.Std.LawfulPartialMap.union_empty_right] at hcoh
  exact hcoh

end CerberusHeapLang
