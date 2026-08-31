/-
CerberusHeapLang.Phase1Probe.Match — PHASE-1 PROBE MODULE (S1a):
the engine characterization of the unified relation, and the
unified drive.

TWO-SIDEDNESS OUTCOME (the probe's K2 question, per construct):
- `store`: TWO-SIDED at any MachineCtx — `engine_step_matchU`
  (match-given-step) AND `engine_complete_storeU` (the engine's
  behavior list is a singleton matched-or-refused, refusals only
  where the mirror is provably stuck). Both directions reuse the
  per-rule step_ctx/discharge lemmas, which were already
  context-general — only the old `engineSteps` entry froze them.
- `case` (value scrutinee): TWO-SIDED at any MachineCtx —
  `engine_step_matchU` + `engine_complete_caseU` (the no-match
  ILLTYPED channel is the refusal side; a new `step_ctx_case_illtyped`
  mirrors the store-illtyped proof).
- values: two-sided under `SeqWF` (`outcomesU_done` /
  `outcomesU_remove_annot` — PROGRAM-DONE requires the empty stack
  and no parent, which is what SeqWF says).
- `run`: ONE-SIDED (match-given-step), the direction adequacy
  consumes (NotStuck supplies the mirror step; its premises are
  exactly the panic-exclusion facts — the engine's refusal channels
  at a jump are failwithI panics, deliberately not modeled). Probe
  restriction: proved under `M.extern = fmapEmpty` (the evaluator
  bridge's pin — Machine.lean header; S1b mover registered).

THE UNIFIED DRIVE. `driveU M` is the {step_ctx → discharge} loop
with every immutable drawn from the context. The two old execution
functions are definitionally its instances (`driveU_spike`,
`driveU_procJ`) — the drive/driveJ split disappears in S1b.
-/
import CerberusHeapLang.Phase1Probe.Machine
import CerberusHeapLang.Adequacy

set_option autoImplicit false

namespace CerberusHeapLang

/-! ## The value protocol at a machine context -/

/-- PROGRAM-DONE at a bare value (reads exactly SeqWF: empty stack
    selects PROGRAM-DONE over RETURN, no parent over THREAD-DONE). -/
theorem outcomesU_done {M : MachineCtx} (hwf : M.SeqWF) (aid : Nat)
    (v : value) (ρ : EnvStack) (σ : Mem) :
    outcomesU M aid (ofVal (.pure v)) ρ σ = [.done v] := by
  unfold outcomesU engineStepsU
  rw [hwf.parent,
    step_ctx_done v M.tagDefs σ M.file M.extern M.tid
      (M.thread (ofVal (.pure v)) ρ) rfl hwf.stack]
  rfl

/-- REMOVE-ANNOT at an annotated value (no context field read). -/
theorem outcomesU_remove_annot (M : MachineCtx) (aid : Nat)
    (ds : List dyn_annotation) (v : value) (ρ : EnvStack) (σ : Mem) :
    outcomesU M aid (ofVal (.annot ds v)) ρ σ =
      [.next (M.thread (ofVal (.pure v)) ρ) σ] := by
  unfold outcomesU engineStepsU
  rw [step_ctx_remove_annot ds v M.tagDefs σ M.file M.extern M.tid M.parent
      (M.thread (ofVal (.annot ds v)) ρ) rfl]
  rfl

/-! ## Match-given-step (the direction adequacy consumes) -/

/-- THE UNIFIED STEP-MATCH: wherever the mirror steps at a cone
    configuration, the engine's discharged behavior list is exactly
    the matching singleton. NOTE what is GONE relative to
    `engine_step_matchJ`: no separate label-map index, no
    `LabeledAt` tie hypothesis (derived from the context by
    `labels_lookup_some`), no frozen profile — the context is
    arbitrary up to the registered `extern` probe restriction. -/
theorem engine_step_matchU {M : MachineCtx} (hext : M.extern = fmapEmpty)
    (aid : Nat) {e e' : CoreExpr} {ev0 : Fmap sym value}
    {evs : List (Fmap sym value)} {ρ' : EnvStack} {σ σ' : Mem}
    (hf : FragU e) (hsz : esize e ≤ lemDefaultFuel)
    (hs : StepU M (e, ev0 :: evs, σ) (e', ρ', σ')) :
    outcomesU M aid e (ev0 :: evs) σ = [.next (M.thread e' ρ') σ'] := by
  cases hf with
  | val_pure v => exact (StepU.val_elim (w := .pure v) hs).elim
  | annot_val ds v => exact (StepU.val_elim (w := .annot ds v) hs).elim
  | store hlib =>
    obtain ⟨mv, fp, σ'', hmv, hmem, hout⟩ := hs.store_inv
    obtain ⟨h1, h2, h3⟩ : e' = Expr [] (Eannot [DA_pos [] fp]
        (Expr [] (Epure (Pexpr [] () (PEval Vunit))))) ∧
        ρ' = ev0 :: evs ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1 h2 h3
    unfold outcomesU engineStepsU storeRedex
    rw [step_ctx_store (DecompJ.root (RedexJ.base (Redex.store hlib))) hsz
      hlib M.tagDefs hmv σ M.file M.extern M.tid M.parent
      (M.thread _ (ev0 :: evs)) rfl]
    simp only [List.map_cons, List.map_nil]
    rw [dischargeStep_store_active hmem]
    rfl
  | run hdep =>
    obtain ⟨params, cont, vs, ev0', evs', -, hl, hvs, hout⟩ :=
      hs.jump_inv (jumpRedex?_run _ _ _ _)
    obtain ⟨p, hproc, hQ⟩ := MachineCtx.labels_lookup_some hl
    rw [MachineCtx.resolveProc_of_extern_empty hext] at hQ
    obtain ⟨h1, h2, h3⟩ : e' = cont ∧
        ρ' = bindArgs params vs (ev0 :: evs) ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1 h2
    obtain rfl : σ = σ' := h3.symm
    unfold outcomesU engineStepsU
    rw [hext]
    exact stepDischarge_run (DecompJ.root (RedexJ.run _ _ _)) hsz hl hdep
      M.tagDefs σ M.file M.tid M.parent p
      (M.thread (runRedex _ _ _) (ev0 :: evs)) rfl hproc hvs aid M.runState hQ
  | case_value hbr hbsz =>
    obtain ⟨cval', e'', hv, hsel, hout⟩ := hs.case_inv
    obtain rfl : _ = cval' := Option.some.inj (valueFromPexpr_val _ _ ▸ hv)
    obtain ⟨h1, h2, h3⟩ : e' = e'' ∧ ρ' = ev0 :: evs ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1 h2
    obtain rfl : σ = σ' := h3.symm
    unfold outcomesU engineStepsU caseRedex
    rw [step_ctx_case_value (DecompJ.root (RedexJ.case_ _ _)) hsz hsel
      M.tagDefs σ M.file M.extern M.tid M.parent
      (M.thread _ (ev0 :: evs)) rfl]
    rfl

/-! ## Engine-completeness (the second direction, where obtained) -/

/-- One matched engine behavior at a machine context (the
    `EngineMatch` shape re-indexed; `refused` requires provable
    mirror stuckness, so refusals contradict NotStuck as before). -/
inductive EngineMatchU (M : MachineCtx) (e : CoreExpr) (ρ : EnvStack)
    (σ : Mem) : EngineOutcome → Prop where
  | step {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem} :
      StepU M (e, ρ, σ) (e', ρ', σ') →
      EngineMatchU M e ρ σ (.next (M.thread e' ρ') σ')
  | removeAnnot {ds : List dyn_annotation} {v : value} :
      e = ofVal (.annot ds v) →
      EngineMatchU M e ρ σ (.next (M.thread (ofVal (.pure v)) ρ) σ)
  | done {v : value} : e = ofVal (.pure v) → EngineMatchU M e ρ σ (.done v)
  | refused {o : EngineOutcome} : o.isRefusal →
      (∀ out, ¬ StepU M (e, ρ, σ) out) → toVal e = none →
      EngineMatchU M e ρ σ o

/-- STORE IS TWO-SIDED at any context: the engine's behavior at a
    store redex is a singleton, and it is a mirror step exactly when
    the mirror can step (encoding + active memM); the ILLTYPED and
    killed channels arise only where the mirror is provably stuck. -/
theorem engine_complete_storeU (M : MachineCtx) (aid : Nat)
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
    {ty : ctype} {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
    (hlib : CerbLocation.isLibraryLocation loc = false)
    (ρ : EnvStack) (σ : Mem) :
    ∃ o, outcomesU M aid (storeRedex loc ann lk ty pv cv mo) ρ σ = [o] ∧
      EngineMatchU M (storeRedex loc ann lk ty pv cv mo) ρ σ o := by
  have hsz : esize (storeRedex loc ann lk ty pv cv mo) ≤ lemDefaultFuel := by
    rw [show esize (storeRedex loc ann lk ty pv cv mo) = 1 from rfl]
    unfold lemDefaultFuel
    omega
  cases hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv with
  | none =>
    refine ⟨.error (String.append (CerbLocation.stringFromLocation loc)
        (String.append "the value of a store("
          (String.append (CerbPP.stringFromCore_ctype (Ctype [] (unatomic_ ty)))
            (String.append ") didn't match the lvalue type: "
              (CerbPP.stringFromCore_value cv))))), ?_, ?_⟩
    · unfold outcomesU engineStepsU storeRedex
      rw [step_ctx_store_illtyped
        (DecompJ.root (RedexJ.base (Redex.store hlib))) hsz M.tagDefs hmv
        σ M.file M.extern M.tid M.parent (M.thread _ ρ) rfl]
      rfl
    · refine .refused trivial (fun out hstep => ?_) rfl
      obtain ⟨mv', -, -, hmv', -, -⟩ := hstep.store_inv
      rw [hmv] at hmv'
      cases hmv'
  | some mv =>
    cases hmem : applyMemM (CerbMem.storeM loc ty lk pv mv) σ with
    | some fpσ =>
      obtain ⟨fp, σ'⟩ := fpσ
      refine ⟨_, ?_, .step (StepU.store_canonical hmv hmem)⟩
      unfold outcomesU engineStepsU storeRedex
      rw [step_ctx_store (DecompJ.root (RedexJ.base (Redex.store hlib))) hsz
        hlib M.tagDefs hmv σ M.file M.extern M.tid M.parent (M.thread _ ρ) rfl]
      simp only [List.map_cons, List.map_nil]
      rw [dischargeStep_store_active hmem]
      rfl
    | none =>
      refine ⟨dischargeStep aid M.runState σ (Step_action_request2
          "StoreRequest" loc M.tid (is_unseq_with_ccall CTX)
          (stExceptUndef_return (StoreRequest2 mo ty lk pv mv (fun _ fp =>
            { M.thread (storeRedex loc ann lk ty pv cv mo) ρ with
              arena := apply_ctx CTX (Expr [] (Eannot [DA_pos [] fp]
                (Expr [] (Epure (Pexpr [] () (PEval Vunit)))))) })))),
        ?_, ?_⟩
      · unfold outcomesU engineStepsU storeRedex
        rw [step_ctx_store (DecompJ.root (RedexJ.base (Redex.store hlib))) hsz
          hlib M.tagDefs hmv σ M.file M.extern M.tid M.parent
          (M.thread _ ρ) rfl]
        rfl
      · refine .refused (dischargeStep_store_refusal hmem)
          (fun out hstep => ?_) rfl
        obtain ⟨mv', fp', σ'', hmv', hmem', -⟩ := hstep.store_inv
        rw [hmv] at hmv'
        obtain rfl : mv = mv' := Option.some.inj hmv'
        rw [hmem] at hmem'
        cases hmem'

/-- Ecase (value scrutinee), NO-MATCH shape: the engine's ILLTYPED
    refusal (one_step0's Ecase value arm, `select_case = none` —
    Core_reduction.lean:353), context undisturbed. The new engine
    equation the case export needs for its refusal side. -/
theorem step_ctx_case_illtyped {e : CoreExpr} {ctx : context}
    {a : List annot} {cval : value} {pats : List (pattern × CoreExpr)}
    (hd : DecompJ e ctx (caseRedex (Pexpr a () (PEval cval)) pats))
    (hsz : esize e ≤ lemDefaultFuel)
    (hsel : select_case subst_sym_expr cval pats = none)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_error2 (String.append "Ecase, mismatched ==> "
        (CerbPP.stringFromCore_expr
          (caseRedex (Pexpr a () (PEval cval)) pats)))] := by
  have hget : get_ctx th.arena =
      [(ctx, caseRedex (Pexpr a () (PEval cval)) pats)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold caseRedex
  cases ctx <;>
    (dsimp only [one_step0]
     rw [show is_irreducible (Expr ([] : List annot)
       (Ecase (Pexpr a () (PEval cval)) pats)) = false from rfl]
     dsimp only [get_loc, valueFromPexpr]
     rw [hsel]
     rfl)

/-- CASE (value scrutinee) IS TWO-SIDED at any context: TAU into the
    selected branch when a branch matches (= exactly when the mirror
    steps), the ILLTYPED refusal when none does (mirror provably
    stuck). The Phase-0 RED row's missing engine-facing pair. -/
theorem engine_complete_caseU (M : MachineCtx) (aid : Nat)
    {b : List annot} {cval : value} {pats : List (pattern × CoreExpr)}
    (ρ : EnvStack) (σ : Mem) :
    ∃ o, outcomesU M aid (caseRedex (Pexpr b () (PEval cval)) pats) ρ σ = [o] ∧
      EngineMatchU M (caseRedex (Pexpr b () (PEval cval)) pats) ρ σ o := by
  have hsz : esize (caseRedex (Pexpr b () (PEval cval)) pats)
      ≤ lemDefaultFuel := by
    rw [show esize (caseRedex (Pexpr b () (PEval cval)) pats) = 1 from rfl]
    unfold lemDefaultFuel
    omega
  cases hsel : select_case subst_sym_expr cval pats with
  | some e' =>
    refine ⟨_, ?_, .step (StepU.case_value (valueFromPexpr_val _ _) hsel)⟩
    unfold outcomesU engineStepsU caseRedex
    rw [step_ctx_case_value (DecompJ.root (RedexJ.case_ _ _)) hsz hsel
      M.tagDefs σ M.file M.extern M.tid M.parent (M.thread _ ρ) rfl]
    rfl
  | none =>
    refine ⟨.error (String.append "Ecase, mismatched ==> "
        (CerbPP.stringFromCore_expr
          (caseRedex (Pexpr b () (PEval cval)) pats))), ?_, ?_⟩
    · unfold outcomesU engineStepsU caseRedex
      rw [step_ctx_case_illtyped (DecompJ.root (RedexJ.case_ _ _)) hsz hsel
        M.tagDefs σ M.file M.extern M.tid M.parent (M.thread _ ρ) rfl]
      rfl
    · refine .refused trivial (fun out hstep => ?_) rfl
      obtain ⟨cval', e'', hv, hsel', -⟩ := hstep.case_inv
      obtain rfl : _ = cval' := Option.some.inj (valueFromPexpr_val _ _ ▸ hv)
      rw [hsel] at hsel'
      cases hsel'

/-! ## The unified drive -/

/-- One drive scrutinee at a context (the {step_ctx → discharge}
    composite the loop iterates). -/
def stepOutcomes (M : MachineCtx) (aid : Nat) (th : thread_state)
    (σ : Mem) : List EngineOutcome :=
  (step_ctx M.tagDefs σ M.file M.extern M.tid (M.parent, th)).map
    (dischargeStep aid M.runState σ)

theorem stepOutcomes_thread (M : MachineCtx) (aid : Nat) (e : CoreExpr)
    (ρ : EnvStack) (σ : Mem) :
    stepOutcomes M aid (M.thread e ρ) σ = outcomesU M aid e ρ σ := rfl

/-- THE ENGINE'S EXECUTION at a machine context: the one drive
    function of which `drive` and `driveJ` are instances. -/
def driveU (M : MachineCtx) (aids : Nat → Nat) :
    Nat → thread_state → Mem → DriveResult
  | 0, th, σ => .more th σ
  | n+1, th, σ =>
    match stepOutcomes M (aids 0) th σ with
    | [.next th' σ'] => driveU M (fun i => aids (i+1)) n th' σ'
    | [.done v] => .done v σ
    | [.killed r] => .killed r
    | _ => .stuck

/-- The straight-line drive is the spike instance, definitionally. -/
theorem driveU_spike : ∀ (n : Nat) (aids : Nat → Nat) (th : thread_state)
    (σ : Mem), driveU spikeCtx aids n th σ = drive aids n th σ
  | 0, aids, th, σ => rfl
  | n+1, aids, th, σ => by
    show (match (step_ctx fmapEmpty σ spikeFile fmapEmpty 0 (none, th)).map
        (dischargeStep (aids 0) spikeRunState σ) with
      | [.next th' σ'] => driveU spikeCtx (fun i => aids (i+1)) n th' σ'
      | [.done v] => DriveResult.done v σ
      | [.killed r] => DriveResult.killed r
      | _ => DriveResult.stuck) = drive aids (n+1) th σ
    rw [show drive aids (n+1) th σ =
      (match (step_ctx fmapEmpty σ spikeFile fmapEmpty 0 (none, th)).map
          (dischargeStep (aids 0) spikeRunState σ) with
        | [.next th' σ'] => drive (fun i => aids (i+1)) n th' σ'
        | [.done v] => DriveResult.done v σ
        | [.killed r] => DriveResult.killed r
        | _ => DriveResult.stuck) from rfl]
    cases houts : (step_ctx fmapEmpty σ spikeFile fmapEmpty 0 (none, th)).map
        (dischargeStep (aids 0) spikeRunState σ) with
    | nil => rfl
    | cons o rest =>
      cases rest with
      | cons o2 rest2 => cases o <;> rfl
      | nil =>
        cases o with
        | next th' σ' => exact driveU_spike n (fun i => aids (i+1)) th' σ'
        | done v => rfl
        | killed r => rfl
        | error s => rfl
        | offFragment => rfl

/-- The jump drive is the proc instance at any run state,
    definitionally (proc/labels are unread by the drive loop itself;
    only the run state enters the discharge). -/
theorem driveU_procJ (p : sym) (rs : core_run_state) :
    ∀ (n : Nat) (aids : Nat → Nat) (th : thread_state) (σ : Mem),
      driveU (procCtx p rs) aids n th σ = driveJ rs aids n th σ
  | 0, aids, th, σ => rfl
  | n+1, aids, th, σ => by
    show (match (step_ctx fmapEmpty σ spikeFile fmapEmpty 0 (none, th)).map
        (dischargeStep (aids 0) rs σ) with
      | [.next th' σ'] => driveU (procCtx p rs) (fun i => aids (i+1)) n th' σ'
      | [.done v] => DriveResult.done v σ
      | [.killed r] => DriveResult.killed r
      | _ => DriveResult.stuck) = driveJ rs aids (n+1) th σ
    rw [show driveJ rs aids (n+1) th σ =
      (match (step_ctx fmapEmpty σ spikeFile fmapEmpty 0 (none, th)).map
          (dischargeStep (aids 0) rs σ) with
        | [.next th' σ'] => driveJ rs (fun i => aids (i+1)) n th' σ'
        | [.done v] => DriveResult.done v σ
        | [.killed r] => DriveResult.killed r
        | _ => DriveResult.stuck) from rfl]
    cases houts : (step_ctx fmapEmpty σ spikeFile fmapEmpty 0 (none, th)).map
        (dischargeStep (aids 0) rs σ) with
    | nil => rfl
    | cons o rest =>
      cases rest with
      | cons o2 rest2 => cases o <;> rfl
      | nil =>
        cases o with
        | next th' σ' => exact driveU_procJ p rs n (fun i => aids (i+1)) th' σ'
        | done v => rfl
        | killed r => rfl
        | error s => rfl
        | offFragment => rfl

/-- ONE certified drive step (the driveJ_step analog, tie-free). -/
theorem driveU_step {M : MachineCtx} (hext : M.extern = fmapEmpty)
    (aids : Nat → Nat) (n : Nat)
    {e e' : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    {ρ' : EnvStack} {σ σ' : Mem}
    (hf : FragU e) (hsz : esize e ≤ lemDefaultFuel)
    (hs : StepU M (e, ev0 :: evs, σ) (e', ρ', σ')) :
    driveU M aids (n + 1) (M.thread e (ev0 :: evs)) σ =
      driveU M (fun i => aids (i + 1)) n (M.thread e' ρ') σ' := by
  show (match stepOutcomes M (aids 0) (M.thread e (ev0 :: evs)) σ with
    | [.next th' σ'] => driveU M (fun i => aids (i+1)) n th' σ'
    | [.done v] => DriveResult.done v σ
    | [.killed r] => DriveResult.killed r
    | _ => DriveResult.stuck) = _
  rw [stepOutcomes_thread, engine_step_matchU hext (aids 0) hf hsz hs]

/-- Value delivery (the driveJ_done analog). -/
theorem driveU_done {M : MachineCtx} (hwf : M.SeqWF) (aids : Nat → Nat)
    (n : Nat) (v : value) (ρ : EnvStack) (σ : Mem) :
    driveU M aids (n + 1) (M.thread (ofVal (.pure v)) ρ) σ = .done v σ := by
  show (match stepOutcomes M (aids 0) (M.thread (ofVal (.pure v)) ρ) σ with
    | [.next th' σ'] => driveU M (fun i => aids (i+1)) n th' σ'
    | [.done v] => DriveResult.done v σ
    | [.killed r] => DriveResult.killed r
    | _ => DriveResult.stuck) = _
  rw [stepOutcomes_thread, outcomesU_done hwf]

/-- Annotated-value delivery: one REMOVE-ANNOT tau, then done. -/
theorem driveU_done_annot {M : MachineCtx} (hwf : M.SeqWF) (aids : Nat → Nat)
    (n : Nat) (ds : List dyn_annotation) (v : value) (ρ : EnvStack) (σ : Mem) :
    driveU M aids (n + 2) (M.thread (ofVal (.annot ds v)) ρ) σ = .done v σ := by
  show (match stepOutcomes M (aids 0) (M.thread (ofVal (.annot ds v)) ρ) σ with
    | [.next th' σ'] => driveU M (fun i => aids (i+1)) (n+1) th' σ'
    | [.done v] => DriveResult.done v σ
    | [.killed r] => DriveResult.killed r
    | _ => DriveResult.stuck) = _
  rw [stepOutcomes_thread, outcomesU_remove_annot]
  exact driveU_done hwf _ n v ρ σ

end CerberusHeapLang
