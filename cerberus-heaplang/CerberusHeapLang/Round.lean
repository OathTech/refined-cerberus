/-
CerberusHeapLang.Round — THE ENGINE-FACING ONE-ROUND RELATION, NAMED
(alloc arc P3.2; the 2026-09-01 skeptical re-audit's R-03).

THE CHOICE [AGENT 2026-09-01, P3.2 — the charter's preferred option]:
`CerberusRound M aid` is THE GRAPH OF THE DISCHARGED `step_ctx`
ENGINE ROUND at a machine context — configuration `c` relates to `c'`
exactly when the engine's discharged behavior list at `c`
(`outcomesU`: one `step_ctx` call, Core_reduction.lean:484, every
core_step2 discharged by the sequential driver's protocol,
Driver.lean:273, projected — Soundness.lean header) is the singleton
successful-next to `c'`. It is defined independently of every
example and of the mirror `Step`.

WHY THIS GRANULARITY (the charter's question, answered): one
`step_ctx` round is exactly the unit the shipped driver iterates
(`driveU`'s scrutinee is one `stepOutcomes` = one round;
DriverCollapse's `loop_step_frag` matches one production scheduler
round to it), so the relation whose graph this is IS the semantics
the package's adequacy theorems quantify over — no coarser
(a multi-round relation would hide the per-round refusal channels
adequacy must see) and no finer (sub-round structure is the engine's
internal control flow, not a Core-level transition).

THE RelSemCore DISCLAIMER (consistent with the README's "two
presentations, one engine" paragraph): `CerberusRound` is NOT bridged
to the semantics repo's own `RelSem.Machine.Step`/`runND_sound`/
`HarnessAdequate` spine, and no such bridge is claimed here. Both
are presentations of the one engine; this package's reference
relation is the engine round above. If a future RefinedC-style
semantic-type layer claims `RelSemCore` as ITS reference semantics,
that bridge must be proved BEFORE the type layer is built (charter
P3.2: "do not let the type layer make this choice implicitly").

WHAT IS PROVED HERE (the R-03 form the charter accepts — an
exhaustive sum classification, because a global iff is falsified by
the value protocol: at an ANNOTATED VALUE the engine performs a
REMOVE-ANNOT round (a successful-next) while the mirror treats the
configuration as a value and does not step, and by the refusal
channels): for every well-sized `Frag` configuration at a
sequentially well-formed context with a cons-shaped environment
stack, `cerberusRound_classify` yields EXACTLY ONE of

- `value_done`   — a bare value; the engine's round is PROGRAM-DONE
                   (`[.done v]`);
- `value_annot`  — an annotated value; the engine's round is
                   REMOVE-ANNOT (a successful-next to the bare value,
                   env and memory verbatim) — NOT a mirror step, by
                   the mirror's value protocol (`toVal`);
- `step`         — the mirror steps, and then for EVERY c':
                   `Step M c c' ↔ CerberusRound M aid c c'`
                   (the two-sided arm: the engine's round is exactly
                   the mirror's step, and conversely; mirror
                   determinism falls out);
- `refused`      — the mirror is STUCK at a non-value configuration
                   (¬ NotStuck: no mirror step, no value).

The classification is exhaustive over `Frag` by construction (its
hypothesis is `Frag e`; the row set of the capability manifest IS
`Frag`'s constructor list) and its `step` arm carries the engine
content (through `engine_step_matchU`). THE RESIDUAL, stated
honestly: the `refused` arm says nothing about the ENGINE's behavior
at a mirror-stuck configuration — the engine may kill, report
ILLTYPED, produce an off-fragment form, or PANIC (`failwithI`, an
OPAQUE constant: no equation about its value is provable, so a
kernel-level classification of a panic channel as "not a
successful-next" is IMPOSSIBLE, not merely unproved). Per-row
refusal classification exists where the engine's refusal channel is
a memory kill or an ILLTYPED report: `cerberusRound_refused_store`,
`_load`, `_create`, `_case` below (store/case from the existing
`engine_complete_storeU`/`_caseU`; load/create new here). The rows
whose refusal channels include a `failwithI` panic (if/run/save/
pure/the operand-evaluation rows/the binder betas) or the memop ND
fork (memop-ptreq) remain ONE-SIDED at the refusal arm — the precise
R-03 residual, recorded in the closure table.

WHAT ADEQUACY NEEDS is the `step` and value arms only: the WP's
`NotStuck` supplies a mirror step (or a value) at every reachable
configuration, and there the engine agrees exactly. The `refused`
arm is exactly the set adequacy excludes.
-/
import CerberusHeapLang.Soundness

set_option autoImplicit false

namespace CerberusHeapLang

/-- A Core configuration: expression, live environment stack, memory. -/
abbrev Config : Type := CoreExpr × EnvStack × Mem

/-- THE ENGINE-FACING ONE-ROUND RELATION: the graph of the discharged
    `step_ctx` round at context `M` with action-id draw `aid`. -/
def CerberusRound (M : MachineCtx) (aid : Nat) (c c' : Config) : Prop :=
  outcomesU M aid c.1 c.2.1 c.2.2 = [.next (M.thread c'.1 c'.2.1) c'.2.2]

/-- The thread literal is injective in (expression, env). -/
theorem MachineCtx.thread_inj {M : MachineCtx} {e e' : CoreExpr} {ρ ρ' : EnvStack}
    (h : M.thread e ρ = M.thread e' ρ') : e = e' ∧ ρ = ρ' :=
  ⟨congrArg thread_state.arena h, congrArg thread_state.env h⟩

/-- MATCH-GIVEN-STEP as a relation inclusion: on the well-sized cone,
    every mirror step is an engine round (`engine_step_matchU`
    re-read). -/
theorem Step.toCerberusRound {M : MachineCtx} (aid : Nat) {e : CoreExpr}
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {σ : Mem} {c' : Config}
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel)
    (hs : Step M (e, ev0 :: evs, σ) c') :
    CerberusRound M aid (e, ev0 :: evs, σ) c' := by
  obtain ⟨e', ρ', σ'⟩ := c'
  exact engine_step_matchU aid hf hsz hs

/-- THE TWO-SIDED ARM: wherever the mirror steps at all, `Step` and
    `CerberusRound` coincide (both directions), for every successor. -/
theorem step_iff_cerberusRound {M : MachineCtx} (aid : Nat) {e : CoreExpr}
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {σ : Mem}
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel)
    (hstep : ∃ c', Step M (e, ev0 :: evs, σ) c') (c' : Config) :
    Step M (e, ev0 :: evs, σ) c' ↔ CerberusRound M aid (e, ev0 :: evs, σ) c' := by
  constructor
  · exact Step.toCerberusRound aid hf hsz
  · intro hr
    obtain ⟨c₀, hs₀⟩ := hstep
    have hr₀ := Step.toCerberusRound aid hf hsz hs₀
    obtain ⟨e', ρ', σ'⟩ := c'
    obtain ⟨e₀, ρ₀, σ₀⟩ := c₀
    unfold CerberusRound at hr hr₀
    rw [hr₀] at hr
    have h1 : M.thread e₀ ρ₀ = M.thread e' ρ' := by
      injection hr with h _; injection h
    have h2 : σ₀ = σ' := by
      injection hr with h _; injection h
    obtain ⟨rfl, rfl⟩ := MachineCtx.thread_inj h1
    subst h2
    exact hs₀

/-- The exhaustive per-configuration classification (statement in the
    module header). -/
inductive RoundClass (M : MachineCtx) (aid : Nat) (c : Config) : Prop where
  | value_done (v : value) :
      c.1 = ofVal (.pure v) →
      outcomesU M aid c.1 c.2.1 c.2.2 = [.done v] →
      RoundClass M aid c
  | value_annot (ds : List dyn_annotation) (v : value) :
      c.1 = ofVal (.annot ds v) →
      outcomesU M aid c.1 c.2.1 c.2.2 =
        [.next (M.thread (ofVal (.pure v)) c.2.1) c.2.2] →
      RoundClass M aid c
  | step (c' : Config) :
      Step M c c' →
      (∀ c'', Step M c c'' ↔ CerberusRound M aid c c'') →
      RoundClass M aid c
  | refused :
      toVal c.1 = none →
      (∀ c', ¬ Step M c c') →
      RoundClass M aid c

/-- THE CLASSIFICATION THEOREM (R-03, charter P3.2 — the exhaustive sum
    form): every well-sized `Frag` configuration at a sequentially
    well-formed context with a cons-shaped env stack falls into
    exactly one `RoundClass` arm; the `step` arm is two-sided. -/
theorem cerberusRound_classify {M : MachineCtx} (hwf : M.SeqWF) (aid : Nat)
    {e : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {σ : Mem}
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel) :
    RoundClass M aid (e, ev0 :: evs, σ) := by
  cases hv : toVal e with
  | some w =>
    have he : ofVal w = e := ofVal_of_toVal hv
    cases w with
    | pure v =>
      refine .value_done v he.symm ?_
      show outcomesU M aid e (ev0 :: evs) σ = [.done v]
      rw [← he]
      exact outcomesU_done hwf aid v (ev0 :: evs) σ
    | annot ds v =>
      refine .value_annot ds v he.symm ?_
      show outcomesU M aid e (ev0 :: evs) σ = [.next (M.thread (ofVal (.pure v)) (ev0 :: evs)) σ]
      rw [← he]
      exact outcomesU_remove_annot M aid ds v (ev0 :: evs) σ
  | none =>
    by_cases hstep : ∃ c', Step M (e, ev0 :: evs, σ) c'
    · obtain ⟨c', hs⟩ := hstep
      exact .step c' hs (step_iff_cerberusRound aid hf hsz ⟨c', hs⟩)
    · exact .refused hv (fun c' hs => hstep ⟨c', hs⟩)

/-- The arms are mutually exclusive (the classification is a
    partition, not merely a cover): a value is never a mirror step
    (value protocol), and `step`/`refused` contradict directly. -/
theorem RoundClass.value_not_step {M : MachineCtx} {c : Config} {w : SpikeVal}
    (he : c.1 = ofVal w) : ∀ c', ¬ Step M c c' := by
  intro c' hs
  obtain ⟨e, ρ, σ⟩ := c
  simp only at he
  subst he
  exact hs.val_elim

/-! ## Per-row REFUSAL classification — the two-sided rows

Where the mirror is stuck at one of these redexes, the engine's
round is a SINGLETON REFUSAL (`.killed`/`.error`/`.offFragment` —
`EngineOutcome.isRefusal`), never a successful-next: store and case
from the existing completeness pairs, load and create proved here
against the same discharge lemmas. -/

/-- LOAD IS TWO-SIDED at any context: the engine's round at a load
    redex is a singleton; it is the mirror step exactly when the
    mirror can step (active loadM), and a refusal (the killed
    channel) exactly where the mirror is provably stuck. -/
theorem engine_complete_loadU (M : MachineCtx) (aid : Nat)
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pv : CerbMem.PointerValue} {mo : memory_order}
    (hlib : CerbLocation.isLibraryLocation loc = false)
    (ρ : EnvStack) (σ : Mem) :
    ∃ o, outcomesU M aid (loadRedex loc ann ty pv mo) ρ σ = [o] ∧
      EngineMatchU M (loadRedex loc ann ty pv mo) ρ σ o := by
  have hsz : esize (loadRedex loc ann ty pv mo) ≤ lemDefaultFuel := by
    rw [show esize (loadRedex loc ann ty pv mo) = 1 from rfl]
    unfold lemDefaultFuel
    omega
  cases hmem : applyMemM (CerbMem.loadM loc ty pv) σ with
  | some r =>
    obtain ⟨⟨fp, mval⟩, σ'⟩ := r
    refine ⟨_, ?_, .step (Step.load_canonical hmem)⟩
    unfold outcomesU engineStepsU loadRedex
    rw [step_ctx_load (Decomp.root (Redex.load hlib)) hsz hlib M.tagDefs σ
      M.file M.extern M.tid M.parent (M.thread _ ρ) rfl]
    simp only [List.map_cons, List.map_nil]
    rw [dischargeStep_load_active hmem]
    rfl
  | none =>
    refine ⟨dischargeStep aid M.runState σ (Step_action_request2
        "LoadRequest" loc M.tid (is_unseq_with_ccall CTX)
        (stExceptUndef_return (LoadRequest2 mo ty pv (fun _ fp mval =>
          { M.thread (loadRedex loc ann ty pv mo) ρ with
            arena := apply_ctx CTX (Expr [] (Eannot [DA_pos [] fp]
              (Expr [] (Epure (Pexpr [] () (PEval
                (valueFromMemValue mval).2)))))) })))),
      ?_, ?_⟩
    · unfold outcomesU engineStepsU loadRedex
      rw [step_ctx_load (Decomp.root (Redex.load hlib)) hsz hlib M.tagDefs σ
        M.file M.extern M.tid M.parent (M.thread _ ρ) rfl]
      rfl
    · refine .refused (dischargeStep_load_refusal hmem) (fun out hstep => ?_) rfl
      obtain ⟨fp', mval', σ'', hmem', -⟩ := hstep.load_inv
      rw [hmem] at hmem'
      cases hmem'

/-- CREATE IS TWO-SIDED at any context: the engine's round at a create
    redex is a singleton; the mirror step exactly when allocateObject
    is active, the refusal (the out-of-memory kill) exactly where the
    mirror is provably stuck. -/
theorem engine_complete_createU (M : MachineCtx) (aid : Nat)
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {align : CerbMem.IntegerValue} {ty : ctype} {pref : prefix0}
    (hlib : CerbLocation.isLibraryLocation loc = false)
    (ρ : EnvStack) (σ : Mem) :
    ∃ o, outcomesU M aid (createRedex loc ann align ty pref) ρ σ = [o] ∧
      EngineMatchU M (createRedex loc ann align ty pref) ρ σ o := by
  have hsz : esize (createRedex loc ann align ty pref) ≤ lemDefaultFuel := by
    rw [show esize (createRedex loc ann align ty pref) = 1 from rfl]
    unfold lemDefaultFuel
    omega
  have hirr := allocateObject_arg_irrel 0 0 pref align ty (get_with_address []) none none
  cases hmem : applyMemM (CerbMem.allocateObject 0 pref align ty none none) σ with
  | some r =>
    obtain ⟨pv, σ'⟩ := r
    refine ⟨_, ?_, .step (Step.create_canonical hmem)⟩
    unfold outcomesU engineStepsU createRedex
    rw [step_ctx_create (Decomp.root (Redex.create hlib)) hsz hlib M.tagDefs σ
      M.file M.extern M.tid M.parent (M.thread _ ρ) rfl]
    simp only [List.map_cons, List.map_nil]
    rw [dischargeStep_create_active (hirr ▸ hmem)]
    rfl
  | none =>
    refine ⟨dischargeStep aid M.runState σ (Step_action_request2
        "CreateRequest" loc M.tid (is_unseq_with_ccall CTX)
        (stExceptUndef_return (CreateRequest2 pref align ty
          (get_with_address []) none (fun _ pv =>
          { M.thread (createRedex loc ann align ty pref) ρ with
            arena := apply_ctx CTX (Expr [] (Epure (Pexpr [] ()
              (PEval (Vobject (OVpointer pv)))))) })))),
      ?_, ?_⟩
    · unfold outcomesU engineStepsU createRedex
      rw [step_ctx_create (Decomp.root (Redex.create hlib)) hsz hlib M.tagDefs σ
        M.file M.extern M.tid M.parent (M.thread _ ρ) rfl]
      rfl
    · refine .refused (dischargeStep_create_refusal (hirr ▸ hmem)) (fun out hstep => ?_) rfl
      obtain ⟨pv', σ'', hmem', -⟩ := hstep.create_inv
      rw [hmem] at hmem'
      cases hmem'

/-- From a completeness pair to the refusal classification: at a
    non-value redex where the mirror is stuck, the engine's round is a
    singleton REFUSAL. -/
theorem EngineMatchU.refusal_of_stuck {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack}
    {σ : Mem} {o : EngineOutcome} (hm : EngineMatchU M e ρ σ o)
    (hnv : toVal e = none) (hstuck : ∀ c', ¬ Step M (e, ρ, σ) c') :
    o.isRefusal := by
  cases hm with
  | step hs => exact (hstuck _ hs).elim
  | removeAnnot he => subst he; simp [toVal, ofVal] at hnv
  | done he => subst he; simp [toVal, ofVal] at hnv
  | refused hr _ _ => exact hr

/-- The refusal classification at a STORE redex. -/
theorem cerberusRound_refused_store (M : MachineCtx) (aid : Nat)
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
    {ty : ctype} {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
    (hlib : CerbLocation.isLibraryLocation loc = false)
    (ρ : EnvStack) (σ : Mem)
    (hstuck : ∀ c', ¬ Step M (storeRedex loc ann lk ty pv cv mo, ρ, σ) c') :
    ∃ o, o.isRefusal ∧ outcomesU M aid (storeRedex loc ann lk ty pv cv mo) ρ σ = [o] := by
  obtain ⟨o, ho, hm⟩ := engine_complete_storeU M aid hlib ρ σ
  exact ⟨o, hm.refusal_of_stuck rfl hstuck, ho⟩

/-- The refusal classification at a LOAD redex. -/
theorem cerberusRound_refused_load (M : MachineCtx) (aid : Nat)
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pv : CerbMem.PointerValue} {mo : memory_order}
    (hlib : CerbLocation.isLibraryLocation loc = false)
    (ρ : EnvStack) (σ : Mem)
    (hstuck : ∀ c', ¬ Step M (loadRedex loc ann ty pv mo, ρ, σ) c') :
    ∃ o, o.isRefusal ∧ outcomesU M aid (loadRedex loc ann ty pv mo) ρ σ = [o] := by
  obtain ⟨o, ho, hm⟩ := engine_complete_loadU M aid hlib ρ σ
  exact ⟨o, hm.refusal_of_stuck rfl hstuck, ho⟩

/-- The refusal classification at a CREATE redex (the out-of-memory
    kill, CerbMem.lean:1479 — the arm `allocCap`'s plan-fit excludes). -/
theorem cerberusRound_refused_create (M : MachineCtx) (aid : Nat)
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {align : CerbMem.IntegerValue} {ty : ctype} {pref : prefix0}
    (hlib : CerbLocation.isLibraryLocation loc = false)
    (ρ : EnvStack) (σ : Mem)
    (hstuck : ∀ c', ¬ Step M (createRedex loc ann align ty pref, ρ, σ) c') :
    ∃ o, o.isRefusal ∧ outcomesU M aid (createRedex loc ann align ty pref) ρ σ = [o] := by
  obtain ⟨o, ho, hm⟩ := engine_complete_createU M aid hlib ρ σ
  exact ⟨o, hm.refusal_of_stuck rfl hstuck, ho⟩

/-- The refusal classification at a value-scrutinee CASE redex (the
    ILLTYPED no-match report). -/
theorem cerberusRound_refused_case (M : MachineCtx) (aid : Nat)
    {b : List annot} {cval : value} {pats : List (pattern × CoreExpr)}
    (hsz : esize (caseRedex (Pexpr b () (PEval cval)) pats) ≤ lemDefaultFuel)
    (ρ : EnvStack) (σ : Mem)
    (hstuck : ∀ c', ¬ Step M (caseRedex (Pexpr b () (PEval cval)) pats, ρ, σ) c') :
    ∃ o, o.isRefusal ∧
      outcomesU M aid (caseRedex (Pexpr b () (PEval cval)) pats) ρ σ = [o] := by
  obtain ⟨o, ho, hm⟩ := engine_complete_caseU M aid hsz ρ σ
  exact ⟨o, hm.refusal_of_stuck rfl hstuck, ho⟩

end CerberusHeapLang
