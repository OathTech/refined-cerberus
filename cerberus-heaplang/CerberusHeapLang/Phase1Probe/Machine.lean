/-
CerberusHeapLang.Phase1Probe.Machine — PHASE-1 PROBE MODULE (S1a).

PROBE STATUS: this module (and everything under Phase1Probe/) is
the S1a architecture probe for the foundations arc's Phase 1
(docs/2026-08-31_foundations-arc-plan.md; audit F-03). It builds
the UNIFIED configuration — an explicit `MachineCtx` carrying every
engine-configuration component outside (expression, env, memory) —
and re-indexes a REPRESENTATIVE SUBSET of the mirror relation over
it: `store` (straight-line), `run` (jump), and value-scrutinee
`case` (the Phase-0 RED row). It lives ALONGSIDE the existing cones
(Step/FragP/FragJ/...): the S1b migration replaces them; nothing
here is consumed by the existing exported corpus. Design record:
docs/2026-08-31_phase1-design-record.md.

THE CONFIGURATION SPLIT. An engine configuration at one sequential
step is exactly
  step_ctx tds σ file ext tid (parent, th)   +   dischargeStep aid rs σ
(Soundness.lean). Everything in it except (th.arena, th.env, σ) is
immutable under the supported fragment (the engine's successors are
`{th with arena := _, env := _}` record updates and the run state is
returned verbatim — the per-rule step_ctx/discharge lemmas show it
field by field). `MachineCtx` names ALL of those immutables
explicitly; the live state is the (CoreExpr × EnvStack × Mem)
triple, unchanged. No frozen example constants remain in the
relation: `spikeCtx`/`procCtx` below are INSTANCES (definitionally
equal to the old frozen profiles), not parts of the judgment.

WF constraints carried as explicit hypotheses (never implicit):
- `SeqWF` (stack empty, no parent thread): read by the VALUE
  protocol only (step_ctx's PROGRAM-DONE vs RETURN/THREAD-DONE
  dispatch). A nonempty stack is procedure-return territory —
  outside the supported fragment; permanent for the sequential
  single-procedure fragment.
- `extern = fmapEmpty` (probe restriction on the RUN
  characterization only): the engine resolves the current procedure
  AND every PEsym through the extern indirection with identity
  fallback (step_ctx Erun arm; eval_pexpr's PEsym arm,
  Core_eval.lean:142). The mirror's pure evaluator does not thread
  extern yet, so the evaluator bridge (Soundness.lean) is proved at
  the empty extern. Registered mover: S1b threads extern through
  `evalPexpr` + the bridge tower (design record §4).

THE LABEL MAP IS DERIVED, NOT CARRIED. The old `Step` took the
label map `Q` as an extra index tied to the run state by a
`LabeledAt` side hypothesis on every J-lane theorem. Here
`MachineCtx.labels` COMPUTES the current procedure's label fiber
from the ctx's own `proc`/`extern`/`runState.labeled` exactly as
step_ctx's Erun arm reads it — the tie hypothesis disappears from
the theorems (it is a definition now), and the label-lookup-failure
panic channels are fail-closed absences of a step, as before.
-/
import CerberusHeapLang.Soundness

set_option autoImplicit false

namespace CerberusHeapLang

/-! ## The machine context -/

/-- Every immutable component of an engine configuration: the
    parameters of `step_ctx` (tagDefs, file, extern, tid, parent),
    the non-(arena/env) fields of the thread state, and the run
    state the discharge protocol threads (read-only under the
    fragment — Erun reads `labeled` through it; per-step aid draws
    remain per-step parameters, as in the driver). -/
structure MachineCtx where
  tagDefs : Fmap sym (CerbLocation.Loc × tag_definition)
  file : generic_file Unit core_run_annotation
  extern : Fmap sym sym
  tid : Nat
  parent : Option Nat
  stack : stack core_run_annotation
  errno : CerbMem.PointerValue
  proc : Option sym
  execLoc : exec_location
  currentLoc : CerbLocation.Loc
  runState : core_run_state

namespace MachineCtx

/-- The thread state a context builds around live (expression, env).
    Explicit literal so record updates of it reduce definitionally
    (the `envThread` precedent, Soundness.lean). -/
def thread (M : MachineCtx) (e : CoreExpr) (ρ : EnvStack) : thread_state :=
  { arena := e, stack0 := M.stack, errno := M.errno, env := ρ,
    current_proc_opt := M.proc, exec_loc := M.execLoc,
    current_loc := M.currentLoc }

@[simp] theorem thread_arena (M : MachineCtx) (e : CoreExpr) (ρ : EnvStack) :
    (M.thread e ρ).arena = e := rfl

@[simp] theorem thread_env (M : MachineCtx) (e : CoreExpr) (ρ : EnvStack) :
    (M.thread e ρ).env = ρ := rfl

/-- The sequential single-procedure well-formedness the VALUE
    protocol reads (PROGRAM-DONE selection in step_ctx's value arm):
    empty call stack, startup thread. Permanent for the supported
    fragment (procedure return is outside it). -/
structure SeqWF (M : MachineCtx) : Prop where
  stack : M.stack = Stack_empty
  parent : M.parent = none

/-- The engine's extern indirection with identity fallback —
    verbatim the `proc_sym` computation of step_ctx's Erun arm
    (Core_reduction.lean:484). -/
def resolveProc (M : MachineCtx) (p : sym) : sym :=
  match fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
      Lem_Basic_classes.ordCompare s1 s2) p M.extern with
  | some q => q
  | none => p

theorem resolveProc_of_extern_empty {M : MachineCtx}
    (hext : M.extern = fmapEmpty) (p : sym) : M.resolveProc p = p := by
  unfold resolveProc
  rw [hext]
  rfl

/-- The current procedure's registered label fiber, read from the
    context exactly as step_ctx's Erun arm reads it (two-level
    `labeled` lookup at the extern-resolved current proc). Lookup
    failure and the no-current-proc case collapse to the EMPTY map:
    `lookupLabel fmapEmpty _ = none`, so the jump rule cannot fire
    there — the engine's failwithI panic channels are mirrored
    fail-closed as absence of a step. -/
def labels (M : MachineCtx) : LabelMap :=
  match M.proc with
  | none => fmapEmpty
  | some p =>
    match fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
        Lem_Basic_classes.ordCompare s1 s2)
        (M.resolveProc p) M.runState.labeled with
    | some Q => Q
    | none => fmapEmpty

/-- The label fiber at a known current procedure (the outer match
    reduced). -/
theorem labels_eq_of_proc {M : MachineCtx} {p : sym} (hp : M.proc = some p) :
    M.labels =
      (match fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
          Lem_Basic_classes.ordCompare s1 s2)
          (M.resolveProc p) M.runState.labeled with
        | some Q => Q
        | none => fmapEmpty) := by
  unfold labels
  rw [hp]

/-- A successful label lookup certifies the whole read path: there
    IS a current procedure and its resolved fiber IS `M.labels` (the
    old `LabeledAt` tie, now a derived fact instead of a hypothesis). -/
theorem labels_lookup_some {M : MachineCtx} {l : sym}
    {pc : List (sym × core_base_type) × CoreExpr}
    (h : lookupLabel M.labels l = some pc) :
    ∃ p, M.proc = some p ∧
      LabeledAt M.runState (M.resolveProc p) M.labels := by
  cases hp : M.proc with
  | none =>
    rw [show M.labels = fmapEmpty by unfold labels; rw [hp],
      lookupLabel_empty] at h
    cases h
  | some p =>
    have hlab := labels_eq_of_proc (M := M) hp
    cases hQ : fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
        Lem_Basic_classes.ordCompare s1 s2)
        (M.resolveProc p) M.runState.labeled with
    | none =>
      rw [hQ] at hlab
      rw [show M.labels = fmapEmpty from hlab, lookupLabel_empty] at h
      cases h
    | some Q =>
      rw [hQ] at hlab
      have hlab' : M.labels = Q := hlab
      exact ⟨p, rfl, show fmapLookupBy _ _ _ = some M.labels by
        rw [hlab']; exact hQ⟩

end MachineCtx

/-! ## The engine entry at a machine context -/

/-- One engine step at context `M` — `step_ctx` with every immutable
    supplied by the context (the generalization of `engineSteps`/
    `engineStepsP`, which pinned them to the frozen profiles). -/
def engineStepsU (M : MachineCtx) (e : CoreExpr) (ρ : EnvStack) (σ : Mem) :
    List core_step2 :=
  step_ctx M.tagDefs σ M.file M.extern M.tid (M.parent, M.thread e ρ)

/-- ... discharged against the context's run state. -/
def outcomesU (M : MachineCtx) (aid : Nat) (e : CoreExpr) (ρ : EnvStack)
    (σ : Mem) : List EngineOutcome :=
  (engineStepsU M e ρ σ).map (dischargeStep aid M.runState σ)

/-! ## The frozen profiles, recovered as INSTANCES -/

/-- The old straight-line frozen profile as a context instance.
    Definitional ties below show the old `engineSteps`/`drive`
    entries are exactly this instance — the frozen constants become
    one point of the context space. -/
def spikeCtx : MachineCtx :=
  { tagDefs := fmapEmpty, file := spikeFile, extern := fmapEmpty,
    tid := 0, parent := none, stack := Stack_empty, errno := default,
    proc := none, execLoc := default, currentLoc := default,
    runState := spikeRunState }

/-- The old jump profile (proc-carrying thread, parameterized run
    state) as a context instance. -/
def procCtx (p : sym) (rs : core_run_state) : MachineCtx :=
  { spikeCtx with proc := some p, runState := rs }

theorem spikeCtx_thread (e : CoreExpr) (ρ : EnvStack) :
    spikeCtx.thread e ρ = envThread e ρ := rfl

theorem procCtx_thread (p : sym) (rs : core_run_state) (e : CoreExpr)
    (ρ : EnvStack) : (procCtx p rs).thread e ρ = procThread p e ρ := rfl

theorem engineStepsU_spike (e : CoreExpr) (ρ : EnvStack) (σ : Mem) :
    engineStepsU spikeCtx e ρ σ = engineSteps e ρ σ := rfl

theorem outcomesU_spike (aid : Nat) (e : CoreExpr) (ρ : EnvStack) (σ : Mem) :
    outcomesU spikeCtx aid e ρ σ = engineOutcomes aid e ρ σ := rfl

theorem engineStepsU_proc (p : sym) (rs : core_run_state) (e : CoreExpr)
    (ρ : EnvStack) (σ : Mem) :
    engineStepsU (procCtx p rs) e ρ σ = engineStepsP p e ρ σ := rfl

theorem outcomesU_proc (p : sym) (rs : core_run_state) (aid : Nat)
    (e : CoreExpr) (ρ : EnvStack) (σ : Mem) :
    outcomesU (procCtx p rs) aid e ρ σ = engineOutcomesP p aid rs e ρ σ := rfl

@[simp] theorem spikeCtx_labels : spikeCtx.labels = spikeLbl := rfl

theorem spikeCtx_wf : spikeCtx.SeqWF := ⟨rfl, rfl⟩

theorem procCtx_wf (p : sym) (rs : core_run_state) :
    (procCtx p rs).SeqWF := ⟨rfl, rfl⟩

/-! ## The unified mirror relation (probe subset)

One relation over (context × live state): the re-indexed `Step` for
the probe's representative constructs. Each rule is the
corresponding `Step` rule VERBATIM except for the index change:
- `store`: the encoding premise is at `M.tagDefs` (the engine's
  memValueFromValue read — the old rule hard-coded `fmapEmpty`);
- `run`: the label lookup is in the DERIVED `M.labels` (the old
  rule's extra `Q` index + `LabeledAt` tie);
- `case_value`: identical (it reads no context at all) — the F-01
  RED row's rule, entering the unified cone below. -/
inductive StepU (M : MachineCtx) :
    CoreExpr × EnvStack × Mem → CoreExpr × EnvStack × Mem → Prop where
  /-- Positive strong store, evaluated operands (Step.store with the
      encoding read at the context's tagDefs). -/
  | store {a : List annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {lk : Bool} {pe1 pe2 pe3 : generic_pexpr Unit sym}
      {ty : ctype} {pv : CerbMem.PointerValue} {cv : value}
      {mo : memory_order} {mv : CerbMem.MemValue} {fp : CerbMem.Footprint}
      {ρ : EnvStack} {σ σ' : Mem}
      (h1 : valueFromPexpr pe1 = some (Vctype ty))
      (h2 : valueFromPexpr pe2 = some (Vobject (OVpointer pv)))
      (h3 : valueFromPexpr pe3 = some cv)
      (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv = some mv)
      (hmem : applyMemM (CerbMem.storeM loc ty lk pv mv) σ = some (fp, σ')) :
      StepU M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Store0 lk pe1 pe2 pe3 mo)))), ρ, σ)
           (Expr [] (Eannot [DA_pos [] fp]
              (Expr [] (Epure (Pexpr [] () (PEval Vunit))))), ρ, σ')
  /-- The global jump (Step.run with the label map derived from the
      context). -/
  | run {e : CoreExpr} {l : sym} {pes : List (generic_pexpr Unit sym)}
      {params : List (sym × core_base_type)} {cont : CoreExpr}
      {vs : List value} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
      {σ : Mem}
      (hj : jumpRedex? e = some (l, pes))
      (hl : lookupLabel M.labels l = some (params, cont))
      (hvs : evalPexprs (ev0 :: evs) pes = some vs) :
      StepU M (e, ev0 :: evs, σ)
           (cont, bindArgs params vs (ev0 :: evs), σ)
  /-- Ecase at a VALUE scrutinee (Step.case_value verbatim — no
      context read). -/
  | case_value {a : List annot} {pe : generic_pexpr Unit sym}
      {pats : List (pattern × CoreExpr)} {cval : value} {e' : CoreExpr}
      {ρ : EnvStack} {σ : Mem}
      (hv : valueFromPexpr pe = some cval)
      (hsel : select_case subst_sym_expr cval pats = some e') :
      StepU M (Expr a (Ecase pe pats), ρ, σ) (e', ρ, σ)

/-- Canonical-operand instance of the store rule (the shape the
    small axiom fires at — the Step.store_canonical analog). -/
theorem StepU.store_canonical {M : MachineCtx} {a : List annot}
    {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {lk : Bool} {ty : ctype}
    {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
    {mv : CerbMem.MemValue} {fp : CerbMem.Footprint}
    {ρ : EnvStack} {σ σ' : Mem}
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv = some mv)
    (hmem : applyMemM (CerbMem.storeM loc ty lk pv mv) σ = some (fp, σ')) :
    StepU M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Store0 lk (Pexpr [] () (PEval (Vctype ty)))
                       (Pexpr [] () (PEval (Vobject (OVpointer pv))))
                       (Pexpr [] () (PEval cv)) mo)))), ρ, σ)
         (Expr [] (Eannot [DA_pos [] fp]
            (Expr [] (Epure (Pexpr [] () (PEval Vunit))))), ρ, σ') :=
  StepU.store rfl rfl rfl hmv hmem

/-! ## Inversions (three constructors: every inversion is one
`cases` with head-shape auto-refutation — the payoff of the unified
index is visible already at probe scale) -/

/-- Values do not step. -/
theorem StepU.val_elim {M : MachineCtx} {w : SpikeVal} {ρ : EnvStack} {σ : Mem}
    {out : CoreExpr × EnvStack × Mem}
    (h : StepU M (ofVal w, ρ, σ) out) : False := by
  cases w with
  | pure v =>
    cases h with
    | run hj hl hvs => simp [ofVal] at hj
  | annot ds v =>
    cases h with
    | run hj hl hvs => simp [ofVal, jumpRedex?, annotRooted] at hj

theorem StepU.toVal_none {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack}
    {σ : Mem} {out : CoreExpr × EnvStack × Mem}
    (h : StepU M (e, ρ, σ) out) : toVal e = none := by
  cases hv : toVal e with
  | none => rfl
  | some w => exact absurd (ofVal_of_toVal hv ▸ h) (fun h => h.val_elim)

/-- Inversion at a canonical store redex. -/
theorem StepU.store_inv {M : MachineCtx} {a : List annot}
    {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {lk : Bool} {ty : ctype}
    {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
    {ρ : EnvStack} {σ : Mem} {out : CoreExpr × EnvStack × Mem}
    (h : StepU M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Store0 lk (Pexpr [] () (PEval (Vctype ty)))
                       (Pexpr [] () (PEval (Vobject (OVpointer pv))))
                       (Pexpr [] () (PEval cv)) mo)))), ρ, σ) out) :
    ∃ mv fp σ',
      memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv = some mv ∧
      applyMemM (CerbMem.storeM loc ty lk pv mv) σ = some (fp, σ') ∧
      out = (Expr [] (Eannot [DA_pos [] fp]
              (Expr [] (Epure (Pexpr [] () (PEval Vunit))))), ρ, σ') := by
  cases h with
  | run hj hl hvs => simp at hj
  | store h1 h2 h3 hmv hmem =>
    rw [valueFromPexpr_val] at h1 h2 h3
    injection h1 with h1; injection h1 with h1
    injection h2 with h2; injection h2 with h2; injection h2 with h2
    injection h3 with h3
    subst h1 h2 h3
    exact ⟨_, _, _, hmv, hmem, rfl⟩

/-- Inversion at a registered jump redex: every step is THE jump. -/
theorem StepU.jump_inv {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack}
    {σ : Mem} {out : CoreExpr × EnvStack × Mem} {l : sym}
    {pes : List (generic_pexpr Unit sym)}
    (hj : jumpRedex? e = some (l, pes))
    (h : StepU M (e, ρ, σ) out) :
    ∃ params cont vs ev0 evs, ρ = ev0 :: evs ∧
      lookupLabel M.labels l = some (params, cont) ∧
      evalPexprs ρ pes = some vs ∧
      out = (cont, bindArgs params vs ρ, σ) := by
  cases h with
  | run hj' hl hvs =>
    obtain ⟨rfl, rfl⟩ : l = _ ∧ pes = _ := by
      have := hj.symm.trans hj'
      exact ⟨(Prod.mk.injEq _ _ _ _ ▸ Option.some.inj this).1,
        (Prod.mk.injEq _ _ _ _ ▸ Option.some.inj this).2⟩
    exact ⟨_, _, _, _, _, rfl, hl, hvs, rfl⟩
  | store h1 h2 h3 hmv hmem => simp at hj
  | case_value hv hsel => simp [jumpRedex?] at hj

/-- Inversion at an Ecase node. -/
theorem StepU.case_inv {M : MachineCtx} {a : List annot}
    {pe : generic_pexpr Unit sym} {pats : List (pattern × CoreExpr)}
    {ρ : EnvStack} {σ : Mem} {out : CoreExpr × EnvStack × Mem}
    (h : StepU M (Expr a (Ecase pe pats), ρ, σ) out) :
    ∃ cval e', valueFromPexpr pe = some cval ∧
      select_case subst_sym_expr cval pats = some e' ∧
      out = (e', ρ, σ) := by
  cases h with
  | case_value hv hsel => exact ⟨_, _, hv, hsel, rfl⟩
  | run hj hl hvs => simp [jumpRedex?] at hj

/-- A successful `valueFromPexpr` readout pins the operand's shape
    (Core_aux.lean:472 — only the PEval arm answers `some`). -/
theorem valueFromPexpr_some_shape {pe : generic_pexpr Unit sym} {v : value}
    (h : valueFromPexpr pe = some v) :
    ∃ b, pe = Pexpr b () (PEval v) := by
  rcases pe with ⟨b, u, pe_⟩
  cases u
  cases pe_ <;>
    first
    | (refine ⟨b, ?_⟩
       rw [valueFromPexpr_val] at h
       injection h with h
       rw [h])
    | (rw [show valueFromPexpr _ = none from rfl] at h; cases h)

/-! ## The unified capability cone (probe subset)

ONE cone predicate — the FragP/FragJ successor for the probe
constructs, over the SAME relation the logic and the engine
characterization use. Value-scrutinee `case` JOINS THE CONE here
(the F-01 export): its constructor carries branch-cone closure and
the branch-size bound as explicit premises.

PROBE LIMITATION (registered, design record §5): `esize` (the fuel
measure) has no `Ecase` arm — `esize (caseRedex _ _) = 1` — so the
size premise currently forces flat branches (values/actions/jumps —
esize 1). The S1b fix is the measure extension
`esize (Ecase pe pats) = 1 + max over branches` plus
esize-invariance of `subst_sym_expr`, after which the same premise
shape is dischargeable for arbitrary branches. This is a real
Phase-1 finding: the fuel accounting was never extended to Ecase —
one more face of the F-01 cone gap. -/
inductive FragU : CoreExpr → Prop where
  | val_pure (v : value) : FragU (Expr [] (Epure (Pexpr [] () (PEval v))))
  | annot_val (ds : List dyn_annotation) (v : value) :
      FragU (Expr [] (Eannot ds (Expr [] (Epure (Pexpr [] () (PEval v))))))
  | store {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
      {ty : ctype} {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
      (hlib : CerbLocation.isLibraryLocation loc = false) :
      FragU (storeRedex loc ann lk ty pv cv mo)
  | run {ra : core_run_annotation} {l : sym}
      {pes : List (generic_pexpr Unit sym)}
      (hdep : ∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel) :
      FragU (runRedex ra l pes)
  | case_value {b : List annot} {cval : value}
      {pats : List (pattern × CoreExpr)}
      (hbr : ∀ e', select_case subst_sym_expr cval pats = some e' → FragU e')
      (hbsz : ∀ e', select_case subst_sym_expr cval pats = some e' →
        esize e' ≤ esize (caseRedex (Pexpr b () (PEval cval)) pats)) :
      FragU (caseRedex (Pexpr b () (PEval cval)) pats)

theorem fragU_ofVal (w : SpikeVal) : FragU (ofVal w) := by
  cases w with
  | pure v => exact .val_pure v
  | annot ds v => exact .annot_val ds v

/-- CLOSURE UNDER STEPS — one theorem, one cone (the audit's
    "coverage cannot differ" mechanism at probe scale): the jump
    successors' membership comes from the label-cone hypothesis
    (the registered-continuation analog of drive_classifyJ's hQf),
    everything else is intrinsic. -/
theorem FragU.step {M : MachineCtx}
    (hQf : ∀ l params cont,
      lookupLabel M.labels l = some (params, cont) → FragU cont)
    {e e' : CoreExpr} {ρ ρ' : EnvStack} {σ σ' : Mem}
    (hf : FragU e) (hs : StepU M (e, ρ, σ) (e', ρ', σ')) : FragU e' := by
  cases hf with
  | val_pure v => exact (StepU.val_elim (w := .pure v) hs).elim
  | annot_val ds v => exact (StepU.val_elim (w := .annot ds v) hs).elim
  | store hlib =>
    obtain ⟨mv, fp, σ'', hmv, hmem, hout⟩ := hs.store_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact .annot_val _ _
  | run hdep =>
    obtain ⟨params, cont, vs, ev0, evs, -, hl, -, hout⟩ :=
      hs.jump_inv (jumpRedex?_run _ _ _ _)
    obtain ⟨h1, -, -⟩ : e' = cont ∧ ρ' = bindArgs params vs ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact hQf _ _ _ hl
  | case_value hbr hbsz =>
    obtain ⟨cval', e'', hv, hsel, hout⟩ := hs.case_inv
    obtain rfl : _ = cval' := Option.some.inj (valueFromPexpr_val _ _ ▸ hv)
    obtain ⟨h1, -, -⟩ : e' = e'' ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact hbr e' hsel

/-- The fuel accounting across a cone step: sizes grow by at most
    one, except at a jump — whose successor is a REGISTERED
    continuation (budgeted statically, the drive_classifyJ pattern). -/
theorem FragU.esize_step {M : MachineCtx}
    {e e' : CoreExpr} {ρ ρ' : EnvStack} {σ σ' : Mem}
    (hf : FragU e) (hs : StepU M (e, ρ, σ) (e', ρ', σ')) :
    esize e' ≤ esize e + 1 ∨
    ∃ l params cont, lookupLabel M.labels l = some (params, cont) ∧
      e' = cont := by
  cases hf with
  | val_pure v => exact (StepU.val_elim (w := .pure v) hs).elim
  | annot_val ds v => exact (StepU.val_elim (w := .annot ds v) hs).elim
  | store hlib =>
    obtain ⟨mv, fp, σ'', hmv, hmem, hout⟩ := hs.store_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left
    simp [esize, storeRedex]
  | run hdep =>
    obtain ⟨params, cont, vs, ev0, evs, -, hl, -, hout⟩ :=
      hs.jump_inv (jumpRedex?_run _ _ _ _)
    obtain ⟨h1, -, -⟩ : e' = cont ∧ ρ' = bindArgs params vs ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact .inr ⟨_, _, _, hl, rfl⟩
  | case_value hbr hbsz =>
    obtain ⟨cval', e'', hv, hsel, hout⟩ := hs.case_inv
    obtain rfl : _ = cval' := Option.some.inj (valueFromPexpr_val _ _ ▸ hv)
    obtain ⟨h1, -, -⟩ : e' = e'' ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left
    have := hbsz e' hsel
    omega

/-- Env cons-shapedness is preserved (the Step.env_cons analog). -/
theorem StepU.env_cons {M : MachineCtx} {e : CoreExpr} {ev0 : Fmap sym value}
    {evs : List (Fmap sym value)} {σ : Mem}
    {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    (h : StepU M (e, ev0 :: evs, σ) (e', ρ', σ')) :
    ∃ ev0', ρ' = ev0' :: evs := by
  cases h with
  | store h1 h2 h3 hmv hmem => exact ⟨ev0, rfl⟩
  | run hj hl hvs => exact bindArgs_cons _ _ _ _
  | case_value hv hsel => exact ⟨ev0, rfl⟩

end CerberusHeapLang
