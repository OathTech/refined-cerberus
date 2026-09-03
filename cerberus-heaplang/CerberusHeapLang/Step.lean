/-
CerberusHeapLang.Step — the fragment's small-step relation: a
hand-written mirror of the engine over the engine's own generated
Core types.

STATUS. `Step M` has ZERO independent authority: every rule carries a
citation into the engine (the cerberus-lean checkout pinned in
../scripts/semantics-pin.env; file:line references are into its
lean_frontend/generated/), and the relation is certified against the
engine's `step_ctx` plus the sequential driver's discharge in
Soundness.lean (`engine_step_matchU`: wherever the mirror steps at a
`Frag` configuration, the engine's discharged behaviour is exactly
that step). A wrong rule here can only make theorems unprovable,
never make an exported engine statement false. Two caveats bound
that guarantee: it does not cover the statement-level readout
vocabulary (`driveU`, `dischargeStep`, `Sat`/`CellCoh` — a wrong
definition THERE yields a true but irrelevant theorem, which is why
the walkthrough prints them), and coverage is fail-open by nature —
a missing rule narrows what is provable without falsifying anything;
the per-construct coverage authority is docs/CAPABILITY_MANIFEST.md.

SCOPE (the mirrored fragment): pure values; `Store0`/`Load0`/`Create0`
actions and the `Kill` action (kill/free arc K2 — any `kill_kind` in
`Step`; the fragment `Frag` admits the STATIC kill only until K3) at
evaluated operands and at the operands the engine
evaluates first (the ACTION_EVAL step); the `PtrEq` memop; strong
sequencing `Esseq` at the wildcard, `Specified`-binder and
plain-symbol-binder patterns; weak sequencing `Ewseq` at the
wildcard; `Esave`, `Eif`, value-scrutinee `Ecase`, the
context-discarding `Erun`; `PEsym`-shaped pure exits; and the
run-time `Eannot` residue those produce; and (calls arc C2) THE
PROCEDURE CALL `Eproc () (Sym f) pes` at `PePure` arguments and THE
RETURN — a value at a non-empty call stack — as mirror steps, certified
and classified, with NO logic rule yet (C3). Every rule uses the
CANONICAL node shapes (empty `List annot`, `()` at the base-type
slot) that `mk_value_e`/`mk_value_pe` (Core_aux.lean:302,645) and the
fragment's authored programs produce; the engine's redex patterns
accept arbitrary annotation lists in some positions (e.g. one_step0's
LETS-PURE, Core_reduction.lean:353), so `Step` is exact on the
fragment and a sub-relation elsewhere — a deliberate divergence
(README, "Registered divergences and limitations").

THE CONFIGURATION (calls arc C1, 2026-09-03 — the configuration
GROWS). The live state is the quadruple `Config := CoreExpr × EnvStack
× Ctl × Mem`: the arena, the environment stack, the thread's LIVE
CONTROL `Ctl` (the call stack `κ`, the current procedure `proc`, the
execution location `execLoc` — the three `thread_state` fields a
procedure call and a return WRITE, step_ctx's PCALL/RETURN arms,
Core_reduction.lean:484) and the memory. Everything else the engine's
configuration holds and the fragment leaves immutable — `step_ctx`'s
parameters (tag definitions, file, extern map, thread id, parent), the
thread's `errno`/`current_loc`, and the run state the discharge
protocol threads (read-only under the fragment: `Erun` reads `labeled`
through it; the PCALL round's argument map and `runEU` are
state-verbatim too) — is the explicit index `MachineCtx`; `M.thread e
ρ ctl` is the engine `thread_state` the configuration denotes. EXACTLY
TWO RULES WRITE THE CONTROL (calls arc C2): `Step.call` pushes the frame
`(ctl.proc, ctx)` — the caller's procedure and the CAPTURED evaluation
context of the call redex — sets the callee as the current procedure
and pushes the execution location; `Step.ret` pops the frame back.
Every other constructor threads `ctl` unchanged (`Step.ctl_cases`,
`Step.ctl_eq` under its two guards); the entry
controls are `spikeCtl` (empty stack, no procedure) and `procCtl p`
(empty stack, in procedure `p`). `spikeCtx` (the straight-line
profile) and `procCtx rs` (the profile with a run state) are INSTANCES
of `MachineCtx`, reducible so that `M.tagDefs`/`M.extern` unfold to
`fmapEmpty` in client proofs. The
action-id counter never enters the fragment's terms: positive
non-excluded actions annotate with `DA_pos [] fp` (step_action,
Core_reduction.lean:424 — `aid1` is unused in the continuation), so
`Step` needs no aid index.

DESIGN NOTES (each mirrors a specific engine behaviour):

1. THE ENVIRONMENT IS LIVE STATE. The engine's thread environment
   (`thread_state.env : List (Fmap sym value)`, Core_run_aux.lean:291)
   is part of the configuration. Wildcard-pattern betas return the
   env verbatim: the engine's `update_env` is the identity on a
   NONEMPTY env stack (Core_aux.lean:861-868, first arm) and a
   `failwithI` panic on an empty one — mirrored as ABSENCE of a step:
   the beta rules fire only at cons-shaped envs (panics are excluded
   by well-formedness shape, never absorbed). The congruence rules
   are stated env-general (a descent step's env update is
   thread-global) so the jump rule composes without restating them.

2. ACTION_EVAL PHRASING. The action rules are stated over
   EVALUATED-OPERAND PREMISES, not syntactic `PEval` patterns:
   `valueFromPexpr peᵢ = some vᵢ` (Core_aux.lean:472) — the engine's
   own request-path dispatch: step_action (Core_reduction.lean:424)
   issues the one-step ACTION_REQUEST exactly when
   `act_valueFromPexpr` succeeds on every operand, and
   `act_valueFromPexpr` (Core_reduction.lean:393) equals
   `valueFromPexpr` everywhere except the `PEconstrained` panic
   channel, which the `valueFromPexpr` premise excludes
   (`valueFromPexpr (PEconstrained …) = none`, so the premise is
   unsatisfiable — no step where the engine panics). Non-value
   operands (e.g. `store(x, a+b)`) take the engine's separate
   ACTION_EVAL step first (`Step.load_eval`/`store_eval`/
   `memop_eval`); the canonical `PEval` instances discharge the
   premises by `rfl` (`valueFromPexpr_val`).

3. THE LABEL MAP IS DERIVED FROM THE CONTEXT AT THE LIVE PROCEDURE.
   `M.labelsAt ctl.proc` is the CURRENT PROCEDURE's static label map —
   the engine's `labeled_continuations` (Core_run_aux.lean:187; the
   analogue of Caesium's `f_code`, RefinedC lifting.v:1002) — read
   from the context's run state at the control's procedure symbol
   through the extern indirection (`resolveExtern`), exactly as
   `step_ctx`'s `Erun` arm reads it at `th_st.current_proc_opt`
   (Core_reduction.lean:484). The runtime tuple `CoreRt` is
   `⟨e, ρ, ctl, M⟩` (Lang.lean); steps preserve `M` by construction of
   `primStep`, which is faithful because the engine never writes
   `labeled` on the sequential path; the control is carried by `Step`
   itself (unchanged by every rule of this slice — `Step.ctl_eq`).
   Clients pin the map with `LabeledAt rs p Q` (Soundness.lean — the
   engine's own `fmapLookupBy` spelling) and `procCtx_labels`.

4. THE GLOBAL JUMP RULE. `Erun` DISCARDS its evaluation context
   (step_ctx's Erun arm returns `{th_st with env := env', arena :=
   cont_expr}` — no `apply_ctx ctx`). The mirror: `jumpRedex?` is
   the structural redex search through the Esseq/Eannot spine (the
   SYNTACTIC image of the context-discard), and `Step.run` fires at
   ANY configuration whose spine hole is a registered `Erun`,
   replacing the whole expression. The congruence rules
   `sseq_ctx`/`annot_ctx` are GUARDED by `jumpRedex? _ = none` so
   that a jump of a subterm is never framed (the engine's
   `K[run l pes] --> cont`, never `K[cont]`). Consequence: no
   `Language.Context` instance for the Esseq frame is possible once
   jumps exist (a jump of e1 and of `Esseq pat e1 e2` step to the
   SAME configuration) — sequencing is proved directly instead
   (Wps.lean `wps_seq`, Wpt.lean `wpt_seq`).

5. Esave / Eif / Ecase are LOCAL rules in the engine's measured
   granularity: Esave entry is a pure TAU at value-shaped parameter
   pexprs (one_step0's Esave valueFromPexprs fast path,
   Core_reduction.lean:353), binding the parameters into the env, and
   an evaluation step otherwise (`Step.save_eval`); Eif takes ONE
   engine step with a BIG-STEP guard (TAU_WITH_RUNSTATE over
   `full_eval_pexpr` — the mirror premise is the pure evaluator
   `evalPexpr`, certified against the engine's evaluator in
   Soundness.lean; the non-boolean-guard panic channel is excluded
   because the rule fires only at `Vtrue`/`Vfalse` results); Ecase
   with a value scrutinee is a TAU into the substituted branch
   (`select_case`, Core_aux.lean:637; the no-match ILLTYPED channel
   is a refusal — absence of a premise; the PEconstrained-scrutinee
   panic is excluded by the `valueFromPexpr` premise). The Ecase
   EVAL arm (small-step scrutinee via `eval_pexpr1`) is not mirrored
   (README, "Deliberately not here").

Design history: the dated records under docs/.
-/
import Core_aux
import Core_run_aux
import Core_reduction
import CerbMem

set_option autoImplicit false

namespace CerberusHeapLang

/-- The fragment's program type: the engine's run-time instantiation
    `expr core_run_annotation = generic_expr core_run_annotation Unit sym`
    (Core.lean:1697/1244; core_run_annotation Core_run_aux.lean:82-88). -/
abbrev CoreExpr : Type := expr core_run_annotation

/-- The fragment's state: the concrete memory model's state, nothing
    else (no driver state, no thread state — recon §5.1). -/
abbrev Mem : Type := CerbMem.MemState

/-- The engine's environment stack: exactly
    `thread_state.env : List (Fmap sym value)`
    (Core_run_aux.lean:291-298). Frames are per-procedure; within a
    procedure the head frame grows monotonically (readiness §2.1
    item 6). Live state as of phase-1 S1 (probe pattern). -/
abbrev EnvStack : Type := List (Fmap sym value)

/-- The frozen entry environment: one empty frame — what the
    production driver parks for a parameterless `main`
    (ProdEntry.prodThread) and what the exported triples are stated
    at. Env-GENERAL statements quantify an `EnvStack` instead. -/
abbrev spikeEnv : EnvStack := [fmapEmpty]

/-! ## Values

The engine's terminal expression forms are `is_irreducible`'s two
value shapes (Core_reduction.lean:293): a bare pure value and a
ONE-layer Eannot-wrapped pure value (double layers force-reduce by
the ANNOTS merge). `SpikeVal` mirrors exactly that classification.

RECORDED DIVERGENCE (slice notes §D1): at an empty context the engine
additionally taus `{A}v --> v` (REMOVE-ANNOT, step_ctx's
`(CTX, Eannot(value))` arm, Core_reduction.lean:484) before reporting
`Step_done2 v`. Step does NOT include that top-level unwrap — the
annotated form is already a value here (carrying the same payload
`v`), because the iris-lean `ToVal` interface requires values not to
step and toVal to be a partial bijection. Artifact 4's readout
statement composes the two: `toVal e = some (.annot ds v)` will be
certified against the engine's `{A}v --> v --> Step_done2 v` tail. -/
inductive SpikeVal : Type where
  | pure (v : value)
  | annot (ds : List dyn_annotation) (v : value)

namespace SpikeVal

/-- The underlying Core value, annotations erased. -/
def val : SpikeVal → value
  | .pure v => v
  | .annot _ v => v

/-- Annotation-merge on values: what wrapping a value form in one more
    `Eannot ds` layer denotes. Mirrors combine_dyn_annotations = (++)
    (Core_reduction.lean:305-306) via the ANNOTS reduction. -/
def merge (ds : List dyn_annotation) : SpikeVal → SpikeVal
  | .pure v => .annot ds v
  | .annot ds' v => .annot (ds ++ ds') v

@[simp] theorem merge_merge (ds ds' : List dyn_annotation) (v : SpikeVal) :
    merge ds (merge ds' v) = merge (ds ++ ds') v := by
  cases v <;> simp [merge]

@[simp] theorem val_merge (ds : List dyn_annotation) (v : SpikeVal) :
    (merge ds v).val = v.val := by
  cases v <;> simp [merge, val]

/-- How a bound value's annotations flow into a continuation's value
    (`lets _ = v in e2` leaves e2's value alone; `lets _ = {A}v in e2`
    prefixes A — LETS-ANNOT + the eventual ANNOTS merge). Value-level
    form; the runtime-tuple form is `CerberusHeapLang.mergeInto`. -/
def mergeInto : SpikeVal → SpikeVal → SpikeVal
  | .pure _, w => w
  | .annot ds _, w => merge ds w

end SpikeVal

/-- Canonical expression of a value (the shape `mk_value_e` produces,
    Core_aux.lean:645, resp. the action continuations' Eannot wrap,
    Core_reduction.lean:424). -/
def ofVal : SpikeVal → CoreExpr
  | .pure v => Expr [] (Epure (Pexpr [] () (PEval v)))
  | .annot ds v => Expr [] (Eannot ds (Expr [] (Epure (Pexpr [] () (PEval v)))))

/-- Partial inverse of `ofVal`: accepts exactly the canonical value
    shapes (mirror of is_irreducible's value forms restricted to
    canonical annotation lists — slice notes §D3). The annotation
    lists are checked by `isEmpty` guards rather than `[]` patterns so
    the match dispatches on the expression constructors only (and thus
    reduces on non-value shapes with symbolic annotation lists). -/
def toVal : CoreExpr → Option SpikeVal
  | Expr a (Epure (Pexpr b _ (PEval v))) =>
      if a.isEmpty && b.isEmpty then some (.pure v) else none
  | Expr a (Eannot ds (Expr a2 (Epure (Pexpr b _ (PEval v))))) =>
      if a.isEmpty && a2.isEmpty && b.isEmpty then some (.annot ds v) else none
  | _ => none

@[simp] theorem toVal_ofVal (v : SpikeVal) : toVal (ofVal v) = some v := by
  cases v <;> rfl

theorem ofVal_of_toVal {e : CoreExpr} {v : SpikeVal}
    (h : toVal e = some v) : ofVal v = e := by
  unfold toVal at h
  split at h
  · rename_i a b u w
    split at h
    · rename_i hcond
      obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hcond
      have ha' : a = [] := List.isEmpty_iff.mp ha
      have hb' : b = [] := List.isEmpty_iff.mp hb
      subst ha' hb'
      cases h
      rfl
    · cases h
  · rename_i a ds a2 b u w
    split at h
    · rename_i hcond
      obtain ⟨⟨ha', ha2'⟩, hb'⟩ : (a = [] ∧ a2 = []) ∧ b = [] := by
        simpa [Bool.and_eq_true_iff] using hcond
      subst ha' ha2' hb'
      cases h
      rfl
    · cases h
  · cases h

/-- Root-level Eannot test — the guard get_ctx uses to choose between
    the ANNOTS-merge redex and Cannot-descent
    (Core_reduction.lean:375, the two Eannot arms of get_ctx). -/
def annotRooted : CoreExpr → Bool
  | Expr _ (Eannot _ _) => true
  | _ => false

/-! ## The label context (S3 — header note 3) -/

/-- The static label map of the CURRENT procedure: the engine's
    per-procedure registered continuations (`labeled_continuations
    core_run_annotation`, Core_run_aux.lean:187 — label ↦
    (parameters, sseq-extended body)). Populated once by
    `collect_labeled_continuations_NEW` (Core_aux.lean:843/853),
    never written on the sequential path. (S2 kept this abbrev in
    Wps.lean; S3 moves it here because Step now consults it.) -/
abbrev LabelMap : Type := labeled_continuations core_run_annotation

/-- Label lookup, in the engine's own spelling (step_ctx's Erun arm,
    Core_reduction.lean:484 — the inner `fmapLookupBy` of the
    two-level `labeled` read; the outer, per-procedure level is the
    certification-side tie, Soundness.lean). -/
def lookupLabel (Q : LabelMap) (l : sym) :
    Option (List (sym × core_base_type) × CoreExpr) :=
  fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
    Lem_Basic_classes.ordCompare s1 s2) l Q

/-! ## The machine context and the live control (S1b — the unified
configuration, design record docs/2026-08-31_phase1-design-record.md
§1; calls arc C1 — docs/2026-09-02_calls-design-spike.md §3 Q1)

`MachineCtx` names every component of an engine configuration the
fragment leaves IMMUTABLE: the parameters of `step_ctx` (tagDefs,
file, extern, tid, parent), the thread's `errno` and `current_loc`,
and the run state the discharge protocol threads (read-only under the
fragment — Erun reads `labeled` through it; per-step aid draws remain
per-step parameters, as in the driver). The thread's CONTROL fields —
`stack0`, `current_proc_opt`, `exec_loc` — are WRITTEN by a procedure
call (step_ctx's `Eproc` PCALL arm, Core_reduction.lean:484) and by
the RETURN arm, so they are LIVE STATE: the `Ctl` component of the
configuration `Config := CoreExpr × EnvStack × Ctl × Mem`. The old
frozen profiles (`spikeCtx`/`procCtx` below) are INSTANCES of
`MachineCtx` — one point of the context space — not parts of the
judgment; the entry controls `spikeCtl`/`procCtl p` are the launch
points of the control space. -/

/-- The engine's extern indirection with identity fallback — the
    `let sym1 := match fmapLookupBy … core_extern1 with …`
    computation of the evaluator's PEsym arm (Core_eval.lean:142)
    and of step_ctx's Erun arm (Core_reduction.lean:484). -/
def resolveExtern (ext : Fmap sym sym) (x : sym) : sym :=
  match fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
      Lem_Basic_classes.ordCompare s1 s2) x ext with
  | some y => y
  | none => x

theorem resolveExtern_empty (x : sym) : resolveExtern fmapEmpty x = x := rfl

/-- A symbol the extern map does not redirect resolves to itself. A
    client states `∀ x, resolveExtern M.extern x = x` — "the program's
    symbols are not extern-redirected" — instead of naming the map's
    value; at `fmapEmpty` this discharges it. -/
theorem resolveExtern_id_of_empty {ext : Fmap sym sym} (h : ext = fmapEmpty)
    (x : sym) : resolveExtern ext x = x := by
  rw [h]; rfl

/-- THE LIVE CONTROL of a thread (calls arc C1): exactly the three
    `thread_state` fields (Core_run_aux.lean:291) the engine writes at
    a procedure call and at a return — step_ctx's PCALL arm
    (Core_reduction.lean:484, col ≈18133): `current_proc_opt := some
    psym`, `exec_loc := push_exec_loc psym th_st.current_loc
    th_st.exec_loc`, `stack0 := Stack_cons2 th_st.current_proc_opt ctx
    th_st.stack0`; the RETURN arm at `Stack_cons2 parent_proc_opt
    caller_ctx sk'` (col ≈2276): `current_proc_opt := parent_proc_opt`,
    `stack0 := sk'`, `exec_loc` untouched.
    - `κ`: the `Stack_cons2` chain as a list of (caller's procedure,
      caller's saved context), innermost first — `Ctl.toStack` is the
      engine's `stack` it denotes; `[]` is `Stack_empty` (the
      PROGRAM-DONE selector of the value arm);
    - `proc`: `current_proc_opt` (what `Erun` reads the label map at);
    - `execLoc`: `exec_loc` (pushed on call, never popped).
    The engine's THIRD stack constructor, `Stack_cons` (Core_run_aux.lean:
    191-203, the continuation stack of the OTHER interpreter, Core_run.lean:
    395 its only writer), is not representable by `Ctl.toStack` and is
    unreachable from `Driver.drive`; step_ctx's value arm PANICS on it
    (`failwithI "Core_reduction ==> Stack_cons"`, col ≈2698) — a
    fail-closed restriction, stated (the C1 range audit's N-1). The two
    writers of the control are `Step.call` and `Step.ret` (calls arc C2);
    every other rule threads it (`Step.ctl_cases`). -/
structure Ctl where
  κ : List (Option sym × context)
  proc : Option sym
  execLoc : exec_location

namespace Ctl

/-- The engine's `stack` denoted by the control's `κ`
    (`Stack_cons2 p ctx` per entry, innermost first, over `Stack_empty`). -/
def toStack (c : Ctl) : _root_.stack core_run_annotation :=
  c.κ.foldr (fun pc sk => Stack_cons2 pc.1 pc.2 sk) Stack_empty

@[simp] theorem toStack_nil (p : Option sym) (ℓ : exec_location) :
    (Ctl.mk [] p ℓ).toStack = Stack_empty := rfl

/-- `κ = []` is exactly `stack0 = Stack_empty`. -/
theorem toStack_eq_empty_iff (c : Ctl) : c.toStack = Stack_empty ↔ c.κ = [] := by
  obtain ⟨κ, p, ℓ⟩ := c
  cases κ with
  | nil => simp [toStack]
  | cons pc κ => simp [toStack]

theorem toStack_of_κ_nil {c : Ctl} (h : c.κ = []) : c.toStack = Stack_empty :=
  (toStack_eq_empty_iff c).2 h

end Ctl

/-- A Core configuration: expression, live environment stack, live
    control, memory. -/
abbrev Config : Type := CoreExpr × EnvStack × Ctl × Mem

/-- Every immutable component of an engine configuration (per-field
    engine slots and fragment reads: the design record §1 table; the
    control fields moved to `Ctl`, calls arc C1). -/
structure MachineCtx where
  tagDefs : Fmap sym (CerbLocation.Loc × tag_definition)
  file : generic_file Unit core_run_annotation
  extern : Fmap sym sym
  tid : Nat
  parent : Option Nat
  errno : CerbMem.PointerValue
  currentLoc : CerbLocation.Loc
  runState : core_run_state

namespace MachineCtx

/-- The thread state a context builds around the live (expression,
    env, control). Explicit literal so record updates of it reduce
    definitionally (the `envThread` precedent). The control fields
    are the CONFIGURATION's (`stack0 := ctl.toStack`,
    `current_proc_opt := ctl.proc`, `exec_loc := ctl.execLoc`) — the
    engine's PCALL/RETURN arms write exactly these three. -/
def thread (M : MachineCtx) (e : CoreExpr) (ρ : EnvStack) (ctl : Ctl) : thread_state :=
  { arena := e, stack0 := ctl.toStack, errno := M.errno, env := ρ,
    current_proc_opt := ctl.proc, exec_loc := ctl.execLoc,
    current_loc := M.currentLoc }

@[simp] theorem thread_arena (M : MachineCtx) (e : CoreExpr) (ρ : EnvStack) (ctl : Ctl) :
    (M.thread e ρ ctl).arena = e := rfl

@[simp] theorem thread_env (M : MachineCtx) (e : CoreExpr) (ρ : EnvStack) (ctl : Ctl) :
    (M.thread e ρ ctl).env = ρ := rfl

@[simp] theorem thread_stack0 (M : MachineCtx) (e : CoreExpr) (ρ : EnvStack) (ctl : Ctl) :
    (M.thread e ρ ctl).stack0 = ctl.toStack := rfl

@[simp] theorem thread_proc (M : MachineCtx) (e : CoreExpr) (ρ : EnvStack) (ctl : Ctl) :
    (M.thread e ρ ctl).current_proc_opt = ctl.proc := rfl

@[simp] theorem thread_execLoc (M : MachineCtx) (e : CoreExpr) (ρ : EnvStack) (ctl : Ctl) :
    (M.thread e ρ ctl).exec_loc = ctl.execLoc := rfl

/-- The sequential well-formedness of the CONTEXT the VALUE protocol
    reads (THREAD-DONE vs PROGRAM-DONE selection in step_ctx's value
    arm): the startup thread. The other half of the old `SeqWF` — the
    EMPTY CALL STACK — is a fact about the live control (`ctl.κ = []`),
    an ENTRY fact of every launch (calls arc C1). -/
structure SeqWF (M : MachineCtx) : Prop where
  parent : M.parent = none

/-- The extern indirection at the context's own extern map —
    verbatim the `proc_sym` computation of step_ctx's Erun arm
    (Core_reduction.lean:484). -/
def resolveProc (M : MachineCtx) (p : sym) : sym :=
  resolveExtern M.extern p

theorem resolveProc_of_extern_empty {M : MachineCtx}
    (hext : M.extern = fmapEmpty) (p : sym) : M.resolveProc p = p := by
  unfold resolveProc
  rw [hext]
  rfl

/-- The registered label fiber of a procedure, read from the context
    exactly as step_ctx's Erun arm reads it (two-level `labeled`
    lookup at the extern-resolved current proc — the LIVE
    `current_proc_opt`, i.e. `ctl.proc` at the configuration). Lookup
    failure and the no-current-proc case collapse to the EMPTY map:
    the jump rule cannot fire there — the engine's failwithI panic
    channels are mirrored fail-closed as absence of a step. The label
    map is DERIVED, not carried (the old `Q : LabelMap` index and its
    `LabeledAt` tie hypothesis are subsumed). -/
def labelsAt (M : MachineCtx) (p : Option sym) : LabelMap :=
  match p with
  | none => fmapEmpty
  | some p =>
    match fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
        Lem_Basic_classes.ordCompare s1 s2)
        (M.resolveProc p) M.runState.labeled with
    | some Q => Q
    | none => fmapEmpty

@[simp] theorem labelsAt_none (M : MachineCtx) : M.labelsAt none = fmapEmpty := rfl

/-- The label fiber at a procedure symbol (the outer match reduced;
    `rfl`, named for rewriting). -/
theorem labelsAt_some (M : MachineCtx) (p : sym) :
    M.labelsAt (some p) =
      (match fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
          Lem_Basic_classes.ordCompare s1 s2)
          (M.resolveProc p) M.runState.labeled with
        | some Q => Q
        | none => fmapEmpty) := rfl

/-- The label fiber at a known current procedure (the outer match
    reduced). -/
theorem labelsAt_eq_of_proc {M : MachineCtx} {c : Ctl} {p : sym} (hp : c.proc = some p) :
    M.labelsAt c.proc =
      (match fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
          Lem_Basic_classes.ordCompare s1 s2)
          (M.resolveProc p) M.runState.labeled with
        | some Q => Q
        | none => fmapEmpty) := by
  rw [hp]
  rfl

end MachineCtx

/-! ## The runtime tuple (S1: env is live state; S1b: + the machine
context — the unified configuration; C1: + the live control) -/

/-- The runtime expression tuple: Core expression + live environment
    stack + live control (thread_state's `arena`, `env` and its three
    control fields) + the machine context (every immutable the
    fragment reads, carried read-only in the tuple; steps preserve it
    by construction of `primStep` — the engine writes no context
    component on the sequential path). -/
structure CoreRt where
  e : CoreExpr
  ρ : EnvStack
  ctl : Ctl
  M : MachineCtx

/-- Values carry the final env, the TERMINAL control's procedure and
    execution location, and the (unchanged) machine context (exported
    posts may project all of them away). A terminal has an EMPTY call
    stack by definition: a value at a non-empty stack is a RETURN
    redex, not a terminal (step_ctx's value arm at `Stack_cons2`,
    Core_reduction.lean:484), so `κ` has no slot here — `toValRt`
    answers `none` at `κ ≠ []`. -/
structure CoreRVal where
  w : SpikeVal
  ρ : EnvStack
  proc : Option sym
  execLoc : exec_location
  M : MachineCtx

/-- The terminal control a value sits at (empty stack). -/
def CoreRVal.ctl (v : CoreRVal) : Ctl := ⟨[], v.proc, v.execLoc⟩

/-- The delivered engine value of a runtime value (annotations and
    env erased — the D1 readout). -/
def CoreRVal.val (v : CoreRVal) : value := v.w.val

/-- Annotation-merge on runtime values: componentwise `SpikeVal.merge`
    (the env, control and label map ride — annotation reduction never
    touches them). -/
def CoreRVal.merge (ds : List dyn_annotation) (v : CoreRVal) : CoreRVal :=
  ⟨SpikeVal.merge ds v.w, v.ρ, v.proc, v.execLoc, v.M⟩

@[simp] theorem CoreRVal.merge_mk (ds : List dyn_annotation) (w : SpikeVal)
    (ρ : EnvStack) (p : Option sym) (ℓ : exec_location) (M : MachineCtx) :
    CoreRVal.merge ds ⟨w, ρ, p, ℓ, M⟩ = ⟨SpikeVal.merge ds w, ρ, p, ℓ, M⟩ := rfl

@[simp] theorem CoreRVal.val_merge (ds : List dyn_annotation) (v : CoreRVal) :
    (CoreRVal.merge ds v).val = v.val := by
  cases v; simp [CoreRVal.merge, CoreRVal.val]

@[simp] theorem CoreRVal.ρ_merge (ds : List dyn_annotation) (v : CoreRVal) :
    (CoreRVal.merge ds v).ρ = v.ρ := by
  cases v; rfl

/-- Componentwise value test (Language-side `toVal`): a value at an
    EMPTY call stack is terminal; at a non-empty stack nothing is
    (the RETURN redex — C2's `Step.ret`). -/
def toValRt (r : CoreRt) : Option CoreRVal :=
  match r.ctl.κ with
  | [] => (toVal r.e).map fun w => ⟨w, r.ρ, r.ctl.proc, r.ctl.execLoc, r.M⟩
  | _ :: _ => none

/-- Componentwise value injection (Language-side `ofVal`): at the
    terminal (empty-stack) control. -/
def ofValRt (v : CoreRVal) : CoreRt := ⟨ofVal v.w, v.ρ, ⟨[], v.proc, v.execLoc⟩, v.M⟩

@[simp] theorem toValRt_mk (e : CoreExpr) (ρ : EnvStack) (p : Option sym)
    (ℓ : exec_location) (M : MachineCtx) :
    toValRt ⟨e, ρ, ⟨[], p, ℓ⟩, M⟩ = (toVal e).map fun w => ⟨w, ρ, p, ℓ, M⟩ := rfl

@[simp] theorem toValRt_mk_cons (e : CoreExpr) (ρ : EnvStack) (pc : Option sym × context)
    (κ : List (Option sym × context)) (p : Option sym) (ℓ : exec_location)
    (M : MachineCtx) :
    toValRt ⟨e, ρ, ⟨pc :: κ, p, ℓ⟩, M⟩ = none := rfl

/-- A non-value expression is a non-value tuple at every control. -/
theorem toValRt_eq_none_of_toVal_none {r : CoreRt} (h : toVal r.e = none) :
    toValRt r = none := by
  obtain ⟨e, ρ, ⟨κ, p, ℓ⟩, M⟩ := r
  cases κ with
  | nil => rw [toValRt_mk]; simp only at h; rw [h]; rfl
  | cons pc κ => rfl

/-- At the terminal control the tuple's value test is the expression's. -/
theorem toValRt_of_κ_nil {r : CoreRt} (h : r.ctl.κ = []) :
    toValRt r = (toVal r.e).map fun w => ⟨w, r.ρ, r.ctl.proc, r.ctl.execLoc, r.M⟩ := by
  obtain ⟨e, ρ, ⟨κ, p, ℓ⟩, M⟩ := r
  simp only at h
  subst h
  rfl

@[simp] theorem ofValRt_mk (w : SpikeVal) (ρ : EnvStack) (p : Option sym)
    (ℓ : exec_location) (M : MachineCtx) :
    ofValRt ⟨w, ρ, p, ℓ, M⟩ = ⟨ofVal w, ρ, ⟨[], p, ℓ⟩, M⟩ := rfl

@[simp] theorem toValRt_ofValRt (v : CoreRVal) : toValRt (ofValRt v) = some v := by
  obtain ⟨w, ρ, p, ℓ, M⟩ := v
  rw [ofValRt_mk, toValRt_mk, toVal_ofVal]
  rfl

/-- Evaluated-operand recognition on canonical shapes: the ACTION_EVAL
    rule premises (`valueFromPexpr`, Core_aux.lean:472) discharge by
    `rfl` on `mk_value_pe`-shaped operands (any node annotations —
    the engine's redex patterns accept them, slice notes §D3). -/
@[simp] theorem valueFromPexpr_val (a : List annot) (v : value) :
    valueFromPexpr (Pexpr a () (PEval v)) = some v := rfl

/-! ## The jump-redex search (S3 — header note 4)

`jumpRedex?` follows get_ctx's decomposition path (Esseq-left,
guarded Eannot descent — Core_reduction.lean:375) and answers
whether the hole holds an `Erun`. It is the SYNTACTIC image of the
engine's context-discard: `jumpRedex? (Esseq pat e1 e2) = jumpRedex?
e1` makes the jump clause of the statement WP invariant under
sequencing frames (probe report §3 case 2). The Eannot guard mirrors
get_ctx's arm order: a double-annot root is the ANNOTS-merge redex,
never a descent. -/

def jumpRedex? : CoreExpr → Option (sym × List (generic_pexpr Unit sym))
  | Expr _ (Erun _ l pes) => some (l, pes)
  | Expr _ (Esseq _ e1 _) => jumpRedex? e1
  | Expr _ (Ewseq _ e1 _) => jumpRedex? e1
  | Expr _ (Eannot _ b) => if annotRooted b then none else jumpRedex? b
  | _ => none

@[simp] theorem jumpRedex?_run (a : List annot) (ra : core_run_annotation)
    (l : sym) (pes : List (generic_pexpr Unit sym)) :
    jumpRedex? (Expr a (Erun ra l pes)) = some (l, pes) := rfl

@[simp] theorem jumpRedex?_sseq (a : List annot) (pat : pattern)
    (e1 e2 : CoreExpr) :
    jumpRedex? (Expr a (Esseq pat e1 e2)) = jumpRedex? e1 := rfl

/-- S1b DRIFT TEST (Ewseq wildcard, design record §8 item 8): the
    Ewseq arm above extends the jump-redex search left through weak
    sequencing, exactly as for Esseq — get_ctx descends Ewseq-left
    into a Cwseq frame (Core_reduction.lean:375) and the engine's
    Erun arm discards the WHOLE context, Cwseq frames included.
    CONSERVATIVE on the pre-existing corpus: every pre-existing
    head's equation (`jumpRedex?_run`/`_sseq`/`_annot`/`_pure`)
    still holds by `rfl`; only Ewseq-containing terms (none before
    this slice) gain a non-`none` answer. -/
@[simp] theorem jumpRedex?_wseq (a : List annot) (pat : pattern)
    (e1 e2 : CoreExpr) :
    jumpRedex? (Expr a (Ewseq pat e1 e2)) = jumpRedex? e1 := rfl

theorem jumpRedex?_annot (a : List annot) (ds : List dyn_annotation)
    (b : CoreExpr) :
    jumpRedex? (Expr a (Eannot ds b)) =
      if annotRooted b then none else jumpRedex? b := rfl

@[simp] theorem jumpRedex?_annot_of_root {b : CoreExpr}
    (a : List annot) (ds : List dyn_annotation) (h : annotRooted b = true) :
    jumpRedex? (Expr a (Eannot ds b)) = none := by
  rw [jumpRedex?_annot, h]; rfl

@[simp] theorem jumpRedex?_annot_of_not_root {b : CoreExpr}
    (a : List annot) (ds : List dyn_annotation) (h : annotRooted b = false) :
    jumpRedex? (Expr a (Eannot ds b)) = jumpRedex? b := by
  rw [jumpRedex?_annot, h]; rfl

@[simp] theorem jumpRedex?_pure (a : List annot) (pe : generic_pexpr Unit sym) :
    jumpRedex? (Expr a (Epure pe)) = none := rfl

@[simp] theorem jumpRedex?_action (a : List annot)
    (p : generic_paction core_run_annotation Unit sym) :
    jumpRedex? (Expr a (Eaction p)) = none := rfl

@[simp] theorem jumpRedex?_memop (a : List annot) (mop : memop)
    (pes : List (generic_pexpr Unit sym)) :
    jumpRedex? (Expr a (Ememop mop pes)) = none := rfl

@[simp] theorem jumpRedex?_ofVal (w : SpikeVal) :
    jumpRedex? (ofVal w) = none := by
  cases w <;> rfl

/-! ## The call-redex search WITH its captured context (calls arc C2)

`callRedex?` is the `Eproc` twin of `jumpRedex?`, following the same
spine (get_ctx's decomposition path, Core_reduction.lean:375: Esseq-left
and Ewseq-left into a `Csseq`/`Cwseq` frame, the guarded `Eannot`
descent into a `Cannot` frame — a double-annot root is the ANNOTS-merge
redex, never a descent), and it BUILDS the engine's own `context` on
the way down, outside-in exactly as get_ctx does (`Csseq annot1 pat ctx
e2` at a node `Expr annot1 (Esseq pat e1 e2)`). The engine's PCALL arm
(Core_reduction.lean:484, col 18133) CAPTURES that context onto the
call stack — `stack0 := Stack_cons2 th_st.current_proc_opt ctx
th_st.stack0` — and the RETURN arm plugs the callee's value back into
it (`apply_ctx caller_ctx …`, col 2276). So a call is a third context
discipline beside the PRESERVING redexes (`apply_ctx ctx r'`) and the
DISCARDING jump: CAPTURING. `Step.call` is therefore stated at the
WHOLE expression, like `Step.run`, with the context it pushes computed
by this function; `Decomp.callRedex?_some` (Soundness.lean) certifies
it against the engine's decomposition. The implementation-constant call
`Eproc _ (Impl _) _` is outside the fragment (`none`). -/
def callRedex? : CoreExpr → Option (context × sym × List (generic_pexpr Unit sym))
  | Expr _ (Eproc _ (Sym f) pes) => some (CTX, f, pes)
  | Expr a (Esseq pat e1 e2) =>
      (callRedex? e1).map fun q => (Csseq a pat q.1 e2, q.2)
  | Expr a (Ewseq pat e1 e2) =>
      (callRedex? e1).map fun q => (Cwseq a pat q.1 e2, q.2)
  | Expr a (Eannot ds b) =>
      if annotRooted b then none else (callRedex? b).map fun q => (Cannot a ds q.1, q.2)
  | _ => none

@[simp] theorem callRedex?_proc (a : List annot) (ra : core_run_annotation)
    (f : sym) (pes : List (generic_pexpr Unit sym)) :
    callRedex? (Expr a (Eproc ra (Sym f) pes)) = some (CTX, f, pes) := rfl

@[simp] theorem callRedex?_proc_impl (a : List annot) (ra : core_run_annotation)
    (ic : implementation_constant) (pes : List (generic_pexpr Unit sym)) :
    callRedex? (Expr a (Eproc ra (Impl ic) pes)) = none := rfl

@[simp] theorem callRedex?_sseq (a : List annot) (pat : pattern) (e1 e2 : CoreExpr) :
    callRedex? (Expr a (Esseq pat e1 e2)) =
      (callRedex? e1).map fun q => (Csseq a pat q.1 e2, q.2) := rfl

@[simp] theorem callRedex?_wseq (a : List annot) (pat : pattern) (e1 e2 : CoreExpr) :
    callRedex? (Expr a (Ewseq pat e1 e2)) =
      (callRedex? e1).map fun q => (Cwseq a pat q.1 e2, q.2) := rfl

theorem callRedex?_annot (a : List annot) (ds : List dyn_annotation) (b : CoreExpr) :
    callRedex? (Expr a (Eannot ds b)) =
      if annotRooted b then none
      else (callRedex? b).map fun q => (Cannot a ds q.1, q.2) := rfl

@[simp] theorem callRedex?_annot_of_root {b : CoreExpr}
    (a : List annot) (ds : List dyn_annotation) (h : annotRooted b = true) :
    callRedex? (Expr a (Eannot ds b)) = none := by
  rw [callRedex?_annot, h]; rfl

@[simp] theorem callRedex?_annot_of_not_root {b : CoreExpr}
    (a : List annot) (ds : List dyn_annotation) (h : annotRooted b = false) :
    callRedex? (Expr a (Eannot ds b)) =
      (callRedex? b).map fun q => (Cannot a ds q.1, q.2) := by
  rw [callRedex?_annot, h]; rfl

@[simp] theorem callRedex?_pure (a : List annot) (pe : generic_pexpr Unit sym) :
    callRedex? (Expr a (Epure pe)) = none := rfl

@[simp] theorem callRedex?_action (a : List annot)
    (p : generic_paction core_run_annotation Unit sym) :
    callRedex? (Expr a (Eaction p)) = none := rfl

@[simp] theorem callRedex?_memop (a : List annot) (mop : memop)
    (pes : List (generic_pexpr Unit sym)) :
    callRedex? (Expr a (Ememop mop pes)) = none := rfl

@[simp] theorem callRedex?_run (a : List annot) (ra : core_run_annotation)
    (l : sym) (pes : List (generic_pexpr Unit sym)) :
    callRedex? (Expr a (Erun ra l pes)) = none := rfl

@[simp] theorem callRedex?_save (a : List annot) (sb : sym × core_base_type)
    (ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)))
    (body : CoreExpr) :
    callRedex? (Expr a (Esave sb ps body)) = none := rfl

@[simp] theorem callRedex?_if (a : List annot) (g : generic_pexpr Unit sym)
    (e2 e3 : CoreExpr) :
    callRedex? (Expr a (Eif g e2 e3)) = none := rfl

@[simp] theorem callRedex?_case (a : List annot) (pe : generic_pexpr Unit sym)
    (pats : List (pattern × CoreExpr)) :
    callRedex? (Expr a (Ecase pe pats)) = none := rfl

@[simp] theorem callRedex?_ofVal (w : SpikeVal) :
    callRedex? (ofVal w) = none := by
  cases w <;> rfl

/-- A frame with no call redex has none in its body (the `Option.map`
    shape of `callRedex?` at the three descents). -/
theorem callRedex?_e1_none_of_sseq {a : List annot} {pat : pattern} {e1 e2 : CoreExpr}
    (h : callRedex? (Expr a (Esseq pat e1 e2)) = none) : callRedex? e1 = none := by
  rw [callRedex?_sseq] at h
  exact Option.map_eq_none_iff.mp h

theorem callRedex?_e1_none_of_wseq {a : List annot} {pat : pattern} {e1 e2 : CoreExpr}
    (h : callRedex? (Expr a (Ewseq pat e1 e2)) = none) : callRedex? e1 = none := by
  rw [callRedex?_wseq] at h
  exact Option.map_eq_none_iff.mp h

theorem callRedex?_body_none_of_annot {a : List annot} {ds : List dyn_annotation}
    {b : CoreExpr} (hg : annotRooted b = false)
    (h : callRedex? (Expr a (Eannot ds b)) = none) : callRedex? b = none := by
  rw [callRedex?_annot_of_not_root _ _ hg] at h
  exact Option.map_eq_none_iff.mp h

/-- The converse direction, for the frame nodes' guards. -/
theorem callRedex?_sseq_none {a : List annot} {pat : pattern} {e1 e2 : CoreExpr}
    (h : callRedex? e1 = none) : callRedex? (Expr a (Esseq pat e1 e2)) = none := by
  rw [callRedex?_sseq, h]; rfl

theorem callRedex?_wseq_none {a : List annot} {pat : pattern} {e1 e2 : CoreExpr}
    (h : callRedex? e1 = none) : callRedex? (Expr a (Ewseq pat e1 e2)) = none := by
  rw [callRedex?_wseq, h]; rfl

theorem callRedex?_annot_none {a : List annot} {ds : List dyn_annotation} {b : CoreExpr}
    (h : callRedex? b = none) : callRedex? (Expr a (Eannot ds b)) = none := by
  rw [callRedex?_annot]
  split
  · rfl
  · rw [h]; rfl

/-- The two spine searches are exclusive: the hole is unique. -/
theorem callRedex?_none_of_jumpRedex?_some :
    ∀ {e : CoreExpr} {lp : sym × List (generic_pexpr Unit sym)},
      jumpRedex? e = some lp → callRedex? e = none
  | Expr a (Esseq pat e1 e2), lp, h => by
      rw [jumpRedex?_sseq] at h
      rw [callRedex?_sseq, callRedex?_none_of_jumpRedex?_some h]; rfl
  | Expr a (Ewseq pat e1 e2), lp, h => by
      rw [jumpRedex?_wseq] at h
      rw [callRedex?_wseq, callRedex?_none_of_jumpRedex?_some h]; rfl
  | Expr a (Eannot ds b), lp, h => by
      rw [jumpRedex?_annot] at h
      rw [callRedex?_annot]
      split at h
      · cases h
      · rename_i hr
        rw [if_neg hr, callRedex?_none_of_jumpRedex?_some h]; rfl
  | Expr a (Erun ra l pes), lp, h => rfl
  | Expr a (Epure _), lp, h => by simp [jumpRedex?] at h
  | Expr a (Ememop _ _), lp, h => by simp [jumpRedex?] at h
  | Expr a (Eaction _), lp, h => by simp [jumpRedex?] at h
  | Expr a (Ecase _ _), lp, h => by simp [jumpRedex?] at h
  | Expr a (Elet _ _ _), lp, h => by simp [jumpRedex?] at h
  | Expr a (Eif _ _ _), lp, h => by simp [jumpRedex?] at h
  | Expr a (Eccall _ _ _ _), lp, h => by simp [jumpRedex?] at h
  | Expr a (Eproc _ _ _), lp, h => by simp [jumpRedex?] at h
  | Expr a (Eunseq _), lp, h => by simp [jumpRedex?] at h
  | Expr a (Ebound _), lp, h => by simp [jumpRedex?] at h
  | Expr a (End _), lp, h => by simp [jumpRedex?] at h
  | Expr a (Esave _ _ _), lp, h => by simp [jumpRedex?] at h
  | Expr a (Epar _), lp, h => by simp [jumpRedex?] at h
  | Expr a (Ewait _), lp, h => by simp [jumpRedex?] at h
  | Expr a (Eexcluded _ _), lp, h => by simp [jumpRedex?] at h

theorem jumpRedex?_none_of_callRedex?_some {e : CoreExpr}
    {q : context × sym × List (generic_pexpr Unit sym)}
    (h : callRedex? e = some q) : jumpRedex? e = none := by
  cases hj : jumpRedex? e with
  | none => rfl
  | some lp => rw [callRedex?_none_of_jumpRedex?_some hj] at h; cases h

/-! ## The pure pexpr evaluator (S3 — header note 5)

A hand-written PARTIAL mirror of the engine's pexpr evaluation on
the fragment's operand grammar: `PEval`, `PEsym` (env lookup at the
frozen `extern = fmapEmpty` — identity indirection), and `PEop` on
integer/boolean operands (step_eval_peop, Core_eval.lean:135; the
`none` results of `ltIval`/`leIval`/`eqIval` are the symbolic
PEconstrained channel, absent from the concrete model's concrete
values — the premise form excludes it fail-closed). Everything else
is `none`: no step where the engine would take an eval path the
mirror does not model. Certified against
`full_eval_pexpr`/`step_eval_pexpr` in Soundness.lean. -/

/-- The engine's boolean-value injection (step_eval_peop's
    `if b then Vtrue else Vfalse`). -/
def boolValue (b : Bool) : value := if b then Vtrue else Vfalse

/-- Binop evaluation on evaluated operands — mirror of
    `step_eval_peop`'s value dispatch (Core_eval.lean:135),
    restricted to integer arithmetic/comparison and boolean
    connectives. Comparison mirrors the engine's operand order
    exactly (`OpGt` is `ltIval ival2 ival1`, `OpGe` is
    `leIval ival2 ival1`). -/
def evalBinop : binop → value → value → Option value
  | .OpAdd, Vobject (OVinteger i1), Vobject (OVinteger i2) =>
      some (Vobject (OVinteger (CerbMem.opIval IntAdd i1 i2)))
  | .OpSub, Vobject (OVinteger i1), Vobject (OVinteger i2) =>
      some (Vobject (OVinteger (CerbMem.opIval IntSub i1 i2)))
  | .OpMul, Vobject (OVinteger i1), Vobject (OVinteger i2) =>
      some (Vobject (OVinteger (CerbMem.opIval IntMul i1 i2)))
  | .OpEq, Vobject (OVinteger i1), Vobject (OVinteger i2) =>
      (CerbMem.eqIval i1 i2).map boolValue
  | .OpLt, Vobject (OVinteger i1), Vobject (OVinteger i2) =>
      (CerbMem.ltIval i1 i2).map boolValue
  | .OpLe, Vobject (OVinteger i1), Vobject (OVinteger i2) =>
      (CerbMem.leIval i1 i2).map boolValue
  | .OpGt, Vobject (OVinteger i1), Vobject (OVinteger i2) =>
      (CerbMem.ltIval i2 i1).map boolValue
  | .OpGe, Vobject (OVinteger i1), Vobject (OVinteger i2) =>
      (CerbMem.leIval i2 i1).map boolValue
  | _, _, _ => none

/-- Array-shift on evaluated operands — mirror of step_eval_pexpr's
    `PEarray_shift` value dispatch (Core_eval.lean:145): a pointer
    and an integer produce `arrayShiftPtrval` (the ENGINE'S OWN
    function, so the mirror is exact by construction — including on
    degenerate pointers, where both compute the same value), applied
    at the TAG ENVIRONMENT `tds` exactly as the engine applies it at
    its reader `(CerbMem.arrayShiftPtrval _lemReader_tagDefs)`
    (Core_eval.lean:145; the C1 reader_consumer threading, cerberus-lean
    docs/2026-08-31_C1-change-manifest.md §4); any
    other operand shapes are fail-closed `none` (the engine's arm
    there is the Illformed_program channel — no mirror step). S4:
    the pointer-arithmetic extension the array exhibit needs. -/
def evalArrayShift (tds : CerbTags.TagDefsMap) (ty : ctype) :
    value → value → Option value
  | Vobject (OVpointer pv), Vobject (OVinteger iv) =>
      some (Vobject (OVpointer (CerbMem.arrayShiftPtrval tds pv ty iv)))
  | _, _ => none

/-- The pure evaluator (fragment operands; partial, fail-closed).
    S1b′: EXTERN IS THREADED — the engine resolves EVERY `PEsym`
    through the extern indirection with identity fallback
    (Core_eval.lean:142, the `let sym1 := match fmapLookupBy … ` of
    the PEsym arm); the S1a probe found the old extern-free evaluator
    pinned the whole bridge tower at `extern = fmapEmpty` (design
    record §5.2). The lookup-failure proc-pointer fallback channel
    (`file1.funs`) is fail-closed absence, as before. -/
def evalPexpr (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack) :
    generic_pexpr Unit sym → Option value
  | Pexpr _ _ (PEval v) => some v
  | Pexpr _ _ (PEsym x) => lookup_env (resolveExtern ext x) ρ
  | Pexpr _ _ (PEop op pe1 pe2) => do
      let v1 ← evalPexpr tds ext ρ pe1
      let v2 ← evalPexpr tds ext ρ pe2
      evalBinop op v1 v2
  | Pexpr _ _ (PEarray_shift pe1 ty pe2) => do
      let v1 ← evalPexpr tds ext ρ pe1
      let v2 ← evalPexpr tds ext ρ pe2
      evalArrayShift tds ty v1 v2
  | _ => none

@[simp] theorem evalPexpr_val (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack)
    (a : List annot) (v : value) :
    evalPexpr tds ext ρ (Pexpr a () (PEval v)) = some v := rfl

@[simp] theorem evalPexpr_sym (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack)
    (a : List annot) (x : sym) :
    evalPexpr tds ext ρ (Pexpr a () (PEsym x)) =
      lookup_env (resolveExtern ext x) ρ := rfl

/-- ... at the empty extern the indirection is the identity (the
    frozen profiles' instance; rfl). -/
@[simp] theorem evalPexpr_sym_empty (tds : CerbTags.TagDefsMap) (ρ : EnvStack)
    (a : List annot) (x : sym) :
    evalPexpr tds fmapEmpty ρ (Pexpr a () (PEsym x)) = lookup_env x ρ := rfl

/-- ... and at ANY extern map that does not redirect `x` (QA-1/Q13: the
    SymFrame-level lookup discharges `resolveExtern` without naming the
    map). -/
theorem evalPexpr_sym_of_resolve (tds : CerbTags.TagDefsMap) {ext : Fmap sym sym}
    (ρ : EnvStack) (a : List annot) {x : sym} (hx : resolveExtern ext x = x) :
    evalPexpr tds ext ρ (Pexpr a () (PEsym x)) = lookup_env x ρ := by
  rw [evalPexpr_sym, hx]

theorem evalPexpr_op (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack) (a : List annot)
    (op : binop) (pe1 pe2 : generic_pexpr Unit sym) :
    evalPexpr tds ext ρ (Pexpr a () (PEop op pe1 pe2)) = (do
      let v1 ← evalPexpr tds ext ρ pe1
      let v2 ← evalPexpr tds ext ρ pe2
      evalBinop op v1 v2) := rfl

theorem evalPexpr_array_shift (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack)
    (a : List annot) (ty : ctype)
    (pe1 pe2 : generic_pexpr Unit sym) :
    evalPexpr tds ext ρ (Pexpr a () (PEarray_shift pe1 ty pe2)) = (do
      let v1 ← evalPexpr tds ext ρ pe1
      let v2 ← evalPexpr tds ext ρ pe2
      evalArrayShift tds ty v1 v2) := rfl

/-- All-or-nothing list evaluation (the engine's per-argument
    `full_eval_pexpr'` fold in step_ctx's Erun arm evaluates each
    argument against the ORIGINAL env — `full_eval_pexpr'` is closed
    over `th_st` — while threading the binding accumulator;
    `evalPexprs` mirrors the evaluation half). -/
def evalPexprs (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack) :
    List (generic_pexpr Unit sym) → Option (List value)
  | [] => some []
  | pe :: pes => do
      let v ← evalPexpr tds ext ρ pe
      let vs ← evalPexprs tds ext ρ pes
      pure (v :: vs)

@[simp] theorem evalPexprs_nil (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack) :
    evalPexprs tds ext ρ [] = some [] := rfl

theorem evalPexprs_cons (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack)
    (pe : generic_pexpr Unit sym)
    (pes : List (generic_pexpr Unit sym)) :
    evalPexprs tds ext ρ (pe :: pes) = (do
      let v ← evalPexpr tds ext ρ pe
      let vs ← evalPexprs tds ext ρ pes
      pure (v :: vs)) := rfl

/-! ## The procedure table and the callee's environment frame (calls arc C2)

`call_proc` (Core_run.lean:93, verbatim modulo whitespace):
```
let bTy_params_body_opt :=
  match fmapLookupBy ordCompare psym file1.stdlib with
  | some (Proc _ _ bTy params body) => some (bTy, params, body)
  | _ => (let core_sym := match fmapLookupBy ordCompare psym core_extern1 with
            | some sym1 => sym1 | none => psym;
          match fmapLookupBy ordCompare core_sym file1.funs with
          | some (Proc _ _ bTy params body) => some (bTy, params, body)
          | _ => none);
match bTy_params_body_opt with
| some (bTy, params, body) =>
  if not (List.length params == List.length cvals) then
    fail0 (Illformed_program ("calling procedure `" ++ show_symbol psym ++
      "' with the wrong number of args: |args|=" ++ stringFromNat (length cvals) ++
      "expecting: " ++ stringFromNat (length params)))
  else let env1 := foldl2 (fun acc (sym1, _) cval => fmapAddBy ordCompare sym1 cval acc)
                     fmapEmpty params cvals;
       except_return (env1, body)
| none => fail0 (Illformed_program ("calling an unknown procedure: " ++ show_symbol psym))
```
`lookupProc` is the lookup half (stdlib first — a user procedure cannot
hide a stdlib one, the engine's own NOTE — then the EXTERN-RESOLVED
`funs` read; anything but a `Proc` declaration is `none`); its two
failures, the unknown procedure and the arity mismatch, are the two
`Illformed_program` KILLS of the completeness rows (Round.lean,
`complete_call`). `procEnv` is the binding half: the parameters bound
into a FRESH frame by the engine's own `foldl2`, pushed on the env stack
(`env := proc_env :: th_st.env`) — the caller's frames ride below,
untouched (`update_env` writes the head frame only, Core_aux.lean:868),
and RETURN pops exactly one frame. -/
def lookupProc (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (f : sym) : Option (List (sym × core_base_type) × CoreExpr) :=
  match fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
      f file.stdlib with
  | some (Proc _ _ _ params body) => some (params, body)
  | _ =>
    match fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
        (resolveExtern ext f) file.funs with
    | some (Proc _ _ _ params body) => some (params, body)
    | _ => none

/-- The callee's fresh parameter frame: `call_proc`'s `foldl2` VERBATIM
    (Core_run.lean:93; `foldl2`, Utils.lean:93, panics on a length
    mismatch — excluded by the arity premise `params.length = vs.length`
    of `Step.call`, exactly where the engine's `if not (length params ==
    length cvals)` guard sits). -/
def procEnv (params : List (sym × core_base_type)) (vs : List value) : Fmap sym value :=
  foldl2 (fun (acc : Fmap sym value) (p : (sym × core_base_type)) (cval : value) =>
      match acc, p, cval with
      | acc, (sym1, _), cval =>
        fmapAddBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
          sym1 cval acc)
    fmapEmpty params vs

@[simp] theorem procEnv_nil : procEnv [] [] = fmapEmpty := rfl

theorem procEnv_cons (x : sym) (bty : core_base_type) (params : List (sym × core_base_type))
    (v : value) (vs : List value) :
    procEnv ((x, bty) :: params) (v :: vs) =
      foldl2 (fun (acc : Fmap sym value) (p : (sym × core_base_type)) (cval : value) =>
          match acc, p, cval with
          | acc, (sym1, _), cval =>
            fmapAddBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
              sym1 cval acc)
        (fmapAddBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
          x v fmapEmpty) params vs := rfl

/-- Canonical spelling of the procedure-call redex: `Eproc` at a Core
    identifier (`Sym f`), annotation-free node. -/
def callRedex (ra : core_run_annotation) (f : sym)
    (pes : List (generic_pexpr Unit sym)) : CoreExpr :=
  Expr [] (Eproc ra (Sym f) pes)

@[simp] theorem callRedex?_callRedex (ra : core_run_annotation) (f : sym)
    (pes : List (generic_pexpr Unit sym)) :
    callRedex? (callRedex ra f pes) = some (CTX, f, pes) := rfl

@[simp] theorem jumpRedex?_callRedex (ra : core_run_annotation) (f : sym)
    (pes : List (generic_pexpr Unit sym)) :
    jumpRedex? (callRedex ra f pes) = none := rfl

@[simp] theorem toVal_callRedex (ra : core_run_annotation) (f : sym)
    (pes : List (generic_pexpr Unit sym)) :
    toVal (callRedex ra f pes) = none := rfl

/-! ## The plain-symbol binder pattern (list-reverse arc, phase A)

`lets x = e1 in e2` at a bare symbol pattern — the engine's own
value-binding idiom for NON-loaded results (the memop protocol's
delivered booleans are bare `Vtrue`/`Vfalse`, so the Specified
unwrap does not apply): `update_env_aux`'s `CaseBase (some sym1, _)`
arm (Core_aux.lean:861) binds the value verbatim. -/
def symPat (pa : List annot) (x : sym) (bty : core_base_type) : pattern :=
  Pattern pa (CaseBase (some x, bty))

/-! ## The Specified-binder pattern (S4)

`lets Specified(x : bty) = e1 in e2` — the load-result unwrapping
idiom: `update_env_aux`'s `CaseCtor Cspecified [pat']` arm
(Core_aux.lean:861) matches a `Vloaded (LVspecified oval)` and binds
the payload as a plain OBJECT value (`Vobject oval`), so the bound
symbol is directly usable in integer arithmetic. This is the shape
S4's binding-sseq betas fire at (the S3 notes' registered item —
the fragment's loads deliver `Vloaded` values, and Core's binding
patterns are the engine's own unwrapping mechanism; no new
evaluation machinery). -/
def specPat (pa pb : List annot) (x : sym) (bty : core_base_type) : pattern :=
  Pattern pa (CaseCtor Cspecified [Pattern pb (CaseBase (some x, bty))])

/-! ## The env-binding folds (Erun / Esave successors) -/

/-- Erun's parameter rebinding: the engine's `stExceptUndef_foldM`
    over `zip sym_bTys pes` (step_ctx Erun arm), with the argument
    values pre-evaluated (`evalPexprs` against the original env) —
    `update_env (mk_sym_pat sym bTy) v` folded left over the zip.
    `List.zip` TRUNCATES on length mismatch, exactly as the engine's
    zip does. -/
def bindArgs (params : List (sym × core_base_type)) (vs : List value)
    (ρ : EnvStack) : EnvStack :=
  List.foldl (fun acc (p : (sym × core_base_type) × value) =>
    update_env (mk_sym_pat p.1.1 p.1.2) p.2 acc) ρ (List.zip params vs)

/-- Esave's entry binding: one_step0's Esave TAU fold
    (Core_reduction.lean:353 — `update_env (mk_sym_pat sym1 bTy)
    cval` folded left over `zip sym_bTy_pes cvals`). -/
def bindSaveParams
    (ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)))
    (cvals : List value) (ρ : EnvStack) : EnvStack :=
  List.foldl (fun acc
      (p : (sym × ((core_base_type ×
        Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))
        × value) =>
    update_env (mk_sym_pat p.1.1 p.1.2.1.1) p.2 acc) ρ (List.zip ps cvals)

/-- The parameter pexprs of an Esave binding list (the projection
    one_step0's Esave arm maps `valueFromPexprs` over). -/
def saveParamPexprs
    (ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))) :
    List (generic_pexpr Unit sym) :=
  ps.map fun p => p.2.2

/-- The engine's RE-FORMED Esave parameter list after the SAVE EVAL
    arm (one_step0's `sym_bTy_pes'`, Core_reduction.lean:353: the
    `stExceptUndef_mapM` over `sym_bTy_pes` keeps each `(sym1, (bTy,
    _))` and replaces the initializer by the evaluated `mk_value_pe
    cval` — the successor node is `Expr annots1 (Esave sym_bTy
    sym_bTy_pes' e)`). Stated over the evaluated value list `cvals`
    (`evalPexprs` of the initializers; same length as `ps`, so the
    zip truncates nothing). -/
def saveParamsWithValues
    (ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)))
    (cvals : List value) :
    List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)) :=
  (List.zip ps cvals).map fun p => (p.1.1, (p.1.2.1, Pexpr [] () (PEval p.2)))

@[simp] theorem saveParamsWithValues_nil (cvals : List value) :
    saveParamsWithValues [] cvals = [] := by
  cases cvals <;> rfl

@[simp] theorem saveParamsWithValues_cons
    (p : sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))
    (ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)))
    (v : value) (cvals : List value) :
    saveParamsWithValues (p :: ps) (v :: cvals) =
      (p.1, (p.2.1, Pexpr [] () (PEval v))) :: saveParamsWithValues ps cvals := rfl

/-- The engine's all-or-nothing operand test, one cons at a time
    (valueFromPexprs, Core_aux.lean:476 — a foldr of the per-operand
    `valueFromPexpr` test). -/
theorem valueFromPexprs_cons (pe : generic_pexpr Unit sym)
    (pes : List (generic_pexpr Unit sym)) :
    valueFromPexprs (pe :: pes) =
      (match valueFromPexpr pe, valueFromPexprs pes with
       | some v, some vs => some (v :: vs)
       | _, _ => none) := by
  unfold valueFromPexprs
  simp only [List.foldr_cons]
  rfl

@[simp] theorem valueFromPexprs_nil : valueFromPexprs [] = some [] := rfl

/-- The engine's all-or-nothing operand test on a two-element list,
    characterized (valueFromPexprs, Core_aux.lean:476 — a foldr of
    the per-operand `valueFromPexpr` test). -/
theorem valueFromPexprs_pair (pe1 pe2 : generic_pexpr Unit sym) :
    valueFromPexprs [pe1, pe2] =
      (match valueFromPexpr pe1, valueFromPexpr pe2 with
       | some v1, some v2 => some [v1, v2]
       | _, _ => none) := by
  unfold valueFromPexprs
  simp only [List.foldr_cons, List.foldr_nil]
  cases valueFromPexpr pe1 <;> cases valueFromPexpr pe2 <;> rfl

/-- Canonical value pexprs are recognized wholesale. -/
theorem valueFromPexprs_map_val (vs : List value) :
    valueFromPexprs (vs.map fun v => Pexpr [] () (PEval v)) = some vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => rw [List.map_cons, valueFromPexprs_cons, valueFromPexpr_val, ih]

/-- The re-formed list's initializers are exactly the canonical value
    pexprs of `cvals` (lengths agreeing). -/
theorem saveParamPexprs_withValues
    (ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)))
    (cvals : List value) (hlen : ps.length = cvals.length) :
    saveParamPexprs (saveParamsWithValues ps cvals) =
      cvals.map fun v => Pexpr [] () (PEval v) := by
  induction ps generalizing cvals with
  | nil => cases cvals with
    | nil => rfl
    | cons _ _ => cases hlen
  | cons p ps ih => cases cvals with
    | nil => cases hlen
    | cons v cvals =>
      rw [saveParamsWithValues_cons, List.map_cons]
      show (p.1, (p.2.1, Pexpr [] () (PEval v))).2.2 ::
        saveParamPexprs (saveParamsWithValues ps cvals) = _
      rw [ih cvals (Nat.succ.inj hlen)]

/-- ... so the re-formed list passes the engine's value test with the
    same values: the successor of the EVAL arm is exactly the TAU
    arm's redex. -/
theorem valueFromPexprs_withValues
    (ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)))
    (cvals : List value) (hlen : ps.length = cvals.length) :
    valueFromPexprs (saveParamPexprs (saveParamsWithValues ps cvals)) = some cvals := by
  rw [saveParamPexprs_withValues ps cvals hlen, valueFromPexprs_map_val]

/-- The pure evaluator is the identity on the engine's value test
    (`evalPexpr` returns a `PEval v` operand's value verbatim). -/
theorem evalPexpr_of_valueFromPexpr (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym)
    (ρ : EnvStack) {pe : generic_pexpr Unit sym} {v : value}
    (h : valueFromPexpr pe = some v) : evalPexpr tds ext ρ pe = some v := by
  rcases pe with ⟨a, u, pe_⟩
  cases u
  cases pe_ <;> simp only [valueFromPexpr] at h
  all_goals first
    | (obtain rfl := Option.some.inj h; exact evalPexpr_val tds ext ρ _ _)
    | (cases h)

/-- All-or-nothing evaluation agrees with the engine's value test on
    literal operand lists (`evalPexpr` is the identity on `PEval v`). -/
theorem evalPexprs_of_valueFromPexprs (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym)
    (ρ : EnvStack) {pes : List (generic_pexpr Unit sym)} {vs : List value}
    (h : valueFromPexprs pes = some vs) : evalPexprs tds ext ρ pes = some vs := by
  induction pes generalizing vs with
  | nil => rw [valueFromPexprs_nil] at h; exact h
  | cons pe pes ih =>
    rw [valueFromPexprs_cons] at h
    revert h
    cases hpe : valueFromPexpr pe with
    | none => intro h; cases h
    | some v =>
      cases hpes : valueFromPexprs pes with
      | none => intro h; cases h
      | some vs' =>
        intro h
        obtain rfl : v :: vs' = vs := Option.some.inj h
        rw [evalPexprs_cons, evalPexpr_of_valueFromPexpr tds ext ρ hpe, ih hpes]
        rfl

theorem evalPexprs_length (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym)
    (ρ : EnvStack) {pes : List (generic_pexpr Unit sym)} {vs : List value}
    (h : evalPexprs tds ext ρ pes = some vs) : pes.length = vs.length := by
  induction pes generalizing vs with
  | nil => rw [evalPexprs_nil] at h; cases h; rfl
  | cons pe pes ih =>
    rw [evalPexprs_cons] at h
    revert h
    cases evalPexpr tds ext ρ pe with
    | none => intro h; cases h
    | some v =>
      cases hpes : evalPexprs tds ext ρ pes with
      | none => intro h; cases h
      | some vs' =>
        intro h
        obtain rfl : v :: vs' = vs := Option.some.inj h
        simp only [List.length_cons, ih hpes]

/-- The literal-initializer test yields a list of the same length. -/
theorem valueFromPexprs_length {pes : List (generic_pexpr Unit sym)} {vs : List value}
    (h : valueFromPexprs pes = some vs) : pes.length = vs.length :=
  evalPexprs_length fmapEmpty fmapEmpty [] (evalPexprs_of_valueFromPexprs _ _ _ h)

/-- `update_env` keeps a cons-shaped stack cons-shaped
    (Core_aux.lean:868 — head-frame update). -/
theorem update_env_cons (pat : pattern) (v : value) (ev0 : Fmap sym value)
    (evs : List (Fmap sym value)) :
    update_env pat v (ev0 :: evs) = update_env_aux pat v ev0 :: evs := rfl

/-- Left folds of `update_env` preserve cons-shapedness. -/
theorem foldl_update_env_cons {α : Type} (f : α → pattern) (g : α → value)
    (xs : List α) (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    ∃ ev0', List.foldl (fun acc a => update_env (f a) (g a) acc)
      (ev0 :: evs) xs = ev0' :: evs := by
  induction xs generalizing ev0 with
  | nil => exact ⟨ev0, rfl⟩
  | cons a xs ih =>
    simp only [List.foldl_cons, update_env_cons]
    exact ih (update_env_aux (f a) (g a) ev0)

theorem bindArgs_cons (params : List (sym × core_base_type))
    (vs : List value) (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    ∃ ev0', bindArgs params vs (ev0 :: evs) = ev0' :: evs :=
  foldl_update_env_cons (α := (sym × core_base_type) × value)
    (fun p => mk_sym_pat p.1.1 p.1.2) (fun p => p.2)
    (List.zip params vs) ev0 evs

theorem bindSaveParams_cons (ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)))
    (cvals : List value) (ev0 : Fmap sym value)
    (evs : List (Fmap sym value)) :
    ∃ ev0', bindSaveParams ps cvals (ev0 :: evs) = ev0' :: evs :=
  foldl_update_env_cons
    (α := (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))
      × value)
    (fun p => mk_sym_pat p.1.1 p.1.2.1.1) (fun p => p.2)
    (List.zip ps cvals) ev0 evs

/-- The entry binding reads only the symbols and base types, so the
    EVAL arm's re-formed list binds exactly as the original. -/
theorem bindSaveParams_withValues
    (ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)))
    (cvals : List value) (ρ : EnvStack) :
    bindSaveParams (saveParamsWithValues ps cvals) cvals ρ =
      bindSaveParams ps cvals ρ := by
  unfold bindSaveParams
  induction ps generalizing cvals ρ with
  | nil => cases cvals <;> rfl
  | cons p ps ih =>
    cases cvals with
    | nil => rfl
    | cons v cvals =>
      rw [saveParamsWithValues_cons, List.zip_cons_cons, List.zip_cons_cons,
        List.foldl_cons, List.foldl_cons]
      exact ih cvals _

/-- One-layer application of a memM state transformer. Sound for the
    fragment's ops because allocateObject/loadM/storeM/killM are all
    single-layer `ND fun st => (NDactive/NDkilled, st')` (recon §2.3;
    grepped: no NDnd/NDbranch in their bodies). `none` = the killed
    (UB/error) channel — Step simply has no step there. -/
def applyMemM {α : Type} (m : CerbMem.memM α) (st : Mem) : Option (α × Mem) :=
  match m with
  | ND f =>
    match f st with
    | (NDactive x, st') => some (x, st')
    | _ => none

/-! ### The action location is irrelevant to the memory operation's outcome

`storeM`/`loadM` take the action's source location, but use it only in
the payload of a `fail_` (`NDkilled (failReason err loc)`,
CerbMem.lean:1623/1669); the active arm and the state never depend on
it. Under `applyMemM`, which projects the killed arm to `none`, the two
operations are therefore location-independent as functions. The engine
attaches `loc' := if isLibraryLocation loc then th.current_loc else loc`
to every action request (`step_ctx`'s process_action,
Core_reduction.lean:484) — these two lemmas are what lets the
certification (Soundness.lean, DriverCollapse.lean) transport the
mirror's premise, stated at the redex's own `loc`, to the engine's
`loc'`. `allocateObject` takes no location. -/

/-- The active-arm projection `applyMemM` performs on a one-layer
    result (`ND f`, `f st`). -/
def ndProj {α : Type} :
    (nd_action α String mem_error (mem_constraint CerbMem.IntegerValue) CerbMem.MemState × Mem) →
      Option (α × Mem)
  | (NDactive x, st') => some (x, st')
  | _ => none

/-- One-layer application of an ndM computation — the raw
    `nd_action × state` pair `applyMemM` projects (killed outcomes stay
    visible; the driver collapse's `runOne` layer, DriverCollapse.lean,
    is this same function at the driver's state). -/
def runOne {a info err cs st : Type} (m : ndM a info err cs st) (s : st) :
    nd_action a info err cs st × st :=
  match m with | ND f => f s

theorem applyMemM_ND {α : Type}
    (f : Mem → nd_action α String mem_error (mem_constraint CerbMem.IntegerValue) CerbMem.MemState × Mem)
    (σ : Mem) : applyMemM (ND f) σ = ndProj (f σ) := rfl

/-- `storeM`'s outcome under `applyMemM` does not depend on the location. -/
theorem storeM_loc_irrel {tds : CerbTags.TagDefsMap} (loc loc' : CerbLocation.Loc)
    {ty : ctype} {lk : Bool} {pv : CerbMem.PointerValue} {mv : CerbMem.MemValue} {σ : Mem} :
    applyMemM (CerbMem.storeM tds loc' ty lk pv mv) σ =
      applyMemM (CerbMem.storeM tds loc ty lk pv mv) σ := by
  unfold CerbMem.storeM
  rw [applyMemM_ND, applyMemM_ND]
  dsimp only
  rcases pv with ⟨prov, base⟩
  cases prov <;> cases base <;> dsimp only <;> repeat' (first | rfl | split)

/-- `loadM`'s outcome under `applyMemM` does not depend on the location. -/
theorem loadM_loc_irrel {tds : CerbTags.TagDefsMap} (loc loc' : CerbLocation.Loc)
    {ty : ctype} {pv : CerbMem.PointerValue} {σ : Mem} :
    applyMemM (CerbMem.loadM tds loc' ty pv) σ =
      applyMemM (CerbMem.loadM tds loc ty pv) σ := by
  unfold CerbMem.loadM
  rw [applyMemM_ND, applyMemM_ND]
  dsimp only
  rcases pv with ⟨prov, base⟩
  cases prov <;> cases base <;> dsimp only <;> repeat' (first | rfl | split)

/-- `killM`'s outcome under `applyMemM` does not depend on the location
    (kill/free arc K2): `loc` reaches only the `fail_` payload
    (CerbMem.lean:1559), never the active arm or the state. -/
theorem killM_loc_irrel (loc loc' : CerbLocation.Loc) {isDyn : Bool}
    {pv : CerbMem.PointerValue} {σ : Mem} :
    applyMemM (CerbMem.killM loc' isDyn pv) σ =
      applyMemM (CerbMem.killM loc isDyn pv) σ := by
  unfold CerbMem.killM
  rw [applyMemM_ND, applyMemM_ND]
  dsimp only
  rcases pv with ⟨prov, base⟩
  cases prov <;> cases base <;> dsimp only <;> repeat' (first | rfl | split)

/-! ## The step relation -/

/-- One engine step of the fragment, memory-composed: expression +
    memory to expression + memory. Failure (any NDkilled arm of
    loadM/storeM — the full vocabulary is recon §2.6) is ABSENCE of a
    step: a non-value with no Step is stuck, and the WP's
    UB-exclusion (R4) is exactly `NotStuck`.

    Mirror map (pin 8fb380c9c, generated/):
    - context decomposition/rebuild: get_ctx/apply_ctx
      (Core_reduction.lean:373-389) — the `*_ctx` congruence rules;
    - redex reduction: one_step0 (Core_reduction.lean:353) — the
      beta/merge rules;
    - actions: step_ctx's process_action + step_action
      (Core_reduction.lean:424,484) surface Load/StoreRequest2, which
      the sequential driver discharges against CerbMem.loadM/storeM
      (Driver.lean:273) and feeds `(aid, fp[, mval])` to the
      continuation — the `load`/`store` rules fuse request +
      discharge + continuation into one step, exactly as the recon's
      mini-drive executed it (§3.3).

    Note on `loc`: the engine passes `loc' = if isLibraryLocation loc
    then current_loc else loc` to the memory op (step_ctx,
    process_action). loc only reaches error payloads — never the
    NDactive result or the state — so the rules pass the action's own
    loc; the certification transports the premise to the engine's
    `loc'` by `storeM_loc_irrel`/`loadM_loc_irrel` (above): the
    success arm does not depend on the location. -/
inductive Step (M : MachineCtx) : Config → Config → Prop where
  /-- Positive strong store, evaluated operands (ACTION_EVAL
      phrasing — header note 2). Mirrors: step_action Store0 arm
      (Core_reduction.lean:424 — operand readout via
      act_valueFromPexpr, memValueFromValue at
      `Ctype [] (unatomic_ ty)`, request `StoreRequest2`), driver
      discharge `liftMem (CerbMem.storeM M.tagDefs loc ty lk pv mv)`
      (Driver.lean:273), continuation
      `Expr [] (Eannot [DA_pos [] fp] (mk_value_e Vunit))` (is_excluded
      = none on the fragment's positive path). storeM: CerbMem.lean:1667.
      The env is unread and returned verbatim (the request path never
      touches thread env). -/
  | store {a : List annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {lk : Bool} {pe1 pe2 pe3 : generic_pexpr Unit sym}
      {ty : ctype} {pv : CerbMem.PointerValue} {cv : value}
      {mo : memory_order} {mv : CerbMem.MemValue} {fp : CerbMem.Footprint}
      {ρ : EnvStack} {ctl : Ctl} {σ σ' : Mem}
      (h1 : valueFromPexpr pe1 = some (Vctype ty))
      (h2 : valueFromPexpr pe2 = some (Vobject (OVpointer pv)))
      (h3 : valueFromPexpr pe3 = some cv)
      (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv = some mv)
      (hmem : applyMemM (CerbMem.storeM M.tagDefs loc ty lk pv mv) σ = some (fp, σ')) :
      Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Store0 lk pe1 pe2 pe3 mo)))), ρ, ctl, σ)
           (Expr [] (Eannot [DA_pos [] fp]
              (Expr [] (Epure (Pexpr [] () (PEval Vunit))))), ρ, ctl, σ')
  /-- Positive strong load, evaluated operands. Mirrors: step_action
      Load0 arm (Core_reduction.lean:424 — request `LoadRequest2`,
      continuation `Expr [] (Eannot [DA_pos [] fp] (mk_value_e
      (valueFromMemValue mval).2))`), driver discharge
      `liftMem (CerbMem.loadM M.tagDefs loc ty pv)` (Driver.lean:273).
      loadM: CerbMem.lean:1586 (returns the state unchanged on the
      active path — σ' = σ is derivable, kept in applyMemM shape). -/
  | load {a : List annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {pe1 pe2 : generic_pexpr Unit sym}
      {ty : ctype} {pv : CerbMem.PointerValue} {mo : memory_order}
      {mval : CerbMem.MemValue} {fp : CerbMem.Footprint}
      {ρ : EnvStack} {ctl : Ctl} {σ σ' : Mem}
      (h1 : valueFromPexpr pe1 = some (Vctype ty))
      (h2 : valueFromPexpr pe2 = some (Vobject (OVpointer pv)))
      (hmem : applyMemM (CerbMem.loadM M.tagDefs loc ty pv) σ = some ((fp, mval), σ')) :
      Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Load0 pe1 pe2 mo)))), ρ, ctl, σ)
           (Expr [] (Eannot [DA_pos [] fp]
              (Expr [] (Epure (Pexpr [] () (PEval
                (valueFromMemValue mval).2))))), ρ, ctl, σ')
  /-- Positive strong create (Extension D: cold-start programs create
      their own cells), evaluated operands. Mirrors: step_action
      Create arm (Core_reduction.lean:424 — value operands
      `(Vobject (OVinteger align), Vctype ty)` classify, no ILLTYPED
      arm for these shapes; request `CreateRequest2 pref align ty
      (get_with_address e_annots) none` with continuation
      `mk_value_e (Vobject (OVpointer ptrval))` — a BARE value, no
      Eannot residue), driver discharge `liftMem ((CerbMem.allocateObject
      _lemReader_tagDefs)
      tid pref align ty req_addr_opt init_opt)` (Driver.lean:273).
      allocateObject DISCARDS both the thread id and the requested
      address (CerbMem.lean:1470-1474, `_ : Nat` / `_ : Option Int`),
      so the rule pins them to `0`/`none`; the certification bridges to
      the engine's `tid1`/`get_with_address []` by `rfl` (discarded
      arguments are definitionally interchangeable). Failure (the
      "out of memory" `Other` kill, CerbMem.lean:1479) is absence of a
      step, exactly as for store/load. -/
  | create {a : List annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {pe1 pe2 : generic_pexpr Unit sym}
      {align : CerbMem.IntegerValue} {ty : ctype} {pref : prefix0}
      {pv : CerbMem.PointerValue} {ρ : EnvStack} {ctl : Ctl} {σ σ' : Mem}
      (h1 : valueFromPexpr pe1 = some (Vobject (OVinteger align)))
      (h2 : valueFromPexpr pe2 = some (Vctype ty))
      (hmem : applyMemM (CerbMem.allocateObject M.tagDefs 0 pref align ty none none) σ =
        some (pv, σ')) :
      Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Create pe1 pe2 pref)))), ρ, ctl, σ)
           (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer pv))))), ρ, ctl, σ')
  /-- Positive strong ALLOC — dynamic allocation, Core's `alloc(al, n)`
      (`Alloc0`, C's `malloc`; kill/free arc K3), evaluated INTEGER
      operands. Mirrors: step_action's Alloc0 arm (Core_reduction.lean:424,
      verbatim modulo whitespace: `| Alloc0 pe1 pe2 pref => match
      act_valueFromPexpr pe1, act_valueFromPexpr pe2 with | some (Vobject
      (OVinteger ival1)), some (Vobject (OVinteger ival2)) => ACTION_REQUEST
      "AllocRequest" loc1 (AllocRequest2 pref ival1 ival2 (fun (aid1 : Nat)
      (ptrval : CerbMem.PointerValue) => mk_value_e (Vobject (OVpointer
      ptrval)))) | some _, some _ => ACTION_ILLTYPED "Alloc" | _, _ =>
      ACTION_EVAL "eval operands of Alloc" …`), driver discharge `liftMem
      (CerbMem.allocateRegion tid1 pref align_ival size_ival)` with the
      continuation `mk_th_st' aid1 ptrval` (Driver.lean:273) — the
      continuation value is `mk_value_e (Vobject (OVpointer ptrval))`, a
      BARE pointer value, no `Eannot` residue (exactly create's shape).
      `allocateRegion` DISCARDS the thread id (CerbMem.lean:1533, `_ :
      Nat`), so the rule pins it to `0`; the certification bridges to the
      engine's `tid1` by `rfl` (`allocateRegion_arg_irrel`). The region
      is UNTYPED (`ty := none`, :1544), of size `sizeN.toNat` (ZERO
      admitted, no `max 1`), its base pushed onto `dynamicAddrs` (:1548).
      Failure — the "out of memory" `Other` kill at `alignedAddr == 0`
      (:1541) — is absence of a step, exactly as for create. -/
  | alloc {a : List annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {pe1 pe2 : generic_pexpr Unit sym}
      {align size : CerbMem.IntegerValue} {pref : prefix0}
      {pv : CerbMem.PointerValue} {ρ : EnvStack} {ctl : Ctl} {σ σ' : Mem}
      (h1 : valueFromPexpr pe1 = some (Vobject (OVinteger align)))
      (h2 : valueFromPexpr pe2 = some (Vobject (OVinteger size)))
      (hmem : applyMemM (CerbMem.allocateRegion 0 pref align size) σ = some (pv, σ')) :
      Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Alloc0 pe1 pe2 pref)))), ρ, ctl, σ)
           (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer pv))))), ρ, ctl, σ')
  /-- Positive strong KILL (kill/free arc K2), evaluated pointer
      operand. Mirrors: step_action's Kill arm (Core_reduction.lean:424,
      verbatim modulo whitespace: `| Kill kind1 pe => match
      act_valueFromPexpr pe with | some (Vobject (OVpointer ptrval)) =>
      ACTION_REQUEST "KillRequest" loc1 (KillRequest2 (is_dynamic kind1)
      ptrval (fun (aid1 : Nat) => mk_value_e Vunit)) | some _ =>
      ACTION_ILLTYPED "Kill" | none => ACTION_EVAL "eval operand of Kill"
      …`), driver discharge `liftMem (CerbMem.killM loc1 is_dynamic1
      ptr_val)` (Driver.lean:273), continuation `mk_value_e Vunit` — a
      BARE unit, no `Eannot` residue (like create, unlike store/load).
      The `Static0 ty` payload is DISCARDED by the engine: only
      `is_dynamic kind` reaches the request, so the rule is generic in
      `kind` (the fragment `Frag.kill` restricts to the static kill;
      the dynamic kill is K3). killM: CerbMem.lean:1555-1580,
      deterministic — every failure arm (`Free_non_matching` UB179a,
      `Free_dead_allocation` UB179b, the non-UB `Free_out_of_bound`) is
      absence of a step. The env is unread and returned verbatim. -/
  | kill {a : List annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {kind : kill_kind} {pe : generic_pexpr Unit sym}
      {pv : CerbMem.PointerValue} {ρ : EnvStack} {ctl : Ctl} {σ σ' : Mem}
      (h1 : valueFromPexpr pe = some (Vobject (OVpointer pv)))
      (hmem : applyMemM (CerbMem.killM loc (is_dynamic kind) pv) σ = some ((), σ')) :
      Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Kill kind pe)))), ρ, ctl, σ)
           (Expr [] (Epure (Pexpr [] () (PEval Vunit))), ρ, ctl, σ')
  /-- LETS-PURE at a wildcard pattern:
      `lets _ = v in E2 --> E2` (one_step0 Esseq bare-value arm,
      Core_reduction.lean:353 "reduction: LETS-PURE"). The env update
      `update_env (CaseBase (none,_))` is the identity on a NONEMPTY
      stack (Core_aux.lean:861-868, first arm) and a failwithI PANIC
      on an empty one — the cons shape is load-bearing (header note
      1): no step exists where the engine panics. -/
  | sseq_pure {a pa : List annot} {bty : core_base_type} {v : value}
      {e2 : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
      {ctl : Ctl} {σ : Mem} :
      Step M (Expr a (Esseq (Pattern pa (CaseBase (none, bty)))
              (ofVal (.pure v)) e2), ev0 :: evs, ctl, σ)
           (e2, ev0 :: evs, ctl, σ)
  /-- LETS-ANNOT at a wildcard pattern:
      `lets _ = {A}v in E2 --> {A} E2` (one_step0 Esseq Eannot arm,
      Core_reduction.lean:353 "reduction: LETS-ANNOT" — the engine
      writes the result node annots as `[]` verbatim). This is the
      R-i residue entering the continuation. Same env discipline as
      LETS-PURE. -/
  | sseq_annot {a pa : List annot} {bty : core_base_type}
      {ds : List dyn_annotation} {v : value} {e2 : CoreExpr}
      {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {ctl : Ctl} {σ : Mem} :
      Step M (Expr a (Esseq (Pattern pa (CaseBase (none, bty)))
              (ofVal (.annot ds v)) e2), ev0 :: evs, ctl, σ)
           (Expr [] (Eannot ds e2), ev0 :: evs, ctl, σ)
  /-- LETW-PURE at a wildcard pattern (S1b DRIFT TEST — Ewseq joins
      through the generic route, design record §8 item 8):
      `letw _ = v in E2 --> E2` (one_step0 Ewseq bare-value arm,
      Core_reduction.lean:353 "reduction: LETW-PURE"). Same env
      discipline as LETS-PURE: `update_env` at a wildcard is the
      identity on a NONEMPTY stack and a failwithI PANIC on an empty
      one — the cons shape is load-bearing (header note 1). -/
  | wseq_pure {a pa : List annot} {bty : core_base_type} {v : value}
      {e2 : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
      {ctl : Ctl} {σ : Mem} :
      Step M (Expr a (Ewseq (Pattern pa (CaseBase (none, bty)))
              (ofVal (.pure v)) e2), ev0 :: evs, ctl, σ)
           (e2, ev0 :: evs, ctl, σ)
  /-- LETW-ANNOT at a wildcard pattern:
      `letw _ = {A}v in E2 --> {A} E2` (one_step0 Ewseq Eannot arm,
      Core_reduction.lean:353 "reduction: LETW-ANNOT" — the engine
      writes the result node annots as `[]` verbatim). Same env
      discipline as LETW-PURE. -/
  | wseq_annot {a pa : List annot} {bty : core_base_type}
      {ds : List dyn_annotation} {v : value} {e2 : CoreExpr}
      {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {ctl : Ctl} {σ : Mem} :
      Step M (Expr a (Ewseq (Pattern pa (CaseBase (none, bty)))
              (ofVal (.annot ds v)) e2), ev0 :: evs, ctl, σ)
           (Expr [] (Eannot ds e2), ev0 :: evs, ctl, σ)
  /-- LETS-PURE at the SPECIFIED-BINDER pattern (S4 binding beta):
      `lets Specified(x) = Specified(ov) in E2 --> E2` with `x` bound
      to the payload OBJECT value (one_step0 Esseq bare-value arm,
      Core_reduction.lean:353 "reduction: LETS-PURE" — the env update
      is `update_env (specPat …)`, whose `CaseCtor Cspecified` arm
      recurses into the sym binder with `Vobject oval`,
      Core_aux.lean:861). A non-`LVspecified` bound value would take
      update_env_aux's failwithI mismatch arm — mirrored fail-closed
      as ABSENCE of a step (the WF-shape discipline, header note 1). -/
  | sseq_spec_pure {a pa pb : List annot} {x : sym} {bty : core_base_type}
      {ov : object_value} {e2 : CoreExpr}
      {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {ctl : Ctl} {σ : Mem} :
      Step M (Expr a (Esseq (specPat pa pb x bty)
              (ofVal (.pure (Vloaded (LVspecified ov)))) e2), ev0 :: evs, ctl, σ)
           (e2, update_env (specPat pa pb x bty) (Vloaded (LVspecified ov))
              (ev0 :: evs), ctl, σ)
  /-- LETS-ANNOT at the Specified-binder pattern:
      `lets Specified(x) = {A}Specified(ov) in E2 --> {A} E2`, same
      binding discipline (one_step0 Esseq Eannot arm, "reduction:
      LETS-ANNOT" — the engine binds the BARE value; the annotations
      flow to the continuation wrapper). -/
  | sseq_spec_annot {a pa pb : List annot} {x : sym} {bty : core_base_type}
      {ds : List dyn_annotation} {ov : object_value} {e2 : CoreExpr}
      {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {ctl : Ctl} {σ : Mem} :
      Step M (Expr a (Esseq (specPat pa pb x bty)
              (ofVal (.annot ds (Vloaded (LVspecified ov)))) e2), ev0 :: evs, ctl, σ)
           (Expr [] (Eannot ds e2),
            update_env (specPat pa pb x bty) (Vloaded (LVspecified ov))
              (ev0 :: evs), ctl, σ)
  /-- PURE at a non-value pexpr (S4): ONE engine step BIG-STEP
      evaluating the pure expression (one_step0's Epure arm,
      Core_reduction.lean:353 "reduction: PURE" — `EVAL "Epure"`
      over `full_eval_pexpr1 pe`, wrapped by step_ctx's EVAL arm
      into a Step_with_runstate2 whose successor arena carries
      `Expr annots1 (Epure (mk_value_pe cval))`). The mirror premise
      is the certified pure evaluator; the PURE-UNDEF channel is
      excluded because the evaluator RETURNS a value. Env, state,
      and node annotations verbatim. -/
  | pure_eval {a : List annot} {pe : generic_pexpr Unit sym} {v : value}
      {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
      (hnv : valueFromPexpr pe = none)
      (hv : evalPexpr M.tagDefs M.extern ρ pe = some v) :
      Step M (Expr a (Epure pe), ρ, ctl, σ)
           (Expr a (Epure (Pexpr [] () (PEval v))), ρ, ctl, σ)
  /-- ACTION_EVAL for a positive strong load with an unevaluated
      pointer operand (S4): ONE engine step BIG-STEP evaluating the
      operands (step_action's Load0 `_, _` arm, Core_reduction.lean:
      424 — `ACTION_EVAL "eval operands of Load"` over the two
      `full_eval_pexpr1` calls, wrapped by process_action's
      ACTION_EVAL arm into Step_with_runstate2; successor
      `Expr e_annots (wrap_act (Load0 (mk_value_pe cval1)
      (mk_value_pe cval2) mo))`). The type operand is pinned at its
      canonical evaluated shape (its re-evaluation is the identity);
      the pointer operand evaluates through the certified pure
      evaluator to a POINTER value — the successor is exactly the
      canonical load redex, so the certified load axiom takes over.
      The PEconstrained PANIC pre-arm of `act_valueFromPexpr` is
      excluded by the evaluator premise's grammar (PePure has no
      PEconstrained). -/
  | load_eval {a : List annot} {loc : CerbLocation.Loc}
      {ann : core_run_annotation} {ty : ctype}
      {pe2 : generic_pexpr Unit sym} {pv : CerbMem.PointerValue}
      {mo : memory_order} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
      (hnv2 : valueFromPexpr pe2 = none)
      (hv2 : evalPexpr M.tagDefs M.extern ρ pe2 = some (Vobject (OVpointer pv))) :
      Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Load0 (Pexpr [] () (PEval (Vctype ty))) pe2 mo)))), ρ, ctl, σ)
           (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Load0 (Pexpr [] () (PEval (Vctype ty)))
                     (Pexpr [] () (PEval (Vobject (OVpointer pv)))) mo)))),
            ρ, ctl, σ)
  /-- Reduction under the strong-sequencing frame. Mirrors get_ctx's
      Esseq arm (descend into e1 when it is not irreducible —
      Core_reduction.lean:375) + apply_ctx's Csseq rebuild
      (Core_reduction.lean:389). No irreducibility guard is needed:
      no Step rule fires on an irreducible e1 (see
      `Step.not_irreducible_shape` note below / slice notes §D4).
      Env-GENERAL: the thread env is global, so a descent step's env
      update carries through the frame unchanged in shape.
      S3 GUARD (header note 4): `jumpRedex? e1 = none` — a jump of
      e1 is NEVER framed; the engine's Erun arm discards the context
      (no `apply_ctx`), so `K[run …] --> cont`, covered by
      `Step.run` alone.
      C2 GUARD (calls arc): `toVal e1 = none` — get_ctx descends into
      `e1` only when `is_irreducible e1 = false` (Core_reduction.lean:375,
      `if is_irreducible e1 then [(CTX, expr1)] else …`). Until C2 the
      guard was derivable (no rule stepped a value); `Step.ret_annot`
      steps the annotated value `{A}v` at a non-empty call stack
      WITHOUT changing the control, and the engine never frames that
      round (at `Esseq pat {A}v e2` the root IS the LETS-ANNOT redex),
      so the engine's own guard becomes load-bearing. A call of `e1`
      (`Step.call`) and a return (`Step.ret`) change the control, so
      they are never instances of the premise. -/
  | sseq_ctx {a : List annot} {pat : pattern} {e1 e1' e2 : CoreExpr}
      {ρ ρ' : EnvStack} {ctl : Ctl} {σ σ' : Mem}
      (hnj : jumpRedex? e1 = none) (hnv : toVal e1 = none) :
      Step M (e1, ρ, ctl, σ) (e1', ρ', ctl, σ') →
      Step M (Expr a (Esseq pat e1 e2), ρ, ctl, σ) (Expr a (Esseq pat e1' e2), ρ', ctl, σ')
  /-- Reduction under the weak-sequencing frame (S1b DRIFT TEST).
      Mirrors get_ctx's Ewseq arm (descend into e1 when it is not
      irreducible — Core_reduction.lean:375) + apply_ctx's Cwseq
      rebuild (Core_reduction.lean:389). Same S3 congruence guard
      as `sseq_ctx`: a jump of e1 is never framed; same C2 guard: a
      value `e1` is never descended into. -/
  | wseq_ctx {a : List annot} {pat : pattern} {e1 e1' e2 : CoreExpr}
      {ρ ρ' : EnvStack} {ctl : Ctl} {σ σ' : Mem}
      (hnj : jumpRedex? e1 = none) (hnv : toVal e1 = none) :
      Step M (e1, ρ, ctl, σ) (e1', ρ', ctl, σ') →
      Step M (Expr a (Ewseq pat e1 e2), ρ, ctl, σ) (Expr a (Ewseq pat e1' e2), ρ', ctl, σ')
  /-- Reduction under a dyn-annotation frame. Mirrors get_ctx's plain
      `Eannot xs e` arm (Cannot-descent — taken only when e is NOT
      itself Eannot-rooted, because the double-annot arm precedes it;
      Core_reduction.lean:375) + apply_ctx's Cannot rebuild
      (Core_reduction.lean:389). The guard is load-bearing: without
      it this rule would race the ANNOTS merge, which the engine
      never does. -/
  | annot_ctx {a : List annot} {ds : List dyn_annotation} {b b' : CoreExpr}
      {ρ ρ' : EnvStack} {ctl : Ctl} {σ σ' : Mem}
      (hnj : jumpRedex? b = none) :
      annotRooted b = false →
      Step M (b, ρ, ctl, σ) (b', ρ', ctl, σ') →
      Step M (Expr a (Eannot ds b), ρ, ctl, σ) (Expr a (Eannot ds b'), ρ', ctl, σ')
  /-- ANNOTS merge: `{A_1} {A_2} E --> {A_1 ++ A_2} E` (one_step0
      Eannot arm, Core_reduction.lean:353 "reduction: ANNOTS";
      combine_dyn_annotations = (++), :305-306; get_ctx routes every
      double-annot root here, :375; the double-annot value is
      explicitly NOT irreducible, :293 first arm). Unconditional on
      the body, exactly as the engine; env untouched. -/
  | annot_merge {a1 a2 : List annot} {ds1 ds2 : List dyn_annotation}
      {b : CoreExpr} {ρ : EnvStack} {ctl : Ctl} {σ : Mem} :
      Step M (Expr a1 (Eannot ds1 (Expr a2 (Eannot ds2 b))), ρ, ctl, σ)
           (Expr (a1 ++ a2) (Eannot (ds1 ++ ds2) b), ρ, ctl, σ)
  /-- THE GLOBAL JUMP (S3, header note 4). Mirrors step_ctx's Erun
      arm (Core_reduction.lean:484): the spine hole holds
      `run l pes`; the label resolves in the CURRENT procedure's
      registered map (`hl` — the `labeled` read is
      `state_except_read`, run-state READ-ONLY; the unresolvable-
      label and no-current-proc failwithI PANIC channels are
      excluded because the rule fires only on successful resolution,
      certified at the proc-carrying profile in Soundness.lean); the
      arguments evaluate against the CURRENT env (`hvs` — the pure
      evaluator, certified against `full_eval_pexpr'`); the successor
      REPLACES THE WHOLE EXPRESSION by the registered sseq-extended
      continuation with the parameters rebound
      (`{th_st with env := env', arena := cont_expr}` — no
      `apply_ctx`: the frame spine is DISCARDED). Cons-shaped env:
      `update_env` panics on an empty stack (Core_aux.lean:868). -/
  | run {e : CoreExpr} {l : sym} {pes : List (generic_pexpr Unit sym)}
      {params : List (sym × core_base_type)} {cont : CoreExpr}
      {vs : List value} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
      {ctl : Ctl} {σ : Mem}
      (hj : jumpRedex? e = some (l, pes))
      (hl : lookupLabel (M.labelsAt ctl.proc) l = some (params, cont))
      (hvs : evalPexprs M.tagDefs M.extern (ev0 :: evs) pes = some vs) :
      Step M (e, ev0 :: evs, ctl, σ)
           (cont, bindArgs params vs (ev0 :: evs), ctl, σ)
  /-- Esave ENTRY at value-shaped parameter pexprs: one_step0's Esave
      TAU arm (Core_reduction.lean:353, `match valueFromPexprs (…
      sym_bTy_pes) with | some cvals => /- reduction: SAVE (tau part)
      -/ TAU "Esave" (foldl update_env …) e`) — the parameters bind
      into the env, the arena becomes the save body. Context-preserving
      (an ordinary redex under the spine). -/
  | save {a : List annot} {sb : sym × core_base_type}
      {ps : List (sym × ((core_base_type ×
        Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
      {body : CoreExpr} {cvals : List value}
      {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {ctl : Ctl} {σ : Mem}
      (hvals : valueFromPexprs (saveParamPexprs ps) = some cvals) :
      Step M (Expr a (Esave sb ps body), ev0 :: evs, ctl, σ)
           (body, bindSaveParams ps cvals (ev0 :: evs), ctl, σ)
  /-- Esave PARAMETER EVALUATION (QA-1/H-1): one_step0's Esave EVAL
      arm (Core_reduction.lean:353, `| none => /- reduction: SAVE
      (eval part) + SAVE-UNDEF -/ EVAL "Esave" (stExceptUndef_bind
      (stExceptUndef_mapM (fun (sym1, (bTy, pe)) => … eval_pexpr1 pe
      … (sym1, (bTy, pe'))) sym_bTy_pes) (fun sym_bTy_pes' =>
      stExceptUndef_return (Expr annots1 (Esave sym_bTy sym_bTy_pes'
      e))))`): when the initializers are NOT all values, ONE engine
      step evaluates every initializer (one full evaluator iteration
      each — `eval_pexpr1`, which on the certified operand grammar
      delivers the `mk_value_pe` form, exactly as `memop_eval`) and
      RE-FORMS the Esave node with the evaluated initializers, node
      annotations preserved; the TAU arm then fires on the successor.
      The mirror premise is the certified pure evaluator over the
      whole list (`evalPexprs`); the SAVE-UNDEF channel is excluded
      because the evaluator RETURNS values. Env and state verbatim. -/
  | save_eval {a : List annot} {sb : sym × core_base_type}
      {ps : List (sym × ((core_base_type ×
        Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
      {body : CoreExpr} {cvals : List value} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
      (hnv : valueFromPexprs (saveParamPexprs ps) = none)
      (hvals : evalPexprs M.tagDefs M.extern ρ (saveParamPexprs ps) = some cvals) :
      Step M (Expr a (Esave sb ps body), ρ, ctl, σ)
           (Expr a (Esave sb (saveParamsWithValues ps cvals) body), ρ, ctl, σ)
  /-- Eif, true branch: ONE engine step with a BIG-STEP guard
      (one_step0's Eif TAU_WITH_RUNSTATE, Core_reduction.lean:353 —
      `full_eval_pexpr1 pe1` then dispatch on Vtrue/Vfalse; any other
      value is a failwithI PANIC, excluded by the premise). The
      mirror premise is the pure evaluator (header note 5). Env and
      state untouched. -/
  | if_true {a : List annot} {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
      {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
      (hg : evalPexpr M.tagDefs M.extern ρ g = some Vtrue) :
      Step M (Expr a (Eif g e2 e3), ρ, ctl, σ) (e2, ρ, ctl, σ)
  /-- Eif, false branch. -/
  | if_false {a : List annot} {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
      {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
      (hg : evalPexpr M.tagDefs M.extern ρ g = some Vfalse) :
      Step M (Expr a (Eif g e2 e3), ρ, ctl, σ) (e3, ρ, ctl, σ)
  /-- Ecase at a VALUE scrutinee: TAU into the substituted branch
      (one_step0's Ecase value arm, Core_reduction.lean:353 —
      `select_case subst_sym_expr cval pat_es`; no-match ILLTYPED is
      a refusal = absence of the `hsel` premise; the
      PEconstrained-scrutinee PANIC arm is excluded by `hv`,
      `valueFromPexpr (PEconstrained …) = none`). The non-value-
      scrutinee EVAL arm (small-step `eval_pexpr1`) is not mirrored
      this slice (header note 5). -/
  | case_value {a : List annot} {pe : generic_pexpr Unit sym}
      {pats : List (pattern × CoreExpr)} {cval : value} {e' : CoreExpr}
      {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
      (hv : valueFromPexpr pe = some cval)
      (hsel : select_case subst_sym_expr cval pats = some e') :
      Step M (Expr a (Ecase pe pats), ρ, ctl, σ) (e', ρ, ctl, σ)
  /-- LETS-PURE at the plain-symbol binder (list-reverse phase A):
      `lets x = v in E2 --> E2` with `x` bound to `v` verbatim
      (one_step0 Esseq bare-value arm, Core_reduction.lean:353
      "reduction: LETS-PURE"; the env update is `update_env
      (symPat …)`, whose `CaseBase (some sym1, _)` arm adds the
      binding, Core_aux.lean:861). RECORDED DIVERGENCE (deliberate,
      fail-closed sub-relation): the `{A}v` LETS-ANNOT variant at
      this pattern is NOT mirrored — the only producer of
      sym-binder-bound values in the fragment is the memop protocol,
      which delivers BARE values (step_ctx's MEMOP continuation,
      Core_reduction.lean:484 — `mk_pure_e`, no Eannot residue); the
      annot variant is a mechanical extension when needed. -/
  | sseq_sym_pure {a pa : List annot} {x : sym} {bty : core_base_type}
      {v : value} {e2 : CoreExpr}
      {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {ctl : Ctl} {σ : Mem} :
      Step M (Expr a (Esseq (symPat pa x bty) (ofVal (.pure v)) e2), ev0 :: evs, ctl, σ)
           (e2, update_env (symPat pa x bty) v (ev0 :: evs), ctl, σ)
  /-- THE POINTER-EQUALITY MEMOP at evaluated operands (list-reverse
      phase A — the honest null test): ONE engine step. Mirrors:
      one_step0's Ememop arm at value operands (`valueFromPexprs pes
      = some cvals` → `MEMOP PtrEq cvals`, Core_reduction.lean:353
      "reduction: MEMOP"), step_ctx's MEMOP dispatch
      (Core_reduction.lean:484 — `Step_memop_request2
      th_st.current_loc PtrEq cvals tid (is_unseq_with_ccall ctx)
      (fun cval => wrap_expr (mk_pure_e (mk_value_pe cval)))`), the
      sequential driver's memop discharge (driver21's
      Step_memop_request2 arm, Driver.lean:377 →
      `perform_memop_request2`, Driver.lean:288, PtrEq arm:
      `liftMem (CerbMem.eqPtrval loc ptr_val1 ptr_val2)` then
      `mk_th_st (if is_eq then Vtrue else Vfalse)`). The successor
      is a BARE pure value (no Eannot residue, unlike load/store —
      the memop protocol carries no dyn annotation). `loc`: the
      engine passes `th_st.current_loc`; `eqPtrval` DISCARDS its loc
      argument (CerbMem.lean:1731, `_ : CerbLocation.Loc`), so the
      rule pins `default` (the frozen profiles' current_loc) — any
      two locs are definitionally the same operation
      (`eqPtrval` never reads it; certified via the rfl bridge in
      Soundness.lean). Failure (the killed channel) and the
      differing-provenance ND fork (`msum`, CerbMem.lean:1753 — a
      real NDnd, not single-layer) are ABSENCE of a step: `applyMemM`
      answers `none` there, fail-closed. -/
  | memop_ptreq {a : List annot} {pe1 pe2 : generic_pexpr Unit sym}
      {pv1 pv2 : CerbMem.PointerValue} {b : Bool}
      {ρ : EnvStack} {ctl : Ctl} {σ σ' : Mem}
      (h1 : valueFromPexpr pe1 = some (Vobject (OVpointer pv1)))
      (h2 : valueFromPexpr pe2 = some (Vobject (OVpointer pv2)))
      (hmem : applyMemM (CerbMem.eqPtrval default pv1 pv2) σ = some (b, σ')) :
      Step M (Expr a (Ememop PtrEq [pe1, pe2]), ρ, ctl, σ)
           (Expr [] (Epure (Pexpr [] () (PEval (boolValue b)))), ρ, ctl, σ')
  /-- MEMOP-OPERAND EVALUATION (list-reverse phase A): ONE engine
      step BIG-STEP evaluating both operands of a two-operand memop
      (one_step0's Ememop arm at a non-value operand list,
      Core_reduction.lean:353 — `EVAL "Ememop"` over
      `stExceptUndef_mapM eval_pexpr1 pes`; step_ctx's eval_pexpr1
      is one full iteration of the evaluator tower — `eval_pexpr20`
      then the Sum readout, Core_reduction.lean:484/84 — which on
      the certified operand grammar delivers the fully evaluated
      `mk_value_pe` form in ONE application, exactly like the
      already-certified `full_eval_pexpr`). Node annotations are
      PRESERVED (`Expr annots1 (Ememop memop1 pes')`). The mirror
      premises are the certified pure evaluator; memop-generic
      exactly as the engine's arm. -/
  | memop_eval {a : List annot} {mop : memop}
      {pe1 pe2 : generic_pexpr Unit sym} {v1 v2 : value}
      {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
      (hnv : valueFromPexprs [pe1, pe2] = none)
      (hv1 : evalPexpr M.tagDefs M.extern ρ pe1 = some v1)
      (hv2 : evalPexpr M.tagDefs M.extern ρ pe2 = some v2) :
      Step M (Expr a (Ememop mop [pe1, pe2]), ρ, ctl, σ)
           (Expr a (Ememop mop
             [Pexpr [] () (PEval v1), Pexpr [] () (PEval v2)]), ρ, ctl, σ)
  /-- ACTION_EVAL for a positive strong store whose operands are NOT
      ALL values (list-reverse phase A; generalized to the engine's
      own dispatch at QA-1/H-1): ONE engine step BIG-STEP evaluating
      the operands (step_action's Store0 arm, Core_reduction.lean:424
      — `match act_valueFromPexpr pe1, act_valueFromPexpr pe2,
      act_valueFromPexpr pe3 with | some (Vctype ty1), some (Vobject
      (OVpointer ptrval)), some cval => ACTION_REQUEST … | some _,
      some _, some _ => ACTION_ILLTYPED "Store" | _, _, _ =>
      ACTION_EVAL "eval operands of Store"` over the three
      `full_eval_pexpr1` calls, wrapped by process_action's
      ACTION_EVAL arm; successor `Expr e_annots (wrap_act (Store0
      is_locking (mk_value_pe cval1) (mk_value_pe cval2) (mk_value_pe
      cval3) mo1))`). The arm fires exactly when the operand triple is
      not all values; the type operand is pinned at its canonical
      evaluated shape (its re-evaluation is the identity), so the
      engine's three-operand test is `hnv` on the pointer/value pair
      — the mixed shapes (`store(int, p, 7)`: symbol pointer, literal
      value; literal pointer, symbol value) are included. Pointer and
      value operands evaluate through the certified pure evaluator —
      the pointer to a POINTER value, so the successor is exactly the
      canonical store redex. The `Store0 … PEconstrained` failwithI
      pre-arm (Core_reduction.lean:424) is excluded by the evaluator
      premise (`evalPexpr (PEconstrained …) = none`). -/
  | store_eval {a : List annot} {loc : CerbLocation.Loc}
      {ann : core_run_annotation} {lk : Bool} {ty : ctype}
      {pe2 pe3 : generic_pexpr Unit sym} {pv : CerbMem.PointerValue}
      {cv : value} {mo : memory_order} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
      (hnv : valueFromPexprs [pe2, pe3] = none)
      (hv2 : evalPexpr M.tagDefs M.extern ρ pe2 = some (Vobject (OVpointer pv)))
      (hv3 : evalPexpr M.tagDefs M.extern ρ pe3 = some cv) :
      Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Store0 lk (Pexpr [] () (PEval (Vctype ty))) pe2 pe3 mo)))), ρ, ctl, σ)
           (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Store0 lk (Pexpr [] () (PEval (Vctype ty)))
                      (Pexpr [] () (PEval (Vobject (OVpointer pv))))
                      (Pexpr [] () (PEval cv)) mo)))), ρ, ctl, σ)
  /-- ACTION_EVAL for a positive strong kill with an unevaluated
      pointer operand (kill/free arc K2): ONE engine step BIG-STEP
      evaluating the operand (step_action's Kill `none` arm,
      Core_reduction.lean:424 — `ACTION_EVAL "eval operand of Kill"`
      over `full_eval_pexpr1 pe`, wrapped by process_action's
      ACTION_EVAL arm into Step_with_runstate2; successor `Expr
      e_annots (wrap_act (Kill kind1 (mk_value_pe cval)))` for ANY
      `cval`). As `load_eval`/`store_eval`, the mirror pins the
      evaluated value to a POINTER — the successor is exactly the
      canonical kill redex; a non-pointer value is the engine's
      ILLTYPED-at-distance-one round (`ShippedRefusal.error_next`,
      `complete_kill_op`), classified, not mirrored. -/
  | kill_eval {a : List annot} {loc : CerbLocation.Loc}
      {ann : core_run_annotation} {kind : kill_kind}
      {pe : generic_pexpr Unit sym} {pv : CerbMem.PointerValue}
      {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
      (hnv : valueFromPexpr pe = none)
      (hv : evalPexpr M.tagDefs M.extern ρ pe = some (Vobject (OVpointer pv))) :
      Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Kill kind pe)))), ρ, ctl, σ)
           (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Kill kind (Pexpr [] () (PEval (Vobject (OVpointer pv)))))))), ρ, ctl, σ)
  /-- ACTION_EVAL for a positive strong alloc whose operands are NOT
      all values (kill/free arc K3): ONE engine step BIG-STEP
      evaluating both operands, alignment first (step_action's Alloc0
      `_, _` arm, Core_reduction.lean:424 — `ACTION_EVAL "eval operands
      of Alloc" (stExceptUndef_bind (full_eval_pexpr1 pe1) (fun cval1 =>
      stExceptUndef_bind (full_eval_pexpr1 pe2) (fun cval2 =>
      stExceptUndef_return (wrap (Alloc0 (mk_value_pe cval1) (mk_value_pe
      cval2) pref)))))`; an already-evaluated operand re-evaluates to
      itself). The arm fires exactly when the operand pair is not all
      values (`hnv`, the engine's `valueFromPexprs` test — mixed shapes
      included, as `store_eval`). As `load_eval`/`store_eval`/`kill_eval`,
      the mirror pins the evaluated values to INTEGERS — the successor is
      exactly the canonical alloc redex; a non-integer value is the
      engine's ILLTYPED-at-distance-one round (`ShippedRefusal.error_next
      … "Alloc"`, `complete_alloc_op`), classified, not mirrored. -/
  | alloc_eval {a : List annot} {loc : CerbLocation.Loc}
      {ann : core_run_annotation} {pe1 pe2 : generic_pexpr Unit sym}
      {align size : CerbMem.IntegerValue} {pref : prefix0}
      {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
      (hnv : valueFromPexprs [pe1, pe2] = none)
      (hv1 : evalPexpr M.tagDefs M.extern ρ pe1 = some (Vobject (OVinteger align)))
      (hv2 : evalPexpr M.tagDefs M.extern ρ pe2 = some (Vobject (OVinteger size))) :
      Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Alloc0 pe1 pe2 pref)))), ρ, ctl, σ)
           (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Alloc0 (Pexpr [] () (PEval (Vobject (OVinteger align))))
                      (Pexpr [] () (PEval (Vobject (OVinteger size)))) pref)))), ρ, ctl, σ)
  /-- THE PROCEDURE CALL (calls arc C2) — context CAPTURING. Mirrors
      step_ctx's PCALL arm (Core_reduction.lean:484, col 18133; verbatim
      modulo whitespace): `| Eproc _ (Sym psym) pes => Step_with_runstate2
      (RSK_eval "Eproc") (stExceptUndef_bind (stExceptUndef_mapM
      full_eval_pexpr' pes) (fun cvals => stExceptUndef_bind (runEU
      (except_bind (call_proc core_extern1 file1 psym cvals)
      exception_undef_return)) (fun (proc_env, expr1) =>
      stExceptUndef_return { { { { { th_st with current_proc_opt := some
      psym } with env := proc_env :: th_st.env } with exec_loc :=
      push_exec_loc psym th_st.current_loc th_st.exec_loc } with stack0 :=
      Stack_cons2 th_st.current_proc_opt ctx th_st.stack0 } with arena :=
      expr1 })))`. ONE round evaluates every argument against the
      CURRENT env (`full_eval_pexpr'` closed over `th_st`; the mirror
      premise is the certified pure evaluator over the whole list,
      `hvs`) AND performs the call: `call_proc`'s lookup (`hf`, the
      mirror `lookupProc`) and arity check (`hlen`), the fresh parameter
      frame pushed (`procEnv`), the callee installed as the arena, the
      current procedure set to the callee, the caller's procedure and
      the redex's EVALUATION CONTEXT `ctx` pushed on the call stack
      (`Stack_cons2 th_st.current_proc_opt ctx th_st.stack0` — the
      control's `κ` grows by `(ctl.proc, ctx)`), the execution location
      pushed (`push_exec_loc`, Core_run_aux.lean:380, at the thread's
      `current_loc` = `M.currentLoc`). The rule is stated at the WHOLE
      expression, like `Step.run`: `callRedex? e = some (ctx, f, pes)`
      names the redex AND the context get_ctx pairs it with, which is
      what the engine captures (a call under `Esseq pat [·] e₂` pushes
      `Csseq [] pat CTX e₂`, so the return re-enters the sequencing
      frame — `Step.ret`). Memory and run state untouched (the monad is
      `runEU`-lifted and state-verbatim; `labeled` is installed once at
      `initial_core_run_state`, never by a call). The two `call_proc`
      failures are ABSENCE of a step: transparent `Illformed_program`
      kills, classified in Round.lean (`complete_call`). The
      implementation-constant call `Eproc _ (Impl _) _` (`Step_fs2`) is
      outside the fragment (`callRedex?` answers `none`). -/
  | call {e : CoreExpr} {ctx : context} {f : sym} {pes : List (generic_pexpr Unit sym)}
      {params : List (sym × core_base_type)} {body : CoreExpr} {vs : List value}
      {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
      (hc : callRedex? e = some (ctx, f, pes))
      (hvs : evalPexprs M.tagDefs M.extern ρ pes = some vs)
      (hf : lookupProc M.file M.extern f = some (params, body))
      (hlen : params.length = vs.length) :
      Step M (e, ρ, ctl, σ)
           (body, procEnv params vs :: ρ,
            ⟨(ctl.proc, ctx) :: ctl.κ, some f, push_exec_loc f M.currentLoc ctl.execLoc⟩, σ)
  /-- THE RETURN (calls arc C2). Mirrors step_ctx's value arm at a
      NON-EMPTY call stack (Core_reduction.lean:484, col 2276; verbatim
      modulo whitespace): `| (CTX, Expr e_annots (Epure (Pexpr _ _ (PEval
      cval)))) => match th_st.stack0 with … | Stack_cons2 parent_proc_opt
      caller_ctx sk' => … /- reduction: RETURN -/ Step_tau2 "end of
      procedure" tsk (match th_st.env with | [] => failwithI "end of proc,
      found an empty Core_run env" | _ :: env' => { { { { th_st with
      current_proc_opt := parent_proc_opt } with env := env' } with stack0
      := sk' } with arena := apply_ctx caller_ctx (Expr e_annots (Epure
      (mk_value_pe cval))) })`. Core has no return statement: the callee's
      arena reducing to a BARE value at `Stack_cons2` IS the return. The
      value is plugged into the caller's SAVED context (`apply_ctx
      caller_ctx`, the context `Step.call` captured), the env stack pops
      one frame (the callee's `procEnv`), the current procedure is
      restored from the frame, `exec_loc` is NOT popped; memory and run
      state untouched (a `Step_tau2`; `tsk` — `TSK_Return` when
      `file1.funinfo` has the procedure, `TSK_Misc` otherwise — reaches
      only the driver's trace). At `Stack_empty` the value arm is
      PROGRAM-DONE (the value protocol, `κ = []`). The empty-env
      `failwithI` PANIC channel is excluded by the cons-shaped env
      premise (the WF-shape discipline, header note 1: the callee's frame
      is on the stack whenever the call stack is non-empty). -/
  | ret {v : value} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
      {p : Option sym} {ctx : context} {κ : List (Option sym × context)}
      {q : Option sym} {ℓ : exec_location} {σ : Mem} :
      Step M (Expr [] (Epure (Pexpr [] () (PEval v))), ev0 :: evs, ⟨(p, ctx) :: κ, q, ℓ⟩, σ)
           (apply_ctx ctx (Expr [] (Epure (Pexpr [] () (PEval v)))), evs, ⟨κ, p, ℓ⟩, σ)
  /-- REMOVE-ANNOT at a NON-EMPTY call stack (calls arc C2). Mirrors
      step_ctx's second arm (Core_reduction.lean:484, col ≈2700): `| (CTX,
      Expr _ (Eannot _ (expr'@(Expr _ (Epure (Pexpr _ _ (PEval _))))))) =>
      Step_tau2 "CTX, Eannot(value)" TSK_Misc { th_st with arena := expr'
      }` — the one-layer annotation of a value is tau'd off, at ANY stack
      (the arm precedes the general arm and does not read `stack0`). At
      `κ = []` the annotated value is a TERMINAL for the mirror (`toValRt`,
      the D1 value protocol; the shipped round is `shipped_remove_annot`,
      Round.lean) and no rule fires; at `κ ≠ []` it is NOT a terminal (a
      value under `Stack_cons2` is on its way to RETURN), so the round
      must be a mirror step: this one. The control is unchanged; the
      bare value then takes `Step.ret`. -/
  | ret_annot {ds : List dyn_annotation} {v : value} {ρ : EnvStack}
      {pc : Option sym × context} {κ : List (Option sym × context)}
      {q : Option sym} {ℓ : exec_location} {σ : Mem} :
      Step M (Expr [] (Eannot ds (Expr [] (Epure (Pexpr [] () (PEval v))))), ρ,
              ⟨pc :: κ, q, ℓ⟩, σ)
           (Expr [] (Epure (Pexpr [] () (PEval v))), ρ, ⟨pc :: κ, q, ℓ⟩, σ)

/-! ## Basic metatheory of Step (inversions the logic needs) -/

/-! ### Canonical-operand instances of the action rules

The evaluated-operand premises discharge by `rfl` at the canonical
`mk_value_pe` shapes; these instances restate the pre-S1 rule forms
so the certification layer and the small-axiom proofs apply them
directly. -/

theorem Step.store_canonical {M : MachineCtx} {a : List annot}
    {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {lk : Bool} {ty : ctype}
    {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
    {mv : CerbMem.MemValue} {fp : CerbMem.Footprint}
    {ρ : EnvStack} {ctl : Ctl} {σ σ' : Mem}
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv = some mv)
    (hmem : applyMemM (CerbMem.storeM M.tagDefs loc ty lk pv mv) σ = some (fp, σ')) :
    Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Store0 lk (Pexpr [] () (PEval (Vctype ty)))
                       (Pexpr [] () (PEval (Vobject (OVpointer pv))))
                       (Pexpr [] () (PEval cv)) mo)))), ρ, ctl, σ)
         (Expr [] (Eannot [DA_pos [] fp]
            (Expr [] (Epure (Pexpr [] () (PEval Vunit))))), ρ, ctl, σ') :=
  Step.store rfl rfl rfl hmv hmem

theorem Step.load_canonical {M : MachineCtx} {a : List annot}
    {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {ty : ctype} {pv : CerbMem.PointerValue}
    {mo : memory_order} {mval : CerbMem.MemValue} {fp : CerbMem.Footprint}
    {ρ : EnvStack} {ctl : Ctl} {σ σ' : Mem}
    (hmem : applyMemM (CerbMem.loadM M.tagDefs loc ty pv) σ = some ((fp, mval), σ')) :
    Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Load0 (Pexpr [] () (PEval (Vctype ty)))
                   (Pexpr [] () (PEval (Vobject (OVpointer pv)))) mo)))), ρ, ctl, σ)
         (Expr [] (Eannot [DA_pos [] fp]
            (Expr [] (Epure (Pexpr [] () (PEval
              (valueFromMemValue mval).2))))), ρ, ctl, σ') :=
  Step.load rfl rfl hmem

theorem Step.create_canonical {M : MachineCtx} {a : List annot}
    {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {align : CerbMem.IntegerValue} {ty : ctype}
    {pref : prefix0} {pv : CerbMem.PointerValue} {ρ : EnvStack} {ctl : Ctl} {σ σ' : Mem}
    (hmem : applyMemM (CerbMem.allocateObject M.tagDefs 0 pref align ty none none) σ =
      some (pv, σ')) :
    Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Create (Pexpr [] () (PEval (Vobject (OVinteger align))))
                    (Pexpr [] () (PEval (Vctype ty))) pref)))), ρ, ctl, σ)
         (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer pv))))), ρ, ctl, σ') :=
  Step.create rfl rfl hmem

theorem Step.kill_canonical {M : MachineCtx} {a : List annot}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {kind : kill_kind}
    {pv : CerbMem.PointerValue} {ρ : EnvStack} {ctl : Ctl} {σ σ' : Mem}
    (hmem : applyMemM (CerbMem.killM loc (is_dynamic kind) pv) σ = some ((), σ')) :
    Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Kill kind (Pexpr [] () (PEval (Vobject (OVpointer pv)))))))), ρ, ctl, σ)
         (Expr [] (Epure (Pexpr [] () (PEval Vunit))), ρ, ctl, σ') :=
  Step.kill rfl hmem

theorem Step.alloc_canonical {M : MachineCtx} {a : List annot}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {align size : CerbMem.IntegerValue} {pref : prefix0}
    {pv : CerbMem.PointerValue} {ρ : EnvStack} {ctl : Ctl} {σ σ' : Mem}
    (hmem : applyMemM (CerbMem.allocateRegion 0 pref align size) σ = some (pv, σ')) :
    Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Alloc0 (Pexpr [] () (PEval (Vobject (OVinteger align))))
                    (Pexpr [] () (PEval (Vobject (OVinteger size)))) pref)))), ρ, ctl, σ)
         (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer pv))))), ρ, ctl, σ') :=
  Step.alloc rfl rfl hmem

/-- S3 RETIREMENT NOTE: phase-1's `Step.env_invariant(')` (no rule
    writes the env) is RETIRED as pre-declared (phase-1 notes §2
    item 6) — `Step.run` and `Step.save` rebind the environment. Its
    survivor: `Step.env_cons` (cons-shapedness is preserved — what
    the sequencing proofs actually need at this stratum). C2: the
    call PUSHES a frame and the return POPS one, so the survivor holds
    at CONTROL-PRESERVING steps (`hctl`); the call/return frame
    discipline is `Step.ctl_cases`. -/
theorem Step.env_cons' {M : MachineCtx} {c c' : Config}
    (h : Step M c c') (hctl : c'.2.2.1 = c.2.2.1) :
    ∀ ev0 evs, c.2.1 = ev0 :: evs → ∃ ev0', c'.2.1 = ev0' :: evs := by
  induction h with
  | store h1 h2 h3 hmv hmem => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | load h1 h2 hmem => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | create h1 h2 hmem => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | kill h1 hmem => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | sseq_pure => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | sseq_annot => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | wseq_pure => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | wseq_annot => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | sseq_spec_pure =>
    intro ev0 evs hin
    obtain ⟨rfl, rfl⟩ := List.cons.inj hin
    exact ⟨_, update_env_cons ..⟩
  | sseq_spec_annot =>
    intro ev0 evs hin
    obtain ⟨rfl, rfl⟩ := List.cons.inj hin
    exact ⟨_, update_env_cons ..⟩
  | pure_eval hnv hv => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | load_eval hnv2 hv2 => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | sseq_ctx hnj hnv hs ih => exact ih hctl
  | wseq_ctx hnj hnv hs ih => exact ih hctl
  | annot_ctx hnj hg hs ih => exact ih hctl
  | annot_merge => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | run hj hl hvs =>
    intro ev0 evs hin
    obtain ⟨rfl, rfl⟩ := List.cons.inj hin
    exact bindArgs_cons _ _ _ _
  | save hvals =>
    intro ev0 evs hin
    obtain ⟨rfl, rfl⟩ := List.cons.inj hin
    exact bindSaveParams_cons _ _ _ _
  | save_eval hnv hvals => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | if_true hg => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | if_false hg => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | case_value hv hsel => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | sseq_sym_pure =>
    intro ev0 evs hin
    obtain ⟨rfl, rfl⟩ := List.cons.inj hin
    exact ⟨_, update_env_cons ..⟩
  | memop_ptreq h1 h2 hmem => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | memop_eval hnv hv1 hv2 => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | store_eval hnv hv2 hv3 => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | kill_eval hnv hv => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | alloc h1 h2 hmem => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | alloc_eval hnv hv1 hv2 => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | call hc hvs hf hlen =>
    exact absurd (congrArg Ctl.κ hctl) (by simp)
  | ret =>
    exact absurd (congrArg Ctl.κ hctl) (by simp)
  | ret_annot => exact fun ev0 evs hin => ⟨ev0, hin⟩

theorem Step.env_cons {M : MachineCtx} {e : CoreExpr} {ev0 : Fmap sym value}
    {evs : List (Fmap sym value)} {ctl : Ctl} {σ : Mem}
    {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    (h : Step M (e, ev0 :: evs, ctl, σ) (e', ρ', ctl, σ')) :
    ∃ ev0', ρ' = ev0' :: evs :=
  h.env_cons' rfl ev0 evs rfl

/-- THE CONTROL IS WRITTEN BY EXACTLY TWO RULES (calls arc C2): every
    step either threads the configuration's `Ctl` unchanged, or is THE
    CALL (the control grows by the captured frame `(ctl.proc, ctx)`, the
    callee becomes the current procedure, the execution location is
    pushed) or THE RETURN (the top frame pops, the caller's procedure is
    restored). C1's `Step.ctl_eq` (every step preserves the control) is
    now the first disjunct under the two guards `Step.ctl_eq`. -/
theorem Step.ctl_cases {M : MachineCtx} {e e' : CoreExpr} {ρ ρ' : EnvStack}
    {ctl ctl' : Ctl} {σ σ' : Mem}
    (h : Step M (e, ρ, ctl, σ) (e', ρ', ctl', σ')) :
    ctl' = ctl ∨
    (∃ ctx f pes params body vs, callRedex? e = some (ctx, f, pes) ∧
      evalPexprs M.tagDefs M.extern ρ pes = some vs ∧
      lookupProc M.file M.extern f = some (params, body) ∧ params.length = vs.length ∧
      e' = body ∧ ρ' = procEnv params vs :: ρ ∧
      ctl' = ⟨(ctl.proc, ctx) :: ctl.κ, some f, push_exec_loc f M.currentLoc ctl.execLoc⟩ ∧
      σ' = σ) ∨
    (∃ v ev0 evs p ctx κ q ℓ, e = Expr [] (Epure (Pexpr [] () (PEval v))) ∧
      ρ = ev0 :: evs ∧ ctl = ⟨(p, ctx) :: κ, q, ℓ⟩ ∧
      e' = apply_ctx ctx (Expr [] (Epure (Pexpr [] () (PEval v)))) ∧ ρ' = evs ∧
      ctl' = ⟨κ, p, ℓ⟩ ∧ σ' = σ) := by
  cases h
  all_goals first
    | exact .inl rfl
    | exact .inr (.inl ⟨_, _, _, _, _, _, ‹callRedex? _ = some _›,
        ‹evalPexprs _ _ _ _ = some _›, ‹lookupProc _ _ _ = some _›,
        ‹List.length _ = List.length _›, rfl, rfl, rfl, rfl⟩)
    | exact .inr (.inr ⟨_, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- The control is preserved at every configuration that is neither a
    call redex (in context) nor a value: the two guards are exactly the
    sources of `Step.call` and `Step.ret`/`Step.ret_annot`. -/
theorem Step.ctl_eq {M : MachineCtx} {e e' : CoreExpr} {ρ ρ' : EnvStack}
    {ctl ctl' : Ctl} {σ σ' : Mem}
    (h : Step M (e, ρ, ctl, σ) (e', ρ', ctl', σ'))
    (hc : callRedex? e = none) (hv : toVal e = none) : ctl' = ctl := by
  rcases h.ctl_cases with heq | ⟨ctx, f, pes, _, _, _, hc', -⟩ |
      ⟨v, _, _, _, _, _, _, _, rfl, -⟩
  · exact heq
  · rw [hc'] at hc; cases hc
  · rw [show toVal (Expr ([] : List _root_.annot) (Epure (Pexpr [] () (PEval v)))) =
      some (.pure v) from rfl] at hv
    cases hv

theorem Step.ctl_eq' {M : MachineCtx} {c c' : Config} (h : Step M c c')
    (hc : callRedex? c.1 = none) (hv : toVal c.1 = none) : c'.2.2.1 = c.2.2.1 := by
  obtain ⟨e, ρ, ctl, σ⟩ := c
  obtain ⟨e', ρ', ctl', σ'⟩ := c'
  exact h.ctl_eq hc hv

/-- A control-preserving step's successor control IS the source
    control (`Step.ctl_eq`), restated on the step itself so that
    congruence rules apply to a step whose successor was produced by
    the Language interface (where the control component is an opaque
    projection). -/
theorem Step.retag {M : MachineCtx} {e e' : CoreExpr} {ρ ρ' : EnvStack}
    {ctl ctl' : Ctl} {σ σ' : Mem}
    (h : Step M (e, ρ, ctl, σ) (e', ρ', ctl', σ'))
    (hc : callRedex? e = none) (hv : toVal e = none) :
    Step M (e, ρ, ctl, σ) (e', ρ', ctl, σ') := by
  obtain rfl := h.ctl_eq hc hv
  exact h

/-- Inversion at a call redex IN CONTEXT: the step is THE CALL, its
    successor determined by the file lookup, the argument values and the
    captured context — the successor does not depend on how the redex
    was reached beyond `ctx`. By induction on the step: a congruence
    rule cannot frame a call of its sub-expression (the pushed control
    differs from the threaded one), so the only rule at a configuration
    with a call redex is `Step.call`. -/
theorem Step.call_inv' {M : MachineCtx} {c : Config}
    {out : Config} (h : Step M c out) :
    ∀ {ctx : context} {f : sym} {pes : List (generic_pexpr Unit sym)},
      callRedex? c.1 = some (ctx, f, pes) →
      ∃ params body vs, evalPexprs M.tagDefs M.extern c.2.1 pes = some vs ∧
        lookupProc M.file M.extern f = some (params, body) ∧ params.length = vs.length ∧
        out = (body, procEnv params vs :: c.2.1,
          ⟨(c.2.2.1.proc, ctx) :: c.2.2.1.κ, some f,
            push_exec_loc f M.currentLoc c.2.2.1.execLoc⟩, c.2.2.2) := by
  induction h with
  | call hc' hvs hf hlen =>
    intro ctx f pes hc
    rw [hc'] at hc
    obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
      have := Option.some.inj hc
      exact ⟨congrArg Prod.fst this, congrArg (fun q => q.2.1) this,
        congrArg (fun q => q.2.2) this⟩
    exact ⟨_, _, _, hvs, hf, hlen, rfl⟩
  | ret => intro ctx f pes hc; simp at hc
  | ret_annot => intro ctx f pes hc; simp [callRedex?, annotRooted] at hc
  | sseq_ctx hnj hnv hs ih =>
    intro ctx f pes hc
    rw [callRedex?_sseq, Option.map_eq_some_iff] at hc
    obtain ⟨⟨ctx1, f1, pes1⟩, hc1, hq⟩ := hc
    obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
      exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq,
        congrArg (fun q => q.2.2) hq⟩
    obtain ⟨_, _, _, -, -, -, hout⟩ := ih hc1
    exact absurd (congrArg (fun c : Config => c.2.2.1.κ) hout) (by simp)
  | wseq_ctx hnj hnv hs ih =>
    intro ctx f pes hc
    rw [callRedex?_wseq, Option.map_eq_some_iff] at hc
    obtain ⟨⟨ctx1, f1, pes1⟩, hc1, hq⟩ := hc
    obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
      exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq,
        congrArg (fun q => q.2.2) hq⟩
    obtain ⟨_, _, _, -, -, -, hout⟩ := ih hc1
    exact absurd (congrArg (fun c : Config => c.2.2.1.κ) hout) (by simp)
  | annot_ctx hnj hg hs ih =>
    intro ctx f pes hc
    rw [callRedex?_annot_of_not_root _ _ hg, Option.map_eq_some_iff] at hc
    obtain ⟨⟨ctx1, f1, pes1⟩, hc1, hq⟩ := hc
    obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
      exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq,
        congrArg (fun q => q.2.2) hq⟩
    obtain ⟨_, _, _, -, -, -, hout⟩ := ih hc1
    exact absurd (congrArg (fun c : Config => c.2.2.1.κ) hout) (by simp)
  | annot_merge => intro ctx f pes hc; simp [callRedex?, annotRooted] at hc
  | sseq_pure => intro ctx f pes hc; simp at hc
  | sseq_annot => intro ctx f pes hc; simp at hc
  | wseq_pure => intro ctx f pes hc; simp at hc
  | wseq_annot => intro ctx f pes hc; simp at hc
  | sseq_spec_pure => intro ctx f pes hc; simp at hc
  | sseq_spec_annot => intro ctx f pes hc; simp at hc
  | sseq_sym_pure => intro ctx f pes hc; simp at hc
  | store h1 h2 h3 hmv hmem => intro ctx f pes hc; simp at hc
  | load h1 h2 hmem => intro ctx f pes hc; simp at hc
  | create h1 h2 hmem => intro ctx f pes hc; simp at hc
  | kill h1 hmem => intro ctx f pes hc; simp at hc
  | alloc h1 h2 hmem => intro ctx f pes hc; simp at hc
  | pure_eval hnv hv => intro ctx f pes hc; simp at hc
  | load_eval hnv2 hv2 => intro ctx f pes hc; simp at hc
  | run hj hl hvs => intro ctx f pes hc; rw [callRedex?_none_of_jumpRedex?_some hj] at hc; cases hc
  | save hvals => intro ctx f pes hc; simp at hc
  | save_eval hnv hvals => intro ctx f pes hc; simp at hc
  | if_true hg => intro ctx f pes hc; simp at hc
  | if_false hg => intro ctx f pes hc; simp at hc
  | case_value hv hsel => intro ctx f pes hc; simp at hc
  | memop_ptreq h1 h2 hmem => intro ctx f pes hc; simp at hc
  | memop_eval hnv hv1 hv2 => intro ctx f pes hc; simp at hc
  | store_eval hnv hv2 hv3 => intro ctx f pes hc; simp at hc
  | kill_eval hnv hv => intro ctx f pes hc; simp at hc
  | alloc_eval hnv hv1 hv2 => intro ctx f pes hc; simp at hc

theorem Step.call_inv {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config} (h : Step M (e, ρ, ctl, σ) out)
    {ctx : context} {f : sym} {pes : List (generic_pexpr Unit sym)}
    (hc : callRedex? e = some (ctx, f, pes)) :
    ∃ params body vs, evalPexprs M.tagDefs M.extern ρ pes = some vs ∧
      lookupProc M.file M.extern f = some (params, body) ∧ params.length = vs.length ∧
      out = (body, procEnv params vs :: ρ,
        ⟨(ctl.proc, ctx) :: ctl.κ, some f, push_exec_loc f M.currentLoc ctl.execLoc⟩, σ) :=
  h.call_inv' hc

/-- A call step is never control-preserving (the frame is pushed). -/
theorem Step.call_ne_same_ctl {M : MachineCtx} {e e' : CoreExpr} {ρ ρ' : EnvStack}
    {ctl : Ctl} {σ σ' : Mem} {ctx : context} {f : sym}
    {pes : List (generic_pexpr Unit sym)}
    (hc : callRedex? e = some (ctx, f, pes))
    (h : Step M (e, ρ, ctl, σ) (e', ρ', ctl, σ')) : False := by
  obtain ⟨_, _, _, -, -, -, hout⟩ := h.call_inv hc
  exact absurd (congrArg (fun c : Config => c.2.2.1.κ) hout) (by simp)

/-- Reducibility at a call redex in context whose lookup, arity and
    arguments succeed. -/
theorem Step.call_of_callRedex {M : MachineCtx} {e : CoreExpr} {ctx : context} {f : sym}
    {pes : List (generic_pexpr Unit sym)} {params : List (sym × core_base_type)}
    {body : CoreExpr} {vs : List value} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    (hc : callRedex? e = some (ctx, f, pes))
    (hvs : evalPexprs M.tagDefs M.extern ρ pes = some vs)
    (hf : lookupProc M.file M.extern f = some (params, body))
    (hlen : params.length = vs.length) :
    Step M (e, ρ, ctl, σ)
      (body, procEnv params vs :: ρ,
       ⟨(ctl.proc, ctx) :: ctl.κ, some f, push_exec_loc f M.currentLoc ctl.execLoc⟩, σ) :=
  Step.call hc hvs hf hlen

/-- Values do not step AT THE EMPTY CALL STACK (the Language interface's
    `val_stuck`; C2: at a non-empty stack a value is the RETURN redex,
    `Step.ret`/`Step.ret_annot`). Engine analogue: is_irreducible
    short-circuits both get_ctx and one_step0 (Core_reduction.lean:293,
    353,375), and the value arm at `Stack_empty` is PROGRAM-DONE. -/
theorem Step.val_elim {M : MachineCtx} {w : SpikeVal} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config} (hκ : ctl.κ = [])
    (h : Step M (ofVal w, ρ, ctl, σ) out) : False := by
  obtain ⟨κ, p, ℓ⟩ := ctl
  simp only at hκ
  subst hκ
  cases w with
  | pure v =>
    cases h with
    | run hj hl hvs => simp [ofVal] at hj
    | pure_eval hnv hv => rw [valueFromPexpr_val] at hnv; cases hnv
    | call hc hvs hf hlen => simp [ofVal] at hc
  | annot ds v =>
    cases h with
    | annot_ctx hnj hg hs =>
      cases hs with
      | run hj hl hvs => simp at hj
      | pure_eval hnv hv => rw [valueFromPexpr_val] at hnv; cases hnv
    | run hj hl hvs => simp [ofVal, jumpRedex?, annotRooted] at hj
    | call hc hvs hf hlen => simp [ofVal, callRedex?, annotRooted] at hc

/-- A BARE value never takes a control-preserving step (its only rule,
    `Step.ret`, pops the call stack). -/
theorem Step.pure_val_elim {M : MachineCtx} {v : value} {ρ : EnvStack} {ctl ctl' : Ctl}
    {σ : Mem} {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    (h : Step M (Expr [] (Epure (Pexpr [] () (PEval v))), ρ, ctl, σ) (e', ρ', ctl', σ'))
    (hctl : ctl' = ctl) : False := by
  cases h with
  | run hj hl hvs => simp at hj
  | pure_eval hnv hv => rw [valueFromPexpr_val] at hnv; cases hnv
  | call hc hvs hf hlen => simp at hc
  | ret => exact absurd (congrArg Ctl.κ hctl) (by simp)

/-- The ANNOTATED value's only control-preserving step is REMOVE-ANNOT
    at a non-empty call stack. -/
theorem Step.annot_val_inv {M : MachineCtx} {ds : List dyn_annotation} {v : value}
    {ρ : EnvStack} {ctl ctl' : Ctl} {σ : Mem} {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    (h : Step M (Expr [] (Eannot ds (Expr [] (Epure (Pexpr [] () (PEval v))))), ρ, ctl, σ)
      (e', ρ', ctl', σ')) (hctl : ctl' = ctl) :
    e' = Expr [] (Epure (Pexpr [] () (PEval v))) ∧ ρ' = ρ ∧ σ' = σ ∧
      ∃ pc κ, ctl.κ = pc :: κ := by
  cases h with
  | annot_ctx hnj hg hs => exact (Step.pure_val_elim hs rfl).elim
  | run hj hl hvs => simp [jumpRedex?, annotRooted] at hj
  | call hc hvs hf hlen => simp [callRedex?, annotRooted] at hc
  | ret_annot => exact ⟨rfl, rfl, rfl, _, _, rfl⟩

theorem Step.toVal_none {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config} (hκ : ctl.κ = [])
    (h : Step M (e, ρ, ctl, σ) out) : toVal e = none := by
  cases hv : toVal e with
  | none => rfl
  | some w => exact absurd (ofVal_of_toVal hv ▸ h) (fun h => h.val_elim hκ)

/-- A stepping tuple is not a Language value: at the empty stack because
    values do not step there, at a non-empty stack by `toValRt`'s
    definition (the `val_stuck` law, Lang.lean). -/
theorem Step.toValRt_none {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config} (h : Step M (e, ρ, ctl, σ) out) :
    toValRt ⟨e, ρ, ctl, M⟩ = none := by
  obtain ⟨κ, p, ℓ⟩ := ctl
  cases κ with
  | nil => rw [toValRt_mk, h.toVal_none rfl]; rfl
  | cons pc κ => rfl

/-- Inversion at a store redex (canonical operand instance — the
    certified cone's shape): the step is unique and fully determined
    by the memM computation; the env is returned verbatim. -/
theorem Step.store_inv {M : MachineCtx} {a : List annot} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {lk : Bool} {ty : ctype}
    {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (h : Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Store0 lk (Pexpr [] () (PEval (Vctype ty)))
                       (Pexpr [] () (PEval (Vobject (OVpointer pv))))
                       (Pexpr [] () (PEval cv)) mo)))), ρ, ctl, σ) out) :
    ∃ mv fp σ',
      memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv = some mv ∧
      applyMemM (CerbMem.storeM M.tagDefs loc ty lk pv mv) σ = some (fp, σ') ∧
      out = (Expr [] (Eannot [DA_pos [] fp]
              (Expr [] (Epure (Pexpr [] () (PEval Vunit))))), ρ, ctl, σ') := by
  cases h with
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | store_eval hnv hv2 hv3 =>
    rw [valueFromPexprs_pair, valueFromPexpr_val, valueFromPexpr_val] at hnv
    cases hnv
  | store h1 h2 h3 hmv hmem =>
    rw [valueFromPexpr_val] at h1 h2 h3
    injection h1 with h1; injection h1 with h1
    injection h2 with h2; injection h2 with h2; injection h2 with h2
    injection h3 with h3
    subst h1 h2 h3
    exact ⟨_, _, _, hmv, hmem, rfl⟩

/-- Inversion at a load redex (canonical operand instance). -/
theorem Step.load_inv {M : MachineCtx} {a : List annot} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {ty : ctype} {pv : CerbMem.PointerValue}
    {mo : memory_order} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config}
    (h : Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Load0 (Pexpr [] () (PEval (Vctype ty)))
                   (Pexpr [] () (PEval (Vobject (OVpointer pv)))) mo)))), ρ, ctl, σ)
          out) :
    ∃ fp mval σ',
      applyMemM (CerbMem.loadM M.tagDefs loc ty pv) σ = some ((fp, mval), σ') ∧
      out = (Expr [] (Eannot [DA_pos [] fp]
              (Expr [] (Epure (Pexpr [] () (PEval
                (valueFromMemValue mval).2))))), ρ, ctl, σ') := by
  cases h with
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | load_eval hnv2 hv2 => rw [valueFromPexpr_val] at hnv2; cases hnv2
  | load h1 h2 hmem =>
    rw [valueFromPexpr_val] at h1 h2
    injection h1 with h1; injection h1 with h1
    injection h2 with h2; injection h2 with h2; injection h2 with h2
    subst h1 h2
    exact ⟨_, _, _, hmem, rfl⟩

/-- Inversion at a create redex (canonical operand instance). -/
theorem Step.create_inv {M : MachineCtx} {a : List annot} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {align : CerbMem.IntegerValue} {ty : ctype}
    {pref : prefix0} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config}
    (h : Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Create (Pexpr [] () (PEval (Vobject (OVinteger align))))
                    (Pexpr [] () (PEval (Vctype ty))) pref)))), ρ, ctl, σ) out) :
    ∃ pv σ',
      applyMemM (CerbMem.allocateObject M.tagDefs 0 pref align ty none none) σ =
        some (pv, σ') ∧
      out = (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer pv))))), ρ, ctl, σ') := by
  cases h with
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | create h1 h2 hmem =>
    rw [valueFromPexpr_val] at h1 h2
    injection h1 with h1; injection h1 with h1; injection h1 with h1
    injection h2 with h2; injection h2 with h2
    subst h1 h2
    exact ⟨_, _, hmem, rfl⟩

/-- Inversion at a kill redex (canonical operand instance, kill/free
    arc K2): the step is unique and fully determined by `killM`; the
    env is returned verbatim. -/
theorem Step.kill_inv {M : MachineCtx} {a : List annot} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {kind : kill_kind} {pv : CerbMem.PointerValue}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (h : Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Kill kind (Pexpr [] () (PEval (Vobject (OVpointer pv)))))))), ρ, ctl, σ) out) :
    ∃ σ',
      applyMemM (CerbMem.killM loc (is_dynamic kind) pv) σ = some ((), σ') ∧
      out = (Expr [] (Epure (Pexpr [] () (PEval Vunit))), ρ, ctl, σ') := by
  cases h with
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | kill_eval hnv hv => rw [valueFromPexpr_val] at hnv; cases hnv
  | kill h1 hmem =>
    rw [valueFromPexpr_val] at h1
    injection h1 with h1; injection h1 with h1; injection h1 with h1
    subst h1
    exact ⟨_, hmem, rfl⟩

/-- Inversion at a positive kill whose pointer operand is NOT a value:
    the ACTION_EVAL step to a POINTER value. -/
theorem Step.kill_op_inv {M : MachineCtx} {a : List annot}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {kind : kill_kind}
    {pe : generic_pexpr Unit sym}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (hnv : valueFromPexpr pe = none)
    (h : Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Kill kind pe)))), ρ, ctl, σ) out) :
    ∃ pv, evalPexpr M.tagDefs M.extern ρ pe = some (Vobject (OVpointer pv)) ∧
      out = (Expr a (Eaction (Paction polarity.Pos (Action loc ann
        (Kill kind (Pexpr [] () (PEval (Vobject (OVpointer pv)))))))), ρ, ctl, σ) := by
  cases h with
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | kill h1 hmem => rw [hnv] at h1; cases h1
  | kill_eval hnv' hv => exact ⟨_, hv, rfl⟩

/-- Inversion at an alloc redex (canonical operand instance, kill/free
    arc K3): the step is unique and fully determined by
    `allocateRegion`; the env is returned verbatim. -/
theorem Step.alloc_inv {M : MachineCtx} {a : List annot} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {align size : CerbMem.IntegerValue}
    {pref : prefix0} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config}
    (h : Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Alloc0 (Pexpr [] () (PEval (Vobject (OVinteger align))))
                    (Pexpr [] () (PEval (Vobject (OVinteger size)))) pref)))), ρ, ctl, σ) out) :
    ∃ pv σ',
      applyMemM (CerbMem.allocateRegion 0 pref align size) σ = some (pv, σ') ∧
      out = (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer pv))))), ρ, ctl, σ') := by
  cases h with
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | alloc_eval hnv hv1 hv2 =>
    rw [valueFromPexprs_pair, valueFromPexpr_val, valueFromPexpr_val] at hnv
    cases hnv
  | alloc h1 h2 hmem =>
    rw [valueFromPexpr_val] at h1 h2
    injection h1 with h1; injection h1 with h1; injection h1 with h1
    injection h2 with h2; injection h2 with h2; injection h2 with h2
    subst h1 h2
    exact ⟨_, _, hmem, rfl⟩

/-- Inversion at a positive alloc whose operands are NOT all values:
    the ACTION_EVAL step to INTEGER values. -/
theorem Step.alloc_op_inv {M : MachineCtx} {a : List annot}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (h : Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Alloc0 pe1 pe2 pref)))), ρ, ctl, σ) out) :
    ∃ align size, evalPexpr M.tagDefs M.extern ρ pe1 = some (Vobject (OVinteger align)) ∧
      evalPexpr M.tagDefs M.extern ρ pe2 = some (Vobject (OVinteger size)) ∧
      out = (Expr a (Eaction (Paction polarity.Pos (Action loc ann
        (Alloc0 (Pexpr [] () (PEval (Vobject (OVinteger align))))
                (Pexpr [] () (PEval (Vobject (OVinteger size)))) pref)))), ρ, ctl, σ) := by
  cases h with
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | alloc h1 h2 hmem => rw [valueFromPexprs_pair, h1, h2] at hnv; cases hnv
  | alloc_eval hnv' hv1 hv2 => exact ⟨_, _, hv1, hv2, rfl⟩

/-! ### THE JUMP-REDEX INVERSION PAIR (probe Toy.lean
`step_jump_inv`/`step_of_jumpRedex`, now on Core — the semantic
cash-in of context-independence: at a jump redex EVERY step is THE
jump and its successor does not depend on the decomposition; the
congruence guards make this a one-level `cases`). -/

theorem Step.jump_inv {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config} {l : sym}
    {pes : List (generic_pexpr Unit sym)}
    (hj : jumpRedex? e = some (l, pes))
    (h : Step M (e, ρ, ctl, σ) out) :
    ∃ params cont vs ev0 evs, ρ = ev0 :: evs ∧
      lookupLabel (M.labelsAt ctl.proc) l = some (params, cont) ∧
      evalPexprs M.tagDefs M.extern ρ pes = some vs ∧
      out = (cont, bindArgs params vs ρ, ctl, σ) := by
  cases h with
  | run hj' hl hvs =>
    obtain ⟨rfl, rfl⟩ : l = _ ∧ pes = _ := by
      have := hj.symm.trans hj'
      exact ⟨(Prod.mk.injEq _ _ _ _ ▸ Option.some.inj this).1,
        (Prod.mk.injEq _ _ _ _ ▸ Option.some.inj this).2⟩
    exact ⟨_, _, _, _, _, rfl, hl, hvs, rfl⟩
  | store h1 h2 h3 hmv hmem => simp at hj
  | load h1 h2 hmem => simp at hj
  | create h1 h2 hmem => simp at hj
  | kill h1 hmem => simp at hj
  | kill_eval hnv hv => simp at hj
  | sseq_pure => rw [jumpRedex?_sseq, jumpRedex?_ofVal] at hj; cases hj
  | sseq_annot => rw [jumpRedex?_sseq, jumpRedex?_ofVal] at hj; cases hj
  | wseq_pure => rw [jumpRedex?_wseq, jumpRedex?_ofVal] at hj; cases hj
  | wseq_annot => rw [jumpRedex?_wseq, jumpRedex?_ofVal] at hj; cases hj
  | sseq_spec_pure => rw [jumpRedex?_sseq, jumpRedex?_ofVal] at hj; cases hj
  | sseq_spec_annot => rw [jumpRedex?_sseq, jumpRedex?_ofVal] at hj; cases hj
  | pure_eval hnv hv => simp at hj
  | load_eval hnv2 hv2 => simp at hj
  | sseq_ctx hnj hs => rw [jumpRedex?_sseq, hnj] at hj; cases hj
  | wseq_ctx hnj hs => rw [jumpRedex?_wseq, hnj] at hj; cases hj
  | annot_ctx hnj hg hs => rw [jumpRedex?_annot_of_not_root _ _ hg, hnj] at hj; cases hj
  | annot_merge =>
    rw [jumpRedex?_annot_of_root _ _ (by rfl)] at hj; cases hj
  | save hvals => simp [jumpRedex?] at hj
  | save_eval hnv hvals => simp [jumpRedex?] at hj
  | if_true hg => simp [jumpRedex?] at hj
  | if_false hg => simp [jumpRedex?] at hj
  | case_value hv hsel => simp [jumpRedex?] at hj
  | sseq_sym_pure => rw [jumpRedex?_sseq, jumpRedex?_ofVal] at hj; cases hj
  | memop_ptreq h1 h2 hmem => simp at hj
  | memop_eval hnv hv1 hv2 => simp at hj
  | store_eval hnv hv2 hv3 => simp at hj
  | alloc h1 h2 hmem => simp at hj
  | alloc_eval hnv hv1 hv2 => simp at hj
  | call hc hvs hf hlen => rw [callRedex?_none_of_jumpRedex?_some hj] at hc; cases hc
  | ret => simp at hj
  | ret_annot => simp [jumpRedex?, annotRooted] at hj

/-- Reducibility at a registered jump redex (the probe's
    `step_of_jumpRedex`). -/
theorem Step.run_of_jumpRedex {M : MachineCtx} {e : CoreExpr} {l : sym}
    {pes : List (generic_pexpr Unit sym)}
    {params : List (sym × core_base_type)} {cont : CoreExpr} {vs : List value}
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {ctl : Ctl} {σ : Mem}
    (hj : jumpRedex? e = some (l, pes))
    (hl : lookupLabel (M.labelsAt ctl.proc) l = some (params, cont))
    (hvs : evalPexprs M.tagDefs M.extern (ev0 :: evs) pes = some vs) :
    Step M (e, ev0 :: evs, ctl, σ) (cont, bindArgs params vs (ev0 :: evs), ctl, σ) :=
  Step.run hj hl hvs

/-- A CALL step of `e` seen from a node whose frame is `fr` (calls arc
    C2): the redex `callRedex? e = some (ctx, f, pes)` under the frame,
    the arguments evaluated at the CURRENT env, the callee found with
    the right arity, and the successor at the pushed control — the
    captured context is the frame applied to the redex's own context
    (`Csseq a pat · e2` at an `Esseq` node, `Cwseq …`, `Cannot a ds ·`),
    exactly get_ctx's outside-in construction. One disjunct of each
    frame inversion below; `fr := id` at the root. -/
def Step.CallOf (M : MachineCtx) (e : CoreExpr) (fr : context → context)
    (ρ : EnvStack) (ctl : Ctl) (σ : Mem) (out : Config) : Prop :=
  ∃ ctx f pes params body vs, callRedex? e = some (ctx, f, pes) ∧
    evalPexprs M.tagDefs M.extern ρ pes = some vs ∧
    lookupProc M.file M.extern f = some (params, body) ∧ params.length = vs.length ∧
    out = (body, procEnv params vs :: ρ,
      ⟨(ctl.proc, fr ctx) :: ctl.κ, some f, push_exec_loc f M.currentLoc ctl.execLoc⟩, σ)

/-- A `CallOf` successor never sits at the source control. -/
theorem Step.CallOf.ne_same_ctl {M : MachineCtx} {e : CoreExpr} {fr : context → context}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    (h : Step.CallOf M e fr ρ ctl σ (e', ρ', ctl, σ')) : False := by
  obtain ⟨_, _, _, _, _, _, -, -, -, -, hout⟩ := h
  exact absurd (congrArg (fun c : Config => c.2.2.1.κ) hout) (by simp)

/-- A `CallOf` witness names a call redex of `e`. -/
theorem Step.CallOf.callRedex?_some {M : MachineCtx} {e : CoreExpr} {fr : context → context}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (h : Step.CallOf M e fr ρ ctl σ out) :
    ∃ ctx f pes, callRedex? e = some (ctx, f, pes) := by
  obtain ⟨ctx, f, pes, _, _, _, hc, -⟩ := h
  exact ⟨ctx, f, pes, hc⟩

/-- Inversion at an Esseq node (S3 form): a frame step of a
    NON-jump-redex, non-value e1, one of the betas, THE GLOBAL JUMP
    (frame discarded — the successor is e1's own jump successor), or
    (C2) THE CALL of e1 with the `Csseq` frame CAPTURED. The frame
    case's `jumpRedex? e1 = none`/`toVal e1 = none` are the congruence
    guards surfacing; the jump disjunct is the readiness's "factor
    theorem gains one disjunct" at the Esseq node; the call disjunct is
    C2's third context discipline. -/
theorem Step.sseq_inv {M : MachineCtx} {a : List annot} {pat : pattern}
    {e1 e2 : CoreExpr}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (h : Step M (Expr a (Esseq pat e1 e2), ρ, ctl, σ) out) :
    (∃ e1' ρ' σ', jumpRedex? e1 = none ∧ toVal e1 = none ∧
        Step M (e1, ρ, ctl, σ) (e1', ρ', ctl, σ') ∧
        out = (Expr a (Esseq pat e1' e2), ρ', ctl, σ')) ∨
    (∃ pa bty v ev0 evs, pat = Pattern pa (CaseBase (none, bty)) ∧
        e1 = ofVal (.pure v) ∧ ρ = ev0 :: evs ∧ out = (e2, ρ, ctl, σ)) ∨
    (∃ pa bty ds v ev0 evs, pat = Pattern pa (CaseBase (none, bty)) ∧
        e1 = ofVal (.annot ds v) ∧ ρ = ev0 :: evs ∧
        out = (Expr [] (Eannot ds e2), ρ, ctl, σ)) ∨
    (∃ l pes params cont vs ev0 evs, jumpRedex? e1 = some (l, pes) ∧
        ρ = ev0 :: evs ∧ lookupLabel (M.labelsAt ctl.proc) l = some (params, cont) ∧
        evalPexprs M.tagDefs M.extern ρ pes = some vs ∧
        out = (cont, bindArgs params vs ρ, ctl, σ)) ∨
    (∃ pa' pb' x bty' ov ev0 evs, pat = specPat pa' pb' x bty' ∧
        e1 = ofVal (.pure (Vloaded (LVspecified ov))) ∧ ρ = ev0 :: evs ∧
        out = (e2, update_env (specPat pa' pb' x bty')
          (Vloaded (LVspecified ov)) ρ, ctl, σ)) ∨
    (∃ pa' pb' x bty' ds ov ev0 evs, pat = specPat pa' pb' x bty' ∧
        e1 = ofVal (.annot ds (Vloaded (LVspecified ov))) ∧ ρ = ev0 :: evs ∧
        out = (Expr [] (Eannot ds e2), update_env (specPat pa' pb' x bty')
          (Vloaded (LVspecified ov)) ρ, ctl, σ)) ∨
    (∃ pa' x bty' v ev0 evs, pat = symPat pa' x bty' ∧
        e1 = ofVal (.pure v) ∧ ρ = ev0 :: evs ∧
        out = (e2, update_env (symPat pa' x bty') v ρ, ctl, σ)) ∨
    Step.CallOf M e1 (fun c => Csseq a pat c e2) ρ ctl σ out := by
  cases h with
  | sseq_ctx hnj hnv hs => exact .inl ⟨_, _, _, hnj, hnv, hs, rfl⟩
  | sseq_pure => exact .inr (.inl ⟨_, _, _, _, _, rfl, rfl, rfl, rfl⟩)
  | sseq_annot => exact .inr (.inr (.inl ⟨_, _, _, _, _, _, rfl, rfl, rfl, rfl⟩))
  | run hj hl hvs =>
    rw [jumpRedex?_sseq] at hj
    exact .inr (.inr (.inr (.inl ⟨_, _, _, _, _, _, _, hj, rfl, hl, hvs, rfl⟩)))
  | sseq_spec_pure =>
    exact .inr (.inr (.inr (.inr (.inl
      ⟨_, _, _, _, _, _, _, rfl, rfl, rfl, rfl⟩))))
  | sseq_spec_annot =>
    exact .inr (.inr (.inr (.inr (.inr (.inl
      ⟨_, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl⟩)))))
  | sseq_sym_pure =>
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨_, _, _, _, _, _, rfl, rfl, rfl, rfl⟩))))))
  | call hc hvs hf hlen =>
    rw [callRedex?_sseq, Option.map_eq_some_iff] at hc
    obtain ⟨⟨ctx1, f1, pes1⟩, hc1, hq⟩ := hc
    obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
      exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq,
        congrArg (fun q => q.2.2) hq⟩
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr
      ⟨ctx1, f1, pes1, _, _, _, hc1, hvs, hf, hlen, rfl⟩))))))

/-- Inversion at an Ewseq node (S1b DRIFT TEST — the wildcard-only
    `sseq_inv` shape): a frame step of a non-jump-redex, non-value e1,
    one of the two wildcard betas, THE GLOBAL JUMP (frame discarded), or
    (C2) THE CALL of e1 with the `Cwseq` frame captured. Only the
    wildcard pattern has beta rules (the mirrored Ewseq fragment —
    spec/sym binder patterns remain outside, README registered
    divergences). -/
theorem Step.wseq_inv {M : MachineCtx} {a : List annot} {pat : pattern}
    {e1 e2 : CoreExpr}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (h : Step M (Expr a (Ewseq pat e1 e2), ρ, ctl, σ) out) :
    (∃ e1' ρ' σ', jumpRedex? e1 = none ∧ toVal e1 = none ∧
        Step M (e1, ρ, ctl, σ) (e1', ρ', ctl, σ') ∧
        out = (Expr a (Ewseq pat e1' e2), ρ', ctl, σ')) ∨
    (∃ pa bty v ev0 evs, pat = Pattern pa (CaseBase (none, bty)) ∧
        e1 = ofVal (.pure v) ∧ ρ = ev0 :: evs ∧ out = (e2, ρ, ctl, σ)) ∨
    (∃ pa bty ds v ev0 evs, pat = Pattern pa (CaseBase (none, bty)) ∧
        e1 = ofVal (.annot ds v) ∧ ρ = ev0 :: evs ∧
        out = (Expr [] (Eannot ds e2), ρ, ctl, σ)) ∨
    (∃ l pes params cont vs ev0 evs, jumpRedex? e1 = some (l, pes) ∧
        ρ = ev0 :: evs ∧ lookupLabel (M.labelsAt ctl.proc) l = some (params, cont) ∧
        evalPexprs M.tagDefs M.extern ρ pes = some vs ∧
        out = (cont, bindArgs params vs ρ, ctl, σ)) ∨
    Step.CallOf M e1 (fun c => Cwseq a pat c e2) ρ ctl σ out := by
  cases h with
  | wseq_ctx hnj hnv hs => exact .inl ⟨_, _, _, hnj, hnv, hs, rfl⟩
  | wseq_pure => exact .inr (.inl ⟨_, _, _, _, _, rfl, rfl, rfl, rfl⟩)
  | wseq_annot => exact .inr (.inr (.inl ⟨_, _, _, _, _, _, rfl, rfl, rfl, rfl⟩))
  | run hj hl hvs =>
    rw [jumpRedex?_wseq] at hj
    exact .inr (.inr (.inr (.inl ⟨_, _, _, _, _, _, _, hj, rfl, hl, hvs, rfl⟩)))
  | call hc hvs hf hlen =>
    rw [callRedex?_wseq, Option.map_eq_some_iff] at hc
    obtain ⟨⟨ctx1, f1, pes1⟩, hc1, hq⟩ := hc
    obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
      exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq,
        congrArg (fun q => q.2.2) hq⟩
    exact .inr (.inr (.inr (.inr ⟨ctx1, f1, pes1, _, _, _, hc1, hvs, hf, hlen, rfl⟩)))

/-- Inversion at an Eannot node (S3 form): Cannot-descent of a
    non-jump-redex body, the ANNOTS merge, the global jump through the
    Cannot frame, or (C2) THE CALL of the body with the `Cannot` frame
    captured, or (C2) REMOVE-ANNOT at a non-empty call stack (the body a
    bare value, the node annotation-free). -/
theorem Step.annot_inv {M : MachineCtx} {a : List annot}
    {ds : List dyn_annotation}
    {b : CoreExpr} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config}
    (h : Step M (Expr a (Eannot ds b), ρ, ctl, σ) out) :
    (annotRooted b = false ∧ jumpRedex? b = none ∧
        ∃ b' ρ' σ', Step M (b, ρ, ctl, σ) (b', ρ', ctl, σ') ∧
        out = (Expr a (Eannot ds b'), ρ', ctl, σ')) ∨
    (∃ a2 ds2 c, b = Expr a2 (Eannot ds2 c) ∧
        out = (Expr (a ++ a2) (Eannot (ds ++ ds2) c), ρ, ctl, σ)) ∨
    (∃ l pes params cont vs ev0 evs, annotRooted b = false ∧
        jumpRedex? b = some (l, pes) ∧
        ρ = ev0 :: evs ∧ lookupLabel (M.labelsAt ctl.proc) l = some (params, cont) ∧
        evalPexprs M.tagDefs M.extern ρ pes = some vs ∧
        out = (cont, bindArgs params vs ρ, ctl, σ)) ∨
    (annotRooted b = false ∧ Step.CallOf M b (fun c => Cannot a ds c) ρ ctl σ out) ∨
    (∃ v pc κ, a = [] ∧ b = Expr [] (Epure (Pexpr [] () (PEval v))) ∧ ctl.κ = pc :: κ ∧
        out = (Expr [] (Epure (Pexpr [] () (PEval v))), ρ, ctl, σ)) := by
  cases h with
  | annot_ctx hnj hg hs => exact .inl ⟨hg, hnj, _, _, _, hs, rfl⟩
  | annot_merge => exact .inr (.inl ⟨_, _, _, rfl, rfl⟩)
  | run hj hl hvs =>
    by_cases hr : annotRooted b = true
    · rw [jumpRedex?_annot_of_root _ _ hr] at hj; cases hj
    · have hr' : annotRooted b = false := by simpa using hr
      rw [jumpRedex?_annot_of_not_root _ _ hr'] at hj
      exact .inr (.inr (.inl ⟨_, _, _, _, _, _, _, hr', hj, rfl, hl, hvs, rfl⟩))
  | call hc hvs hf hlen =>
    by_cases hr : annotRooted b = true
    · rw [callRedex?_annot_of_root _ _ hr] at hc; cases hc
    · have hr' : annotRooted b = false := by simpa using hr
      rw [callRedex?_annot_of_not_root _ _ hr', Option.map_eq_some_iff] at hc
      obtain ⟨⟨ctx1, f1, pes1⟩, hc1, hq⟩ := hc
      obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
        exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq,
          congrArg (fun q => q.2.2) hq⟩
      exact .inr (.inr (.inr (.inl ⟨hr', ctx1, f1, pes1, _, _, _, hc1, hvs, hf, hlen, rfl⟩)))
  | ret_annot => exact .inr (.inr (.inr (.inr ⟨_, _, _, rfl, rfl, rfl, rfl⟩)))

/-- Inversion at an Esave node: either the entry TAU (value-shaped
    initializers) or the parameter-EVAL step (initializers not all
    values, re-formed with their values) — the engine's two arms. -/
theorem Step.save_inv {M : MachineCtx} {a : List annot}
    {sb : sym × core_base_type}
    {ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
    {body : CoreExpr} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config}
    (h : Step M (Expr a (Esave sb ps body), ρ, ctl, σ) out) :
    (∃ cvals ev0 evs, ρ = ev0 :: evs ∧
      valueFromPexprs (saveParamPexprs ps) = some cvals ∧
      out = (body, bindSaveParams ps cvals ρ, ctl, σ)) ∨
    (∃ cvals, valueFromPexprs (saveParamPexprs ps) = none ∧
      evalPexprs M.tagDefs M.extern ρ (saveParamPexprs ps) = some cvals ∧
      out = (Expr a (Esave sb (saveParamsWithValues ps cvals) body), ρ, ctl, σ)) := by
  cases h with
  | save hvals => exact .inl ⟨_, _, _, rfl, hvals, rfl⟩
  | save_eval hnv hvals => exact .inr ⟨_, hnv, hvals, rfl⟩
  | run hj hl hvs => simp [jumpRedex?] at hj
  | call hc hvs hf hlen => simp at hc

/-- Inversion at an Esave node with VALUE initializers: the entry TAU
    only (the pre-QA-1 shape, retained as the literal instance). -/
theorem Step.save_vals_inv {M : MachineCtx} {a : List annot}
    {sb : sym × core_base_type}
    {ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
    {body : CoreExpr} {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {cvals : List value}
    {out : Config}
    (hvals : valueFromPexprs (saveParamPexprs ps) = some cvals)
    (h : Step M (Expr a (Esave sb ps body), ρ, ctl, σ) out) :
    ∃ ev0 evs, ρ = ev0 :: evs ∧ out = (body, bindSaveParams ps cvals ρ, ctl, σ) := by
  rcases h.save_inv with ⟨cvals', ev0, evs, hρ, hvals', hout⟩ |
      ⟨_, hnv, _, _⟩
  · obtain rfl : cvals = cvals' := Option.some.inj (hvals.symm.trans hvals')
    exact ⟨ev0, evs, hρ, hout⟩
  · rw [hvals] at hnv; cases hnv

/-- Inversion at an Esave node whose initializers are NOT all values:
    the parameter-EVAL step only. -/
theorem Step.save_op_inv {M : MachineCtx} {a : List annot}
    {sb : sym × core_base_type}
    {ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
    {body : CoreExpr} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config}
    (hnv : valueFromPexprs (saveParamPexprs ps) = none)
    (h : Step M (Expr a (Esave sb ps body), ρ, ctl, σ) out) :
    ∃ cvals, evalPexprs M.tagDefs M.extern ρ (saveParamPexprs ps) = some cvals ∧
      out = (Expr a (Esave sb (saveParamsWithValues ps cvals) body), ρ, ctl, σ) := by
  rcases h.save_inv with ⟨_, _, _, _, hvals, _⟩ | ⟨cvals, _, hvals, hout⟩
  · rw [hnv] at hvals; cases hvals
  · exact ⟨cvals, hvals, hout⟩

/-- Inversion at an Eif node: the guard evaluates to a boolean and
    the step selects the branch. -/
theorem Step.if_inv {M : MachineCtx} {a : List annot}
    {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (h : Step M (Expr a (Eif g e2 e3), ρ, ctl, σ) out) :
    (evalPexpr M.tagDefs M.extern ρ g = some Vtrue ∧ out = (e2, ρ, ctl, σ)) ∨
    (evalPexpr M.tagDefs M.extern ρ g = some Vfalse ∧ out = (e3, ρ, ctl, σ)) := by
  cases h with
  | if_true hg => exact .inl ⟨hg, rfl⟩
  | if_false hg => exact .inr ⟨hg, rfl⟩
  | run hj hl hvs => simp [jumpRedex?] at hj
  | call hc hvs hf hlen => simp at hc

/-- Inversion at an Ecase node: the value-scrutinee selection TAU. -/
theorem Step.case_inv {M : MachineCtx} {a : List annot}
    {pe : generic_pexpr Unit sym} {pats : List (pattern × CoreExpr)}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (h : Step M (Expr a (Ecase pe pats), ρ, ctl, σ) out) :
    ∃ cval e', valueFromPexpr pe = some cval ∧
      select_case subst_sym_expr cval pats = some e' ∧
      out = (e', ρ, ctl, σ) := by
  cases h with
  | case_value hv hsel => exact ⟨_, _, hv, hsel, rfl⟩
  | run hj hl hvs => simp [jumpRedex?] at hj
  | call hc hvs hf hlen => simp at hc

/-- Inversion at an Epure node (S4): the big-step PURE evaluation. -/
theorem Step.pure_inv {M : MachineCtx} {a : List annot}
    {pe : generic_pexpr Unit sym} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config}
    (hnv : valueFromPexpr pe = none)
    (h : Step M (Expr a (Epure pe), ρ, ctl, σ) out) :
    ∃ v, valueFromPexpr pe = none ∧ evalPexpr M.tagDefs M.extern ρ pe = some v ∧
      out = (Expr a (Epure (Pexpr [] () (PEval v))), ρ, ctl, σ) := by
  cases h with
  | pure_eval hnv hv => exact ⟨_, hnv, hv, rfl⟩
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | ret => rw [valueFromPexpr_val] at hnv; cases hnv

/-- Inversion at a positive load whose pointer operand is NOT a
    value (S4): the ACTION_EVAL step. The operand's non-value shape
    is a side hypothesis (it discharges by `rfl`/`simp` at authored
    shapes) so the canonical load rule's arms refute. -/
theorem Step.load_op_inv {M : MachineCtx} {a : List annot}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pe2 : generic_pexpr Unit sym} {mo : memory_order}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (hnv2 : valueFromPexpr pe2 = none)
    (h : Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Load0 (Pexpr [] () (PEval (Vctype ty))) pe2 mo)))), ρ, ctl, σ) out) :
    ∃ pv, evalPexpr M.tagDefs M.extern ρ pe2 = some (Vobject (OVpointer pv)) ∧
      out = (Expr a (Eaction (Paction polarity.Pos (Action loc ann
        (Load0 (Pexpr [] () (PEval (Vctype ty)))
               (Pexpr [] () (PEval (Vobject (OVpointer pv)))) mo)))), ρ, ctl, σ) := by
  cases h with
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | load h1 h2 hmem => rw [hnv2] at h2; cases h2
  | load_eval hnv2' hv2 => exact ⟨_, hv2, rfl⟩

/-- Inversion at the pointer-equality memop with VALUE operands: the
    step is unique and fully determined by the memM computation. -/
theorem Step.memop_ptreq_inv {M : MachineCtx} {a : List annot}
    {pe1 pe2 : generic_pexpr Unit sym} {pv1 pv2 : CerbMem.PointerValue}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (h1 : valueFromPexpr pe1 = some (Vobject (OVpointer pv1)))
    (h2 : valueFromPexpr pe2 = some (Vobject (OVpointer pv2)))
    (h : Step M (Expr a (Ememop PtrEq [pe1, pe2]), ρ, ctl, σ) out) :
    ∃ b σ', applyMemM (CerbMem.eqPtrval default pv1 pv2) σ = some (b, σ') ∧
      out = (Expr [] (Epure (Pexpr [] () (PEval (boolValue b)))), ρ, ctl, σ') := by
  cases h with
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | memop_ptreq h1' h2' hmem =>
    rw [h1] at h1'
    rw [h2] at h2'
    obtain rfl : pv1 = _ := by simpa using h1'
    obtain rfl : pv2 = _ := by simpa using h2'
    exact ⟨_, _, hmem, rfl⟩
  | memop_eval hnv hv1 hv2 =>
    rw [valueFromPexprs_pair, h1, h2] at hnv
    cases hnv

/-- Inversion at the pointer-equality memop with VALUE operands, any
    values (the successor-general form of `memop_ptreq_inv`, for the
    same-control sweeps): the step is the PtrEq round at two pointers. -/
theorem Step.memop_vals_inv {M : MachineCtx} {a : List annot} {v1 v2 : value}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (h : Step M (Expr a (Ememop PtrEq [Pexpr [] () (PEval v1), Pexpr [] () (PEval v2)]),
      ρ, ctl, σ) out) :
    ∃ pv1 pv2 b σ', v1 = Vobject (OVpointer pv1) ∧ v2 = Vobject (OVpointer pv2) ∧
      applyMemM (CerbMem.eqPtrval default pv1 pv2) σ = some (b, σ') ∧
      out = (Expr [] (Epure (Pexpr [] () (PEval (boolValue b)))), ρ, ctl, σ') := by
  cases h with
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | memop_ptreq h1 h2 hmem =>
    rw [valueFromPexpr_val] at h1 h2
    exact ⟨_, _, _, _, Option.some.inj h1, Option.some.inj h2, hmem, rfl⟩
  | memop_eval hnv hv1 hv2 =>
    rw [valueFromPexprs_pair, valueFromPexpr_val, valueFromPexpr_val] at hnv
    cases hnv

/-- Inversion at a two-operand memop with a NON-value operand list:
    the operand-evaluation step. -/
theorem Step.memop_op_inv {M : MachineCtx} {a : List annot} {mop : memop}
    {pe1 pe2 : generic_pexpr Unit sym}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (h : Step M (Expr a (Ememop mop [pe1, pe2]), ρ, ctl, σ) out) :
    ∃ v1 v2, evalPexpr M.tagDefs M.extern ρ pe1 = some v1 ∧ evalPexpr M.tagDefs M.extern ρ pe2 = some v2 ∧
      out = (Expr a (Ememop mop
        [Pexpr [] () (PEval v1), Pexpr [] () (PEval v2)]), ρ, ctl, σ) := by
  cases h with
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | memop_ptreq h1 h2 hmem =>
    rw [valueFromPexprs_pair, h1, h2] at hnv
    cases hnv
  | memop_eval hnv' hv1 hv2 => exact ⟨_, _, hv1, hv2, rfl⟩

/-- Inversion at a store whose operands are NOT all values: the
    ACTION_EVAL step. -/
theorem Step.store_op_inv {M : MachineCtx} {a : List annot}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
    {ty : ctype} {pe2 pe3 : generic_pexpr Unit sym} {mo : memory_order}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (hnv : valueFromPexprs [pe2, pe3] = none)
    (h : Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
        (Store0 lk (Pexpr [] () (PEval (Vctype ty))) pe2 pe3 mo)))), ρ, ctl, σ)
      out) :
    ∃ pv cv, evalPexpr M.tagDefs M.extern ρ pe2 = some (Vobject (OVpointer pv)) ∧
      evalPexpr M.tagDefs M.extern ρ pe3 = some cv ∧
      out = (Expr a (Eaction (Paction polarity.Pos (Action loc ann
        (Store0 lk (Pexpr [] () (PEval (Vctype ty)))
                (Pexpr [] () (PEval (Vobject (OVpointer pv))))
                (Pexpr [] () (PEval cv)) mo)))), ρ, ctl, σ) := by
  cases h with
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | store h1 h2 h3 hmv hmem => rw [valueFromPexprs_pair, h2, h3] at hnv; cases hnv
  | store_eval hnv' hv2 hv3 => exact ⟨_, _, hv2, hv3, rfl⟩

/-- Constructor-clash refutation: the Specified-binder pattern is
    never the wildcard base pattern (the wildcard-context proofs'
    dispatch fact). -/
theorem specPat_ne_base {pa' : List annot} {bty' : core_base_type}
    {pa pb : List annot} {x : sym} {bty : core_base_type}
    (h : Pattern pa' (CaseBase (none, bty')) = specPat pa pb x bty) : False := by
  simp [specPat] at h

theorem specPat_inj {pa pb pa' pb' : List annot} {x x' : sym}
    {bty bty' : core_base_type}
    (h : specPat pa pb x bty = specPat pa' pb' x' bty') :
    pa = pa' ∧ pb = pb' ∧ x = x' ∧ bty = bty' := by
  simpa [specPat] using h

/-- The plain-symbol pattern is never the wildcard base pattern
    (`some x ≠ none`). -/
theorem symPat_ne_base {pa' : List annot} {bty' : core_base_type}
    {pa : List annot} {x : sym} {bty : core_base_type}
    (h : Pattern pa' (CaseBase (none, bty')) = symPat pa x bty) : False := by
  simp [symPat] at h

/-- ... nor the Specified-binder pattern (CaseCtor vs CaseBase). -/
theorem symPat_ne_spec {pa pb : List annot} {x : sym} {bty : core_base_type}
    {pa' : List annot} {x' : sym} {bty' : core_base_type}
    (h : specPat pa pb x bty = symPat pa' x' bty') : False := by
  simp [specPat, symPat] at h

theorem symPat_inj {pa pa' : List annot} {x x' : sym}
    {bty bty' : core_base_type}
    (h : symPat pa x bty = symPat pa' x' bty') :
    pa = pa' ∧ x = x' ∧ bty = bty' := by
  simpa [symPat] using h

/-- A non-value pure expression is not a mirror value (feeds the
    S4 PURE rule's wps face). -/
theorem toVal_pure_none {a : List annot} {pe : generic_pexpr Unit sym}
    (hnv : valueFromPexpr pe = none) : toVal (Expr a (Epure pe)) = none := by
  rcases pe with ⟨b, u, pe_⟩
  cases u
  cases pe_ <;>
    first
    | rfl
    | (rw [valueFromPexpr_val] at hnv; cases hnv)

/-- Canonical spelling of the S4 PURE redex (non-value pure
    expression at the root). -/
def pureRedex (pe : generic_pexpr Unit sym) : CoreExpr :=
  Expr [] (Epure pe)

/-- Canonical spelling of the S4 load ACTION_EVAL redex: positive
    strong load, canonical evaluated type operand, UNevaluated
    pointer operand. -/
def loadOpRedex (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (ty : ctype) (pe2 : generic_pexpr Unit sym) (mo : memory_order) : CoreExpr :=
  Expr [] (Eaction (Paction polarity.Pos (Action loc ann
    (Load0 (Pexpr [] () (PEval (Vctype ty))) pe2 mo))))

/-- Canonical spelling of a memop redex (list-reverse phase A):
    `[]` node annotations, operands per instance. -/
def memopRedex (mop : memop) (pes : List (generic_pexpr Unit sym)) : CoreExpr :=
  Expr [] (Ememop mop pes)

/-- The pointer-equality memop at canonical VALUE operands (the
    post-ACTION_EVAL shape the memop axiom fires at). -/
def memopPtrEqVals (v1 v2 : value) : CoreExpr :=
  memopRedex PtrEq [Pexpr [] () (PEval v1), Pexpr [] () (PEval v2)]

/-- Canonical spelling of the store ACTION_EVAL redex: positive
    strong non-locking store, canonical evaluated type operand,
    UNevaluated pointer/value operands. -/
def storeOpRedex (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (ty : ctype) (pe2 pe3 : generic_pexpr Unit sym) (mo : memory_order) :
    CoreExpr :=
  Expr [] (Eaction (Paction polarity.Pos (Action loc ann
    (Store0 false (Pexpr [] () (PEval (Vctype ty))) pe2 pe3 mo))))

/-- Canonical spelling of the kill redex (kill/free arc K2): positive
    strong kill of any kind at the canonical EVALUATED pointer operand
    (`Rules.killExpr` is the same spelling). -/
def killRedex (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (kind : kill_kind) (pv : CerbMem.PointerValue) : CoreExpr :=
  Expr [] (Eaction (Paction polarity.Pos (Action loc ann
    (Kill kind (Pexpr [] () (PEval (Vobject (OVpointer pv))))))))

/-- Canonical spelling of the kill ACTION_EVAL redex: positive strong
    kill at an UNevaluated pointer operand. -/
def killOpRedex (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (kind : kill_kind) (pe : generic_pexpr Unit sym) : CoreExpr :=
  Expr [] (Eaction (Paction polarity.Pos (Action loc ann (Kill kind pe))))

/-- Canonical spelling of the alloc redex (kill/free arc K3): positive
    strong dynamic allocation at canonical EVALUATED integer operands
    (`Rules.allocExpr` is the same spelling). -/
def allocRedex (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (align size : CerbMem.IntegerValue) (pref : prefix0) : CoreExpr :=
  Expr [] (Eaction (Paction polarity.Pos (Action loc ann
    (Alloc0 (Pexpr [] () (PEval (Vobject (OVinteger align))))
            (Pexpr [] () (PEval (Vobject (OVinteger size)))) pref))))

/-- Canonical spelling of the alloc ACTION_EVAL redex: positive strong
    dynamic allocation at operands that are NOT all values. -/
def allocOpRedex (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (pe1 pe2 : generic_pexpr Unit sym) (pref : prefix0) : CoreExpr :=
  Expr [] (Eaction (Paction polarity.Pos (Action loc ann (Alloc0 pe1 pe2 pref))))

/-! ## The frozen profiles as context instances

`spikeLbl` survives as the frozen EMPTY label map VALUE (the
`spikeEnv` precedent) — the label fiber of the straight-line launch
profile. The frozen profiles themselves are now `MachineCtx`
INSTANCES: `spikeCtx` (the straight-line/production launch context)
and `procCtx rs` (the jump profile over a parameterized run state;
the thread is IN a procedure through the entry control `procCtl p`). No frozen constant remains inside any
judgment; exported statements pin the launch profile through these
instances only.

S1b RETIREMENT NOTE (design record §8.3, prune-don't-merge): the
phase-1 parallel cone `FragP` (and its `Decomp`-side machinery in
Soundness.lean) is DELETED — the ONE cone is `Frag` (Soundness.lean;
the migrated `FragJ` with value-scrutinee `Ecase` joined). -/

abbrev spikeLbl : LabelMap := fmapEmpty

@[simp] theorem lookupLabel_empty (l : sym) :
    lookupLabel spikeLbl l = none := rfl

/-- The default (empty) Core file. Only proc/impl/funinfo lookups
    read it; the fragment performs none. -/
def spikeFile : generic_file Unit core_run_annotation := default

/-- The frozen core_run_state (Core_run_aux.lean:353-358). The
    fragment's request monads thread it; only the aid would reach a
    continuation, and the fragment's continuations ignore it (D2). -/
def spikeRunState : core_run_state :=
  { tid_supply := 1, aid_supply := 0, excluded_supply := 0, sym_supply := 0,
    labeled := fmapEmpty }

/-- The entry control of the straight-line profile: empty call stack,
    no current procedure, default execution location (the `envThread`
    literal's control fields, Soundness.lean). Reducible for the same
    reason as `spikeCtx`. -/
@[reducible] def spikeCtl : Ctl := ⟨[], none, default⟩

/-- The entry control of the jump profile: empty call stack, IN
    PROCEDURE `p` (what `Erun` reads the label map at), default
    execution location (the `procThread` literal's control fields). -/
@[reducible] def procCtl (p : sym) : Ctl := ⟨[], some p, default⟩

@[simp] theorem spikeCtl_κ : spikeCtl.κ = [] := rfl
@[simp] theorem spikeCtl_proc : spikeCtl.proc = none := rfl
@[simp] theorem procCtl_κ (p : sym) : (procCtl p).κ = [] := rfl
@[simp] theorem procCtl_proc (p : sym) : (procCtl p).proc = some p := rfl

/-- The straight-line frozen profile as a context instance
    (tagDefs/extern empty, default file, tid 0, no parent, frozen run
    state; the control — empty stack, no current procedure — is the
    entry control `spikeCtl`).

    REDUCIBLE (tag-environment threading, 2026-09-02): the logic's
    rules are stated at `M.tagDefs`; the clients state their
    footprints at the program's environment `fmapEmpty`. Making the
    concrete profiles reducible lets `(procCtx rs).tagDefs` and
    `spikeCtx.tagDefs` unfold to `fmapEmpty` under the proof mode's
    reducible-transparency matching, so no client proof has to
    rewrite the environment by hand. -/
@[reducible] def spikeCtx : MachineCtx :=
  { tagDefs := fmapEmpty, file := spikeFile, extern := fmapEmpty,
    tid := 0, parent := none, errno := default, currentLoc := default,
    runState := spikeRunState }

/-- The jump profile (parameterized run state) as a context instance
    (reducible — see `spikeCtx`); its thread is IN a procedure through
    the entry control `procCtl p`, not through the context (C1). -/
@[reducible] def procCtx (rs : core_run_state) : MachineCtx :=
  { spikeCtx with runState := rs }

/-- Field-projection equations for the two profile instances. -/
@[simp] theorem spikeCtx_tagDefs : spikeCtx.tagDefs = fmapEmpty := rfl
@[simp] theorem spikeCtx_extern : spikeCtx.extern = fmapEmpty := rfl
@[simp] theorem spikeCtx_runState : spikeCtx.runState = spikeRunState := rfl
@[simp] theorem procCtx_tagDefs (rs : core_run_state) :
    (procCtx rs).tagDefs = fmapEmpty := rfl
@[simp] theorem procCtx_extern (rs : core_run_state) :
    (procCtx rs).extern = fmapEmpty := rfl
@[simp] theorem procCtx_runState (rs : core_run_state) :
    (procCtx rs).runState = rs := rfl

/-- The straight-line profile's label map at its entry control: empty
    (no current procedure). -/
@[simp] theorem spikeCtx_labels : spikeCtx.labelsAt spikeCtl.proc = spikeLbl := rfl

theorem spikeCtx_wf : spikeCtx.SeqWF := ⟨rfl⟩

theorem procCtx_wf (rs : core_run_state) : (procCtx rs).SeqWF := ⟨rfl⟩

/-- The jump profile's DERIVED label map at a successful two-level
    `labeled` read (the old `LabeledAt` tie, consumed): the fiber at
    the current procedure IS the context's label map. Stated in the
    engine's own lookup spelling (extern empty in the profile, so the
    proc redirect is the identity fallback). -/
theorem procCtx_labels {p : sym} {rs : core_run_state} {Q : LabelMap}
    (hQ : fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
      Lem_Basic_classes.ordCompare s1 s2) p rs.labeled = some Q) :
    (procCtx rs).labelsAt (procCtl p).proc = Q := by
  rw [MachineCtx.labelsAt_eq_of_proc (M := procCtx rs) (c := procCtl p) rfl,
    MachineCtx.resolveProc_of_extern_empty rfl]
  show (match fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
      Lem_Basic_classes.ordCompare s1 s2) p rs.labeled with
    | some Q => Q
    | none => fmapEmpty) = Q
  rw [hQ]

end CerberusHeapLang
