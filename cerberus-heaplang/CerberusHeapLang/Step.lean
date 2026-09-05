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
vocabulary (`DriverSafeCtl`/`DriverDoneCtl`, `Sat`/`CellCoh` — a wrong
definition THERE yields a true but irrelevant theorem, which is why
the walkthrough prints them), and coverage is fail-open by nature —
a missing rule narrows what is provable without falsifying anything;
the per-construct coverage authority is docs/CAPABILITY_MANIFEST.md.

SCOPE (the mirrored fragment): pure values; `Store0`/`Load0`/`Create0`
actions and the `Kill` action (kill/free arc K2; any `kill_kind` in
both `Step` and `Frag` — K3 lifted the fragment's static-only
restriction) at evaluated operands and at the operands the engine
evaluates first (the ACTION_EVAL step); the `PtrEq` memop; strong
sequencing `Esseq` at the wildcard, `Specified`-binder,
plain-symbol-binder and (E2) flat-tuple-binder patterns; weak
sequencing `Ewseq` at the wildcard and (E2) at the plain-symbol and
flat-tuple binders; `Esave`, `Eif`, `Ecase` at a value scrutinee and
(E2) at a covered non-value scrutinee (`case_eval`), the
context-discarding `Erun`; the PURE round at any covered non-value
operand (`pure_eval`; E2 — the E1 mirror took `PEsym` only); `bound`
and located nodes (E1); and the run-time `Eannot` residue those
produce; and (calls arc C2) THE
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
GROWS; dialect arc E1, 2026-09-04 — it grows again). The live state is
the quadruple `Config := CoreExpr × EnvStack × Ctl × Mem`: the arena,
the environment stack, the thread's LIVE CONTROL `Ctl` (the call stack
`κ`, the current procedure `proc`, the execution location `execLoc` —
the three `thread_state` fields a procedure call and a return WRITE,
step_ctx's PCALL/RETURN arms, Core_reduction.lean:484 — and, since E1,
the current location `curLoc`, which the general arm of `step_ctx`
rewrites from the redex node's first non-library `Aloc`, and the run
state's two supplies `sup : RunSup`, which no rule writes yet and E5's
negative actions will) and the memory. Everything else the engine's
configuration holds and the fragment leaves immutable — `step_ctx`'s
parameters (tag definitions, file, extern map, thread id, parent), the
thread's `errno`, and the run state's `labeled` map the discharge
protocol threads (read-only under the fragment: `Erun` reads it; the
PCALL round's argument map and `runEU` are state-verbatim too) — is the
explicit index `MachineCtx`; `M.thread e ρ ctl` is the engine
`thread_state` the configuration denotes. EXACTLY TWO RULES WRITE THE
CALL-STACK PART OF THE CONTROL (calls arc C2): `Step.call` pushes the
frame `(ctl.proc, ctx)` — the caller's procedure and the CAPTURED
evaluation context of the call redex — sets the callee as the current
procedure and pushes the execution location; `Step.ret` pops the frame
back. Every other constructor threads `κ`/`proc`/`execLoc` unchanged
and writes the location (`ctl.upd a`, E1; `Step.ctl_cases`,
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

Design history: the dated records under docs/. E1 (the emitted-Core
dialect arc's first slice — annotations live on every node with the
location update on the control, `Ebound`, `Ivalignof`/`Ivsizeof`, the
run-state supplies on the control, `BareHead` retired):
docs/2026-09-04_e1-notes.md.
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

/-- THE VALUE WITH ITS STATIC ANNOTATION LISTS (E1). The engine's two
    value shapes accept ANY static annotations (`is_irreducible`,
    Core_reduction.lean:293: `Expr _ (Epure (Pexpr _ _ (PEval _)))` and
    `Expr _ (Eannot _ (Expr _ (Epure (Pexpr _ _ (PEval _)))))`), and the
    PURE round KEEPS the node's annotations on the value it produces
    (`Expr annots (Epure (mk_value_pe cval))`, core_reduction.lem:299;
    Core_reduction.lean:353), so located values are first-class runtime
    terms of emitted Core. `SpikeVal` ERASES them (`toVal`, what the
    judgments' postconditions see); `SpikeValA` carries them, in exact
    bijection with the value expressions (`ofValA`/`toValA`), and is the
    iris-lean `Language` value (`CoreRVal.w`) so that `ofValRt`/`toValRt`
    stay inverse. `outer` is the node's list, `inner` the annotated form's
    inner node list, `pe` the pexpr's list (`[]` after any engine round —
    `mk_value_pe`). -/
inductive SpikeValA : Type where
  | pure (outer pe : List annot) (v : value)
  | annot (outer inner pe : List annot) (ds : List dyn_annotation) (v : value)

namespace SpikeValA

/-- The erasure onto the judgments' value type. -/
def erase : SpikeValA → SpikeVal
  | .pure _ _ v => .pure v
  | .annot _ _ _ ds v => .annot ds v

@[simp] theorem erase_pure (a b : List _root_.annot) (v : value) : (pure a b v).erase = .pure v := rfl
@[simp] theorem erase_annot (a a2 b : List _root_.annot) (ds : List dyn_annotation) (v : value) :
    (annot a a2 b ds v).erase = .annot ds v := rfl

/-- The underlying Core value. -/
def val (w : SpikeValA) : value := w.erase.val

@[simp] theorem val_pure (a b : List _root_.annot) (v : value) : (pure a b v).val = v := rfl
@[simp] theorem val_annot (a a2 b : List _root_.annot) (ds : List dyn_annotation) (v : value) :
    (annot a a2 b ds v).val = v := rfl

/-- Wrapping a value form in one more `Eannot ds` layer at a node
    annotated `a`: the bare form BECOMES the annotated form (no round —
    it is already a value shape), the annotated form is the ANNOTS merge
    (`Expr (annots ++ annots2) (Eannot (xs1 ++ xs2) e)`,
    core_reduction.lem:301–304). Erases to `SpikeVal.merge ds`. -/
def merge (a : List _root_.annot) (ds : List dyn_annotation) : SpikeValA → SpikeValA
  | .pure a2 b v => .annot a a2 b ds v
  | .annot a1 a2 b ds' v => .annot (a ++ a1) a2 b (ds ++ ds') v

@[simp] theorem erase_merge (a : List _root_.annot) (ds : List dyn_annotation) (w : SpikeValA) :
    (merge a ds w).erase = SpikeVal.merge ds w.erase := by
  cases w <;> rfl

@[simp] theorem val_merge (a : List _root_.annot) (ds : List dyn_annotation) (w : SpikeValA) :
    (merge a ds w).val = w.val := by
  cases w <;> rfl

end SpikeValA

/-- The canonical (annotation-free) annotated form of an erased value:
    the shape `mk_value_e` produces (Core_aux.lean:302,645), resp. the
    action continuations' Eannot wrap (Core_reduction.lean:424). -/
def SpikeVal.canon : SpikeVal → SpikeValA
  | .pure v => .pure [] [] v
  | .annot ds v => .annot [] [] [] ds v

@[simp] theorem SpikeVal.erase_canon (w : SpikeVal) : w.canon.erase = w := by
  cases w <;> rfl

@[simp] theorem SpikeVal.canon_pure (v : value) : (SpikeVal.pure v).canon = .pure [] [] v := rfl
@[simp] theorem SpikeVal.canon_annot (ds : List dyn_annotation) (v : value) :
    (SpikeVal.annot ds v).canon = .annot [] [] [] ds v := rfl

/-- Expression of a value AT its static annotation lists (the exact
    injection). -/
def ofValA : SpikeValA → CoreExpr
  | .pure a b v => Expr a (Epure (Pexpr b () (PEval v)))
  | .annot a a2 b ds v => Expr a (Eannot ds (Expr a2 (Epure (Pexpr b () (PEval v)))))

@[simp] theorem ofValA_pure (a b : List annot) (v : value) :
    ofValA (.pure a b v) = Expr a (Epure (Pexpr b () (PEval v))) := rfl

@[simp] theorem ofValA_annot (a a2 b : List annot) (ds : List dyn_annotation) (v : value) :
    ofValA (.annot a a2 b ds v) = Expr a (Eannot ds (Expr a2 (Epure (Pexpr b () (PEval v))))) := rfl

/-- Canonical expression of an erased value. -/
def ofVal (w : SpikeVal) : CoreExpr := ofValA w.canon

@[simp] theorem ofVal_pure (v : value) :
    ofVal (.pure v) = Expr [] (Epure (Pexpr [] () (PEval v))) := rfl

@[simp] theorem ofVal_annot (ds : List dyn_annotation) (v : value) :
    ofVal (.annot ds v) = Expr [] (Eannot ds (Expr [] (Epure (Pexpr [] () (PEval v))))) := rfl

@[simp] theorem ofValA_canon (w : SpikeVal) : ofValA w.canon = ofVal w := rfl

/-- The exact value test: `is_irreducible`'s two value shapes
    (Core_reduction.lean:293) with their annotation lists. Dispatches on
    expression constructors only, so it reduces on non-value shapes with
    symbolic annotation lists. -/
def toValA : CoreExpr → Option SpikeValA
  | Expr a (Epure (Pexpr b _ (PEval v))) => some (.pure a b v)
  | Expr a (Eannot ds (Expr a2 (Epure (Pexpr b _ (PEval v))))) => some (.annot a a2 b ds v)
  | _ => none

/-- The ERASING value test (the pre-E1 `toVal`, now at any static
    annotation lists): what `wps.pre`/`twp.pre` read. -/
def toVal : CoreExpr → Option SpikeVal
  | Expr _ (Epure (Pexpr _ _ (PEval v))) => some (.pure v)
  | Expr _ (Eannot ds (Expr _ (Epure (Pexpr _ _ (PEval v))))) => some (.annot ds v)
  | _ => none

theorem toVal_eq_toValA (e : CoreExpr) : toVal e = (toValA e).map SpikeValA.erase := by
  unfold toVal toValA
  split <;> rfl

@[simp] theorem toValA_ofValA (w : SpikeValA) : toValA (ofValA w) = some w := by
  cases w <;> rfl

@[simp] theorem toVal_ofValA (w : SpikeValA) : toVal (ofValA w) = some w.erase := by
  cases w <;> rfl

@[simp] theorem toVal_ofVal (w : SpikeVal) : toVal (ofVal w) = some w := by
  cases w <;> rfl

@[simp] theorem toValA_ofVal (w : SpikeVal) : toValA (ofVal w) = some w.canon := by
  cases w <;> rfl

@[simp] theorem toVal_pure_val (a b : List annot) (v : value) :
    toVal (Expr a (Epure (Pexpr b () (PEval v)))) = some (.pure v) := rfl

@[simp] theorem toVal_annot_val (a a2 b : List annot) (ds : List dyn_annotation) (v : value) :
    toVal (Expr a (Eannot ds (Expr a2 (Epure (Pexpr b () (PEval v)))))) = some (.annot ds v) := rfl

/-- A value expression IS the injection of its exact value. -/
theorem ofValA_of_toValA {e : CoreExpr} {w : SpikeValA}
    (h : toValA e = some w) : ofValA w = e := by
  unfold toValA at h
  split at h
  · cases h; rfl
  · cases h; rfl
  · cases h

/-- The exact injection is injective. -/
theorem ofValA_inj {w w' : SpikeValA} (h : ofValA w = ofValA w') : w = w' := by
  have := congrArg toValA h
  rw [toValA_ofValA, toValA_ofValA] at this
  exact Option.some.inj this

/-- The erased value test's witness: a value expression is `ofValA` of
    some exact value erasing to it (the pre-E1 `ofVal_of_toVal`, up to
    the annotation lists). -/
theorem ofValA_of_toVal {e : CoreExpr} {w : SpikeVal}
    (h : toVal e = some w) : ∃ wa : SpikeValA, wa.erase = w ∧ ofValA wa = e := by
  rw [toVal_eq_toValA] at h
  cases hA : toValA e with
  | none => rw [hA] at h; cases h
  | some wa =>
    rw [hA] at h
    exact ⟨wa, Option.some.inj h, ofValA_of_toValA hA⟩

theorem toValA_none_of_toVal_none {e : CoreExpr} (h : toVal e = none) : toValA e = none := by
  rw [toVal_eq_toValA] at h
  exact Option.map_eq_none_iff.mp h

theorem toVal_none_of_toValA_none {e : CoreExpr} (h : toValA e = none) : toVal e = none := by
  rw [toVal_eq_toValA, h]; rfl

/-- A value expression at the canonical (annotation-free) lists is the
    canonical injection (the pre-E1 `ofVal_of_toVal`, conditional). -/
theorem ofVal_of_toVal {e : CoreExpr} {w : SpikeVal}
    (h : toValA e = some w.canon) : ofVal w = e :=
  ofValA_of_toValA h

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

/-- THE RUN STATE'S LIVE SUPPLIES (E1, designed for E5 — see `Ctl.sup`):
    `core_run_state.sym_supply` and `.excluded_supply`, both `Nat`
    (Core_run_aux.lean:356–357). -/
structure RunSup where
  sym : Nat
  excl : Nat
  deriving DecidableEq, Inhabited

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
  /-- E1 (the emitted-Core dialect arc, `current_loc` LIVE): the thread's
      `current_loc` (Core_run_aux.lean:298). WRITTEN by step_ctx's general
      arm at every redex node whose annotations carry a non-library source
      location (`get_loc e_annots`, core_reduction.lem:1155–1164;
      Core_reduction.lean:484 `let maybe_loc := get_loc e_annots; let th_st
      := match maybe_loc with | none => th_st | some loc1 => if
      isLibraryLocation loc1 then th_st else { th_st with current_loc :=
      loc1 }`), READ by the PCALL push (`push_exec_loc psym
      th_st.current_loc …`, :1396), the action requests' library-location
      fallback (`requestLoc`), the memop request and the evaluator's
      undef payloads. The value arms (PROGRAM-DONE, RETURN, REMOVE-ANNOT,
      :1102–:1151) do not write it. `Ctl.upd a` is the mirror's image of
      that write (`locUpd`). -/
  curLoc : CerbLocation.Loc
  /-- E1 (designed in E1's shape for E5, DECISIONS "E0's TEN QUESTIONS
      RATIFIED" (4)): THE RUN STATE'S LIVE SUPPLIES — `core_run_state`'s
      `sym_supply` and `excluded_supply` (Core_run_aux.lean:356–357), which
      the negative-action protocol draws from (`E.fresh_symbol`,
      `E.fresh_excluded_id`, core_reduction.lem:1298–1301; E5). No E1 rule
      writes them (every E1 rule threads `ctl.sup` verbatim); they are
      carried here so that E5 adds RULES, not a configuration re-shape. The
      driver ties: `MachineCtx.Embeds` (Round.lean) reads them off
      `dst.core_run_state0`, `CerberusRound`/`loop_step_frag` fix the
      successor run state's two fields to the successor control's. -/
  sup : RunSup

/-- The engine's location write at a redex node: `get_loc a` (the FIRST
    `Aloc`, everything else skipped, Annot.lean:299; annot.lem:101–133),
    kept unless it is a library location (`CerbLocation.isLibraryLocation`,
    CerbLocation.lean:180). Verbatim the `let th_st := match maybe_loc …`
    of step_ctx's general arm (Core_reduction.lean:484). -/
def locUpd (a : List annot) (l : CerbLocation.Loc) : CerbLocation.Loc :=
  match get_loc a with
  | none => l
  | some loc => if CerbLocation.isLibraryLocation loc = true then l else loc

@[simp] theorem locUpd_nil (l : CerbLocation.Loc) : locUpd [] l = l := rfl

/-- The same write on the engine's thread (the shape the per-rule engine
    equations in Soundness.lean state their successor thread with). -/
def locUpdTh (a : List annot) (th : thread_state) : thread_state :=
  match get_loc a with
  | none => th
  | some loc => if CerbLocation.isLibraryLocation loc = true then th
                else { th with current_loc := loc }

@[simp] theorem locUpdTh_nil (th : thread_state) : locUpdTh [] th = th := rfl

namespace Ctl

/-- The control after a general-arm round at a redex node annotated `a`:
    only `curLoc` moves (`locUpd`). Every E1 leaf rule's successor control
    is `ctl.upd a`; the annotation-free spellings give `ctl.upd [] = ctl`
    definitionally. -/
def upd (c : Ctl) (a : List annot) : Ctl := { c with curLoc := locUpd a c.curLoc }

@[simp] theorem upd_nil (c : Ctl) : c.upd [] = c := rfl
@[simp] theorem upd_κ (c : Ctl) (a : List annot) : (c.upd a).κ = c.κ := rfl
@[simp] theorem upd_proc (c : Ctl) (a : List annot) : (c.upd a).proc = c.proc := rfl
@[simp] theorem upd_execLoc (c : Ctl) (a : List annot) : (c.upd a).execLoc = c.execLoc := rfl
@[simp] theorem upd_curLoc (c : Ctl) (a : List annot) : (c.upd a).curLoc = locUpd a c.curLoc := rfl
@[simp] theorem upd_sup (c : Ctl) (a : List annot) : (c.upd a).sup = c.sup := rfl
@[simp] theorem upd_mk (κ : List (Option sym × context)) (p : Option sym) (ℓ : exec_location)
    (lc : CerbLocation.Loc) (sp : RunSup) (a : List annot) :
    (Ctl.mk κ p ℓ lc sp).upd a = Ctl.mk κ p ℓ (locUpd a lc) sp := rfl

/-- The PCALL control (step_ctx's Eproc arm, Core_reduction.lean:484 col
    ≈18133; core_reduction.lem:1386–1400): at the redex node annotated `a`
    the location is written FIRST (the general arm's `th_st`), then the
    frame `(ctl.proc, ctx)` is pushed, the callee becomes current, and the
    execution location is pushed at the UPDATED `current_loc`. -/
def callPush (c : Ctl) (a : List annot) (ctx : context) (f : sym) : Ctl :=
  ⟨(c.proc, ctx) :: c.κ, some f, push_exec_loc f (locUpd a c.curLoc) c.execLoc,
   locUpd a c.curLoc, c.sup⟩

@[simp] theorem callPush_κ (c : Ctl) (a : List annot) (ctx : context) (f : sym) :
    (c.callPush a ctx f).κ = (c.proc, ctx) :: c.κ := rfl
@[simp] theorem callPush_proc (c : Ctl) (a : List annot) (ctx : context) (f : sym) :
    (c.callPush a ctx f).proc = some f := rfl
@[simp] theorem callPush_sup (c : Ctl) (a : List annot) (ctx : context) (f : sym) :
    (c.callPush a ctx f).sup = c.sup := rfl

/-- The engine's `stack` denoted by the control's `κ`
    (`Stack_cons2 p ctx` per entry, innermost first, over `Stack_empty`). -/
def toStack (c : Ctl) : _root_.stack core_run_annotation :=
  c.κ.foldr (fun pc sk => Stack_cons2 pc.1 pc.2 sk) Stack_empty

@[simp] theorem toStack_nil (p : Option sym) (ℓ : exec_location) (lc : CerbLocation.Loc)
    (sp : RunSup) : (Ctl.mk [] p ℓ lc sp).toStack = Stack_empty := rfl

/-- E1: the location write leaves the denoted stack alone. -/
@[simp] theorem toStack_upd (c : Ctl) (a : List annot) : (c.upd a).toStack = c.toStack := rfl

/-- E1: PCALL pushes the caller's frame onto the denoted stack. -/
@[simp] theorem toStack_callPush (c : Ctl) (a : List annot) (ctx : context) (f : sym) :
    (c.callPush a ctx f).toStack = Stack_cons2 c.proc ctx c.toStack := rfl

/-- `κ = []` is exactly `stack0 = Stack_empty`. -/
theorem toStack_eq_empty_iff (c : Ctl) : c.toStack = Stack_empty ↔ c.κ = [] := by
  obtain ⟨κ, p, ℓ, lc, sp⟩ := c
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
  /-- The run state's IMMUTABLE part: only `labeled` is read by the mirror
      (`labelsAt`); the two live supplies live in `Ctl.sup` (E1) and the
      driver ties fix only `labeled` to this field (`MachineCtx.Embeds`). -/
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
    current_loc := ctl.curLoc }

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

@[simp] theorem thread_current_loc (M : MachineCtx) (e : CoreExpr) (ρ : EnvStack) (ctl : Ctl) :
    (M.thread e ρ ctl).current_loc = ctl.curLoc := rfl

/-- THE LOCATION WRITE, mirror = engine: the engine's general-arm thread at
    a redex node annotated `a`, with the successor arena and env installed,
    IS the mirror's thread at the updated control. -/
theorem thread_upd (M : MachineCtx) (e e' : CoreExpr) (ρ ρ' : EnvStack) (ctl : Ctl)
    (a : List annot) :
    { locUpdTh a (M.thread e ρ ctl) with arena := e', env := ρ' } =
      M.thread e' ρ' (ctl.upd a) := by
  unfold locUpdTh Ctl.upd locUpd
  cases get_loc a with
  | none => rfl
  | some loc =>
    dsimp only
    by_cases h : CerbLocation.isLibraryLocation loc = true
    · simp only [if_pos h]; rfl
    · simp only [if_neg h]; rfl

/-- `thread_upd` with the env untouched (the arena-only successors). -/
theorem thread_upd_arena (M : MachineCtx) (e e' : CoreExpr) (ρ : EnvStack) (ctl : Ctl)
    (a : List annot) :
    { locUpdTh a (M.thread e ρ ctl) with arena := e' } = M.thread e' ρ (ctl.upd a) := by
  unfold locUpdTh Ctl.upd locUpd
  cases get_loc a with
  | none => rfl
  | some loc =>
    dsimp only
    by_cases h : CerbLocation.isLibraryLocation loc = true
    · simp only [if_pos h]; rfl
    · simp only [if_neg h]; rfl

/-- E1, THE DRIVER-THREAD FORM of the location write: at a thread whose
    `current_loc` is the control's, `locUpdTh` is the update to the
    updated control's `curLoc` (the driver lanes' tie `hcl`). -/
theorem locUpdTh_ctl {th₀ : thread_state} {ctl : Ctl} (hcl : th₀.current_loc = ctl.curLoc)
    (a : List annot) (e : CoreExpr) (ρ : EnvStack) :
    locUpdTh a { th₀ with arena := e, env := ρ } =
      { th₀ with arena := e, env := ρ, current_loc := (ctl.upd a).curLoc } := by
  unfold locUpdTh Ctl.upd locUpd
  cases get_loc a with
  | none => rw [← hcl]
  | some loc =>
    dsimp only
    rcases Bool.eq_false_or_eq_true (CerbLocation.isLibraryLocation loc) with h | h <;>
      simp only [h, Bool.false_eq_true, ↓reduceIte] <;> (try rw [← hcl]) <;> rfl

/-- The location write at the mirror's own thread literal: the updated
    thread IS the thread at the updated control (the one rewrite every
    round equation needs — the successor literals `{ locUpdTh a (M.thread
    e ρ ctl) with … }` then read `{ M.thread e ρ (ctl.upd a) with … }`,
    definitionally the mirror's successor thread). -/
theorem locUpdTh_thread (M : MachineCtx) (e : CoreExpr) (ρ : EnvStack) (ctl : Ctl)
    (a : List annot) : locUpdTh a (M.thread e ρ ctl) = M.thread e ρ (ctl.upd a) := by
  unfold locUpdTh Ctl.upd locUpd
  cases get_loc a with
  | none => rfl
  | some loc =>
    dsimp only
    by_cases h : CerbLocation.isLibraryLocation loc = true
    · simp only [if_pos h]
    · simp only [if_neg h]; rfl

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

/-- Values carry the exact value (E1: `SpikeValA`, the erased value with
    its static annotation lists), the final env, the TERMINAL control's
    procedure, execution location, current location and run supplies (E1:
    the two new `Ctl` fields), and the (unchanged) machine context
    (exported posts may project all of them away). A terminal has an
    EMPTY call stack by definition: a value at a non-empty stack is a
    RETURN redex, not a terminal (step_ctx's value arm at `Stack_cons2`,
    Core_reduction.lean:484), so `κ` has no slot here — `toValRt` answers
    `none` at `κ ≠ []`. -/
structure CoreRVal where
  w : SpikeValA
  ρ : EnvStack
  proc : Option sym
  execLoc : exec_location
  M : MachineCtx
  curLoc : CerbLocation.Loc
  sup : RunSup

/-- The terminal control a value sits at (empty stack). -/
def CoreRVal.ctl (v : CoreRVal) : Ctl := ⟨[], v.proc, v.execLoc, v.curLoc, v.sup⟩

/-- The delivered engine value of a runtime value (annotations and
    env erased — the D1 readout). -/
def CoreRVal.val (v : CoreRVal) : value := v.w.val

/-- The erased value of a runtime value (what a postcondition
    `Ψ : SpikeVal → …` is applied to). -/
def CoreRVal.sv (v : CoreRVal) : SpikeVal := v.w.erase

@[simp] theorem CoreRVal.val_eq_sv_val (v : CoreRVal) : v.val = v.sv.val := rfl

/-- Annotation-merge on runtime values: componentwise `SpikeValA.merge`
    (the env, control and label map ride — annotation reduction never
    touches them). -/
def CoreRVal.merge (a : List annot) (ds : List dyn_annotation) (v : CoreRVal) : CoreRVal :=
  ⟨SpikeValA.merge a ds v.w, v.ρ, v.proc, v.execLoc, v.M, v.curLoc, v.sup⟩

@[simp] theorem CoreRVal.merge_mk (a : List annot) (ds : List dyn_annotation) (w : SpikeValA)
    (ρ : EnvStack) (p : Option sym) (ℓ : exec_location) (M : MachineCtx)
    (lc : CerbLocation.Loc) (sp : RunSup) :
    CoreRVal.merge a ds ⟨w, ρ, p, ℓ, M, lc, sp⟩ = ⟨SpikeValA.merge a ds w, ρ, p, ℓ, M, lc, sp⟩ := rfl

@[simp] theorem CoreRVal.val_merge (a : List annot) (ds : List dyn_annotation) (v : CoreRVal) :
    (CoreRVal.merge a ds v).val = v.val := by
  cases v; simp [CoreRVal.merge, CoreRVal.val]

@[simp] theorem CoreRVal.sv_merge (a : List annot) (ds : List dyn_annotation) (v : CoreRVal) :
    (CoreRVal.merge a ds v).sv = SpikeVal.merge ds v.sv := by
  cases v; simp [CoreRVal.merge, CoreRVal.sv]

@[simp] theorem CoreRVal.ρ_merge (a : List annot) (ds : List dyn_annotation) (v : CoreRVal) :
    (CoreRVal.merge a ds v).ρ = v.ρ := by
  cases v; rfl

/-- Componentwise value test (Language-side `toVal`): a value at an
    EMPTY call stack is terminal; at a non-empty stack nothing is
    (the RETURN redex — C2's `Step.ret`). -/
def toValRt (r : CoreRt) : Option CoreRVal :=
  match r.ctl.κ with
  | [] => (toValA r.e).map fun w => ⟨w, r.ρ, r.ctl.proc, r.ctl.execLoc, r.M, r.ctl.curLoc, r.ctl.sup⟩
  | _ :: _ => none

/-- Componentwise value injection (Language-side `ofVal`): at the
    terminal (empty-stack) control, at the value's own annotation lists. -/
def ofValRt (v : CoreRVal) : CoreRt :=
  ⟨ofValA v.w, v.ρ, ⟨[], v.proc, v.execLoc, v.curLoc, v.sup⟩, v.M⟩

@[simp] theorem toValRt_mk (e : CoreExpr) (ρ : EnvStack) (p : Option sym)
    (ℓ : exec_location) (lc : CerbLocation.Loc) (sp : RunSup) (M : MachineCtx) :
    toValRt ⟨e, ρ, ⟨[], p, ℓ, lc, sp⟩, M⟩ =
      (toValA e).map fun w => ⟨w, ρ, p, ℓ, M, lc, sp⟩ := rfl

@[simp] theorem toValRt_mk_cons (e : CoreExpr) (ρ : EnvStack) (pc : Option sym × context)
    (κ : List (Option sym × context)) (p : Option sym) (ℓ : exec_location)
    (lc : CerbLocation.Loc) (sp : RunSup) (M : MachineCtx) :
    toValRt ⟨e, ρ, ⟨pc :: κ, p, ℓ, lc, sp⟩, M⟩ = none := rfl

/-- A non-value expression is a non-value tuple at every control. -/
theorem toValRt_eq_none_of_toVal_none {r : CoreRt} (h : toVal r.e = none) :
    toValRt r = none := by
  obtain ⟨e, ρ, ⟨κ, p, ℓ, lc, sp⟩, M⟩ := r
  cases κ with
  | nil => rw [toValRt_mk]; simp only at h; rw [toValA_none_of_toVal_none h]; rfl
  | cons pc κ => rfl

/-- At the terminal control the tuple's value test is the expression's. -/
theorem toValRt_of_κ_nil {r : CoreRt} (h : r.ctl.κ = []) :
    toValRt r = (toValA r.e).map fun w =>
      ⟨w, r.ρ, r.ctl.proc, r.ctl.execLoc, r.M, r.ctl.curLoc, r.ctl.sup⟩ := by
  obtain ⟨e, ρ, ⟨κ, p, ℓ, lc, sp⟩, M⟩ := r
  simp only at h
  subst h
  rfl

@[simp] theorem ofValRt_mk (w : SpikeValA) (ρ : EnvStack) (p : Option sym)
    (ℓ : exec_location) (M : MachineCtx) (lc : CerbLocation.Loc) (sp : RunSup) :
    ofValRt ⟨w, ρ, p, ℓ, M, lc, sp⟩ = ⟨ofValA w, ρ, ⟨[], p, ℓ, lc, sp⟩, M⟩ := rfl

@[simp] theorem toValRt_ofValRt (v : CoreRVal) : toValRt (ofValRt v) = some v := by
  obtain ⟨w, ρ, p, ℓ, M, lc, sp⟩ := v
  rw [ofValRt_mk, toValRt_mk, toValA_ofValA]
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
  | Expr _ (Ebound b) => jumpRedex? b
  | _ => none

/-- E1: the `Cbound` frame joins the spine (get_ctx's `Ebound` arm,
    core_reduction.lem:563–568: descend when the body is reducible —
    every spine body here is a non-value). -/
@[simp] theorem jumpRedex?_bound (a : List annot) (b : CoreExpr) :
    jumpRedex? (Expr a (Ebound b)) = jumpRedex? b := rfl

/-- The static annotation list of a node (E1): what `Ctl.upd` reads at a
    root redex. -/
def rootAnnots : CoreExpr → List annot
  | Expr a _ => a

@[simp] theorem rootAnnots_mk (a : List annot) (e : generic_expr_ core_run_annotation Unit sym) :
    rootAnnots (Expr a e) = a := rfl

/-- THE REDEX NODE'S ANNOTATIONS (E1): the static annotation list of the
    node at the end of get_ctx's decomposition path (Esseq-left, Ewseq-left,
    the guarded `Eannot` descent, the `Ebound` descent — core_reduction.lem:
    524–575), i.e. of the `Expr e_annots expr_` step_ctx's general arm
    binds and reads `get_loc` from. Meaningful where the path ends in a
    reducible node (the `run`/`call` rules); a double-annot root is the
    ANNOTS-merge redex itself. -/
def redexAnnots : CoreExpr → List annot
  | Expr a (Esseq _ e1 _) => if (toVal e1).isSome then a else redexAnnots e1
  | Expr a (Ewseq _ e1 _) => if (toVal e1).isSome then a else redexAnnots e1
  | Expr a (Eannot _ b) => if annotRooted b then a else redexAnnots b
  | Expr a (Ebound b) => if (toVal b).isSome then a else redexAnnots b
  | Expr a _ => a

@[simp] theorem redexAnnots_run (a : List annot) (ra : core_run_annotation) (l : sym)
    (pes : List (generic_pexpr Unit sym)) : redexAnnots (Expr a (Erun ra l pes)) = a := rfl

@[simp] theorem redexAnnots_proc (a : List annot) (ra : core_run_annotation) (nm : generic_name sym)
    (pes : List (generic_pexpr Unit sym)) : redexAnnots (Expr a (Eproc ra nm pes)) = a := rfl

theorem redexAnnots_sseq (a : List annot) (pat : pattern) (e1 e2 : CoreExpr) :
    redexAnnots (Expr a (Esseq pat e1 e2)) =
      if (toVal e1).isSome then a else redexAnnots e1 := rfl

theorem redexAnnots_wseq (a : List annot) (pat : pattern) (e1 e2 : CoreExpr) :
    redexAnnots (Expr a (Ewseq pat e1 e2)) =
      if (toVal e1).isSome then a else redexAnnots e1 := rfl

theorem redexAnnots_annot (a : List annot) (ds : List dyn_annotation) (b : CoreExpr) :
    redexAnnots (Expr a (Eannot ds b)) = if annotRooted b then a else redexAnnots b := rfl

theorem redexAnnots_bound (a : List annot) (b : CoreExpr) :
    redexAnnots (Expr a (Ebound b)) = if (toVal b).isSome then a else redexAnnots b := rfl

@[simp] theorem redexAnnots_sseq_of_nv {e1 : CoreExpr} (a : List annot) (pat : pattern)
    (e2 : CoreExpr) (h : toVal e1 = none) :
    redexAnnots (Expr a (Esseq pat e1 e2)) = redexAnnots e1 := by
  rw [redexAnnots_sseq, h]; rfl

@[simp] theorem redexAnnots_wseq_of_nv {e1 : CoreExpr} (a : List annot) (pat : pattern)
    (e2 : CoreExpr) (h : toVal e1 = none) :
    redexAnnots (Expr a (Ewseq pat e1 e2)) = redexAnnots e1 := by
  rw [redexAnnots_wseq, h]; rfl

@[simp] theorem redexAnnots_annot_of_not_root {b : CoreExpr} (a : List annot)
    (ds : List dyn_annotation) (h : annotRooted b = false) :
    redexAnnots (Expr a (Eannot ds b)) = redexAnnots b := by
  rw [redexAnnots_annot, h]; rfl

@[simp] theorem redexAnnots_bound_of_nv {b : CoreExpr} (a : List annot) (h : toVal b = none) :
    redexAnnots (Expr a (Ebound b)) = redexAnnots b := by
  rw [redexAnnots_bound, h]; rfl

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
  | Expr a (Ebound b) => (callRedex? b).map fun q => (Cbound a q.1, q.2)
  | _ => none

/-- E1: the `Cbound` frame (get_ctx's `Ebound` arm, core_reduction.lem:
    563–568; `apply_ctx (Cbound annot ctx') e = Expr annot (Ebound …)`,
    :618–619). -/
@[simp] theorem callRedex?_bound (a : List annot) (b : CoreExpr) :
    callRedex? (Expr a (Ebound b)) = (callRedex? b).map fun q => (Cbound a q.1, q.2) := rfl

theorem callRedex?_body_none_of_bound {a : List annot} {b : CoreExpr}
    (h : callRedex? (Expr a (Ebound b)) = none) : callRedex? b = none := by
  rw [callRedex?_bound] at h
  exact Option.map_eq_none_iff.mp h

theorem callRedex?_bound_none {a : List annot} {b : CoreExpr}
    (h : callRedex? b = none) : callRedex? (Expr a (Ebound b)) = none := by
  rw [callRedex?_bound, h]; rfl

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
  | Expr a (Ebound b), lp, h => by
      rw [jumpRedex?_bound] at h
      rw [callRedex?_bound, callRedex?_none_of_jumpRedex?_some h]; rfl
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

/-! ## The pure-expression depth measure (E2: moved here from
Soundness.lean, extended to the loaded-value grammar)

`peDepth` bounds the per-level fuel draw of the engine's
`step_eval_pexpr`/`pull_constrained` (both recurse one fuel level per
operand level) AND, since E2, the number of evaluator PASSES (iterations
of `eval_pexpr_aux2`, Core_eval.lean:152): the arms that return an
UNEVALUATED pexpr — `PEcase` (the selected branch, core_eval.lem:725–745)
and the operand REBUILDS at a non-value operand — strictly decrease it
(`stepPexpr_depth_lt`, Soundness.lean), so `peDepth pe ≤ lemDefaultFuel`
bounds every pass's depth and the pass count at once. The measure is a
SUM at the two constructs whose operand keeps evaluating beside a large
sibling (`PEcase`'s scrutinee beside its alternatives, `PEif`'s guard
beside its branches) and a MAX elsewhere — a max would not decrease when
the sibling dominates. The pre-E2 equations (`peDepth_op`,
`peDepth_array_shift`, `peDepth_ctor1`, `peDepth_val`) hold verbatim. -/
mutual
def peDepth : generic_pexpr Unit sym → Nat
  | Pexpr _ _ (PEop _ pe1 pe2) => 1 + max (peDepth pe1) (peDepth pe2)
  | Pexpr _ _ (PEarray_shift pe1 _ pe2) => 1 + max (peDepth pe1) (peDepth pe2)
  | Pexpr _ _ (PEctor _ pes) => 1 + peDepthList pes
  | Pexpr _ _ (PEcase pe pats) => 1 + peDepth pe + peDepthAlts pats
  | Pexpr _ _ (PEnot pe) => 1 + peDepth pe
  | Pexpr _ _ (PEif pe1 pe2 pe3) => 1 + peDepth pe1 + max (peDepth pe2) (peDepth pe3)
  | _ => 1

/-- SUM of the depths of an operand list (0 at nil) — a sum so that a
    pass strictly decreases it whenever one operand strictly decreases
    and none increases. -/
def peDepthList : List (generic_pexpr Unit sym) → Nat
  | [] => 0
  | pe :: pes => peDepth pe + peDepthList pes

/-- Max depth of a case alternative list's bodies (0 at nil). -/
def peDepthAlts : List (pattern × generic_pexpr Unit sym) → Nat
  | [] => 0
  | (_, pe) :: rest => max (peDepth pe) (peDepthAlts rest)
end

@[simp] theorem peDepth_val (a : List annot) (v : value) :
    peDepth (Pexpr a () (PEval v)) = 1 := rfl

@[simp] theorem peDepth_sym (a : List annot) (x : sym) :
    peDepth (Pexpr a () (PEsym x)) = 1 := rfl

@[simp] theorem peDepth_undef (a : List annot) (loc : CerbLocation.Loc) (ub : undefined_behaviour) :
    peDepth (Pexpr a () (PEundef loc ub)) = 1 := rfl

@[simp] theorem peDepth_op (a : List annot) (op : binop)
    (pe1 pe2 : generic_pexpr Unit sym) :
    peDepth (Pexpr a () (PEop op pe1 pe2)) =
      1 + max (peDepth pe1) (peDepth pe2) := rfl

@[simp] theorem peDepth_array_shift (a : List annot) (ty : ctype)
    (pe1 pe2 : generic_pexpr Unit sym) :
    peDepth (Pexpr a () (PEarray_shift pe1 ty pe2)) =
      1 + max (peDepth pe1) (peDepth pe2) := rfl

@[simp] theorem peDepth_ctor (a : List annot) (c : ctor)
    (pes : List (generic_pexpr Unit sym)) :
    peDepth (Pexpr a () (PEctor c pes)) = 1 + peDepthList pes := rfl

@[simp] theorem peDepth_ctor1 (a : List annot) (c : ctor)
    (pe : generic_pexpr Unit sym) :
    peDepth (Pexpr a () (PEctor c [pe])) = 1 + peDepth pe := by
  simp [peDepth, peDepthList]

@[simp] theorem peDepth_case (a : List annot) (pe : generic_pexpr Unit sym)
    (pats : List (pattern × generic_pexpr Unit sym)) :
    peDepth (Pexpr a () (PEcase pe pats)) = 1 + peDepth pe + peDepthAlts pats := rfl

@[simp] theorem peDepth_not (a : List annot) (pe : generic_pexpr Unit sym) :
    peDepth (Pexpr a () (PEnot pe)) = 1 + peDepth pe := rfl

@[simp] theorem peDepth_if (a : List annot) (pe1 pe2 pe3 : generic_pexpr Unit sym) :
    peDepth (Pexpr a () (PEif pe1 pe2 pe3)) =
      1 + peDepth pe1 + max (peDepth pe2) (peDepth pe3) := rfl

@[simp] theorem peDepthList_nil : peDepthList [] = 0 := rfl
@[simp] theorem peDepthList_cons (pe : generic_pexpr Unit sym)
    (pes : List (generic_pexpr Unit sym)) :
    peDepthList (pe :: pes) = peDepth pe + peDepthList pes := rfl
@[simp] theorem peDepthAlts_nil : peDepthAlts [] = 0 := rfl
@[simp] theorem peDepthAlts_cons (pat : pattern) (pe : generic_pexpr Unit sym)
    (rest : List (pattern × generic_pexpr Unit sym)) :
    peDepthAlts ((pat, pe) :: rest) = max (peDepth pe) (peDepthAlts rest) := rfl

theorem peDepth_pos (pe : generic_pexpr Unit sym) : 1 ≤ peDepth pe := by
  rcases pe with ⟨a, u, pe_⟩
  cases pe_ <;> simp [peDepth] <;> omega

theorem peDepth_le_list_of_mem {pe : generic_pexpr Unit sym}
    {pes : List (generic_pexpr Unit sym)} (h : pe ∈ pes) :
    peDepth pe ≤ peDepthList pes := by
  induction pes with
  | nil => cases h
  | cons q qs ih =>
    rw [peDepthList_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · omega
    · have := ih h'; omega

theorem peDepth_le_alts_of_mem {pat : pattern} {pe : generic_pexpr Unit sym}
    {pats : List (pattern × generic_pexpr Unit sym)} (h : (pat, pe) ∈ pats) :
    peDepth pe ≤ peDepthAlts pats := by
  induction pats with
  | nil => cases h
  | cons q qs ih =>
    obtain ⟨qp, qe⟩ := q
    rw [peDepthAlts_cons]
    rcases List.mem_cons.mp h with heq | h'
    · cases heq; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h') (Nat.le_max_right _ _)

/-! ## The pure evaluator

Two functions mirror the engine's evaluator tower (Core_eval.lean:135–158 /
core_eval.lem:536–1140):

* `stepPexpr` is ONE PASS of `step_eval_pexpr` on the covered grammar,
  FAITHFUL to the pass structure: an arm whose operands all reach values
  in the pass delivers the value (`valPe v`); the arms that return an
  UNEVALUATED pexpr — `PEcase` at a value scrutinee returns the selected
  branch `strip pe''` (core_eval.lem:736–740, `Pexpr [] () <$>`), `PEif`
  returns the pass on the chosen branch (`strip <$> self pe2`, :1015–1018),
  and every arm at a NON-value operand REBUILDS the node around the
  operands' pass results (`PEop binop pe1' pe2'`, :533; `PEctor ctor pes'`,
  :722; `PEcase pe' pat_pes`, :743; `PEnot pe'`, :815; `PEif pe1' pe2 pe3`,
  :1046; `PEarray_shift pe1' ty pe2'`, :759) — are mirrored EXACTLY, so
  the mirror's successive passes are the engine's. Every engine KILL
  (`Illformed_program …`), UNDEF (`PEundef`, `Undefined.undef loc' [ub]`,
  :596–604) and PANIC (`PEcase` without a matching pattern, :741) is `none`
  here (fail-closed) and classified in EvalClass.lean. Certified pass by
  pass against `step_eval_pexpr` in Soundness.lean (`step_eval_bridge`).
* `evalPexpr` is the BIG-STEP value: structural over the operands
  (`PEop`, `PEarray_shift`, `PEctor`, `PEnot`, `PEif`) and, at `PEcase`,
  the value of the selected branch — GUARDED by grammar membership of the
  alternatives (`isPePureAlts pats`; likewise both branches of a pure `if`,
  so that a big-step value implies the covered shape of the WHOLE term,
  unselected branches included — `evalPexpr_shape`) and by the depth check
  `peDepth (reannot0 pe'') ≤ peDepthAlts pats` (the substituted branch's
  depth does not exceed the alternatives' — true of every substitution
  the engine performs, symbols for values, but stated as a CHECK rather
  than proved through the fuelled `subst_sym_pexpr`: [USER 2026-09-04]
  E0 question 8, the substitution-size lemma is carried locally). The
  check is what makes `evalPexpr` a well-founded recursion on `peDepth`
  and what bounds the engine's PASS COUNT by `peDepth pe`
  (`stepPexpr_depth_lt`, Soundness.lean). The mirror rules consume
  `evalPexpr`; its pre-E2 equations (`evalPexpr_val`/`_sym`/`_op`/
  `_array_shift`/`_tyctor`) are unchanged in statement.

The two agree on successes: a pass preserves the big-step value
(`evalPexpr_step`), so the engine's iteration until a value delivers
`evalPexpr`'s answer (`aux2_bridge`). -/

/-- The engine's canonical value pexpr (`mk_value_pe`, Core_aux.lean:302). -/
def valPe (v : value) : generic_pexpr Unit sym := Pexpr [] () (PEval v)

/-- The engine's `Pexpr [] () (strip1 pe)` — the outer annotation list
    and type annotation reset (step_eval_pexpr's result wrapper,
    Core_eval.lean:142). -/
def reannot0 : generic_pexpr Unit sym → generic_pexpr Unit sym
  | Pexpr _ _ p => Pexpr [] () p

@[simp] theorem reannot0_mk (a : List annot) (u : Unit) (p : generic_pexpr_ Unit sym) :
    reannot0 (Pexpr a u p) = Pexpr [] () p := rfl

@[simp] theorem valueFromPexpr_valPe (v : value) : valueFromPexpr (valPe v) = some v := rfl

/-- The type-argument constructors at a literal ctype: E1's `Ivalignof`/
    `Ivsizeof` and (E2) `Unspecified(ty)` — `Cunspecified [Vctype ty] ↦
    Vloaded (LVunspecified ty)` (core_eval.lem:682–683). -/
def isTyCtor : ctor → Bool
  | .Civalignof => true
  | .Civsizeof => true
  | .Cunspecified => true
  | _ => false

/-- The value of a type-argument constructor at a ctype. -/
def evalTyCtor (tds : CerbTags.TagDefsMap) : ctor → ctype → Option value
  | .Civalignof, ty => some (Vobject (OVinteger (CerbMem.alignofIval tds ty)))
  | .Civsizeof, ty => some (Vobject (OVinteger (CerbMem.sizeofIval tds ty)))
  | .Cunspecified, ty => some (Vloaded (LVunspecified ty))
  | _, _ => none

@[simp] theorem evalTyCtor_alignof (tds : CerbTags.TagDefsMap) (ty : ctype) :
    evalTyCtor tds .Civalignof ty = some (Vobject (OVinteger (CerbMem.alignofIval tds ty))) := rfl

@[simp] theorem evalTyCtor_sizeof (tds : CerbTags.TagDefsMap) (ty : ctype) :
    evalTyCtor tds .Civsizeof ty = some (Vobject (OVinteger (CerbMem.sizeofIval tds ty))) := rfl

@[simp] theorem evalTyCtor_unspecified (tds : CerbTags.TagDefsMap) (ty : ctype) :
    evalTyCtor tds .Cunspecified ty = some (Vloaded (LVunspecified ty)) := rfl

theorem evalTyCtor_isSome {tds : CerbTags.TagDefsMap} {c : ctor} {ty : ctype} {v : value}
    (h : evalTyCtor tds c ty = some v) : isTyCtor c = true := by
  cases c <;> first | rfl | (cases h)

/-- The constructor dispatch at evaluated operands — the `PEctor` arm's
    value match (core_eval.lem:607–723, Core_eval.lean:145), on the
    constructors the mirror covers: the type-argument constructors
    (`evalTyCtor`), `Cspecified [Vobject ov] ↦ Vloaded (LVspecified ov)`
    (:680–681), `Ctuple cvals ↦ Vtuple cvals` (:614–615). Every other
    (constructor, operand) pairing is `none`: the engine's success arms
    outside the mirror (`Cnil`/`Ccons`/`Carray`/the bitwise constants/
    `Cfvfromint`/`Civfromfloat`/`CivNULLcap`) and its ill-typed KILL
    (`(_, Just cvals)`, :720–722) are classified in EvalClass.lean. -/
def evalCtor (tds : CerbTags.TagDefsMap) : ctor → List value → Option value
  | .Civalignof, [Vctype ty] => evalTyCtor tds .Civalignof ty
  | .Civsizeof, [Vctype ty] => evalTyCtor tds .Civsizeof ty
  | .Cunspecified, [Vctype ty] => evalTyCtor tds .Cunspecified ty
  | .Cspecified, [Vobject ov] => some (Vloaded (LVspecified ov))
  | .Ctuple, vs => some (Vtuple vs)
  | _, _ => none

@[simp] theorem evalCtor_spec (tds : CerbTags.TagDefsMap) (ov : object_value) :
    evalCtor tds .Cspecified [Vobject ov] = some (Vloaded (LVspecified ov)) := rfl

@[simp] theorem evalCtor_tuple (tds : CerbTags.TagDefsMap) (vs : List value) :
    evalCtor tds .Ctuple vs = some (Vtuple vs) := rfl

theorem evalCtor_tyCtor (tds : CerbTags.TagDefsMap) {c : ctor} (hc : isTyCtor c = true)
    (ty : ctype) : evalCtor tds c [Vctype ty] = evalTyCtor tds c ty := by
  cases c <;> first | rfl | (cases hc)

/-- The binops the mirror evaluator covers (`evalBinop`): integer
    arithmetic `Add`/`Sub`/`Mul` and the comparisons
    `Eq`/`Lt`/`Le`/`Gt`/`Ge`. `Div`/`Rem_t`/`Rem_f`/`Exp`/`And`/`Or` are
    outside (fragment closure, 2026-09-02: the operand grammar is
    declared as exactly what the mirror covers). -/
def isMirroredOp : binop → Bool
  | .OpAdd | .OpSub | .OpMul | .OpEq | .OpLt | .OpLe | .OpGt | .OpGe => true
  | _ => false

/-- E2: the constructors the mirror evaluator covers (`evalCtor`): the
    type-argument constants, `Specified`, tuples. -/
def isMirroredCtor : ctor → Bool
  | .Civalignof | .Civsizeof | .Cunspecified | .Cspecified | .Ctuple => true
  | _ => false

/-! Boolean membership in the covered operand grammar (the Prop form is
`PePure`, Soundness.lean; `PePure.of_isPePure`/`isPePure_of_PePure` relate
them). Kernel-decidable at authored operands. E2: the one-pass mirror is
GUARDED by it at every pass (`stepPexpr`), which is what makes a pass's
success imply the covered shape without any lemma about the engine's
substitution. -/
mutual
def isPePure : generic_pexpr Unit sym → Bool
  | Pexpr _ _ (PEval _) => true
  | Pexpr _ _ (PEsym _) => true
  | Pexpr _ _ (PEop op pe1 pe2) => isMirroredOp op && isPePure pe1 && isPePure pe2
  | Pexpr _ _ (PEarray_shift pe1 _ pe2) => isPePure pe1 && isPePure pe2
  | Pexpr _ _ (PEctor c pes) => isMirroredCtor c && isPePureList pes
  | Pexpr _ _ (PEcase pe pats) => isPePure pe && isPePureAlts pats
  | Pexpr _ _ (PEnot pe) => isPePure pe
  | Pexpr _ _ (PEif pe1 pe2 pe3) => isPePure pe1 && isPePure pe2 && isPePure pe3
  | Pexpr _ _ (PEundef _ _) => true
  | _ => false

def isPePureList : List (generic_pexpr Unit sym) → Bool
  | [] => true
  | pe :: pes => isPePure pe && isPePureList pes

def isPePureAlts : List (pattern × generic_pexpr Unit sym) → Bool
  | [] => true
  | (_, pe) :: rest => isPePure pe && isPePureAlts rest
end

mutual
/-- ONE PASS of `step_eval_pexpr`, UNGUARDED (module section header):
    faithful to the engine's pass on the covered constructors, `none` at
    the engine's kills/undefs/panics and off the grammar. -/
def stepPexprRaw (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack) :
    generic_pexpr Unit sym → Option (generic_pexpr Unit sym)
  | Pexpr _ _ (PEval v) => some (valPe v)
  | Pexpr _ _ (PEsym x) => (lookup_env (resolveExtern ext x) ρ).map valPe
  | Pexpr _ _ (PEop op pe1 pe2) => do
      let r1 ← stepPexprRaw tds ext ρ pe1
      let r2 ← stepPexprRaw tds ext ρ pe2
      match valueFromPexpr r1, valueFromPexpr r2 with
      | some v1, some v2 => (evalBinop op v1 v2).map valPe
      | _, _ => some (Pexpr [] () (PEop op r1 r2))
  | Pexpr _ _ (PEarray_shift pe1 ty pe2) => do
      let r1 ← stepPexprRaw tds ext ρ pe1
      let r2 ← stepPexprRaw tds ext ρ pe2
      match valueFromPexpr r1, valueFromPexpr r2 with
      | some v1, some v2 => (evalArrayShift tds ty v1 v2).map valPe
      | _, _ => some (Pexpr [] () (PEarray_shift r1 ty r2))
  | Pexpr _ _ (PEctor c pes) => do
      let rs ← stepPexprsRaw tds ext ρ pes
      match valueFromPexprs rs with
      | some vs => (evalCtor tds c vs).map valPe
      | none => some (Pexpr [] () (PEctor c rs))
  | Pexpr _ _ (PEcase pe pats) => do
      let r ← stepPexprRaw tds ext ρ pe
      match valueFromPexpr r with
      | some cval => (select_case subst_sym_pexpr cval pats).map reannot0
      | none => some (Pexpr [] () (PEcase r pats))
  | Pexpr _ _ (PEnot pe) => do
      let r ← stepPexprRaw tds ext ρ pe
      match valueFromPexpr r with
      | some Vtrue => some (valPe Vfalse)
      | some Vfalse => some (valPe Vtrue)
      | some _ => none
      | none => some (Pexpr [] () (PEnot r))
  | Pexpr _ _ (PEif pe1 pe2 pe3) => do
      let r1 ← stepPexprRaw tds ext ρ pe1
      match valueFromPexpr r1 with
      | some Vtrue => (stepPexprRaw tds ext ρ pe2).map reannot0
      | some Vfalse => (stepPexprRaw tds ext ρ pe3).map reannot0
      | some _ => none
      | none => some (Pexpr [] () (PEif r1 pe2 pe3))
  | _ => none

/-- The pass mapped over an operand list (the engine's
    `exception_undef_mapM self pes`). -/
def stepPexprsRaw (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack) :
    List (generic_pexpr Unit sym) → Option (List (generic_pexpr Unit sym))
  | [] => some []
  | pe :: pes => do
      let r ← stepPexprRaw tds ext ρ pe
      let rs ← stepPexprsRaw tds ext ρ pes
      some (r :: rs)
end

/-- ONE PASS of `step_eval_pexpr` on the covered grammar: the faithful
    pass, GUARDED by grammar membership (`isPePure`) — so a pass succeeds
    only at a covered term, and the term the engine iterates on next is
    covered exactly when the mirror's next pass succeeds. -/
def stepPexpr (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack)
    (pe : generic_pexpr Unit sym) : Option (generic_pexpr Unit sym) :=
  if isPePure pe then stepPexprRaw tds ext ρ pe else none

/-! THE BIG-STEP VALUE (module section header): what the mirror rules
consume. Mutually recursive with its list form, well-founded on the depth (a
pexpr weighs `2 * peDepth`, an operand list `2 * peDepthList + 1`). -/
mutual
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
  | Pexpr _ _ (PEctor c pes) => do
      let vs ← evalPexprList tds ext ρ pes
      evalCtor tds c vs
  | Pexpr _ _ (PEcase pe pats) =>
      if isPePureAlts pats then do
        let cval ← evalPexpr tds ext ρ pe
        let pe'' ← select_case subst_sym_pexpr cval pats
        if peDepth (reannot0 pe'') ≤ peDepthAlts pats then evalPexpr tds ext ρ (reannot0 pe'')
        else none
      else none
  | Pexpr _ _ (PEnot pe) => do
      let v ← evalPexpr tds ext ρ pe
      match v with
      | Vtrue => some Vfalse
      | Vfalse => some Vtrue
      | _ => none
  | Pexpr _ _ (PEif pe1 pe2 pe3) =>
      if isPePure pe2 && isPePure pe3 then do
        let b ← evalPexpr tds ext ρ pe1
        match b with
        | Vtrue => evalPexpr tds ext ρ pe2
        | Vfalse => evalPexpr tds ext ρ pe3
        | _ => none
      else none
  | _ => none
termination_by pe => 2 * peDepth pe
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (simp only [peDepth]; omega)
    | (simp only [peDepth, peDepthList_cons]; omega)
    | (rename_i h; simp only [peDepth]; omega)

/-- The big-step values of an operand list (all or nothing). -/
def evalPexprList (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack) :
    List (generic_pexpr Unit sym) → Option (List value)
  | [] => some []
  | pe :: pes => do
      let v ← evalPexpr tds ext ρ pe
      let vs ← evalPexprList tds ext ρ pes
      some (v :: vs)
termination_by pes => 2 * peDepthList pes + 1
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := peDepth_pos pe; omega)
end

/-! ### The big-step equations (statements as before E2) -/

@[simp] theorem evalPexpr_val (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack)
    (a : List annot) (v : value) :
    evalPexpr tds ext ρ (Pexpr a () (PEval v)) = some v := by
  rw [evalPexpr]

@[simp] theorem evalPexpr_valPe (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack)
    (v : value) : evalPexpr tds ext ρ (valPe v) = some v := by
  rw [valPe, evalPexpr]

@[simp] theorem evalPexpr_sym (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack)
    (a : List annot) (x : sym) :
    evalPexpr tds ext ρ (Pexpr a () (PEsym x)) =
      lookup_env (resolveExtern ext x) ρ := by
  rw [evalPexpr]

/-- ... at the empty extern the indirection is the identity (the
    frozen profiles' instance). -/
@[simp] theorem evalPexpr_sym_empty (tds : CerbTags.TagDefsMap) (ρ : EnvStack)
    (a : List annot) (x : sym) :
    evalPexpr tds fmapEmpty ρ (Pexpr a () (PEsym x)) = lookup_env x ρ := by
  rw [evalPexpr_sym]; rfl

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
      evalBinop op v1 v2) := by
  rw [evalPexpr]

theorem evalPexpr_array_shift (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack)
    (a : List annot) (ty : ctype)
    (pe1 pe2 : generic_pexpr Unit sym) :
    evalPexpr tds ext ρ (Pexpr a () (PEarray_shift pe1 ty pe2)) = (do
      let v1 ← evalPexpr tds ext ρ pe1
      let v2 ← evalPexpr tds ext ρ pe2
      evalArrayShift tds ty v1 v2) := by
  rw [evalPexpr]

theorem evalPexpr_ctor (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack)
    (a : List annot) (c : ctor) (pes : List (generic_pexpr Unit sym)) :
    evalPexpr tds ext ρ (Pexpr a () (PEctor c pes)) = (do
      let vs ← evalPexprList tds ext ρ pes
      evalCtor tds c vs) := by
  rw [evalPexpr]

@[simp] theorem evalPexprList_nil (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack) :
    evalPexprList tds ext ρ [] = some [] := by
  rw [evalPexprList]

theorem evalPexprList_cons (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack)
    (pe : generic_pexpr Unit sym) (pes : List (generic_pexpr Unit sym)) :
    evalPexprList tds ext ρ (pe :: pes) = (do
      let v ← evalPexpr tds ext ρ pe
      let vs ← evalPexprList tds ext ρ pes
      some (v :: vs)) := by
  rw [evalPexprList]

theorem evalPexpr_ctor1 (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack)
    (a : List annot) (c : ctor) (pe : generic_pexpr Unit sym) :
    evalPexpr tds ext ρ (Pexpr a () (PEctor c [pe])) = (do
      let v ← evalPexpr tds ext ρ pe
      evalCtor tds c [v]) := by
  rw [evalPexpr_ctor, evalPexprList_cons, evalPexprList_nil]
  cases evalPexpr tds ext ρ pe <;> rfl

theorem evalPexpr_ctor2 (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack)
    (a : List annot) (c : ctor) (pe1 pe2 : generic_pexpr Unit sym) :
    evalPexpr tds ext ρ (Pexpr a () (PEctor c [pe1, pe2])) = (do
      let v1 ← evalPexpr tds ext ρ pe1
      let v2 ← evalPexpr tds ext ρ pe2
      evalCtor tds c [v1, v2]) := by
  rw [evalPexpr_ctor, evalPexprList_cons, evalPexprList_cons, evalPexprList_nil]
  cases evalPexpr tds ext ρ pe1 <;> cases evalPexpr tds ext ρ pe2 <;> rfl

/-- E2: stated at a TYPE-ARGUMENT constructor (`hc`) — a one-tuple of a
    ctype, `Ctuple [Vctype ty]`, is a genuine engine value (`Vtuple [Vctype
    ty]`) outside `evalTyCtor`, so the pre-E2 unconditional statement is
    false at `Ctuple`; `evalPexpr_ctor1` is the unconditional form. -/
@[simp] theorem evalPexpr_tyctor (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack)
    (a b : List annot) (c : ctor) (ty : ctype) (hc : isTyCtor c = true) :
    evalPexpr tds ext ρ (Pexpr a () (PEctor c [Pexpr b () (PEval (Vctype ty))])) =
      evalTyCtor tds c ty := by
  rw [evalPexpr_ctor1, evalPexpr_val]
  cases c <;> first | rfl | (cases hc)

theorem evalPexpr_case (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack)
    (a : List annot) (pe : generic_pexpr Unit sym) (pats : List (pattern × generic_pexpr Unit sym)) :
    evalPexpr tds ext ρ (Pexpr a () (PEcase pe pats)) =
      (if isPePureAlts pats then (do
        let cval ← evalPexpr tds ext ρ pe
        let pe'' ← select_case subst_sym_pexpr cval pats
        if peDepth (reannot0 pe'') ≤ peDepthAlts pats then evalPexpr tds ext ρ (reannot0 pe'')
        else none) else none) := by
  rw [evalPexpr]

theorem evalPexpr_not (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack)
    (a : List annot) (pe : generic_pexpr Unit sym) :
    evalPexpr tds ext ρ (Pexpr a () (PEnot pe)) = (do
      let v ← evalPexpr tds ext ρ pe
      match v with
      | Vtrue => some Vfalse
      | Vfalse => some Vtrue
      | _ => none) := by
  rw [evalPexpr]

theorem evalPexpr_if (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack)
    (a : List annot) (pe1 pe2 pe3 : generic_pexpr Unit sym) :
    evalPexpr tds ext ρ (Pexpr a () (PEif pe1 pe2 pe3)) =
      (if isPePure pe2 && isPePure pe3 then (do
        let b ← evalPexpr tds ext ρ pe1
        match b with
        | Vtrue => evalPexpr tds ext ρ pe2
        | Vfalse => evalPexpr tds ext ρ pe3
        | _ => none) else none) := by
  rw [evalPexpr]

@[simp] theorem evalPexpr_undef (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack)
    (a : List annot) (loc : CerbLocation.Loc) (ub : undefined_behaviour) :
    evalPexpr tds ext ρ (Pexpr a () (PEundef loc ub)) = none := by
  rw [evalPexpr.eq_def]


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

/-- A singleton literal operand list evaluates to its value. -/
theorem evalPexprs_single_val (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack)
    (a : List annot) (v : value) :
    evalPexprs tds ext ρ [Pexpr a () (PEval v)] = some [v] := by
  rw [evalPexprs_cons, evalPexpr_val, evalPexprs_nil]
  rfl

/-- A literal head evaluates to its value in front of an evaluated tail. -/
theorem evalPexprs_cons_val (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack)
    (a : List annot) (v : value) (pes : List (generic_pexpr Unit sym)) (vs : List value)
    (h : evalPexprs tds ext ρ pes = some vs) :
    evalPexprs tds ext ρ (Pexpr a () (PEval v) :: pes) = some (v :: vs) := by
  rw [evalPexprs_cons, evalPexpr_val, h]
  rfl

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
    identifier (`Sym f`) at a node annotated `a` (E1). -/
def callRedex (a : List annot) (ra : core_run_annotation) (f : sym)
    (pes : List (generic_pexpr Unit sym)) : CoreExpr :=
  Expr a (Eproc ra (Sym f) pes)

@[simp] theorem callRedex?_callRedex (a : List annot) (ra : core_run_annotation) (f : sym)
    (pes : List (generic_pexpr Unit sym)) :
    callRedex? (callRedex a ra f pes) = some (CTX, f, pes) := rfl

@[simp] theorem jumpRedex?_callRedex (a : List annot) (ra : core_run_annotation) (f : sym)
    (pes : List (generic_pexpr Unit sym)) :
    jumpRedex? (callRedex a ra f pes) = none := rfl

@[simp] theorem toVal_callRedex (a : List annot) (ra : core_run_annotation) (f : sym)
    (pes : List (generic_pexpr Unit sym)) :
    toVal (callRedex a ra f pes) = none := rfl

@[simp] theorem redexAnnots_callRedex (a : List annot) (ra : core_run_annotation) (f : sym)
    (pes : List (generic_pexpr Unit sym)) :
    redexAnnots (callRedex a ra f pes) = a := rfl

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

/-! ## The flat TUPLE binder pattern (E2)

`let weak (a: loaded integer, b: loaded integer) = …` — the shape of every
corpus tuple binder (docs/corpus-e0: the pair delivered by an `unseq`):
a `Ctuple` pattern whose components are BASE patterns (a symbol or a
wildcard at a base type). `update_env_aux`'s `CaseCtor Ctuple pats',
Vtuple cvals` arm binds by a `foldr` over `zip pats' cvals`
(core_aux.lem:2444–2447; Core_aux.lean:861): `zip` TRUNCATES, so an arity
mismatch binds the common prefix and the engine does NOT fail — mirrored
verbatim through `update_env`. The base components always match, so the
ONLY binding failure at this pattern is a head value that is not a
`Vtuple` — `update_env_aux`'s catch-all `failwithI` (the binding PANIC,
classified in Round.lean). NESTED tuple patterns (the C call protocol's
`((fp, (ret, params, variadic, proto)), arg…)`) are E6's: a mismatch at
an inner component leaves the panic under a `fmapAddBy`, outside
`ShippedRefusal.panic_env`'s shape. -/

/-- A base component: `(x : bty)` or `(_ : bty)` at its own annotations. -/
abbrev TupleLeaf : Type := List annot × Option sym × core_base_type

def leafPat (t : TupleLeaf) : pattern := Pattern t.1 (CaseBase (t.2.1, t.2.2))

def tuplePat (pa : List annot) (ls : List TupleLeaf) : pattern :=
  Pattern pa (CaseCtor Ctuple (ls.map leafPat))

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

    Mirror map (pin f95ef8d9c, generated/):
    - context decomposition/rebuild: get_ctx/apply_ctx
      (Core_reduction.lean:381/389; core_reduction.lem:524–625) — the
      `*_ctx` congruence rules (E1: + `bound_ctx`, the `Cbound` frame);
    - redex reduction: one_step0 (Core_reduction.lean:353) — the
      beta/merge rules;
    - actions: step_ctx's process_action + step_action
      (Core_reduction.lean:424,484) surface Load/StoreRequest2, which
      the sequential driver discharges against CerbMem.loadM/storeM
      (Driver.lean:273) and feeds `(aid, fp[, mval])` to the
      continuation — the `load`/`store` rules fuse request +
      discharge + continuation into one step.

    THE LOCATION WRITE (E1). Every rule that is an instance of step_ctx's
    GENERAL arm (core_reduction.lem:1153–1164: everything but the three
    value arms PROGRAM-DONE/RETURN/REMOVE-ANNOT) writes the thread's
    `current_loc` from the REDEX NODE's annotations before anything else:
    its successor control is `ctl.upd a` (`Ctl.upd`/`locUpd`), `a` the
    redex node's static annotation list — for the whole-expression rules
    `run`/`call` the node get_ctx's path ends in, `redexAnnots e`. The
    congruence rules thread whatever control the framed step produced
    (a general-arm step; the guards exclude the call and the return, which
    are stated at the whole expression). `ret`/`ret_annot` (value arms)
    leave the control's location alone. `ctl.upd [] = ctl` by `rfl`, so
    the annotation-free spellings read exactly as before E1.

    ANNOTATED VALUES (E1). The value heads of the betas and the REMOVE-*
    rules are stated at ANY static annotation lists (`ofValA (.pure a1 b1
    v)`, `ofValA (.annot a1 a2 b1 ds v)`), as
    the engine's arms are (`Expr pe1_annots (Epure pe1)` with
    `valueFromPexpr pe1 = Just cval`, core_reduction.lem:385–423).

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
      touches thread env). Successor control `ctl.upd a` (E1). -/
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
              (Expr [] (Epure (Pexpr [] () (PEval Vunit))))), ρ, ctl.upd a, σ')
  /-- Positive strong load, evaluated operands. Mirrors: step_action
      Load0 arm (Core_reduction.lean:424 — request `LoadRequest2`,
      continuation `Expr [] (Eannot [DA_pos [] fp] (mk_value_e
      (valueFromMemValue mval).2))`), driver discharge
      `liftMem (CerbMem.loadM M.tagDefs loc ty pv)` (Driver.lean:273).
      loadM: CerbMem.lean:1586. -/
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
                (valueFromMemValue mval).2))))), ρ, ctl.upd a, σ')
  /-- Positive strong create, evaluated operands. Mirrors: step_action
      Create arm (Core_reduction.lean:424; core_reduction.lem:642–651 —
      value operands `(Vobject (OVinteger align), Vctype ty)` classify;
      request `CreateRequest2 pref align ty (get_with_address e_annots)
      none` with continuation `mk_value_e (Vobject (OVpointer ptrval))`,
      a BARE value), driver discharge `liftMem (allocateObject tagDefs
      tid pref align ty req_addr_opt init_opt)` (Driver.lean:273).
      allocateObject DISCARDS the thread id and the requested address
      (CerbMem.lean:1844–1845, `_ : Nat` / `_ : Option Int`), so the rule
      pins them to `0`/`none`; the certification bridges to the engine's
      `tid1`/`get_with_address a` by `rfl` (discarded arguments are
      definitionally interchangeable — E1: at ANY node annotations, so an
      `ACerb_with_address` attribute changes nothing at this pin). -/
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
           (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer pv))))), ρ, ctl.upd a, σ')
  /-- Positive strong ALLOC (`Alloc0`, C's `malloc`; kill/free arc K3),
      evaluated INTEGER operands. Mirrors step_action's Alloc0 arm
      (Core_reduction.lean:424), driver discharge `liftMem
      (CerbMem.allocateRegion tid1 pref align_ival size_ival)`,
      continuation `mk_value_e (Vobject (OVpointer ptrval))`.
      `allocateRegion` DISCARDS the thread id (CerbMem.lean:1533). -/
  | alloc {a : List annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {pe1 pe2 : generic_pexpr Unit sym}
      {align size : CerbMem.IntegerValue} {pref : prefix0}
      {pv : CerbMem.PointerValue} {ρ : EnvStack} {ctl : Ctl} {σ σ' : Mem}
      (h1 : valueFromPexpr pe1 = some (Vobject (OVinteger align)))
      (h2 : valueFromPexpr pe2 = some (Vobject (OVinteger size)))
      (hmem : applyMemM (CerbMem.allocateRegion 0 pref align size) σ = some (pv, σ')) :
      Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Alloc0 pe1 pe2 pref)))), ρ, ctl, σ)
           (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer pv))))), ρ, ctl.upd a, σ')
  /-- Positive strong KILL (kill/free arc K2), evaluated pointer operand.
      Mirrors step_action's Kill arm (Core_reduction.lean:424), driver
      discharge `liftMem (CerbMem.killM loc1 is_dynamic1 ptr_val)`,
      continuation `mk_value_e Vunit`. Only `is_dynamic kind` reaches the
      request. killM: CerbMem.lean:1555–1580. -/
  | kill {a : List annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {kind : kill_kind} {pe : generic_pexpr Unit sym}
      {pv : CerbMem.PointerValue} {ρ : EnvStack} {ctl : Ctl} {σ σ' : Mem}
      (h1 : valueFromPexpr pe = some (Vobject (OVpointer pv)))
      (hmem : applyMemM (CerbMem.killM loc (is_dynamic kind) pv) σ = some ((), σ')) :
      Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Kill kind pe)))), ρ, ctl, σ)
           (Expr [] (Epure (Pexpr [] () (PEval Vunit))), ρ, ctl.upd a, σ')
  /-- LETS-PURE at a wildcard pattern: `lets _ = v in E2 --> E2`
      (one_step0's Esseq bare-value arm, Core_reduction.lean:353;
      core_reduction.lem:407–414 — the head is `Expr pe1_annots (Epure
      pe1)` with `valueFromPexpr pe1 = Just cval`: ANY static annotations,
      E1 `ofValA`). `update_env (CaseBase (none,_))` is the identity on a
      NONEMPTY stack (Core_aux.lean:861-868) and a failwithI PANIC on an
      empty one — the cons shape is load-bearing (header note 1). -/
  | sseq_pure {a pa a1 b1 : List annot} {bty : core_base_type} {v : value}
      {e2 : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
      {ctl : Ctl} {σ : Mem} :
      Step M (Expr a (Esseq (Pattern pa (CaseBase (none, bty)))
              (ofValA (.pure a1 b1 v)) e2), ev0 :: evs, ctl, σ)
           (e2, ev0 :: evs, ctl.upd a, σ)
  /-- LETS-ANNOT at a wildcard pattern: `lets _ = {A}v in E2 --> {A} E2`
      (one_step0 Esseq Eannot arm, "reduction: LETS-ANNOT",
      core_reduction.lem:416–423 — the result node is `Expr [] (Eannot xs
      e2)` verbatim). -/
  | sseq_annot {a pa a1 a2 b1 : List annot} {bty : core_base_type}
      {ds : List dyn_annotation} {v : value} {e2 : CoreExpr}
      {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {ctl : Ctl} {σ : Mem} :
      Step M (Expr a (Esseq (Pattern pa (CaseBase (none, bty)))
              (ofValA (.annot a1 a2 b1 ds v)) e2), ev0 :: evs, ctl, σ)
           (Expr [] (Eannot ds e2), ev0 :: evs, ctl.upd a, σ)
  /-- LETW-PURE at a wildcard pattern (one_step0's Ewseq bare-value arm,
      core_reduction.lem:389–396). -/
  | wseq_pure {a pa a1 b1 : List annot} {bty : core_base_type} {v : value}
      {e2 : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
      {ctl : Ctl} {σ : Mem} :
      Step M (Expr a (Ewseq (Pattern pa (CaseBase (none, bty)))
              (ofValA (.pure a1 b1 v)) e2), ev0 :: evs, ctl, σ)
           (e2, ev0 :: evs, ctl.upd a, σ)
  /-- LETW-ANNOT at a wildcard pattern (core_reduction.lem:397–405). -/
  | wseq_annot {a pa a1 a2 b1 : List annot} {bty : core_base_type}
      {ds : List dyn_annotation} {v : value} {e2 : CoreExpr}
      {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {ctl : Ctl} {σ : Mem} :
      Step M (Expr a (Ewseq (Pattern pa (CaseBase (none, bty)))
              (ofValA (.annot a1 a2 b1 ds v)) e2), ev0 :: evs, ctl, σ)
           (Expr [] (Eannot ds e2), ev0 :: evs, ctl.upd a, σ)
  /-- LETS-PURE at the Specified-binder pattern (S4): `lets Specified(x)
      = Specified(ov) in E2 --> E2` with `x ↦ Vobject ov`
      (`update_env_aux`'s `CaseCtor Cspecified [pat']` arm,
      Core_aux.lean:861). -/
  | sseq_spec_pure {a pa pb a1 b1 : List annot} {x : sym} {bty : core_base_type}
      {ov : object_value} {e2 : CoreExpr}
      {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {ctl : Ctl} {σ : Mem} :
      Step M (Expr a (Esseq (specPat pa pb x bty)
              (ofValA (.pure a1 b1 (Vloaded (LVspecified ov)))) e2), ev0 :: evs, ctl, σ)
           (e2, update_env (specPat pa pb x bty) (Vloaded (LVspecified ov))
              (ev0 :: evs), ctl.upd a, σ)
  /-- LETS-ANNOT at the Specified-binder pattern. -/
  | sseq_spec_annot {a pa pb a1 a2 b1 : List annot} {x : sym} {bty : core_base_type}
      {ds : List dyn_annotation} {ov : object_value} {e2 : CoreExpr}
      {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {ctl : Ctl} {σ : Mem} :
      Step M (Expr a (Esseq (specPat pa pb x bty)
              (ofValA (.annot a1 a2 b1 ds (Vloaded (LVspecified ov)))) e2), ev0 :: evs, ctl, σ)
           (Expr [] (Eannot ds e2),
            update_env (specPat pa pb x bty) (Vloaded (LVspecified ov))
              (ev0 :: evs), ctl.upd a, σ)
  /-- PURE at a non-value pexpr (S4): ONE engine step BIG-STEP evaluating
      the pure expression (one_step0's Epure arm, "reduction: PURE",
      core_reduction.lem:288–299 — the successor keeps the node's
      annotations: `Expr annots (Epure (mk_value_pe cval))`). -/
  | pure_eval {a : List annot} {pe : generic_pexpr Unit sym} {v : value}
      {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
      (hnv : valueFromPexpr pe = none)
      (hv : evalPexpr M.tagDefs M.extern ρ pe = some v) :
      Step M (Expr a (Epure pe), ρ, ctl, σ)
           (Expr a (Epure (Pexpr [] () (PEval v))), ρ, ctl.upd a, σ)
  /-- ACTION_EVAL for a positive strong load with an unevaluated pointer
      operand (S4): step_action's Load0 `_, _` arm (Core_reduction.lean:424,
      `ACTION_EVAL "eval operands of Load"`), process_action's ACTION_EVAL
      arm rebuilds `Expr e_annots (wrap_act …)` at the evaluated operands
      (`mk_value_pe`); the mirror pins the pointer operand's value to a
      POINTER (a non-pointer is the ILLTYPED-at-distance-one round). -/
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
            ρ, ctl.upd a, σ)
  /-- Reduction under the strong-sequencing frame. Mirrors get_ctx's
      Esseq arm (descend into e1 when it is not irreducible —
      core_reduction.lem:557–562) + apply_ctx's Csseq rebuild (:620).
      GUARDS: `jumpRedex? e1 = none` (a jump of e1 is never framed — the
      Erun arm discards the context), `callRedex? e1 = none` (E1: a call
      of e1 is never framed — the PCALL arm CAPTURES the context, stated
      at the whole expression by `Step.call`), `toVal e1 = none` (get_ctx
      descends only into a reducible e1). The framed step is therefore a
      general-arm step and its control write is threaded (`ctl'`). -/
  | sseq_ctx {a : List annot} {pat : pattern} {e1 e1' e2 : CoreExpr}
      {ρ ρ' : EnvStack} {ctl ctl' : Ctl} {σ σ' : Mem}
      (hnj : jumpRedex? e1 = none) (hnc : callRedex? e1 = none) (hnv : toVal e1 = none) :
      Step M (e1, ρ, ctl, σ) (e1', ρ', ctl', σ') →
      Step M (Expr a (Esseq pat e1 e2), ρ, ctl, σ) (Expr a (Esseq pat e1' e2), ρ', ctl', σ')
  /-- Reduction under the weak-sequencing frame (get_ctx's Ewseq arm /
      Cwseq, core_reduction.lem:549–556, :622). Same guards. -/
  | wseq_ctx {a : List annot} {pat : pattern} {e1 e1' e2 : CoreExpr}
      {ρ ρ' : EnvStack} {ctl ctl' : Ctl} {σ σ' : Mem}
      (hnj : jumpRedex? e1 = none) (hnc : callRedex? e1 = none) (hnv : toVal e1 = none) :
      Step M (e1, ρ, ctl, σ) (e1', ρ', ctl', σ') →
      Step M (Expr a (Ewseq pat e1 e2), ρ, ctl, σ) (Expr a (Ewseq pat e1' e2), ρ', ctl', σ')
  /-- Reduction under a dyn-annotation frame (get_ctx's plain `Eannot xs
      e` arm / Cannot, core_reduction.lem:583–586 — taken only when e is
      NOT itself Eannot-rooted, the double-annot arm precedes it, and the
      whole node is reducible: `toVal b = none` is get_ctx's
      `is_irreducible` test — `{A}v` is a VALUE, never descended into; E1
      makes the guard load-bearing because the framed step's control is
      threaded and a bare value under a frame could otherwise RETURN). -/
  | annot_ctx {a : List annot} {ds : List dyn_annotation} {b b' : CoreExpr}
      {ρ ρ' : EnvStack} {ctl ctl' : Ctl} {σ σ' : Mem}
      (hnj : jumpRedex? b = none) (hnc : callRedex? b = none) (hnv : toVal b = none) :
      annotRooted b = false →
      Step M (b, ρ, ctl, σ) (b', ρ', ctl', σ') →
      Step M (Expr a (Eannot ds b), ρ, ctl, σ) (Expr a (Eannot ds b'), ρ', ctl', σ')
  /-- E1: reduction under the `bound` frame (get_ctx's `Ebound` arm /
      `Cbound`, core_reduction.lem:563–568; apply_ctx `Cbound annot ctx'`,
      :618–619). Same three guards as `sseq_ctx`; `toVal b = none` is
      get_ctx's `is_irreducible e` test. `is_unseq_with_ccall_aux` RESETS
      its accumulator at a `Cbound` (:514) — inert on this sequential
      fragment (no `Cunseq` frame exists yet), recorded for E4. -/
  | bound_ctx {a : List annot} {b b' : CoreExpr}
      {ρ ρ' : EnvStack} {ctl ctl' : Ctl} {σ σ' : Mem}
      (hnj : jumpRedex? b = none) (hnc : callRedex? b = none) (hnv : toVal b = none) :
      Step M (b, ρ, ctl, σ) (b', ρ', ctl', σ') →
      Step M (Expr a (Ebound b), ρ, ctl, σ) (Expr a (Ebound b'), ρ', ctl', σ')
  /-- E1: REMOVE-BOUND at a bare value — `bound(v) --> v` (step_ctx's
      general arm, core_reduction.lem:1221–1226, Core_reduction.lean:484:
      `Ebound (expr'@(Expr _ (Epure (Pexpr _ _ (PEval _))))) => Step_tau2
      "CTX, Ebound(value)" TSK_Misc (wrap_expr expr')` — the value node
      VERBATIM, any annotations; `wrap_expr` is at the location-updated
      thread). -/
  | bound_pure {a a1 b1 : List annot} {v : value}
      {ρ : EnvStack} {ctl : Ctl} {σ : Mem} :
      Step M (Expr a (Ebound (ofValA (.pure a1 b1 v))), ρ, ctl, σ)
           (ofValA (.pure a1 b1 v), ρ, ctl.upd a, σ)
  /-- E1: REMOVE-BOUND at an annotated value — `bound({A}v) --> v`
      (core_reduction.lem:1214–1219: `Ebound (Expr _ (Eannot _ (expr'@(Expr
      _ (Epure (Pexpr _ _ (PEval _)))))))`): the DYNAMIC annotations are
      DISCARDED and the inner value node is returned verbatim. -/
  | bound_annot {a a1 a2 b1 : List annot} {ds : List dyn_annotation} {v : value}
      {ρ : EnvStack} {ctl : Ctl} {σ : Mem} :
      Step M (Expr a (Ebound (ofValA (.annot a1 a2 b1 ds v))), ρ, ctl, σ)
           (ofValA (.pure a2 b1 v), ρ, ctl.upd a, σ)
  /-- ANNOTS merge: `{A_1} {A_2} E --> {A_1 ++ A_2} E` (one_step0 Eannot
      arm, core_reduction.lem:301–304; combine_dyn_annotations = (++)). -/
  | annot_merge {a1 a2 : List annot} {ds1 ds2 : List dyn_annotation}
      {b : CoreExpr} {ρ : EnvStack} {ctl : Ctl} {σ : Mem} :
      Step M (Expr a1 (Eannot ds1 (Expr a2 (Eannot ds2 b))), ρ, ctl, σ)
           (Expr (a1 ++ a2) (Eannot (ds1 ++ ds2) b), ρ, ctl.upd a1, σ)
  /-- THE GLOBAL JUMP (S3, header note 4). Mirrors step_ctx's Erun arm
      (core_reduction.lem:1414–1441): the spine hole holds `run l pes`;
      the label resolves in the CURRENT procedure's registered map
      (`hl`); the arguments evaluate against the CURRENT env (`hvs`); the
      successor REPLACES THE WHOLE EXPRESSION by the registered
      continuation with the parameters rebound (`{th_st with env :=
      env', arena := cont_expr}` — no `apply_ctx`), at the thread the
      general arm located from the `run` node (`redexAnnots e`). -/
  | run {e : CoreExpr} {l : sym} {pes : List (generic_pexpr Unit sym)}
      {params : List (sym × core_base_type)} {cont : CoreExpr}
      {vs : List value} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
      {ctl : Ctl} {σ : Mem}
      (hj : jumpRedex? e = some (l, pes))
      (hl : lookupLabel (M.labelsAt ctl.proc) l = some (params, cont))
      (hvs : evalPexprs M.tagDefs M.extern (ev0 :: evs) pes = some vs) :
      Step M (e, ev0 :: evs, ctl, σ)
           (cont, bindArgs params vs (ev0 :: evs), ctl.upd (redexAnnots e), σ)
  /-- Esave ENTRY at value-shaped parameter pexprs: one_step0's Esave TAU
      arm (core_reduction.lem:425–436). -/
  | save {a : List annot} {sb : sym × core_base_type}
      {ps : List (sym × ((core_base_type ×
        Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
      {body : CoreExpr} {cvals : List value}
      {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {ctl : Ctl} {σ : Mem}
      (hvals : valueFromPexprs (saveParamPexprs ps) = some cvals) :
      Step M (Expr a (Esave sb ps body), ev0 :: evs, ctl, σ)
           (body, bindSaveParams ps cvals (ev0 :: evs), ctl.upd a, σ)
  /-- Esave PARAMETER EVALUATION (QA-1/H-1): one_step0's Esave EVAL arm
      (core_reduction.lem:437–445): the initializers are evaluated and the
      node RE-FORMED, annotations preserved. -/
  | save_eval {a : List annot} {sb : sym × core_base_type}
      {ps : List (sym × ((core_base_type ×
        Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
      {body : CoreExpr} {cvals : List value} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
      (hnv : valueFromPexprs (saveParamPexprs ps) = none)
      (hvals : evalPexprs M.tagDefs M.extern ρ (saveParamPexprs ps) = some cvals) :
      Step M (Expr a (Esave sb ps body), ρ, ctl, σ)
           (Expr a (Esave sb (saveParamsWithValues ps cvals) body), ρ, ctl.upd a, σ)
  /-- Eif, true branch: ONE engine step with a BIG-STEP guard (one_step0's
      Eif TAU_WITH_RUNSTATE, core_reduction.lem:363–375). -/
  | if_true {a : List annot} {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
      {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
      (hg : evalPexpr M.tagDefs M.extern ρ g = some Vtrue) :
      Step M (Expr a (Eif g e2 e3), ρ, ctl, σ) (e2, ρ, ctl.upd a, σ)
  /-- Eif, false branch. -/
  | if_false {a : List annot} {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
      {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
      (hg : evalPexpr M.tagDefs M.extern ρ g = some Vfalse) :
      Step M (Expr a (Eif g e2 e3), ρ, ctl, σ) (e3, ρ, ctl.upd a, σ)
  /-- Ecase at a VALUE scrutinee: TAU into the substituted branch
      (one_step0's Ecase value arm, core_reduction.lem:325–336). -/
  | case_value {a : List annot} {pe : generic_pexpr Unit sym}
      {pats : List (pattern × CoreExpr)} {cval : value} {e' : CoreExpr}
      {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
      (hv : valueFromPexpr pe = some cval)
      (hsel : select_case subst_sym_expr cval pats = some e') :
      Step M (Expr a (Ecase pe pats), ρ, ctl, σ) (e', ρ, ctl.upd a, σ)
  /-- LETS-PURE at the plain-symbol binder: `lets x = v in E2 --> E2`
      with `x` bound to `v` verbatim (`update_env (symPat …)`,
      Core_aux.lean:861). -/
  | sseq_sym_pure {a pa a1 b1 : List annot} {x : sym} {bty : core_base_type}
      {v : value} {e2 : CoreExpr}
      {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {ctl : Ctl} {σ : Mem} :
      Step M (Expr a (Esseq (symPat pa x bty) (ofValA (.pure a1 b1 v)) e2), ev0 :: evs, ctl, σ)
           (e2, update_env (symPat pa x bty) v (ev0 :: evs), ctl.upd a, σ)
  /-- E1: LETS-ANNOT at the plain-symbol binder — `lets x = {A}v in E2 -->
      {A} E2` with `x ↦ v` (the SAME engine arm as `sseq_annot`,
      core_reduction.lem:416–423; the emitted dialect reaches it: `let
      strong a = bound(…)` never does, `bound` drops the annotations, but
      the pattern-general binders of E2 do). Retires the `BareHead`
      OUT-OF-SCOPE row. -/
  | sseq_sym_annot {a pa a1 a2 b1 : List annot} {x : sym} {bty : core_base_type}
      {ds : List dyn_annotation} {v : value} {e2 : CoreExpr}
      {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {ctl : Ctl} {σ : Mem} :
      Step M (Expr a (Esseq (symPat pa x bty) (ofValA (.annot a1 a2 b1 ds v)) e2), ev0 :: evs, ctl, σ)
           (Expr [] (Eannot ds e2), update_env (symPat pa x bty) v (ev0 :: evs), ctl.upd a, σ)
  /-- E2: LETS-PURE at a flat TUPLE binder — `lets (x1, …, xn) = (v1, …, vn)
      in E2 --> E2` with each `xi ↦ vi` (one_step0's Esseq bare-value arm,
      core_reduction.lem:407–414, binding through `update_env`'s `CaseCtor
      Ctuple pats', Vtuple cvals` arm, core_aux.lem:2444–2447 — a `foldr`
      over the TRUNCATING `zip`, so any arity is an engine success). The
      head value is pinned to a TUPLE: at any other value the engine's
      binder is the `failwithI` PANIC (classified, not mirrored —
      `complete_beta_tuple`). -/
  | sseq_tuple_pure {a pa a1 b1 : List annot} {ls : List TupleLeaf} {vs : List value}
      {e2 : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {ctl : Ctl} {σ : Mem} :
      Step M (Expr a (Esseq (tuplePat pa ls) (ofValA (.pure a1 b1 (Vtuple vs))) e2), ev0 :: evs, ctl, σ)
           (e2, update_env (tuplePat pa ls) (Vtuple vs) (ev0 :: evs), ctl.upd a, σ)
  /-- E2: LETS-ANNOT at a flat tuple binder (core_reduction.lem:416–423). -/
  | sseq_tuple_annot {a pa a1 a2 b1 : List annot} {ls : List TupleLeaf} {vs : List value}
      {ds : List dyn_annotation} {e2 : CoreExpr}
      {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {ctl : Ctl} {σ : Mem} :
      Step M (Expr a (Esseq (tuplePat pa ls) (ofValA (.annot a1 a2 b1 ds (Vtuple vs))) e2), ev0 :: evs, ctl, σ)
           (Expr [] (Eannot ds e2), update_env (tuplePat pa ls) (Vtuple vs) (ev0 :: evs), ctl.upd a, σ)
  /-- E2: LETW-PURE at a flat tuple binder — the corpus's `let weak (a, b) =
      …` (one_step0's Ewseq bare-value arm, core_reduction.lem:389–396). -/
  | wseq_tuple_pure {a pa a1 b1 : List annot} {ls : List TupleLeaf} {vs : List value}
      {e2 : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {ctl : Ctl} {σ : Mem} :
      Step M (Expr a (Ewseq (tuplePat pa ls) (ofValA (.pure a1 b1 (Vtuple vs))) e2), ev0 :: evs, ctl, σ)
           (e2, update_env (tuplePat pa ls) (Vtuple vs) (ev0 :: evs), ctl.upd a, σ)
  /-- E2: LETW-ANNOT at a flat tuple binder (core_reduction.lem:397–405) —
      the shape every corpus `let weak (a, b) = unseq(…)` reaches once E4
      delivers the unseq's ANNOTATED tuple. -/
  | wseq_tuple_annot {a pa a1 a2 b1 : List annot} {ls : List TupleLeaf} {vs : List value}
      {ds : List dyn_annotation} {e2 : CoreExpr}
      {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {ctl : Ctl} {σ : Mem} :
      Step M (Expr a (Ewseq (tuplePat pa ls) (ofValA (.annot a1 a2 b1 ds (Vtuple vs))) e2), ev0 :: evs, ctl, σ)
           (Expr [] (Eannot ds e2), update_env (tuplePat pa ls) (Vtuple vs) (ev0 :: evs), ctl.upd a, σ)
  /-- E2: LETW-PURE at the plain-symbol binder — the corpus's `let weak
      a_515: pointer = pure(x) in load('signed int', a_515)` (one_step0's
      Ewseq bare-value arm, core_reduction.lem:389–396; `update_env_aux`'s
      `CaseBase (Just sym, _)` arm binds any value verbatim). -/
  | wseq_sym_pure {a pa a1 b1 : List annot} {x : sym} {bty : core_base_type}
      {v : value} {e2 : CoreExpr}
      {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {ctl : Ctl} {σ : Mem} :
      Step M (Expr a (Ewseq (symPat pa x bty) (ofValA (.pure a1 b1 v)) e2), ev0 :: evs, ctl, σ)
           (e2, update_env (symPat pa x bty) v (ev0 :: evs), ctl.upd a, σ)
  /-- E2: LETW-ANNOT at the plain-symbol binder (core_reduction.lem:397–405). -/
  | wseq_sym_annot {a pa a1 a2 b1 : List annot} {x : sym} {bty : core_base_type}
      {ds : List dyn_annotation} {v : value} {e2 : CoreExpr}
      {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {ctl : Ctl} {σ : Mem} :
      Step M (Expr a (Ewseq (symPat pa x bty) (ofValA (.annot a1 a2 b1 ds v)) e2), ev0 :: evs, ctl, σ)
           (Expr [] (Eannot ds e2), update_env (symPat pa x bty) v (ev0 :: evs), ctl.upd a, σ)
  /-- E2: Ecase at a NON-value scrutinee — the EVAL round (one_step0's Ecase
      `Nothing` arm, core_reduction.lem:323–339: `EVAL "Ecase" (eval_pexpr pe
      >>= fun pe' -> E.return (Expr annots (Ecase pe' pat_es)))`; step_ctx's
      `eval_pexpr` is the iterate-until-value evaluator under its `Sum`
      readout, delivering `mk_value_pe cval`, :1092–1098): the scrutinee
      evaluated through the certified big-step evaluator, the node REBUILT
      with the value scrutinee at its own annotations; the next round is
      `case_value`. -/
  | case_eval {a : List annot} {pe : generic_pexpr Unit sym}
      {pats : List (pattern × CoreExpr)} {cval : value}
      {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
      (hnv : valueFromPexpr pe = none)
      (hv : evalPexpr M.tagDefs M.extern ρ pe = some cval) :
      Step M (Expr a (Ecase pe pats), ρ, ctl, σ)
           (Expr a (Ecase (Pexpr [] () (PEval cval)) pats), ρ, ctl.upd a, σ)
  /-- THE POINTER-EQUALITY MEMOP at evaluated operands: ONE engine step
      (one_step0's Ememop arm at values → `MEMOP PtrEq cvals`; step_ctx's
      MEMOP dispatch `Step_memop_request2 th_st.current_loc …`,
      core_reduction.lem:1475–1479; the driver's `perform_memop_request2`
      PtrEq arm `liftMem (eqPtrval loc …)`). The successor is a BARE pure
      value. `eqPtrval` DISCARDS its loc argument (CerbMem.lean:1731). -/
  | memop_ptreq {a : List annot} {pe1 pe2 : generic_pexpr Unit sym}
      {pv1 pv2 : CerbMem.PointerValue} {b : Bool}
      {ρ : EnvStack} {ctl : Ctl} {σ σ' : Mem}
      (h1 : valueFromPexpr pe1 = some (Vobject (OVpointer pv1)))
      (h2 : valueFromPexpr pe2 = some (Vobject (OVpointer pv2)))
      (hmem : applyMemM (CerbMem.eqPtrval default pv1 pv2) σ = some (b, σ')) :
      Step M (Expr a (Ememop PtrEq [pe1, pe2]), ρ, ctl, σ)
           (Expr [] (Epure (Pexpr [] () (PEval (boolValue b)))), ρ, ctl.upd a, σ')
  /-- MEMOP-OPERAND EVALUATION: one_step0's Ememop arm at a non-value
      operand list (core_reduction.lem:310–319), node annotations
      PRESERVED. -/
  | memop_eval {a : List annot} {mop : memop}
      {pe1 pe2 : generic_pexpr Unit sym} {v1 v2 : value}
      {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
      (hnv : valueFromPexprs [pe1, pe2] = none)
      (hv1 : evalPexpr M.tagDefs M.extern ρ pe1 = some v1)
      (hv2 : evalPexpr M.tagDefs M.extern ρ pe2 = some v2) :
      Step M (Expr a (Ememop mop [pe1, pe2]), ρ, ctl, σ)
           (Expr a (Ememop mop
             [Pexpr [] () (PEval v1), Pexpr [] () (PEval v2)]), ρ, ctl.upd a, σ)
  /-- ACTION_EVAL for a positive strong store whose operands are NOT ALL
      values (step_action's Store0 `_, _, _` arm, Core_reduction.lean:424). -/
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
                      (Pexpr [] () (PEval cv)) mo)))), ρ, ctl.upd a, σ)
  /-- ACTION_EVAL for a positive strong kill with an unevaluated pointer
      operand (step_action's Kill `none` arm). -/
  | kill_eval {a : List annot} {loc : CerbLocation.Loc}
      {ann : core_run_annotation} {kind : kill_kind}
      {pe : generic_pexpr Unit sym} {pv : CerbMem.PointerValue}
      {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
      (hnv : valueFromPexpr pe = none)
      (hv : evalPexpr M.tagDefs M.extern ρ pe = some (Vobject (OVpointer pv))) :
      Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Kill kind pe)))), ρ, ctl, σ)
           (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Kill kind (Pexpr [] () (PEval (Vobject (OVpointer pv)))))))), ρ, ctl.upd a, σ)
  /-- ACTION_EVAL for a positive strong alloc whose operands are NOT all
      values (step_action's Alloc0 `_, _` arm). -/
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
                      (Pexpr [] () (PEval (Vobject (OVinteger size)))) pref)))), ρ, ctl.upd a, σ)
  /-- E1: ACTION_EVAL for a positive strong create whose operands are NOT
      all values — the round every emitted `create(Ivalignof(ty), ty)`
      takes first (step_action's Create `(_, _)` arm, core_reduction.lem:
      656–661: `ACTION_EVAL "eval operands of Create" (full_eval_pexpr pe1
      >>= cval1 -> full_eval_pexpr pe2 >>= cval2 -> return (wrap (Create
      (mk_value_pe cval1) (mk_value_pe cval2) pref)))`, wrapped by
      process_action's ACTION_EVAL arm into `Expr e_annots (wrap_act
      act')` in context). The mirror pins the values to an INTEGER and a
      CTYPE — the successor is exactly the create redex; anything else is
      the ILLTYPED-at-distance-one round (`ACTION_ILLTYPED "Create"`,
      :654), classified, not mirrored. -/
  | create_eval {a : List annot} {loc : CerbLocation.Loc}
      {ann : core_run_annotation} {pe1 pe2 : generic_pexpr Unit sym}
      {align : CerbMem.IntegerValue} {ty : ctype} {pref : prefix0}
      {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
      (hnv : valueFromPexprs [pe1, pe2] = none)
      (hv1 : evalPexpr M.tagDefs M.extern ρ pe1 = some (Vobject (OVinteger align)))
      (hv2 : evalPexpr M.tagDefs M.extern ρ pe2 = some (Vctype ty)) :
      Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Create pe1 pe2 pref)))), ρ, ctl, σ)
           (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Create (Pexpr [] () (PEval (Vobject (OVinteger align))))
                      (Pexpr [] () (PEval (Vctype ty))) pref)))), ρ, ctl.upd a, σ)
  /-- THE PROCEDURE CALL (calls arc C2) — context CAPTURING. Mirrors
      step_ctx's PCALL arm (core_reduction.lem:1384–1400): ONE round
      evaluates every argument against the CURRENT env (`hvs`) AND
      performs the call: `call_proc`'s lookup (`hf`) and arity check
      (`hlen`), the fresh parameter frame pushed (`procEnv`), the callee
      installed, the current procedure set, the caller's procedure and the
      redex's EVALUATION CONTEXT `ctx` pushed on the call stack, the
      execution location pushed at the thread's current location — E1:
      the location the general arm wrote from the `Eproc` node
      (`Ctl.callPush ctl (redexAnnots e) ctx f`). Memory and run state
      untouched (`labeled` installed once, never by a call). -/
  | call {e : CoreExpr} {ctx : context} {f : sym} {pes : List (generic_pexpr Unit sym)}
      {params : List (sym × core_base_type)} {body : CoreExpr} {vs : List value}
      {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
      (hc : callRedex? e = some (ctx, f, pes))
      (hvs : evalPexprs M.tagDefs M.extern ρ pes = some vs)
      (hf : lookupProc M.file M.extern f = some (params, body))
      (hlen : params.length = vs.length) :
      Step M (e, ρ, ctl, σ)
           (body, procEnv params vs :: ρ, ctl.callPush (redexAnnots e) ctx f, σ)
  /-- THE RETURN (calls arc C2). Mirrors step_ctx's value arm at a
      NON-EMPTY call stack (core_reduction.lem:1115–1145): the callee's
      arena reducing to a BARE value at `Stack_cons2` IS the return. The
      value is plugged into the caller's SAVED context (`apply_ctx
      caller_ctx (Expr e_annots (Epure (mk_value_pe cval)))` — E1: the
      value node's static annotations RIDE, the pexpr's are reset), the
      env stack pops one frame, the current procedure is restored,
      `exec_loc` and (E1) `current_loc` are NOT touched (a value arm — no
      location write). The empty-env failwithI PANIC channel is excluded
      by the cons-shaped env premise. -/
  | ret {a1 b1 : List annot} {v : value} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
      {p : Option sym} {ctx : context} {κ : List (Option sym × context)}
      {q : Option sym} {ℓ : exec_location} {lc : CerbLocation.Loc} {sp : RunSup} {σ : Mem} :
      Step M (ofValA (.pure a1 b1 v), ev0 :: evs, ⟨(p, ctx) :: κ, q, ℓ, lc, sp⟩, σ)
           (apply_ctx ctx (ofValA (.pure a1 [] v)), evs, ⟨κ, p, ℓ, lc, sp⟩, σ)
  /-- REMOVE-ANNOT at a NON-EMPTY call stack (calls arc C2). Mirrors
      step_ctx's second arm (core_reduction.lem:1146–1151): `(CTX, Expr _
      (Eannot _ (expr'@(Expr _ (Epure (Pexpr _ _ (PEval _)))))) =>
      Step_tau2 "CTX, Eannot(value)" TSK_Misc { th_st with arena := expr'
      }` — the inner value node VERBATIM, at ANY annotations (E1), at ANY
      stack (the arm precedes the general arm; no location write). At
      `κ = []` the annotated value is a TERMINAL for the mirror. -/
  | ret_annot {a1 a2 b1 : List annot} {ds : List dyn_annotation} {v : value} {ρ : EnvStack}
      {pc : Option sym × context} {κ : List (Option sym × context)}
      {q : Option sym} {ℓ : exec_location} {lc : CerbLocation.Loc} {sp : RunSup} {σ : Mem} :
      Step M (ofValA (.annot a1 a2 b1 ds v), ρ, ⟨pc :: κ, q, ℓ, lc, sp⟩, σ)
           (ofValA (.pure a2 b1 v), ρ, ⟨pc :: κ, q, ℓ, lc, sp⟩, σ)

/-! ## Basic metatheory of Step (inversions the logic needs) -/

/-! ### Values never sit under a spine search -/

theorem toVal_none_of_jumpRedex?_some {e : CoreExpr} {lp : sym × List (generic_pexpr Unit sym)}
    (h : jumpRedex? e = some lp) : toVal e = none := by
  cases hv : toVal e with
  | none => rfl
  | some w =>
    obtain ⟨wa, -, rfl⟩ := ofValA_of_toVal hv
    cases wa <;> simp [jumpRedex?, annotRooted] at h

theorem toVal_none_of_callRedex?_some {e : CoreExpr}
    {q : context × sym × List (generic_pexpr Unit sym)}
    (h : callRedex? e = some q) : toVal e = none := by
  cases hv : toVal e with
  | none => rfl
  | some w =>
    obtain ⟨wa, -, rfl⟩ := ofValA_of_toVal hv
    cases wa <;> simp [callRedex?, annotRooted] at h

@[simp] theorem jumpRedex?_ofValA (w : SpikeValA) : jumpRedex? (ofValA w) = none := by
  cases w <;> simp [jumpRedex?, annotRooted]

@[simp] theorem callRedex?_ofValA (w : SpikeValA) : callRedex? (ofValA w) = none := by
  cases w <;> simp [callRedex?, annotRooted]

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
            (Expr [] (Epure (Pexpr [] () (PEval Vunit))))), ρ, ctl.upd a, σ') :=
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
              (valueFromMemValue mval).2))))), ρ, ctl.upd a, σ') :=
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
         (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer pv))))), ρ, ctl.upd a, σ') :=
  Step.create rfl rfl hmem

theorem Step.kill_canonical {M : MachineCtx} {a : List annot}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {kind : kill_kind}
    {pv : CerbMem.PointerValue} {ρ : EnvStack} {ctl : Ctl} {σ σ' : Mem}
    (hmem : applyMemM (CerbMem.killM loc (is_dynamic kind) pv) σ = some ((), σ')) :
    Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Kill kind (Pexpr [] () (PEval (Vobject (OVpointer pv)))))))), ρ, ctl, σ)
         (Expr [] (Epure (Pexpr [] () (PEval Vunit))), ρ, ctl.upd a, σ') :=
  Step.kill rfl hmem

theorem Step.alloc_canonical {M : MachineCtx} {a : List annot}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {align size : CerbMem.IntegerValue} {pref : prefix0}
    {pv : CerbMem.PointerValue} {ρ : EnvStack} {ctl : Ctl} {σ σ' : Mem}
    (hmem : applyMemM (CerbMem.allocateRegion 0 pref align size) σ = some (pv, σ')) :
    Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Alloc0 (Pexpr [] () (PEval (Vobject (OVinteger align))))
                    (Pexpr [] () (PEval (Vobject (OVinteger size)))) pref)))), ρ, ctl, σ)
         (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer pv))))), ρ, ctl.upd a, σ') :=
  Step.alloc rfl rfl hmem

/-! ### THE CONTROL ACROSS A STEP (calls arc C2; E1 the location write)

Every step either is a GENERAL-ARM round — the control's `κ`, `proc`,
`execLoc`, `sup` are threaded and only `curLoc` is written, `ctl' = ctl.upd
a` at the redex node's annotations `a` — or THE CALL (the control grows by
the captured frame, the callee becomes the current procedure, the
execution location is pushed at the written location: `Ctl.callPush`) or
THE RETURN (the top frame pops, the caller's procedure is restored,
location and supplies untouched). -/

theorem Step.ctl_cases {M : MachineCtx} {e e' : CoreExpr} {ρ ρ' : EnvStack}
    {ctl ctl' : Ctl} {σ σ' : Mem}
    (h : Step M (e, ρ, ctl, σ) (e', ρ', ctl', σ')) :
    (∃ a, ctl' = ctl.upd a) ∨
    (∃ ctx f pes params body vs, callRedex? e = some (ctx, f, pes) ∧
      evalPexprs M.tagDefs M.extern ρ pes = some vs ∧
      lookupProc M.file M.extern f = some (params, body) ∧ params.length = vs.length ∧
      e' = body ∧ ρ' = procEnv params vs :: ρ ∧
      ctl' = ctl.callPush (redexAnnots e) ctx f ∧ σ' = σ) ∨
    (∃ a1 b1 v ev0 evs p ctx κ q ℓ lc sp, e = ofValA (.pure a1 b1 v) ∧
      ρ = ev0 :: evs ∧ ctl = ⟨(p, ctx) :: κ, q, ℓ, lc, sp⟩ ∧
      e' = apply_ctx ctx (ofValA (.pure a1 [] v)) ∧ ρ' = evs ∧
      ctl' = ⟨κ, p, ℓ, lc, sp⟩ ∧ σ' = σ) := by
  generalize hcfg : (e, ρ, ctl, σ) = c at h
  generalize hcfg' : (e', ρ', ctl', σ') = c' at h
  induction h generalizing e ρ ctl σ e' ρ' ctl' σ' with
  | store h1 h2 h3 hmv hmem => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | load h1 h2 hmem => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | create h1 h2 hmem => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | alloc h1 h2 hmem => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | kill h1 hmem => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | sseq_pure => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | sseq_annot => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | wseq_pure => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | wseq_annot => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | sseq_spec_pure => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | sseq_spec_annot => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | pure_eval hnv hv => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | load_eval hnv2 hv2 => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | sseq_ctx hnj hnc hnv hs ih =>
    cases hcfg; cases hcfg'
    rcases ih rfl rfl with ⟨a, rfl⟩ | ⟨_, _, _, _, _, _, hc1, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, -⟩
    · exact .inl ⟨a, rfl⟩
    · rw [hc1] at hnc; cases hnc
    · rw [toVal_ofValA] at hnv; cases hnv
  | wseq_ctx hnj hnc hnv hs ih =>
    cases hcfg; cases hcfg'
    rcases ih rfl rfl with ⟨a, rfl⟩ | ⟨_, _, _, _, _, _, hc1, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, -⟩
    · exact .inl ⟨a, rfl⟩
    · rw [hc1] at hnc; cases hnc
    · rw [toVal_ofValA] at hnv; cases hnv
  | annot_ctx hnj hnc hnv hg hs ih =>
    cases hcfg; cases hcfg'
    rcases ih rfl rfl with ⟨a, rfl⟩ | ⟨_, _, _, _, _, _, hc1, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, -⟩
    · exact .inl ⟨a, rfl⟩
    · rw [hc1] at hnc; cases hnc
    · rw [toVal_ofValA] at hnv; cases hnv
  | bound_ctx hnj hnc hnv hs ih =>
    cases hcfg; cases hcfg'
    rcases ih rfl rfl with ⟨a, rfl⟩ | ⟨_, _, _, _, _, _, hc1, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, -⟩
    · exact .inl ⟨a, rfl⟩
    · rw [hc1] at hnc; cases hnc
    · rw [toVal_ofValA] at hnv; cases hnv
  | bound_pure => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | bound_annot => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | annot_merge => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | run hj hl hvs => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | save hvals => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | save_eval hnv hvals => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | if_true hg => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | if_false hg => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | case_value hv hsel => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | sseq_sym_pure => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | sseq_sym_annot => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | sseq_tuple_pure => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | sseq_tuple_annot => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | wseq_tuple_pure => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | wseq_tuple_annot => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | wseq_sym_pure => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | wseq_sym_annot => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | case_eval hnv hv => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | memop_ptreq h1 h2 hmem => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | memop_eval hnv hv1 hv2 => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | store_eval hnv hv2 hv3 => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | kill_eval hnv hv => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | alloc_eval hnv hv1 hv2 => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | create_eval hnv hv1 hv2 => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | call hc hvs hf hlen =>
    cases hcfg; cases hcfg'
    exact .inr (.inl ⟨_, _, _, _, _, _, hc, hvs, hf, hlen, rfl, rfl, rfl, rfl⟩)
  | ret =>
    cases hcfg; cases hcfg'
    exact .inr (.inr ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  | ret_annot => cases hcfg; cases hcfg'; exact .inl ⟨[], rfl⟩

/-- The κ/proc/execLoc/sup projections of a general-arm successor. -/
theorem Step.ctl_upd {M : MachineCtx} {e e' : CoreExpr} {ρ ρ' : EnvStack}
    {ctl ctl' : Ctl} {σ σ' : Mem}
    (h : Step M (e, ρ, ctl, σ) (e', ρ', ctl', σ'))
    (hc : callRedex? e = none) (hv : toVal e = none) : ∃ a, ctl' = ctl.upd a := by
  rcases h.ctl_cases with heq | ⟨ctx, f, pes, _, _, _, hc', -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, -⟩
  · exact heq
  · rw [hc'] at hc; cases hc
  · rw [toVal_ofValA] at hv; cases hv

/-- The control's frame fields are preserved at every configuration that
    is neither a call redex (in context) nor a value (the pre-E1
    `Step.ctl_eq`, minus the location). -/
theorem Step.ctl_eq {M : MachineCtx} {e e' : CoreExpr} {ρ ρ' : EnvStack}
    {ctl ctl' : Ctl} {σ σ' : Mem}
    (h : Step M (e, ρ, ctl, σ) (e', ρ', ctl', σ'))
    (hc : callRedex? e = none) (hv : toVal e = none) :
    ctl'.κ = ctl.κ ∧ ctl'.proc = ctl.proc ∧ ctl'.execLoc = ctl.execLoc ∧ ctl'.sup = ctl.sup := by
  obtain ⟨a, rfl⟩ := h.ctl_upd hc hv
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem Step.ctl_eq' {M : MachineCtx} {c c' : Config} (h : Step M c c')
    (hc : callRedex? c.1 = none) (hv : toVal c.1 = none) : ∃ a, c'.2.2.1 = c.2.2.1.upd a := by
  obtain ⟨e, ρ, ctl, σ⟩ := c
  obtain ⟨e', ρ', ctl', σ'⟩ := c'
  exact h.ctl_upd hc hv

/-- A general-arm step's successor control IS an update of the source
    control (`Step.ctl_upd`), restated on the step itself so that
    congruence rules apply to a step whose successor was produced by
    the Language interface (where the control component is an opaque
    projection). -/
theorem Step.retag {M : MachineCtx} {e e' : CoreExpr} {ρ ρ' : EnvStack}
    {ctl ctl' : Ctl} {σ σ' : Mem}
    (h : Step M (e, ρ, ctl, σ) (e', ρ', ctl', σ'))
    (hc : callRedex? e = none) (hv : toVal e = none) :
    ∃ a, Step M (e, ρ, ctl, σ) (e', ρ', ctl.upd a, σ') := by
  obtain ⟨a, rfl⟩ := h.ctl_upd hc hv
  exact ⟨a, h⟩

/-- A step that keeps the call stack is a general-arm step: `κ` grows at
    the call and shrinks at the return. -/
theorem Step.ctl_upd_of_κ {M : MachineCtx} {e e' : CoreExpr} {ρ ρ' : EnvStack}
    {ctl ctl' : Ctl} {σ σ' : Mem}
    (h : Step M (e, ρ, ctl, σ) (e', ρ', ctl', σ')) (hκ : ctl'.κ = ctl.κ) :
    ∃ a, ctl' = ctl.upd a := by
  rcases h.ctl_cases with heq | ⟨ctx, f, pes, _, _, _, -, -, -, -, -, -, rfl, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, -, -, rfl, -, -, rfl, -⟩
  · exact heq
  · exact absurd hκ (by simp)
  · exact absurd hκ (by simp)

theorem Step.env_cons' {M : MachineCtx} {c c' : Config}
    (h : Step M c c') (hκ : c'.2.2.1.κ = c.2.2.1.κ) :
    ∀ ev0 evs, c.2.1 = ev0 :: evs → ∃ ev0', c'.2.1 = ev0' :: evs := by
  induction h with
  | store h1 h2 h3 hmv hmem => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | load h1 h2 hmem => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | create h1 h2 hmem => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | alloc h1 h2 hmem => exact fun ev0 evs hin => ⟨ev0, hin⟩
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
  | sseq_ctx hnj hnc hnv hs ih => exact ih hκ
  | wseq_ctx hnj hnc hnv hs ih => exact ih hκ
  | annot_ctx hnj hnc hnv hg hs ih => exact ih hκ
  | bound_ctx hnj hnc hnv hs ih => exact ih hκ
  | bound_pure => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | bound_annot => exact fun ev0 evs hin => ⟨ev0, hin⟩
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
  | sseq_sym_annot =>
    intro ev0 evs hin
    obtain ⟨rfl, rfl⟩ := List.cons.inj hin
    exact ⟨_, update_env_cons ..⟩
  | sseq_tuple_pure =>
    intro ev0 evs hin
    obtain ⟨rfl, rfl⟩ := List.cons.inj hin
    exact ⟨_, update_env_cons ..⟩
  | sseq_tuple_annot =>
    intro ev0 evs hin
    obtain ⟨rfl, rfl⟩ := List.cons.inj hin
    exact ⟨_, update_env_cons ..⟩
  | wseq_tuple_pure =>
    intro ev0 evs hin
    obtain ⟨rfl, rfl⟩ := List.cons.inj hin
    exact ⟨_, update_env_cons ..⟩
  | wseq_tuple_annot =>
    intro ev0 evs hin
    obtain ⟨rfl, rfl⟩ := List.cons.inj hin
    exact ⟨_, update_env_cons ..⟩
  | wseq_sym_pure =>
    intro ev0 evs hin
    obtain ⟨rfl, rfl⟩ := List.cons.inj hin
    exact ⟨_, update_env_cons ..⟩
  | wseq_sym_annot =>
    intro ev0 evs hin
    obtain ⟨rfl, rfl⟩ := List.cons.inj hin
    exact ⟨_, update_env_cons ..⟩
  | case_eval hnv hv => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | memop_ptreq h1 h2 hmem => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | memop_eval hnv hv1 hv2 => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | store_eval hnv hv2 hv3 => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | kill_eval hnv hv => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | alloc_eval hnv hv1 hv2 => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | create_eval hnv hv1 hv2 => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | call hc hvs hf hlen => exact absurd hκ (by simp)
  | ret => exact absurd hκ (by simp)
  | ret_annot => exact fun ev0 evs hin => ⟨ev0, hin⟩

theorem Step.env_cons {M : MachineCtx} {e : CoreExpr} {ev0 : Fmap sym value}
    {evs : List (Fmap sym value)} {ctl ctl' : Ctl} {σ : Mem}
    {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    (h : Step M (e, ev0 :: evs, ctl, σ) (e', ρ', ctl', σ')) (hκ : ctl'.κ = ctl.κ) :
    ∃ ev0', ρ' = ev0' :: evs :=
  h.env_cons' hκ ev0 evs rfl

/-- Inversion at a call redex IN CONTEXT: the step is THE CALL, its
    successor determined by the file lookup, the argument values and the
    captured context. By induction on the step: a congruence rule cannot
    frame a call of its sub-expression (E1: the guard `hnc`), so the only
    rule at a configuration with a call redex is `Step.call`. -/
theorem Step.call_inv' {M : MachineCtx} {c : Config}
    {out : Config} (h : Step M c out) :
    ∀ {ctx : context} {f : sym} {pes : List (generic_pexpr Unit sym)},
      callRedex? c.1 = some (ctx, f, pes) →
      ∃ params body vs, evalPexprs M.tagDefs M.extern c.2.1 pes = some vs ∧
        lookupProc M.file M.extern f = some (params, body) ∧ params.length = vs.length ∧
        out = (body, procEnv params vs :: c.2.1,
          c.2.2.1.callPush (redexAnnots c.1) ctx f, c.2.2.2) := by
  cases h with
  | store h1 h2 h3 hmv hmem => intro ctx f pes hc; simp [callRedex?] at hc
  | load h1 h2 hmem => intro ctx f pes hc; simp [callRedex?] at hc
  | create h1 h2 hmem => intro ctx f pes hc; simp [callRedex?] at hc
  | alloc h1 h2 hmem => intro ctx f pes hc; simp [callRedex?] at hc
  | kill h1 hmem => intro ctx f pes hc; simp [callRedex?] at hc
  | sseq_pure => intro ctx f pes hc; simp [callRedex?] at hc
  | sseq_annot => intro ctx f pes hc; simp [callRedex?] at hc
  | wseq_pure => intro ctx f pes hc; simp [callRedex?] at hc
  | wseq_annot => intro ctx f pes hc; simp [callRedex?] at hc
  | sseq_spec_pure => intro ctx f pes hc; simp [callRedex?] at hc
  | sseq_spec_annot => intro ctx f pes hc; simp [callRedex?] at hc
  | pure_eval hnv hv => intro ctx f pes hc; simp [callRedex?] at hc
  | load_eval hnv2 hv2 => intro ctx f pes hc; simp [callRedex?] at hc
  | sseq_ctx hnj hnc hnv hs => intro ctx f pes hc; rw [callRedex?_sseq, hnc] at hc; cases hc
  | wseq_ctx hnj hnc hnv hs => intro ctx f pes hc; rw [callRedex?_wseq, hnc] at hc; cases hc
  | annot_ctx hnj hnc hnv hg hs => intro ctx f pes hc; rw [callRedex?_annot_of_not_root _ _ hg, hnc] at hc; cases hc
  | bound_ctx hnj hnc hnv hs => intro ctx f pes hc; rw [callRedex?_bound, hnc] at hc; cases hc
  | bound_pure => intro ctx f pes hc; simp [callRedex?] at hc
  | bound_annot => intro ctx f pes hc; simp [callRedex?] at hc
  | annot_merge => intro ctx f pes hc; simp [callRedex?, annotRooted] at hc
  | run hj hl hvs => intro ctx f pes hc; rw [callRedex?_none_of_jumpRedex?_some hj] at hc; cases hc
  | save hvals => intro ctx f pes hc; simp [callRedex?] at hc
  | save_eval hnv hvals => intro ctx f pes hc; simp [callRedex?] at hc
  | if_true hg => intro ctx f pes hc; simp [callRedex?] at hc
  | if_false hg => intro ctx f pes hc; simp [callRedex?] at hc
  | case_value hv hsel => intro ctx f pes hc; simp [callRedex?] at hc
  | sseq_sym_pure => intro ctx f pes hc; simp [callRedex?] at hc
  | sseq_sym_annot => intro ctx f pes hc; simp [callRedex?] at hc
  | sseq_tuple_pure => intro ctx f pes hc; simp [callRedex?] at hc
  | sseq_tuple_annot => intro ctx f pes hc; simp [callRedex?] at hc
  | wseq_tuple_pure => intro ctx f pes hc; simp [callRedex?] at hc
  | wseq_tuple_annot => intro ctx f pes hc; simp [callRedex?] at hc
  | wseq_sym_pure => intro ctx f pes hc; simp [callRedex?] at hc
  | wseq_sym_annot => intro ctx f pes hc; simp [callRedex?] at hc
  | case_eval hnv hv => intro ctx f pes hc; simp [callRedex?] at hc
  | memop_ptreq h1 h2 hmem => intro ctx f pes hc; simp [callRedex?] at hc
  | memop_eval hnv hv1 hv2 => intro ctx f pes hc; simp [callRedex?] at hc
  | store_eval hnv hv2 hv3 => intro ctx f pes hc; simp [callRedex?] at hc
  | kill_eval hnv hv => intro ctx f pes hc; simp [callRedex?] at hc
  | alloc_eval hnv hv1 hv2 => intro ctx f pes hc; simp [callRedex?] at hc
  | create_eval hnv hv1 hv2 => intro ctx f pes hc; simp [callRedex?] at hc
  | call hc hvs hf hlen =>
    intro ctx f pes hc0
    rw [hc] at hc0
    obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
      have := Option.some.inj hc0
      exact ⟨congrArg Prod.fst this, congrArg (fun q => q.2.1) this,
        congrArg (fun q => q.2.2) this⟩
    exact ⟨_, _, _, hvs, hf, hlen, rfl⟩
  | ret => intro ctx f pes hc; simp at hc
  | ret_annot => intro ctx f pes hc; simp [callRedex?] at hc

theorem Step.call_inv {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config} (h : Step M (e, ρ, ctl, σ) out)
    {ctx : context} {f : sym} {pes : List (generic_pexpr Unit sym)}
    (hc : callRedex? e = some (ctx, f, pes)) :
    ∃ params body vs, evalPexprs M.tagDefs M.extern ρ pes = some vs ∧
      lookupProc M.file M.extern f = some (params, body) ∧ params.length = vs.length ∧
      out = (body, procEnv params vs :: ρ, ctl.callPush (redexAnnots e) ctx f, σ) :=
  h.call_inv' hc

/-- A call step never keeps the call stack (the frame is pushed). -/
theorem Step.call_ne_same_κ {M : MachineCtx} {e e' : CoreExpr} {ρ ρ' : EnvStack}
    {ctl ctl' : Ctl} {σ σ' : Mem} {ctx : context} {f : sym}
    {pes : List (generic_pexpr Unit sym)}
    (hc : callRedex? e = some (ctx, f, pes))
    (h : Step M (e, ρ, ctl, σ) (e', ρ', ctl', σ')) (hκ : ctl'.κ = ctl.κ) : False := by
  obtain ⟨_, _, _, -, -, -, hout⟩ := h.call_inv hc
  have := congrArg (fun c : Config => c.2.2.1.κ) hout
  simp at this
  rw [this] at hκ
  exact absurd hκ (by simp)

/-- A call step is never a general-arm step. -/
theorem Step.call_ne_upd {M : MachineCtx} {e e' : CoreExpr} {ρ ρ' : EnvStack}
    {ctl : Ctl} {σ σ' : Mem} {ctx : context} {f : sym} {a : List annot}
    {pes : List (generic_pexpr Unit sym)}
    (hc : callRedex? e = some (ctx, f, pes))
    (h : Step M (e, ρ, ctl, σ) (e', ρ', ctl.upd a, σ')) : False :=
  h.call_ne_same_κ hc rfl

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
      (body, procEnv params vs :: ρ, ctl.callPush (redexAnnots e) ctx f, σ) :=
  Step.call hc hvs hf hlen

/-- Values do not step AT THE EMPTY CALL STACK (the Language interface's
    `val_stuck`; C2: at a non-empty stack a value is the RETURN redex,
    `Step.ret`/`Step.ret_annot`). Engine analogue: is_irreducible
    short-circuits both get_ctx and one_step0 (Core_reduction.lean:293,
    353,375), and the value arm at `Stack_empty` is PROGRAM-DONE. -/
theorem Step.val_elim {M : MachineCtx} {w : SpikeValA} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config} (hκ : ctl.κ = [])
    (h : Step M (ofValA w, ρ, ctl, σ) out) : False := by
  obtain ⟨κ, p, ℓ, lc, sp⟩ := ctl
  simp only at hκ
  subst hκ
  cases w with
  | pure a b v =>
    cases h with
    | run hj hl hvs => simp at hj
    | pure_eval hnv hv => rw [valueFromPexpr_val] at hnv; cases hnv
    | call hc hvs hf hlen => simp at hc
  | annot a a2 b ds v =>
    cases h with
    | annot_ctx hnj hnc hnv hg hs => rw [toVal_pure_val] at hnv; cases hnv
    | run hj hl hvs => simp [jumpRedex?, annotRooted] at hj
    | call hc hvs hf hlen => simp [callRedex?] at hc

/-- A BARE value never takes a stack-preserving step (its only rule,
    `Step.ret`, pops the call stack). -/
theorem Step.pure_val_elim {M : MachineCtx} {a b : List annot} {v : value} {ρ : EnvStack}
    {ctl ctl' : Ctl} {σ : Mem} {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    (h : Step M (ofValA (.pure a b v), ρ, ctl, σ) (e', ρ', ctl', σ'))
    (hκ : ctl'.κ = ctl.κ) : False := by
  cases h with
  | run hj hl hvs => simp at hj
  | pure_eval hnv hv => rw [valueFromPexpr_val] at hnv; cases hnv
  | call hc hvs hf hlen => simp at hc
  | ret => exact absurd hκ (by simp)

/-- The ANNOTATED value's only stack-preserving step is REMOVE-ANNOT at a
    non-empty call stack: the inner value node verbatim, control untouched. -/
theorem Step.annot_val_inv {M : MachineCtx} {a a2 b : List annot} {ds : List dyn_annotation}
    {v : value} {ρ : EnvStack} {ctl ctl' : Ctl} {σ : Mem} {e' : CoreExpr} {ρ' : EnvStack}
    {σ' : Mem}
    (h : Step M (ofValA (.annot a a2 b ds v), ρ, ctl, σ) (e', ρ', ctl', σ'))
    (hκ : ctl'.κ = ctl.κ) :
    e' = ofValA (.pure a2 b v) ∧ ρ' = ρ ∧ σ' = σ ∧ ctl' = ctl ∧
      ∃ pc κ, ctl.κ = pc :: κ := by
  cases h with
  | annot_ctx hnj hnc hnv hg hs => rw [toVal_pure_val] at hnv; cases hnv
  | run hj hl hvs => simp [jumpRedex?, annotRooted] at hj
  | call hc hvs hf hlen => simp [callRedex?] at hc
  | ret_annot => exact ⟨rfl, rfl, rfl, rfl, _, _, rfl⟩

theorem Step.toVal_none {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config} (hκ : ctl.κ = [])
    (h : Step M (e, ρ, ctl, σ) out) : toVal e = none := by
  cases hv : toVal e with
  | none => rfl
  | some w =>
    obtain ⟨wa, -, rfl⟩ := ofValA_of_toVal hv
    exact (h.val_elim hκ).elim

theorem Step.toValA_none {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config} (hκ : ctl.κ = [])
    (h : Step M (e, ρ, ctl, σ) out) : toValA e = none :=
  toValA_none_of_toVal_none (h.toVal_none hκ)

/-- A stepping tuple is not a Language value: at the empty stack because
    values do not step there, at a non-empty stack by `toValRt`'s
    definition (the `val_stuck` law, Lang.lean). -/
theorem Step.toValRt_none {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config} (h : Step M (e, ρ, ctl, σ) out) :
    toValRt ⟨e, ρ, ctl, M⟩ = none := by
  obtain ⟨κ, p, ℓ, lc, sp⟩ := ctl
  cases κ with
  | nil => rw [toValRt_mk, h.toValA_none rfl]; rfl
  | cons pc κ => rfl

/-! ### The environment stack across steps (calls arc C3) -/

/-- `SameTail ρ ρ'`: `ρ'` has the same frames BELOW THE HEAD as `ρ` — a
    cons-shaped `ρ` yields a cons-shaped `ρ'` with the identical tail.
    This is the shape every stack-preserving step preserves
    (`Step.sameTail`: `update_env` writes the head frame only,
    Core_aux.lean:868; the call and the return are the two frame
    writers). -/
def SameTail (ρ ρ' : EnvStack) : Prop :=
  ∀ ev0 evs, ρ = ev0 :: evs → ∃ ev0', ρ' = ev0' :: evs

theorem SameTail.refl (ρ : EnvStack) : SameTail ρ ρ := fun ev0 _ h => ⟨ev0, h⟩

theorem SameTail.trans {ρ₁ ρ₂ ρ₃ : EnvStack} (h12 : SameTail ρ₁ ρ₂)
    (h23 : SameTail ρ₂ ρ₃) : SameTail ρ₁ ρ₃ := by
  intro ev0 evs h
  obtain ⟨ev1, h1⟩ := h12 ev0 evs h
  exact h23 ev1 evs h1

theorem SameTail.cons_inv {ev0 : Fmap sym value} {evs ρ' : EnvStack}
    (h : SameTail (ev0 :: evs) ρ') : ∃ ev0', ρ' = ev0' :: evs :=
  h ev0 evs rfl

/-- A stack-preserving step keeps the frames below the head. -/
theorem Step.sameTail {M : MachineCtx} {e e' : CoreExpr} {ρ ρ' : EnvStack}
    {ctl ctl' : Ctl} {σ σ' : Mem}
    (h : Step M (e, ρ, ctl, σ) (e', ρ', ctl', σ')) (hκ : ctl'.κ = ctl.κ) : SameTail ρ ρ' :=
  h.env_cons' hκ

/-- THE ENVIRONMENT-DEPTH INVARIANT: the environment stack is always
    deeper than the call stack. -/
theorem Step.env_depth {M : MachineCtx} {e e' : CoreExpr} {ρ ρ' : EnvStack}
    {ctl ctl' : Ctl} {σ σ' : Mem}
    (h : Step M (e, ρ, ctl, σ) (e', ρ', ctl', σ'))
    (hlen : ctl.κ.length < ρ.length) : ctl'.κ.length < ρ'.length := by
  rcases h.ctl_cases with ⟨a, rfl⟩ |
      ⟨ctx, f, pes, params, body, vs, -, -, -, -, rfl, rfl, rfl, rfl⟩ |
      ⟨a1, b1, v, ev0, evs, p, ctx, κ, q, ℓ, lc, sp, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases ρ with
    | nil => simp at hlen
    | cons ev0 evs =>
      obtain ⟨ev0', rfl⟩ := h.env_cons' rfl ev0 evs rfl
      simpa using hlen
  · simp only [Ctl.callPush_κ, List.length_cons]
    omega
  · simp only [List.length_cons] at hlen ⊢
    omega

/-- Inversion at a BARE value under a frame: the step is THE RETURN —
    the env is cons-shaped, the value is plugged into the saved context
    (its pexpr annotations reset by `mk_value_pe`), one env frame and the
    top control frame pop, the caller's procedure is restored, `exec_loc`
    and the location ride. -/
theorem Step.ret_inv {M : MachineCtx} {a b : List annot} {v : value} {ρ : EnvStack}
    {pc : Option sym × context} {κ : List (Option sym × context)}
    {q : Option sym} {ℓ : exec_location} {lc : CerbLocation.Loc} {sp : RunSup} {σ : Mem}
    {out : Config}
    (h : Step M (ofValA (.pure a b v), ρ, ⟨pc :: κ, q, ℓ, lc, sp⟩, σ) out) :
    ∃ ev0 evs, ρ = ev0 :: evs ∧
      out = (apply_ctx pc.2 (ofValA (.pure a [] v)), evs, ⟨κ, pc.1, ℓ, lc, sp⟩, σ) := by
  obtain ⟨e', ρ', ctl', σ'⟩ := out
  cases h with
  | run hj hl hvs => simp at hj
  | pure_eval hnv hv => rw [valueFromPexpr_val] at hnv; cases hnv
  | call hc hvs hf hlen => simp at hc
  | ret => exact ⟨_, _, rfl, rfl⟩

/-- Inversion at an ANNOTATED value under a frame: the step is
    REMOVE-ANNOT (the control and env untouched, the inner node verbatim). -/
theorem Step.ret_annot_inv {M : MachineCtx} {a a2 b : List annot} {ds : List dyn_annotation}
    {v : value} {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (h : Step M (ofValA (.annot a a2 b ds v), ρ, ctl, σ) out) :
    out = (ofValA (.pure a2 b v), ρ, ctl, σ) := by
  obtain ⟨e', ρ', ctl', σ'⟩ := out
  cases h with
  | annot_ctx hnj hnc hnv hg hs => rw [toVal_pure_val] at hnv; cases hnv
  | run hj hl hvs => simp [jumpRedex?, annotRooted] at hj
  | call hc hvs hf hlen => simp [callRedex?] at hc
  | ret_annot => rfl

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
              (Expr [] (Epure (Pexpr [] () (PEval Vunit))))), ρ, ctl.upd a, σ') := by
  cases h with
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | store_eval hnv hv2 hv3 =>
    rw [valueFromPexprs_pair, valueFromPexpr_val, valueFromPexpr_val] at hnv
    cases hnv
  | store h1 h2 h3 hmv hmem =>
    rw [valueFromPexpr_val] at h1 h2 h3
    obtain rfl : ty = _ := by simpa using h1
    obtain rfl : pv = _ := by simpa using h2
    obtain rfl : cv = _ := by simpa using h3
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
                (valueFromMemValue mval).2))))), ρ, ctl.upd a, σ') := by
  cases h with
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | load_eval hnv2 hv2 => rw [valueFromPexpr_val] at hnv2; cases hnv2
  | load h1 h2 hmem =>
    rw [valueFromPexpr_val] at h1 h2
    obtain rfl : ty = _ := by simpa using h1
    obtain rfl : pv = _ := by simpa using h2
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
      applyMemM (CerbMem.allocateObject M.tagDefs 0 pref align ty none none) σ = some (pv, σ') ∧
      out = (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer pv))))), ρ, ctl.upd a, σ') := by
  cases h with
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | create_eval hnv hv1 hv2 =>
    rw [valueFromPexprs_pair, valueFromPexpr_val, valueFromPexpr_val] at hnv
    cases hnv
  | create h1 h2 hmem =>
    rw [valueFromPexpr_val] at h1 h2
    obtain rfl : align = _ := by simpa using h1
    obtain rfl : ty = _ := by simpa using h2
    exact ⟨_, _, hmem, rfl⟩

/-- E1: inversion at a create whose operands are NOT all values: the
    ACTION_EVAL step (the alloc/store twin). -/
theorem Step.create_op_inv {M : MachineCtx} {a : List annot}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (h : Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Create pe1 pe2 pref)))), ρ, ctl, σ) out) :
    ∃ align ty, evalPexpr M.tagDefs M.extern ρ pe1 = some (Vobject (OVinteger align)) ∧
      evalPexpr M.tagDefs M.extern ρ pe2 = some (Vctype ty) ∧
      out = (Expr a (Eaction (Paction polarity.Pos (Action loc ann
        (Create (Pexpr [] () (PEval (Vobject (OVinteger align))))
                (Pexpr [] () (PEval (Vctype ty))) pref)))), ρ, ctl.upd a, σ) := by
  cases h with
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | create h1 h2 hmem => rw [valueFromPexprs_pair, h1, h2] at hnv; cases hnv
  | create_eval hnv' hv1 hv2 => exact ⟨_, _, hv1, hv2, rfl⟩

/-- Inversion at a kill redex of either kind (canonical operand instance). -/
theorem Step.kill_inv {M : MachineCtx} {a : List annot} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {kind : kill_kind} {pv : CerbMem.PointerValue}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (h : Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Kill kind (Pexpr [] () (PEval (Vobject (OVpointer pv)))))))), ρ, ctl, σ) out) :
    ∃ σ', applyMemM (CerbMem.killM loc (is_dynamic kind) pv) σ = some ((), σ') ∧
      out = (Expr [] (Epure (Pexpr [] () (PEval Vunit))), ρ, ctl.upd a, σ') := by
  cases h with
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | kill_eval hnv hv => rw [valueFromPexpr_val] at hnv; cases hnv
  | kill h1 hmem =>
    rw [valueFromPexpr_val] at h1
    obtain rfl : pv = _ := by simpa using h1
    exact ⟨_, hmem, rfl⟩

/-- Inversion at a kill whose operand is NOT a value: the ACTION_EVAL step. -/
theorem Step.kill_op_inv {M : MachineCtx} {a : List annot}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {kind : kill_kind}
    {pe : generic_pexpr Unit sym}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (hnv : valueFromPexpr pe = none)
    (h : Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Kill kind pe)))), ρ, ctl, σ) out) :
    ∃ pv, evalPexpr M.tagDefs M.extern ρ pe = some (Vobject (OVpointer pv)) ∧
      out = (Expr a (Eaction (Paction polarity.Pos (Action loc ann
        (Kill kind (Pexpr [] () (PEval (Vobject (OVpointer pv)))))))), ρ, ctl.upd a, σ) := by
  cases h with
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | kill h1 hmem => rw [hnv] at h1; cases h1
  | kill_eval hnv' hv => exact ⟨_, hv, rfl⟩

/-- Inversion at an alloc redex (canonical operand instance). -/
theorem Step.alloc_inv {M : MachineCtx} {a : List annot} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {align size : CerbMem.IntegerValue}
    {pref : prefix0} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config}
    (h : Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Alloc0 (Pexpr [] () (PEval (Vobject (OVinteger align))))
                    (Pexpr [] () (PEval (Vobject (OVinteger size)))) pref)))), ρ, ctl, σ) out) :
    ∃ pv σ',
      applyMemM (CerbMem.allocateRegion 0 pref align size) σ = some (pv, σ') ∧
      out = (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer pv))))), ρ, ctl.upd a, σ') := by
  cases h with
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | alloc_eval hnv hv1 hv2 =>
    rw [valueFromPexprs_pair, valueFromPexpr_val, valueFromPexpr_val] at hnv
    cases hnv
  | alloc h1 h2 hmem =>
    rw [valueFromPexpr_val] at h1 h2
    obtain rfl : align = _ := by simpa using h1
    obtain rfl : size = _ := by simpa using h2
    exact ⟨_, _, hmem, rfl⟩

/-- Inversion at an alloc whose operands are NOT all values: the
    ACTION_EVAL step. -/
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
                (Pexpr [] () (PEval (Vobject (OVinteger size)))) pref)))), ρ, ctl.upd a, σ) := by
  cases h with
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | alloc h1 h2 hmem => rw [valueFromPexprs_pair, h1, h2] at hnv; cases hnv
  | alloc_eval hnv' hv1 hv2 => exact ⟨_, _, hv1, hv2, rfl⟩

/-! ### THE JUMP-REDEX INVERSION PAIR -/

/-- Inversion at a configuration whose spine hole is an `Erun`: the step
    is THE GLOBAL JUMP, its successor determined by the label map, the
    argument values and the redex node's location (`redexAnnots e`) — by
    induction on the step: no congruence rule frames a jump (`hnj`). -/
theorem Step.jump_inv {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {l : sym} {pes : List (generic_pexpr Unit sym)} {out : Config}
    (hj0 : jumpRedex? e = some (l, pes))
    (h : Step M (e, ρ, ctl, σ) out) :
    ∃ params cont vs ev0 evs, ρ = ev0 :: evs ∧
      lookupLabel (M.labelsAt ctl.proc) l = some (params, cont) ∧
      evalPexprs M.tagDefs M.extern ρ pes = some vs ∧
      out = (cont, bindArgs params vs ρ, ctl.upd (redexAnnots e), σ) := by
  cases h with
  | store h1 h2 h3 hmv hmem => simp [jumpRedex?] at hj0
  | load h1 h2 hmem => simp [jumpRedex?] at hj0
  | create h1 h2 hmem => simp [jumpRedex?] at hj0
  | alloc h1 h2 hmem => simp [jumpRedex?] at hj0
  | kill h1 hmem => simp [jumpRedex?] at hj0
  | sseq_pure => simp [jumpRedex?] at hj0
  | sseq_annot => simp [jumpRedex?] at hj0
  | wseq_pure => simp [jumpRedex?] at hj0
  | wseq_annot => simp [jumpRedex?] at hj0
  | sseq_spec_pure => simp [jumpRedex?] at hj0
  | sseq_spec_annot => simp [jumpRedex?] at hj0
  | pure_eval hnv hv => simp [jumpRedex?] at hj0
  | load_eval hnv2 hv2 => simp [jumpRedex?] at hj0
  | sseq_ctx hnj hnc hnv hs => rw [jumpRedex?_sseq, hnj] at hj0; cases hj0
  | wseq_ctx hnj hnc hnv hs => rw [jumpRedex?_wseq, hnj] at hj0; cases hj0
  | annot_ctx hnj hnc hnv hg hs => rw [jumpRedex?_annot_of_not_root _ _ hg, hnj] at hj0; cases hj0
  | bound_ctx hnj hnc hnv hs => rw [jumpRedex?_bound, hnj] at hj0; cases hj0
  | bound_pure => simp [jumpRedex?] at hj0
  | bound_annot => simp [jumpRedex?] at hj0
  | annot_merge => simp [jumpRedex?, annotRooted] at hj0
  | run hj hl hvs =>
    rw [hj] at hj0
    obtain ⟨rfl, rfl⟩ : _ ∧ _ := by
      have := Option.some.inj hj0
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    exact ⟨_, _, _, _, _, rfl, hl, hvs, rfl⟩
  | save hvals => simp [jumpRedex?] at hj0
  | save_eval hnv hvals => simp [jumpRedex?] at hj0
  | if_true hg => simp [jumpRedex?] at hj0
  | if_false hg => simp [jumpRedex?] at hj0
  | case_value hv hsel => simp [jumpRedex?] at hj0
  | sseq_sym_pure => simp [jumpRedex?] at hj0
  | sseq_sym_annot => simp [jumpRedex?] at hj0
  | sseq_tuple_pure => simp [jumpRedex?] at hj0
  | sseq_tuple_annot => simp [jumpRedex?] at hj0
  | wseq_tuple_pure => simp [jumpRedex?] at hj0
  | wseq_tuple_annot => simp [jumpRedex?] at hj0
  | wseq_sym_pure => simp [jumpRedex?] at hj0
  | wseq_sym_annot => simp [jumpRedex?] at hj0
  | case_eval hnv hv => simp [jumpRedex?] at hj0
  | memop_ptreq h1 h2 hmem => simp [jumpRedex?] at hj0
  | memop_eval hnv hv1 hv2 => simp [jumpRedex?] at hj0
  | store_eval hnv hv2 hv3 => simp [jumpRedex?] at hj0
  | kill_eval hnv hv => simp [jumpRedex?] at hj0
  | alloc_eval hnv hv1 hv2 => simp [jumpRedex?] at hj0
  | create_eval hnv hv1 hv2 => simp [jumpRedex?] at hj0
  | call hc hvs hf hlen => rw [callRedex?_none_of_jumpRedex?_some hj0] at hc; cases hc
  | ret => simp at hj0
  | ret_annot => simp [jumpRedex?] at hj0

/-- Reducibility at a jump redex whose label resolves and whose
    arguments evaluate. -/
theorem Step.run_of_jumpRedex {M : MachineCtx} {e : CoreExpr} {l : sym}
    {pes : List (generic_pexpr Unit sym)}
    {params : List (sym × core_base_type)} {cont : CoreExpr} {vs : List value}
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {ctl : Ctl} {σ : Mem}
    (hj : jumpRedex? e = some (l, pes))
    (hl : lookupLabel (M.labelsAt ctl.proc) l = some (params, cont))
    (hvs : evalPexprs M.tagDefs M.extern (ev0 :: evs) pes = some vs) :
    Step M (e, ev0 :: evs, ctl, σ)
      (cont, bindArgs params vs (ev0 :: evs), ctl.upd (redexAnnots e), σ) :=
  Step.run hj hl hvs

/-- A CALL step of `e` seen from a node whose frame is `fr` (calls arc
    C2): the redex `callRedex? e = some (ctx, f, pes)` under the frame,
    the arguments evaluated at the CURRENT env, the callee found with
    the right arity, and the successor at the pushed control — the
    captured context is the frame applied to the redex's own context,
    exactly get_ctx's outside-in construction; E1: the location written
    from the `Eproc` node (`redexAnnots e`, the same node seen from the
    frame). -/
def Step.CallOf (M : MachineCtx) (e : CoreExpr) (fr : context → context)
    (ρ : EnvStack) (ctl : Ctl) (σ : Mem) (out : Config) : Prop :=
  ∃ ctx f pes params body vs, callRedex? e = some (ctx, f, pes) ∧
    evalPexprs M.tagDefs M.extern ρ pes = some vs ∧
    lookupProc M.file M.extern f = some (params, body) ∧ params.length = vs.length ∧
    out = (body, procEnv params vs :: ρ, ctl.callPush (redexAnnots e) (fr ctx) f, σ)

/-- A `CallOf` successor never keeps the call stack. -/
theorem Step.CallOf.ne_same_κ {M : MachineCtx} {e : CoreExpr} {fr : context → context}
    {ρ : EnvStack} {ctl ctl' : Ctl} {σ : Mem} {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    (h : Step.CallOf M e fr ρ ctl σ (e', ρ', ctl', σ')) (hκ : ctl'.κ = ctl.κ) : False := by
  obtain ⟨_, _, _, _, _, _, -, -, -, -, hout⟩ := h
  have := congrArg (fun c : Config => c.2.2.1.κ) hout
  simp at this
  rw [this] at hκ
  exact absurd hκ (by simp)

theorem Step.CallOf.ne_upd {M : MachineCtx} {e : CoreExpr} {fr : context → context}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    {a : List annot}
    (h : Step.CallOf M e fr ρ ctl σ (e', ρ', ctl.upd a, σ')) : False :=
  h.ne_same_κ rfl

/-- A `CallOf` witness names a call redex of `e`. -/
theorem Step.CallOf.callRedex?_some {M : MachineCtx} {e : CoreExpr} {fr : context → context}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (h : Step.CallOf M e fr ρ ctl σ out) :
    ∃ ctx f pes, callRedex? e = some (ctx, f, pes) := by
  obtain ⟨ctx, f, pes, _, _, _, hc, -⟩ := h
  exact ⟨ctx, f, pes, hc⟩

/-- The call rule seen from a frame: `Step.call` at the framed node IS
    `CallOf` of the body (the frame's context is the redex's context
    under the frame; the redex node is the body's). -/
theorem Step.callOf_of_call_sseq {M : MachineCtx} {a : List annot} {pat : pattern}
    {e1 e2 : CoreExpr} {ctx : context} {f : sym} {pes : List (generic_pexpr Unit sym)}
    {params : List (sym × core_base_type)} {body : CoreExpr} {vs : List value}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    (hc : callRedex? (Expr a (Esseq pat e1 e2)) = some (ctx, f, pes))
    (hvs : evalPexprs M.tagDefs M.extern ρ pes = some vs)
    (hf : lookupProc M.file M.extern f = some (params, body))
    (hlen : params.length = vs.length) :
    Step.CallOf M e1 (fun c => Csseq a pat c e2) ρ ctl σ
      (body, procEnv params vs :: ρ,
       ctl.callPush (redexAnnots (Expr a (Esseq pat e1 e2))) ctx f, σ) := by
  rw [callRedex?_sseq, Option.map_eq_some_iff] at hc
  obtain ⟨⟨ctx1, f1, pes1⟩, hc1, hq⟩ := hc
  obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
    exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq,
      congrArg (fun q => q.2.2) hq⟩
  refine ⟨ctx1, f1, pes1, _, _, _, hc1, hvs, hf, hlen, ?_⟩
  rw [redexAnnots_sseq_of_nv _ _ _ (toVal_none_of_callRedex?_some hc1)]

/-- Inversion at an Esseq node: a frame step of a non-jump, non-call,
    non-value e1 (a general-arm step, its control write threaded), one of
    the betas (at ANY value annotations), THE GLOBAL JUMP (frame
    discarded), or THE CALL of e1 with the `Csseq` frame CAPTURED. -/
theorem Step.sseq_inv {M : MachineCtx} {a : List annot} {pat : pattern}
    {e1 e2 : CoreExpr}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (h : Step M (Expr a (Esseq pat e1 e2), ρ, ctl, σ) out) :
    (∃ e1' ρ' ctl' σ', jumpRedex? e1 = none ∧ callRedex? e1 = none ∧ toVal e1 = none ∧
        Step M (e1, ρ, ctl, σ) (e1', ρ', ctl', σ') ∧
        out = (Expr a (Esseq pat e1' e2), ρ', ctl', σ')) ∨
    (∃ pa bty a1 b1 v ev0 evs, pat = Pattern pa (CaseBase (none, bty)) ∧
        e1 = ofValA (.pure a1 b1 v) ∧ ρ = ev0 :: evs ∧ out = (e2, ρ, ctl.upd a, σ)) ∨
    (∃ pa bty a1 a2 b1 ds v ev0 evs, pat = Pattern pa (CaseBase (none, bty)) ∧
        e1 = ofValA (.annot a1 a2 b1 ds v) ∧ ρ = ev0 :: evs ∧
        out = (Expr [] (Eannot ds e2), ρ, ctl.upd a, σ)) ∨
    (∃ l pes params cont vs ev0 evs, jumpRedex? e1 = some (l, pes) ∧
        ρ = ev0 :: evs ∧ lookupLabel (M.labelsAt ctl.proc) l = some (params, cont) ∧
        evalPexprs M.tagDefs M.extern ρ pes = some vs ∧
        out = (cont, bindArgs params vs ρ, ctl.upd (redexAnnots e1), σ)) ∨
    (∃ pa' pb' x bty' a1 b1 ov ev0 evs, pat = specPat pa' pb' x bty' ∧
        e1 = ofValA (.pure a1 b1 (Vloaded (LVspecified ov))) ∧ ρ = ev0 :: evs ∧
        out = (e2, update_env (specPat pa' pb' x bty')
          (Vloaded (LVspecified ov)) ρ, ctl.upd a, σ)) ∨
    (∃ pa' pb' x bty' a1 a2 b1 ds ov ev0 evs, pat = specPat pa' pb' x bty' ∧
        e1 = ofValA (.annot a1 a2 b1 ds (Vloaded (LVspecified ov))) ∧ ρ = ev0 :: evs ∧
        out = (Expr [] (Eannot ds e2), update_env (specPat pa' pb' x bty')
          (Vloaded (LVspecified ov)) ρ, ctl.upd a, σ)) ∨
    (∃ pa' x bty' a1 b1 v ev0 evs, pat = symPat pa' x bty' ∧
        e1 = ofValA (.pure a1 b1 v) ∧ ρ = ev0 :: evs ∧
        out = (e2, update_env (symPat pa' x bty') v ρ, ctl.upd a, σ)) ∨
    (∃ pa' x bty' a1 a2 b1 ds v ev0 evs, pat = symPat pa' x bty' ∧
        e1 = ofValA (.annot a1 a2 b1 ds v) ∧ ρ = ev0 :: evs ∧
        out = (Expr [] (Eannot ds e2), update_env (symPat pa' x bty') v ρ, ctl.upd a, σ)) ∨
    (∃ pa' ls a1 b1 vs ev0 evs, pat = tuplePat pa' ls ∧
        e1 = ofValA (.pure a1 b1 (Vtuple vs)) ∧ ρ = ev0 :: evs ∧
        out = (e2, update_env (tuplePat pa' ls) (Vtuple vs) ρ, ctl.upd a, σ)) ∨
    (∃ pa' ls a1 a2 b1 ds vs ev0 evs, pat = tuplePat pa' ls ∧
        e1 = ofValA (.annot a1 a2 b1 ds (Vtuple vs)) ∧ ρ = ev0 :: evs ∧
        out = (Expr [] (Eannot ds e2), update_env (tuplePat pa' ls) (Vtuple vs) ρ, ctl.upd a, σ)) ∨
    Step.CallOf M e1 (fun c => Csseq a pat c e2) ρ ctl σ out := by
  cases h with
  | sseq_ctx hnj hnc hnv hs => exact .inl ⟨_, _, _, _, hnj, hnc, hnv, hs, rfl⟩
  | sseq_pure => exact .inr (.inl ⟨_, _, _, _, _, _, _, rfl, rfl, rfl, rfl⟩)
  | sseq_annot => exact .inr (.inr (.inl ⟨_, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl⟩))
  | run hj hl hvs =>
    rw [jumpRedex?_sseq] at hj
    refine .inr (.inr (.inr (.inl ⟨_, _, _, _, _, _, _, hj, rfl, hl, hvs, ?_⟩)))
    rw [redexAnnots_sseq_of_nv _ _ _ (toVal_none_of_jumpRedex?_some hj)]
  | sseq_spec_pure =>
    exact .inr (.inr (.inr (.inr (.inl
      ⟨_, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl⟩))))
  | sseq_spec_annot =>
    exact .inr (.inr (.inr (.inr (.inr (.inl
      ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl⟩)))))
  | sseq_sym_pure =>
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨_, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl⟩))))))
  | sseq_sym_annot =>
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨_, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl⟩)))))))
  | sseq_tuple_pure =>
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨_, _, _, _, _, _, _, rfl, rfl, rfl, rfl⟩))))))))
  | sseq_tuple_annot =>
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨_, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl⟩)))))))))
  | call hc hvs hf hlen =>
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
      (Step.callOf_of_call_sseq hc hvs hf hlen))))))))))

theorem Step.callOf_of_call_wseq {M : MachineCtx} {a : List annot} {pat : pattern}
    {e1 e2 : CoreExpr} {ctx : context} {f : sym} {pes : List (generic_pexpr Unit sym)}
    {params : List (sym × core_base_type)} {body : CoreExpr} {vs : List value}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    (hc : callRedex? (Expr a (Ewseq pat e1 e2)) = some (ctx, f, pes))
    (hvs : evalPexprs M.tagDefs M.extern ρ pes = some vs)
    (hf : lookupProc M.file M.extern f = some (params, body))
    (hlen : params.length = vs.length) :
    Step.CallOf M e1 (fun c => Cwseq a pat c e2) ρ ctl σ
      (body, procEnv params vs :: ρ,
       ctl.callPush (redexAnnots (Expr a (Ewseq pat e1 e2))) ctx f, σ) := by
  rw [callRedex?_wseq, Option.map_eq_some_iff] at hc
  obtain ⟨⟨ctx1, f1, pes1⟩, hc1, hq⟩ := hc
  obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
    exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq,
      congrArg (fun q => q.2.2) hq⟩
  refine ⟨ctx1, f1, pes1, _, _, _, hc1, hvs, hf, hlen, ?_⟩
  rw [redexAnnots_wseq_of_nv _ _ _ (toVal_none_of_callRedex?_some hc1)]

/-- Inversion at an Ewseq node (the wildcard-only `sseq_inv` shape). -/
theorem Step.wseq_inv {M : MachineCtx} {a : List annot} {pat : pattern}
    {e1 e2 : CoreExpr}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (h : Step M (Expr a (Ewseq pat e1 e2), ρ, ctl, σ) out) :
    (∃ e1' ρ' ctl' σ', jumpRedex? e1 = none ∧ callRedex? e1 = none ∧ toVal e1 = none ∧
        Step M (e1, ρ, ctl, σ) (e1', ρ', ctl', σ') ∧
        out = (Expr a (Ewseq pat e1' e2), ρ', ctl', σ')) ∨
    (∃ pa bty a1 b1 v ev0 evs, pat = Pattern pa (CaseBase (none, bty)) ∧
        e1 = ofValA (.pure a1 b1 v) ∧ ρ = ev0 :: evs ∧ out = (e2, ρ, ctl.upd a, σ)) ∨
    (∃ pa bty a1 a2 b1 ds v ev0 evs, pat = Pattern pa (CaseBase (none, bty)) ∧
        e1 = ofValA (.annot a1 a2 b1 ds v) ∧ ρ = ev0 :: evs ∧
        out = (Expr [] (Eannot ds e2), ρ, ctl.upd a, σ)) ∨
    (∃ l pes params cont vs ev0 evs, jumpRedex? e1 = some (l, pes) ∧
        ρ = ev0 :: evs ∧ lookupLabel (M.labelsAt ctl.proc) l = some (params, cont) ∧
        evalPexprs M.tagDefs M.extern ρ pes = some vs ∧
        out = (cont, bindArgs params vs ρ, ctl.upd (redexAnnots e1), σ)) ∨
    (∃ pa' x bty' a1 b1 v ev0 evs, pat = symPat pa' x bty' ∧
        e1 = ofValA (.pure a1 b1 v) ∧ ρ = ev0 :: evs ∧
        out = (e2, update_env (symPat pa' x bty') v ρ, ctl.upd a, σ)) ∨
    (∃ pa' x bty' a1 a2 b1 ds v ev0 evs, pat = symPat pa' x bty' ∧
        e1 = ofValA (.annot a1 a2 b1 ds v) ∧ ρ = ev0 :: evs ∧
        out = (Expr [] (Eannot ds e2), update_env (symPat pa' x bty') v ρ, ctl.upd a, σ)) ∨
    (∃ pa' ls a1 b1 vs ev0 evs, pat = tuplePat pa' ls ∧
        e1 = ofValA (.pure a1 b1 (Vtuple vs)) ∧ ρ = ev0 :: evs ∧
        out = (e2, update_env (tuplePat pa' ls) (Vtuple vs) ρ, ctl.upd a, σ)) ∨
    (∃ pa' ls a1 a2 b1 ds vs ev0 evs, pat = tuplePat pa' ls ∧
        e1 = ofValA (.annot a1 a2 b1 ds (Vtuple vs)) ∧ ρ = ev0 :: evs ∧
        out = (Expr [] (Eannot ds e2), update_env (tuplePat pa' ls) (Vtuple vs) ρ, ctl.upd a, σ)) ∨
    Step.CallOf M e1 (fun c => Cwseq a pat c e2) ρ ctl σ out := by
  cases h with
  | wseq_ctx hnj hnc hnv hs => exact .inl ⟨_, _, _, _, hnj, hnc, hnv, hs, rfl⟩
  | wseq_pure => exact .inr (.inl ⟨_, _, _, _, _, _, _, rfl, rfl, rfl, rfl⟩)
  | wseq_annot => exact .inr (.inr (.inl ⟨_, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl⟩))
  | wseq_sym_pure =>
    exact .inr (.inr (.inr (.inr (.inl ⟨_, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl⟩))))
  | wseq_sym_annot =>
    exact .inr (.inr (.inr (.inr (.inr (.inl
      ⟨_, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl⟩)))))
  | wseq_tuple_pure =>
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨_, _, _, _, _, _, _, rfl, rfl, rfl, rfl⟩))))))
  | wseq_tuple_annot =>
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨_, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl⟩)))))))
  | run hj hl hvs =>
    rw [jumpRedex?_wseq] at hj
    refine .inr (.inr (.inr (.inl ⟨_, _, _, _, _, _, _, hj, rfl, hl, hvs, ?_⟩)))
    rw [redexAnnots_wseq_of_nv _ _ _ (toVal_none_of_jumpRedex?_some hj)]
  | call hc hvs hf hlen =>
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
      (Step.callOf_of_call_wseq hc hvs hf hlen))))))))

theorem Step.callOf_of_call_annot {M : MachineCtx} {a : List annot} {ds : List dyn_annotation}
    {b : CoreExpr} {ctx : context} {f : sym} {pes : List (generic_pexpr Unit sym)}
    {params : List (sym × core_base_type)} {body : CoreExpr} {vs : List value}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} (hg : annotRooted b = false)
    (hc : callRedex? (Expr a (Eannot ds b)) = some (ctx, f, pes))
    (hvs : evalPexprs M.tagDefs M.extern ρ pes = some vs)
    (hf : lookupProc M.file M.extern f = some (params, body))
    (hlen : params.length = vs.length) :
    Step.CallOf M b (fun c => Cannot a ds c) ρ ctl σ
      (body, procEnv params vs :: ρ,
       ctl.callPush (redexAnnots (Expr a (Eannot ds b))) ctx f, σ) := by
  rw [callRedex?_annot_of_not_root _ _ hg, Option.map_eq_some_iff] at hc
  obtain ⟨⟨ctx1, f1, pes1⟩, hc1, hq⟩ := hc
  obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
    exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq,
      congrArg (fun q => q.2.2) hq⟩
  refine ⟨ctx1, f1, pes1, _, _, _, hc1, hvs, hf, hlen, ?_⟩
  rw [redexAnnots_annot_of_not_root _ _ hg]

/-- Inversion at an Eannot node: Cannot-descent of a non-jump, non-call
    body (its control write threaded), the ANNOTS merge, the global jump
    through the Cannot frame, THE CALL of the body with the `Cannot` frame
    captured, or REMOVE-ANNOT at a non-empty call stack (the body a bare
    value at any annotations). -/
theorem Step.annot_inv {M : MachineCtx} {a : List annot}
    {ds : List dyn_annotation}
    {b : CoreExpr} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config}
    (h : Step M (Expr a (Eannot ds b), ρ, ctl, σ) out) :
    (annotRooted b = false ∧ jumpRedex? b = none ∧ callRedex? b = none ∧ toVal b = none ∧
        ∃ b' ρ' ctl' σ', Step M (b, ρ, ctl, σ) (b', ρ', ctl', σ') ∧
        out = (Expr a (Eannot ds b'), ρ', ctl', σ')) ∨
    (∃ a2 ds2 c, b = Expr a2 (Eannot ds2 c) ∧
        out = (Expr (a ++ a2) (Eannot (ds ++ ds2) c), ρ, ctl.upd a, σ)) ∨
    (∃ l pes params cont vs ev0 evs, annotRooted b = false ∧
        jumpRedex? b = some (l, pes) ∧
        ρ = ev0 :: evs ∧ lookupLabel (M.labelsAt ctl.proc) l = some (params, cont) ∧
        evalPexprs M.tagDefs M.extern ρ pes = some vs ∧
        out = (cont, bindArgs params vs ρ, ctl.upd (redexAnnots b), σ)) ∨
    (annotRooted b = false ∧ Step.CallOf M b (fun c => Cannot a ds c) ρ ctl σ out) ∨
    (∃ a2 b1 v pc κ, b = ofValA (.pure a2 b1 v) ∧ ctl.κ = pc :: κ ∧
        out = (ofValA (.pure a2 b1 v), ρ, ctl, σ)) := by
  cases h with
  | annot_ctx hnj hnc hnv hg hs => exact .inl ⟨hg, hnj, hnc, hnv, _, _, _, _, hs, rfl⟩
  | annot_merge => exact .inr (.inl ⟨_, _, _, rfl, rfl⟩)
  | run hj hl hvs =>
    by_cases hr : annotRooted b = true
    · rw [jumpRedex?_annot_of_root _ _ hr] at hj; cases hj
    · have hr' : annotRooted b = false := by simpa using hr
      rw [jumpRedex?_annot_of_not_root _ _ hr'] at hj
      refine .inr (.inr (.inl ⟨_, _, _, _, _, _, _, hr', hj, rfl, hl, hvs, ?_⟩))
      rw [redexAnnots_annot_of_not_root _ _ hr']
  | call hc hvs hf hlen =>
    by_cases hr : annotRooted b = true
    · rw [callRedex?_annot_of_root _ _ hr] at hc; cases hc
    · have hr' : annotRooted b = false := by simpa using hr
      exact .inr (.inr (.inr (.inl ⟨hr', Step.callOf_of_call_annot hr' hc hvs hf hlen⟩)))
  | ret_annot => exact .inr (.inr (.inr (.inr ⟨_, _, _, _, _, rfl, rfl, rfl⟩)))

theorem Step.callOf_of_call_bound {M : MachineCtx} {a : List annot}
    {b : CoreExpr} {ctx : context} {f : sym} {pes : List (generic_pexpr Unit sym)}
    {params : List (sym × core_base_type)} {body : CoreExpr} {vs : List value}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    (hc : callRedex? (Expr a (Ebound b)) = some (ctx, f, pes))
    (hvs : evalPexprs M.tagDefs M.extern ρ pes = some vs)
    (hf : lookupProc M.file M.extern f = some (params, body))
    (hlen : params.length = vs.length) :
    Step.CallOf M b (fun c => Cbound a c) ρ ctl σ
      (body, procEnv params vs :: ρ,
       ctl.callPush (redexAnnots (Expr a (Ebound b))) ctx f, σ) := by
  rw [callRedex?_bound, Option.map_eq_some_iff] at hc
  obtain ⟨⟨ctx1, f1, pes1⟩, hc1, hq⟩ := hc
  obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
    exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq,
      congrArg (fun q => q.2.2) hq⟩
  refine ⟨ctx1, f1, pes1, _, _, _, hc1, hvs, hf, hlen, ?_⟩
  rw [redexAnnots_bound_of_nv _ (toVal_none_of_callRedex?_some hc1)]

/-- E1: inversion at an Ebound node: Cbound-descent of a non-jump,
    non-call, non-value body, REMOVE-BOUND at a bare or annotated value,
    the global jump through the frame, or THE CALL of the body with the
    `Cbound` frame captured. -/
theorem Step.bound_inv {M : MachineCtx} {a : List annot} {b : CoreExpr}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (h : Step M (Expr a (Ebound b), ρ, ctl, σ) out) :
    (∃ b' ρ' ctl' σ', jumpRedex? b = none ∧ callRedex? b = none ∧ toVal b = none ∧
        Step M (b, ρ, ctl, σ) (b', ρ', ctl', σ') ∧
        out = (Expr a (Ebound b'), ρ', ctl', σ')) ∨
    (∃ a1 b1 v, b = ofValA (.pure a1 b1 v) ∧ out = (ofValA (.pure a1 b1 v), ρ, ctl.upd a, σ)) ∨
    (∃ a1 a2 b1 ds v, b = ofValA (.annot a1 a2 b1 ds v) ∧
        out = (ofValA (.pure a2 b1 v), ρ, ctl.upd a, σ)) ∨
    (∃ l pes params cont vs ev0 evs, jumpRedex? b = some (l, pes) ∧
        ρ = ev0 :: evs ∧ lookupLabel (M.labelsAt ctl.proc) l = some (params, cont) ∧
        evalPexprs M.tagDefs M.extern ρ pes = some vs ∧
        out = (cont, bindArgs params vs ρ, ctl.upd (redexAnnots b), σ)) ∨
    Step.CallOf M b (fun c => Cbound a c) ρ ctl σ out := by
  cases h with
  | bound_ctx hnj hnc hnv hs => exact .inl ⟨_, _, _, _, hnj, hnc, hnv, hs, rfl⟩
  | bound_pure => exact .inr (.inl ⟨_, _, _, rfl, rfl⟩)
  | bound_annot => exact .inr (.inr (.inl ⟨_, _, _, _, _, rfl, rfl⟩))
  | run hj hl hvs =>
    rw [jumpRedex?_bound] at hj
    refine .inr (.inr (.inr (.inl ⟨_, _, _, _, _, _, _, hj, rfl, hl, hvs, ?_⟩)))
    rw [redexAnnots_bound_of_nv _ (toVal_none_of_jumpRedex?_some hj)]
  | call hc hvs hf hlen =>
    exact .inr (.inr (.inr (.inr (Step.callOf_of_call_bound hc hvs hf hlen))))

/-- Inversion at an Esave node: either the entry TAU (value-shaped
    initializers) or the parameter-EVAL step. -/
theorem Step.save_inv {M : MachineCtx} {a : List annot}
    {sb : sym × core_base_type}
    {ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
    {body : CoreExpr} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config}
    (h : Step M (Expr a (Esave sb ps body), ρ, ctl, σ) out) :
    (∃ cvals ev0 evs, ρ = ev0 :: evs ∧
      valueFromPexprs (saveParamPexprs ps) = some cvals ∧
      out = (body, bindSaveParams ps cvals ρ, ctl.upd a, σ)) ∨
    (∃ cvals, valueFromPexprs (saveParamPexprs ps) = none ∧
      evalPexprs M.tagDefs M.extern ρ (saveParamPexprs ps) = some cvals ∧
      out = (Expr a (Esave sb (saveParamsWithValues ps cvals) body), ρ, ctl.upd a, σ)) := by
  cases h with
  | save hvals => exact .inl ⟨_, _, _, rfl, hvals, rfl⟩
  | save_eval hnv hvals => exact .inr ⟨_, hnv, hvals, rfl⟩
  | run hj hl hvs => simp [jumpRedex?] at hj
  | call hc hvs hf hlen => simp at hc

/-- Inversion at an Esave node with VALUE initializers: the entry TAU. -/
theorem Step.save_vals_inv {M : MachineCtx} {a : List annot}
    {sb : sym × core_base_type}
    {ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
    {body : CoreExpr} {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {cvals : List value}
    {out : Config}
    (hvals : valueFromPexprs (saveParamPexprs ps) = some cvals)
    (h : Step M (Expr a (Esave sb ps body), ρ, ctl, σ) out) :
    ∃ ev0 evs, ρ = ev0 :: evs ∧ out = (body, bindSaveParams ps cvals ρ, ctl.upd a, σ) := by
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
      out = (Expr a (Esave sb (saveParamsWithValues ps cvals) body), ρ, ctl.upd a, σ) := by
  rcases h.save_inv with ⟨_, _, _, _, hvals, _⟩ | ⟨cvals, _, hvals, hout⟩
  · rw [hnv] at hvals; cases hvals
  · exact ⟨cvals, hvals, hout⟩

/-- Inversion at an Eif node. -/
theorem Step.if_inv {M : MachineCtx} {a : List annot}
    {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (h : Step M (Expr a (Eif g e2 e3), ρ, ctl, σ) out) :
    (evalPexpr M.tagDefs M.extern ρ g = some Vtrue ∧ out = (e2, ρ, ctl.upd a, σ)) ∨
    (evalPexpr M.tagDefs M.extern ρ g = some Vfalse ∧ out = (e3, ρ, ctl.upd a, σ)) := by
  cases h with
  | if_true hg => exact .inl ⟨hg, rfl⟩
  | if_false hg => exact .inr ⟨hg, rfl⟩
  | run hj hl hvs => simp [jumpRedex?] at hj
  | call hc hvs hf hlen => simp at hc

/-- Inversion at an Ecase node (E2: two arms — the substitution TAU at a
    value scrutinee, the EVAL round at a non-value one). -/
theorem Step.case_inv {M : MachineCtx} {a : List annot}
    {pe : generic_pexpr Unit sym} {pats : List (pattern × CoreExpr)}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (h : Step M (Expr a (Ecase pe pats), ρ, ctl, σ) out) :
    (∃ cval e', valueFromPexpr pe = some cval ∧
      select_case subst_sym_expr cval pats = some e' ∧
      out = (e', ρ, ctl.upd a, σ)) ∨
    (∃ cval, valueFromPexpr pe = none ∧ evalPexpr M.tagDefs M.extern ρ pe = some cval ∧
      out = (Expr a (Ecase (Pexpr [] () (PEval cval)) pats), ρ, ctl.upd a, σ)) := by
  cases h with
  | case_value hv hsel => exact .inl ⟨_, _, hv, hsel, rfl⟩
  | case_eval hnv hv => exact .inr ⟨_, hnv, hv, rfl⟩
  | run hj hl hvs => simp [jumpRedex?] at hj
  | call hc hvs hf hlen => simp at hc

/-- The value-scrutinee instance of `case_inv` (the pre-E2 statement). -/
theorem Step.case_value_inv {M : MachineCtx} {a : List annot}
    {pe : generic_pexpr Unit sym} {pats : List (pattern × CoreExpr)}
    {cval : value} {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (hv : valueFromPexpr pe = some cval)
    (h : Step M (Expr a (Ecase pe pats), ρ, ctl, σ) out) :
    ∃ e', select_case subst_sym_expr cval pats = some e' ∧ out = (e', ρ, ctl.upd a, σ) := by
  rcases h.case_inv with ⟨cval', e', hv', hsel, hout⟩ | ⟨_, hnv, -, -⟩
  · obtain rfl : cval = cval' := Option.some.inj (hv.symm.trans hv')
    exact ⟨e', hsel, hout⟩
  · rw [hv] at hnv; cases hnv

/-- The non-value-scrutinee instance of `case_inv` (E2). -/
theorem Step.case_op_inv {M : MachineCtx} {a : List annot}
    {pe : generic_pexpr Unit sym} {pats : List (pattern × CoreExpr)}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (hnv : valueFromPexpr pe = none)
    (h : Step M (Expr a (Ecase pe pats), ρ, ctl, σ) out) :
    ∃ cval, evalPexpr M.tagDefs M.extern ρ pe = some cval ∧
      out = (Expr a (Ecase (Pexpr [] () (PEval cval)) pats), ρ, ctl.upd a, σ) := by
  rcases h.case_inv with ⟨cval, e', hv, -, -⟩ | ⟨cval, -, hv, hout⟩
  · rw [hnv] at hv; cases hv
  · exact ⟨cval, hv, hout⟩

/-- Inversion at an Epure node (S4): the big-step PURE evaluation. -/
theorem Step.pure_inv {M : MachineCtx} {a : List annot}
    {pe : generic_pexpr Unit sym} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config}
    (hnv : valueFromPexpr pe = none)
    (h : Step M (Expr a (Epure pe), ρ, ctl, σ) out) :
    ∃ v, valueFromPexpr pe = none ∧ evalPexpr M.tagDefs M.extern ρ pe = some v ∧
      out = (Expr a (Epure (Pexpr [] () (PEval v))), ρ, ctl.upd a, σ) := by
  cases h with
  | pure_eval hnv hv => exact ⟨_, hnv, hv, rfl⟩
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | ret => rw [valueFromPexpr_val] at hnv; cases hnv

/-- Inversion at a positive load whose pointer operand is NOT a
    value (S4): the ACTION_EVAL step. -/
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
               (Pexpr [] () (PEval (Vobject (OVpointer pv)))) mo)))), ρ, ctl.upd a, σ) := by
  cases h with
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | load h1 h2 hmem => rw [hnv2] at h2; cases h2
  | load_eval hnv2' hv2 => exact ⟨_, hv2, rfl⟩

/-- Inversion at the pointer-equality memop with VALUE operands. -/
theorem Step.memop_ptreq_inv {M : MachineCtx} {a : List annot}
    {pe1 pe2 : generic_pexpr Unit sym} {pv1 pv2 : CerbMem.PointerValue}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (h1 : valueFromPexpr pe1 = some (Vobject (OVpointer pv1)))
    (h2 : valueFromPexpr pe2 = some (Vobject (OVpointer pv2)))
    (h : Step M (Expr a (Ememop PtrEq [pe1, pe2]), ρ, ctl, σ) out) :
    ∃ b σ', applyMemM (CerbMem.eqPtrval default pv1 pv2) σ = some (b, σ') ∧
      out = (Expr [] (Epure (Pexpr [] () (PEval (boolValue b)))), ρ, ctl.upd a, σ') := by
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
    values. -/
theorem Step.memop_vals_inv {M : MachineCtx} {a : List annot} {v1 v2 : value}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (h : Step M (Expr a (Ememop PtrEq [Pexpr [] () (PEval v1), Pexpr [] () (PEval v2)]),
      ρ, ctl, σ) out) :
    ∃ pv1 pv2 b σ', v1 = Vobject (OVpointer pv1) ∧ v2 = Vobject (OVpointer pv2) ∧
      applyMemM (CerbMem.eqPtrval default pv1 pv2) σ = some (b, σ') ∧
      out = (Expr [] (Epure (Pexpr [] () (PEval (boolValue b)))), ρ, ctl.upd a, σ') := by
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
        [Pexpr [] () (PEval v1), Pexpr [] () (PEval v2)]), ρ, ctl.upd a, σ) := by
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
                (Pexpr [] () (PEval cv)) mo)))), ρ, ctl.upd a, σ) := by
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

/-! E2: the flat tuple binder pattern against the three other binder shapes. -/

theorem tuplePat_ne_base {pa' : List annot} {bty' : core_base_type}
    {pa : List annot} {ls : List TupleLeaf}
    (h : Pattern pa' (CaseBase (none, bty')) = tuplePat pa ls) : False := by
  simp [tuplePat] at h

theorem symPat_ne_tuple {pa : List annot} {x : sym} {bty : core_base_type}
    {pa' : List annot} {ls : List TupleLeaf}
    (h : symPat pa x bty = tuplePat pa' ls) : False := by
  simp [symPat, tuplePat] at h

theorem specPat_ne_tuple {pa pb : List annot} {x : sym} {bty : core_base_type}
    {pa' : List annot} {ls : List TupleLeaf}
    (h : specPat pa pb x bty = tuplePat pa' ls) : False := by
  simp [specPat, tuplePat] at h

theorem leafPat_inj {t t' : TupleLeaf} (h : leafPat t = leafPat t') : t = t' := by
  obtain ⟨a, x, b⟩ := t
  obtain ⟨a', x', b'⟩ := t'
  cases h
  rfl

theorem map_leafPat_inj {ls ls' : List TupleLeaf}
    (h : ls.map leafPat = ls'.map leafPat) : ls = ls' := by
  induction ls generalizing ls' with
  | nil => cases ls' with
    | nil => rfl
    | cons _ _ => cases h
  | cons t ts ih => cases ls' with
    | nil => cases h
    | cons t' ts' =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [leafPat_inj h.1, ih h.2]

theorem tuplePat_inj {pa pa' : List annot} {ls ls' : List TupleLeaf}
    (h : tuplePat pa ls = tuplePat pa' ls') : pa = pa' ∧ ls = ls' := by
  unfold tuplePat at h
  injection h with h1 h2
  injection h2 with _ h3
  exact ⟨h1, map_leafPat_inj h3⟩

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

theorem toValA_pure_none {a : List annot} {pe : generic_pexpr Unit sym}
    (hnv : valueFromPexpr pe = none) : toValA (Expr a (Epure pe)) = none :=
  toValA_none_of_toVal_none (toVal_pure_none hnv)

/-! ## Canonical redex spellings (E1: annotation-parametric — the node's
static annotation list is the FIRST argument; the pre-E1 spellings are the
`[]` instances) -/

/-- Canonical spelling of the S4 PURE redex (non-value pure
    expression at the root). -/
def pureRedex (a : List annot) (pe : generic_pexpr Unit sym) : CoreExpr :=
  Expr a (Epure pe)

/-- Canonical spelling of the S4 load ACTION_EVAL redex: positive
    strong load, canonical evaluated type operand, UNevaluated
    pointer operand. -/
def loadOpRedex (a : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (ty : ctype) (pe2 : generic_pexpr Unit sym) (mo : memory_order) : CoreExpr :=
  Expr a (Eaction (Paction polarity.Pos (Action loc ann
    (Load0 (Pexpr [] () (PEval (Vctype ty))) pe2 mo))))

/-- Canonical spelling of a memop redex: operands per instance. -/
def memopRedex (a : List annot) (mop : memop) (pes : List (generic_pexpr Unit sym)) : CoreExpr :=
  Expr a (Ememop mop pes)

/-- The pointer-equality memop at canonical VALUE operands (the
    post-ACTION_EVAL shape the memop axiom fires at). -/
def memopPtrEqVals (a : List annot) (v1 v2 : value) : CoreExpr :=
  memopRedex a PtrEq [Pexpr [] () (PEval v1), Pexpr [] () (PEval v2)]

/-- Canonical spelling of the store ACTION_EVAL redex: positive
    strong non-locking store, canonical evaluated type operand,
    UNevaluated pointer/value operands. -/
def storeOpRedex (a : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (ty : ctype) (pe2 pe3 : generic_pexpr Unit sym) (mo : memory_order) :
    CoreExpr :=
  Expr a (Eaction (Paction polarity.Pos (Action loc ann
    (Store0 false (Pexpr [] () (PEval (Vctype ty))) pe2 pe3 mo))))

/-- Canonical spelling of the kill redex (kill/free arc K2): positive
    strong kill of any kind at the canonical EVALUATED pointer operand
    (`Rules.killExpr` is the same spelling). -/
def killRedex (a : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (kind : kill_kind) (pv : CerbMem.PointerValue) : CoreExpr :=
  Expr a (Eaction (Paction polarity.Pos (Action loc ann
    (Kill kind (Pexpr [] () (PEval (Vobject (OVpointer pv))))))))

/-- Canonical spelling of the kill ACTION_EVAL redex: positive strong
    kill at an UNevaluated pointer operand. -/
def killOpRedex (a : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (kind : kill_kind) (pe : generic_pexpr Unit sym) : CoreExpr :=
  Expr a (Eaction (Paction polarity.Pos (Action loc ann (Kill kind pe))))

/-- Canonical spelling of the alloc redex (kill/free arc K3): positive
    strong dynamic allocation at canonical EVALUATED integer operands
    (`Rules.allocExpr` is the same spelling). -/
def allocRedex (a : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (align size : CerbMem.IntegerValue) (pref : prefix0) : CoreExpr :=
  Expr a (Eaction (Paction polarity.Pos (Action loc ann
    (Alloc0 (Pexpr [] () (PEval (Vobject (OVinteger align))))
            (Pexpr [] () (PEval (Vobject (OVinteger size)))) pref))))

/-- Canonical spelling of the alloc ACTION_EVAL redex: positive strong
    dynamic allocation at operands that are NOT all values. -/
def allocOpRedex (a : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (pe1 pe2 : generic_pexpr Unit sym) (pref : prefix0) : CoreExpr :=
  Expr a (Eaction (Paction polarity.Pos (Action loc ann (Alloc0 pe1 pe2 pref))))

/-- E1: canonical spelling of the create ACTION_EVAL redex: positive
    strong create at operands that are NOT all values (every emitted
    `create(Ivalignof(ty), ty)`). -/
def createOpRedex (a : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (pe1 pe2 : generic_pexpr Unit sym) (pref : prefix0) : CoreExpr :=
  Expr a (Eaction (Paction polarity.Pos (Action loc ann (Create pe1 pe2 pref))))

/-- E1: canonical spelling of the `bound` node. -/
def boundRedex (a : List annot) (b : CoreExpr) : CoreExpr := Expr a (Ebound b)

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
@[reducible] def spikeCtl : Ctl := ⟨[], none, default, default, default⟩

/-- The entry control of the jump profile: empty call stack, IN
    PROCEDURE `p` (what `Erun` reads the label map at), default
    execution location (the `procThread` literal's control fields). -/
@[reducible] def procCtl (p : sym) : Ctl := ⟨[], some p, default, default, default⟩

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
    tid := 0, parent := none, errno := default,
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
