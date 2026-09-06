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
import LemLibTheorems

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

/-- E4: the value injection is injective on lists. -/
theorem map_ofValA_inj : ∀ {ws ws' : List SpikeValA}, ws.map ofValA = ws'.map ofValA → ws = ws'
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | w :: ws, w' :: ws', h => by
    rw [List.map_cons, List.map_cons] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    rw [ofValA_inj h1, map_ofValA_inj h2]

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

/-! ## E4: the `unseq` vocabulary (dialect arc E4, docs/2026-09-05_e4-notes.md)

The sequential driver's `Eunseq`: get_ctx at an `unseq` whose components are
not all irreducible walks the components LEFT TO RIGHT and PREPENDS each
reducible component's contexts to the accumulator (`get_ctx_unseq_aux`,
core_reduction.lem:590–601), so the LAST reducible component's entry heads
the engine's step list and the shipped loop, which takes the FIRST
advanceable entry (`find_can_advance`, driver.lem:1049–1057), reduces that
component — deterministically, while every entry is advanceable. The
mirror FOCUSES the last reducible component (`jumpRedexU?`/`callRedexU?`/
`redexAnnotsU` below, `Step.unseq_ctx`); at all-value components the
node completes into the annotated tuple (`Step.unseq_vals`, the engine's
`one_step_unseq_aux`, mirrored by `collectUnseq`). -/

/-- E4: the engine's value test as a Boolean — `is_irreducible`'s two value
    shapes (Core_reduction.lean:293; `is_irreducible_eq_isValE`,
    Soundness.lean). -/
def isValE (e : CoreExpr) : Bool := (toVal e).isSome

/-- E4: every component is a value — get_ctx's `List.all es is_irreducible`
    at an `Eunseq` node (core_reduction.lem:545). -/
def valsOnly (es : List CoreExpr) : Bool := es.all isValE

@[simp] theorem isValE_ofValA (w : SpikeValA) : isValE (ofValA w) = true := by
  simp [isValE, toVal_ofValA]

theorem isValE_of_toVal_none {e : CoreExpr} (h : toVal e = none) : isValE e = false := by
  simp [isValE, h]

theorem toVal_none_of_isValE_false {e : CoreExpr} (h : isValE e = false) : toVal e = none := by
  unfold isValE at h
  cases hv : toVal e with
  | none => rfl
  | some w => rw [hv] at h; cases h

@[simp] theorem valsOnly_nil : valsOnly [] = true := rfl

@[simp] theorem valsOnly_cons (e : CoreExpr) (es : List CoreExpr) :
    valsOnly (e :: es) = (isValE e && valsOnly es) := rfl

theorem valsOnly_append (es1 es2 : List CoreExpr) :
    valsOnly (es1 ++ es2) = (valsOnly es1 && valsOnly es2) := by
  simp [valsOnly, List.all_append]

theorem valsOnly_map_ofValA (ws : List SpikeValA) : valsOnly (ws.map ofValA) = true := by
  induction ws with
  | nil => rfl
  | cons w ws ih => rw [List.map_cons, valsOnly_cons, isValE_ofValA, ih]; rfl

/-- A list with a non-value component is not all values. -/
theorem valsOnly_append_cons_false {es1 : List CoreExpr} {e : CoreExpr} {es2 : List CoreExpr}
    (hnv : toVal e = none) : valsOnly (es1 ++ e :: es2) = false := by
  rw [valsOnly_append, valsOnly_cons, isValE_of_toVal_none hnv]
  simp

/-- An all-values list is the image of its exact values. -/
theorem valsOnly_true_map {es : List CoreExpr} (h : valsOnly es = true) :
    ∃ ws : List SpikeValA, es = ws.map ofValA := by
  induction es with
  | nil => exact ⟨[], rfl⟩
  | cons e es ih =>
    rw [valsOnly_cons, Bool.and_eq_true] at h
    obtain ⟨ws, rfl⟩ := ih h.2
    have h1 := h.1
    unfold isValE at h1
    cases hv : toVal e with
    | none => rw [hv] at h1; cases h1
    | some w =>
      obtain ⟨wa, -, rfl⟩ := ofValA_of_toVal hv
      exact ⟨wa :: ws, rfl⟩

/-- THE FOCUS EXISTS: a component list that is not all values has a LAST
    reducible component (`e`), every later component (`es2`) a value. -/
theorem focus_exists {es : List CoreExpr} (h : valsOnly es = false) :
    ∃ (es1 : List CoreExpr) (e : CoreExpr) (es2 : List CoreExpr),
      es = es1 ++ e :: es2 ∧ toVal e = none ∧ valsOnly es2 = true := by
  induction es with
  | nil => cases h
  | cons e es ih =>
    cases hv2 : valsOnly es with
    | true =>
      refine ⟨[], e, es, rfl, ?_, hv2⟩
      rw [valsOnly_cons, hv2, Bool.and_true] at h
      exact toVal_none_of_isValE_false h
    | false =>
      obtain ⟨es1, e', es2, rfl, hnv, hv2'⟩ := ih hv2
      exact ⟨e :: es1, e', es2, rfl, hnv, hv2'⟩

/-- THE FOCUS IS UNIQUE: two focus splits of one list agree. -/
theorem focus_unique {es1 es1' : List CoreExpr} {e e' : CoreExpr} {es2 es2' : List CoreExpr}
    (h : es1 ++ e :: es2 = es1' ++ e' :: es2') (hnv : toVal e = none) (hnv' : toVal e' = none)
    (hv2 : valsOnly es2 = true) (hv2' : valsOnly es2' = true) :
    es1 = es1' ∧ e = e' ∧ es2 = es2' := by
  induction es1 generalizing es1' with
  | nil =>
    cases es1' with
    | nil =>
      rw [List.nil_append, List.nil_append] at h
      obtain ⟨rfl, rfl⟩ := List.cons.inj h
      exact ⟨rfl, rfl, rfl⟩
    | cons x xs =>
      rw [List.nil_append, List.cons_append] at h
      obtain ⟨rfl, h2⟩ := List.cons.inj h
      rw [h2, valsOnly_append_cons_false hnv'] at hv2
      cases hv2
  | cons x xs ih =>
    cases es1' with
    | nil =>
      rw [List.nil_append, List.cons_append] at h
      obtain ⟨rfl, h2⟩ := List.cons.inj h
      rw [← h2, valsOnly_append_cons_false hnv] at hv2'
      cases hv2'
    | cons y ys =>
      rw [List.cons_append, List.cons_append] at h
      obtain ⟨rfl, h2⟩ := List.cons.inj h
      obtain ⟨rfl, rfl, rfl⟩ := ih h2
      exact ⟨rfl, rfl, rfl⟩

mutual
/-- E4: the sibling condition of the engine's `is_unseq_with_ccall`
    (core_reduction.lem:501–519: at a `Cunseq` frame the accumulator
    becomes `acc || List.any (es1 ++ es2) has_ccall`): no `Eccall` anywhere
    in the term, on the shapes whose `has_ccall` recursion `esize` bounds
    (the fuelled engine function, core_reduction.lem:474–498 —
    `has_ccall_lemFuel`; bridge `ccallFree_has_ccall`, Soundness.lean).
    E5: `Ecase` descends into EVERY alternative, `Elet` into its body and
    `End` into its alternatives — exactly `has_ccall`'s arms
    (core_reduction.lem:466–474): the corpus places a `case` inside an
    `unseq` component (t4's `&&`, t5's `>`); the selected branch's
    ccall-freedom after `case_value` is `ccallFree_subst` (Soundness.lean,
    the substitution SHAPE lemma at the engine's fuel), and E4's coarse
    `false` at these three constructors is gone. -/
def ccallFree : CoreExpr → Bool
  | Expr _ (Eccall _ _ _ _) => false
  | Expr _ (Ecase _ pats) => ccallFreeAlts pats
  | Expr _ (Elet _ _ e2) => ccallFree e2
  | Expr _ (End es) => ccallFreeList es
  | Expr _ (Esseq _ e1 e2) => ccallFree e1 && ccallFree e2
  | Expr _ (Ewseq _ e1 e2) => ccallFree e1 && ccallFree e2
  | Expr _ (Eif _ e2 e3) => ccallFree e2 && ccallFree e3
  | Expr _ (Eannot _ b) => ccallFree b
  | Expr _ (Ebound b) => ccallFree b
  | Expr _ (Esave _ _ body) => ccallFree body
  | Expr _ (Eunseq es) => ccallFreeList es
  | _ => true
def ccallFreeList : List CoreExpr → Bool
  | [] => true
  | e :: es => ccallFree e && ccallFreeList es
/-- E5: `has_ccall`'s `Ecase` arm — `List.any (fun (_, e) => has_ccall e)`
    over EVERY alternative (core_reduction.lem:466–469). -/
def ccallFreeAlts : List (pattern × CoreExpr) → Bool
  | [] => true
  | (_, e) :: rest => ccallFree e && ccallFreeAlts rest
end

@[simp] theorem ccallFreeAlts_nil : ccallFreeAlts [] = true := rfl
@[simp] theorem ccallFreeAlts_cons (q : pattern × CoreExpr) (rest : List (pattern × CoreExpr)) :
    ccallFreeAlts (q :: rest) = (ccallFree q.2 && ccallFreeAlts rest) := by
  obtain ⟨pat, e⟩ := q; rfl

theorem ccallFreeAlts_mem {pats : List (pattern × CoreExpr)} (h : ccallFreeAlts pats = true)
    {q : pattern × CoreExpr} (hq : q ∈ pats) : ccallFree q.2 = true := by
  induction pats with
  | nil => cases hq
  | cons r rest ih =>
    rw [ccallFreeAlts_cons, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h.1
    · exact ih h.2 hq

@[simp] theorem ccallFreeList_nil : ccallFreeList [] = true := rfl
@[simp] theorem ccallFreeList_cons (e : CoreExpr) (es : List CoreExpr) :
    ccallFreeList (e :: es) = (ccallFree e && ccallFreeList es) := rfl

theorem ccallFreeList_append (es1 es2 : List CoreExpr) :
    ccallFreeList (es1 ++ es2) = (ccallFreeList es1 && ccallFreeList es2) := by
  induction es1 with
  | nil => simp
  | cons e es ih => simp [ih, Bool.and_assoc]

@[simp] theorem ccallFree_ofValA (w : SpikeValA) : ccallFree (ofValA w) = true := by
  cases w <;> rfl
mutual
/-- E5: NEGATIVE-FREE terms — no `Paction Neg0` node anywhere. The static
    premise of `wps_bound`/`wpt_bound`: the `bound` frame PERFORMS the
    negative-action round itself (`Step.neg_bound`, core_reduction.lem:
    1290–1338), so the `bound` congruence rule is sound only for bodies that
    never reach one; the predicate is preserved by every stack-preserving
    non-jump round (`Step.negFree_preserved`, Soundness.lean). Descends
    exactly where `ccallFree` does. E5 slice 2: an `Eexcluded n act` node
    IS negative-free (slice 1 excluded it): the excluded action's rounds
    (`Step.excluded_store`/`_eval`) are ordinary rounds of the body — the
    body the negative-action round REWRITES TO (`negRewrite`) contains one,
    and `wps_bound` must apply to it for the protocol to compose. -/
def negFree : CoreExpr → Bool
  | Expr _ (Eaction (Paction polarity.Neg0 _)) => false
  | Expr _ (Ecase _ pats) => negFreeAlts pats
  | Expr _ (Elet _ _ e2) => negFree e2
  | Expr _ (End es) => negFreeList es
  | Expr _ (Esseq _ e1 e2) => negFree e1 && negFree e2
  | Expr _ (Ewseq _ e1 e2) => negFree e1 && negFree e2
  | Expr _ (Eif _ e2 e3) => negFree e2 && negFree e3
  | Expr _ (Eannot _ b) => negFree b
  | Expr _ (Ebound b) => negFree b
  | Expr _ (Esave _ _ body) => negFree body
  | Expr _ (Eunseq es) => negFreeList es
  | _ => true
def negFreeList : List CoreExpr → Bool
  | [] => true
  | e :: es => negFree e && negFreeList es
/-- E5: `negFree` over EVERY alternative of an `Ecase` — the twin of
    `ccallFreeAlts` (`has_ccall`'s `Ecase` arm, core_reduction.lem:466–469). -/
def negFreeAlts : List (pattern × CoreExpr) → Bool
  | [] => true
  | (_, e) :: rest => negFree e && negFreeAlts rest
end

@[simp] theorem negFreeAlts_nil : negFreeAlts [] = true := rfl
@[simp] theorem negFreeAlts_cons (q : pattern × CoreExpr) (rest : List (pattern × CoreExpr)) :
    negFreeAlts (q :: rest) = (negFree q.2 && negFreeAlts rest) := by
  obtain ⟨pat, e⟩ := q; rfl

theorem negFreeAlts_mem {pats : List (pattern × CoreExpr)} (h : negFreeAlts pats = true)
    {q : pattern × CoreExpr} (hq : q ∈ pats) : negFree q.2 = true := by
  induction pats with
  | nil => cases hq
  | cons r rest ih =>
    rw [negFreeAlts_cons, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h.1
    · exact ih h.2 hq

@[simp] theorem negFreeList_nil : negFreeList [] = true := rfl
@[simp] theorem negFreeList_cons (e : CoreExpr) (es : List CoreExpr) :
    negFreeList (e :: es) = (negFree e && negFreeList es) := rfl

theorem negFreeList_append (es1 es2 : List CoreExpr) :
    negFreeList (es1 ++ es2) = (negFreeList es1 && negFreeList es2) := by
  induction es1 with
  | nil => simp
  | cons e es ih => simp [ih, Bool.and_assoc]

@[simp] theorem negFree_ofValA (w : SpikeValA) : negFree (ofValA w) = true := by
  cases w <;> rfl


/-- E4: the completion of an `unseq` at all-value components — the engine's
    `one_step_unseq_aux` (core_reduction.lem:258–274) on the mirror's exact
    values: the values are collected in order (the accumulator is reversed
    at the end), the dynamic annotations of the annotated components are
    combined (`combine_dyn_annotations` = `++`, :246–247) after the race
    test `do_race` (:215–242) against the accumulator — a race is `none`
    (the engine's UNSEQUENCED-RACE, UB035). Bridge:
    `one_step_unseq_aux_collect` (Soundness.lean). -/
def collectUnseq : List dyn_annotation × List value → List SpikeValA →
    Option (List dyn_annotation × List value)
  | (fps, vs), [] => some (fps, vs.reverse)
  | (fps, vs), .pure _ _ v :: ws => collectUnseq (fps, v :: vs) ws
  | (fps, vs), .annot _ _ _ ds v :: ws =>
      if do_race ds fps then none
      else collectUnseq (combine_dyn_annotations ds fps, v :: vs) ws

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

/-- E5: THE SUPPLY DRAW of the negative-action round — the engine's
    `E.fresh_excluded_id >>= fun n -> … E.fresh_symbol >>= fun sym -> …`
    (core_reduction.lem:1298–1301; Core_reduction.lean:75–82
    `fresh_excluded_id`/`fresh_symbol0` over `Core_run.fresh_symbol'`,
    Core_run.lean:123–126): both supplies advance by one. The drawn id is
    `c.sup.excl`, the drawn symbol `fresh_given_int c.sup.sym`
    (Symbol.lean:334, `Symbol (digest ()) n SD_None`). Only the two
    supplies move; κ/proc/execLoc/curLoc are the general arm's. -/
def draw (c : Ctl) : Ctl := { c with sup := ⟨c.sup.sym + 1, c.sup.excl + 1⟩ }

@[simp] theorem draw_κ (c : Ctl) : c.draw.κ = c.κ := rfl
@[simp] theorem draw_proc (c : Ctl) : c.draw.proc = c.proc := rfl
@[simp] theorem draw_execLoc (c : Ctl) : c.draw.execLoc = c.execLoc := rfl
@[simp] theorem draw_curLoc (c : Ctl) : c.draw.curLoc = c.curLoc := rfl
@[simp] theorem draw_sup (c : Ctl) : c.draw.sup = ⟨c.sup.sym + 1, c.sup.excl + 1⟩ := rfl
@[simp] theorem draw_mk (κ : List (Option sym × context)) (p : Option sym) (ℓ : exec_location)
    (lc : CerbLocation.Loc) (sp : RunSup) :
    (Ctl.mk κ p ℓ lc sp).draw = Ctl.mk κ p ℓ lc ⟨sp.sym + 1, sp.excl + 1⟩ := rfl

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

/-- E5: the supply draw leaves the denoted stack alone. -/
@[simp] theorem toStack_draw (c : Ctl) : c.draw.toStack = c.toStack := rfl

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
  /-- The run state's IMMUTABLE part: `labeled` is read by the mirror
      (`labelsAt`); the two live supplies live in `Ctl.sup` (E1) and the
      driver ties fix only `labeled` to this field (`MachineCtx.Embeds`).
      E5 (slice 2): this field's `sym_supply` is READ by the judgments as
      THE SUPPLY FLOOR — the run's initial symbol supply, below which no
      symbol is ever drawn: `wps.pre`/`wpt.pre` carry `M.runState.sym_supply
      ≤ sp.sym` at every step, `Step.sup_sym_le` preserves it, and the
      negative-action rule (`wps_neg_bound`) delivers its fresh symbol's id
      at or above it. The production context (`prodCtx`, ProdEntry.lean)
      carries the genuine initial run state, whose `sym_supply` IS the
      entry supply `sup` (`initial_core_run_state sup`, `LemLib.supplySplit`);
      the seeded profiles (`spikeCtx`/`procCtx`/`procCtxF`) carry the floor
      `0`, their entry controls' supply (`default`). -/
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

mutual
/-- The jump-redex search along get_ctx's spine (header note 4; E4: through the
    `Cunseq` descent, `jumpRedexU?`). -/
def jumpRedex? : CoreExpr → Option (sym × List (generic_pexpr Unit sym))
  | Expr _ (Erun _ l pes) => some (l, pes)
  | Expr _ (Esseq _ e1 _) => jumpRedex? e1
  | Expr _ (Ewseq _ e1 _) => jumpRedex? e1
  | Expr _ (Eannot _ b) => if annotRooted b then none else jumpRedex? b
  | Expr _ (Ebound b) => jumpRedex? b
  | Expr _ (Eunseq es) => jumpRedexU? es
  | _ => none
/-- E4: the search at the FOCUSED component of an `unseq` — the LAST
    reducible one (get_ctx's `Cunseq` descent, core_reduction.lem:544–548,
    :590–601: the last reducible component's context heads the step list;
    the spine follows it). At all-value components: `none` (the
    completion redex). -/
def jumpRedexU? : List CoreExpr → Option (sym × List (generic_pexpr Unit sym))
  | [] => none
  | e :: es => if valsOnly es then jumpRedex? e else jumpRedexU? es
end

@[simp] theorem jumpRedex?_unseq (a : List annot) (es : List CoreExpr) :
    jumpRedex? (Expr a (Eunseq es)) = jumpRedexU? es := rfl

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

mutual
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
  | Expr a (Eunseq es) => redexAnnotsU a es
  | Expr a _ => a
/-- E4: the redex node's annotations under the `Cunseq` descent — the
    focused (last reducible) component's; the node's own at all values. -/
def redexAnnotsU (a : List annot) : List CoreExpr → List annot
  | [] => a
  | e :: es => if valsOnly es then (if isValE e then a else redexAnnots e) else redexAnnotsU a es
end

@[simp] theorem redexAnnots_unseq (a : List annot) (es : List CoreExpr) :
    redexAnnots (Expr a (Eunseq es)) = redexAnnotsU a es := rfl

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

mutual
/-- The call-redex search WITH its captured context (E4: through the `Cunseq`
    descent, `callRedexU?`). -/
def callRedex? : CoreExpr → Option (context × sym × List (generic_pexpr Unit sym))
  | Expr _ (Eproc _ (Sym f) pes) => some (CTX, f, pes)
  | Expr a (Esseq pat e1 e2) =>
      (callRedex? e1).map fun q => (Csseq a pat q.1 e2, q.2)
  | Expr a (Ewseq pat e1 e2) =>
      (callRedex? e1).map fun q => (Cwseq a pat q.1 e2, q.2)
  | Expr a (Eannot ds b) =>
      if annotRooted b then none else (callRedex? b).map fun q => (Cannot a ds q.1, q.2)
  | Expr a (Ebound b) => (callRedex? b).map fun q => (Cbound a q.1, q.2)
  | Expr a (Eunseq es) => callRedexU? a [] es
  | _ => none
/-- E4: the search under the `Cunseq` frame at the focused component,
    building the engine's frame `Cunseq annot es1 ctx es2` outside-in
    (`pre` accumulates the earlier components; apply_ctx's `Cunseq` arm,
    core_reduction.lem:616–617). -/
def callRedexU? (a : List annot) (pre : List CoreExpr) :
    List CoreExpr → Option (context × sym × List (generic_pexpr Unit sym))
  | [] => none
  | e :: es =>
      if valsOnly es then (callRedex? e).map fun q => (Cunseq a pre q.1 es, q.2)
      else callRedexU? a (pre ++ [e]) es
end

@[simp] theorem callRedex?_unseq (a : List annot) (es : List CoreExpr) :
    callRedex? (Expr a (Eunseq es)) = callRedexU? a [] es := rfl

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

@[simp] theorem callRedex?_excluded (a : List annot) (n : Nat)
    (act : generic_action core_run_annotation Unit sym) :
    callRedex? (Expr a (Eexcluded n act)) = none := rfl
@[simp] theorem jumpRedex?_excluded (a : List annot) (n : Nat)
    (act : generic_action core_run_annotation Unit sym) :
    jumpRedex? (Expr a (Eexcluded n act)) = none := rfl

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

/-! ### E4: the three spine searches at the `Cunseq` descent -/

theorem jumpRedexU?_focus {es1 : List CoreExpr} {e : CoreExpr} {es2 : List CoreExpr}
    (hnv : toVal e = none) (hv2 : valsOnly es2 = true) :
    jumpRedexU? (es1 ++ e :: es2) = jumpRedex? e := by
  induction es1 with
  | nil => simp only [List.nil_append, jumpRedexU?, hv2, ↓reduceIte]
  | cons x xs ih =>
    simp only [List.cons_append, jumpRedexU?, valsOnly_append_cons_false hnv, Bool.false_eq_true,
      ↓reduceIte]
    exact ih

/-- The jump search at an `unseq` with a focus IS the focused component's. -/
theorem jumpRedex?_unseq_focus (a : List annot) {es1 : List CoreExpr} {e : CoreExpr}
    {es2 : List CoreExpr} (hnv : toVal e = none) (hv2 : valsOnly es2 = true) :
    jumpRedex? (Expr a (Eunseq (es1 ++ e :: es2))) = jumpRedex? e := by
  rw [jumpRedex?_unseq, jumpRedexU?_focus hnv hv2]

theorem jumpRedexU?_vals (ws : List SpikeValA) : jumpRedexU? (ws.map ofValA) = none := by
  cases ws with
  | nil => rfl
  | cons w ws =>
    simp only [List.map_cons, jumpRedexU?, valsOnly_map_ofValA, ↓reduceIte]
    cases w <;> simp [jumpRedex?, annotRooted]

@[simp] theorem jumpRedex?_unseq_vals (a : List annot) (ws : List SpikeValA) :
    jumpRedex? (Expr a (Eunseq (ws.map ofValA))) = none := by
  rw [jumpRedex?_unseq, jumpRedexU?_vals]

theorem redexAnnotsU_focus (a : List annot) {es1 : List CoreExpr} {e : CoreExpr}
    {es2 : List CoreExpr} (hnv : toVal e = none) (hv2 : valsOnly es2 = true) :
    redexAnnotsU a (es1 ++ e :: es2) = redexAnnots e := by
  induction es1 with
  | nil =>
    simp only [List.nil_append, redexAnnotsU, hv2, ↓reduceIte, isValE_of_toVal_none hnv,
      Bool.false_eq_true]
  | cons x xs ih =>
    simp only [List.cons_append, redexAnnotsU, valsOnly_append_cons_false hnv, Bool.false_eq_true,
      ↓reduceIte]
    exact ih

@[simp] theorem redexAnnots_unseq_focus (a : List annot) {es1 : List CoreExpr} {e : CoreExpr}
    {es2 : List CoreExpr} (hnv : toVal e = none) (hv2 : valsOnly es2 = true) :
    redexAnnots (Expr a (Eunseq (es1 ++ e :: es2))) = redexAnnots e := by
  rw [redexAnnots_unseq, redexAnnotsU_focus a hnv hv2]

theorem redexAnnotsU_vals (a : List annot) (ws : List SpikeValA) :
    redexAnnotsU a (ws.map ofValA) = a := by
  cases ws with
  | nil => rfl
  | cons w ws => simp only [List.map_cons, redexAnnotsU, valsOnly_map_ofValA, isValE_ofValA, ↓reduceIte]

@[simp] theorem redexAnnots_unseq_vals (a : List annot) (ws : List SpikeValA) :
    redexAnnots (Expr a (Eunseq (ws.map ofValA))) = a := by
  rw [redexAnnots_unseq, redexAnnotsU_vals]

theorem callRedexU?_focus (a : List annot) {es1 : List CoreExpr} {e : CoreExpr}
    {es2 : List CoreExpr} (hnv : toVal e = none) (hv2 : valsOnly es2 = true) :
    ∀ pre : List CoreExpr, callRedexU? a pre (es1 ++ e :: es2) =
      (callRedex? e).map fun q => (Cunseq a (pre ++ es1) q.1 es2, q.2) := by
  induction es1 with
  | nil => intro pre; simp only [List.nil_append, callRedexU?, hv2, ↓reduceIte, List.append_nil]
  | cons x xs ih =>
    intro pre
    simp only [List.cons_append, callRedexU?, valsOnly_append_cons_false hnv, Bool.false_eq_true,
      ↓reduceIte]
    rw [ih (pre ++ [x]), List.append_assoc, List.singleton_append]

/-- The call search at an `unseq` with a focus: the focused component's,
    its captured context under the engine's `Cunseq annot es1 _ es2` frame. -/
theorem callRedex?_unseq_focus (a : List annot) {es1 : List CoreExpr} {e : CoreExpr}
    {es2 : List CoreExpr} (hnv : toVal e = none) (hv2 : valsOnly es2 = true) :
    callRedex? (Expr a (Eunseq (es1 ++ e :: es2))) =
      (callRedex? e).map fun q => (Cunseq a es1 q.1 es2, q.2) := by
  rw [callRedex?_unseq, callRedexU?_focus a hnv hv2 [], List.nil_append]

theorem callRedexU?_vals (a : List annot) (pre : List CoreExpr) (ws : List SpikeValA) :
    callRedexU? a pre (ws.map ofValA) = none := by
  cases ws with
  | nil => rfl
  | cons w ws =>
    simp only [List.map_cons, callRedexU?, valsOnly_map_ofValA, ↓reduceIte]
    cases w <;> simp [callRedex?, annotRooted]

@[simp] theorem callRedex?_unseq_vals (a : List annot) (ws : List SpikeValA) :
    callRedex? (Expr a (Eunseq (ws.map ofValA))) = none := by
  rw [callRedex?_unseq, callRedexU?_vals]

theorem callRedex?_unseq_none {a : List annot} {es1 : List CoreExpr} {e : CoreExpr}
    {es2 : List CoreExpr} (hnv : toVal e = none) (hv2 : valsOnly es2 = true)
    (h : callRedex? e = none) : callRedex? (Expr a (Eunseq (es1 ++ e :: es2))) = none := by
  rw [callRedex?_unseq_focus a hnv hv2, h]; rfl

theorem apply_ctx_unseq (a : List annot) (es1 : List CoreExpr) (ctx : context)
    (es2 : List CoreExpr) (e : CoreExpr) :
    apply_ctx (Cunseq a es1 ctx es2) e = Expr a (Eunseq (es1 ++ apply_ctx ctx e :: es2)) := rfl

/-! ### E5: the NEGATIVE-ACTION spine search

The engine's Neg arm (step_ctx's general arm, core_reduction.lem:1290–1338;
Core_reduction.lean:484 `Eaction (Paction p act) => … | Neg => match
break_at_bound_and_sseq ctx with …`) fires at the redex `neg(act)` and
REWRITES THE ARENA at the OUTERMOST `bound` of the redex's context (the
first `Cbound` from the root, `break_at_bound_and_sseq`, :868–912). The
mirror states the rewrite at that `bound` node (`Step.neg_bound`): the
search `negRedex?` — `callRedex?`'s twin — locates the negative action under
the frames `Csseq`/`Cwseq`/`Cannot`/`Cbound`/`Cunseq`(focused) and returns
the engine's context from the searched node down to the redex, the redex
node's annotation list (the location the general arm writes) and the action.
The `bound` frame rule (`Step.bound_ctx`) is GUARDED by `negRedex? b = none`
so that an inner `bound` never frames a rewrite the engine performs at an
outer one; the other frames commute with the rewrite (`break_at_bound_and_sseq`
wraps them, :874–905). -/

/-- The engine's action type at the run annotation. -/
abbrev CoreAction : Type := generic_action core_run_annotation Unit sym

mutual
def negRedex? : CoreExpr → Option (context × List annot × CoreAction)
  | Expr a (Eaction (Paction polarity.Neg0 act)) => some (CTX, a, act)
  | Expr a (Esseq pat e1 e2) =>
      (negRedex? e1).map fun q => (Csseq a pat q.1 e2, q.2)
  | Expr a (Ewseq pat e1 e2) =>
      (negRedex? e1).map fun q => (Cwseq a pat q.1 e2, q.2)
  | Expr a (Eannot ds b) =>
      if annotRooted b then none else (negRedex? b).map fun q => (Cannot a ds q.1, q.2)
  | Expr a (Ebound b) => (negRedex? b).map fun q => (Cbound a q.1, q.2)
  | Expr a (Eunseq es) => negRedexU? a [] es
  | _ => none
def negRedexU? (a : List annot) (pre : List CoreExpr) :
    List CoreExpr → Option (context × List annot × CoreAction)
  | [] => none
  | e :: es =>
      if valsOnly es then (negRedex? e).map fun q => (Cunseq a pre q.1 es, q.2)
      else negRedexU? a (pre ++ [e]) es
end

@[simp] theorem negRedex?_neg (a : List annot) (act : CoreAction) :
    negRedex? (Expr a (Eaction (Paction polarity.Neg0 act))) = some (CTX, a, act) := rfl
@[simp] theorem negRedex?_pos (a : List annot) (act : CoreAction) :
    negRedex? (Expr a (Eaction (Paction polarity.Pos act))) = none := rfl
@[simp] theorem negRedex?_unseq (a : List annot) (es : List CoreExpr) :
    negRedex? (Expr a (Eunseq es)) = negRedexU? a [] es := rfl
@[simp] theorem negRedex?_bound (a : List annot) (b : CoreExpr) :
    negRedex? (Expr a (Ebound b)) = (negRedex? b).map fun q => (Cbound a q.1, q.2) := rfl
@[simp] theorem negRedex?_sseq (a : List annot) (pat : pattern) (e1 e2 : CoreExpr) :
    negRedex? (Expr a (Esseq pat e1 e2)) =
      (negRedex? e1).map fun q => (Csseq a pat q.1 e2, q.2) := rfl
@[simp] theorem negRedex?_wseq (a : List annot) (pat : pattern) (e1 e2 : CoreExpr) :
    negRedex? (Expr a (Ewseq pat e1 e2)) =
      (negRedex? e1).map fun q => (Cwseq a pat q.1 e2, q.2) := rfl
theorem negRedex?_annot (a : List annot) (ds : List dyn_annotation) (b : CoreExpr) :
    negRedex? (Expr a (Eannot ds b)) =
      if annotRooted b then none
      else (negRedex? b).map fun q => (Cannot a ds q.1, q.2) := rfl
@[simp] theorem negRedex?_annot_of_root {b : CoreExpr}
    (a : List annot) (ds : List dyn_annotation) (h : annotRooted b = true) :
    negRedex? (Expr a (Eannot ds b)) = none := by
  rw [negRedex?_annot, h]; rfl
@[simp] theorem negRedex?_annot_of_not_root {b : CoreExpr}
    (a : List annot) (ds : List dyn_annotation) (h : annotRooted b = false) :
    negRedex? (Expr a (Eannot ds b)) =
      (negRedex? b).map fun q => (Cannot a ds q.1, q.2) := by
  rw [negRedex?_annot, h]; rfl
@[simp] theorem negRedex?_pure (a : List annot) (pe : generic_pexpr Unit sym) :
    negRedex? (Expr a (Epure pe)) = none := rfl
@[simp] theorem negRedex?_proc (a : List annot) (ra : core_run_annotation)
    (nm : generic_name sym) (pes : List (generic_pexpr Unit sym)) :
    negRedex? (Expr a (Eproc ra nm pes)) = none := rfl
@[simp] theorem negRedex?_memop (a : List annot) (mop : memop)
    (pes : List (generic_pexpr Unit sym)) :
    negRedex? (Expr a (Ememop mop pes)) = none := rfl
@[simp] theorem negRedex?_run (a : List annot) (ra : core_run_annotation)
    (l : sym) (pes : List (generic_pexpr Unit sym)) :
    negRedex? (Expr a (Erun ra l pes)) = none := rfl
@[simp] theorem negRedex?_save (a : List annot) (sb : sym × core_base_type)
    (ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)))
    (body : CoreExpr) :
    negRedex? (Expr a (Esave sb ps body)) = none := rfl
@[simp] theorem negRedex?_if (a : List annot) (g : generic_pexpr Unit sym)
    (e2 e3 : CoreExpr) :
    negRedex? (Expr a (Eif g e2 e3)) = none := rfl
@[simp] theorem negRedex?_case (a : List annot) (pe : generic_pexpr Unit sym)
    (pats : List (pattern × CoreExpr)) :
    negRedex? (Expr a (Ecase pe pats)) = none := rfl
@[simp] theorem negRedex?_let (a : List annot) (pat : pattern) (pe : generic_pexpr Unit sym)
    (e2 : CoreExpr) :
    negRedex? (Expr a (Elet pat pe e2)) = none := rfl
@[simp] theorem negRedex?_nd (a : List annot) (es : List CoreExpr) :
    negRedex? (Expr a (End es)) = none := rfl
@[simp] theorem negRedex?_excluded (a : List annot) (n : Nat) (act : CoreAction) :
    negRedex? (Expr a (Eexcluded n act)) = none := rfl
@[simp] theorem negRedex?_ofValA (w : SpikeValA) : negRedex? (ofValA w) = none := by
  cases w <;> simp [negRedex?, annotRooted]
@[simp] theorem negRedex?_ofVal (w : SpikeVal) : negRedex? (ofVal w) = none := by
  cases w <;> rfl

theorem negRedex?_body_none_of_bound {a : List annot} {b : CoreExpr}
    (h : negRedex? (Expr a (Ebound b)) = none) : negRedex? b = none := by
  rw [negRedex?_bound] at h
  exact Option.map_eq_none_iff.mp h
theorem negRedex?_bound_none {a : List annot} {b : CoreExpr}
    (h : negRedex? b = none) : negRedex? (Expr a (Ebound b)) = none := by
  rw [negRedex?_bound, h]; rfl
theorem negRedex?_e1_none_of_sseq {a : List annot} {pat : pattern} {e1 e2 : CoreExpr}
    (h : negRedex? (Expr a (Esseq pat e1 e2)) = none) : negRedex? e1 = none := by
  rw [negRedex?_sseq] at h
  exact Option.map_eq_none_iff.mp h
theorem negRedex?_e1_none_of_wseq {a : List annot} {pat : pattern} {e1 e2 : CoreExpr}
    (h : negRedex? (Expr a (Ewseq pat e1 e2)) = none) : negRedex? e1 = none := by
  rw [negRedex?_wseq] at h
  exact Option.map_eq_none_iff.mp h
theorem negRedex?_sseq_none {a : List annot} {pat : pattern} {e1 e2 : CoreExpr}
    (h : negRedex? e1 = none) : negRedex? (Expr a (Esseq pat e1 e2)) = none := by
  rw [negRedex?_sseq, h]; rfl
theorem negRedex?_wseq_none {a : List annot} {pat : pattern} {e1 e2 : CoreExpr}
    (h : negRedex? e1 = none) : negRedex? (Expr a (Ewseq pat e1 e2)) = none := by
  rw [negRedex?_wseq, h]; rfl
theorem negRedex?_annot_none {a : List annot} {ds : List dyn_annotation} {b : CoreExpr}
    (h : negRedex? b = none) : negRedex? (Expr a (Eannot ds b)) = none := by
  rw [negRedex?_annot]
  split
  · rfl
  · rw [h]; rfl

theorem negRedexU?_focus (a : List annot) {es1 : List CoreExpr} {e : CoreExpr}
    {es2 : List CoreExpr} (hnv : toVal e = none) (hv2 : valsOnly es2 = true) :
    ∀ pre : List CoreExpr, negRedexU? a pre (es1 ++ e :: es2) =
      (negRedex? e).map fun q => (Cunseq a (pre ++ es1) q.1 es2, q.2) := by
  induction es1 with
  | nil => intro pre; simp only [List.nil_append, negRedexU?, hv2, ↓reduceIte, List.append_nil]
  | cons x xs ih =>
    intro pre
    simp only [List.cons_append, negRedexU?, valsOnly_append_cons_false hnv, Bool.false_eq_true,
      ↓reduceIte]
    rw [ih (pre ++ [x]), List.append_assoc, List.singleton_append]

/-- The negative-action search at an `unseq` with a focus: the focused
    component's, under the engine's `Cunseq annot es1 _ es2` frame. -/
theorem negRedex?_unseq_focus (a : List annot) {es1 : List CoreExpr} {e : CoreExpr}
    {es2 : List CoreExpr} (hnv : toVal e = none) (hv2 : valsOnly es2 = true) :
    negRedex? (Expr a (Eunseq (es1 ++ e :: es2))) =
      (negRedex? e).map fun q => (Cunseq a es1 q.1 es2, q.2) := by
  rw [negRedex?_unseq, negRedexU?_focus a hnv hv2 [], List.nil_append]

theorem negRedexU?_vals (a : List annot) (pre : List CoreExpr) (ws : List SpikeValA) :
    negRedexU? a pre (ws.map ofValA) = none := by
  cases ws with
  | nil => rfl
  | cons w ws =>
    simp only [List.map_cons, negRedexU?, valsOnly_map_ofValA, ↓reduceIte]
    cases w <;> simp [negRedex?, annotRooted]

@[simp] theorem negRedex?_unseq_vals (a : List annot) (ws : List SpikeValA) :
    negRedex? (Expr a (Eunseq (ws.map ofValA))) = none := by
  rw [negRedex?_unseq, negRedexU?_vals]

theorem negRedex?_unseq_none {a : List annot} {es1 : List CoreExpr} {e : CoreExpr}
    {es2 : List CoreExpr} (hnv : toVal e = none) (hv2 : valsOnly es2 = true)
    (h : negRedex? e = none) : negRedex? (Expr a (Eunseq (es1 ++ e :: es2))) = none := by
  rw [negRedex?_unseq_focus a hnv hv2, h]; rfl

mutual
/-- E5: a negative-free term has no negative redex (its `bound` frame is the
    congruence `Step.bound_ctx`, never `Step.neg_bound`). -/
theorem negRedex?_none_of_negFree : ∀ {e : CoreExpr}, negFree e = true → negRedex? e = none
  | Expr a (Esseq pat e1 e2), h => by
      simp only [negFree, Bool.and_eq_true] at h
      exact negRedex?_sseq_none (negRedex?_none_of_negFree h.1)
  | Expr a (Ewseq pat e1 e2), h => by
      simp only [negFree, Bool.and_eq_true] at h
      exact negRedex?_wseq_none (negRedex?_none_of_negFree h.1)
  | Expr a (Eannot ds b), h =>
      negRedex?_annot_none (negRedex?_none_of_negFree (by simpa only [negFree] using h))
  | Expr a (Ebound b), h =>
      negRedex?_bound_none (negRedex?_none_of_negFree (by simpa only [negFree] using h))
  | Expr a (Eunseq es), h => by
      rw [negRedex?_unseq]
      exact negRedexU?_none_of_negFreeList (by simpa only [negFree] using h)
  | Expr a (Eaction (Paction polarity.Neg0 _)), h => by simp [negFree] at h
  | Expr a (Eaction (Paction polarity.Pos _)), h => rfl
  | Expr a (Erun _ _ _), h => rfl
  | Expr a (Epure _), h => rfl
  | Expr a (Ememop _ _), h => rfl
  | Expr a (Ecase _ _), h => rfl
  | Expr a (Elet _ _ _), h => rfl
  | Expr a (Eif _ _ _), h => rfl
  | Expr a (Eccall _ _ _ _), h => rfl
  | Expr a (Eproc _ _ _), h => rfl
  | Expr a (End _), h => rfl
  | Expr a (Esave _ _ _), h => rfl
  | Expr a (Epar _), h => rfl
  | Expr a (Ewait _), h => rfl
  | Expr a (Eexcluded _ _), h => rfl
theorem negRedexU?_none_of_negFreeList :
    ∀ {a : List annot} {pre es : List CoreExpr},
      negFreeList es = true → negRedexU? a pre es = none
  | a, pre, [], h => rfl
  | a, pre, e :: es, h => by
      simp only [negFreeList_cons, Bool.and_eq_true] at h
      simp only [negRedexU?]
      split
      · rw [negRedex?_none_of_negFree h.1]; rfl
      · exact negRedexU?_none_of_negFreeList h.2
end

theorem toVal_none_of_negRedex?_some {e : CoreExpr} {q : context × List annot × CoreAction}
    (h : negRedex? e = some q) : toVal e = none := by
  cases hv : toVal e with
  | none => rfl
  | some w =>
    obtain ⟨wa, -, rfl⟩ := ofValA_of_toVal hv
    cases wa <;> simp [negRedex?, annotRooted] at h

/-- E5: THE NEGATIVE-ACTION REWRITE — the engine's `expr'` in the
    `BOUND_NO_SSEQ ctx_bound ctxA` arm (core_reduction.lem:1298–1309;
    Core_reduction.lean:484), VERBATIM through the engine's own
    constructors (Core_aux.lean): at the drawn exclusion id `n` and the
    drawn symbol `s`,
    `let weak (_: unit, s: unit) = unseq(Eexcluded n act, ctxA'[pure(Unit)])
    in pure(s)` with `ctxA' = add_exclusion n ctxA` (:939–958 — every
    `DA_*` list of a `Cannot` frame in `ctxA` gains `n`). The excluded
    action then performs under `process_action (Just n)` (:1345–1346),
    delivering `{DA_neg n [] fp} Unit` (`Step.excluded_store`). -/
def negRewrite (n : Nat) (s : sym) (ctxA : context) (act : CoreAction) : CoreExpr :=
  mk_wseq_e (mk_tuple_pat [mk_empty_pat BTy_unit, mk_sym_pat s BTy_unit])
    (mk_unseq_e [Expr [] (Eexcluded n act),
      apply_ctx (add_exclusion n ctxA) (mk_pure_e mk_unit_pe)])
    (mk_pure_e (mk_sym_pe s))

/-- E5 (slice 2): the engine's per-annotation exclusion write of
    `add_exclusion` (core_reduction.lem:939–958; Core_reduction.lean:472 —
    the `Cannot` arm's `List.map`): the drawn exclusion id `n` is pushed onto
    the exclusion list of every dynamic annotation of the frame. -/
def addExcl (n : Nat) : dyn_annotation → dyn_annotation
  | DA_neg id excl fp => DA_neg id (n :: excl) fp
  | DA_pos excl fp => DA_pos (n :: excl) fp

@[simp] theorem add_exclusion_CTX (n : Nat) : add_exclusion n CTX = CTX := rfl
@[simp] theorem add_exclusion_wseq (n : Nat) (a : List annot) (pat : pattern) (ctx : context)
    (e2 : CoreExpr) :
    add_exclusion n (Cwseq a pat ctx e2) = Cwseq a pat (add_exclusion n ctx) e2 := rfl
@[simp] theorem add_exclusion_sseq (n : Nat) (a : List annot) (pat : pattern) (ctx : context)
    (e2 : CoreExpr) :
    add_exclusion n (Csseq a pat ctx e2) = Csseq a pat (add_exclusion n ctx) e2 := rfl
@[simp] theorem add_exclusion_annot (n : Nat) (a : List annot) (ds : List dyn_annotation)
    (ctx : context) :
    add_exclusion n (Cannot a ds ctx) = Cannot a (ds.map (addExcl n)) (add_exclusion n ctx) := by
  show Cannot a (List.map _ ds) _ = _
  congr 1

/-- E5 (slice 2): `do_race` against NO annotations is `false` (`do_race`,
    Core_reduction.lean:300: `List.any xs1 (fun … => List.any xs2 …)` at
    `xs2 = []`). -/
theorem do_race_nil_right (ds : List dyn_annotation) : do_race ds [] = false := by
  induction ds with
  | nil => rfl
  | cons d rest ih =>
    cases d <;> simp only [do_race, List.any_cons, List.any_nil, Bool.false_or] at ih ⊢ <;> exact ih

/-- E5 (slice 2): THE EXCLUSION PROTOCOL'S RACE VERDICT — annotations that
    all carry the exclusion id `n` never race with the excluded action's own
    `DA_neg n [] fp` (`do_race`'s `Lem_List.elem id1 exclusion2` tests,
    Core_reduction.lean:300): the footprints are never compared. -/
theorem lem_nat_beq_self (n : Nat) : (n == n) = true := by
  simp only [BEq.beq, Lem_Basic_classes.isEqual, Lem_Basic_classes.setElemCompare,
    defaultCompare, Nat.compare_eq_eq.mpr rfl]
theorem lem_elem_self (n : Nat) (l : List Nat) : Lem_List.elem n (n :: l) = true := by
  simp only [Lem_List.elem, listMemberBy, lem_nat_beq_self, Bool.true_or]
theorem do_race_addExcl_neg (n : Nat) (ds : List dyn_annotation) (fp : CerbMem.Footprint) :
    do_race (ds.map (addExcl n)) [DA_neg n [] fp] = false := by
  induction ds with
  | nil => rfl
  | cons d rest ih =>
    cases d <;>
      simp only [List.map_cons, addExcl, do_race, List.any_cons, List.any_nil, Bool.or_false,
        lem_elem_self, if_true, Bool.false_or] at ih ⊢ <;> exact ih

/-- The rewrite, spelled out: `mk_tuple_pat` at two components IS the
    `Ctuple` pattern (Core_aux.lean:121), `mk_wseq_e`/`mk_unseq_e`/`mk_pure_e`
    build `Expr []` nodes (:641–665). -/
theorem negRewrite_eq (n : Nat) (s : sym) (ctxA : context) (act : CoreAction) :
    negRewrite n s ctxA act =
      Expr [] (Ewseq (Pattern [] (CaseCtor Ctuple
          [Pattern [] (CaseBase (none, BTy_unit)), Pattern [] (CaseBase (some s, BTy_unit))]))
        (Expr [] (Eunseq [Expr [] (Eexcluded n act),
          apply_ctx (add_exclusion n ctxA) (Expr [] (Epure (Pexpr [] () (PEval Vunit))))]))
        (Expr [] (Epure (Pexpr [] () (PEsym s))))) := rfl

mutual
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
  | Expr a (Eunseq es), lp, h => by
      rw [jumpRedex?_unseq] at h
      rw [callRedex?_unseq]
      exact callRedexU?_none_of_jumpRedexU?_some h
  | Expr a (Ebound b), lp, h => by
      rw [jumpRedex?_bound] at h
      rw [callRedex?_bound, callRedex?_none_of_jumpRedex?_some h]; rfl
  | Expr a (End _), lp, h => by simp [jumpRedex?] at h
  | Expr a (Esave _ _ _), lp, h => by simp [jumpRedex?] at h
  | Expr a (Epar _), lp, h => by simp [jumpRedex?] at h
  | Expr a (Ewait _), lp, h => by simp [jumpRedex?] at h
  | Expr a (Eexcluded _ _), lp, h => by simp [jumpRedex?] at h
/-- The list twin at the `Cunseq` descent (E4). -/
theorem callRedexU?_none_of_jumpRedexU?_some :
    ∀ {a : List annot} {pre : List CoreExpr} {es : List CoreExpr}
      {lp : sym × List (generic_pexpr Unit sym)},
      jumpRedexU? es = some lp → callRedexU? a pre es = none
  | a, pre, [], lp, h => by cases h
  | a, pre, e :: es, lp, h => by
      simp only [jumpRedexU?] at h
      simp only [callRedexU?]
      split at h
      · rename_i hv
        rw [if_pos hv, callRedex?_none_of_jumpRedex?_some h]; rfl
      · rename_i hv
        rw [if_neg hv]
        exact callRedexU?_none_of_jumpRedexU?_some h
end

theorem jumpRedex?_none_of_callRedex?_some {e : CoreExpr}
    {q : context × sym × List (generic_pexpr Unit sym)}
    (h : callRedex? e = some q) : jumpRedex? e = none := by
  cases hj : jumpRedex? e with
  | none => rfl
  | some lp => rw [callRedex?_none_of_jumpRedex?_some hj] at h; cases h

mutual
/-- E5: the negative-action search is exclusive with the other two: the
    hole is unique (a term's redex is a call, a jump, a negative action, or
    none of them). -/
theorem callRedex?_none_of_negRedex?_some :
    ∀ {e : CoreExpr} {q : context × List annot × CoreAction},
      negRedex? e = some q → callRedex? e = none
  | Expr a (Esseq pat e1 e2), q, h => by
      rw [negRedex?_sseq, Option.map_eq_some_iff] at h
      obtain ⟨q1, h1, -⟩ := h
      rw [callRedex?_sseq, callRedex?_none_of_negRedex?_some h1]; rfl
  | Expr a (Ewseq pat e1 e2), q, h => by
      rw [negRedex?_wseq, Option.map_eq_some_iff] at h
      obtain ⟨q1, h1, -⟩ := h
      rw [callRedex?_wseq, callRedex?_none_of_negRedex?_some h1]; rfl
  | Expr a (Eannot ds b), q, h => by
      rw [negRedex?_annot] at h
      rw [callRedex?_annot]
      split at h
      · cases h
      · rename_i hr
        rw [Option.map_eq_some_iff] at h
        obtain ⟨q1, h1, -⟩ := h
        rw [if_neg hr, callRedex?_none_of_negRedex?_some h1]; rfl
  | Expr a (Ebound b), q, h => by
      rw [negRedex?_bound, Option.map_eq_some_iff] at h
      obtain ⟨q1, h1, -⟩ := h
      rw [callRedex?_bound, callRedex?_none_of_negRedex?_some h1]; rfl
  | Expr a (Eunseq es), q, h => by
      rw [negRedex?_unseq] at h
      rw [callRedex?_unseq]
      exact callRedexU?_none_of_negRedexU?_some h
  | Expr a (Eaction _), q, h => rfl
  | Expr a (Erun ra l pes), q, h => by simp [negRedex?] at h
  | Expr a (Epure _), q, h => by simp [negRedex?] at h
  | Expr a (Ememop _ _), q, h => by simp [negRedex?] at h
  | Expr a (Ecase _ _), q, h => by simp [negRedex?] at h
  | Expr a (Elet _ _ _), q, h => by simp [negRedex?] at h
  | Expr a (Eif _ _ _), q, h => by simp [negRedex?] at h
  | Expr a (Eccall _ _ _ _), q, h => by simp [negRedex?] at h
  | Expr a (Eproc _ _ _), q, h => by simp [negRedex?] at h
  | Expr a (End _), q, h => by simp [negRedex?] at h
  | Expr a (Esave _ _ _), q, h => by simp [negRedex?] at h
  | Expr a (Epar _), q, h => by simp [negRedex?] at h
  | Expr a (Ewait _), q, h => by simp [negRedex?] at h
  | Expr a (Eexcluded _ _), q, h => by simp [negRedex?] at h
theorem callRedexU?_none_of_negRedexU?_some :
    ∀ {a : List annot} {pre : List CoreExpr} {es : List CoreExpr}
      {q : context × List annot × CoreAction},
      negRedexU? a pre es = some q → callRedexU? a pre es = none
  | a, pre, [], q, h => by cases h
  | a, pre, e :: es, q, h => by
      simp only [negRedexU?] at h
      simp only [callRedexU?]
      split at h
      · rename_i hv
        rw [Option.map_eq_some_iff] at h
        obtain ⟨q1, h1, -⟩ := h
        rw [if_pos hv, callRedex?_none_of_negRedex?_some h1]; rfl
      · rename_i hv
        rw [if_neg hv]
        exact callRedexU?_none_of_negRedexU?_some h
end

mutual
theorem jumpRedex?_none_of_negRedex?_some :
    ∀ {e : CoreExpr} {q : context × List annot × CoreAction},
      negRedex? e = some q → jumpRedex? e = none
  | Expr a (Esseq pat e1 e2), q, h => by
      rw [negRedex?_sseq, Option.map_eq_some_iff] at h
      obtain ⟨q1, h1, -⟩ := h
      rw [jumpRedex?_sseq]; exact jumpRedex?_none_of_negRedex?_some h1
  | Expr a (Ewseq pat e1 e2), q, h => by
      rw [negRedex?_wseq, Option.map_eq_some_iff] at h
      obtain ⟨q1, h1, -⟩ := h
      rw [jumpRedex?_wseq]; exact jumpRedex?_none_of_negRedex?_some h1
  | Expr a (Eannot ds b), q, h => by
      rw [negRedex?_annot] at h
      rw [jumpRedex?_annot]
      split at h
      · cases h
      · rename_i hr
        rw [Option.map_eq_some_iff] at h
        obtain ⟨q1, h1, -⟩ := h
        rw [if_neg hr]; exact jumpRedex?_none_of_negRedex?_some h1
  | Expr a (Ebound b), q, h => by
      rw [negRedex?_bound, Option.map_eq_some_iff] at h
      obtain ⟨q1, h1, -⟩ := h
      rw [jumpRedex?_bound]; exact jumpRedex?_none_of_negRedex?_some h1
  | Expr a (Eunseq es), q, h => by
      rw [negRedex?_unseq] at h
      rw [jumpRedex?_unseq]
      exact jumpRedexU?_none_of_negRedexU?_some h
  | Expr a (Eaction _), q, h => rfl
  | Expr a (Erun ra l pes), q, h => by simp [negRedex?] at h
  | Expr a (Epure _), q, h => by simp [negRedex?] at h
  | Expr a (Ememop _ _), q, h => by simp [negRedex?] at h
  | Expr a (Ecase _ _), q, h => by simp [negRedex?] at h
  | Expr a (Elet _ _ _), q, h => by simp [negRedex?] at h
  | Expr a (Eif _ _ _), q, h => by simp [negRedex?] at h
  | Expr a (Eccall _ _ _ _), q, h => by simp [negRedex?] at h
  | Expr a (Eproc _ _ _), q, h => by simp [negRedex?] at h
  | Expr a (End _), q, h => by simp [negRedex?] at h
  | Expr a (Esave _ _ _), q, h => by simp [negRedex?] at h
  | Expr a (Epar _), q, h => by simp [negRedex?] at h
  | Expr a (Ewait _), q, h => by simp [negRedex?] at h
  | Expr a (Eexcluded _ _), q, h => by simp [negRedex?] at h
theorem jumpRedexU?_none_of_negRedexU?_some :
    ∀ {a : List annot} {pre : List CoreExpr} {es : List CoreExpr}
      {q : context × List annot × CoreAction},
      negRedexU? a pre es = some q → jumpRedexU? es = none
  | a, pre, [], q, h => by cases h
  | a, pre, e :: es, q, h => by
      simp only [negRedexU?] at h
      simp only [jumpRedexU?]
      split at h
      · rename_i hv
        rw [Option.map_eq_some_iff] at h
        obtain ⟨q1, h1, -⟩ := h
        rw [if_pos hv]; exact jumpRedex?_none_of_negRedex?_some h1
      · rename_i hv
        rw [if_neg hv]
        exact jumpRedexU?_none_of_negRedexU?_some h
end

theorem negRedex?_none_of_callRedex?_some {e : CoreExpr}
    {q : context × sym × List (generic_pexpr Unit sym)}
    (h : callRedex? e = some q) : negRedex? e = none := by
  cases hn : negRedex? e with
  | none => rfl
  | some q' => rw [callRedex?_none_of_negRedex?_some hn] at h; cases h

theorem negRedex?_none_of_jumpRedex?_some {e : CoreExpr}
    {lp : sym × List (generic_pexpr Unit sym)}
    (h : jumpRedex? e = some lp) : negRedex? e = none := by
  cases hn : negRedex? e with
  | none => rfl
  | some q' => rw [jumpRedex?_none_of_negRedex?_some hn] at h; cases h

mutual
/-- E5: the negative-action search RETURNS THE DECOMPOSITION: a term with a
    positive answer is the returned context plugged with the negative action
    (`apply_ctx`, Core_reduction.lean:388). -/
theorem negRedex?_apply_ctx_eq :
    ∀ {e : CoreExpr} {ctxA : context} {a : List annot} {act : CoreAction},
      negRedex? e = some (ctxA, a, act) →
      e = apply_ctx ctxA (Expr a (Eaction (Paction polarity.Neg0 act)))
  | Expr a0 (Eaction (Paction polarity.Neg0 act0)), ctxA, a, act, h => by
      rw [negRedex?_neg] at h
      obtain ⟨rfl, rfl, rfl⟩ : CTX = ctxA ∧ a0 = a ∧ act0 = act := by
        have := Option.some.inj h
        exact ⟨congrArg Prod.fst this, congrArg (fun q => q.2.1) this,
          congrArg (fun q => q.2.2) this⟩
      rfl
  | Expr a0 (Eaction (Paction polarity.Pos act0)), ctxA, a, act, h => by
      rw [negRedex?_pos] at h; cases h
  | Expr a0 (Esseq pat e1 e2), ctxA, a, act, h => by
      rw [negRedex?_sseq, Option.map_eq_some_iff] at h
      obtain ⟨⟨c1, a1, act1⟩, h1, hq⟩ := h
      obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
        exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq, congrArg (fun q => q.2.2) hq⟩
      show _ = Expr a0 (Esseq pat (apply_ctx c1 _) e2)
      rw [← negRedex?_apply_ctx_eq h1]
  | Expr a0 (Ewseq pat e1 e2), ctxA, a, act, h => by
      rw [negRedex?_wseq, Option.map_eq_some_iff] at h
      obtain ⟨⟨c1, a1, act1⟩, h1, hq⟩ := h
      obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
        exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq, congrArg (fun q => q.2.2) hq⟩
      show _ = Expr a0 (Ewseq pat (apply_ctx c1 _) e2)
      rw [← negRedex?_apply_ctx_eq h1]
  | Expr a0 (Eannot ds b), ctxA, a, act, h => by
      rw [negRedex?_annot] at h
      split at h
      · cases h
      · rw [Option.map_eq_some_iff] at h
        obtain ⟨⟨c1, a1, act1⟩, h1, hq⟩ := h
        obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
          exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq, congrArg (fun q => q.2.2) hq⟩
        show _ = Expr a0 (Eannot ds (apply_ctx c1 _))
        rw [← negRedex?_apply_ctx_eq h1]
  | Expr a0 (Ebound b), ctxA, a, act, h => by
      rw [negRedex?_bound, Option.map_eq_some_iff] at h
      obtain ⟨⟨c1, a1, act1⟩, h1, hq⟩ := h
      obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
        exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq, congrArg (fun q => q.2.2) hq⟩
      show _ = Expr a0 (Ebound (apply_ctx c1 _))
      rw [← negRedex?_apply_ctx_eq h1]
  | Expr a0 (Eunseq es), ctxA, a, act, h => by
      rw [negRedex?_unseq] at h
      obtain ⟨es1, c1, es2, rfl, hes⟩ := negRedexU?_apply_ctx_eq h
      rw [List.nil_append]
      exact congrArg (fun l => Expr a0 (Eunseq l)) hes
  | Expr a0 (Erun ra l pes), ctxA, a, act, h => by simp [negRedex?] at h
  | Expr a0 (Epure _), ctxA, a, act, h => by simp [negRedex?] at h
  | Expr a0 (Ememop _ _), ctxA, a, act, h => by simp [negRedex?] at h
  | Expr a0 (Ecase _ _), ctxA, a, act, h => by simp [negRedex?] at h
  | Expr a0 (Elet _ _ _), ctxA, a, act, h => by simp [negRedex?] at h
  | Expr a0 (Eif _ _ _), ctxA, a, act, h => by simp [negRedex?] at h
  | Expr a0 (Eccall _ _ _ _), ctxA, a, act, h => by simp [negRedex?] at h
  | Expr a0 (Eproc _ _ _), ctxA, a, act, h => by simp [negRedex?] at h
  | Expr a0 (End _), ctxA, a, act, h => by simp [negRedex?] at h
  | Expr a0 (Esave _ _ _), ctxA, a, act, h => by simp [negRedex?] at h
  | Expr a0 (Epar _), ctxA, a, act, h => by simp [negRedex?] at h
  | Expr a0 (Ewait _), ctxA, a, act, h => by simp [negRedex?] at h
  | Expr a0 (Eexcluded _ _), ctxA, a, act, h => by simp [negRedex?] at h
/-- The list twin: the answer's context is `Cunseq a0 (pre ++ es1) c es2` and
    the searched list is `es1 ++ apply_ctx c (neg) :: es2`. -/
theorem negRedexU?_apply_ctx_eq :
    ∀ {a0 : List annot} {pre es : List CoreExpr} {ctxA : context} {a : List annot}
      {act : CoreAction},
      negRedexU? a0 pre es = some (ctxA, a, act) →
      ∃ (es1 : List CoreExpr) (c : context) (es2 : List CoreExpr),
        ctxA = Cunseq a0 (pre ++ es1) c es2 ∧
        es = es1 ++ apply_ctx c (Expr a (Eaction (Paction polarity.Neg0 act))) :: es2
  | a0, pre, [], ctxA, a, act, h => by cases h
  | a0, pre, e :: es, ctxA, a, act, h => by
      simp only [negRedexU?] at h
      split at h
      · rename_i hv
        rw [Option.map_eq_some_iff] at h
        obtain ⟨⟨c1, a1, act1⟩, h1, hq⟩ := h
        obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
          exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq, congrArg (fun q => q.2.2) hq⟩
        refine ⟨[], c1, es, by rw [List.append_nil], ?_⟩
        rw [List.nil_append, ← negRedex?_apply_ctx_eq h1]
      · rename_i hv
        obtain ⟨es1, c1, es2, rfl, hes⟩ := negRedexU?_apply_ctx_eq h
        refine ⟨e :: es1, c1, es2, by rw [List.append_assoc, List.singleton_append], ?_⟩
        rw [hes]; rfl
end

mutual
/-- E5: the call search RETURNS THE DECOMPOSITION (`negRedex?_apply_ctx_eq`'s
    twin): a term with a positive answer is the returned context plugged
    with the `Eproc` node (its two annotations existential). -/
theorem callRedex?_apply_ctx_eq :
    ∀ {e : CoreExpr} {ctx : context} {f : sym} {pes : List (generic_pexpr Unit sym)},
      callRedex? e = some (ctx, f, pes) →
      ∃ (an : List annot) (ra : core_run_annotation),
        e = apply_ctx ctx (Expr an (Eproc ra (Sym f) pes))
  | Expr a0 (Eproc ra0 (Sym f0) pes0), ctx, f, pes, h => by
      have h' : (some (CTX, f0, pes0) : Option (context × sym × List (generic_pexpr Unit sym))) =
          some (ctx, f, pes) := h
      obtain ⟨rfl, rfl, rfl⟩ : CTX = ctx ∧ f0 = f ∧ pes0 = pes := by
        have := Option.some.inj h'
        exact ⟨congrArg Prod.fst this, congrArg (fun q => q.2.1) this,
          congrArg (fun q => q.2.2) this⟩
      exact ⟨a0, ra0, rfl⟩
  | Expr a0 (Eproc ra0 (Impl _) pes0), ctx, f, pes, h => by simp [callRedex?] at h
  | Expr a0 (Esseq pat e1 e2), ctx, f, pes, h => by
      rw [callRedex?_sseq, Option.map_eq_some_iff] at h
      obtain ⟨⟨c1, f1, pes1⟩, h1, hq⟩ := h
      obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
        exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq, congrArg (fun q => q.2.2) hq⟩
      obtain ⟨an, ra, he1⟩ := callRedex?_apply_ctx_eq h1
      exact ⟨an, ra, by show _ = Expr a0 (Esseq pat (apply_ctx c1 _) e2); rw [← he1]⟩
  | Expr a0 (Ewseq pat e1 e2), ctx, f, pes, h => by
      rw [callRedex?_wseq, Option.map_eq_some_iff] at h
      obtain ⟨⟨c1, f1, pes1⟩, h1, hq⟩ := h
      obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
        exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq, congrArg (fun q => q.2.2) hq⟩
      obtain ⟨an, ra, he1⟩ := callRedex?_apply_ctx_eq h1
      exact ⟨an, ra, by show _ = Expr a0 (Ewseq pat (apply_ctx c1 _) e2); rw [← he1]⟩
  | Expr a0 (Eannot ds b), ctx, f, pes, h => by
      rw [callRedex?_annot] at h
      split at h
      · cases h
      · rw [Option.map_eq_some_iff] at h
        obtain ⟨⟨c1, f1, pes1⟩, h1, hq⟩ := h
        obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
          exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq, congrArg (fun q => q.2.2) hq⟩
        obtain ⟨an, ra, he1⟩ := callRedex?_apply_ctx_eq h1
        exact ⟨an, ra, by show _ = Expr a0 (Eannot ds (apply_ctx c1 _)); rw [← he1]⟩
  | Expr a0 (Ebound b), ctx, f, pes, h => by
      rw [callRedex?_bound, Option.map_eq_some_iff] at h
      obtain ⟨⟨c1, f1, pes1⟩, h1, hq⟩ := h
      obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
        exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq, congrArg (fun q => q.2.2) hq⟩
      obtain ⟨an, ra, he1⟩ := callRedex?_apply_ctx_eq h1
      exact ⟨an, ra, by show _ = Expr a0 (Ebound (apply_ctx c1 _)); rw [← he1]⟩
  | Expr a0 (Eunseq es), ctx, f, pes, h => by
      rw [callRedex?_unseq] at h
      obtain ⟨es1, c1, es2, an, ra, rfl, hes⟩ := callRedexU?_apply_ctx_eq h
      refine ⟨an, ra, ?_⟩
      rw [List.nil_append]
      exact congrArg (fun l => Expr a0 (Eunseq l)) hes
  | Expr a0 (Eaction _), ctx, f, pes, h => by simp [callRedex?] at h
  | Expr a0 (Erun _ _ _), ctx, f, pes, h => by simp [callRedex?] at h
  | Expr a0 (Epure _), ctx, f, pes, h => by simp [callRedex?] at h
  | Expr a0 (Ememop _ _), ctx, f, pes, h => by simp [callRedex?] at h
  | Expr a0 (Ecase _ _), ctx, f, pes, h => by simp [callRedex?] at h
  | Expr a0 (Elet _ _ _), ctx, f, pes, h => by simp [callRedex?] at h
  | Expr a0 (Eif _ _ _), ctx, f, pes, h => by simp [callRedex?] at h
  | Expr a0 (Eccall _ _ _ _), ctx, f, pes, h => by simp [callRedex?] at h
  | Expr a0 (End _), ctx, f, pes, h => by simp [callRedex?] at h
  | Expr a0 (Esave _ _ _), ctx, f, pes, h => by simp [callRedex?] at h
  | Expr a0 (Epar _), ctx, f, pes, h => by simp [callRedex?] at h
  | Expr a0 (Ewait _), ctx, f, pes, h => by simp [callRedex?] at h
  | Expr a0 (Eexcluded _ _), ctx, f, pes, h => by simp [callRedex?] at h
/-- The list twin (`negRedexU?_apply_ctx_eq`'s). -/
theorem callRedexU?_apply_ctx_eq :
    ∀ {a0 : List annot} {pre es : List CoreExpr} {ctx : context} {f : sym}
      {pes : List (generic_pexpr Unit sym)},
      callRedexU? a0 pre es = some (ctx, f, pes) →
      ∃ (es1 : List CoreExpr) (c : context) (es2 : List CoreExpr) (an : List annot)
        (ra : core_run_annotation),
        ctx = Cunseq a0 (pre ++ es1) c es2 ∧
        es = es1 ++ apply_ctx c (Expr an (Eproc ra (Sym f) pes)) :: es2
  | a0, pre, [], ctx, f, pes, h => by cases h
  | a0, pre, e :: es, ctx, f, pes, h => by
      simp only [callRedexU?] at h
      split at h
      · rename_i hv
        rw [Option.map_eq_some_iff] at h
        obtain ⟨⟨c1, f1, pes1⟩, h1, hq⟩ := h
        obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
          exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq, congrArg (fun q => q.2.2) hq⟩
        obtain ⟨an, ra, he⟩ := callRedex?_apply_ctx_eq h1
        refine ⟨[], c1, es, an, ra, by rw [List.append_nil], ?_⟩
        rw [List.nil_append, ← he]
      · rename_i hv
        obtain ⟨es1, c1, es2, an, ra, rfl, hes⟩ := callRedexU?_apply_ctx_eq h
        refine ⟨e :: es1, c1, es2, an, ra, by rw [List.append_assoc, List.singleton_append], ?_⟩
        rw [hes]; rfl
end

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
  -- E3 (the std.core bodies the emitted dialect unfolds): `rem_f` (wrapI,
  -- std.core:238; the `(_, int, int)` arm, core_eval.lem:429–441), ctype
  -- equality (`conv_int`'s `ty = '_Bool'`, std.core:33; core_eval.lem:347–348:
  -- `if ty1 = ty2 then Vtrue else Vfalse`, the generated `ctypeEqual`), and the
  -- boolean connectives at two booleans (`is_representable_integer`'s `/\`,
  -- std.core:6; core_eval.lem:454–466, :502–511 — the truth tables; a
  -- non-boolean operand is the `Illformed_program` kill, EvalClass.lean).
  | .OpRem_f, Vobject (OVinteger i1), Vobject (OVinteger i2) =>
      some (Vobject (OVinteger (CerbMem.opIval IntRem_f i1 i2)))
  | .OpEq, Vctype ty1, Vctype ty2 => some (boolValue (ctypeEqual ty1 ty2))
  | .OpAnd, Vtrue, Vtrue => some Vtrue
  | .OpAnd, Vtrue, Vfalse => some Vfalse
  | .OpAnd, Vfalse, Vtrue => some Vfalse
  | .OpAnd, Vfalse, Vfalse => some Vfalse
  | .OpOr, Vtrue, Vtrue => some Vtrue
  | .OpOr, Vtrue, Vfalse => some Vtrue
  | .OpOr, Vfalse, Vtrue => some Vtrue
  | .OpOr, Vfalse, Vfalse => some Vfalse
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
def evalArrayShift [LemFuel] (tds : CerbTags.TagDefsMap) (ty : ctype) :
    value → value → Option value
  | Vobject (OVpointer pv), Vobject (OVinteger iv) =>
      some (Vobject (OVpointer (CerbMem.arrayShiftPtrval tds pv ty iv)))
  | _, _ => none

/-! ### E3: the impl-defined integer semantics, on evaluated operands

The engine evaluates the AST constructors `PEconv_int`/`PEwrapI`/
`PEcatch_exceptional_condition` (core.lem:243–245 — printed as
`__conv_int__`, `wrapI_<op>`, `catch_exceptional_condition_<op>`) by its
OWN functions `mk_conv_int`/`mk_wrapI_op`/`mk_call_catch_exceptional_condition`
(core_eval.lem:61–113; Core_eval.lean:76–108) over the memory model's
integer values (`CerbMem.minIval`/`maxIval`/`opIval`, generated
CerbMem.lean:1261–1366). The four dispatches below call those functions
VERBATIM at an object integer (two object integers) and are `none` at any
other value — the engine's `Illformed_program` kills, classified in
EvalClass.lean. `mk_conv_int`'s signed non-representable arm wraps
(`mk_wrapI`) where std.core's `conv_int` would call the impl-defined
`<Integer.conv_nonrepresentable_signed_integer>`; for the pinned gcc impl
the two coincide (../docs/2026-09-05_note-cerberus-lean-conv-int-divergence.md). -/

/-- `__conv_int__(ity, v)`: `mk_conv_int` (core_eval.lem:819–822). -/
def evalConvInt (ity : integerType) : value → Option value
  | Vobject (OVinteger iv) => some (Vobject (OVinteger (mk_conv_int ity iv)))
  | _ => none

/-- `wrapI_<op>(ity, v1, v2)`: `mk_wrapI_op` (core_eval.lem:828–833). -/
def evalWrapI (ity : integerType) (op : iop) : value → value → Option value
  | Vobject (OVinteger i1), Vobject (OVinteger i2) =>
      some (Vobject (OVinteger (mk_wrapI_op ity op i1 i2)))
  | _, _ => none

/-- `catch_exceptional_condition_<op>(ity, v1, v2)`: `mk_iop` then the range
    check (core_eval.lem:839–849): IN RANGE the value; OUT OF RANGE `none` —
    the engine's `undef loc [UB036_exceptional_condition]`, the classifier's
    `.undef` face (a KILL, never a default). -/
def evalCatch (ity : integerType) (op : iop) : value → value → Option value
  | Vobject (OVinteger i1), Vobject (OVinteger i2) =>
      (mk_call_catch_exceptional_condition ity op i1 i2).map fun iv => Vobject (OVinteger iv)
  | _, _ => none

/-- `is_unsigned(ty)` at a ctype (core_eval.lem:1081–1082). -/
def evalIsUnsigned : value → Option value
  | Vctype ty => some (boolValue (is_unsigned_integer_type ty))
  | _ => none

/-! ## E3 — the standard-library unfolding: budgets and the callee body

The emitted dialect calls the Core standard library (`conv_loaded_int`,
`conv_int`, `is_representable_integer`, …): a `PEcall nm pes` whose
arguments have reached values is replaced by the callee's BODY with the
values substituted (`call_function file nm cvals`, core_eval.lem:120–163 /
Core_eval.lean:111: `file.stdlib` first, then `file.funs`, for a `Sym`
name; `file.impl` for an `Impl` name; the body returned UNEVALUATED,
core_eval.lem:965–979, then `pull_constrained 0`). The mirror evaluator
reads the SAME file object (its `file` parameter is the machine context's
`M.file`) and unfolds through `callBody`, the success path of
`call_function` verbatim: the two lookups, the arity check (the engine's
`failwithI` PANIC at a mismatch, :149–154, is `none` here), and the
substitution `foldl2 subst_sym_pexpr` (:156).

THE INLINING BUDGET. The depth measure `peDepth` bounds the evaluator's
passes and every fuelled recursion below it; a call node must therefore
weigh MORE than the body it unfolds to. `stdBudget nm` is a STATIC
per-callee bound on the depth of that callee's body, keyed by the
callee's printed name (the std.core function names; the `Impl`
constant): the depth of `PEcall nm pes` is `1 + peDepthList pes +
stdBudget nm`, and the evaluator unfolds only when the substituted body's
depth is within the budget (a CHECK, as the `case` arm's depth check —
[USER 2026-09-04] E0 question 8: no lemma through the fuelled
`subst_sym_pexpr`). The budgets are the depths of the transcribed std.core
bodies at the pin (StdCore.lean, `peDepth_isReprBody` … kernel-checked
equalities), each callee's budget exceeding the budgets of the callees its
body names — the acyclic call graph `conv_loaded_int → conv_int →
is_representable_integer` (std.core:5–67). A name outside the table has
budget 0, so no body unfolds under it (fail-closed: the classifier's
`.uncovered`): so `wrapI` (std.core:229–242 — its body is a pure `let`,
outside the grammar) and the impl function
`<Integer.conv_nonrepresentable_signed_integer>` (the gcc impl :17–19,
`wrapI(ty, n)`), both reached by `conv_int` only at a NON-representable
value (never in the corpus, whose arithmetic is in range), and the
recursive `params_length_aux`/`params_nth` (std.core:108–128), whose
unfolding depth is data-dependent — pending (docs/2026-09-05_e3-notes.md). -/

/-- The static inlining budget of a callee (module note above). -/
def stdBudget : generic_name sym → Nat
  | Sym (Symbol _ _ (SD_Id "is_representable_integer")) => 4
  | Sym (Symbol _ _ (SD_Id "conv_int")) => 17
  | Sym (Symbol _ _ (SD_Id "conv_loaded_int")) => 23
  | _ => 0

/-- Every budget is tiny against the evaluator's fuel. -/
theorem stdBudget_le (nm : generic_name sym) : stdBudget nm ≤ 23 := by
  unfold stdBudget
  split <;> omega

/-- The callee's declaration, as `call_function` finds it
    (core_eval.lem:124–146): a `Sym` name in `file.stdlib` then `file.funs`
    (a `Fun` declaration: its parameters and body; any other declaration
    kind is the engine's `failwithI` PANIC, :157–162 — `none` here), an
    `Impl` name in `file.impl0` (an `IFun`; a `Def` is the
    `Illformed_program` kill, :143–145 — `none` here). -/
def lookupFun (file : generic_file Unit core_run_annotation) :
    generic_name sym → Option (List (sym × core_base_type) × generic_pexpr Unit sym)
  | Sym f =>
    match fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
        f file.stdlib with
    | some (Fun _ params body) => some (params, body)
    | some _ => none
    | none =>
      match fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
          f file.funs with
      | some (Fun _ params body) => some (params, body)
      | _ => none
  | Impl c =>
    match fmapLookupBy implementation_constant_compare c file.impl0 with
    | some (IFun _ params body) => some (params, body)
    | _ => none

/-- The callee's body with the argument values substituted —
    `call_function`'s success path verbatim (core_eval.lem:148–156:
    `Utils.foldl2 (fun acc (a, _) cval -> Caux.subst_sym_pexpr a cval acc)
    body_pe params arg_cvals` under the arity check). -/
def callBody (file : generic_file Unit core_run_annotation) (nm : generic_name sym)
    (vs : List value) : Option (generic_pexpr Unit sym) :=
  match lookupFun file nm with
  | some (params, body) =>
    if params.length = vs.length then
      some (foldl2 (fun (acc : generic_pexpr Unit sym) (p : sym × core_base_type) (cval : value) =>
        match acc, p, cval with
        | acc, (a, _), cval => subst_sym_pexpr a cval acc) body params vs)
    else none
  | none => none

/-! ## The pure-expression depth measure (E2: moved here from
Soundness.lean, extended to the loaded-value grammar)

`peDepth` bounds the per-level fuel draw of the engine's
`step_eval_pexpr`/`pull_constrained` (both recurse one fuel level per
operand level) AND, since E2, the number of evaluator PASSES (iterations
of `eval_pexpr_aux2`, Core_eval.lean:152): the arms that return an
UNEVALUATED pexpr — `PEcase` (the selected branch, core_eval.lem:725–745)
and the operand REBUILDS at a non-value operand — strictly decrease it
(`stepPexpr_depth_lt`, Soundness.lean). The engine's wrappers now supply
structural bounds for each traversal; `peDepth pe ≤ LemFuel.fuel` bounds
the number of evaluation passes at the ambient instance. The measure is a
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
  -- E3: the impl arithmetic constructors and `is_unsigned` (one level per
  -- operand level) and the standard-library CALL — the arguments plus the
  -- callee's static inlining budget (module note).
  | Pexpr _ _ (PEconv_int _ pe) => 1 + peDepth pe
  | Pexpr _ _ (PEwrapI _ _ pe1 pe2) => 1 + max (peDepth pe1) (peDepth pe2)
  | Pexpr _ _ (PEcatch_exceptional_condition _ _ pe1 pe2) => 1 + max (peDepth pe1) (peDepth pe2)
  | Pexpr _ _ (PEis_unsigned pe) => 1 + peDepth pe
  | Pexpr _ _ (PEcall nm pes) => 1 + peDepthList pes + stdBudget nm
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

@[simp] theorem peDepth_conv_int (a : List annot) (ity : integerType) (pe : generic_pexpr Unit sym) :
    peDepth (Pexpr a () (PEconv_int ity pe)) = 1 + peDepth pe := by rw [peDepth]

@[simp] theorem peDepth_wrapI (a : List annot) (ity : integerType) (op : iop)
    (pe1 pe2 : generic_pexpr Unit sym) :
    peDepth (Pexpr a () (PEwrapI ity op pe1 pe2)) = 1 + max (peDepth pe1) (peDepth pe2) := by
  rw [peDepth]

@[simp] theorem peDepth_catch (a : List annot) (ity : integerType) (op : iop)
    (pe1 pe2 : generic_pexpr Unit sym) :
    peDepth (Pexpr a () (PEcatch_exceptional_condition ity op pe1 pe2)) =
      1 + max (peDepth pe1) (peDepth pe2) := by
  rw [peDepth]

@[simp] theorem peDepth_is_unsigned (a : List annot) (pe : generic_pexpr Unit sym) :
    peDepth (Pexpr a () (PEis_unsigned pe)) = 1 + peDepth pe := by rw [peDepth]

@[simp] theorem peDepth_call (a : List annot) (nm : generic_name sym)
    (pes : List (generic_pexpr Unit sym)) :
    peDepth (Pexpr a () (PEcall nm pes)) = 1 + peDepthList pes + stdBudget nm := by rw [peDepth]

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
  | .Civmin => true
  | .Civmax => true
  | _ => false

/-- The value of a type-argument constructor at a ctype. -/
def evalTyCtor [LemFuel] (tds : CerbTags.TagDefsMap) : ctor → ctype → Option value
  | .Civalignof, ty => some (Vobject (OVinteger (CerbMem.alignofIval tds ty)))
  | .Civsizeof, ty => some (Vobject (OVinteger (CerbMem.sizeofIval tds ty)))
  | .Cunspecified, ty => some (Vloaded (LVunspecified ty))
  -- E3: `Ivmin(ty)`/`Ivmax(ty)` (std.core's `is_representable_integer` and
  -- `wrapI`): `unatomic_ ty` must be an integer type, then the memory
  -- model's `min_ival`/`max_ival` (core_eval.lem:632–647); any other ctype
  -- is the engine's `error` PANIC — `none` here (fail-closed).
  | .Civmin, ty =>
    match unatomic_ ty with
    | Basic (Integer ity) => some (Vobject (OVinteger (CerbMem.minIval ity)))
    | _ => none
  | .Civmax, ty =>
    match unatomic_ ty with
    | Basic (Integer ity) => some (Vobject (OVinteger (CerbMem.maxIval ity)))
    | _ => none
  | _, _ => none

@[simp] theorem evalTyCtor_alignof [LemFuel] (tds : CerbTags.TagDefsMap) (ty : ctype) :
    evalTyCtor tds .Civalignof ty = some (Vobject (OVinteger (CerbMem.alignofIval tds ty))) := rfl

@[simp] theorem evalTyCtor_sizeof [LemFuel] (tds : CerbTags.TagDefsMap) (ty : ctype) :
    evalTyCtor tds .Civsizeof ty = some (Vobject (OVinteger (CerbMem.sizeofIval tds ty))) := rfl

@[simp] theorem evalTyCtor_unspecified [LemFuel] (tds : CerbTags.TagDefsMap) (ty : ctype) :
    evalTyCtor tds .Cunspecified ty = some (Vloaded (LVunspecified ty)) := rfl

theorem evalTyCtor_isSome [LemFuel] {tds : CerbTags.TagDefsMap} {c : ctor} {ty : ctype} {v : value}
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
def evalCtor [LemFuel] (tds : CerbTags.TagDefsMap) : ctor → List value → Option value
  | .Civalignof, [Vctype ty] => evalTyCtor tds .Civalignof ty
  | .Civsizeof, [Vctype ty] => evalTyCtor tds .Civsizeof ty
  | .Cunspecified, [Vctype ty] => evalTyCtor tds .Cunspecified ty
  | .Civmin, [Vctype ty] => evalTyCtor tds .Civmin ty
  | .Civmax, [Vctype ty] => evalTyCtor tds .Civmax ty
  | .Cspecified, [Vobject ov] => some (Vloaded (LVspecified ov))
  | .Ctuple, vs => some (Vtuple vs)
  | _, _ => none

@[simp] theorem evalCtor_spec [LemFuel] (tds : CerbTags.TagDefsMap) (ov : object_value) :
    evalCtor tds .Cspecified [Vobject ov] = some (Vloaded (LVspecified ov)) := rfl

@[simp] theorem evalCtor_tuple [LemFuel] (tds : CerbTags.TagDefsMap) (vs : List value) :
    evalCtor tds .Ctuple vs = some (Vtuple vs) := rfl

theorem evalCtor_tyCtor [LemFuel] (tds : CerbTags.TagDefsMap) {c : ctor} (hc : isTyCtor c = true)
    (ty : ctype) : evalCtor tds c [Vctype ty] = evalTyCtor tds c ty := by
  cases c <;> first | rfl | (cases hc)

/-- The binops the mirror evaluator covers (`evalBinop`): integer
    arithmetic `Add`/`Sub`/`Mul` and the comparisons
    `Eq`/`Lt`/`Le`/`Gt`/`Ge`. `Div`/`Rem_t`/`Rem_f`/`Exp`/`And`/`Or` are
    outside (fragment closure, 2026-09-02: the operand grammar is
    declared as exactly what the mirror covers). -/
def isMirroredOp : binop → Bool
  | .OpAdd | .OpSub | .OpMul | .OpEq | .OpLt | .OpLe | .OpGt | .OpGe => true
  | .OpRem_f | .OpAnd | .OpOr => true  -- E3 (std.core bodies)
  | _ => false

/-- E2: the constructors the mirror evaluator covers (`evalCtor`): the
    type-argument constants, `Specified`, tuples. -/
def isMirroredCtor : ctor → Bool
  | .Civalignof | .Civsizeof | .Cunspecified | .Cspecified | .Ctuple => true
  | .Civmin | .Civmax => true  -- E3
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
  -- E3: the impl arithmetic constructors, `is_unsigned`, and a call at ANY name (the file decides what it unfolds to; an unknown or
  -- over-budget callee is the classifier's business, EvalClass.lean)
  | Pexpr _ _ (PEconv_int _ pe) => isPePure pe
  | Pexpr _ _ (PEwrapI _ _ pe1 pe2) => isPePure pe1 && isPePure pe2
  | Pexpr _ _ (PEcatch_exceptional_condition _ _ pe1 pe2) => isPePure pe1 && isPePure pe2
  -- `is_unsigned(e)` only at a LEAF operand (`peDepth pe = 1`: a value or a
  -- symbol — the std.core body's substituted ctype): the engine REBUILDS a
  -- non-value operand as `PEis_scalar pe'` (core_eval.lem:1086), so the
  -- iterated passes would compute `is_scalar`, not `is_unsigned`; the
  -- big-step mirror must not claim otherwise (fail-closed).
  | Pexpr _ _ (PEis_unsigned pe) => isPePure pe && decide (peDepth pe = 1)
  | Pexpr _ _ (PEcall _ pes) => isPePureList pes
  | _ => false

def isPePureList : List (generic_pexpr Unit sym) → Bool
  | [] => true
  | pe :: pes => isPePure pe && isPePureList pes

def isPePureAlts : List (pattern × generic_pexpr Unit sym) → Bool
  | [] => true
  | (_, pe) :: rest => isPePure pe && isPePureAlts rest
end

/-- The constrained-pull's image on the covered grammar: annotation
    renormalization only (`pull_constrained` rebuilds every node with `[]`
    annots and recurses into the operands of `PEop`/`PEarray_shift`/`PEnot`
    /`PEconv_int`/`PEwrapI`/`PEcatch_exceptional_condition`/`PEis_unsigned`
    and the scrutinee of `PEcase`; the operands of `PEctor`/`PEif`/`PEcall`
    and the alternatives of `PEcase` are kept VERBATIM by
    `pull_helper` (core_eval.lem:170–307 — the `Right` accumulator pushes
    the ORIGINAL `pe`); no `PEconstrained` exists to pull). E3 moved it
    here from Soundness.lean: the pass applies it to the body a call
    unfolds to (core_eval.lem:975). -/
def peStrip : generic_pexpr Unit sym → generic_pexpr Unit sym
  | Pexpr _ _ (PEop op pe1 pe2) => Pexpr [] () (PEop op (peStrip pe1) (peStrip pe2))
  | Pexpr _ _ (PEarray_shift pe1 ty pe2) =>
      Pexpr [] () (PEarray_shift (peStrip pe1) ty (peStrip pe2))
  | Pexpr _ _ (PEcase pe pats) => Pexpr [] () (PEcase (peStrip pe) pats)
  | Pexpr _ _ (PEnot pe) => Pexpr [] () (PEnot (peStrip pe))
  | Pexpr _ _ (PEconv_int ity pe) => Pexpr [] () (PEconv_int ity (peStrip pe))
  | Pexpr _ _ (PEwrapI ity op pe1 pe2) => Pexpr [] () (PEwrapI ity op (peStrip pe1) (peStrip pe2))
  | Pexpr _ _ (PEcatch_exceptional_condition ity op pe1 pe2) =>
      Pexpr [] () (PEcatch_exceptional_condition ity op (peStrip pe1) (peStrip pe2))
  | Pexpr _ _ (PEis_unsigned pe) => Pexpr [] () (PEis_unsigned (peStrip pe))
  | Pexpr _ _ pex => Pexpr [] () pex

mutual
/-- ONE PASS of `step_eval_pexpr`, UNGUARDED (module section header):
    faithful to the engine's pass on the covered constructors, `none` at
    the engine's kills/undefs/panics and off the grammar. -/
def stepPexprRaw [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym)
    (file : generic_file Unit core_run_annotation) (ρ : EnvStack) :
    generic_pexpr Unit sym → Option (generic_pexpr Unit sym)
  | Pexpr _ _ (PEval v) => some (valPe v)
  | Pexpr _ _ (PEsym x) => (lookup_env (resolveExtern ext x) ρ).map valPe
  | Pexpr _ _ (PEop op pe1 pe2) => do
      let r1 ← stepPexprRaw tds ext file ρ pe1
      let r2 ← stepPexprRaw tds ext file ρ pe2
      match valueFromPexpr r1, valueFromPexpr r2 with
      | some v1, some v2 => (evalBinop op v1 v2).map valPe
      | _, _ => some (Pexpr [] () (PEop op r1 r2))
  | Pexpr _ _ (PEarray_shift pe1 ty pe2) => do
      let r1 ← stepPexprRaw tds ext file ρ pe1
      let r2 ← stepPexprRaw tds ext file ρ pe2
      match valueFromPexpr r1, valueFromPexpr r2 with
      | some v1, some v2 => (evalArrayShift tds ty v1 v2).map valPe
      | _, _ => some (Pexpr [] () (PEarray_shift r1 ty r2))
  | Pexpr _ _ (PEctor c pes) => do
      let rs ← stepPexprsRaw tds ext file ρ pes
      match valueFromPexprs rs with
      | some vs => (evalCtor tds c vs).map valPe
      | none => some (Pexpr [] () (PEctor c rs))
  | Pexpr _ _ (PEcase pe pats) => do
      let r ← stepPexprRaw tds ext file ρ pe
      match valueFromPexpr r with
      | some cval => (select_case subst_sym_pexpr cval pats).map reannot0
      | none => some (Pexpr [] () (PEcase r pats))
  | Pexpr _ _ (PEnot pe) => do
      let r ← stepPexprRaw tds ext file ρ pe
      match valueFromPexpr r with
      | some Vtrue => some (valPe Vfalse)
      | some Vfalse => some (valPe Vtrue)
      | some _ => none
      | none => some (Pexpr [] () (PEnot r))
  | Pexpr _ _ (PEif pe1 pe2 pe3) => do
      let r1 ← stepPexprRaw tds ext file ρ pe1
      match valueFromPexpr r1 with
      | some Vtrue => (stepPexprRaw tds ext file ρ pe2).map reannot0
      | some Vfalse => (stepPexprRaw tds ext file ρ pe3).map reannot0
      | some _ => none
      | none => some (Pexpr [] () (PEif r1 pe2 pe3))
  -- E3. `__conv_int__(ity, e)`: at an object integer the engine's OWN
  -- `mk_conv_int` (core_eval.lem:819–827; :61–81); any other value is the
  -- `Illformed_program` kill (`none`); a non-value rebuilds.
  | Pexpr _ _ (PEconv_int ity pe) => do
      let r ← stepPexprRaw tds ext file ρ pe
      match valueFromPexpr r with
      | some v => (evalConvInt ity v).map valPe
      | none => some (Pexpr [] () (PEconv_int ity r))
  -- `wrapI_<op>(ity, e1, e2)`: `mk_wrapI_op` at two object integers
  -- (core_eval.lem:828–838; :93–96).
  | Pexpr _ _ (PEwrapI ity op pe1 pe2) => do
      let r1 ← stepPexprRaw tds ext file ρ pe1
      let r2 ← stepPexprRaw tds ext file ρ pe2
      match valueFromPexpr r1, valueFromPexpr r2 with
      | some v1, some v2 => (evalWrapI ity op v1 v2).map valPe
      | _, _ => some (Pexpr [] () (PEwrapI ity op r1 r2))
  -- `catch_exceptional_condition_<op>(ity, e1, e2)`: `mk_iop` then the range
  -- check `mk_call_catch_exceptional_condition` (core_eval.lem:839–854;
  -- :83–111): in range the value, OUT OF RANGE the engine's
  -- `undef loc [UB036_exceptional_condition]` — `none` here, the
  -- classifier's `.undef` face (a KILL, never a default).
  | Pexpr _ _ (PEcatch_exceptional_condition ity op pe1 pe2) => do
      let r1 ← stepPexprRaw tds ext file ρ pe1
      let r2 ← stepPexprRaw tds ext file ρ pe2
      match valueFromPexpr r1, valueFromPexpr r2 with
      | some v1, some v2 => (evalCatch ity op v1 v2).map valPe
      | _, _ => some (Pexpr [] () (PEcatch_exceptional_condition ity op r1 r2))
  -- `is_unsigned(ty)` (core_eval.lem:1078–1087): the Ail predicate at a
  -- ctype; a non-ctype value is the kill. NOTE the engine's rebuild arm
  -- at a non-value operand is `PEis_scalar pe'` (:1086 — the lem source's
  -- own text, mirrored VERBATIM; the rebuilt node is outside the grammar,
  -- so a following pass is `.uncovered`; unreachable at the std.core
  -- bodies, whose operand is a substituted ctype value).
  | Pexpr _ _ (PEis_unsigned pe) => do
      let r ← stepPexprRaw tds ext file ρ pe
      match valueFromPexpr r with
      | some v => (evalIsUnsigned v).map valPe
      | none => some (Pexpr [] () (PEis_scalar r))
  -- THE CALL (core_eval.lem:965–995): at argument values the callee's body
  -- with the values substituted (`callBody`), pulled (`peStrip`, the image
  -- of `pull_constrained 0`, :975), returned UNEVALUATED — provided it is
  -- in the covered grammar within the callee's inlining budget (module
  -- note; otherwise `none`, the classifier's `.uncovered`); an unknown
  -- callee is the kill (`none`); a non-value argument rebuilds.
  | Pexpr _ _ (PEcall nm pes) => do
      let rs ← stepPexprsRaw tds ext file ρ pes
      match valueFromPexprs rs with
      | some vs =>
        match callBody file nm vs with
        | some body =>
          if isPePure (peStrip body) && decide (peDepth (peStrip body) ≤ stdBudget nm) then
            some (peStrip body)
          else none
        | none => none
      | none => some (Pexpr [] () (PEcall nm rs))
  | _ => none

/-- The pass mapped over an operand list (the engine's
    `exception_undef_mapM self pes`). -/
def stepPexprsRaw [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym)
    (file : generic_file Unit core_run_annotation) (ρ : EnvStack) :
    List (generic_pexpr Unit sym) → Option (List (generic_pexpr Unit sym))
  | [] => some []
  | pe :: pes => do
      let r ← stepPexprRaw tds ext file ρ pe
      let rs ← stepPexprsRaw tds ext file ρ pes
      some (r :: rs)
end

/-- ONE PASS of `step_eval_pexpr` on the covered grammar: the faithful
    pass, GUARDED by grammar membership (`isPePure`) — so a pass succeeds
    only at a covered term, and the term the engine iterates on next is
    covered exactly when the mirror's next pass succeeds. -/
def stepPexpr [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym)
    (file : generic_file Unit core_run_annotation) (ρ : EnvStack)
    (pe : generic_pexpr Unit sym) : Option (generic_pexpr Unit sym) :=
  if isPePure pe then stepPexprRaw tds ext file ρ pe else none

/-! THE BIG-STEP VALUE (module section header): what the mirror rules
consume. Mutually recursive with its list form, well-founded on the depth (a
pexpr weighs `2 * peDepth`, an operand list `2 * peDepthList + 1`). -/
mutual
def evalPexpr [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym)
    (file : generic_file Unit core_run_annotation) (ρ : EnvStack) :
    generic_pexpr Unit sym → Option value
  | Pexpr _ _ (PEval v) => some v
  | Pexpr _ _ (PEsym x) => lookup_env (resolveExtern ext x) ρ
  | Pexpr _ _ (PEop op pe1 pe2) => do
      let v1 ← evalPexpr tds ext file ρ pe1
      let v2 ← evalPexpr tds ext file ρ pe2
      evalBinop op v1 v2
  | Pexpr _ _ (PEarray_shift pe1 ty pe2) => do
      let v1 ← evalPexpr tds ext file ρ pe1
      let v2 ← evalPexpr tds ext file ρ pe2
      evalArrayShift tds ty v1 v2
  | Pexpr _ _ (PEctor c pes) => do
      let vs ← evalPexprList tds ext file ρ pes
      evalCtor tds c vs
  | Pexpr _ _ (PEcase pe pats) =>
      if isPePureAlts pats then do
        let cval ← evalPexpr tds ext file ρ pe
        let pe'' ← select_case subst_sym_pexpr cval pats
        if peDepth (reannot0 pe'') ≤ peDepthAlts pats then evalPexpr tds ext file ρ (reannot0 pe'')
        else none
      else none
  | Pexpr _ _ (PEnot pe) => do
      let v ← evalPexpr tds ext file ρ pe
      match v with
      | Vtrue => some Vfalse
      | Vfalse => some Vtrue
      | _ => none
  | Pexpr _ _ (PEif pe1 pe2 pe3) =>
      if isPePure pe2 && isPePure pe3 then do
        let b ← evalPexpr tds ext file ρ pe1
        match b with
        | Vtrue => evalPexpr tds ext file ρ pe2
        | Vfalse => evalPexpr tds ext file ρ pe3
        | _ => none
      else none
  -- E3 (the pass's arms, big-step): the engine's own integer functions at
  -- object integers; `none` at the kill/undef faces.
  | Pexpr _ _ (PEconv_int ity pe) => do
      let v ← evalPexpr tds ext file ρ pe
      evalConvInt ity v
  | Pexpr _ _ (PEwrapI ity op pe1 pe2) => do
      let v1 ← evalPexpr tds ext file ρ pe1
      let v2 ← evalPexpr tds ext file ρ pe2
      evalWrapI ity op v1 v2
  | Pexpr _ _ (PEcatch_exceptional_condition ity op pe1 pe2) => do
      let v1 ← evalPexpr tds ext file ρ pe1
      let v2 ← evalPexpr tds ext file ρ pe2
      evalCatch ity op v1 v2
  | Pexpr _ _ (PEis_unsigned pe) =>
      if peDepth pe = 1 then do
        let v ← evalPexpr tds ext file ρ pe
        evalIsUnsigned v
      else none
  | Pexpr _ _ (PEcall nm pes) => do
      let vs ← evalPexprList tds ext file ρ pes
      let body ← callBody file nm vs
      if peDepth (peStrip body) ≤ stdBudget nm then evalPexpr tds ext file ρ (peStrip body)
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
def evalPexprList [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym)
    (file : generic_file Unit core_run_annotation) (ρ : EnvStack) :
    List (generic_pexpr Unit sym) → Option (List value)
  | [] => some []
  | pe :: pes => do
      let v ← evalPexpr tds ext file ρ pe
      let vs ← evalPexprList tds ext file ρ pes
      some (v :: vs)
termination_by pes => 2 * peDepthList pes + 1
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := peDepth_pos pe; omega)
end

/-! ### The big-step equations (statements as before E2) -/

@[simp] theorem evalPexpr_val [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) {file : generic_file Unit core_run_annotation} (ρ : EnvStack)
    (a : List annot) (v : value) :
    evalPexpr tds ext file ρ (Pexpr a () (PEval v)) = some v := by
  rw [evalPexpr]

@[simp] theorem evalPexpr_valPe [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) {file : generic_file Unit core_run_annotation} (ρ : EnvStack)
    (v : value) : evalPexpr tds ext file ρ (valPe v) = some v := by
  rw [valPe, evalPexpr]

@[simp] theorem evalPexpr_sym [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) {file : generic_file Unit core_run_annotation} (ρ : EnvStack)
    (a : List annot) (x : sym) :
    evalPexpr tds ext file ρ (Pexpr a () (PEsym x)) =
      lookup_env (resolveExtern ext x) ρ := by
  rw [evalPexpr]

/-- ... at the empty extern the indirection is the identity (the
    frozen profiles' instance). -/
@[simp] theorem evalPexpr_sym_empty [LemFuel] {file : generic_file Unit core_run_annotation} (tds : CerbTags.TagDefsMap) (ρ : EnvStack)
    (a : List annot) (x : sym) :
    evalPexpr tds fmapEmpty file ρ (Pexpr a () (PEsym x)) = lookup_env x ρ := by
  rw [evalPexpr_sym]; rfl

/-- ... and at ANY extern map that does not redirect `x` (QA-1/Q13: the
    SymFrame-level lookup discharges `resolveExtern` without naming the
    map). -/
theorem evalPexpr_sym_of_resolve [LemFuel] (tds : CerbTags.TagDefsMap) {ext : Fmap sym sym} {file : generic_file Unit core_run_annotation}
    (ρ : EnvStack) (a : List annot) {x : sym} (hx : resolveExtern ext x = x) :
    evalPexpr tds ext file ρ (Pexpr a () (PEsym x)) = lookup_env x ρ := by
  rw [evalPexpr_sym, hx]

theorem evalPexpr_op [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) {file : generic_file Unit core_run_annotation} (ρ : EnvStack) (a : List annot)
    (op : binop) (pe1 pe2 : generic_pexpr Unit sym) :
    evalPexpr tds ext file ρ (Pexpr a () (PEop op pe1 pe2)) = (do
      let v1 ← evalPexpr tds ext file ρ pe1
      let v2 ← evalPexpr tds ext file ρ pe2
      evalBinop op v1 v2) := by
  rw [evalPexpr]

theorem evalPexpr_array_shift [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) {file : generic_file Unit core_run_annotation} (ρ : EnvStack)
    (a : List annot) (ty : ctype)
    (pe1 pe2 : generic_pexpr Unit sym) :
    evalPexpr tds ext file ρ (Pexpr a () (PEarray_shift pe1 ty pe2)) = (do
      let v1 ← evalPexpr tds ext file ρ pe1
      let v2 ← evalPexpr tds ext file ρ pe2
      evalArrayShift tds ty v1 v2) := by
  rw [evalPexpr]

theorem evalPexpr_ctor [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) {file : generic_file Unit core_run_annotation} (ρ : EnvStack)
    (a : List annot) (c : ctor) (pes : List (generic_pexpr Unit sym)) :
    evalPexpr tds ext file ρ (Pexpr a () (PEctor c pes)) = (do
      let vs ← evalPexprList tds ext file ρ pes
      evalCtor tds c vs) := by
  rw [evalPexpr]

@[simp] theorem evalPexprList_nil [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) {file : generic_file Unit core_run_annotation} (ρ : EnvStack) :
    evalPexprList tds ext file ρ [] = some [] := by
  rw [evalPexprList]

theorem evalPexprList_cons [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) {file : generic_file Unit core_run_annotation} (ρ : EnvStack)
    (pe : generic_pexpr Unit sym) (pes : List (generic_pexpr Unit sym)) :
    evalPexprList tds ext file ρ (pe :: pes) = (do
      let v ← evalPexpr tds ext file ρ pe
      let vs ← evalPexprList tds ext file ρ pes
      some (v :: vs)) := by
  rw [evalPexprList]

theorem evalPexpr_ctor1 [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) {file : generic_file Unit core_run_annotation} (ρ : EnvStack)
    (a : List annot) (c : ctor) (pe : generic_pexpr Unit sym) :
    evalPexpr tds ext file ρ (Pexpr a () (PEctor c [pe])) = (do
      let v ← evalPexpr tds ext file ρ pe
      evalCtor tds c [v]) := by
  rw [evalPexpr_ctor, evalPexprList_cons, evalPexprList_nil]
  cases evalPexpr tds ext file ρ pe <;> rfl

theorem evalPexpr_ctor2 [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) {file : generic_file Unit core_run_annotation} (ρ : EnvStack)
    (a : List annot) (c : ctor) (pe1 pe2 : generic_pexpr Unit sym) :
    evalPexpr tds ext file ρ (Pexpr a () (PEctor c [pe1, pe2])) = (do
      let v1 ← evalPexpr tds ext file ρ pe1
      let v2 ← evalPexpr tds ext file ρ pe2
      evalCtor tds c [v1, v2]) := by
  rw [evalPexpr_ctor, evalPexprList_cons, evalPexprList_cons, evalPexprList_nil]
  cases evalPexpr tds ext file ρ pe1 <;> cases evalPexpr tds ext file ρ pe2 <;> rfl

/-- E2: stated at a TYPE-ARGUMENT constructor (`hc`) — a one-tuple of a
    ctype, `Ctuple [Vctype ty]`, is a genuine engine value (`Vtuple [Vctype
    ty]`) outside `evalTyCtor`, so the pre-E2 unconditional statement is
    false at `Ctuple`; `evalPexpr_ctor1` is the unconditional form. -/
@[simp] theorem evalPexpr_tyctor [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) {file : generic_file Unit core_run_annotation} (ρ : EnvStack)
    (a b : List annot) (c : ctor) (ty : ctype) (hc : isTyCtor c = true) :
    evalPexpr tds ext file ρ (Pexpr a () (PEctor c [Pexpr b () (PEval (Vctype ty))])) =
      evalTyCtor tds c ty := by
  rw [evalPexpr_ctor1, evalPexpr_val]
  cases c <;> first | rfl | (cases hc)

theorem evalPexpr_case [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) {file : generic_file Unit core_run_annotation} (ρ : EnvStack)
    (a : List annot) (pe : generic_pexpr Unit sym) (pats : List (pattern × generic_pexpr Unit sym)) :
    evalPexpr tds ext file ρ (Pexpr a () (PEcase pe pats)) =
      (if isPePureAlts pats then (do
        let cval ← evalPexpr tds ext file ρ pe
        let pe'' ← select_case subst_sym_pexpr cval pats
        if peDepth (reannot0 pe'') ≤ peDepthAlts pats then evalPexpr tds ext file ρ (reannot0 pe'')
        else none) else none) := by
  rw [evalPexpr]

theorem evalPexpr_not [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) {file : generic_file Unit core_run_annotation} (ρ : EnvStack)
    (a : List annot) (pe : generic_pexpr Unit sym) :
    evalPexpr tds ext file ρ (Pexpr a () (PEnot pe)) = (do
      let v ← evalPexpr tds ext file ρ pe
      match v with
      | Vtrue => some Vfalse
      | Vfalse => some Vtrue
      | _ => none) := by
  rw [evalPexpr]

theorem evalPexpr_if [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) {file : generic_file Unit core_run_annotation} (ρ : EnvStack)
    (a : List annot) (pe1 pe2 pe3 : generic_pexpr Unit sym) :
    evalPexpr tds ext file ρ (Pexpr a () (PEif pe1 pe2 pe3)) =
      (if isPePure pe2 && isPePure pe3 then (do
        let b ← evalPexpr tds ext file ρ pe1
        match b with
        | Vtrue => evalPexpr tds ext file ρ pe2
        | Vfalse => evalPexpr tds ext file ρ pe3
        | _ => none) else none) := by
  rw [evalPexpr]

@[simp] theorem evalPexpr_undef [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) {file : generic_file Unit core_run_annotation} (ρ : EnvStack)
    (a : List annot) (loc : CerbLocation.Loc) (ub : undefined_behaviour) :
    evalPexpr tds ext file ρ (Pexpr a () (PEundef loc ub)) = none := by
  rw [evalPexpr.eq_def]

/-! ### E3: the big-step equations at the impl arithmetic constructors,
`is_unsigned` and the standard-library call -/

theorem evalPexpr_conv_int [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym)
    {file : generic_file Unit core_run_annotation} (ρ : EnvStack)
    (a : List annot) (ity : integerType) (pe : generic_pexpr Unit sym) :
    evalPexpr tds ext file ρ (Pexpr a () (PEconv_int ity pe)) = (do
      let v ← evalPexpr tds ext file ρ pe
      evalConvInt ity v) := by
  rw [evalPexpr]

theorem evalPexpr_wrapI [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym)
    {file : generic_file Unit core_run_annotation} (ρ : EnvStack)
    (a : List annot) (ity : integerType) (op : iop) (pe1 pe2 : generic_pexpr Unit sym) :
    evalPexpr tds ext file ρ (Pexpr a () (PEwrapI ity op pe1 pe2)) = (do
      let v1 ← evalPexpr tds ext file ρ pe1
      let v2 ← evalPexpr tds ext file ρ pe2
      evalWrapI ity op v1 v2) := by
  rw [evalPexpr]

theorem evalPexpr_catch [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym)
    {file : generic_file Unit core_run_annotation} (ρ : EnvStack)
    (a : List annot) (ity : integerType) (op : iop) (pe1 pe2 : generic_pexpr Unit sym) :
    evalPexpr tds ext file ρ (Pexpr a () (PEcatch_exceptional_condition ity op pe1 pe2)) = (do
      let v1 ← evalPexpr tds ext file ρ pe1
      let v2 ← evalPexpr tds ext file ρ pe2
      evalCatch ity op v1 v2) := by
  rw [evalPexpr]

theorem evalPexpr_is_unsigned [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym)
    {file : generic_file Unit core_run_annotation} (ρ : EnvStack)
    (a : List annot) (pe : generic_pexpr Unit sym) :
    evalPexpr tds ext file ρ (Pexpr a () (PEis_unsigned pe)) =
      (if peDepth pe = 1 then (do
        let v ← evalPexpr tds ext file ρ pe
        evalIsUnsigned v) else none) := by
  rw [evalPexpr]

theorem evalPexpr_call [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym)
    {file : generic_file Unit core_run_annotation} (ρ : EnvStack)
    (a : List annot) (nm : generic_name sym) (pes : List (generic_pexpr Unit sym)) :
    evalPexpr tds ext file ρ (Pexpr a () (PEcall nm pes)) = (do
      let vs ← evalPexprList tds ext file ρ pes
      let body ← callBody file nm vs
      if peDepth (peStrip body) ≤ stdBudget nm then evalPexpr tds ext file ρ (peStrip body)
      else none) := by
  rw [evalPexpr]


/-- All-or-nothing list evaluation (the engine's per-argument
    `full_eval_pexpr'` fold in step_ctx's Erun arm evaluates each
    argument against the ORIGINAL env — `full_eval_pexpr'` is closed
    over `th_st` — while threading the binding accumulator;
    `evalPexprs` mirrors the evaluation half). -/
def evalPexprs [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym)
    (file : generic_file Unit core_run_annotation) (ρ : EnvStack) :
    List (generic_pexpr Unit sym) → Option (List value)
  | [] => some []
  | pe :: pes => do
      let v ← evalPexpr tds ext file ρ pe
      let vs ← evalPexprs tds ext file ρ pes
      pure (v :: vs)

@[simp] theorem evalPexprs_nil [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) {file : generic_file Unit core_run_annotation} (ρ : EnvStack) :
    evalPexprs tds ext file ρ [] = some [] := rfl

theorem evalPexprs_cons [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) {file : generic_file Unit core_run_annotation} (ρ : EnvStack)
    (pe : generic_pexpr Unit sym)
    (pes : List (generic_pexpr Unit sym)) :
    evalPexprs tds ext file ρ (pe :: pes) = (do
      let v ← evalPexpr tds ext file ρ pe
      let vs ← evalPexprs tds ext file ρ pes
      pure (v :: vs)) := rfl

/-- A singleton literal operand list evaluates to its value. -/
theorem evalPexprs_single_val [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) {file : generic_file Unit core_run_annotation} (ρ : EnvStack)
    (a : List annot) (v : value) :
    evalPexprs tds ext file ρ [Pexpr a () (PEval v)] = some [v] := by
  rw [evalPexprs_cons, evalPexpr_val, evalPexprs_nil]
  rfl

/-- A literal head evaluates to its value in front of an evaluated tail. -/
theorem evalPexprs_cons_val [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) {file : generic_file Unit core_run_annotation} (ρ : EnvStack)
    (a : List annot) (v : value) (pes : List (generic_pexpr Unit sym)) (vs : List value)
    (h : evalPexprs tds ext file ρ pes = some vs) :
    evalPexprs tds ext file ρ (Pexpr a () (PEval v) :: pes) = some (v :: vs) := by
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
  simp only [LemLibTheorems.lemListFoldr_eq, List.foldr_cons]
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
  simp only [LemLibTheorems.lemListFoldr_eq, List.foldr_cons, List.foldr_nil]
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
theorem evalPexpr_of_valueFromPexpr [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) {file : generic_file Unit core_run_annotation}
    (ρ : EnvStack) {pe : generic_pexpr Unit sym} {v : value}
    (h : valueFromPexpr pe = some v) : evalPexpr tds ext file ρ pe = some v := by
  rcases pe with ⟨a, u, pe_⟩
  cases u
  cases pe_ <;> simp only [valueFromPexpr] at h
  all_goals first
    | (obtain rfl := Option.some.inj h; exact evalPexpr_val tds ext ρ _ _)
    | (cases h)

/-- All-or-nothing evaluation agrees with the engine's value test on
    literal operand lists (`evalPexpr` is the identity on `PEval v`). -/
theorem evalPexprs_of_valueFromPexprs [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) {file : generic_file Unit core_run_annotation}
    (ρ : EnvStack) {pes : List (generic_pexpr Unit sym)} {vs : List value}
    (h : valueFromPexprs pes = some vs) : evalPexprs tds ext file ρ pes = some vs := by
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

theorem evalPexprs_length [LemFuel] (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) {file : generic_file Unit core_run_annotation}
    (ρ : EnvStack) {pes : List (generic_pexpr Unit sym)} {vs : List value}
    (h : evalPexprs tds ext file ρ pes = some vs) : pes.length = vs.length := by
  induction pes generalizing vs with
  | nil => rw [evalPexprs_nil] at h; cases h; rfl
  | cons pe pes ih =>
    rw [evalPexprs_cons] at h
    revert h
    cases evalPexpr tds ext file ρ pe with
    | none => intro h; cases h
    | some v =>
      cases hpes : evalPexprs tds ext file ρ pes with
      | none => intro h; cases h
      | some vs' =>
        intro h
        obtain rfl : v :: vs' = vs := Option.some.inj h
        simp only [List.length_cons, ih hpes]

/-- The literal-initializer test yields a list of the same length. -/
theorem valueFromPexprs_length {pes : List (generic_pexpr Unit sym)} {vs : List value}
    (h : valueFromPexprs pes = some vs) : pes.length = vs.length := by
  induction pes generalizing vs with
  | nil => rw [valueFromPexprs_nil] at h; cases h; rfl
  | cons pe pes ih =>
    rw [valueFromPexprs_cons] at h
    revert h
    cases valueFromPexpr pe with
    | none => intro h; cases h
    | some v =>
      cases hpes : valueFromPexprs pes with
      | none => intro h; cases h
      | some vs' =>
        intro h
        obtain rfl : v :: vs' = vs := Option.some.inj h
        simp only [List.length_cons, ih hpes]

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
theorem storeM_loc_irrel [LemFuel] {tds : CerbTags.TagDefsMap} (loc loc' : CerbLocation.Loc)
    {ty : ctype} {lk : Bool} {pv : CerbMem.PointerValue} {mv : CerbMem.MemValue} {σ : Mem} :
    applyMemM (CerbMem.storeM tds loc' ty lk pv mv) σ =
      applyMemM (CerbMem.storeM tds loc ty lk pv mv) σ := by
  unfold CerbMem.storeM
  rw [applyMemM_ND, applyMemM_ND]
  dsimp only
  rcases pv with ⟨prov, base⟩
  cases prov <;> cases base <;> dsimp only <;> repeat' (first | rfl | split)

/-- `loadM`'s outcome under `applyMemM` does not depend on the location. -/
theorem loadM_loc_irrel [LemFuel] {tds : CerbTags.TagDefsMap} (loc loc' : CerbLocation.Loc)
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
inductive Step [LemFuel] (M : MachineCtx) : Config → Config → Prop where
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
  /-- Positive strong CREATE at evaluated operands. The memory request
      retains `get_with_address a`, exactly as step_ctx's CreateRequest2.
      CerbMem discards the thread id; a requested address is unsupported
      and takes its disclosed panic path. Public ordinary-allocation rules
      establish that the node requests no address. -/
  | create {a : List annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {pe1 pe2 : generic_pexpr Unit sym}
      {align : CerbMem.IntegerValue} {ty : ctype} {pref : prefix0}
      {pv : CerbMem.PointerValue} {ρ : EnvStack} {ctl : Ctl} {σ σ' : Mem}
      (h1 : valueFromPexpr pe1 = some (Vobject (OVinteger align)))
      (h2 : valueFromPexpr pe2 = some (Vctype ty))
      (hmem : applyMemM (CerbMem.allocateObject M.tagDefs 0 pref align ty (get_with_address a) none) σ =
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
      (hv : evalPexpr M.tagDefs M.extern M.file ρ pe = some v) :
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
      (hv2 : evalPexpr M.tagDefs M.extern M.file ρ pe2 = some (Vobject (OVpointer pv))) :
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
      (hnj : jumpRedex? b = none) (hnc : callRedex? b = none) (hnn : negRedex? b = none)
      (hnv : toVal b = none) :
      Step M (b, ρ, ctl, σ) (b', ρ', ctl', σ') →
      Step M (Expr a (Ebound b), ρ, ctl, σ) (Expr a (Ebound b'), ρ', ctl', σ')
  /-- E5: THE NEGATIVE-ACTION ROUND at the OUTERMOST `bound` of the redex's
      context — step_ctx's `Eaction (Paction Neg act)` arm (core_reduction.lem:
      1290–1309; Core_reduction.lean:484, the `BOUND_NO_SSEQ ctx_bound ctxA`
      case of `break_at_bound_and_sseq ctx`, :868–912): `Step_with_runstate2
      (RSK_tau "Neg Action, no break ==> …" TSK_Misc)` draws a fresh exclusion
      id (`E.fresh_excluded_id`, the run state's `excluded_supply`) and a fresh
      symbol (`E.fresh_symbol`, its `sym_supply`), and rewrites the arena to
      `apply_ctx ctx_bound expr'` with `expr'` = `negRewrite`. The mirror
      states the round at the `bound` node: `negRedex? b` locates the
      negative action under `b` and returns the engine's inner context `ctxA`
      (`ctx_bound = ⟨the frames above⟩ ++ Cbound an CTX`, so the frames above
      REBUILD verbatim — they commute with the rewrite — and the guard
      `hnn` on `bound_ctx` keeps an inner `bound` from framing what the engine
      rewrites at the outer one); `break_at_sseq ctxA = none` selects the
      engine's `BOUND_NO_SSEQ` arm — the `BOUND_WITH_SSEQ` arms (a strong
      sequence between the bound and the action, :1319–1338) are NOT mirrored
      (a registered residual, Round.lean `OpenRound.neg_sseq`). The successor
      control is the general arm's location write at the ACTION node's
      annotations `a` (the redex's `e_annots`) with both supplies advanced
      (`Ctl.draw`); env and memory untouched (a TAU). The drawn values are
      the control's supplies before the draw: `n = ctl.sup.excl`,
      `s = fresh_given_int ctl.sup.sym` (Core_run.lean:123–126,
      Symbol.lean:334). -/
  | neg_bound {an : List annot} {b : CoreExpr} {ctxA : context} {a : List annot}
      {act : CoreAction} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
      (hn : negRedex? b = some (ctxA, a, act))
      (hss : break_at_sseq ctxA = none) :
      Step M (Expr an (Ebound b), ρ, ctl, σ)
           (Expr an (Ebound (negRewrite ctl.sup.excl (fresh_given_int ctl.sup.sym) ctxA act)),
            ρ, (ctl.upd a).draw, σ)
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
  /-- E4: reduction under the `Cunseq` frame at the FOCUSED component — the
      LAST reducible one, every later component (`es2`) a value (get_ctx's
      `Eunseq` arm and `get_ctx_unseq_aux`, core_reduction.lem:544–548,
      :590–601: each reducible component's contexts are PREPENDED to the
      accumulator, so the last reducible component's entry heads the
      engine's step list, and the shipped loop takes the head when it is
      advanceable — `find_can_advance`, driver.lem:1049–1057; apply_ctx's
      `Cunseq` rebuild `Expr annot (Eunseq (es1 ++ [apply_ctx ctx' e] ++
      es2))`, :616–617). The SIBLINGS are ccall-free (`ccallFreeList`):
      `is_unseq_with_ccall` is then `false` at the frame
      (core_reduction.lem:501–519), so an action or memop request under it
      IS advanceable (driver.lem:914–917, :925–927) — the ccall-sibling
      pattern (t9) is E6/E7's. Same three guards as `sseq_ctx`; `toVal e =
      none` is get_ctx's `is_irreducible e = false`. -/
  | unseq_ctx {a : List annot} {es1 : List CoreExpr} {e e' : CoreExpr} {es2 : List CoreExpr}
      {ρ ρ' : EnvStack} {ctl ctl' : Ctl} {σ σ' : Mem}
      (hv2 : valsOnly es2 = true) (hcc : ccallFreeList (es1 ++ es2) = true)
      (hnj : jumpRedex? e = none) (hnc : callRedex? e = none) (hnv : toVal e = none) :
      Step M (e, ρ, ctl, σ) (e', ρ', ctl', σ') →
      Step M (Expr a (Eunseq (es1 ++ e :: es2)), ρ, ctl, σ)
           (Expr a (Eunseq (es1 ++ e' :: es2)), ρ', ctl', σ')
  /-- E4: UNSEQ-PURE / UNSEQ-ANNOT — `unseq({A_1}?v_1, …, {A_n}?v_n) -->
      {A_1 ++ … ++ A_n}(v_1, …, v_n)` (one_step0's `Eunseq` arm at
      all-irreducible components, core_reduction.lem:375–386, through
      `one_step_unseq_aux` :258–274 — the mirror's `collectUnseq`; step_ctx's
      general arm wraps the TAU as `Step_tau2 "…" TSK_Misc` at the
      location-updated thread with the env verbatim, :1461–1463; the
      successor `Expr annots (Eannot fps (mk_value_e (Vtuple cvals)))`
      VERBATIM — an `Eannot` node even at `fps = []`). A race
      (`collectUnseq … = none`) is the engine's UNSEQUENCED-RACE kill
      (UB035, :1480–1484), classified in Round.lean, never a step. -/
  | unseq_vals {a : List annot} {ws : List SpikeValA} {fps : List dyn_annotation}
      {cvals : List value} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
      (hcol : collectUnseq ([], []) ws = some (fps, cvals)) :
      Step M (Expr a (Eunseq (ws.map ofValA)), ρ, ctl, σ)
           (Expr a (Eannot fps (Expr [] (Epure (Pexpr [] () (PEval (Vtuple cvals)))))),
            ρ, ctl.upd a, σ)
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
      (hvs : evalPexprs M.tagDefs M.extern M.file (ev0 :: evs) pes = some vs) :
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
      (hvals : evalPexprs M.tagDefs M.extern M.file ρ (saveParamPexprs ps) = some cvals) :
      Step M (Expr a (Esave sb ps body), ρ, ctl, σ)
           (Expr a (Esave sb (saveParamsWithValues ps cvals) body), ρ, ctl.upd a, σ)
  /-- Eif, true branch: ONE engine step with a BIG-STEP guard (one_step0's
      Eif TAU_WITH_RUNSTATE, core_reduction.lem:363–375). -/
  | if_true {a : List annot} {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
      {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
      (hg : evalPexpr M.tagDefs M.extern M.file ρ g = some Vtrue) :
      Step M (Expr a (Eif g e2 e3), ρ, ctl, σ) (e2, ρ, ctl.upd a, σ)
  /-- Eif, false branch. -/
  | if_false {a : List annot} {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
      {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
      (hg : evalPexpr M.tagDefs M.extern M.file ρ g = some Vfalse) :
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
      (hv : evalPexpr M.tagDefs M.extern M.file ρ pe = some cval) :
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
      (hv1 : evalPexpr M.tagDefs M.extern M.file ρ pe1 = some v1)
      (hv2 : evalPexpr M.tagDefs M.extern M.file ρ pe2 = some v2) :
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
      (hv2 : evalPexpr M.tagDefs M.extern M.file ρ pe2 = some (Vobject (OVpointer pv)))
      (hv3 : evalPexpr M.tagDefs M.extern M.file ρ pe3 = some cv) :
      Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Store0 lk (Pexpr [] () (PEval (Vctype ty))) pe2 pe3 mo)))), ρ, ctl, σ)
           (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Store0 lk (Pexpr [] () (PEval (Vctype ty)))
                      (Pexpr [] () (PEval (Vobject (OVpointer pv))))
                      (Pexpr [] () (PEval cv)) mo)))), ρ, ctl.upd a, σ)
  /-- E5: THE EXCLUDED STORE at evaluated operands — the negative action's
      performance under `Eexcluded n act` (step_ctx's `Eexcluded n act =>
      process_action (Just n) (fun z -> Eexcluded n z) act` arm,
      core_reduction.lem:1345–1346; Core_reduction.lean:484): step_action's
      Store0 arm at `is_excluded = Just n` (:694–711) issues the same
      `StoreRequest2` as the positive store, its continuation
      `Expr [] (Eannot [DA_neg n [] fp] (mk_value_e Vunit))` — the dynamic
      annotation is NEGATIVE with the exclusion id (the unseq completion
      `do_race` reads it; `collectUnseq`). Driver discharge identical to
      `Step.store` (`action_request_sequential2`'s StoreRequest2 arm,
      driver.lem:690–708). Successor control `ctl.upd a` at the `Eexcluded`
      node's annotations (the general arm's `e_annots`). -/
  | excluded_store {a : List annot} {n : Nat} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {lk : Bool} {pe1 pe2 pe3 : generic_pexpr Unit sym}
      {ty : ctype} {pv : CerbMem.PointerValue} {cv : value}
      {mo : memory_order} {mv : CerbMem.MemValue} {fp : CerbMem.Footprint}
      {ρ : EnvStack} {ctl : Ctl} {σ σ' : Mem}
      (h1 : valueFromPexpr pe1 = some (Vctype ty))
      (h2 : valueFromPexpr pe2 = some (Vobject (OVpointer pv)))
      (h3 : valueFromPexpr pe3 = some cv)
      (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv = some mv)
      (hmem : applyMemM (CerbMem.storeM M.tagDefs loc ty lk pv mv) σ = some (fp, σ')) :
      Step M (Expr a (Eexcluded n (Action loc ann (Store0 lk pe1 pe2 pe3 mo))), ρ, ctl, σ)
           (Expr [] (Eannot [DA_neg n [] fp]
              (Expr [] (Epure (Pexpr [] () (PEval Vunit))))), ρ, ctl.upd a, σ')
  /-- E5: ACTION_EVAL for an excluded store whose operands are NOT all values
      (step_action's Store0 `_, _, _` arm under `process_action (Just n)`:
      the node is REBUILT as `Expr e_annots (Eexcluded n act')` at the
      evaluated operands, core_reduction.lem:721–727). -/
  | excluded_store_eval {a : List annot} {n : Nat} {loc : CerbLocation.Loc}
      {ann : core_run_annotation} {lk : Bool} {ty : ctype}
      {pe2 pe3 : generic_pexpr Unit sym} {pv : CerbMem.PointerValue}
      {cv : value} {mo : memory_order} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
      (hnv : valueFromPexprs [pe2, pe3] = none)
      (hv2 : evalPexpr M.tagDefs M.extern M.file ρ pe2 = some (Vobject (OVpointer pv)))
      (hv3 : evalPexpr M.tagDefs M.extern M.file ρ pe3 = some cv) :
      Step M (Expr a (Eexcluded n (Action loc ann
              (Store0 lk (Pexpr [] () (PEval (Vctype ty))) pe2 pe3 mo))), ρ, ctl, σ)
           (Expr a (Eexcluded n (Action loc ann
              (Store0 lk (Pexpr [] () (PEval (Vctype ty)))
                      (Pexpr [] () (PEval (Vobject (OVpointer pv))))
                      (Pexpr [] () (PEval cv)) mo))), ρ, ctl.upd a, σ)
  /-- ACTION_EVAL for a positive strong kill with an unevaluated pointer
      operand (step_action's Kill `none` arm). -/
  | kill_eval {a : List annot} {loc : CerbLocation.Loc}
      {ann : core_run_annotation} {kind : kill_kind}
      {pe : generic_pexpr Unit sym} {pv : CerbMem.PointerValue}
      {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
      (hnv : valueFromPexpr pe = none)
      (hv : evalPexpr M.tagDefs M.extern M.file ρ pe = some (Vobject (OVpointer pv))) :
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
      (hv1 : evalPexpr M.tagDefs M.extern M.file ρ pe1 = some (Vobject (OVinteger align)))
      (hv2 : evalPexpr M.tagDefs M.extern M.file ρ pe2 = some (Vobject (OVinteger size))) :
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
      (hv1 : evalPexpr M.tagDefs M.extern M.file ρ pe1 = some (Vobject (OVinteger align)))
      (hv2 : evalPexpr M.tagDefs M.extern M.file ρ pe2 = some (Vctype ty)) :
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
      (hvs : evalPexprs M.tagDefs M.extern M.file ρ pes = some vs)
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

theorem Step.store_canonical [LemFuel] {M : MachineCtx} {a : List annot}
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

theorem Step.load_canonical [LemFuel] {M : MachineCtx} {a : List annot}
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

theorem Step.create_canonical [LemFuel] {M : MachineCtx} {a : List annot}
    {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {align : CerbMem.IntegerValue} {ty : ctype}
    {pref : prefix0} {pv : CerbMem.PointerValue} {ρ : EnvStack} {ctl : Ctl} {σ σ' : Mem}
    (hmem : applyMemM (CerbMem.allocateObject M.tagDefs 0 pref align ty (get_with_address a) none) σ =
      some (pv, σ')) :
    Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Create (Pexpr [] () (PEval (Vobject (OVinteger align))))
                    (Pexpr [] () (PEval (Vctype ty))) pref)))), ρ, ctl, σ)
         (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer pv))))), ρ, ctl.upd a, σ') :=
  Step.create rfl rfl hmem

theorem Step.kill_canonical [LemFuel] {M : MachineCtx} {a : List annot}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {kind : kill_kind}
    {pv : CerbMem.PointerValue} {ρ : EnvStack} {ctl : Ctl} {σ σ' : Mem}
    (hmem : applyMemM (CerbMem.killM loc (is_dynamic kind) pv) σ = some ((), σ')) :
    Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Kill kind (Pexpr [] () (PEval (Vobject (OVpointer pv)))))))), ρ, ctl, σ)
         (Expr [] (Epure (Pexpr [] () (PEval Vunit))), ρ, ctl.upd a, σ') :=
  Step.kill rfl hmem

theorem Step.alloc_canonical [LemFuel] {M : MachineCtx} {a : List annot}
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

theorem Step.ctl_cases [LemFuel] {M : MachineCtx} {e e' : CoreExpr} {ρ ρ' : EnvStack}
    {ctl ctl' : Ctl} {σ σ' : Mem}
    (h : Step M (e, ρ, ctl, σ) (e', ρ', ctl', σ')) :
    (∃ a, ctl' = ctl.upd a) ∨
    (∃ a, ctl' = (ctl.upd a).draw) ∨
    (∃ ctx f pes params body vs, callRedex? e = some (ctx, f, pes) ∧
      evalPexprs M.tagDefs M.extern M.file ρ pes = some vs ∧
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
    rcases ih rfl rfl with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨_, _, _, _, _, _, hc1, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, -⟩
    · exact .inl ⟨a, rfl⟩
    · exact .inr (.inl ⟨a, rfl⟩)
    · rw [hc1] at hnc; cases hnc
    · rw [toVal_ofValA] at hnv; cases hnv
  | wseq_ctx hnj hnc hnv hs ih =>
    cases hcfg; cases hcfg'
    rcases ih rfl rfl with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨_, _, _, _, _, _, hc1, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, -⟩
    · exact .inl ⟨a, rfl⟩
    · exact .inr (.inl ⟨a, rfl⟩)
    · rw [hc1] at hnc; cases hnc
    · rw [toVal_ofValA] at hnv; cases hnv
  | annot_ctx hnj hnc hnv hg hs ih =>
    cases hcfg; cases hcfg'
    rcases ih rfl rfl with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨_, _, _, _, _, _, hc1, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, -⟩
    · exact .inl ⟨a, rfl⟩
    · exact .inr (.inl ⟨a, rfl⟩)
    · rw [hc1] at hnc; cases hnc
    · rw [toVal_ofValA] at hnv; cases hnv
  | bound_ctx hnj hnc hnn hnv hs ih =>
    cases hcfg; cases hcfg'
    rcases ih rfl rfl with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨_, _, _, _, _, _, hc1, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, -⟩
    · exact .inl ⟨a, rfl⟩
    · exact .inr (.inl ⟨a, rfl⟩)
    · rw [hc1] at hnc; cases hnc
    · rw [toVal_ofValA] at hnv; cases hnv
  | bound_pure => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | unseq_ctx hv2 hcc hnj hnc hnv hs ih =>
    cases hcfg; cases hcfg'
    rcases ih rfl rfl with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨_, _, _, _, _, _, hc1, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, -⟩
    · exact .inl ⟨a, rfl⟩
    · exact .inr (.inl ⟨a, rfl⟩)
    · rw [hc1] at hnc; cases hnc
    · rw [toVal_ofValA] at hnv; cases hnv
  | unseq_vals hcol => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | bound_annot => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | neg_bound hn hss => cases hcfg; cases hcfg'; exact .inr (.inl ⟨_, rfl⟩)
  | excluded_store h1 h2 h3 hmv hmem => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
  | excluded_store_eval hnv hv2 hv3 => cases hcfg; cases hcfg'; exact .inl ⟨_, rfl⟩
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
    exact .inr (.inr (.inl ⟨_, _, _, _, _, _, hc, hvs, hf, hlen, rfl, rfl, rfl, rfl⟩))
  | ret =>
    cases hcfg; cases hcfg'
    exact .inr (.inr (.inr ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩))
  | ret_annot => cases hcfg; cases hcfg'; exact .inl ⟨[], rfl⟩

/-- The general-arm successor control: the location write, or — E5 — the
    location write followed by the supply draw (`Step.neg_bound`). -/
theorem Step.ctl_upd [LemFuel] {M : MachineCtx} {e e' : CoreExpr} {ρ ρ' : EnvStack}
    {ctl ctl' : Ctl} {σ σ' : Mem}
    (h : Step M (e, ρ, ctl, σ) (e', ρ', ctl', σ'))
    (hc : callRedex? e = none) (hv : toVal e = none) :
    ∃ a, ctl' = ctl.upd a ∨ ctl' = (ctl.upd a).draw := by
  rcases h.ctl_cases with ⟨a, heq⟩ | ⟨a, heq⟩ | ⟨ctx, f, pes, _, _, _, hc', -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, -⟩
  · exact ⟨a, .inl heq⟩
  · exact ⟨a, .inr heq⟩
  · rw [hc'] at hc; cases hc
  · rw [toVal_ofValA] at hv; cases hv

/-- The control's FRAME fields (κ, proc, execLoc) are preserved at every
    configuration that is neither a call redex (in context) nor a value
    (the pre-E1 `Step.ctl_eq`, minus the location; E5: minus the
    supplies, which the negative-action round draws from). -/
theorem Step.ctl_eq [LemFuel] {M : MachineCtx} {e e' : CoreExpr} {ρ ρ' : EnvStack}
    {ctl ctl' : Ctl} {σ σ' : Mem}
    (h : Step M (e, ρ, ctl, σ) (e', ρ', ctl', σ'))
    (hc : callRedex? e = none) (hv : toVal e = none) :
    ctl'.κ = ctl.κ ∧ ctl'.proc = ctl.proc ∧ ctl'.execLoc = ctl.execLoc := by
  obtain ⟨a, rfl | rfl⟩ := h.ctl_upd hc hv <;> exact ⟨rfl, rfl, rfl⟩

theorem Step.ctl_eq' [LemFuel] {M : MachineCtx} {c c' : Config} (h : Step M c c')
    (hc : callRedex? c.1 = none) (hv : toVal c.1 = none) :
    ∃ a, c'.2.2.1 = c.2.2.1.upd a ∨ c'.2.2.1 = (c.2.2.1.upd a).draw := by
  obtain ⟨e, ρ, ctl, σ⟩ := c
  obtain ⟨e', ρ', ctl', σ'⟩ := c'
  exact h.ctl_upd hc hv

/-- E5 (slice 2): THE CONTROL'S SYMBOL SUPPLY NEVER DECREASES along a step —
    its only writer is the negative-action round's draw (`Ctl.draw`,
    `Step.neg_bound`); the general arm's location write, the call push and
    the return carry `sup` verbatim. This is what preserves the WP-level
    supply bound `M.runState.sym_supply ≤ sp.sym` of `wps.pre`/`wpt.pre`
    (Wps.lean/Wpt.lean) from a configuration to its successor. -/
theorem Step.sup_sym_le [LemFuel] {M : MachineCtx} {e e' : CoreExpr} {ρ ρ' : EnvStack}
    {ctl ctl' : Ctl} {σ σ' : Mem}
    (h : Step M (e, ρ, ctl, σ) (e', ρ', ctl', σ')) : ctl.sup.sym ≤ ctl'.sup.sym := by
  rcases h.ctl_cases with ⟨a, rfl⟩ | ⟨a, rfl⟩ |
      ⟨ctx, f, pes, params, body, vs, -, -, -, -, -, -, rfl, -⟩ |
      ⟨a1, b1, v, ev0, evs, q, ctx, κ, q', ℓ, lc, sp, -, -, rfl, -, -, rfl, -⟩
  · exact Nat.le_refl _
  · exact Nat.le_succ _
  · exact Nat.le_refl _
  · exact Nat.le_refl _

/-- A general-arm step's successor control IS an update of the source
    control — or its supply draw (E5) — restated on the step itself so that
    congruence rules apply to a step whose successor was produced by
    the Language interface (where the control component is an opaque
    projection). -/
theorem Step.retag [LemFuel] {M : MachineCtx} {e e' : CoreExpr} {ρ ρ' : EnvStack}
    {ctl ctl' : Ctl} {σ σ' : Mem}
    (h : Step M (e, ρ, ctl, σ) (e', ρ', ctl', σ'))
    (hc : callRedex? e = none) (hv : toVal e = none) :
    ∃ a, Step M (e, ρ, ctl, σ) (e', ρ', ctl.upd a, σ') ∨
      Step M (e, ρ, ctl, σ) (e', ρ', (ctl.upd a).draw, σ') := by
  obtain ⟨a, rfl | rfl⟩ := h.ctl_upd hc hv
  · exact ⟨a, .inl h⟩
  · exact ⟨a, .inr h⟩

/-- A step that keeps the call stack is a general-arm step: `κ` grows at
    the call and shrinks at the return. -/
theorem Step.ctl_upd_of_κ [LemFuel] {M : MachineCtx} {e e' : CoreExpr} {ρ ρ' : EnvStack}
    {ctl ctl' : Ctl} {σ σ' : Mem}
    (h : Step M (e, ρ, ctl, σ) (e', ρ', ctl', σ')) (hκ : ctl'.κ = ctl.κ) :
    ∃ a, ctl' = ctl.upd a ∨ ctl' = (ctl.upd a).draw := by
  rcases h.ctl_cases with ⟨a, heq⟩ | ⟨a, heq⟩ |
      ⟨ctx, f, pes, _, _, _, -, -, -, -, -, -, rfl, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, -, -, rfl, -, -, rfl, -⟩
  · exact ⟨a, .inl heq⟩
  · exact ⟨a, .inr heq⟩
  · exact absurd hκ (by simp)
  · exact absurd hκ (by simp)

/-- The frame fields at a stack-keeping step. -/
theorem Step.ctl_frame_of_κ [LemFuel] {M : MachineCtx} {e e' : CoreExpr} {ρ ρ' : EnvStack}
    {ctl ctl' : Ctl} {σ σ' : Mem}
    (h : Step M (e, ρ, ctl, σ) (e', ρ', ctl', σ')) (hκ : ctl'.κ = ctl.κ) :
    ctl'.proc = ctl.proc ∧ ctl'.execLoc = ctl.execLoc := by
  obtain ⟨a, rfl | rfl⟩ := h.ctl_upd_of_κ hκ <;> exact ⟨rfl, rfl⟩

theorem Step.env_cons' [LemFuel] {M : MachineCtx} {c c' : Config}
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
  | bound_ctx hnj hnc hnn hnv hs ih => exact ih hκ
  | bound_pure => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | unseq_ctx hv2 hcc hnj hnc hnv hs ih => exact ih hκ
  | unseq_vals hcol => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | bound_annot => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | neg_bound hn hss => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | excluded_store h1 h2 h3 hmv hmem => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | excluded_store_eval hnv hv2 hv3 => exact fun ev0 evs hin => ⟨ev0, hin⟩
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

theorem Step.env_cons [LemFuel] {M : MachineCtx} {e : CoreExpr} {ev0 : Fmap sym value}
    {evs : List (Fmap sym value)} {ctl ctl' : Ctl} {σ : Mem}
    {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    (h : Step M (e, ev0 :: evs, ctl, σ) (e', ρ', ctl', σ')) (hκ : ctl'.κ = ctl.κ) :
    ∃ ev0', ρ' = ev0' :: evs :=
  h.env_cons' hκ ev0 evs rfl

/-! `Step.ccallFree_preserved` moved to Soundness.lean in E5: the `case_value`
case needs the substitution shape lemma ccallFree_subst, whose structural
wrapper bound is discharged beside esize in Soundness.lean. -/

/-- Inversion at a call redex IN CONTEXT: the step is THE CALL, its
    successor determined by the file lookup, the argument values and the
    captured context. By induction on the step: a congruence rule cannot
    frame a call of its sub-expression (E1: the guard `hnc`), so the only
    rule at a configuration with a call redex is `Step.call`. -/
theorem Step.call_inv' [LemFuel] {M : MachineCtx} {c : Config}
    {out : Config} (h : Step M c out) :
    ∀ {ctx : context} {f : sym} {pes : List (generic_pexpr Unit sym)},
      callRedex? c.1 = some (ctx, f, pes) →
      ∃ params body vs, evalPexprs M.tagDefs M.extern M.file c.2.1 pes = some vs ∧
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
  | bound_ctx hnj hnc hnn hnv hs => intro ctx f pes hc; rw [callRedex?_bound, hnc] at hc; cases hc
  | bound_pure => intro ctx f pes hc; simp [callRedex?] at hc
  | unseq_ctx hv2 hcc hnj hnc hnv hs =>
    intro ctx f pes hc; rw [callRedex?_unseq_focus _ hnv hv2, hnc] at hc; cases hc
  | unseq_vals hcol => intro ctx f pes hc; rw [callRedex?_unseq_vals] at hc; cases hc
  | bound_annot => intro ctx f pes hc; simp [callRedex?] at hc
  | neg_bound hn hss =>
    intro ctx f pes hc
    rw [callRedex?_bound, callRedex?_none_of_negRedex?_some hn] at hc; cases hc
  | excluded_store h1 h2 h3 hmv hmem => intro ctx f pes hc; simp [callRedex?] at hc
  | excluded_store_eval hnv hv2 hv3 => intro ctx f pes hc; simp [callRedex?] at hc
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

theorem Step.call_inv [LemFuel] {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config} (h : Step M (e, ρ, ctl, σ) out)
    {ctx : context} {f : sym} {pes : List (generic_pexpr Unit sym)}
    (hc : callRedex? e = some (ctx, f, pes)) :
    ∃ params body vs, evalPexprs M.tagDefs M.extern M.file ρ pes = some vs ∧
      lookupProc M.file M.extern f = some (params, body) ∧ params.length = vs.length ∧
      out = (body, procEnv params vs :: ρ, ctl.callPush (redexAnnots e) ctx f, σ) :=
  h.call_inv' hc

/-- A call step never keeps the call stack (the frame is pushed). -/
theorem Step.call_ne_same_κ [LemFuel] {M : MachineCtx} {e e' : CoreExpr} {ρ ρ' : EnvStack}
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
theorem Step.call_ne_upd [LemFuel] {M : MachineCtx} {e e' : CoreExpr} {ρ ρ' : EnvStack}
    {ctl : Ctl} {σ σ' : Mem} {ctx : context} {f : sym} {a : List annot}
    {pes : List (generic_pexpr Unit sym)}
    (hc : callRedex? e = some (ctx, f, pes))
    (h : Step M (e, ρ, ctl, σ) (e', ρ', ctl.upd a, σ')) : False :=
  h.call_ne_same_κ hc rfl

/-- Reducibility at a call redex in context whose lookup, arity and
    arguments succeed. -/
theorem Step.call_of_callRedex [LemFuel] {M : MachineCtx} {e : CoreExpr} {ctx : context} {f : sym}
    {pes : List (generic_pexpr Unit sym)} {params : List (sym × core_base_type)}
    {body : CoreExpr} {vs : List value} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    (hc : callRedex? e = some (ctx, f, pes))
    (hvs : evalPexprs M.tagDefs M.extern M.file ρ pes = some vs)
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
theorem Step.val_elim [LemFuel] {M : MachineCtx} {w : SpikeValA} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
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
theorem Step.pure_val_elim [LemFuel] {M : MachineCtx} {a b : List annot} {v : value} {ρ : EnvStack}
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
theorem Step.annot_val_inv [LemFuel] {M : MachineCtx} {a a2 b : List annot} {ds : List dyn_annotation}
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

theorem Step.toVal_none [LemFuel] {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config} (hκ : ctl.κ = [])
    (h : Step M (e, ρ, ctl, σ) out) : toVal e = none := by
  cases hv : toVal e with
  | none => rfl
  | some w =>
    obtain ⟨wa, -, rfl⟩ := ofValA_of_toVal hv
    exact (h.val_elim hκ).elim

theorem Step.toValA_none [LemFuel] {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config} (hκ : ctl.κ = [])
    (h : Step M (e, ρ, ctl, σ) out) : toValA e = none :=
  toValA_none_of_toVal_none (h.toVal_none hκ)

/-- A stepping tuple is not a Language value: at the empty stack because
    values do not step there, at a non-empty stack by `toValRt`'s
    definition (the `val_stuck` law, Lang.lean). -/
theorem Step.toValRt_none [LemFuel] {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
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
theorem Step.sameTail [LemFuel] {M : MachineCtx} {e e' : CoreExpr} {ρ ρ' : EnvStack}
    {ctl ctl' : Ctl} {σ σ' : Mem}
    (h : Step M (e, ρ, ctl, σ) (e', ρ', ctl', σ')) (hκ : ctl'.κ = ctl.κ) : SameTail ρ ρ' :=
  h.env_cons' hκ

/-- THE ENVIRONMENT-DEPTH INVARIANT: the environment stack is always
    deeper than the call stack. -/
theorem Step.env_depth [LemFuel] {M : MachineCtx} {e e' : CoreExpr} {ρ ρ' : EnvStack}
    {ctl ctl' : Ctl} {σ σ' : Mem}
    (h : Step M (e, ρ, ctl, σ) (e', ρ', ctl', σ'))
    (hlen : ctl.κ.length < ρ.length) : ctl'.κ.length < ρ'.length := by
  rcases h.ctl_cases with ⟨a, rfl⟩ | ⟨a, rfl⟩ |
      ⟨ctx, f, pes, params, body, vs, -, -, -, -, rfl, rfl, rfl, rfl⟩ |
      ⟨a1, b1, v, ev0, evs, p, ctx, κ, q, ℓ, lc, sp, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases ρ with
    | nil => simp at hlen
    | cons ev0 evs =>
      obtain ⟨ev0', rfl⟩ := h.env_cons' rfl ev0 evs rfl
      simpa using hlen
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
theorem Step.ret_inv [LemFuel] {M : MachineCtx} {a b : List annot} {v : value} {ρ : EnvStack}
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
theorem Step.ret_annot_inv [LemFuel] {M : MachineCtx} {a a2 b : List annot} {ds : List dyn_annotation}
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
theorem Step.store_inv [LemFuel] {M : MachineCtx} {a : List annot} {loc : CerbLocation.Loc}
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
theorem Step.load_inv [LemFuel] {M : MachineCtx} {a : List annot} {loc : CerbLocation.Loc}
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
theorem Step.create_inv [LemFuel] {M : MachineCtx} {a : List annot} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {align : CerbMem.IntegerValue} {ty : ctype}
    {pref : prefix0} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config}
    (h : Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Create (Pexpr [] () (PEval (Vobject (OVinteger align))))
                    (Pexpr [] () (PEval (Vctype ty))) pref)))), ρ, ctl, σ) out) :
    ∃ pv σ',
      applyMemM (CerbMem.allocateObject M.tagDefs 0 pref align ty (get_with_address a) none) σ = some (pv, σ') ∧
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
theorem Step.create_op_inv [LemFuel] {M : MachineCtx} {a : List annot}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (h : Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Create pe1 pe2 pref)))), ρ, ctl, σ) out) :
    ∃ align ty, evalPexpr M.tagDefs M.extern M.file ρ pe1 = some (Vobject (OVinteger align)) ∧
      evalPexpr M.tagDefs M.extern M.file ρ pe2 = some (Vctype ty) ∧
      out = (Expr a (Eaction (Paction polarity.Pos (Action loc ann
        (Create (Pexpr [] () (PEval (Vobject (OVinteger align))))
                (Pexpr [] () (PEval (Vctype ty))) pref)))), ρ, ctl.upd a, σ) := by
  cases h with
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | create h1 h2 hmem => rw [valueFromPexprs_pair, h1, h2] at hnv; cases hnv
  | create_eval hnv' hv1 hv2 => exact ⟨_, _, hv1, hv2, rfl⟩

/-- Inversion at a kill redex of either kind (canonical operand instance). -/
theorem Step.kill_inv [LemFuel] {M : MachineCtx} {a : List annot} {loc : CerbLocation.Loc}
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
theorem Step.kill_op_inv [LemFuel] {M : MachineCtx} {a : List annot}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {kind : kill_kind}
    {pe : generic_pexpr Unit sym}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (hnv : valueFromPexpr pe = none)
    (h : Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Kill kind pe)))), ρ, ctl, σ) out) :
    ∃ pv, evalPexpr M.tagDefs M.extern M.file ρ pe = some (Vobject (OVpointer pv)) ∧
      out = (Expr a (Eaction (Paction polarity.Pos (Action loc ann
        (Kill kind (Pexpr [] () (PEval (Vobject (OVpointer pv)))))))), ρ, ctl.upd a, σ) := by
  cases h with
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | kill h1 hmem => rw [hnv] at h1; cases h1
  | kill_eval hnv' hv => exact ⟨_, hv, rfl⟩

/-- Inversion at an alloc redex (canonical operand instance). -/
theorem Step.alloc_inv [LemFuel] {M : MachineCtx} {a : List annot} {loc : CerbLocation.Loc}
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
theorem Step.alloc_op_inv [LemFuel] {M : MachineCtx} {a : List annot}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (h : Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Alloc0 pe1 pe2 pref)))), ρ, ctl, σ) out) :
    ∃ align size, evalPexpr M.tagDefs M.extern M.file ρ pe1 = some (Vobject (OVinteger align)) ∧
      evalPexpr M.tagDefs M.extern M.file ρ pe2 = some (Vobject (OVinteger size)) ∧
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
theorem Step.jump_inv [LemFuel] {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {l : sym} {pes : List (generic_pexpr Unit sym)} {out : Config}
    (hj0 : jumpRedex? e = some (l, pes))
    (h : Step M (e, ρ, ctl, σ) out) :
    ∃ params cont vs ev0 evs, ρ = ev0 :: evs ∧
      lookupLabel (M.labelsAt ctl.proc) l = some (params, cont) ∧
      evalPexprs M.tagDefs M.extern M.file ρ pes = some vs ∧
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
  | bound_ctx hnj hnc hnn hnv hs => rw [jumpRedex?_bound, hnj] at hj0; cases hj0
  | bound_pure => simp [jumpRedex?] at hj0
  | unseq_ctx hv2 hcc hnj hnc hnv hs => rw [jumpRedex?_unseq_focus _ hnv hv2, hnj] at hj0; cases hj0
  | unseq_vals hcol => rw [jumpRedex?_unseq_vals] at hj0; cases hj0
  | bound_annot => simp [jumpRedex?] at hj0
  | neg_bound hn hss => rw [jumpRedex?_bound, jumpRedex?_none_of_negRedex?_some hn] at hj0; cases hj0
  | excluded_store h1 h2 h3 hmv hmem => simp [jumpRedex?] at hj0
  | excluded_store_eval hnv hv2 hv3 => simp [jumpRedex?] at hj0
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
theorem Step.run_of_jumpRedex [LemFuel] {M : MachineCtx} {e : CoreExpr} {l : sym}
    {pes : List (generic_pexpr Unit sym)}
    {params : List (sym × core_base_type)} {cont : CoreExpr} {vs : List value}
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {ctl : Ctl} {σ : Mem}
    (hj : jumpRedex? e = some (l, pes))
    (hl : lookupLabel (M.labelsAt ctl.proc) l = some (params, cont))
    (hvs : evalPexprs M.tagDefs M.extern M.file (ev0 :: evs) pes = some vs) :
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
def Step.CallOf [LemFuel] (M : MachineCtx) (e : CoreExpr) (fr : context → context)
    (ρ : EnvStack) (ctl : Ctl) (σ : Mem) (out : Config) : Prop :=
  ∃ ctx f pes params body vs, callRedex? e = some (ctx, f, pes) ∧
    evalPexprs M.tagDefs M.extern M.file ρ pes = some vs ∧
    lookupProc M.file M.extern f = some (params, body) ∧ params.length = vs.length ∧
    out = (body, procEnv params vs :: ρ, ctl.callPush (redexAnnots e) (fr ctx) f, σ)

/-- A `CallOf` successor never keeps the call stack. -/
theorem Step.CallOf.ne_same_κ [LemFuel] {M : MachineCtx} {e : CoreExpr} {fr : context → context}
    {ρ : EnvStack} {ctl ctl' : Ctl} {σ : Mem} {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    (h : Step.CallOf M e fr ρ ctl σ (e', ρ', ctl', σ')) (hκ : ctl'.κ = ctl.κ) : False := by
  obtain ⟨_, _, _, _, _, _, -, -, -, -, hout⟩ := h
  have := congrArg (fun c : Config => c.2.2.1.κ) hout
  simp at this
  rw [this] at hκ
  exact absurd hκ (by simp)

theorem Step.CallOf.ne_upd [LemFuel] {M : MachineCtx} {e : CoreExpr} {fr : context → context}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    {a : List annot}
    (h : Step.CallOf M e fr ρ ctl σ (e', ρ', ctl.upd a, σ')) : False :=
  h.ne_same_κ rfl

/-- A `CallOf` witness names a call redex of `e`. -/
theorem Step.CallOf.callRedex?_some [LemFuel] {M : MachineCtx} {e : CoreExpr} {fr : context → context}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (h : Step.CallOf M e fr ρ ctl σ out) :
    ∃ ctx f pes, callRedex? e = some (ctx, f, pes) := by
  obtain ⟨ctx, f, pes, _, _, _, hc, -⟩ := h
  exact ⟨ctx, f, pes, hc⟩

/-- The call rule seen from a frame: `Step.call` at the framed node IS
    `CallOf` of the body (the frame's context is the redex's context
    under the frame; the redex node is the body's). -/
theorem Step.callOf_of_call_sseq [LemFuel] {M : MachineCtx} {a : List annot} {pat : pattern}
    {e1 e2 : CoreExpr} {ctx : context} {f : sym} {pes : List (generic_pexpr Unit sym)}
    {params : List (sym × core_base_type)} {body : CoreExpr} {vs : List value}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    (hc : callRedex? (Expr a (Esseq pat e1 e2)) = some (ctx, f, pes))
    (hvs : evalPexprs M.tagDefs M.extern M.file ρ pes = some vs)
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
theorem Step.sseq_inv [LemFuel] {M : MachineCtx} {a : List annot} {pat : pattern}
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
        evalPexprs M.tagDefs M.extern M.file ρ pes = some vs ∧
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

theorem Step.callOf_of_call_wseq [LemFuel] {M : MachineCtx} {a : List annot} {pat : pattern}
    {e1 e2 : CoreExpr} {ctx : context} {f : sym} {pes : List (generic_pexpr Unit sym)}
    {params : List (sym × core_base_type)} {body : CoreExpr} {vs : List value}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    (hc : callRedex? (Expr a (Ewseq pat e1 e2)) = some (ctx, f, pes))
    (hvs : evalPexprs M.tagDefs M.extern M.file ρ pes = some vs)
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
theorem Step.wseq_inv [LemFuel] {M : MachineCtx} {a : List annot} {pat : pattern}
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
        evalPexprs M.tagDefs M.extern M.file ρ pes = some vs ∧
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

theorem Step.callOf_of_call_annot [LemFuel] {M : MachineCtx} {a : List annot} {ds : List dyn_annotation}
    {b : CoreExpr} {ctx : context} {f : sym} {pes : List (generic_pexpr Unit sym)}
    {params : List (sym × core_base_type)} {body : CoreExpr} {vs : List value}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} (hg : annotRooted b = false)
    (hc : callRedex? (Expr a (Eannot ds b)) = some (ctx, f, pes))
    (hvs : evalPexprs M.tagDefs M.extern M.file ρ pes = some vs)
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
theorem Step.annot_inv [LemFuel] {M : MachineCtx} {a : List annot}
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
        evalPexprs M.tagDefs M.extern M.file ρ pes = some vs ∧
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

theorem Step.callOf_of_call_bound [LemFuel] {M : MachineCtx} {a : List annot}
    {b : CoreExpr} {ctx : context} {f : sym} {pes : List (generic_pexpr Unit sym)}
    {params : List (sym × core_base_type)} {body : CoreExpr} {vs : List value}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    (hc : callRedex? (Expr a (Ebound b)) = some (ctx, f, pes))
    (hvs : evalPexprs M.tagDefs M.extern M.file ρ pes = some vs)
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
theorem Step.bound_inv [LemFuel] {M : MachineCtx} {a : List annot} {b : CoreExpr}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (h : Step M (Expr a (Ebound b), ρ, ctl, σ) out) :
    (∃ b' ρ' ctl' σ', jumpRedex? b = none ∧ callRedex? b = none ∧ negRedex? b = none ∧
        toVal b = none ∧
        Step M (b, ρ, ctl, σ) (b', ρ', ctl', σ') ∧
        out = (Expr a (Ebound b'), ρ', ctl', σ')) ∨
    (∃ a1 b1 v, b = ofValA (.pure a1 b1 v) ∧ out = (ofValA (.pure a1 b1 v), ρ, ctl.upd a, σ)) ∨
    (∃ a1 a2 b1 ds v, b = ofValA (.annot a1 a2 b1 ds v) ∧
        out = (ofValA (.pure a2 b1 v), ρ, ctl.upd a, σ)) ∨
    (∃ l pes params cont vs ev0 evs, jumpRedex? b = some (l, pes) ∧
        ρ = ev0 :: evs ∧ lookupLabel (M.labelsAt ctl.proc) l = some (params, cont) ∧
        evalPexprs M.tagDefs M.extern M.file ρ pes = some vs ∧
        out = (cont, bindArgs params vs ρ, ctl.upd (redexAnnots b), σ)) ∨
    Step.CallOf M b (fun c => Cbound a c) ρ ctl σ out ∨
    (∃ ctxA a' act, negRedex? b = some (ctxA, a', act) ∧ break_at_sseq ctxA = none ∧
        out = (Expr a (Ebound (negRewrite ctl.sup.excl (fresh_given_int ctl.sup.sym) ctxA act)),
          ρ, (ctl.upd a').draw, σ)) := by
  cases h with
  | bound_ctx hnj hnc hnn hnv hs => exact .inl ⟨_, _, _, _, hnj, hnc, hnn, hnv, hs, rfl⟩
  | bound_pure => exact .inr (.inl ⟨_, _, _, rfl, rfl⟩)
  | bound_annot => exact .inr (.inr (.inl ⟨_, _, _, _, _, rfl, rfl⟩))
  | run hj hl hvs =>
    rw [jumpRedex?_bound] at hj
    refine .inr (.inr (.inr (.inl ⟨_, _, _, _, _, _, _, hj, rfl, hl, hvs, ?_⟩)))
    rw [redexAnnots_bound_of_nv _ (toVal_none_of_jumpRedex?_some hj)]
  | call hc hvs hf hlen =>
    exact .inr (.inr (.inr (.inr (.inl (Step.callOf_of_call_bound hc hvs hf hlen)))))
  | neg_bound hn hss => exact .inr (.inr (.inr (.inr (.inr ⟨_, _, _, hn, hss, rfl⟩))))

/-- The call rule seen from the `Cunseq` frame (E4). -/
theorem Step.callOf_of_call_unseq [LemFuel] {M : MachineCtx} {a : List annot}
    {es1 : List CoreExpr} {e : CoreExpr} {es2 : List CoreExpr}
    {ctx : context} {f : sym} {pes : List (generic_pexpr Unit sym)}
    {params : List (sym × core_base_type)} {body : CoreExpr} {vs : List value}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    (hnv : toVal e = none) (hv2 : valsOnly es2 = true)
    (hc : callRedex? (Expr a (Eunseq (es1 ++ e :: es2))) = some (ctx, f, pes))
    (hvs : evalPexprs M.tagDefs M.extern M.file ρ pes = some vs)
    (hf : lookupProc M.file M.extern f = some (params, body))
    (hlen : params.length = vs.length) :
    Step.CallOf M e (fun c => Cunseq a es1 c es2) ρ ctl σ
      (body, procEnv params vs :: ρ,
       ctl.callPush (redexAnnots (Expr a (Eunseq (es1 ++ e :: es2)))) ctx f, σ) := by
  rw [callRedex?_unseq_focus a hnv hv2, Option.map_eq_some_iff] at hc
  obtain ⟨⟨ctx1, f1, pes1⟩, hc1, hq⟩ := hc
  obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
    exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq,
      congrArg (fun q => q.2.2) hq⟩
  refine ⟨ctx1, f1, pes1, _, _, _, hc1, hvs, hf, hlen, ?_⟩
  rw [redexAnnots_unseq_focus a hnv hv2]

/-- Inversion at an `Eunseq` node (E4): a frame step of the FOCUSED
    component (the last reducible one — `focus_unique` identifies it with
    any other focus split), the completion at all values, THE GLOBAL JUMP
    (the search descends to the focus, frame discarded), or THE CALL of the
    focused component with the `Cunseq` frame CAPTURED. -/
theorem Step.unseq_inv [LemFuel] {M : MachineCtx} {a : List annot} {es : List CoreExpr}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (h : Step M (Expr a (Eunseq es), ρ, ctl, σ) out) :
    (∃ es1 e es2 e' ρ' ctl' σ', es = es1 ++ e :: es2 ∧ valsOnly es2 = true ∧
        ccallFreeList (es1 ++ es2) = true ∧
        jumpRedex? e = none ∧ callRedex? e = none ∧ toVal e = none ∧
        Step M (e, ρ, ctl, σ) (e', ρ', ctl', σ') ∧
        out = (Expr a (Eunseq (es1 ++ e' :: es2)), ρ', ctl', σ')) ∨
    (∃ ws fps cvals, es = ws.map ofValA ∧ collectUnseq ([], []) ws = some (fps, cvals) ∧
        out = (Expr a (Eannot fps (Expr [] (Epure (Pexpr [] () (PEval (Vtuple cvals)))))),
          ρ, ctl.upd a, σ)) ∨
    (∃ l pes params cont vs ev0 evs, jumpRedex? (Expr a (Eunseq es)) = some (l, pes) ∧
        ρ = ev0 :: evs ∧ lookupLabel (M.labelsAt ctl.proc) l = some (params, cont) ∧
        evalPexprs M.tagDefs M.extern M.file ρ pes = some vs ∧
        out = (cont, bindArgs params vs ρ, ctl.upd (redexAnnots (Expr a (Eunseq es))), σ)) ∨
    (∃ es1 e es2, es = es1 ++ e :: es2 ∧ toVal e = none ∧ valsOnly es2 = true ∧
        Step.CallOf M e (fun c => Cunseq a es1 c es2) ρ ctl σ out) := by
  cases h with
  | unseq_ctx hv2 hcc hnj hnc hnv hs =>
    exact .inl ⟨_, _, _, _, _, _, _, rfl, hv2, hcc, hnj, hnc, hnv, hs, rfl⟩
  | unseq_vals hcol => exact .inr (.inl ⟨_, _, _, rfl, hcol, rfl⟩)
  | run hj hl hvs => exact .inr (.inr (.inl ⟨_, _, _, _, _, _, _, hj, rfl, hl, hvs, rfl⟩))
  | call hc hvs hf hlen =>
    have hnvU : toVal (Expr a (Eunseq es)) = none := rfl
    cases hvo : valsOnly es with
    | true =>
      obtain ⟨ws, rfl⟩ := valsOnly_true_map hvo
      rw [callRedex?_unseq_vals] at hc
      cases hc
    | false =>
      obtain ⟨es1, e, es2, rfl, hnv, hv2⟩ := focus_exists hvo
      exact .inr (.inr (.inr ⟨es1, e, es2, rfl, hnv, hv2,
        Step.callOf_of_call_unseq hnv hv2 hc hvs hf hlen⟩))

/-- Inversion at an Esave node: either the entry TAU (value-shaped
    initializers) or the parameter-EVAL step. -/
theorem Step.save_inv [LemFuel] {M : MachineCtx} {a : List annot}
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
      evalPexprs M.tagDefs M.extern M.file ρ (saveParamPexprs ps) = some cvals ∧
      out = (Expr a (Esave sb (saveParamsWithValues ps cvals) body), ρ, ctl.upd a, σ)) := by
  cases h with
  | save hvals => exact .inl ⟨_, _, _, rfl, hvals, rfl⟩
  | save_eval hnv hvals => exact .inr ⟨_, hnv, hvals, rfl⟩
  | run hj hl hvs => simp [jumpRedex?] at hj
  | call hc hvs hf hlen => simp at hc

/-- Inversion at an Esave node with VALUE initializers: the entry TAU. -/
theorem Step.save_vals_inv [LemFuel] {M : MachineCtx} {a : List annot}
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
theorem Step.save_op_inv [LemFuel] {M : MachineCtx} {a : List annot}
    {sb : sym × core_base_type}
    {ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
    {body : CoreExpr} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config}
    (hnv : valueFromPexprs (saveParamPexprs ps) = none)
    (h : Step M (Expr a (Esave sb ps body), ρ, ctl, σ) out) :
    ∃ cvals, evalPexprs M.tagDefs M.extern M.file ρ (saveParamPexprs ps) = some cvals ∧
      out = (Expr a (Esave sb (saveParamsWithValues ps cvals) body), ρ, ctl.upd a, σ) := by
  rcases h.save_inv with ⟨_, _, _, _, hvals, _⟩ | ⟨cvals, _, hvals, hout⟩
  · rw [hnv] at hvals; cases hvals
  · exact ⟨cvals, hvals, hout⟩

/-- Inversion at an Eif node. -/
theorem Step.if_inv [LemFuel] {M : MachineCtx} {a : List annot}
    {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (h : Step M (Expr a (Eif g e2 e3), ρ, ctl, σ) out) :
    (evalPexpr M.tagDefs M.extern M.file ρ g = some Vtrue ∧ out = (e2, ρ, ctl.upd a, σ)) ∨
    (evalPexpr M.tagDefs M.extern M.file ρ g = some Vfalse ∧ out = (e3, ρ, ctl.upd a, σ)) := by
  cases h with
  | if_true hg => exact .inl ⟨hg, rfl⟩
  | if_false hg => exact .inr ⟨hg, rfl⟩
  | run hj hl hvs => simp [jumpRedex?] at hj
  | call hc hvs hf hlen => simp at hc

/-- Inversion at an Ecase node (E2: two arms — the substitution TAU at a
    value scrutinee, the EVAL round at a non-value one). -/
theorem Step.case_inv [LemFuel] {M : MachineCtx} {a : List annot}
    {pe : generic_pexpr Unit sym} {pats : List (pattern × CoreExpr)}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (h : Step M (Expr a (Ecase pe pats), ρ, ctl, σ) out) :
    (∃ cval e', valueFromPexpr pe = some cval ∧
      select_case subst_sym_expr cval pats = some e' ∧
      out = (e', ρ, ctl.upd a, σ)) ∨
    (∃ cval, valueFromPexpr pe = none ∧ evalPexpr M.tagDefs M.extern M.file ρ pe = some cval ∧
      out = (Expr a (Ecase (Pexpr [] () (PEval cval)) pats), ρ, ctl.upd a, σ)) := by
  cases h with
  | case_value hv hsel => exact .inl ⟨_, _, hv, hsel, rfl⟩
  | case_eval hnv hv => exact .inr ⟨_, hnv, hv, rfl⟩
  | run hj hl hvs => simp [jumpRedex?] at hj
  | call hc hvs hf hlen => simp at hc

/-- The value-scrutinee instance of `case_inv` (the pre-E2 statement). -/
theorem Step.case_value_inv [LemFuel] {M : MachineCtx} {a : List annot}
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
theorem Step.case_op_inv [LemFuel] {M : MachineCtx} {a : List annot}
    {pe : generic_pexpr Unit sym} {pats : List (pattern × CoreExpr)}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (hnv : valueFromPexpr pe = none)
    (h : Step M (Expr a (Ecase pe pats), ρ, ctl, σ) out) :
    ∃ cval, evalPexpr M.tagDefs M.extern M.file ρ pe = some cval ∧
      out = (Expr a (Ecase (Pexpr [] () (PEval cval)) pats), ρ, ctl.upd a, σ) := by
  rcases h.case_inv with ⟨cval, e', hv, -, -⟩ | ⟨cval, -, hv, hout⟩
  · rw [hnv] at hv; cases hv
  · exact ⟨cval, hv, hout⟩

/-- Inversion at an Epure node (S4): the big-step PURE evaluation. -/
theorem Step.pure_inv [LemFuel] {M : MachineCtx} {a : List annot}
    {pe : generic_pexpr Unit sym} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config}
    (hnv : valueFromPexpr pe = none)
    (h : Step M (Expr a (Epure pe), ρ, ctl, σ) out) :
    ∃ v, valueFromPexpr pe = none ∧ evalPexpr M.tagDefs M.extern M.file ρ pe = some v ∧
      out = (Expr a (Epure (Pexpr [] () (PEval v))), ρ, ctl.upd a, σ) := by
  cases h with
  | pure_eval hnv hv => exact ⟨_, hnv, hv, rfl⟩
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | ret => rw [valueFromPexpr_val] at hnv; cases hnv

/-- Inversion at a positive load whose pointer operand is NOT a
    value (S4): the ACTION_EVAL step. -/
theorem Step.load_op_inv [LemFuel] {M : MachineCtx} {a : List annot}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pe2 : generic_pexpr Unit sym} {mo : memory_order}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (hnv2 : valueFromPexpr pe2 = none)
    (h : Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Load0 (Pexpr [] () (PEval (Vctype ty))) pe2 mo)))), ρ, ctl, σ) out) :
    ∃ pv, evalPexpr M.tagDefs M.extern M.file ρ pe2 = some (Vobject (OVpointer pv)) ∧
      out = (Expr a (Eaction (Paction polarity.Pos (Action loc ann
        (Load0 (Pexpr [] () (PEval (Vctype ty)))
               (Pexpr [] () (PEval (Vobject (OVpointer pv)))) mo)))), ρ, ctl.upd a, σ) := by
  cases h with
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | load h1 h2 hmem => rw [hnv2] at h2; cases h2
  | load_eval hnv2' hv2 => exact ⟨_, hv2, rfl⟩

/-- Inversion at the pointer-equality memop with VALUE operands. -/
theorem Step.memop_ptreq_inv [LemFuel] {M : MachineCtx} {a : List annot}
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
theorem Step.memop_vals_inv [LemFuel] {M : MachineCtx} {a : List annot} {v1 v2 : value}
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
theorem Step.memop_op_inv [LemFuel] {M : MachineCtx} {a : List annot} {mop : memop}
    {pe1 pe2 : generic_pexpr Unit sym}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (h : Step M (Expr a (Ememop mop [pe1, pe2]), ρ, ctl, σ) out) :
    ∃ v1 v2, evalPexpr M.tagDefs M.extern M.file ρ pe1 = some v1 ∧ evalPexpr M.tagDefs M.extern M.file ρ pe2 = some v2 ∧
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
theorem Step.store_op_inv [LemFuel] {M : MachineCtx} {a : List annot}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
    {ty : ctype} {pe2 pe3 : generic_pexpr Unit sym} {mo : memory_order}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (hnv : valueFromPexprs [pe2, pe3] = none)
    (h : Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
        (Store0 lk (Pexpr [] () (PEval (Vctype ty))) pe2 pe3 mo)))), ρ, ctl, σ)
      out) :
    ∃ pv cv, evalPexpr M.tagDefs M.extern M.file ρ pe2 = some (Vobject (OVpointer pv)) ∧
      evalPexpr M.tagDefs M.extern M.file ρ pe3 = some cv ∧
      out = (Expr a (Eaction (Paction polarity.Pos (Action loc ann
        (Store0 lk (Pexpr [] () (PEval (Vctype ty)))
                (Pexpr [] () (PEval (Vobject (OVpointer pv))))
                (Pexpr [] () (PEval cv)) mo)))), ρ, ctl.upd a, σ) := by
  cases h with
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | store h1 h2 h3 hmv hmem => rw [valueFromPexprs_pair, h2, h3] at hnv; cases hnv
  | store_eval hnv' hv2 hv3 => exact ⟨_, _, hv2, hv3, rfl⟩

/-- E5: inversion at an excluded store with evaluated operands: the step
    is `Step.excluded_store`, its successor determined by the memory
    operation (the negative dynamic annotation carries the exclusion id). -/
theorem Step.excluded_store_inv [LemFuel] {M : MachineCtx} {a : List annot} {n : Nat}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool} {ty : ctype}
    {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (h : Step M (Expr a (Eexcluded n (Action loc ann
            (Store0 lk (Pexpr [] () (PEval (Vctype ty)))
                       (Pexpr [] () (PEval (Vobject (OVpointer pv))))
                       (Pexpr [] () (PEval cv)) mo))), ρ, ctl, σ) out) :
    ∃ mv fp σ',
      memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv = some mv ∧
      applyMemM (CerbMem.storeM M.tagDefs loc ty lk pv mv) σ = some (fp, σ') ∧
      out = (Expr [] (Eannot [DA_neg n [] fp]
              (Expr [] (Epure (Pexpr [] () (PEval Vunit))))), ρ, ctl.upd a, σ') := by
  cases h with
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | excluded_store_eval hnv hv2 hv3 =>
    rw [valueFromPexprs_pair, valueFromPexpr_val, valueFromPexpr_val] at hnv
    cases hnv
  | excluded_store h1 h2 h3 hmv hmem =>
    rw [valueFromPexpr_val] at h1 h2 h3
    obtain rfl : ty = _ := by simpa using h1
    obtain rfl : pv = _ := by simpa using h2
    obtain rfl : cv = _ := by simpa using h3
    exact ⟨_, _, _, hmv, hmem, rfl⟩

/-- E5: inversion at an excluded store whose operands are not all values:
    the step is the ACTION_EVAL round `Step.excluded_store_eval`. -/
theorem Step.excluded_store_op_inv [LemFuel] {M : MachineCtx} {a : List annot} {n : Nat}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
    {ty : ctype} {pe2 pe3 : generic_pexpr Unit sym} {mo : memory_order}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (hnv : valueFromPexprs [pe2, pe3] = none)
    (h : Step M (Expr a (Eexcluded n (Action loc ann
        (Store0 lk (Pexpr [] () (PEval (Vctype ty))) pe2 pe3 mo))), ρ, ctl, σ)
      out) :
    ∃ pv cv, evalPexpr M.tagDefs M.extern M.file ρ pe2 = some (Vobject (OVpointer pv)) ∧
      evalPexpr M.tagDefs M.extern M.file ρ pe3 = some cv ∧
      out = (Expr a (Eexcluded n (Action loc ann
        (Store0 lk (Pexpr [] () (PEval (Vctype ty)))
                (Pexpr [] () (PEval (Vobject (OVpointer pv))))
                (Pexpr [] () (PEval cv)) mo))), ρ, ctl.upd a, σ) := by
  cases h with
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc
  | excluded_store h1 h2 h3 hmv hmem => rw [valueFromPexprs_pair, h2, h3] at hnv; cases hnv
  | excluded_store_eval hnv' hv2 hv3 => exact ⟨_, _, hv2, hv3, rfl⟩

/-- E5: a NEGATIVE action at the root has no mirror step of its own — the
    engine rewrites at the enclosing `bound` (`Step.neg_bound`), or panics
    without one (`NO_BOUND`, classified in Round.lean). -/
theorem Step.neg_root_elim [LemFuel] {M : MachineCtx} {a : List annot} {act : CoreAction}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (h : Step M (Expr a (Eaction (Paction polarity.Neg0 act)), ρ, ctl, σ) out) : False := by
  cases h with
  | run hj hl hvs => simp at hj
  | call hc hvs hf hlen => simp at hc

/-- E5: `nd(…)` at the root has no mirror step — the engine's round is the
    scheduler FORK (`Step_nd2`, classified `ShippedRefusal.fork`). -/
theorem Step.nd_root_elim [LemFuel] {M : MachineCtx} {a : List annot} {es : List CoreExpr}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (h : Step M (Expr a (End es), ρ, ctl, σ) out) : False := by
  cases h with
  | run hj hl hvs => simp [jumpRedex?] at hj
  | call hc hvs hf hlen => simp [callRedex?] at hc

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
    the entry control `procCtl p`, not through the context (C1). E5
    (slice 2): the run state's two supplies are NORMALISED to the entry
    control's (`procCtl p`'s `sup = default = ⟨0, 0⟩`) — the profile reads
    `rs` for its label registry only, and the supply floor the judgments
    read (`MachineCtx.runState`) must be the entry control's supply. -/
@[reducible] def procCtx (rs : core_run_state) : MachineCtx :=
  { spikeCtx with runState := { rs with sym_supply := 0, excluded_supply := 0 } }

/-- Field-projection equations for the two profile instances. -/
@[simp] theorem spikeCtx_tagDefs : spikeCtx.tagDefs = fmapEmpty := rfl
@[simp] theorem spikeCtx_extern : spikeCtx.extern = fmapEmpty := rfl
@[simp] theorem spikeCtx_runState : spikeCtx.runState = spikeRunState := rfl
@[simp] theorem procCtx_tagDefs (rs : core_run_state) :
    (procCtx rs).tagDefs = fmapEmpty := rfl
@[simp] theorem procCtx_extern (rs : core_run_state) :
    (procCtx rs).extern = fmapEmpty := rfl
@[simp] theorem procCtx_runState_labeled (rs : core_run_state) :
    (procCtx rs).runState.labeled = rs.labeled := rfl
@[simp] theorem procCtx_sym_supply (rs : core_run_state) :
    (procCtx rs).runState.sym_supply = 0 := rfl

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

/-! ### E3: the jump profile AT A FILE

The mirror evaluator reads the file object since E3 (a standard-library
call unfolds through `M.file.stdlib`), so a certified run's context must
carry the SAME file the driver runs: the production statements' file is
`prodFile e` (ProdEntry.lean), and the one-procedure lane ties the driver
state's `core_file` to the context's (`DriverDoneAt`'s `F`, ProdLoop.lean).
`procCtxF f rs` is the jump profile at the file `f`; `procCtx rs` is its
instance at the default file (the file-blind exhibits keep it; the
production statements run their derivations at `procCtxF (prodFile …)`). -/
@[reducible] def procCtxF (f : generic_file Unit core_run_annotation) (rs : core_run_state) :
    MachineCtx :=
  { spikeCtx with file := f, runState := { rs with sym_supply := 0, excluded_supply := 0 } }

@[simp] theorem procCtxF_tagDefs (f : generic_file Unit core_run_annotation) (rs : core_run_state) :
    (procCtxF f rs).tagDefs = fmapEmpty := rfl
@[simp] theorem procCtxF_extern (f : generic_file Unit core_run_annotation) (rs : core_run_state) :
    (procCtxF f rs).extern = fmapEmpty := rfl
@[simp] theorem procCtxF_runState_labeled (f : generic_file Unit core_run_annotation)
    (rs : core_run_state) : (procCtxF f rs).runState.labeled = rs.labeled := rfl
@[simp] theorem procCtxF_sym_supply (f : generic_file Unit core_run_annotation)
    (rs : core_run_state) : (procCtxF f rs).runState.sym_supply = 0 := rfl
@[simp] theorem procCtxF_file (f : generic_file Unit core_run_annotation) (rs : core_run_state) :
    (procCtxF f rs).file = f := rfl

/-- `procCtx_labels` at a file. -/
theorem procCtxF_labels {f : generic_file Unit core_run_annotation} {p : sym}
    {rs : core_run_state} {Q : LabelMap}
    (hQ : fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
      Lem_Basic_classes.ordCompare s1 s2) p rs.labeled = some Q) :
    (procCtxF f rs).labelsAt (procCtl p).proc = Q := by
  rw [MachineCtx.labelsAt_eq_of_proc (M := procCtxF f rs) (c := procCtl p) rfl,
    MachineCtx.resolveProc_of_extern_empty rfl]
  show (match fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
      Lem_Basic_classes.ordCompare s1 s2) p rs.labeled with
    | some Q => Q
    | none => fmapEmpty) = Q
  rw [hQ]

end CerberusHeapLang
