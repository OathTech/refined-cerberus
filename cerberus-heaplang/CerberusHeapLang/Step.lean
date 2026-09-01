/-
CerberusHeapLang.Step — the fragment's inductive small-step
relation, MIRRORING the engine over the engine's own generated Core
types.

STATUS: this relation is hand-written, grammar-keyed, and has ZERO
independent authority. Every rule carries a mirror-cite into the
engine (the cerberus-lean checkout pinned in
../scripts/semantics-pin.env; file:line references are into its
lean_frontend/generated/). The certification against the engine's
`step_ctx`/driver composite is Soundness.lean (`engine_complete` +
the context-undisturbed per-rule lemmas); the engine-facing meaning
of everything proved over Step lands through Adequacy.lean's
semantic triples. A wrong rule here can therefore only make
theorems unprovable, never make an exported engine statement false
— WITH the idiom-faithfulness caveat (2026-08-31 foundational
audit, F-09): that guarantee covers exactly the layers interior to
proofs (Step, the logic, iris-lean). It does NOT extend to the
statement-level specification idiom (drive/driveJ, dischargeStep,
the readout predicates) — a wrong definition THERE yields a true
but irrelevant theorem — and it is fail-open for COVERAGE: a
missing rule or cone case silently narrows what is provable
without falsifying anything (the realized instance: value-scrutinee
Ecase, below). The per-construct coverage authority is
docs/CAPABILITY_MANIFEST.md.

SCOPE (the mirrored fragment): pure values, Load0/Store0/Create0
actions, the PtrEq memop, strong sequencing `Esseq` (wildcard,
`Specified`-binder and plain-symbol-binder patterns),
`Esave`/`Eif`/value-scrutinee `Ecase`, the context-discarding
`Erun`, pure/operand evaluation, and the run-time `Eannot` residue
those produce. NB value-scrutinee `Ecase` is LOCAL RULE ONLY: it
has a mirror rule, a wps rule and a per-step engine equation
(`step_ctx_case_value`), but NO `FragJ` membership and NO adequacy
consumer — it is not adequacy-exportable (RED row in
docs/CAPABILITY_MANIFEST.md until Phase 1 exports it; 2026-08-31
foundational audit F-01). `Ewseq` is NOT included (three more rules and every
inversion lemma doubles — deliberately deferred, register in
README "Registered divergences"). All rules use the CANONICAL node
shapes (empty `List annot` lists, `()` at bty) that
`mk_value_e`/`mk_value_pe` (Core_aux.lean:302,645) and the
fragment's authored programs produce; the engine's redex patterns
accept arbitrary annotation lists in some positions (e.g.
one_step0's LETS-PURE, Core_reduction.lean:353) — Step takes the
canonical instances, so it is exact on the fragment cone and a
sub-relation elsewhere (recorded divergence D3,
docs/2026-08-30_spike-sliceA-notes.md).

The minimal surrounding context frozen out of the judgment:
tagDefs = fmapEmpty, extern = fmapEmpty, default file, tid 0. The
aid counter (driver_state.core_run_state0.aid_supply) never enters
the fragment's terms: positive non-excluded actions annotate with
`DA_pos [] fp` (step_action, Core_reduction.lean:424 Store0/Load0
arms — aid1 is unused in the continuation's dyn_annots), so Step
needs no aid index.

DESIGN NOTES (each mirrors a specific engine behavior):

1. THE ENVIRONMENT IS LIVE STATE. The engine's thread environment
   (`thread_state.env : List (Fmap sym value)`, Core_run_aux.lean:291)
   is part of the configuration: `Step : CoreExpr × EnvStack × Mem
   → …`. Wildcard-pattern betas return the env verbatim: the
   engine's `update_env` is the identity on a NONEMPTY env stack
   (Core_aux.lean:861-868, first arm) and a failwithI PANIC on an
   empty one — mirrored fail-closed as ABSENCE of a step: the beta
   rules fire only at cons-shaped envs (the panic-channel
   discipline: panics are excluded by WF shape, never absorbed).
   The congruence rules are stated env-GENERAL (a descent step's
   env update is thread-global) so the jump rule composes without
   restating them.

2. ACTION_EVAL PHRASING. The action rules are stated over
   EVALUATED-OPERAND PREMISES, not syntactic `PEval` patterns:
   `valueFromPexpr peᵢ = some vᵢ` (Core_aux.lean:472) — the
   engine's own request-path dispatch: step_action
   (Core_reduction.lean:424) issues the one-step ACTION_REQUEST
   exactly when `act_valueFromPexpr` succeeds on every operand, and
   `act_valueFromPexpr` (Core_reduction.lean:393) equals
   `valueFromPexpr` everywhere except the `PEconstrained` PANIC
   channel, which the `valueFromPexpr` premise excludes fail-closed
   (`valueFromPexpr (PEconstrained …) = none`, so the premise is
   unsatisfiable — no step where the engine panics). Non-value
   operands (e.g. `store(x, a+b)`) take the engine's separate
   ACTION_EVAL step first (`Step.load_eval`/`store_eval`/
   `memop_eval`); the canonical `PEval` instances discharge the
   premises by `rfl` (`valueFromPexpr_val`).

3. THE LABEL CONTEXT IS PART OF THE RUNTIME TUPLE. `CoreRt`/
   `CoreRVal` carry `lbl : LabelMap` — the CURRENT PROCEDURE's
   static label map (the engine's `labeled_continuations`,
   Core_run_aux.lean:187; the analog of Caesium's `f_code`,
   RefinedC lifting.v:1002). `Step` takes it as a leading parameter
   `Q`; steps preserve it by construction of `primStep` (Lang.lean)
   — the engine never writes `labeled` on the sequential path. The
   certification ties `Q` to `core_run_state.labeled` at the
   current procedure by the pure equation
   `fmapLookupBy ord p rs.labeled = some Q` with
   `current_proc_opt = some p` and the frozen `extern = fmapEmpty`
   (step_ctx's Erun arm resolves the proc through extern with
   identity fallback, Core_reduction.lean:484) — Soundness.lean's
   jump-profile lemmas.

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
   (Rules.lean `wp_sseq`, Wps.lean `wps_seq`).

5. Esave / Eif / Ecase are LOCAL rules in the engine's measured
   granularity: Esave entry is a pure TAU at value-shaped parameter
   pexprs (one_step0's Esave valueFromPexprs fast-path,
   Core_reduction.lean:353), binding the parameters into the env;
   Eif takes ONE engine step with a BIG-STEP guard
   (TAU_WITH_RUNSTATE over `full_eval_pexpr` — the mirror premise
   is the PURE evaluator `evalPexpr`, certified against the
   engine's evaluator in Soundness.lean; the non-boolean-guard
   failwithI PANIC channel is excluded because the rule fires only
   at `Vtrue`/`Vfalse` results); Ecase with a value scrutinee is a
   TAU into the substituted branch (`select_case`,
   Core_aux.lean:637; the no-match ILLTYPED channel is a refusal —
   absence of a premise; the PEconstrained-scrutinee PANIC is
   excluded by the `valueFromPexpr` premise). The Ecase EVAL arm
   (small-step scrutinee via `eval_pexpr1`) is NOT mirrored —
   registered extension (README "Registered divergences").

Design records (chronology, findings, alternatives priced):
docs/2026-08-30_spike-minilog-plan.md, docs/2026-08-30_spike-recon.md,
docs/2026-08-31_s0-probe-report.md, the dated slice notes.
-/
import Core_aux
import Core_run_aux
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

/-! ## The machine context (S1b — the unified configuration;
design record docs/2026-08-31_phase1-design-record.md §1)

`MachineCtx` names EVERY immutable component of an engine
configuration: the parameters of `step_ctx` (tagDefs, file, extern,
tid, parent), the non-(arena/env) fields of the thread state, and
the run state the discharge protocol threads (read-only under the
fragment — Erun reads `labeled` through it; per-step aid draws
remain per-step parameters, as in the driver). The live state stays
the `(CoreExpr × EnvStack × Mem)` triple. The old frozen profiles
(`spikeCtx`/`procCtx` below) are INSTANCES — one point of the
context space — not parts of the judgment. -/

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

/-- Every immutable component of an engine configuration (per-field
    engine slots and fragment reads: the design record §1 table). -/
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
    (the `envThread` precedent). -/
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

/-- The current procedure's registered label fiber, read from the
    context exactly as step_ctx's Erun arm reads it (two-level
    `labeled` lookup at the extern-resolved current proc). Lookup
    failure and the no-current-proc case collapse to the EMPTY map:
    the jump rule cannot fire there — the engine's failwithI panic
    channels are mirrored fail-closed as absence of a step. The old
    `Q : LabelMap` index and its `LabeledAt` tie hypothesis are
    subsumed: the label map is DERIVED, not carried. -/
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

end MachineCtx

/-! ## The runtime tuple (S1: env is live state; S1b: + the machine
context — the unified configuration; the S3 label-map slot was the
`labels` projection of it) -/

/-- The runtime expression tuple: Core expression + live environment
    stack (thread_state's `arena` and `env` components) + the machine
    context (every immutable the fragment reads, carried read-only in
    the tuple; steps preserve it by construction of `primStep` —
    the engine writes no context component on the sequential path). -/
structure CoreRt where
  e : CoreExpr
  ρ : EnvStack
  M : MachineCtx

/-- Values carry the final env and the (unchanged) machine context
    (exported posts may project both away). -/
structure CoreRVal where
  w : SpikeVal
  ρ : EnvStack
  M : MachineCtx

/-- The delivered engine value of a runtime value (annotations and
    env erased — the D1 readout). -/
def CoreRVal.val (v : CoreRVal) : value := v.w.val

/-- Annotation-merge on runtime values: componentwise `SpikeVal.merge`
    (the env and label map ride — annotation reduction never touches
    them). -/
def CoreRVal.merge (ds : List dyn_annotation) (v : CoreRVal) : CoreRVal :=
  ⟨SpikeVal.merge ds v.w, v.ρ, v.M⟩

@[simp] theorem CoreRVal.merge_mk (ds : List dyn_annotation) (w : SpikeVal)
    (ρ : EnvStack) (M : MachineCtx) :
    CoreRVal.merge ds ⟨w, ρ, M⟩ = ⟨SpikeVal.merge ds w, ρ, M⟩ := rfl

@[simp] theorem CoreRVal.merge_merge (ds ds' : List dyn_annotation)
    (v : CoreRVal) :
    CoreRVal.merge ds (CoreRVal.merge ds' v) = CoreRVal.merge (ds ++ ds') v := by
  cases v; simp [CoreRVal.merge]

@[simp] theorem CoreRVal.val_merge (ds : List dyn_annotation) (v : CoreRVal) :
    (CoreRVal.merge ds v).val = v.val := by
  cases v; simp [CoreRVal.merge, CoreRVal.val]

@[simp] theorem CoreRVal.ρ_merge (ds : List dyn_annotation) (v : CoreRVal) :
    (CoreRVal.merge ds v).ρ = v.ρ := by
  cases v; rfl

/-- Componentwise value test (Language-side `toVal`). -/
def toValRt (r : CoreRt) : Option CoreRVal :=
  (toVal r.e).map fun w => ⟨w, r.ρ, r.M⟩

/-- Componentwise value injection (Language-side `ofVal`). -/
def ofValRt (v : CoreRVal) : CoreRt := ⟨ofVal v.w, v.ρ, v.M⟩

@[simp] theorem toValRt_mk (e : CoreExpr) (ρ : EnvStack) (M : MachineCtx) :
    toValRt ⟨e, ρ, M⟩ = (toVal e).map fun w => ⟨w, ρ, M⟩ := rfl

@[simp] theorem ofValRt_mk (w : SpikeVal) (ρ : EnvStack) (M : MachineCtx) :
    ofValRt ⟨w, ρ, M⟩ = ⟨ofVal w, ρ, M⟩ := rfl

@[simp] theorem toValRt_ofValRt (v : CoreRVal) : toValRt (ofValRt v) = some v := by
  obtain ⟨w, ρ, M⟩ := v
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
  | Expr _ (Eannot _ b) => if annotRooted b then none else jumpRedex? b
  | _ => none

@[simp] theorem jumpRedex?_run (a : List annot) (ra : core_run_annotation)
    (l : sym) (pes : List (generic_pexpr Unit sym)) :
    jumpRedex? (Expr a (Erun ra l pes)) = some (l, pes) := rfl

@[simp] theorem jumpRedex?_sseq (a : List annot) (pat : pattern)
    (e1 e2 : CoreExpr) :
    jumpRedex? (Expr a (Esseq pat e1 e2)) = jumpRedex? e1 := rfl

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
    degenerate pointers, where both compute the same value); any
    other operand shapes are fail-closed `none` (the engine's arm
    there is the Illformed_program channel — no mirror step). S4:
    the pointer-arithmetic extension the array exhibit needs. -/
def evalArrayShift (ty : ctype) : value → value → Option value
  | Vobject (OVpointer pv), Vobject (OVinteger iv) =>
      some (Vobject (OVpointer (CerbMem.arrayShiftPtrval pv ty iv)))
  | _, _ => none

/-- The pure evaluator (fragment operands; partial, fail-closed).
    S1b′: EXTERN IS THREADED — the engine resolves EVERY `PEsym`
    through the extern indirection with identity fallback
    (Core_eval.lean:142, the `let sym1 := match fmapLookupBy … ` of
    the PEsym arm); the S1a probe found the old extern-free evaluator
    pinned the whole bridge tower at `extern = fmapEmpty` (design
    record §5.2). The lookup-failure proc-pointer fallback channel
    (`file1.funs`) is fail-closed absence, as before. -/
def evalPexpr (ext : Fmap sym sym) (ρ : EnvStack) :
    generic_pexpr Unit sym → Option value
  | Pexpr _ _ (PEval v) => some v
  | Pexpr _ _ (PEsym x) => lookup_env (resolveExtern ext x) ρ
  | Pexpr _ _ (PEop op pe1 pe2) => do
      let v1 ← evalPexpr ext ρ pe1
      let v2 ← evalPexpr ext ρ pe2
      evalBinop op v1 v2
  | Pexpr _ _ (PEarray_shift pe1 ty pe2) => do
      let v1 ← evalPexpr ext ρ pe1
      let v2 ← evalPexpr ext ρ pe2
      evalArrayShift ty v1 v2
  | _ => none

@[simp] theorem evalPexpr_val (ext : Fmap sym sym) (ρ : EnvStack)
    (a : List annot) (v : value) :
    evalPexpr ext ρ (Pexpr a () (PEval v)) = some v := rfl

@[simp] theorem evalPexpr_sym (ext : Fmap sym sym) (ρ : EnvStack)
    (a : List annot) (x : sym) :
    evalPexpr ext ρ (Pexpr a () (PEsym x)) =
      lookup_env (resolveExtern ext x) ρ := rfl

/-- ... at the empty extern the indirection is the identity (the
    frozen profiles' instance; rfl). -/
@[simp] theorem evalPexpr_sym_empty (ρ : EnvStack) (a : List annot) (x : sym) :
    evalPexpr fmapEmpty ρ (Pexpr a () (PEsym x)) = lookup_env x ρ := rfl

theorem evalPexpr_op (ext : Fmap sym sym) (ρ : EnvStack) (a : List annot)
    (op : binop) (pe1 pe2 : generic_pexpr Unit sym) :
    evalPexpr ext ρ (Pexpr a () (PEop op pe1 pe2)) = (do
      let v1 ← evalPexpr ext ρ pe1
      let v2 ← evalPexpr ext ρ pe2
      evalBinop op v1 v2) := rfl

theorem evalPexpr_array_shift (ext : Fmap sym sym) (ρ : EnvStack)
    (a : List annot) (ty : ctype)
    (pe1 pe2 : generic_pexpr Unit sym) :
    evalPexpr ext ρ (Pexpr a () (PEarray_shift pe1 ty pe2)) = (do
      let v1 ← evalPexpr ext ρ pe1
      let v2 ← evalPexpr ext ρ pe2
      evalArrayShift ty v1 v2) := rfl

/-- All-or-nothing list evaluation (the engine's per-argument
    `full_eval_pexpr'` fold in step_ctx's Erun arm evaluates each
    argument against the ORIGINAL env — `full_eval_pexpr'` is closed
    over `th_st` — while threading the binding accumulator;
    `evalPexprs` mirrors the evaluation half). -/
def evalPexprs (ext : Fmap sym sym) (ρ : EnvStack) :
    List (generic_pexpr Unit sym) → Option (List value)
  | [] => some []
  | pe :: pes => do
      let v ← evalPexpr ext ρ pe
      let vs ← evalPexprs ext ρ pes
      pure (v :: vs)

@[simp] theorem evalPexprs_nil (ext : Fmap sym sym) (ρ : EnvStack) :
    evalPexprs ext ρ [] = some [] := rfl

theorem evalPexprs_cons (ext : Fmap sym sym) (ρ : EnvStack)
    (pe : generic_pexpr Unit sym)
    (pes : List (generic_pexpr Unit sym)) :
    evalPexprs ext ρ (pe :: pes) = (do
      let v ← evalPexpr ext ρ pe
      let vs ← evalPexprs ext ρ pes
      pure (v :: vs)) := rfl

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
    loc; fragment locations are not library locations (slice notes
    §D5). -/
inductive Step (M : MachineCtx) :
    CoreExpr × EnvStack × Mem → CoreExpr × EnvStack × Mem → Prop where
  /-- Positive strong store, evaluated operands (ACTION_EVAL
      phrasing — header note 2). Mirrors: step_action Store0 arm
      (Core_reduction.lean:424 — operand readout via
      act_valueFromPexpr, memValueFromValue at
      `Ctype [] (unatomic_ ty)`, request `StoreRequest2`), driver
      discharge `liftMem (CerbMem.storeM loc ty lk pv mv)`
      (Driver.lean:273), continuation
      `Expr [] (Eannot [DA_pos [] fp] (mk_value_e Vunit))` (is_excluded
      = none on the fragment's positive path). storeM: CerbMem.lean:1632.
      The env is unread and returned verbatim (the request path never
      touches thread env). -/
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
      Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Store0 lk pe1 pe2 pe3 mo)))), ρ, σ)
           (Expr [] (Eannot [DA_pos [] fp]
              (Expr [] (Epure (Pexpr [] () (PEval Vunit))))), ρ, σ')
  /-- Positive strong load, evaluated operands. Mirrors: step_action
      Load0 arm (Core_reduction.lean:424 — request `LoadRequest2`,
      continuation `Expr [] (Eannot [DA_pos [] fp] (mk_value_e
      (valueFromMemValue mval).2))`), driver discharge
      `liftMem (CerbMem.loadM loc ty pv)` (Driver.lean:273).
      loadM: CerbMem.lean:1586 (returns the state unchanged on the
      active path — σ' = σ is derivable, kept in applyMemM shape). -/
  | load {a : List annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {pe1 pe2 : generic_pexpr Unit sym}
      {ty : ctype} {pv : CerbMem.PointerValue} {mo : memory_order}
      {mval : CerbMem.MemValue} {fp : CerbMem.Footprint}
      {ρ : EnvStack} {σ σ' : Mem}
      (h1 : valueFromPexpr pe1 = some (Vctype ty))
      (h2 : valueFromPexpr pe2 = some (Vobject (OVpointer pv)))
      (hmem : applyMemM (CerbMem.loadM loc ty pv) σ = some ((fp, mval), σ')) :
      Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Load0 pe1 pe2 mo)))), ρ, σ)
           (Expr [] (Eannot [DA_pos [] fp]
              (Expr [] (Epure (Pexpr [] () (PEval
                (valueFromMemValue mval).2))))), ρ, σ')
  /-- Positive strong create (Extension D: cold-start programs create
      their own cells), evaluated operands. Mirrors: step_action
      Create arm (Core_reduction.lean:424 — value operands
      `(Vobject (OVinteger align), Vctype ty)` classify, no ILLTYPED
      arm for these shapes; request `CreateRequest2 pref align ty
      (get_with_address e_annots) none` with continuation
      `mk_value_e (Vobject (OVpointer ptrval))` — a BARE value, no
      Eannot residue), driver discharge `liftMem (CerbMem.allocateObject
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
      {pv : CerbMem.PointerValue} {ρ : EnvStack} {σ σ' : Mem}
      (h1 : valueFromPexpr pe1 = some (Vobject (OVinteger align)))
      (h2 : valueFromPexpr pe2 = some (Vctype ty))
      (hmem : applyMemM (CerbMem.allocateObject 0 pref align ty none none) σ =
        some (pv, σ')) :
      Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Create pe1 pe2 pref)))), ρ, σ)
           (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer pv))))), ρ, σ')
  /-- LETS-PURE at a wildcard pattern:
      `lets _ = v in E2 --> E2` (one_step0 Esseq bare-value arm,
      Core_reduction.lean:353 "reduction: LETS-PURE"). The env update
      `update_env (CaseBase (none,_))` is the identity on a NONEMPTY
      stack (Core_aux.lean:861-868, first arm) and a failwithI PANIC
      on an empty one — the cons shape is load-bearing (header note
      1): no step exists where the engine panics. -/
  | sseq_pure {a pa : List annot} {bty : core_base_type} {v : value}
      {e2 : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
      {σ : Mem} :
      Step M (Expr a (Esseq (Pattern pa (CaseBase (none, bty)))
              (ofVal (.pure v)) e2), ev0 :: evs, σ)
           (e2, ev0 :: evs, σ)
  /-- LETS-ANNOT at a wildcard pattern:
      `lets _ = {A}v in E2 --> {A} E2` (one_step0 Esseq Eannot arm,
      Core_reduction.lean:353 "reduction: LETS-ANNOT" — the engine
      writes the result node annots as `[]` verbatim). This is the
      R-i residue entering the continuation. Same env discipline as
      LETS-PURE. -/
  | sseq_annot {a pa : List annot} {bty : core_base_type}
      {ds : List dyn_annotation} {v : value} {e2 : CoreExpr}
      {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {σ : Mem} :
      Step M (Expr a (Esseq (Pattern pa (CaseBase (none, bty)))
              (ofVal (.annot ds v)) e2), ev0 :: evs, σ)
           (Expr [] (Eannot ds e2), ev0 :: evs, σ)
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
      {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {σ : Mem} :
      Step M (Expr a (Esseq (specPat pa pb x bty)
              (ofVal (.pure (Vloaded (LVspecified ov)))) e2), ev0 :: evs, σ)
           (e2, update_env (specPat pa pb x bty) (Vloaded (LVspecified ov))
              (ev0 :: evs), σ)
  /-- LETS-ANNOT at the Specified-binder pattern:
      `lets Specified(x) = {A}Specified(ov) in E2 --> {A} E2`, same
      binding discipline (one_step0 Esseq Eannot arm, "reduction:
      LETS-ANNOT" — the engine binds the BARE value; the annotations
      flow to the continuation wrapper). -/
  | sseq_spec_annot {a pa pb : List annot} {x : sym} {bty : core_base_type}
      {ds : List dyn_annotation} {ov : object_value} {e2 : CoreExpr}
      {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {σ : Mem} :
      Step M (Expr a (Esseq (specPat pa pb x bty)
              (ofVal (.annot ds (Vloaded (LVspecified ov)))) e2), ev0 :: evs, σ)
           (Expr [] (Eannot ds e2),
            update_env (specPat pa pb x bty) (Vloaded (LVspecified ov))
              (ev0 :: evs), σ)
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
      {ρ : EnvStack} {σ : Mem}
      (hnv : valueFromPexpr pe = none)
      (hv : evalPexpr M.extern ρ pe = some v) :
      Step M (Expr a (Epure pe), ρ, σ)
           (Expr a (Epure (Pexpr [] () (PEval v))), ρ, σ)
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
      {mo : memory_order} {ρ : EnvStack} {σ : Mem}
      (hnv2 : valueFromPexpr pe2 = none)
      (hv2 : evalPexpr M.extern ρ pe2 = some (Vobject (OVpointer pv))) :
      Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Load0 (Pexpr [] () (PEval (Vctype ty))) pe2 mo)))), ρ, σ)
           (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Load0 (Pexpr [] () (PEval (Vctype ty)))
                     (Pexpr [] () (PEval (Vobject (OVpointer pv)))) mo)))),
            ρ, σ)
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
      `Step.run` alone. -/
  | sseq_ctx {a : List annot} {pat : pattern} {e1 e1' e2 : CoreExpr}
      {ρ ρ' : EnvStack} {σ σ' : Mem}
      (hnj : jumpRedex? e1 = none) :
      Step M (e1, ρ, σ) (e1', ρ', σ') →
      Step M (Expr a (Esseq pat e1 e2), ρ, σ) (Expr a (Esseq pat e1' e2), ρ', σ')
  /-- Reduction under a dyn-annotation frame. Mirrors get_ctx's plain
      `Eannot xs e` arm (Cannot-descent — taken only when e is NOT
      itself Eannot-rooted, because the double-annot arm precedes it;
      Core_reduction.lean:375) + apply_ctx's Cannot rebuild
      (Core_reduction.lean:389). The guard is load-bearing: without
      it this rule would race the ANNOTS merge, which the engine
      never does. -/
  | annot_ctx {a : List annot} {ds : List dyn_annotation} {b b' : CoreExpr}
      {ρ ρ' : EnvStack} {σ σ' : Mem}
      (hnj : jumpRedex? b = none) :
      annotRooted b = false →
      Step M (b, ρ, σ) (b', ρ', σ') →
      Step M (Expr a (Eannot ds b), ρ, σ) (Expr a (Eannot ds b'), ρ', σ')
  /-- ANNOTS merge: `{A_1} {A_2} E --> {A_1 ++ A_2} E` (one_step0
      Eannot arm, Core_reduction.lean:353 "reduction: ANNOTS";
      combine_dyn_annotations = (++), :305-306; get_ctx routes every
      double-annot root here, :375; the double-annot value is
      explicitly NOT irreducible, :293 first arm). Unconditional on
      the body, exactly as the engine; env untouched. -/
  | annot_merge {a1 a2 : List annot} {ds1 ds2 : List dyn_annotation}
      {b : CoreExpr} {ρ : EnvStack} {σ : Mem} :
      Step M (Expr a1 (Eannot ds1 (Expr a2 (Eannot ds2 b))), ρ, σ)
           (Expr (a1 ++ a2) (Eannot (ds1 ++ ds2) b), ρ, σ)
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
      {σ : Mem}
      (hj : jumpRedex? e = some (l, pes))
      (hl : lookupLabel M.labels l = some (params, cont))
      (hvs : evalPexprs M.extern (ev0 :: evs) pes = some vs) :
      Step M (e, ev0 :: evs, σ)
           (cont, bindArgs params vs (ev0 :: evs), σ)
  /-- Esave ENTRY at value-shaped parameter pexprs: one_step0's Esave
      TAU fast-path (Core_reduction.lean:353, "reduction: SAVE (tau
      part)") — the parameters bind into the env, the arena becomes
      the save body. Context-preserving (an ordinary redex under the
      spine). Non-value parameter pexprs take the engine's EVAL arm
      (small-step `eval_pexpr1` mapM) — not mirrored this slice
      (absence of a step; authored fragment saves carry value
      initializers). -/
  | save {a : List annot} {sb : sym × core_base_type}
      {ps : List (sym × ((core_base_type ×
        Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
      {body : CoreExpr} {cvals : List value}
      {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {σ : Mem}
      (hvals : valueFromPexprs (saveParamPexprs ps) = some cvals) :
      Step M (Expr a (Esave sb ps body), ev0 :: evs, σ)
           (body, bindSaveParams ps cvals (ev0 :: evs), σ)
  /-- Eif, true branch: ONE engine step with a BIG-STEP guard
      (one_step0's Eif TAU_WITH_RUNSTATE, Core_reduction.lean:353 —
      `full_eval_pexpr1 pe1` then dispatch on Vtrue/Vfalse; any other
      value is a failwithI PANIC, excluded by the premise). The
      mirror premise is the pure evaluator (header note 5). Env and
      state untouched. -/
  | if_true {a : List annot} {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
      {ρ : EnvStack} {σ : Mem}
      (hg : evalPexpr M.extern ρ g = some Vtrue) :
      Step M (Expr a (Eif g e2 e3), ρ, σ) (e2, ρ, σ)
  /-- Eif, false branch. -/
  | if_false {a : List annot} {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
      {ρ : EnvStack} {σ : Mem}
      (hg : evalPexpr M.extern ρ g = some Vfalse) :
      Step M (Expr a (Eif g e2 e3), ρ, σ) (e3, ρ, σ)
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
      {ρ : EnvStack} {σ : Mem}
      (hv : valueFromPexpr pe = some cval)
      (hsel : select_case subst_sym_expr cval pats = some e') :
      Step M (Expr a (Ecase pe pats), ρ, σ) (e', ρ, σ)
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
      {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {σ : Mem} :
      Step M (Expr a (Esseq (symPat pa x bty) (ofVal (.pure v)) e2), ev0 :: evs, σ)
           (e2, update_env (symPat pa x bty) v (ev0 :: evs), σ)
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
      {ρ : EnvStack} {σ σ' : Mem}
      (h1 : valueFromPexpr pe1 = some (Vobject (OVpointer pv1)))
      (h2 : valueFromPexpr pe2 = some (Vobject (OVpointer pv2)))
      (hmem : applyMemM (CerbMem.eqPtrval default pv1 pv2) σ = some (b, σ')) :
      Step M (Expr a (Ememop PtrEq [pe1, pe2]), ρ, σ)
           (Expr [] (Epure (Pexpr [] () (PEval (boolValue b)))), ρ, σ')
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
      {ρ : EnvStack} {σ : Mem}
      (hnv : valueFromPexprs [pe1, pe2] = none)
      (hv1 : evalPexpr M.extern ρ pe1 = some v1)
      (hv2 : evalPexpr M.extern ρ pe2 = some v2) :
      Step M (Expr a (Ememop mop [pe1, pe2]), ρ, σ)
           (Expr a (Ememop mop
             [Pexpr [] () (PEval v1), Pexpr [] () (PEval v2)]), ρ, σ)
  /-- ACTION_EVAL for a positive strong store with unevaluated
      pointer AND value operands (list-reverse phase A — the
      loop-carried interior store): ONE engine step BIG-STEP
      evaluating the operands (step_action's Store0 `_, _, _` arm,
      Core_reduction.lean:424 — `ACTION_EVAL "eval operands of
      Store"` over the three `full_eval_pexpr1` calls, wrapped by
      process_action's ACTION_EVAL arm; successor `Expr e_annots
      (wrap_act (Store0 is_locking (mk_value_pe cval1) (mk_value_pe
      cval2) (mk_value_pe cval3) mo1))`). The type operand is pinned
      at its canonical evaluated shape (its re-evaluation is the
      identity); pointer and value operands evaluate through the
      certified pure evaluator — the pointer to a POINTER value, so
      the successor is exactly the canonical store redex. The
      `Store0 … PEconstrained` failwithI pre-arm
      (Core_reduction.lean:424) is excluded by the evaluator premise
      (`evalPexpr (PEconstrained …) = none`). -/
  | store_eval {a : List annot} {loc : CerbLocation.Loc}
      {ann : core_run_annotation} {lk : Bool} {ty : ctype}
      {pe2 pe3 : generic_pexpr Unit sym} {pv : CerbMem.PointerValue}
      {cv : value} {mo : memory_order} {ρ : EnvStack} {σ : Mem}
      (hnv2 : valueFromPexpr pe2 = none)
      (hnv3 : valueFromPexpr pe3 = none)
      (hv2 : evalPexpr M.extern ρ pe2 = some (Vobject (OVpointer pv)))
      (hv3 : evalPexpr M.extern ρ pe3 = some cv) :
      Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Store0 lk (Pexpr [] () (PEval (Vctype ty))) pe2 pe3 mo)))), ρ, σ)
           (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Store0 lk (Pexpr [] () (PEval (Vctype ty)))
                      (Pexpr [] () (PEval (Vobject (OVpointer pv))))
                      (Pexpr [] () (PEval cv)) mo)))), ρ, σ)

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
    {ρ : EnvStack} {σ σ' : Mem}
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv = some mv)
    (hmem : applyMemM (CerbMem.storeM loc ty lk pv mv) σ = some (fp, σ')) :
    Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Store0 lk (Pexpr [] () (PEval (Vctype ty)))
                       (Pexpr [] () (PEval (Vobject (OVpointer pv))))
                       (Pexpr [] () (PEval cv)) mo)))), ρ, σ)
         (Expr [] (Eannot [DA_pos [] fp]
            (Expr [] (Epure (Pexpr [] () (PEval Vunit))))), ρ, σ') :=
  Step.store rfl rfl rfl hmv hmem

theorem Step.load_canonical {M : MachineCtx} {a : List annot}
    {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {ty : ctype} {pv : CerbMem.PointerValue}
    {mo : memory_order} {mval : CerbMem.MemValue} {fp : CerbMem.Footprint}
    {ρ : EnvStack} {σ σ' : Mem}
    (hmem : applyMemM (CerbMem.loadM loc ty pv) σ = some ((fp, mval), σ')) :
    Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Load0 (Pexpr [] () (PEval (Vctype ty)))
                   (Pexpr [] () (PEval (Vobject (OVpointer pv)))) mo)))), ρ, σ)
         (Expr [] (Eannot [DA_pos [] fp]
            (Expr [] (Epure (Pexpr [] () (PEval
              (valueFromMemValue mval).2))))), ρ, σ') :=
  Step.load rfl rfl hmem

theorem Step.create_canonical {M : MachineCtx} {a : List annot}
    {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {align : CerbMem.IntegerValue} {ty : ctype}
    {pref : prefix0} {pv : CerbMem.PointerValue} {ρ : EnvStack} {σ σ' : Mem}
    (hmem : applyMemM (CerbMem.allocateObject 0 pref align ty none none) σ =
      some (pv, σ')) :
    Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Create (Pexpr [] () (PEval (Vobject (OVinteger align))))
                    (Pexpr [] () (PEval (Vctype ty))) pref)))), ρ, σ)
         (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer pv))))), ρ, σ') :=
  Step.create rfl rfl hmem

/-- S3 RETIREMENT NOTE: phase-1's `Step.env_invariant(')` (no rule
    writes the env) is RETIRED as pre-declared (phase-1 notes §2
    item 6) — `Step.run` and `Step.save` rebind the environment. Its
    two survivors: `Step.env_cons` (cons-shapedness is preserved —
    what the sequencing proofs actually need at this stratum) and
    the FragP-scoped invariance in Soundness.lean
    (`Step.env_invariant_frag` — the old cone has no env-writing
    shapes). -/
theorem Step.env_cons' {M : MachineCtx} {c c' : CoreExpr × EnvStack × Mem}
    (h : Step M c c') :
    ∀ ev0 evs, c.2.1 = ev0 :: evs → ∃ ev0', c'.2.1 = ev0' :: evs := by
  induction h with
  | store h1 h2 h3 hmv hmem => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | load h1 h2 hmem => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | create h1 h2 hmem => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | sseq_pure => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | sseq_annot => exact fun ev0 evs hin => ⟨ev0, hin⟩
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
  | sseq_ctx hnj hs ih => exact ih
  | annot_ctx hnj hg hs ih => exact ih
  | annot_merge => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | run hj hl hvs =>
    intro ev0 evs hin
    obtain ⟨rfl, rfl⟩ := List.cons.inj hin
    exact bindArgs_cons _ _ _ _
  | save hvals =>
    intro ev0 evs hin
    obtain ⟨rfl, rfl⟩ := List.cons.inj hin
    exact bindSaveParams_cons _ _ _ _
  | if_true hg => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | if_false hg => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | case_value hv hsel => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | sseq_sym_pure =>
    intro ev0 evs hin
    obtain ⟨rfl, rfl⟩ := List.cons.inj hin
    exact ⟨_, update_env_cons ..⟩
  | memop_ptreq h1 h2 hmem => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | memop_eval hnv hv1 hv2 => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | store_eval hnv2 hnv3 hv2 hv3 => exact fun ev0 evs hin => ⟨ev0, hin⟩

theorem Step.env_cons {M : MachineCtx} {e : CoreExpr} {ev0 : Fmap sym value}
    {evs : List (Fmap sym value)} {σ : Mem}
    {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    (h : Step M (e, ev0 :: evs, σ) (e', ρ', σ')) :
    ∃ ev0', ρ' = ev0' :: evs :=
  h.env_cons' ev0 evs rfl

/-- Values do not step (the Language interface's `val_stuck`).
    Engine analogue: is_irreducible short-circuits both get_ctx and
    one_step0 (Core_reduction.lean:293,353,375). -/
theorem Step.val_elim {M : MachineCtx} {w : SpikeVal} {ρ : EnvStack} {σ : Mem}
    {out : CoreExpr × EnvStack × Mem}
    (h : Step M (ofVal w, ρ, σ) out) : False := by
  cases w with
  | pure v =>
    cases h with
    | run hj hl hvs => simp [ofVal] at hj
    | pure_eval hnv hv => rw [valueFromPexpr_val] at hnv; cases hnv
  | annot ds v =>
    cases h with
    | annot_ctx hnj hg hs =>
      cases hs with
      | run hj hl hvs => simp at hj
      | pure_eval hnv hv => rw [valueFromPexpr_val] at hnv; cases hnv
    | run hj hl hvs => simp [ofVal, jumpRedex?, annotRooted] at hj

theorem Step.toVal_none {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack} {σ : Mem}
    {out : CoreExpr × EnvStack × Mem}
    (h : Step M (e, ρ, σ) out) : toVal e = none := by
  cases hv : toVal e with
  | none => rfl
  | some w => exact absurd (ofVal_of_toVal hv ▸ h) (fun h => h.val_elim)

/-- Inversion at a store redex (canonical operand instance — the
    certified cone's shape): the step is unique and fully determined
    by the memM computation; the env is returned verbatim. -/
theorem Step.store_inv {M : MachineCtx} {a : List annot} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {lk : Bool} {ty : ctype}
    {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
    {ρ : EnvStack} {σ : Mem} {out : CoreExpr × EnvStack × Mem}
    (h : Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
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
  | store_eval hnv2 hnv3 hv2 hv3 => rw [valueFromPexpr_val] at hnv2; cases hnv2
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
    {mo : memory_order} {ρ : EnvStack} {σ : Mem}
    {out : CoreExpr × EnvStack × Mem}
    (h : Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Load0 (Pexpr [] () (PEval (Vctype ty)))
                   (Pexpr [] () (PEval (Vobject (OVpointer pv)))) mo)))), ρ, σ)
          out) :
    ∃ fp mval σ',
      applyMemM (CerbMem.loadM loc ty pv) σ = some ((fp, mval), σ') ∧
      out = (Expr [] (Eannot [DA_pos [] fp]
              (Expr [] (Epure (Pexpr [] () (PEval
                (valueFromMemValue mval).2))))), ρ, σ') := by
  cases h with
  | run hj hl hvs => simp at hj
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
    {pref : prefix0} {ρ : EnvStack} {σ : Mem}
    {out : CoreExpr × EnvStack × Mem}
    (h : Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Create (Pexpr [] () (PEval (Vobject (OVinteger align))))
                    (Pexpr [] () (PEval (Vctype ty))) pref)))), ρ, σ) out) :
    ∃ pv σ',
      applyMemM (CerbMem.allocateObject 0 pref align ty none none) σ =
        some (pv, σ') ∧
      out = (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer pv))))), ρ, σ') := by
  cases h with
  | run hj hl hvs => simp at hj
  | create h1 h2 hmem =>
    rw [valueFromPexpr_val] at h1 h2
    injection h1 with h1; injection h1 with h1; injection h1 with h1
    injection h2 with h2; injection h2 with h2
    subst h1 h2
    exact ⟨_, _, hmem, rfl⟩

/-! ### THE JUMP-REDEX INVERSION PAIR (probe Toy.lean
`step_jump_inv`/`step_of_jumpRedex`, now on Core — the semantic
cash-in of context-independence: at a jump redex EVERY step is THE
jump and its successor does not depend on the decomposition; the
congruence guards make this a one-level `cases`). -/

theorem Step.jump_inv {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack} {σ : Mem}
    {out : CoreExpr × EnvStack × Mem} {l : sym}
    {pes : List (generic_pexpr Unit sym)}
    (hj : jumpRedex? e = some (l, pes))
    (h : Step M (e, ρ, σ) out) :
    ∃ params cont vs ev0 evs, ρ = ev0 :: evs ∧
      lookupLabel M.labels l = some (params, cont) ∧
      evalPexprs M.extern ρ pes = some vs ∧
      out = (cont, bindArgs params vs ρ, σ) := by
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
  | sseq_pure => rw [jumpRedex?_sseq, jumpRedex?_ofVal] at hj; cases hj
  | sseq_annot => rw [jumpRedex?_sseq, jumpRedex?_ofVal] at hj; cases hj
  | sseq_spec_pure => rw [jumpRedex?_sseq, jumpRedex?_ofVal] at hj; cases hj
  | sseq_spec_annot => rw [jumpRedex?_sseq, jumpRedex?_ofVal] at hj; cases hj
  | pure_eval hnv hv => simp at hj
  | load_eval hnv2 hv2 => simp at hj
  | sseq_ctx hnj hs => rw [jumpRedex?_sseq, hnj] at hj; cases hj
  | annot_ctx hnj hg hs => rw [jumpRedex?_annot_of_not_root _ _ hg, hnj] at hj; cases hj
  | annot_merge =>
    rw [jumpRedex?_annot_of_root _ _ (by rfl)] at hj; cases hj
  | save hvals => simp [jumpRedex?] at hj
  | if_true hg => simp [jumpRedex?] at hj
  | if_false hg => simp [jumpRedex?] at hj
  | case_value hv hsel => simp [jumpRedex?] at hj
  | sseq_sym_pure => rw [jumpRedex?_sseq, jumpRedex?_ofVal] at hj; cases hj
  | memop_ptreq h1 h2 hmem => simp at hj
  | memop_eval hnv hv1 hv2 => simp at hj
  | store_eval hnv2 hnv3 hv2 hv3 => simp at hj

/-- Reducibility at a registered jump redex (the probe's
    `step_of_jumpRedex`). -/
theorem Step.run_of_jumpRedex {M : MachineCtx} {e : CoreExpr} {l : sym}
    {pes : List (generic_pexpr Unit sym)}
    {params : List (sym × core_base_type)} {cont : CoreExpr} {vs : List value}
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {σ : Mem}
    (hj : jumpRedex? e = some (l, pes))
    (hl : lookupLabel M.labels l = some (params, cont))
    (hvs : evalPexprs M.extern (ev0 :: evs) pes = some vs) :
    Step M (e, ev0 :: evs, σ) (cont, bindArgs params vs (ev0 :: evs), σ) :=
  Step.run hj hl hvs

/-- Inversion at an Esseq node (S3 form): a frame step of a
    NON-jump-redex e1, one of the two betas, or THE GLOBAL JUMP
    (frame discarded — the successor is e1's own jump successor).
    The frame case's `jumpRedex? e1 = none` is the S3 congruence
    guard surfacing; the jump disjunct is the readiness's "factor
    theorem gains one disjunct" at the Esseq node. -/
theorem Step.sseq_inv {M : MachineCtx} {a : List annot} {pat : pattern}
    {e1 e2 : CoreExpr}
    {ρ : EnvStack} {σ : Mem} {out : CoreExpr × EnvStack × Mem}
    (h : Step M (Expr a (Esseq pat e1 e2), ρ, σ) out) :
    (∃ e1' ρ' σ', jumpRedex? e1 = none ∧ Step M (e1, ρ, σ) (e1', ρ', σ') ∧
        out = (Expr a (Esseq pat e1' e2), ρ', σ')) ∨
    (∃ pa bty v ev0 evs, pat = Pattern pa (CaseBase (none, bty)) ∧
        e1 = ofVal (.pure v) ∧ ρ = ev0 :: evs ∧ out = (e2, ρ, σ)) ∨
    (∃ pa bty ds v ev0 evs, pat = Pattern pa (CaseBase (none, bty)) ∧
        e1 = ofVal (.annot ds v) ∧ ρ = ev0 :: evs ∧
        out = (Expr [] (Eannot ds e2), ρ, σ)) ∨
    (∃ l pes params cont vs ev0 evs, jumpRedex? e1 = some (l, pes) ∧
        ρ = ev0 :: evs ∧ lookupLabel M.labels l = some (params, cont) ∧
        evalPexprs M.extern ρ pes = some vs ∧
        out = (cont, bindArgs params vs ρ, σ)) ∨
    (∃ pa' pb' x bty' ov ev0 evs, pat = specPat pa' pb' x bty' ∧
        e1 = ofVal (.pure (Vloaded (LVspecified ov))) ∧ ρ = ev0 :: evs ∧
        out = (e2, update_env (specPat pa' pb' x bty')
          (Vloaded (LVspecified ov)) ρ, σ)) ∨
    (∃ pa' pb' x bty' ds ov ev0 evs, pat = specPat pa' pb' x bty' ∧
        e1 = ofVal (.annot ds (Vloaded (LVspecified ov))) ∧ ρ = ev0 :: evs ∧
        out = (Expr [] (Eannot ds e2), update_env (specPat pa' pb' x bty')
          (Vloaded (LVspecified ov)) ρ, σ)) ∨
    (∃ pa' x bty' v ev0 evs, pat = symPat pa' x bty' ∧
        e1 = ofVal (.pure v) ∧ ρ = ev0 :: evs ∧
        out = (e2, update_env (symPat pa' x bty') v ρ, σ)) := by
  cases h with
  | sseq_ctx hnj hs => exact .inl ⟨_, _, _, hnj, hs, rfl⟩
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
    exact .inr (.inr (.inr (.inr (.inr (.inr
      ⟨_, _, _, _, _, _, rfl, rfl, rfl, rfl⟩)))))

/-- Inversion at an Eannot node (S3 form): Cannot-descent of a
    non-jump-redex body, the ANNOTS merge, or the global jump
    through the Cannot frame. -/
theorem Step.annot_inv {M : MachineCtx} {a : List annot}
    {ds : List dyn_annotation}
    {b : CoreExpr} {ρ : EnvStack} {σ : Mem}
    {out : CoreExpr × EnvStack × Mem}
    (h : Step M (Expr a (Eannot ds b), ρ, σ) out) :
    (annotRooted b = false ∧ jumpRedex? b = none ∧
        ∃ b' ρ' σ', Step M (b, ρ, σ) (b', ρ', σ') ∧
        out = (Expr a (Eannot ds b'), ρ', σ')) ∨
    (∃ a2 ds2 c, b = Expr a2 (Eannot ds2 c) ∧
        out = (Expr (a ++ a2) (Eannot (ds ++ ds2) c), ρ, σ)) ∨
    (∃ l pes params cont vs ev0 evs, annotRooted b = false ∧
        jumpRedex? b = some (l, pes) ∧
        ρ = ev0 :: evs ∧ lookupLabel M.labels l = some (params, cont) ∧
        evalPexprs M.extern ρ pes = some vs ∧
        out = (cont, bindArgs params vs ρ, σ)) := by
  cases h with
  | annot_ctx hnj hg hs => exact .inl ⟨hg, hnj, _, _, _, hs, rfl⟩
  | annot_merge => exact .inr (.inl ⟨_, _, _, rfl, rfl⟩)
  | run hj hl hvs =>
    by_cases hr : annotRooted b = true
    · rw [jumpRedex?_annot_of_root _ _ hr] at hj; cases hj
    · have hr' : annotRooted b = false := by simpa using hr
      rw [jumpRedex?_annot_of_not_root _ _ hr'] at hj
      exact .inr (.inr ⟨_, _, _, _, _, _, _, hr', hj, rfl, hl, hvs, rfl⟩)

/-- Inversion at an Esave node: the entry TAU (value-shaped params). -/
theorem Step.save_inv {M : MachineCtx} {a : List annot}
    {sb : sym × core_base_type}
    {ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
    {body : CoreExpr} {ρ : EnvStack} {σ : Mem}
    {out : CoreExpr × EnvStack × Mem}
    (h : Step M (Expr a (Esave sb ps body), ρ, σ) out) :
    ∃ cvals ev0 evs, ρ = ev0 :: evs ∧
      valueFromPexprs (saveParamPexprs ps) = some cvals ∧
      out = (body, bindSaveParams ps cvals ρ, σ) := by
  cases h with
  | save hvals => exact ⟨_, _, _, rfl, hvals, rfl⟩
  | run hj hl hvs => simp [jumpRedex?] at hj

/-- Inversion at an Eif node: the guard evaluates to a boolean and
    the step selects the branch. -/
theorem Step.if_inv {M : MachineCtx} {a : List annot}
    {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
    {ρ : EnvStack} {σ : Mem} {out : CoreExpr × EnvStack × Mem}
    (h : Step M (Expr a (Eif g e2 e3), ρ, σ) out) :
    (evalPexpr M.extern ρ g = some Vtrue ∧ out = (e2, ρ, σ)) ∨
    (evalPexpr M.extern ρ g = some Vfalse ∧ out = (e3, ρ, σ)) := by
  cases h with
  | if_true hg => exact .inl ⟨hg, rfl⟩
  | if_false hg => exact .inr ⟨hg, rfl⟩
  | run hj hl hvs => simp [jumpRedex?] at hj

/-- Inversion at an Ecase node: the value-scrutinee selection TAU. -/
theorem Step.case_inv {M : MachineCtx} {a : List annot}
    {pe : generic_pexpr Unit sym} {pats : List (pattern × CoreExpr)}
    {ρ : EnvStack} {σ : Mem} {out : CoreExpr × EnvStack × Mem}
    (h : Step M (Expr a (Ecase pe pats), ρ, σ) out) :
    ∃ cval e', valueFromPexpr pe = some cval ∧
      select_case subst_sym_expr cval pats = some e' ∧
      out = (e', ρ, σ) := by
  cases h with
  | case_value hv hsel => exact ⟨_, _, hv, hsel, rfl⟩
  | run hj hl hvs => simp [jumpRedex?] at hj

/-- Inversion at an Epure node (S4): the big-step PURE evaluation. -/
theorem Step.pure_inv {M : MachineCtx} {a : List annot}
    {pe : generic_pexpr Unit sym} {ρ : EnvStack} {σ : Mem}
    {out : CoreExpr × EnvStack × Mem}
    (h : Step M (Expr a (Epure pe), ρ, σ) out) :
    ∃ v, valueFromPexpr pe = none ∧ evalPexpr M.extern ρ pe = some v ∧
      out = (Expr a (Epure (Pexpr [] () (PEval v))), ρ, σ) := by
  cases h with
  | pure_eval hnv hv => exact ⟨_, hnv, hv, rfl⟩
  | run hj hl hvs => simp at hj

/-- Inversion at a positive load whose pointer operand is NOT a
    value (S4): the ACTION_EVAL step. The operand's non-value shape
    is a side hypothesis (it discharges by `rfl`/`simp` at authored
    shapes) so the canonical load rule's arms refute. -/
theorem Step.load_op_inv {M : MachineCtx} {a : List annot}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pe2 : generic_pexpr Unit sym} {mo : memory_order}
    {ρ : EnvStack} {σ : Mem} {out : CoreExpr × EnvStack × Mem}
    (hnv2 : valueFromPexpr pe2 = none)
    (h : Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Load0 (Pexpr [] () (PEval (Vctype ty))) pe2 mo)))), ρ, σ) out) :
    ∃ pv, evalPexpr M.extern ρ pe2 = some (Vobject (OVpointer pv)) ∧
      out = (Expr a (Eaction (Paction polarity.Pos (Action loc ann
        (Load0 (Pexpr [] () (PEval (Vctype ty)))
               (Pexpr [] () (PEval (Vobject (OVpointer pv)))) mo)))), ρ, σ) := by
  cases h with
  | run hj hl hvs => simp at hj
  | load h1 h2 hmem => rw [hnv2] at h2; cases h2
  | load_eval hnv2' hv2 => exact ⟨_, hv2, rfl⟩

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

/-- Inversion at the pointer-equality memop with VALUE operands: the
    step is unique and fully determined by the memM computation. -/
theorem Step.memop_ptreq_inv {M : MachineCtx} {a : List annot}
    {pe1 pe2 : generic_pexpr Unit sym} {pv1 pv2 : CerbMem.PointerValue}
    {ρ : EnvStack} {σ : Mem} {out : CoreExpr × EnvStack × Mem}
    (h1 : valueFromPexpr pe1 = some (Vobject (OVpointer pv1)))
    (h2 : valueFromPexpr pe2 = some (Vobject (OVpointer pv2)))
    (h : Step M (Expr a (Ememop PtrEq [pe1, pe2]), ρ, σ) out) :
    ∃ b σ', applyMemM (CerbMem.eqPtrval default pv1 pv2) σ = some (b, σ') ∧
      out = (Expr [] (Epure (Pexpr [] () (PEval (boolValue b)))), ρ, σ') := by
  cases h with
  | run hj hl hvs => simp at hj
  | memop_ptreq h1' h2' hmem =>
    rw [h1] at h1'
    rw [h2] at h2'
    obtain rfl : pv1 = _ := by simpa using h1'
    obtain rfl : pv2 = _ := by simpa using h2'
    exact ⟨_, _, hmem, rfl⟩
  | memop_eval hnv hv1 hv2 =>
    rw [valueFromPexprs_pair, h1, h2] at hnv
    cases hnv

/-- Inversion at a two-operand memop with a NON-value operand list:
    the operand-evaluation step. -/
theorem Step.memop_op_inv {M : MachineCtx} {a : List annot} {mop : memop}
    {pe1 pe2 : generic_pexpr Unit sym}
    {ρ : EnvStack} {σ : Mem} {out : CoreExpr × EnvStack × Mem}
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (h : Step M (Expr a (Ememop mop [pe1, pe2]), ρ, σ) out) :
    ∃ v1 v2, evalPexpr M.extern ρ pe1 = some v1 ∧ evalPexpr M.extern ρ pe2 = some v2 ∧
      out = (Expr a (Ememop mop
        [Pexpr [] () (PEval v1), Pexpr [] () (PEval v2)]), ρ, σ) := by
  cases h with
  | run hj hl hvs => simp at hj
  | memop_ptreq h1 h2 hmem =>
    rw [valueFromPexprs_pair, h1, h2] at hnv
    cases hnv
  | memop_eval hnv' hv1 hv2 => exact ⟨_, _, hv1, hv2, rfl⟩

/-- Inversion at a store whose pointer operand is NOT a value: the
    ACTION_EVAL step (and its value operand is not a value either —
    the rule's shape). -/
theorem Step.store_op_inv {M : MachineCtx} {a : List annot}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
    {ty : ctype} {pe2 pe3 : generic_pexpr Unit sym} {mo : memory_order}
    {ρ : EnvStack} {σ : Mem} {out : CoreExpr × EnvStack × Mem}
    (hnv2 : valueFromPexpr pe2 = none)
    (h : Step M (Expr a (Eaction (Paction polarity.Pos (Action loc ann
        (Store0 lk (Pexpr [] () (PEval (Vctype ty))) pe2 pe3 mo)))), ρ, σ)
      out) :
    ∃ pv cv, evalPexpr M.extern ρ pe2 = some (Vobject (OVpointer pv)) ∧
      evalPexpr M.extern ρ pe3 = some cv ∧ valueFromPexpr pe3 = none ∧
      out = (Expr a (Eaction (Paction polarity.Pos (Action loc ann
        (Store0 lk (Pexpr [] () (PEval (Vctype ty)))
                (Pexpr [] () (PEval (Vobject (OVpointer pv))))
                (Pexpr [] () (PEval cv)) mo)))), ρ, σ) := by
  cases h with
  | run hj hl hvs => simp at hj
  | store h1 h2 h3 hmv hmem => rw [hnv2] at h2; cases h2
  | store_eval hnv2' hnv3 hv2 hv3 => exact ⟨_, _, hv2, hv3, hnv3, rfl⟩

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

/-! ## The frozen profiles as context instances

`spikeLbl` survives as the frozen EMPTY label map VALUE (the
`spikeEnv` precedent) — the label fiber of the straight-line launch
profile. The frozen profiles themselves are now `MachineCtx`
INSTANCES: `spikeCtx` (the straight-line/production launch context)
and `procCtx p rs` (the jump profile: proc-carrying thread over a
parameterized run state). No frozen constant remains inside any
judgment; exported statements pin the launch profile through these
instances only.

S1b RETIREMENT NOTE (design record §8.3, prune-don't-merge): the
phase-1 parallel cone `FragP` (and its `Decomp`-side machinery in
Soundness.lean) is DELETED — the ONE capability cone is `Frag`
(Soundness.lean; the migrated `FragJ` with value-scrutinee `Ecase`
joined). The straight-line TWO-SIDEDNESS sub-grammar that
`engine_complete` needs survives as `StraightFrag` (Soundness.lean),
which is NOT a capability cone (membership embeds via
`StraightFrag.toFrag`). -/

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

/-- The straight-line frozen profile as a context instance
    (tagDefs/extern empty, default file, tid 0, no parent, empty
    stack, no current procedure, frozen run state). -/
def spikeCtx : MachineCtx :=
  { tagDefs := fmapEmpty, file := spikeFile, extern := fmapEmpty,
    tid := 0, parent := none, stack := Stack_empty, errno := default,
    proc := none, execLoc := default, currentLoc := default,
    runState := spikeRunState }

/-- The jump profile (proc-carrying thread, parameterized run state)
    as a context instance. -/
def procCtx (p : sym) (rs : core_run_state) : MachineCtx :=
  { spikeCtx with proc := some p, runState := rs }

/-- A run-state-only variant of the spike context (the old `driveJ`
    profile: the drive loop itself reads no proc — only the
    discharge's run state differs). -/
def rsCtx (rs : core_run_state) : MachineCtx :=
  { spikeCtx with runState := rs }

/-- Field-projection equations for the frozen instances (rewriting
    aids: statements at the instances reduce to the old frozen
    constants). -/
@[simp] theorem spikeCtx_tagDefs : spikeCtx.tagDefs = fmapEmpty := rfl
@[simp] theorem spikeCtx_extern : spikeCtx.extern = fmapEmpty := rfl
@[simp] theorem spikeCtx_runState : spikeCtx.runState = spikeRunState := rfl
@[simp] theorem procCtx_tagDefs (p : sym) (rs : core_run_state) :
    (procCtx p rs).tagDefs = fmapEmpty := rfl
@[simp] theorem procCtx_extern (p : sym) (rs : core_run_state) :
    (procCtx p rs).extern = fmapEmpty := rfl
@[simp] theorem procCtx_runState (p : sym) (rs : core_run_state) :
    (procCtx p rs).runState = rs := rfl
@[simp] theorem rsCtx_extern (rs : core_run_state) :
    (rsCtx rs).extern = fmapEmpty := rfl
@[simp] theorem rsCtx_runState (rs : core_run_state) :
    (rsCtx rs).runState = rs := rfl

@[simp] theorem spikeCtx_labels : spikeCtx.labels = spikeLbl := rfl

@[simp] theorem rsCtx_labels (rs : core_run_state) :
    (rsCtx rs).labels = spikeLbl := rfl

theorem spikeCtx_wf : spikeCtx.SeqWF := ⟨rfl, rfl⟩

theorem procCtx_wf (p : sym) (rs : core_run_state) :
    (procCtx p rs).SeqWF := ⟨rfl, rfl⟩

theorem rsCtx_wf (rs : core_run_state) : (rsCtx rs).SeqWF := ⟨rfl, rfl⟩

/-- The jump profile's DERIVED label map at a successful two-level
    `labeled` read (the old `LabeledAt` tie, consumed): the fiber at
    the current procedure IS the context's label map. Stated in the
    engine's own lookup spelling (extern empty in the profile, so the
    proc redirect is the identity fallback). -/
theorem procCtx_labels {p : sym} {rs : core_run_state} {Q : LabelMap}
    (hQ : fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
      Lem_Basic_classes.ordCompare s1 s2) p rs.labeled = some Q) :
    (procCtx p rs).labels = Q := by
  rw [MachineCtx.labels_eq_of_proc (M := procCtx p rs) rfl,
    MachineCtx.resolveProc_of_extern_empty rfl]
  show (match fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
      Lem_Basic_classes.ordCompare s1 s2) p rs.labeled with
    | some Q => Q
    | none => fmapEmpty) = Q
  rw [hQ]

/-- At an empty derived label map nothing ever jumps: any step's
    subject has no REGISTERED jump redex (registration is what the
    jump rule needs). -/
theorem Step.jumpRedex?_none_of_empty {M : MachineCtx}
    (hlbl : M.labels = spikeLbl) {e : CoreExpr} {ρ : EnvStack}
    {σ : Mem} {out : CoreExpr × EnvStack × Mem}
    (h : Step M (e, ρ, σ) out) : jumpRedex? e = none := by
  cases hj : jumpRedex? e with
  | none => rfl
  | some lp =>
    obtain ⟨l, pes⟩ := lp
    obtain ⟨params, cont, vs, ev0, evs, -, hl, -, -⟩ := h.jump_inv hj
    rw [hlbl, lookupLabel_empty] at hl
    cases hl

/-- ... the `spikeCtx` instance (the straight-line lane's guard fact). -/
theorem Step.jumpRedex?_none_of_spikeCtx {e : CoreExpr} {ρ : EnvStack}
    {σ : Mem} {out : CoreExpr × EnvStack × Mem}
    (h : Step spikeCtx (e, ρ, σ) out) : jumpRedex? e = none :=
  h.jumpRedex?_none_of_empty rfl

end CerberusHeapLang
