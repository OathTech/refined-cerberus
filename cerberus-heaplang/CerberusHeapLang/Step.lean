/-
CerberusHeapLang.Step — spike artifact 1: the fragment's
inductive small-step over the REAL generated Core types.

STATUS: this relation is hand-written, grammar-keyed, and has ZERO
independent authority. Every rule carries a mirror-cite into the
engine (cerberus-lean pin 8fb380c9c, lean_frontend/generated/). The
certification against the engine's `step_ctx`/driver composite is
Soundness.lean (slice B: `engine_complete` + the context-undisturbed
per-rule lemmas); the engine-facing meaning of everything proved over
Step lands through Adequacy.lean's semantic triples.

Scope (the spike fragment, docs/2026-08-30_spike-minilog-plan.md):
pure values, Load0/Store0 actions (positive polarity, wildcard-bound
strong sequencing), Esseq, and the run-time Eannot residue those
produce. Ewseq is NOT included (it was not free: three more rules and
every inversion lemma doubles — recorded in the slice notes). All
rules use the CANONICAL node shapes (empty `List annot` lists, `()`
at bty) that `mk_value_e`/`mk_value_pe` (Core_aux.lean:302,645) and
the fragment's authored programs produce; the engine's redex
patterns accept arbitrary annotation lists in some positions
(e.g. one_step0's LETS-PURE, Core_reduction.lean:353) — Step takes
the canonical instances, so it is exact on the fragment cone and a
sub-relation elsewhere (recorded divergence, slice notes §D3).

The minimal surrounding context frozen out of the judgment (recon
§3.2): tagDefs = fmapEmpty, extern = fmapEmpty, default file, tid 0.
The aid counter (driver_state.core_run_state0.aid_supply) never
enters the fragment's terms: positive non-excluded actions annotate
with `DA_pos [] fp` (step_action, Core_reduction.lean:424
Store0/Load0 arms — aid1 is unused in the continuation's dyn_annots),
so Step needs no aid index.

PHASE-1 RESTRATIFICATION (S1, two-phase arc plan
docs/2026-08-31_two-phase-arc-plan.md; probe prescription
docs/2026-08-31_s0-probe-report.md §6):

1. THE ENVIRONMENT IS LIVE STATE. The engine's thread environment
   (`thread_state.env : List (Fmap sym value)`, Core_run_aux.lean:291)
   joins the configuration: `Step : CoreExpr × EnvStack × Mem → …`,
   the probe's componentwise `TRt`/`TRVal` pattern (StmtProbe/Toy.lean)
   minus the label-map component (S3's; the S3 landing is the
   frozen-context restatement against `core_run_state.labeled`).
   Every phase-1 rule RETURNS the env verbatim (`Step.env_invariant`):
   the fragment's patterns are wildcards, whose `update_env` is the
   identity on a NONEMPTY env stack (Core_aux.lean:861-868, first
   arm) and a failwithI PANIC on an empty one — mirrored fail-closed
   as ABSENCE of a step: the beta rules fire only at cons-shaped
   envs (the readiness review's panic-channel discipline: panics are
   excluded by WF shape, never absorbed). The congruence rules are
   stated env-GENERAL (a descent step's env update is thread-global)
   so the S3 jump rule extends without restating them.

2. ACTION_EVAL PHRASING. The action rules are stated over
   EVALUATED-OPERAND PREMISES, not syntactic `PEval` patterns:
   `valueFromPexpr peᵢ = some vᵢ` (Core_aux.lean:472) — the engine's
   own request-path dispatch: step_action (Core_reduction.lean:424)
   issues the one-step ACTION_REQUEST exactly when
   `act_valueFromPexpr` succeeds on every operand, and
   `act_valueFromPexpr` (Core_reduction.lean:393) equals
   `valueFromPexpr` everywhere except the `PEconstrained` PANIC
   channel, which the `valueFromPexpr` premise excludes fail-closed
   (`valueFromPexpr (PEconstrained …) = none`, so the premise is
   unsatisfiable — no step where the engine panics). Non-value
   operands (e.g. `store(x, a+b)`) take the engine's separate
   ACTION_EVAL step first; that step rule is phase 2's — these rule
   STATEMENTS already cover the post-eval shapes, so its arrival is
   additive. The canonical `PEval` instances discharge the premises
   by `rfl` (`valueFromPexpr_val`), so the certified fragment cone
   (Soundness.lean FragP — still canonical) is unchanged.

PHASE-2 S3 (jumps and branches — two-phase arc plan §Phase 2; probe
report §6 S3 prescription):

3. THE LABEL CONTEXT JOINS THE RUNTIME TUPLE. `CoreRt`/`CoreRVal`
   gain `lbl : LabelMap` — the CURRENT PROCEDURE's static label map
   (the engine's `labeled_continuations`, Core_run_aux.lean:187;
   Caesium `f_code` carried by `to_rtstmt rf`, lifting.v:1002; the
   probe's `TRt.fn`). `Step` takes it as a leading parameter `Q`;
   steps preserve it by construction of `primStep` (Lang.lean) —
   the engine never writes `labeled` on the sequential path. The
   certification ties `Q` to `core_run_state.labeled` at the
   current procedure by the pure equation
   `fmapLookupBy ord p rs.labeled = some Q` with
   `current_proc_opt = some p` and the frozen `extern = fmapEmpty`
   (step_ctx's Erun arm resolves the proc through extern with
   identity fallback, Core_reduction.lean:484) — Soundness.lean's
   jump-profile lemmas.

4. THE GLOBAL JUMP RULE. `Erun` DISCARDS its evaluation context
   (step_ctx's Erun arm returns `{th_st with env := env', arena :=
   cont_expr}` — no `apply_ctx ctx`; readiness §2.1 items 1-3). The
   mirror: `jumpRedex?` is the structural redex search through the
   Esseq/Eannot spine (the SYNTACTIC image of the context-discard —
   probe Toy.lean `jumpRedex?`), and `Step.run` fires at ANY
   configuration whose spine hole is a registered `Erun`, replacing
   the whole expression. The congruence rules `sseq_ctx`/`annot_ctx`
   are GUARDED by `jumpRedex? _ = none` so that a jump of a subterm
   is never framed (the engine's `K[run l pes] --> cont`, never
   `K[cont]`); this retires `Step.env_invariant` and the
   `Language.Context` instance for Esseq (both pre-declared —
   phase-1 notes §2 item 6, Lang.lean header).

5. Esave / Eif / Ecase are LOCAL rules in the engine's measured
   granularity (readiness §2.1 items 4-6): Esave entry is a pure
   TAU at value-shaped parameter pexprs (one_step0's Esave
   valueFromPexprs fast-path, Core_reduction.lean:353), binding the
   parameters into the env; Eif takes ONE engine step with a
   BIG-STEP guard (TAU_WITH_RUNSTATE over `full_eval_pexpr` — the
   mirror premise is the PURE evaluator `evalPexpr`, certified
   against the engine's evaluator in Soundness.lean; the
   non-boolean-guard failwithI PANIC channel is excluded because
   the rule fires only at `Vtrue`/`Vfalse` results); Ecase with a
   value scrutinee is a TAU into the substituted branch
   (`select_case`, Core_aux.lean:637; the no-match ILLTYPED channel
   is a refusal — absence of a premise; the PEconstrained-scrutinee
   PANIC is excluded by the `valueFromPexpr` premise). The Ecase
   EVAL arm (small-step scrutinee via `eval_pexpr1`) is measured
   but NOT mirrored this slice — recorded S4 item together with the
   substitution-closure lemmas its cone needs.
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

/-! ## The runtime tuple (S1: env is live state; S3: + the label map —
the probe's full `TRt`/`TRVal` pattern, StmtProbe/Toy.lean:113-124) -/

/-- The runtime expression tuple: Core expression + live environment
    stack (thread_state's `arena` and `env` components) + the static
    per-procedure label map (read-only context carried in the tuple —
    Caesium's `to_rtstmt rf`; the rest of the thread state stays
    frozen context — Soundness.lean). -/
structure CoreRt where
  e : CoreExpr
  ρ : EnvStack
  lbl : LabelMap

/-- Values carry the final env and the (unchanged) label map
    (exported posts may project both away — probe `TRVal`). -/
structure CoreRVal where
  w : SpikeVal
  ρ : EnvStack
  lbl : LabelMap

/-- The delivered engine value of a runtime value (annotations and
    env erased — the D1 readout). -/
def CoreRVal.val (v : CoreRVal) : value := v.w.val

/-- Annotation-merge on runtime values: componentwise `SpikeVal.merge`
    (the env and label map ride — annotation reduction never touches
    them). -/
def CoreRVal.merge (ds : List dyn_annotation) (v : CoreRVal) : CoreRVal :=
  ⟨SpikeVal.merge ds v.w, v.ρ, v.lbl⟩

@[simp] theorem CoreRVal.merge_mk (ds : List dyn_annotation) (w : SpikeVal)
    (ρ : EnvStack) (Q : LabelMap) :
    CoreRVal.merge ds ⟨w, ρ, Q⟩ = ⟨SpikeVal.merge ds w, ρ, Q⟩ := rfl

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
  (toVal r.e).map fun w => ⟨w, r.ρ, r.lbl⟩

/-- Componentwise value injection (Language-side `ofVal`). -/
def ofValRt (v : CoreRVal) : CoreRt := ⟨ofVal v.w, v.ρ, v.lbl⟩

@[simp] theorem toValRt_mk (e : CoreExpr) (ρ : EnvStack) (Q : LabelMap) :
    toValRt ⟨e, ρ, Q⟩ = (toVal e).map fun w => ⟨w, ρ, Q⟩ := rfl

@[simp] theorem ofValRt_mk (w : SpikeVal) (ρ : EnvStack) (Q : LabelMap) :
    ofValRt ⟨w, ρ, Q⟩ = ⟨ofVal w, ρ, Q⟩ := rfl

@[simp] theorem toValRt_ofValRt (v : CoreRVal) : toValRt (ofValRt v) = some v := by
  obtain ⟨w, ρ, Q⟩ := v
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

/-- The pure evaluator (fragment operands; partial, fail-closed). -/
def evalPexpr (ρ : EnvStack) : generic_pexpr Unit sym → Option value
  | Pexpr _ _ (PEval v) => some v
  | Pexpr _ _ (PEsym x) => lookup_env x ρ
  | Pexpr _ _ (PEop op pe1 pe2) => do
      let v1 ← evalPexpr ρ pe1
      let v2 ← evalPexpr ρ pe2
      evalBinop op v1 v2
  | _ => none

@[simp] theorem evalPexpr_val (ρ : EnvStack) (a : List annot) (v : value) :
    evalPexpr ρ (Pexpr a () (PEval v)) = some v := rfl

@[simp] theorem evalPexpr_sym (ρ : EnvStack) (a : List annot) (x : sym) :
    evalPexpr ρ (Pexpr a () (PEsym x)) = lookup_env x ρ := rfl

theorem evalPexpr_op (ρ : EnvStack) (a : List annot) (op : binop)
    (pe1 pe2 : generic_pexpr Unit sym) :
    evalPexpr ρ (Pexpr a () (PEop op pe1 pe2)) = (do
      let v1 ← evalPexpr ρ pe1
      let v2 ← evalPexpr ρ pe2
      evalBinop op v1 v2) := rfl

/-- All-or-nothing list evaluation (the engine's per-argument
    `full_eval_pexpr'` fold in step_ctx's Erun arm evaluates each
    argument against the ORIGINAL env — `full_eval_pexpr'` is closed
    over `th_st` — while threading the binding accumulator;
    `evalPexprs` mirrors the evaluation half). -/
def evalPexprs (ρ : EnvStack) : List (generic_pexpr Unit sym) →
    Option (List value)
  | [] => some []
  | pe :: pes => do
      let v ← evalPexpr ρ pe
      let vs ← evalPexprs ρ pes
      pure (v :: vs)

@[simp] theorem evalPexprs_nil (ρ : EnvStack) : evalPexprs ρ [] = some [] := rfl

theorem evalPexprs_cons (ρ : EnvStack) (pe : generic_pexpr Unit sym)
    (pes : List (generic_pexpr Unit sym)) :
    evalPexprs ρ (pe :: pes) = (do
      let v ← evalPexpr ρ pe
      let vs ← evalPexprs ρ pes
      pure (v :: vs)) := rfl

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
inductive Step (Q : LabelMap) :
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
      (hmv : memValueFromValue fmapEmpty (Ctype [] (unatomic_ ty)) cv = some mv)
      (hmem : applyMemM (CerbMem.storeM loc ty lk pv mv) σ = some (fp, σ')) :
      Step Q (Expr a (Eaction (Paction polarity.Pos (Action loc ann
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
      Step Q (Expr a (Eaction (Paction polarity.Pos (Action loc ann
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
      Step Q (Expr a (Eaction (Paction polarity.Pos (Action loc ann
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
      Step Q (Expr a (Esseq (Pattern pa (CaseBase (none, bty)))
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
      Step Q (Expr a (Esseq (Pattern pa (CaseBase (none, bty)))
              (ofVal (.annot ds v)) e2), ev0 :: evs, σ)
           (Expr [] (Eannot ds e2), ev0 :: evs, σ)
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
      Step Q (e1, ρ, σ) (e1', ρ', σ') →
      Step Q (Expr a (Esseq pat e1 e2), ρ, σ) (Expr a (Esseq pat e1' e2), ρ', σ')
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
      Step Q (b, ρ, σ) (b', ρ', σ') →
      Step Q (Expr a (Eannot ds b), ρ, σ) (Expr a (Eannot ds b'), ρ', σ')
  /-- ANNOTS merge: `{A_1} {A_2} E --> {A_1 ++ A_2} E` (one_step0
      Eannot arm, Core_reduction.lean:353 "reduction: ANNOTS";
      combine_dyn_annotations = (++), :305-306; get_ctx routes every
      double-annot root here, :375; the double-annot value is
      explicitly NOT irreducible, :293 first arm). Unconditional on
      the body, exactly as the engine; env untouched. -/
  | annot_merge {a1 a2 : List annot} {ds1 ds2 : List dyn_annotation}
      {b : CoreExpr} {ρ : EnvStack} {σ : Mem} :
      Step Q (Expr a1 (Eannot ds1 (Expr a2 (Eannot ds2 b))), ρ, σ)
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
      (hl : lookupLabel Q l = some (params, cont))
      (hvs : evalPexprs (ev0 :: evs) pes = some vs) :
      Step Q (e, ev0 :: evs, σ)
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
      Step Q (Expr a (Esave sb ps body), ev0 :: evs, σ)
           (body, bindSaveParams ps cvals (ev0 :: evs), σ)
  /-- Eif, true branch: ONE engine step with a BIG-STEP guard
      (one_step0's Eif TAU_WITH_RUNSTATE, Core_reduction.lean:353 —
      `full_eval_pexpr1 pe1` then dispatch on Vtrue/Vfalse; any other
      value is a failwithI PANIC, excluded by the premise). The
      mirror premise is the pure evaluator (header note 5). Env and
      state untouched. -/
  | if_true {a : List annot} {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
      {ρ : EnvStack} {σ : Mem}
      (hg : evalPexpr ρ g = some Vtrue) :
      Step Q (Expr a (Eif g e2 e3), ρ, σ) (e2, ρ, σ)
  /-- Eif, false branch. -/
  | if_false {a : List annot} {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
      {ρ : EnvStack} {σ : Mem}
      (hg : evalPexpr ρ g = some Vfalse) :
      Step Q (Expr a (Eif g e2 e3), ρ, σ) (e3, ρ, σ)
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
      Step Q (Expr a (Ecase pe pats), ρ, σ) (e', ρ, σ)

/-! ## Basic metatheory of Step (inversions the logic needs) -/

/-! ### Canonical-operand instances of the action rules

The evaluated-operand premises discharge by `rfl` at the canonical
`mk_value_pe` shapes; these instances restate the pre-S1 rule forms
so the certification layer and the small-axiom proofs apply them
directly. -/

theorem Step.store_canonical {Q : LabelMap} {a : List annot}
    {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {lk : Bool} {ty : ctype}
    {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
    {mv : CerbMem.MemValue} {fp : CerbMem.Footprint}
    {ρ : EnvStack} {σ σ' : Mem}
    (hmv : memValueFromValue fmapEmpty (Ctype [] (unatomic_ ty)) cv = some mv)
    (hmem : applyMemM (CerbMem.storeM loc ty lk pv mv) σ = some (fp, σ')) :
    Step Q (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Store0 lk (Pexpr [] () (PEval (Vctype ty)))
                       (Pexpr [] () (PEval (Vobject (OVpointer pv))))
                       (Pexpr [] () (PEval cv)) mo)))), ρ, σ)
         (Expr [] (Eannot [DA_pos [] fp]
            (Expr [] (Epure (Pexpr [] () (PEval Vunit))))), ρ, σ') :=
  Step.store rfl rfl rfl hmv hmem

theorem Step.load_canonical {Q : LabelMap} {a : List annot}
    {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {ty : ctype} {pv : CerbMem.PointerValue}
    {mo : memory_order} {mval : CerbMem.MemValue} {fp : CerbMem.Footprint}
    {ρ : EnvStack} {σ σ' : Mem}
    (hmem : applyMemM (CerbMem.loadM loc ty pv) σ = some ((fp, mval), σ')) :
    Step Q (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Load0 (Pexpr [] () (PEval (Vctype ty)))
                   (Pexpr [] () (PEval (Vobject (OVpointer pv)))) mo)))), ρ, σ)
         (Expr [] (Eannot [DA_pos [] fp]
            (Expr [] (Epure (Pexpr [] () (PEval
              (valueFromMemValue mval).2))))), ρ, σ') :=
  Step.load rfl rfl hmem

theorem Step.create_canonical {Q : LabelMap} {a : List annot}
    {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {align : CerbMem.IntegerValue} {ty : ctype}
    {pref : prefix0} {pv : CerbMem.PointerValue} {ρ : EnvStack} {σ σ' : Mem}
    (hmem : applyMemM (CerbMem.allocateObject 0 pref align ty none none) σ =
      some (pv, σ')) :
    Step Q (Expr a (Eaction (Paction polarity.Pos (Action loc ann
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
theorem Step.env_cons' {Q : LabelMap} {c c' : CoreExpr × EnvStack × Mem}
    (h : Step Q c c') :
    ∀ ev0 evs, c.2.1 = ev0 :: evs → ∃ ev0', c'.2.1 = ev0' :: evs := by
  induction h with
  | store h1 h2 h3 hmv hmem => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | load h1 h2 hmem => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | create h1 h2 hmem => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | sseq_pure => exact fun ev0 evs hin => ⟨ev0, hin⟩
  | sseq_annot => exact fun ev0 evs hin => ⟨ev0, hin⟩
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

theorem Step.env_cons {Q : LabelMap} {e : CoreExpr} {ev0 : Fmap sym value}
    {evs : List (Fmap sym value)} {σ : Mem}
    {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    (h : Step Q (e, ev0 :: evs, σ) (e', ρ', σ')) :
    ∃ ev0', ρ' = ev0' :: evs :=
  h.env_cons' ev0 evs rfl

/-- Values do not step (the Language interface's `val_stuck`).
    Engine analogue: is_irreducible short-circuits both get_ctx and
    one_step0 (Core_reduction.lean:293,353,375). -/
theorem Step.val_elim {Q : LabelMap} {w : SpikeVal} {ρ : EnvStack} {σ : Mem}
    {out : CoreExpr × EnvStack × Mem}
    (h : Step Q (ofVal w, ρ, σ) out) : False := by
  cases w with
  | pure v =>
    cases h with
    | run hj hl hvs => simp [ofVal] at hj
  | annot ds v =>
    cases h with
    | annot_ctx hnj hg hs =>
      cases hs with
      | run hj hl hvs => simp at hj
    | run hj hl hvs => simp [ofVal, jumpRedex?, annotRooted] at hj

theorem Step.toVal_none {Q : LabelMap} {e : CoreExpr} {ρ : EnvStack} {σ : Mem}
    {out : CoreExpr × EnvStack × Mem}
    (h : Step Q (e, ρ, σ) out) : toVal e = none := by
  cases hv : toVal e with
  | none => rfl
  | some w => exact absurd (ofVal_of_toVal hv ▸ h) (fun h => h.val_elim)

/-- Inversion at a store redex (canonical operand instance — the
    certified cone's shape): the step is unique and fully determined
    by the memM computation; the env is returned verbatim. -/
theorem Step.store_inv {Q : LabelMap} {a : List annot} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {lk : Bool} {ty : ctype}
    {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
    {ρ : EnvStack} {σ : Mem} {out : CoreExpr × EnvStack × Mem}
    (h : Step Q (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Store0 lk (Pexpr [] () (PEval (Vctype ty)))
                       (Pexpr [] () (PEval (Vobject (OVpointer pv))))
                       (Pexpr [] () (PEval cv)) mo)))), ρ, σ) out) :
    ∃ mv fp σ',
      memValueFromValue fmapEmpty (Ctype [] (unatomic_ ty)) cv = some mv ∧
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

/-- Inversion at a load redex (canonical operand instance). -/
theorem Step.load_inv {Q : LabelMap} {a : List annot} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {ty : ctype} {pv : CerbMem.PointerValue}
    {mo : memory_order} {ρ : EnvStack} {σ : Mem}
    {out : CoreExpr × EnvStack × Mem}
    (h : Step Q (Expr a (Eaction (Paction polarity.Pos (Action loc ann
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
  | load h1 h2 hmem =>
    rw [valueFromPexpr_val] at h1 h2
    injection h1 with h1; injection h1 with h1
    injection h2 with h2; injection h2 with h2; injection h2 with h2
    subst h1 h2
    exact ⟨_, _, _, hmem, rfl⟩

/-- Inversion at a create redex (canonical operand instance). -/
theorem Step.create_inv {Q : LabelMap} {a : List annot} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {align : CerbMem.IntegerValue} {ty : ctype}
    {pref : prefix0} {ρ : EnvStack} {σ : Mem}
    {out : CoreExpr × EnvStack × Mem}
    (h : Step Q (Expr a (Eaction (Paction polarity.Pos (Action loc ann
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

theorem Step.jump_inv {Q : LabelMap} {e : CoreExpr} {ρ : EnvStack} {σ : Mem}
    {out : CoreExpr × EnvStack × Mem} {l : sym}
    {pes : List (generic_pexpr Unit sym)}
    (hj : jumpRedex? e = some (l, pes))
    (h : Step Q (e, ρ, σ) out) :
    ∃ params cont vs ev0 evs, ρ = ev0 :: evs ∧
      lookupLabel Q l = some (params, cont) ∧
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
  | load h1 h2 hmem => simp at hj
  | create h1 h2 hmem => simp at hj
  | sseq_pure => rw [jumpRedex?_sseq, jumpRedex?_ofVal] at hj; cases hj
  | sseq_annot => rw [jumpRedex?_sseq, jumpRedex?_ofVal] at hj; cases hj
  | sseq_ctx hnj hs => rw [jumpRedex?_sseq, hnj] at hj; cases hj
  | annot_ctx hnj hg hs => rw [jumpRedex?_annot_of_not_root _ _ hg, hnj] at hj; cases hj
  | annot_merge =>
    rw [jumpRedex?_annot_of_root _ _ (by rfl)] at hj; cases hj
  | save hvals => simp [jumpRedex?] at hj
  | if_true hg => simp [jumpRedex?] at hj
  | if_false hg => simp [jumpRedex?] at hj
  | case_value hv hsel => simp [jumpRedex?] at hj

/-- Reducibility at a registered jump redex (the probe's
    `step_of_jumpRedex`). -/
theorem Step.run_of_jumpRedex {Q : LabelMap} {e : CoreExpr} {l : sym}
    {pes : List (generic_pexpr Unit sym)}
    {params : List (sym × core_base_type)} {cont : CoreExpr} {vs : List value}
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {σ : Mem}
    (hj : jumpRedex? e = some (l, pes))
    (hl : lookupLabel Q l = some (params, cont))
    (hvs : evalPexprs (ev0 :: evs) pes = some vs) :
    Step Q (e, ev0 :: evs, σ) (cont, bindArgs params vs (ev0 :: evs), σ) :=
  Step.run hj hl hvs

/-- Inversion at an Esseq node (S3 form): a frame step of a
    NON-jump-redex e1, one of the two betas, or THE GLOBAL JUMP
    (frame discarded — the successor is e1's own jump successor).
    The frame case's `jumpRedex? e1 = none` is the S3 congruence
    guard surfacing; the jump disjunct is the readiness's "factor
    theorem gains one disjunct" at the Esseq node. -/
theorem Step.sseq_inv {Q : LabelMap} {a : List annot} {pat : pattern}
    {e1 e2 : CoreExpr}
    {ρ : EnvStack} {σ : Mem} {out : CoreExpr × EnvStack × Mem}
    (h : Step Q (Expr a (Esseq pat e1 e2), ρ, σ) out) :
    (∃ e1' ρ' σ', jumpRedex? e1 = none ∧ Step Q (e1, ρ, σ) (e1', ρ', σ') ∧
        out = (Expr a (Esseq pat e1' e2), ρ', σ')) ∨
    (∃ pa bty v ev0 evs, pat = Pattern pa (CaseBase (none, bty)) ∧
        e1 = ofVal (.pure v) ∧ ρ = ev0 :: evs ∧ out = (e2, ρ, σ)) ∨
    (∃ pa bty ds v ev0 evs, pat = Pattern pa (CaseBase (none, bty)) ∧
        e1 = ofVal (.annot ds v) ∧ ρ = ev0 :: evs ∧
        out = (Expr [] (Eannot ds e2), ρ, σ)) ∨
    (∃ l pes params cont vs ev0 evs, jumpRedex? e1 = some (l, pes) ∧
        ρ = ev0 :: evs ∧ lookupLabel Q l = some (params, cont) ∧
        evalPexprs ρ pes = some vs ∧
        out = (cont, bindArgs params vs ρ, σ)) := by
  cases h with
  | sseq_ctx hnj hs => exact .inl ⟨_, _, _, hnj, hs, rfl⟩
  | sseq_pure => exact .inr (.inl ⟨_, _, _, _, _, rfl, rfl, rfl, rfl⟩)
  | sseq_annot => exact .inr (.inr (.inl ⟨_, _, _, _, _, _, rfl, rfl, rfl, rfl⟩))
  | run hj hl hvs =>
    rw [jumpRedex?_sseq] at hj
    exact .inr (.inr (.inr ⟨_, _, _, _, _, _, _, hj, rfl, hl, hvs, rfl⟩))

/-- Inversion at an Eannot node (S3 form): Cannot-descent of a
    non-jump-redex body, the ANNOTS merge, or the global jump
    through the Cannot frame. -/
theorem Step.annot_inv {Q : LabelMap} {a : List annot}
    {ds : List dyn_annotation}
    {b : CoreExpr} {ρ : EnvStack} {σ : Mem}
    {out : CoreExpr × EnvStack × Mem}
    (h : Step Q (Expr a (Eannot ds b), ρ, σ) out) :
    (annotRooted b = false ∧ jumpRedex? b = none ∧
        ∃ b' ρ' σ', Step Q (b, ρ, σ) (b', ρ', σ') ∧
        out = (Expr a (Eannot ds b'), ρ', σ')) ∨
    (∃ a2 ds2 c, b = Expr a2 (Eannot ds2 c) ∧
        out = (Expr (a ++ a2) (Eannot (ds ++ ds2) c), ρ, σ)) ∨
    (∃ l pes params cont vs ev0 evs, annotRooted b = false ∧
        jumpRedex? b = some (l, pes) ∧
        ρ = ev0 :: evs ∧ lookupLabel Q l = some (params, cont) ∧
        evalPexprs ρ pes = some vs ∧
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
theorem Step.save_inv {Q : LabelMap} {a : List annot}
    {sb : sym × core_base_type}
    {ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
    {body : CoreExpr} {ρ : EnvStack} {σ : Mem}
    {out : CoreExpr × EnvStack × Mem}
    (h : Step Q (Expr a (Esave sb ps body), ρ, σ) out) :
    ∃ cvals ev0 evs, ρ = ev0 :: evs ∧
      valueFromPexprs (saveParamPexprs ps) = some cvals ∧
      out = (body, bindSaveParams ps cvals ρ, σ) := by
  cases h with
  | save hvals => exact ⟨_, _, _, rfl, hvals, rfl⟩
  | run hj hl hvs => simp [jumpRedex?] at hj

/-- Inversion at an Eif node: the guard evaluates to a boolean and
    the step selects the branch. -/
theorem Step.if_inv {Q : LabelMap} {a : List annot}
    {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
    {ρ : EnvStack} {σ : Mem} {out : CoreExpr × EnvStack × Mem}
    (h : Step Q (Expr a (Eif g e2 e3), ρ, σ) out) :
    (evalPexpr ρ g = some Vtrue ∧ out = (e2, ρ, σ)) ∨
    (evalPexpr ρ g = some Vfalse ∧ out = (e3, ρ, σ)) := by
  cases h with
  | if_true hg => exact .inl ⟨hg, rfl⟩
  | if_false hg => exact .inr ⟨hg, rfl⟩
  | run hj hl hvs => simp [jumpRedex?] at hj

/-- Inversion at an Ecase node: the value-scrutinee selection TAU. -/
theorem Step.case_inv {Q : LabelMap} {a : List annot}
    {pe : generic_pexpr Unit sym} {pats : List (pattern × CoreExpr)}
    {ρ : EnvStack} {σ : Mem} {out : CoreExpr × EnvStack × Mem}
    (h : Step Q (Expr a (Ecase pe pats), ρ, σ) out) :
    ∃ cval e', valueFromPexpr pe = some cval ∧
      select_case subst_sym_expr cval pats = some e' ∧
      out = (e', ρ, σ) := by
  cases h with
  | case_value hv hsel => exact ⟨_, _, hv, hsel, rfl⟩
  | run hj hl hvs => simp [jumpRedex?] at hj

/-! ## The frozen entry label map + the phase-1 fragment cone

`spikeLbl` is the S3 analog of `spikeEnv`: the frozen EMPTY label
map the jump-free exports pin their tuples at (the production
driver's `labeled` fiber at `current_proc_opt = none` — no procedure,
no registered labels). At `spikeLbl` the jump rule can never fire
(`lookupLabel_empty`), so the phase-1 corpus's statements survive
pinned, with their proofs refuting the jump disjuncts.

`FragP` (the phase-1 syntactic fragment cone) MOVES here from
Soundness.lean unchanged in statement: S3's retirement of the
unconditional env invariance (pre-declared) leaves its survivors
(`Step.env_invariant_frag`, Rules.lean `wp_env_invariant_frag`)
FragP-scoped, and Rules.lean does not import the boundary module. -/

abbrev spikeLbl : LabelMap := fmapEmpty

@[simp] theorem lookupLabel_empty (l : sym) :
    lookupLabel spikeLbl l = none := rfl

/-- At the empty label map nothing ever jumps: any step's subject has
    no REGISTERED jump redex — and since registration is what the
    jump rule needs, a step's subject with a syntactic jump redex is
    impossible. -/
theorem Step.jumpRedex?_none_of_spikeLbl {e : CoreExpr} {ρ : EnvStack}
    {σ : Mem} {out : CoreExpr × EnvStack × Mem}
    (h : Step spikeLbl (e, ρ, σ) out) : jumpRedex? e = none := by
  cases hj : jumpRedex? e with
  | none => rfl
  | some lp =>
    obtain ⟨l, pes⟩ := lp
    obtain ⟨params, cont, vs, ev0, evs, -, hl, -, -⟩ := h.jump_inv hj
    rw [lookupLabel_empty] at hl
    cases hl

/-- The syntactic fragment (canonical shapes, closed under Step —
    `FragP.step`): pure values, positive non-library store/load with
    canonical value operands, wildcard strong sequencing, and the
    run-time Eannot residue. Node annotation lists are pinned `[]`
    (what authored programs and every engine successor produce);
    `isLibraryLocation loc = false` freezes step_ctx's
    library-location current_loc substitution out of the fragment
    (slice-A D5). S3: FragP stays the PHASE-1 cone (no
    Eif/Ecase/Esave/Erun) — the extended cone is Soundness.lean's
    `FragJ`. -/
inductive FragP : CoreExpr → Prop where
  | val_pure (v : value) : FragP (Expr [] (Epure (Pexpr [] () (PEval v))))
  | store {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
      {ty : ctype} {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
      (hlib : CerbLocation.isLibraryLocation loc = false) :
      FragP (Expr [] (Eaction (Paction polarity.Pos (Action loc ann
        (Store0 lk (Pexpr [] () (PEval (Vctype ty)))
                   (Pexpr [] () (PEval (Vobject (OVpointer pv))))
                   (Pexpr [] () (PEval cv)) mo)))))
  | load {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
      {pv : CerbMem.PointerValue} {mo : memory_order}
      (hlib : CerbLocation.isLibraryLocation loc = false) :
      FragP (Expr [] (Eaction (Paction polarity.Pos (Action loc ann
        (Load0 (Pexpr [] () (PEval (Vctype ty)))
               (Pexpr [] () (PEval (Vobject (OVpointer pv)))) mo)))))
  | create {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {align : CerbMem.IntegerValue} {ty : ctype} {pref : prefix0}
      (hlib : CerbLocation.isLibraryLocation loc = false) :
      FragP (Expr [] (Eaction (Paction polarity.Pos (Action loc ann
        (Create (Pexpr [] () (PEval (Vobject (OVinteger align))))
                (Pexpr [] () (PEval (Vctype ty))) pref)))))
  | sseq {pa : List annot} {bty : core_base_type} {e1 e2 : CoreExpr} :
      FragP e1 → FragP e2 →
      FragP (Expr [] (Esseq (Pattern pa (CaseBase (none, bty))) e1 e2))
  | annot {ds : List dyn_annotation} {b : CoreExpr} :
      FragP b → FragP (Expr [] (Eannot ds b))

/-- Both value forms are fragment terms (`ofVal (.annot ds v)` is
    `annot` over `val_pure`). -/
theorem fragP_ofVal (w : SpikeVal) : FragP (ofVal w) := by
  cases w with
  | pure v => exact .val_pure v
  | annot ds v => exact .annot (.val_pure v)

/-- The phase-1 cone has no jump redex (no `Erun` shape exists in
    it). -/
theorem FragP.jumpRedex?_none {e : CoreExpr} (hf : FragP e) :
    jumpRedex? e = none := by
  induction hf with
  | val_pure v => rfl
  | store hlib => rfl
  | load hlib => rfl
  | create hlib => rfl
  | sseq hf1 hf2 ih1 ih2 => rw [jumpRedex?_sseq]; exact ih1
  | annot hfb ihb =>
    rw [jumpRedex?_annot]
    split
    · rfl
    · exact ihb

/-- Closure + FragP-scoped env invariance in one pass: on the
    phase-1 cone no rule writes the environment (the S3 survivor of
    the retired `Step.env_invariant` — pre-declared, phase-1 notes
    §2 item 6). -/
theorem FragP.step_env {Q : LabelMap} {e : CoreExpr} {ρ : EnvStack} {σ : Mem}
    {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    (hf : FragP e) (hs : Step Q (e, ρ, σ) (e', ρ', σ')) :
    FragP e' ∧ ρ' = ρ := by
  induction hf generalizing e' ρ' σ' with
  | val_pure v => exact (Step.val_elim (w := .pure v) hs).elim
  | store hlib =>
    obtain ⟨mv, fp, σ'', hmv, hmem, hout⟩ := hs.store_inv
    obtain ⟨h1, h2, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact ⟨.annot (.val_pure Vunit), h2⟩
  | load hlib =>
    obtain ⟨fp, mval, σ'', hmem, hout⟩ := hs.load_inv
    obtain ⟨h1, h2, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact ⟨.annot (.val_pure _), h2⟩
  | create hlib =>
    obtain ⟨pv, σ'', hmem, hout⟩ := hs.create_inv
    obtain ⟨h1, h2, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact ⟨.val_pure _, h2⟩
  | sseq hf1 hf2 ih1 ih2 =>
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
        ⟨_, _, v, _, _, _, _, _, hout⟩ | ⟨_, _, ds', v, _, _, _, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩
    · obtain ⟨h1, h2, -⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1 h2
      obtain ⟨hf1', hρ⟩ := ih1 hstep
      exact ⟨.sseq hf1' hf2, hρ⟩
    · obtain ⟨h1, h2, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact ⟨hf2, h2⟩
    · obtain ⟨h1, h2, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact ⟨.annot hf2, h2⟩
    · rw [hf1.jumpRedex?_none] at hj
      cases hj
  | annot hfb ihb =>
    rcases hs.annot_inv with ⟨hg, hnj, b', ρ'', σ'', hstep, hout⟩ |
        ⟨a2, ds2, c, hb, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hg, hj, _, _, _, _⟩
    · obtain ⟨h1, h2, -⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1 h2
      obtain ⟨hfb', hρ⟩ := ihb hstep
      exact ⟨.annot hfb', hρ⟩
    · subst hb
      obtain ⟨h1, h2, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      cases hfb with
      | annot hfc => exact ⟨.annot hfc, h2⟩
    · rw [hfb.jumpRedex?_none] at hj
      cases hj

/-- The fragment is closed under Step (statement of the phase-1
    lemma, now over the S3 relation at any label map). -/
theorem FragP.step {Q : LabelMap} {e : CoreExpr} {ρ : EnvStack} {σ : Mem}
    {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    (hf : FragP e) (hs : Step Q (e, ρ, σ) (e', ρ', σ')) : FragP e' :=
  (hf.step_env hs).1

/-- FragP-scoped env invariance (the retired `Step.env_invariant`'s
    survivor). -/
theorem Step.env_invariant_frag {Q : LabelMap} {e : CoreExpr} {ρ : EnvStack}
    {σ : Mem} {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    (hf : FragP e) (h : Step Q (e, ρ, σ) (e', ρ', σ')) : ρ' = ρ :=
  (hf.step_env h).2

end CerberusHeapLang
