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

/-! ## The runtime tuple (S1: env is live state — probe `TRt`/`TRVal`
pattern, StmtProbe/Toy.lean:113-124, minus the label map) -/

/-- The runtime expression tuple: Core expression + live environment
    stack (thread_state's `arena` and `env` components; the rest of
    the thread state stays frozen context — Soundness.lean). -/
structure CoreRt where
  e : CoreExpr
  ρ : EnvStack

/-- Values carry the final env (exported posts may project it away —
    probe `TRVal`). -/
structure CoreRVal where
  w : SpikeVal
  ρ : EnvStack

/-- The delivered engine value of a runtime value (annotations and
    env erased — the D1 readout). -/
def CoreRVal.val (v : CoreRVal) : value := v.w.val

/-- Annotation-merge on runtime values: componentwise `SpikeVal.merge`
    (the env rides — annotation reduction never touches it). -/
def CoreRVal.merge (ds : List dyn_annotation) (v : CoreRVal) : CoreRVal :=
  ⟨SpikeVal.merge ds v.w, v.ρ⟩

@[simp] theorem CoreRVal.merge_mk (ds : List dyn_annotation) (w : SpikeVal)
    (ρ : EnvStack) : CoreRVal.merge ds ⟨w, ρ⟩ = ⟨SpikeVal.merge ds w, ρ⟩ := rfl

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
  (toVal r.e).map fun w => ⟨w, r.ρ⟩

/-- Componentwise value injection (Language-side `ofVal`). -/
def ofValRt (v : CoreRVal) : CoreRt := ⟨ofVal v.w, v.ρ⟩

@[simp] theorem toValRt_mk (e : CoreExpr) (ρ : EnvStack) :
    toValRt ⟨e, ρ⟩ = (toVal e).map fun w => ⟨w, ρ⟩ := rfl

@[simp] theorem ofValRt_mk (w : SpikeVal) (ρ : EnvStack) :
    ofValRt ⟨w, ρ⟩ = ⟨ofVal w, ρ⟩ := rfl

@[simp] theorem toValRt_ofValRt (v : CoreRVal) : toValRt (ofValRt v) = some v := by
  obtain ⟨w, ρ⟩ := v
  rw [ofValRt_mk, toValRt_mk, toVal_ofVal]
  rfl

/-- Evaluated-operand recognition on canonical shapes: the ACTION_EVAL
    rule premises (`valueFromPexpr`, Core_aux.lean:472) discharge by
    `rfl` on `mk_value_pe`-shaped operands (any node annotations —
    the engine's redex patterns accept them, slice notes §D3). -/
@[simp] theorem valueFromPexpr_val (a : List annot) (v : value) :
    valueFromPexpr (Pexpr a () (PEval v)) = some v := rfl

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
inductive Step : CoreExpr × EnvStack × Mem → CoreExpr × EnvStack × Mem → Prop where
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
      Step (Expr a (Eaction (Paction polarity.Pos (Action loc ann
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
      Step (Expr a (Eaction (Paction polarity.Pos (Action loc ann
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
      Step (Expr a (Eaction (Paction polarity.Pos (Action loc ann
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
      Step (Expr a (Esseq (Pattern pa (CaseBase (none, bty)))
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
      Step (Expr a (Esseq (Pattern pa (CaseBase (none, bty)))
              (ofVal (.annot ds v)) e2), ev0 :: evs, σ)
           (Expr [] (Eannot ds e2), ev0 :: evs, σ)
  /-- Reduction under the strong-sequencing frame. Mirrors get_ctx's
      Esseq arm (descend into e1 when it is not irreducible —
      Core_reduction.lean:375) + apply_ctx's Csseq rebuild
      (Core_reduction.lean:389). No irreducibility guard is needed:
      no Step rule fires on an irreducible e1 (see
      `Step.not_irreducible_shape` note below / slice notes §D4).
      Env-GENERAL: the thread env is global, so a descent step's env
      update carries through the frame unchanged in shape. -/
  | sseq_ctx {a : List annot} {pat : pattern} {e1 e1' e2 : CoreExpr}
      {ρ ρ' : EnvStack} {σ σ' : Mem} :
      Step (e1, ρ, σ) (e1', ρ', σ') →
      Step (Expr a (Esseq pat e1 e2), ρ, σ) (Expr a (Esseq pat e1' e2), ρ', σ')
  /-- Reduction under a dyn-annotation frame. Mirrors get_ctx's plain
      `Eannot xs e` arm (Cannot-descent — taken only when e is NOT
      itself Eannot-rooted, because the double-annot arm precedes it;
      Core_reduction.lean:375) + apply_ctx's Cannot rebuild
      (Core_reduction.lean:389). The guard is load-bearing: without
      it this rule would race the ANNOTS merge, which the engine
      never does. -/
  | annot_ctx {a : List annot} {ds : List dyn_annotation} {b b' : CoreExpr}
      {ρ ρ' : EnvStack} {σ σ' : Mem} :
      annotRooted b = false →
      Step (b, ρ, σ) (b', ρ', σ') →
      Step (Expr a (Eannot ds b), ρ, σ) (Expr a (Eannot ds b'), ρ', σ')
  /-- ANNOTS merge: `{A_1} {A_2} E --> {A_1 ++ A_2} E` (one_step0
      Eannot arm, Core_reduction.lean:353 "reduction: ANNOTS";
      combine_dyn_annotations = (++), :305-306; get_ctx routes every
      double-annot root here, :375; the double-annot value is
      explicitly NOT irreducible, :293 first arm). Unconditional on
      the body, exactly as the engine; env untouched. -/
  | annot_merge {a1 a2 : List annot} {ds1 ds2 : List dyn_annotation}
      {b : CoreExpr} {ρ : EnvStack} {σ : Mem} :
      Step (Expr a1 (Eannot ds1 (Expr a2 (Eannot ds2 b))), ρ, σ)
           (Expr (a1 ++ a2) (Eannot (ds1 ++ ds2) b), ρ, σ)

/-! ## Basic metatheory of Step (inversions the logic needs) -/

/-! ### Canonical-operand instances of the action rules

The evaluated-operand premises discharge by `rfl` at the canonical
`mk_value_pe` shapes; these instances restate the pre-S1 rule forms
so the certification layer and the small-axiom proofs apply them
directly. -/

theorem Step.store_canonical {a : List annot} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {lk : Bool} {ty : ctype}
    {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
    {mv : CerbMem.MemValue} {fp : CerbMem.Footprint}
    {ρ : EnvStack} {σ σ' : Mem}
    (hmv : memValueFromValue fmapEmpty (Ctype [] (unatomic_ ty)) cv = some mv)
    (hmem : applyMemM (CerbMem.storeM loc ty lk pv mv) σ = some (fp, σ')) :
    Step (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Store0 lk (Pexpr [] () (PEval (Vctype ty)))
                       (Pexpr [] () (PEval (Vobject (OVpointer pv))))
                       (Pexpr [] () (PEval cv)) mo)))), ρ, σ)
         (Expr [] (Eannot [DA_pos [] fp]
            (Expr [] (Epure (Pexpr [] () (PEval Vunit))))), ρ, σ') :=
  Step.store rfl rfl rfl hmv hmem

theorem Step.load_canonical {a : List annot} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {ty : ctype} {pv : CerbMem.PointerValue}
    {mo : memory_order} {mval : CerbMem.MemValue} {fp : CerbMem.Footprint}
    {ρ : EnvStack} {σ σ' : Mem}
    (hmem : applyMemM (CerbMem.loadM loc ty pv) σ = some ((fp, mval), σ')) :
    Step (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Load0 (Pexpr [] () (PEval (Vctype ty)))
                   (Pexpr [] () (PEval (Vobject (OVpointer pv)))) mo)))), ρ, σ)
         (Expr [] (Eannot [DA_pos [] fp]
            (Expr [] (Epure (Pexpr [] () (PEval
              (valueFromMemValue mval).2))))), ρ, σ') :=
  Step.load rfl rfl hmem

theorem Step.create_canonical {a : List annot} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {align : CerbMem.IntegerValue} {ty : ctype}
    {pref : prefix0} {pv : CerbMem.PointerValue} {ρ : EnvStack} {σ σ' : Mem}
    (hmem : applyMemM (CerbMem.allocateObject 0 pref align ty none none) σ =
      some (pv, σ')) :
    Step (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Create (Pexpr [] () (PEval (Vobject (OVinteger align))))
                    (Pexpr [] () (PEval (Vctype ty))) pref)))), ρ, σ)
         (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer pv))))), ρ, σ') :=
  Step.create rfl rfl hmem

/-- PHASE-1 ENV INVARIANCE: no rule of the branch-free sequential
    fragment writes the environment (wildcard betas are the identity;
    the request path never touches thread env; congruences carry the
    inner step's env). The S3 jump rule (Erun parameter rebinding)
    RETIRES this lemma — its deletion then is a pre-declared,
    documented statement removal (phase-1 notes). -/
theorem Step.env_invariant' {c c' : CoreExpr × EnvStack × Mem}
    (h : Step c c') : c'.2.1 = c.2.1 := by
  induction h <;> first | rfl | assumption

theorem Step.env_invariant {e : CoreExpr} {ρ : EnvStack} {σ : Mem}
    {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    (h : Step (e, ρ, σ) (e', ρ', σ')) : ρ' = ρ :=
  h.env_invariant'

/-- Values do not step (the Language interface's `val_stuck`).
    Engine analogue: is_irreducible short-circuits both get_ctx and
    one_step0 (Core_reduction.lean:293,353,375). -/
theorem Step.val_elim {w : SpikeVal} {ρ : EnvStack} {σ : Mem}
    {out : CoreExpr × EnvStack × Mem}
    (h : Step (ofVal w, ρ, σ) out) : False := by
  cases w with
  | pure v => cases h
  | annot ds v =>
    cases h with
    | annot_ctx hg hs => cases hs

theorem Step.toVal_none {e : CoreExpr} {ρ : EnvStack} {σ : Mem}
    {out : CoreExpr × EnvStack × Mem}
    (h : Step (e, ρ, σ) out) : toVal e = none := by
  cases hv : toVal e with
  | none => rfl
  | some w => exact absurd (ofVal_of_toVal hv ▸ h) (fun h => h.val_elim)

/-- Inversion at a store redex (canonical operand instance — the
    certified cone's shape): the step is unique and fully determined
    by the memM computation; the env is returned verbatim. -/
theorem Step.store_inv {a : List annot} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {lk : Bool} {ty : ctype}
    {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
    {ρ : EnvStack} {σ : Mem} {out : CoreExpr × EnvStack × Mem}
    (h : Step (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Store0 lk (Pexpr [] () (PEval (Vctype ty)))
                       (Pexpr [] () (PEval (Vobject (OVpointer pv))))
                       (Pexpr [] () (PEval cv)) mo)))), ρ, σ) out) :
    ∃ mv fp σ',
      memValueFromValue fmapEmpty (Ctype [] (unatomic_ ty)) cv = some mv ∧
      applyMemM (CerbMem.storeM loc ty lk pv mv) σ = some (fp, σ') ∧
      out = (Expr [] (Eannot [DA_pos [] fp]
              (Expr [] (Epure (Pexpr [] () (PEval Vunit))))), ρ, σ') := by
  cases h with
  | store h1 h2 h3 hmv hmem =>
    rw [valueFromPexpr_val] at h1 h2 h3
    injection h1 with h1; injection h1 with h1
    injection h2 with h2; injection h2 with h2; injection h2 with h2
    injection h3 with h3
    subst h1 h2 h3
    exact ⟨_, _, _, hmv, hmem, rfl⟩

/-- Inversion at a load redex (canonical operand instance). -/
theorem Step.load_inv {a : List annot} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {ty : ctype} {pv : CerbMem.PointerValue}
    {mo : memory_order} {ρ : EnvStack} {σ : Mem}
    {out : CoreExpr × EnvStack × Mem}
    (h : Step (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Load0 (Pexpr [] () (PEval (Vctype ty)))
                   (Pexpr [] () (PEval (Vobject (OVpointer pv)))) mo)))), ρ, σ)
          out) :
    ∃ fp mval σ',
      applyMemM (CerbMem.loadM loc ty pv) σ = some ((fp, mval), σ') ∧
      out = (Expr [] (Eannot [DA_pos [] fp]
              (Expr [] (Epure (Pexpr [] () (PEval
                (valueFromMemValue mval).2))))), ρ, σ') := by
  cases h with
  | load h1 h2 hmem =>
    rw [valueFromPexpr_val] at h1 h2
    injection h1 with h1; injection h1 with h1
    injection h2 with h2; injection h2 with h2; injection h2 with h2
    subst h1 h2
    exact ⟨_, _, _, hmem, rfl⟩

/-- Inversion at a create redex (canonical operand instance). -/
theorem Step.create_inv {a : List annot} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {align : CerbMem.IntegerValue} {ty : ctype}
    {pref : prefix0} {ρ : EnvStack} {σ : Mem}
    {out : CoreExpr × EnvStack × Mem}
    (h : Step (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Create (Pexpr [] () (PEval (Vobject (OVinteger align))))
                    (Pexpr [] () (PEval (Vctype ty))) pref)))), ρ, σ) out) :
    ∃ pv σ',
      applyMemM (CerbMem.allocateObject 0 pref align ty none none) σ =
        some (pv, σ') ∧
      out = (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer pv))))), ρ, σ') := by
  cases h with
  | create h1 h2 hmem =>
    rw [valueFromPexpr_val] at h1 h2
    injection h1 with h1; injection h1 with h1; injection h1 with h1
    injection h2 with h2; injection h2 with h2
    subst h1 h2
    exact ⟨_, _, hmem, rfl⟩

/-- Inversion at an Esseq node: either a frame step of e1, or one of
    the two betas (which require e1 to be a canonical value form and
    the env stack to be nonempty). -/
theorem Step.sseq_inv {a : List annot} {pat : pattern} {e1 e2 : CoreExpr}
    {ρ : EnvStack} {σ : Mem} {out : CoreExpr × EnvStack × Mem}
    (h : Step (Expr a (Esseq pat e1 e2), ρ, σ) out) :
    (∃ e1' ρ' σ', Step (e1, ρ, σ) (e1', ρ', σ') ∧
        out = (Expr a (Esseq pat e1' e2), ρ', σ')) ∨
    (∃ pa bty v ev0 evs, pat = Pattern pa (CaseBase (none, bty)) ∧
        e1 = ofVal (.pure v) ∧ ρ = ev0 :: evs ∧ out = (e2, ρ, σ)) ∨
    (∃ pa bty ds v ev0 evs, pat = Pattern pa (CaseBase (none, bty)) ∧
        e1 = ofVal (.annot ds v) ∧ ρ = ev0 :: evs ∧
        out = (Expr [] (Eannot ds e2), ρ, σ)) := by
  cases h with
  | sseq_ctx hs => exact .inl ⟨_, _, _, hs, rfl⟩
  | sseq_pure => exact .inr (.inl ⟨_, _, _, _, _, rfl, rfl, rfl, rfl⟩)
  | sseq_annot => exact .inr (.inr ⟨_, _, _, _, _, _, rfl, rfl, rfl, rfl⟩)

/-- Inversion at an Eannot node: Cannot-descent (non-annot-rooted
    body) or the ANNOTS merge (annot-rooted body). -/
theorem Step.annot_inv {a : List annot} {ds : List dyn_annotation}
    {b : CoreExpr} {ρ : EnvStack} {σ : Mem}
    {out : CoreExpr × EnvStack × Mem}
    (h : Step (Expr a (Eannot ds b), ρ, σ) out) :
    (annotRooted b = false ∧ ∃ b' ρ' σ', Step (b, ρ, σ) (b', ρ', σ') ∧
        out = (Expr a (Eannot ds b'), ρ', σ')) ∨
    (∃ a2 ds2 c, b = Expr a2 (Eannot ds2 c) ∧
        out = (Expr (a ++ a2) (Eannot (ds ++ ds2) c), ρ, σ)) := by
  cases h with
  | annot_ctx hg hs => exact .inl ⟨hg, _, _, _, hs, rfl⟩
  | annot_merge => exact .inr ⟨_, _, _, rfl, rfl⟩

end CerberusHeapLang
