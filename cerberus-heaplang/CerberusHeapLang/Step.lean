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
§3.2): tagDefs = fmapEmpty, extern = fmapEmpty, default file, tid 0,
env = [fmapEmpty]. Wildcard patterns keep the env frozen:
update_env with `CaseBase (none, _)` is the identity on the
environment (Core_aux.lean:861-868, first arm). The aid counter
(driver_state.core_run_state0.aid_supply) never enters the fragment's
terms: positive non-excluded actions annotate with `DA_pos [] fp`
(step_action, Core_reduction.lean:424 Store0/Load0 arms — aid1 is
unused in the continuation's dyn_annots), so Step needs no aid index.
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
inductive Step : CoreExpr × Mem → CoreExpr × Mem → Prop where
  /-- Positive strong store, canonical operands. Mirrors:
      step_action Store0 arm (Core_reduction.lean:424 — operand
      readout via act_valueFromPexpr, memValueFromValue at
      `Ctype [] (unatomic_ ty)`, request `StoreRequest2`), driver
      discharge `liftMem (CerbMem.storeM loc ty lk pv mv)`
      (Driver.lean:273), continuation
      `Expr [] (Eannot [DA_pos [] fp] (mk_value_e Vunit))` (is_excluded
      = none on the fragment's positive path). storeM: CerbMem.lean:1632. -/
  | store {a : List annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {lk : Bool} {ty : ctype} {pv : CerbMem.PointerValue} {cv : value}
      {mo : memory_order} {mv : CerbMem.MemValue} {fp : CerbMem.Footprint}
      {σ σ' : Mem}
      (hmv : memValueFromValue fmapEmpty (Ctype [] (unatomic_ ty)) cv = some mv)
      (hmem : applyMemM (CerbMem.storeM loc ty lk pv mv) σ = some (fp, σ')) :
      Step (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Store0 lk (Pexpr [] () (PEval (Vctype ty)))
                         (Pexpr [] () (PEval (Vobject (OVpointer pv))))
                         (Pexpr [] () (PEval cv)) mo)))), σ)
           (Expr [] (Eannot [DA_pos [] fp]
              (Expr [] (Epure (Pexpr [] () (PEval Vunit))))), σ')
  /-- Positive strong load, canonical operands. Mirrors: step_action
      Load0 arm (Core_reduction.lean:424 — request `LoadRequest2`,
      continuation `Expr [] (Eannot [DA_pos [] fp] (mk_value_e
      (valueFromMemValue mval).2))`), driver discharge
      `liftMem (CerbMem.loadM loc ty pv)` (Driver.lean:273).
      loadM: CerbMem.lean:1586 (returns the state unchanged on the
      active path — σ' = σ is derivable, kept in applyMemM shape). -/
  | load {a : List annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {ty : ctype} {pv : CerbMem.PointerValue} {mo : memory_order}
      {mval : CerbMem.MemValue} {fp : CerbMem.Footprint} {σ σ' : Mem}
      (hmem : applyMemM (CerbMem.loadM loc ty pv) σ = some ((fp, mval), σ')) :
      Step (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Load0 (Pexpr [] () (PEval (Vctype ty)))
                     (Pexpr [] () (PEval (Vobject (OVpointer pv)))) mo)))), σ)
           (Expr [] (Eannot [DA_pos [] fp]
              (Expr [] (Epure (Pexpr [] () (PEval
                (valueFromMemValue mval).2))))), σ')
  /-- Positive strong create (Extension D: cold-start programs create
      their own cells). Mirrors: step_action Create arm
      (Core_reduction.lean:424 — canonical operands
      `(Vobject (OVinteger align), Vctype ty)` always classify, so no
      ILLTYPED arm exists for this shape; request `CreateRequest2 pref
      align ty (get_with_address e_annots) none` with continuation
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
      {align : CerbMem.IntegerValue} {ty : ctype} {pref : prefix0}
      {pv : CerbMem.PointerValue} {σ σ' : Mem}
      (hmem : applyMemM (CerbMem.allocateObject 0 pref align ty none none) σ =
        some (pv, σ')) :
      Step (Expr a (Eaction (Paction polarity.Pos (Action loc ann
              (Create (Pexpr [] () (PEval (Vobject (OVinteger align))))
                      (Pexpr [] () (PEval (Vctype ty))) pref)))), σ)
           (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer pv))))), σ')
  /-- LETS-PURE at a wildcard pattern:
      `lets _ = v in E2 --> E2` (one_step0 Esseq bare-value arm,
      Core_reduction.lean:353 "reduction: LETS-PURE"; the env update
      `update_env (CaseBase (none,_))` is the identity,
      Core_aux.lean:861-868 — the frozen env survives). -/
  | sseq_pure {a pa : List annot} {bty : core_base_type} {v : value}
      {e2 : CoreExpr} {σ : Mem} :
      Step (Expr a (Esseq (Pattern pa (CaseBase (none, bty)))
              (ofVal (.pure v)) e2), σ)
           (e2, σ)
  /-- LETS-ANNOT at a wildcard pattern:
      `lets _ = {A}v in E2 --> {A} E2` (one_step0 Esseq Eannot arm,
      Core_reduction.lean:353 "reduction: LETS-ANNOT" — the engine
      writes the result node annots as `[]` verbatim). This is the
      R-i residue entering the continuation. -/
  | sseq_annot {a pa : List annot} {bty : core_base_type}
      {ds : List dyn_annotation} {v : value} {e2 : CoreExpr} {σ : Mem} :
      Step (Expr a (Esseq (Pattern pa (CaseBase (none, bty)))
              (ofVal (.annot ds v)) e2), σ)
           (Expr [] (Eannot ds e2), σ)
  /-- Reduction under the strong-sequencing frame. Mirrors get_ctx's
      Esseq arm (descend into e1 when it is not irreducible —
      Core_reduction.lean:375) + apply_ctx's Csseq rebuild
      (Core_reduction.lean:389). No irreducibility guard is needed:
      no Step rule fires on an irreducible e1 (see
      `Step.not_irreducible_shape` note below / slice notes §D4). -/
  | sseq_ctx {a : List annot} {pat : pattern} {e1 e1' e2 : CoreExpr}
      {σ σ' : Mem} :
      Step (e1, σ) (e1', σ') →
      Step (Expr a (Esseq pat e1 e2), σ) (Expr a (Esseq pat e1' e2), σ')
  /-- Reduction under a dyn-annotation frame. Mirrors get_ctx's plain
      `Eannot xs e` arm (Cannot-descent — taken only when e is NOT
      itself Eannot-rooted, because the double-annot arm precedes it;
      Core_reduction.lean:375) + apply_ctx's Cannot rebuild
      (Core_reduction.lean:389). The guard is load-bearing: without
      it this rule would race the ANNOTS merge, which the engine
      never does. -/
  | annot_ctx {a : List annot} {ds : List dyn_annotation} {b b' : CoreExpr}
      {σ σ' : Mem} :
      annotRooted b = false →
      Step (b, σ) (b', σ') →
      Step (Expr a (Eannot ds b), σ) (Expr a (Eannot ds b'), σ')
  /-- ANNOTS merge: `{A_1} {A_2} E --> {A_1 ++ A_2} E` (one_step0
      Eannot arm, Core_reduction.lean:353 "reduction: ANNOTS";
      combine_dyn_annotations = (++), :305-306; get_ctx routes every
      double-annot root here, :375; the double-annot value is
      explicitly NOT irreducible, :293 first arm). Unconditional on
      the body, exactly as the engine. -/
  | annot_merge {a1 a2 : List annot} {ds1 ds2 : List dyn_annotation}
      {b : CoreExpr} {σ : Mem} :
      Step (Expr a1 (Eannot ds1 (Expr a2 (Eannot ds2 b))), σ)
           (Expr (a1 ++ a2) (Eannot (ds1 ++ ds2) b), σ)

/-! ## Basic metatheory of Step (inversions the logic needs) -/

/-- Values do not step (the Language interface's `val_stuck`).
    Engine analogue: is_irreducible short-circuits both get_ctx and
    one_step0 (Core_reduction.lean:293,353,375). -/
theorem Step.val_elim {w : SpikeVal} {σ : Mem} {out : CoreExpr × Mem}
    (h : Step (ofVal w, σ) out) : False := by
  cases w with
  | pure v => cases h
  | annot ds v =>
    cases h with
    | annot_ctx hg hs => cases hs

theorem Step.toVal_none {e : CoreExpr} {σ : Mem} {out : CoreExpr × Mem}
    (h : Step (e, σ) out) : toVal e = none := by
  cases hv : toVal e with
  | none => rfl
  | some w => exact absurd (ofVal_of_toVal hv ▸ h) (fun h => h.val_elim)

/-- Inversion at a store redex: the step is unique and fully
    determined by the memM computation. -/
theorem Step.store_inv {a : List annot} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {lk : Bool} {ty : ctype}
    {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
    {σ : Mem} {out : CoreExpr × Mem}
    (h : Step (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Store0 lk (Pexpr [] () (PEval (Vctype ty)))
                       (Pexpr [] () (PEval (Vobject (OVpointer pv))))
                       (Pexpr [] () (PEval cv)) mo)))), σ) out) :
    ∃ mv fp σ',
      memValueFromValue fmapEmpty (Ctype [] (unatomic_ ty)) cv = some mv ∧
      applyMemM (CerbMem.storeM loc ty lk pv mv) σ = some (fp, σ') ∧
      out = (Expr [] (Eannot [DA_pos [] fp]
              (Expr [] (Epure (Pexpr [] () (PEval Vunit))))), σ') := by
  cases h with
  | store hmv hmem => exact ⟨_, _, _, hmv, hmem, rfl⟩

/-- Inversion at a load redex. -/
theorem Step.load_inv {a : List annot} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {ty : ctype} {pv : CerbMem.PointerValue}
    {mo : memory_order} {σ : Mem} {out : CoreExpr × Mem}
    (h : Step (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Load0 (Pexpr [] () (PEval (Vctype ty)))
                   (Pexpr [] () (PEval (Vobject (OVpointer pv)))) mo)))), σ)
          out) :
    ∃ fp mval σ',
      applyMemM (CerbMem.loadM loc ty pv) σ = some ((fp, mval), σ') ∧
      out = (Expr [] (Eannot [DA_pos [] fp]
              (Expr [] (Epure (Pexpr [] () (PEval
                (valueFromMemValue mval).2))))), σ') := by
  cases h with
  | load hmem => exact ⟨_, _, _, hmem, rfl⟩

/-- Inversion at a create redex. -/
theorem Step.create_inv {a : List annot} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {align : CerbMem.IntegerValue} {ty : ctype}
    {pref : prefix0} {σ : Mem} {out : CoreExpr × Mem}
    (h : Step (Expr a (Eaction (Paction polarity.Pos (Action loc ann
            (Create (Pexpr [] () (PEval (Vobject (OVinteger align))))
                    (Pexpr [] () (PEval (Vctype ty))) pref)))), σ) out) :
    ∃ pv σ',
      applyMemM (CerbMem.allocateObject 0 pref align ty none none) σ =
        some (pv, σ') ∧
      out = (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer pv))))), σ') := by
  cases h with
  | create hmem => exact ⟨_, _, hmem, rfl⟩

/-- Inversion at an Esseq node: either a frame step of e1, or one of
    the two betas (which require e1 to be a canonical value form). -/
theorem Step.sseq_inv {a : List annot} {pat : pattern} {e1 e2 : CoreExpr}
    {σ : Mem} {out : CoreExpr × Mem}
    (h : Step (Expr a (Esseq pat e1 e2), σ) out) :
    (∃ e1' σ', Step (e1, σ) (e1', σ') ∧
        out = (Expr a (Esseq pat e1' e2), σ')) ∨
    (∃ pa bty v, pat = Pattern pa (CaseBase (none, bty)) ∧
        e1 = ofVal (.pure v) ∧ out = (e2, σ)) ∨
    (∃ pa bty ds v, pat = Pattern pa (CaseBase (none, bty)) ∧
        e1 = ofVal (.annot ds v) ∧
        out = (Expr [] (Eannot ds e2), σ)) := by
  cases h with
  | sseq_ctx hs => exact .inl ⟨_, _, hs, rfl⟩
  | sseq_pure => exact .inr (.inl ⟨_, _, _, rfl, rfl, rfl⟩)
  | sseq_annot => exact .inr (.inr ⟨_, _, _, _, rfl, rfl, rfl⟩)

/-- Inversion at an Eannot node: Cannot-descent (non-annot-rooted
    body) or the ANNOTS merge (annot-rooted body). -/
theorem Step.annot_inv {a : List annot} {ds : List dyn_annotation}
    {b : CoreExpr} {σ : Mem} {out : CoreExpr × Mem}
    (h : Step (Expr a (Eannot ds b), σ) out) :
    (annotRooted b = false ∧ ∃ b' σ', Step (b, σ) (b', σ') ∧
        out = (Expr a (Eannot ds b'), σ')) ∨
    (∃ a2 ds2 c, b = Expr a2 (Eannot ds2 c) ∧
        out = (Expr (a ++ a2) (Eannot (ds ++ ds2) c), σ)) := by
  cases h with
  | annot_ctx hg hs => exact .inl ⟨hg, _, _, hs, rfl⟩
  | annot_merge => exact .inr ⟨_, _, _, rfl, rfl⟩

end CerberusHeapLang
