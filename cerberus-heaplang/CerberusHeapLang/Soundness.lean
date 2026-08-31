/-
CerberusHeapLang.Soundness — THE BOUNDARY MODULE: the only module
that references the engine's step machinery (`step_ctx`,
Core_reduction.lean:484); everything here certifies the
hand-written `Step` (Step.lean) against the engine at the frozen
minimal context.

WHAT IS PROVED (the certification direction, and why it suffices):

ENGINE-COMPLETENESS ON THE FRAGMENT, per construct: for every
fragment configuration (FragP below), the engine's step list at the
frozen context is a SINGLETON whose discharge (the Driver.lean:273
memM protocol, projected to (thread_state, MemState)) is matched by
Step — `engine_complete`:
  - a Step-matched successor (per-rule lemmas engineSteps_store /
    _load / _beta_pure / _beta_annot / _merge, plus the congruence
    closure get_ctx_decomp / Decomp.rebuild — one lemma per Step
    rule);
  - or the value protocol (engine_done / engine_remove_annot — the
    D1 readout composition: the engine taus `{A}v --> v` where Step
    treats `{A}v` as a value, then reports `Step_done2 v`);
  - or a REFUSAL (NDkilled / Step_error2) at a configuration where
    Step provably has NO step (`Decomp.step_factor` + the per-action
    inversions).

Why this direction suffices for adequacy (Adequacy.lean): the WP's
NotStuck obligation (proved against Step) guarantees every reachable
fragment configuration is a Step-value or Step-reducible; since the
engine's one behavior is either Step-matched (so it stays inside the
Step-reachable, WP-covered cone) or a refusal (which requires
Step-stuckness, contradicting NotStuck), the engine can never kill
and its final value is the one the WP's postcondition speaks about.
The soundness direction (every Step is engine-realizable) is NOT
needed for that statement and is not claimed; the active-path
equalities in the per-rule lemmas are exact (iff-grade on the
fragment), so nothing here relies on Step over-approximating.

THE DISCHARGE MIRROR (dischargeStep): Step_action_request2's request
monad is run on the frozen core_run_state and the request discharged
against the REAL CerbMem.loadM/storeM exactly as the sequential
driver does (action_request_sequential2, Driver.lean:273), with the
following projections, each cited:
  - `prefixOfPointer` is dropped: it is `memReturn none`
    (CerbMem.lean:2064) — state-invariant and never-killing, its
    result only enters the driver's trace;
  - the driver_state wrapper (trace events, fs, concurrency,
    dr_step_counter) is projected away — the fragment reads and
    writes only the thread_state and the MemState;
  - the aid drawn by perform_action_request2 (Driver.lean:284) is an
    arbitrary parameter here: the fragment's positive non-excluded
    continuations build `DA_pos [] fp` and ignore it (step_action,
    Core_reduction.lean:424; recorded finding D2,
    docs/2026-08-30_spike-sliceA-notes.md) — the per-rule lemmas
    hold for every aid.

FUEL HONESTY: the engine's get_ctx is fuel-bounded
(get_ctx_lemFuel, Core_reduction.lean:373, budget lemDefaultFuel =
10^6) and its exhaustion leaf is opaque (LemLib fuelExhausted —
deliberately not provably equal to anything). Every statement about
a symbolic configuration therefore carries an `esize e ≤
lemDefaultFuel` side condition; `esize` grows by at most 1 per step
(Step.esize_succ), so Adequacy.lean's drive statements carry
`esize e₀ + steps ≤ lemDefaultFuel`. This is an honest engine
artifact, not slack: past the budget the engine really does bail.
-/
import CerberusHeapLang.Step
import Core_reduction

set_option autoImplicit false

namespace CerberusHeapLang

/-! ## The frozen minimal context (measured by probe —
docs/2026-08-30_spike-recon.md §3.2)

tagDefs/extern empty (no structs, no linked externs in the
fragment), default file (only proc/impl lookups read it — the
fragment has none), tid 0, no parent thread, empty environment stack
(wildcard patterns never look anything up), and a hand-built
core_run_state (NEVER initial_core_run_state — that draws sym_supply
through an effectful seam, Core_run_aux.lean:395). -/

/-- The default (empty) Core file. Only proc/impl/funinfo lookups
    read it; the fragment performs none. -/
def spikeFile : generic_file Unit core_run_annotation := default

/-- The frozen thread state around an arena AND a live env stack
    (S1): empty stack, no current procedure. An explicit literal so
    that record updates of it reduce definitionally. -/
def envThread (e : CoreExpr) (ρ : EnvStack) : thread_state :=
  { arena := e, stack0 := Stack_empty, errno := default, env := ρ,
    current_proc_opt := none, exec_loc := default, current_loc := default }

/-- The frozen thread at the entry env (`spikeEnv` — one empty
    frame): the exported statements' launch profile. -/
def spikeThread (e : CoreExpr) : thread_state := envThread e spikeEnv

@[simp] theorem envThread_arena (e : CoreExpr) (ρ : EnvStack) :
    (envThread e ρ).arena = e := rfl

@[simp] theorem spikeThread_arena (e : CoreExpr) :
    (spikeThread e).arena = e := rfl

/-- The frozen core_run_state (Core_run_aux.lean:353-358). The
    fragment's request monads thread it; only the aid would reach a
    continuation, and the fragment's continuations ignore it (D2). -/
def spikeRunState : core_run_state :=
  { tid_supply := 1, aid_supply := 0, excluded_supply := 0, sym_supply := 0,
    labeled := fmapEmpty }

/-- THE ENGINE ENTRY: one expression-level step of the engine at the
    frozen context — `step_ctx` (Core_reduction.lean:484) verbatim.
    S1: the env stack is a parameter (live state). -/
def engineSteps (e : CoreExpr) (ρ : EnvStack) (σ : Mem) : List core_step2 :=
  step_ctx fmapEmpty σ spikeFile fmapEmpty 0 (none, envThread e ρ)

/-! ## The discharge (the Driver.lean:273 protocol, projected) -/

/-- One discharged engine behavior. `offFragment` marks core_step2
    forms the fragment never produces (`engine_complete` proves they
    arise, if at all, only where Step is stuck — on the fragment they
    do not arise at all, but that stronger fact is not needed). -/
inductive EngineOutcome : Type where
  | next (th : thread_state) (σ : Mem)
  | done (v : value)
  | killed (r : kill_reason mem_error)
  | error (s : String)
  | offFragment

/-- The engine refuses to continue: the killed channel (UB and
    non-UB kills alike, recon §2.6), an ILLTYPED report, or a
    non-fragment step form. -/
def EngineOutcome.isRefusal : EngineOutcome → Prop
  | .killed _ => True
  | .error _ => True
  | .offFragment => True
  | _ => False

/-- Discharge one core_step2 against the memory state — the
    sequential driver's protocol (action_request_sequential2,
    Driver.lean:273) projected to (thread_state, MemState); see the
    header for the three cited projections. The request monad is run
    on a QUANTIFIED core_run_state `rs` (the fragment's requests are
    `stExceptUndef_return`, so `rs` is returned verbatim — proved ∀ rs
    in the discharge lemmas; the run state is context, undisturbed);
    `aid` mirrors the driver's fresh action-id draw (Driver.lean:284),
    the one run-state component the real driver ticks
    (fresh_action_id', aid_supply + 1). -/
def dischargeStep (aid : Nat) (rs : core_run_state) (σ : Mem) :
    core_step2 → EngineOutcome
  | Step_tau2 _ _ th' => .next th' σ
  | Step_done2 v => .done v
  | Step_error2 s => .error s
  | Step_action_request2 _ loc _ _ m =>
    match m rs with
    | Result (Defined req, _) =>
      match req with
      | StoreRequest2 _mo ty lk pv mv k =>
        (match CerbMem.storeM loc ty lk pv mv with
         | ND f =>
           match f σ with
           | (NDactive fp, σ') => .next (k aid fp) σ'
           | (NDkilled r, _) => .killed r
           | _ => .offFragment)
      | LoadRequest2 _mo ty pv k =>
        (match CerbMem.loadM loc ty pv with
         | ND f =>
           match f σ with
           | (NDactive p, σ') => .next (k aid p.1 p.2) σ'
           | (NDkilled r, _) => .killed r
           | _ => .offFragment)
      | CreateRequest2 pref align ty reqAddr initOpt k =>
        -- Extension D: the driver's CreateRequest discharge
        -- (Driver.lean:273, `liftMem (CerbMem.allocateObject tid1 pref
        -- align_ival lvalue_ty req_addr_opt init_opt)`). allocateObject
        -- discards its tid argument (CerbMem.lean:1470, `_ : Nat`), so
        -- the projection passes 0; the payload's reqAddr/initOpt are
        -- threaded verbatim.
        (match CerbMem.allocateObject 0 pref align ty reqAddr initOpt with
         | ND f =>
           match f σ with
           | (NDactive pv, σ') => .next (k aid pv) σ'
           | (NDkilled r, _) => .killed r
           | _ => .offFragment)
      | _ => .offFragment
    | _ => .offFragment
  | Step_with_runstate2 _ m =>
    -- S3: the sequential driver's `liftCore_run` protocol
    -- (Driver.lean:245/336) projected: run the monad on the
    -- quantified run state; `Defined` continues, `Undef`/`Error`
    -- kill; a monad-level `Exception` is the driver's
    -- `Other (DErr_core_run …)` kill — off the fragment protocol
    -- here (the fragment's with-runstate monads never raise, proved
    -- ∀ rs in the per-rule discharge lemmas). The projection drops
    -- the returned run state; the fragment's monads return it
    -- verbatim (Erun's `labeled` read is `state_except_read` —
    -- READ-ONLY; guard/argument evaluation is `runEU`-lifted — the
    -- D14 partition rows, recorded in the slice notes).
    match m rs with
    | Result (Defined th', _) => .next th' σ
    | Result (Undef l ubs, _) => .killed (Undef0 l ubs)
    | Result (Error l s, _) => .killed (Error0 l s)
    | Exception _ => .offFragment
  | Step_memop_request2 loc mop cvals _ _ k =>
    -- List-reverse phase A: the sequential driver's memop discharge
    -- (driver21's Step_memop_request2 arm, Driver.lean:377 →
    -- perform_memop_request2, Driver.lean:288), projected exactly as
    -- the action requests above. The fragment mirrors ONE memop —
    -- PtrEq at pointer operands (`liftMem (CerbMem.eqPtrval loc
    -- ptr_val1 ptr_val2)`, continuation `mk_th_st (if is_eq then
    -- Vtrue else Vfalse)`); every other memop/operand shape is
    -- offFragment (fail-closed). The is_unseq_with_ccall flag is
    -- ignored exactly as driver21's arm ignores it (the multi-thread
    -- wakeup bookkeeping of advance_step, Driver.lean:336, is not
    -- part of the sequential projection). The differing-provenance
    -- `msum` fork of eqPtrval (CerbMem.lean:1753) is a real NDnd —
    -- not single-layer — and lands in offFragment.
    match mop, cvals with
    | PtrEq, [Vobject (OVpointer pv1), Vobject (OVpointer pv2)] =>
      (match CerbMem.eqPtrval loc pv1 pv2 with
       | ND f =>
         match f σ with
         | (NDactive b, σ') => .next (k (if b then Vtrue else Vfalse)) σ'
         | (NDkilled r, _) => .killed r
         | _ => .offFragment)
    | _, _ => .offFragment
  | _ => .offFragment

/-- The engine's discharged behavior list at a configuration. -/
def engineOutcomes (aid : Nat) (e : CoreExpr) (ρ : EnvStack) (σ : Mem) :
    List EngineOutcome :=
  (engineSteps e ρ σ).map (dischargeStep aid spikeRunState σ)

/-! ## The size measure (fuel accounting; see FUEL HONESTY above) -/

/-- Nesting depth of the sequencing/annotation spine — an upper
    bound for get_ctx's fuel use on the fragment. -/
def esize : CoreExpr → Nat
  | Expr _ (Esseq _ e1 e2) => 1 + max (esize e1) (esize e2)
  | Expr _ (Eannot _ b) => 1 + esize b
  | Expr _ (Eif _ e2 e3) => 1 + max (esize e2) (esize e3)
  | Expr _ (Esave _ _ body) => 1 + esize body
  | _ => 1

/-! ## The fragment cone

S3 NOTE: `FragP` (+ `fragP_ofVal`, `FragP.step`, and the env-
invariance survivor `Step.env_invariant_frag`) MOVED to Step.lean,
statements unchanged — Rules.lean needs the cone for the
FragP-scoped restatements forced by the pre-declared retirement of
the unconditional env invariance. -/

/-! ## Small facts about values and irreducibility -/

/-- Canonical redex spellings (the exact node shapes FragP.store/load
    range over; also the spellings Rules.lean's storeExpr/loadExpr
    produce). -/
def storeRedex (loc : CerbLocation.Loc) (ann : core_run_annotation) (lk : Bool)
    (ty : ctype) (pv : CerbMem.PointerValue) (cv : value) (mo : memory_order) :
    CoreExpr :=
  Expr [] (Eaction (Paction polarity.Pos (Action loc ann
    (Store0 lk (Pexpr [] () (PEval (Vctype ty)))
               (Pexpr [] () (PEval (Vobject (OVpointer pv))))
               (Pexpr [] () (PEval cv)) mo))))

def loadRedex (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (mo : memory_order) : CoreExpr :=
  Expr [] (Eaction (Paction polarity.Pos (Action loc ann
    (Load0 (Pexpr [] () (PEval (Vctype ty)))
           (Pexpr [] () (PEval (Vobject (OVpointer pv)))) mo))))

def createRedex (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (align : CerbMem.IntegerValue) (ty : ctype) (pref : prefix0) : CoreExpr :=
  Expr [] (Eaction (Paction polarity.Pos (Action loc ann
    (Create (Pexpr [] () (PEval (Vobject (OVinteger align))))
            (Pexpr [] () (PEval (Vctype ty))) pref))))

/-- `is_irreducible` (Core_reduction.lean:293) holds on both value
    forms. -/
theorem is_irreducible_ofVal (w : SpikeVal) : is_irreducible (ofVal w) = true := by
  cases w <;> rfl

@[simp] theorem is_irreducible_sseq {a : List annot} {pat : pattern}
    {e1 e2 : CoreExpr} :
    is_irreducible (Expr a (Esseq pat e1 e2)) = false := rfl

@[simp] theorem is_irreducible_action {a : List annot}
    {p : generic_paction core_run_annotation Unit sym} :
    is_irreducible (Expr a (Eaction p)) = false := rfl

/-- A value form under `toVal` is irreducible in the engine's sense. -/
theorem is_irreducible_of_toVal {e : CoreExpr} {w : SpikeVal}
    (h : toVal e = some w) : is_irreducible e = true := by
  rw [← ofVal_of_toVal h]; exact is_irreducible_ofVal w

/-! ## The redex classification and the decomposition judgment -/

/-- The fragment's root redexes: exactly the five shapes one engine
    step consumes at the hole. `merge` carries its irreducibility
    refutation (the shape is Eannot-rooted, so it is not a rfl fact
    at a symbolic body — it is discharged shape-by-shape when the
    decomposition is built, `FragP.decomp`). -/
inductive Redex : CoreExpr → Prop where
  | store {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
      {ty : ctype} {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
      (hlib : CerbLocation.isLibraryLocation loc = false) :
      Redex (storeRedex loc ann lk ty pv cv mo)
  | load {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
      {pv : CerbMem.PointerValue} {mo : memory_order}
      (hlib : CerbLocation.isLibraryLocation loc = false) :
      Redex (loadRedex loc ann ty pv mo)
  | create {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {align : CerbMem.IntegerValue} {ty : ctype} {pref : prefix0}
      (hlib : CerbLocation.isLibraryLocation loc = false) :
      Redex (createRedex loc ann align ty pref)
  | beta_pure {pa : List annot} {bty : core_base_type} {v : value} {e2 : CoreExpr} :
      Redex (Expr [] (Esseq (Pattern pa (CaseBase (none, bty))) (ofVal (.pure v)) e2))
  | beta_annot {pa : List annot} {bty : core_base_type}
      {ds : List dyn_annotation} {v : value} {e2 : CoreExpr} :
      Redex (Expr [] (Esseq (Pattern pa (CaseBase (none, bty))) (ofVal (.annot ds v)) e2))
  | merge {ds1 ds2 : List dyn_annotation} {b : CoreExpr}
      (hirr : is_irreducible (Expr [] (Eannot ds1 (Expr [] (Eannot ds2 b)))) = false) :
      Redex (Expr [] (Eannot ds1 (Expr [] (Eannot ds2 b))))

/-- The engine's context decomposition of a non-value fragment term,
    as a judgment: `Decomp e ctx r` says get_ctx (Core_reduction.lean:
    373-381) decomposes `e` into evaluation context `ctx` with root
    redex `r` (proved: `Decomp.get_ctx`). The `annot` layer carries
    (a) the non-annot-rooted-body guard (the same guard Step's
    annot_ctx rule carries — get_ctx's arm order routes annot-rooted
    bodies to the merge redex instead), (b) the node's irreducibility
    refutation, and (c) its one-layer get_ctx equation — all three
    are matcher facts about the body's head constructor, discharged
    shape-by-shape at construction (`FragP.decomp`). -/
inductive Decomp : CoreExpr → context → CoreExpr → Prop where
  | root {r : CoreExpr} : Redex r → Decomp r CTX r
  | sseq {pa : List annot} {bty : core_base_type} {e1 e2 : CoreExpr}
      {ctx : context} {r : CoreExpr} :
      Decomp e1 ctx r →
      Decomp (Expr [] (Esseq (Pattern pa (CaseBase (none, bty))) e1 e2))
             (Csseq [] (Pattern pa (CaseBase (none, bty))) ctx e2) r
  | annot {ds : List dyn_annotation} {b : CoreExpr} {ctx : context} {r : CoreExpr}
      (hroot : annotRooted b = false)
      (hirr : is_irreducible (Expr [] (Eannot ds b)) = false)
      (hmap : ∀ n : Nat,
        get_ctx_lemFuel (n+1) (Expr [] (Eannot ds b)) =
          List.map (fun p => (Cannot [] ds p.1, p.2)) (get_ctx_lemFuel n b)) :
      Decomp b ctx r → Decomp (Expr [] (Eannot ds b)) (Cannot [] ds ctx) r

/-- Any decomposed term is engine-reducible in shape. -/
theorem Decomp.not_irreducible {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (h : Decomp e ctx r) : is_irreducible e = false := by
  induction h with
  | root hr =>
    cases hr with
    | store hlib => rfl
    | load hlib => rfl
    | create hlib => rfl
    | beta_pure => rfl
    | beta_annot => rfl
    | merge hirr => exact hirr
  | sseq _ _ => rfl
  | annot _ hirr _ _ _ => exact hirr

/-- Fragment evaluation contexts (CTX/Csseq/Cannot chains) carry no
    unsequenced call: `is_unseq_with_ccall` (Core_reduction.lean:364-369)
    is false on every Decomp-produced context. (Extension D: the
    production driver's `can_advance` reads exactly this flag on
    action-request steps, Driver.lean:310.) -/
theorem Decomp.unseq_ccall_false {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (h : Decomp e ctx r) : is_unseq_with_ccall ctx = false := by
  have aux : ∀ {e' : CoreExpr} {ctx' : context} {r' : CoreExpr},
      Decomp e' ctx' r' → ∀ b : Bool, is_unseq_with_ccall_aux b ctx' = b := by
    intro e' ctx' r' h'
    induction h' with
    | root _ => intro b; rfl
    | sseq _ ih => intro b; simpa [is_unseq_with_ccall_aux] using ih b
    | annot _ _ _ _ ih => intro b; simpa [is_unseq_with_ccall_aux] using ih b
  unfold is_unseq_with_ccall
  exact aux h false

/-- Rebuild: `apply_ctx` (Core_reduction.lean:388) undoes the
    decomposition. -/
theorem Decomp.apply_eq {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (h : Decomp e ctx r) : apply_ctx ctx r = e := by
  induction h with
  | root _ => rfl
  | sseq _ ih => simpa [apply_ctx] using ih
  | annot _ _ _ _ ih => simpa [apply_ctx] using ih

/-- The phase-1 redex shapes carry no jump redex (S3: the guard
    facts the congruence certification feeds `Step.sseq_ctx`/
    `Step.annot_ctx`). -/
theorem Redex.jumpRedex?_none {r : CoreExpr} (h : Redex r) :
    jumpRedex? r = none := by
  cases h with
  | store hlib => rfl
  | load hlib => rfl
  | create hlib => rfl
  | beta_pure => rw [jumpRedex?_sseq, jumpRedex?_ofVal]
  | beta_annot => rw [jumpRedex?_sseq, jumpRedex?_ofVal]
  | merge hirr => exact jumpRedex?_annot_of_root _ _ rfl

/-- A term decomposing to a phase-1 redex has no jump redex — the
    decomposition and `jumpRedex?` walk the same leftmost path. -/
theorem Decomp.jumpRedex?_none {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (h : Decomp e ctx r) : jumpRedex? e = none := by
  induction h with
  | root hr => exact hr.jumpRedex?_none
  | sseq hd ih => rw [jumpRedex?_sseq]; exact ih
  | annot hroot hirr hmap hd ih =>
    rw [jumpRedex?_annot_of_not_root _ _ hroot]; exact ih

/-- Rebuild of a redex-step through the decomposition — certifies
    Step's two congruence rules (sseq_ctx / annot_ctx) against
    get_ctx-descent + apply_ctx-rebuild. (S3: the congruence guards
    are discharged by `Decomp.jumpRedex?_none` — the descent path
    holds a phase-1 redex, not a jump.) -/
theorem Decomp.rebuild {Q : LabelMap} {e : CoreExpr} {ctx : context}
    {r r' : CoreExpr}
    {ρ ρ' : EnvStack} {σ σ' : Mem} (h : Decomp e ctx r)
    (hs : Step Q (r, ρ, σ) (r', ρ', σ')) :
    Step Q (e, ρ, σ) (apply_ctx ctx r', ρ', σ') := by
  induction h with
  | root _ => exact hs
  | sseq hd ih => exact Step.sseq_ctx hd.jumpRedex?_none (ih hs)
  | annot hroot _ _ hd ih =>
    exact Step.annot_ctx hd.jumpRedex?_none hroot (ih hs)

/-- Factorization: every Step of a decomposed term is a Step of its
    redex, rebuilt. (The inversion direction of the congruence
    certification; with the per-redex inversions it converts engine
    refusals into global Step-stuckness. S3: the jump disjuncts of
    the node inversions are VACUOUS here — the decomposition holds a
    phase-1 redex, `Decomp.jumpRedex?_none` — so the phase-1
    statement survives; the jump-carrying factorization is
    `DecompJ.step_factor` below.) -/
theorem Decomp.step_factor {Q : LabelMap} {e : CoreExpr} {ctx : context}
    {r : CoreExpr}
    {ρ : EnvStack} {σ : Mem} {out : CoreExpr × EnvStack × Mem}
    (h : Decomp e ctx r) (hs : Step Q (e, ρ, σ) out) :
    ∃ r' ρ' σ', Step Q (r, ρ, σ) (r', ρ', σ') ∧
      out = (apply_ctx ctx r', ρ', σ') := by
  induction h generalizing out with
  | root _ => exact ⟨out.1, out.2.1, out.2.2, hs, rfl⟩
  | sseq hd ih =>
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
        ⟨_, _, v, _, _, _, he1, _, _⟩ | ⟨_, _, ds, v, _, _, _, he1, _, _⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, hpat, _, _, _⟩
    · obtain ⟨r', ρr, σr, hr, heq⟩ := ih hstep
      obtain ⟨he, hρ, hσ⟩ : e1' = apply_ctx _ r' ∧ ρ'' = ρr ∧ σ'' = σr := by
        simpa [Prod.mk.injEq] using heq
      subst he hρ hσ
      exact ⟨r', _, _, hr, by rw [hout]; rfl⟩
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
    · rw [hd.jumpRedex?_none] at hj
      cases hj
    · exact (specPat_ne_base hpat).elim
    · exact (specPat_ne_base hpat).elim
    · exact (symPat_ne_base hpat).elim
  | annot hroot _ _ hd ih =>
    rcases hs.annot_inv with ⟨_, hnj, b', ρ'', σ'', hstep, hout⟩ |
        ⟨a2, ds2, c, hb, _⟩ |
        ⟨l, pes, params, cont, vs, _, _, _, hj, _, _, _, _⟩
    · obtain ⟨r', ρr, σr, hr, heq⟩ := ih hstep
      obtain ⟨he, hρ, hσ⟩ : b' = apply_ctx _ r' ∧ ρ'' = ρr ∧ σ'' = σr := by
        simpa [Prod.mk.injEq] using heq
      subst he hρ hσ
      exact ⟨r', _, _, hr, by rw [hout]; rfl⟩
    · rw [hb] at hroot
      simp [annotRooted] at hroot
    · rw [hd.jumpRedex?_none] at hj
      cases hj

/-! ## esize bookkeeping -/

@[simp] theorem esize_sseq {a : List annot} {pat : pattern} {e1 e2 : CoreExpr} :
    esize (Expr a (Esseq pat e1 e2)) = 1 + max (esize e1) (esize e2) := rfl

@[simp] theorem esize_annot {a : List annot} {ds : List dyn_annotation}
    {b : CoreExpr} : esize (Expr a (Eannot ds b)) = 1 + esize b := rfl

theorem esize_pos (e : CoreExpr) : 1 ≤ esize e := by
  rcases e with ⟨a, e_⟩
  cases e_ <;> simp [esize] <;> omega

/-! ## get_ctx characterization (Core_reduction.lean:373-381)

One-layer unfold lemmas at each fragment shape, then the singleton
decomposition `Decomp.get_ctx`. Every lemma is about the FUELLED
worker at explicit fuel; `Decomp.get_ctx_default` instantiates the
production budget (get_ctx := get_ctx_lemFuel lemDefaultFuel,
Core_reduction.lean:381). -/

theorem get_ctx_ofVal (w : SpikeVal) (n : Nat) :
    get_ctx_lemFuel (n+1) (ofVal w) = [(CTX, ofVal w)] := by
  cases w <;> rfl

theorem get_ctx_sseq {a : List annot} {pat : pattern} {e1 e2 : CoreExpr}
    (h : is_irreducible e1 = false) (n : Nat) :
    get_ctx_lemFuel (n+1) (Expr a (Esseq pat e1 e2)) =
      List.map (fun p => (Csseq a pat p.1 e2, p.2)) (get_ctx_lemFuel n e1) := by
  rw [show get_ctx_lemFuel (n+1) (Expr a (Esseq pat e1 e2)) =
      (if is_irreducible e1 = true then [(CTX, Expr a (Esseq pat e1 e2))]
       else List.map (fun p => (Csseq a pat p.1 e2, p.2)) (get_ctx_lemFuel n e1))
    from rfl, h]
  rfl

theorem get_ctx_sseq_val {a : List annot} {pat : pattern} {w : SpikeVal}
    {e2 : CoreExpr} (n : Nat) :
    get_ctx_lemFuel (n+1) (Expr a (Esseq pat (ofVal w) e2)) =
      [(CTX, Expr a (Esseq pat (ofVal w) e2))] := by
  cases w <;> rfl

theorem get_ctx_action {a : List annot}
    {p : generic_paction core_run_annotation Unit sym} (n : Nat) :
    get_ctx_lemFuel (n+1) (Expr a (Eaction p)) = [(CTX, Expr a (Eaction p))] := rfl

theorem get_ctx_merge {a a2 : List annot} {ds1 ds2 : List dyn_annotation}
    {b : CoreExpr} (n : Nat) :
    get_ctx_lemFuel (n+1) (Expr a (Eannot ds1 (Expr a2 (Eannot ds2 b)))) =
      [(CTX, Expr a (Eannot ds1 (Expr a2 (Eannot ds2 b))))] := by
  rw [show get_ctx_lemFuel (n+1) (Expr a (Eannot ds1 (Expr a2 (Eannot ds2 b)))) =
      (if is_irreducible (Expr a (Eannot ds1 (Expr a2 (Eannot ds2 b)))) = true
       then [(CTX, Expr a (Eannot ds1 (Expr a2 (Eannot ds2 b))))]
       else [(CTX, Expr a (Eannot ds1 (Expr a2 (Eannot ds2 b))))]) from rfl]
  split <;> rfl

/-- The engine's singleton decomposition of a decomposed fragment
    term, at any sufficient fuel. -/
theorem Decomp.get_ctx_at {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (h : Decomp e ctx r) :
    ∀ n : Nat, esize e ≤ n → get_ctx_lemFuel n e = [(ctx, r)] := by
  induction h with
  | root hr =>
    intro n hn
    have h1 : 1 ≤ n := Nat.le_trans (esize_pos _) hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    cases hr with
    | store hlib => exact get_ctx_action m
    | load hlib => exact get_ctx_action m
    | create hlib => exact get_ctx_action m
    | beta_pure => exact get_ctx_sseq_val m
    | beta_annot => exact get_ctx_sseq_val m
    | merge hirr => exact get_ctx_merge m
  | sseq hd ih =>
    intro n hn
    rw [esize_sseq] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [get_ctx_sseq hd.not_irreducible m, ih m (by omega)]
    rfl
  | annot hroot hirr hmap hd ih =>
    intro n hn
    rw [esize_annot] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [hmap m, ih m (by omega)]
    rfl

/-- ... at the production budget. -/
theorem Decomp.get_ctx_default {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (h : Decomp e ctx r) (hsz : esize e ≤ lemDefaultFuel) :
    get_ctx e = [(ctx, r)] :=
  h.get_ctx_at lemDefaultFuel hsz

/-! ## The per-rule engine equations — CONTEXT UNDISTURBED
([USER 2026-08-30]: the theorem shape)

Each Step rule's engine mirror is stated with the machine's
NON-expression, non-memory configuration QUANTIFIED and returned
VERBATIM: the machine starts at ⟨heap, ctx⟩ and ends at ⟨heap', ctx⟩.
This is the machine-level locality/frame property — classical
lineage: the locality conditions of abstract separation logic
(Calcagno–O'Hearn–Yang), here proved of the ENGINE's own step
function per rule.

The three-way partition per component (recorded per rule in the
slice-B notes; the WF premises named below are exactly what the
engine code inspects):
- UNTOUCHED-UNREAD (quantified, verbatim, no premise): file,
  extern, thread_state's errno / current_proc_opt / exec_loc /
  stack (except PROGRAM-DONE) / current_loc (the fragment's `[]`
  node annotations keep get_loc = none, and `hlib` keeps the
  library-location substitution off — step_ctx's loc' let), the
  parent tid (except PROGRAM-DONE), and the memory σ for the pure
  taus.
- READ-ONLY-UNDER-WF (quantified, verbatim, premise named):
  tagDefs — read by the store rule only, at operand encoding
  (memValueFromValue, step_action Store0 arm,
  Core_reduction.lean:424); the premise is the encoding fact AT the
  quantified tagDefs. env — read by the two beta rules only
  (update_env, Core_aux.lean:868 fails loudly on an empty stack);
  the premise is nonemptiness, and the wildcard update is the
  identity (Core_aux.lean:861 first arm). stack0/parent — read by
  PROGRAM-DONE only (Stack_empty / no-parent select Step_done2 over
  RETURN / THREAD-DONE).
- TOUCHED (explicit in the transition): the arena (the expression)
  and, through the action requests' discharge, the MemState. tid is
  not state: it is copied verbatim into the request payload.
  step_ctx itself ticks no counter; the sequential driver's
  action-id draw (fresh_action_id', Driver.lean:284) ticks
  core_run_state.aid_supply per action — mirrored here by the
  quantified `aid` discharge parameter, while the request monad
  itself returns the run state verbatim (∀ rs, proved in the
  discharge lemmas).

`engineSteps_*` (the frozen-context forms the adequacy drive
launches from) are one-line corollaries of the `step_ctx_*` strong
forms. -/

/-! ### The extended redex/decomposition layer (S3)

`RedexJ`/`DecompJ` extend the phase-1 `Redex`/`Decomp` with the four
new root shapes (Esave / Eif / Ecase / Erun — all singleton `get_ctx`
roots, readiness §3 ND-collapse row). The phase-1 `Decomp` and its
lemmas stay VERBATIM (their jump disjuncts are vacuous —
`Decomp.jumpRedex?_none`); the jump-carrying factor theorem is
`DecompJ.step_factor` — the readiness's "factor theorem gains one
disjunct", with the disjunct saying the successor is the redex's OWN
successor, NOT rebuilt: the engine's context-discard as a theorem. -/

/-- Canonical new-root spellings. -/
def saveRedex (sb : sym × core_base_type)
    (ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)))
    (body : CoreExpr) : CoreExpr :=
  Expr [] (Esave sb ps body)

def ifRedex (g : generic_pexpr Unit sym) (e2 e3 : CoreExpr) : CoreExpr :=
  Expr [] (Eif g e2 e3)

def caseRedex (pe : generic_pexpr Unit sym)
    (pats : List (pattern × CoreExpr)) : CoreExpr :=
  Expr [] (Ecase pe pats)

def runRedex (ra : core_run_annotation) (l : sym)
    (pes : List (generic_pexpr Unit sym)) : CoreExpr :=
  Expr [] (Erun ra l pes)

inductive RedexJ : CoreExpr → Prop where
  | base {r : CoreExpr} : Redex r → RedexJ r
  | save (sb : sym × core_base_type)
      (ps : List (sym × ((core_base_type ×
        Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)))
      (body : CoreExpr) : RedexJ (saveRedex sb ps body)
  | if_ (g : generic_pexpr Unit sym) (e2 e3 : CoreExpr) :
      RedexJ (ifRedex g e2 e3)
  | case_ (pe : generic_pexpr Unit sym) (pats : List (pattern × CoreExpr)) :
      RedexJ (caseRedex pe pats)
  | run (ra : core_run_annotation) (l : sym)
      (pes : List (generic_pexpr Unit sym)) : RedexJ (runRedex ra l pes)
  | pure_e {pe : generic_pexpr Unit sym}
      (hnv : valueFromPexpr pe = none) : RedexJ (pureRedex pe)
  | load_op (loc : CerbLocation.Loc) (ann : core_run_annotation)
      (ty : ctype) {pe2 : generic_pexpr Unit sym} (mo : memory_order)
      (hnv2 : valueFromPexpr pe2 = none) :
      RedexJ (loadOpRedex loc ann ty pe2 mo)
  | beta_spec {pa pb : List annot} {x : sym} {bty : core_base_type}
      {w : SpikeVal} {e2 : CoreExpr} :
      RedexJ (Expr [] (Esseq (specPat pa pb x bty) (ofVal w) e2))
  | memop (mop : memop) (pes : List (generic_pexpr Unit sym)) :
      RedexJ (memopRedex mop pes)
  | store_op (loc : CerbLocation.Loc) (ann : core_run_annotation)
      (ty : ctype) {pe2 pe3 : generic_pexpr Unit sym} (mo : memory_order)
      (hnv2 : valueFromPexpr pe2 = none) :
      RedexJ (storeOpRedex loc ann ty pe2 pe3 mo)
  | beta_sym {pa : List annot} {x : sym} {bty : core_base_type}
      {w : SpikeVal} {e2 : CoreExpr} :
      RedexJ (Expr [] (Esseq (symPat pa x bty) (ofVal w) e2))

/-- The extended decomposition: the same three layers as `Decomp`
    (get_ctx's arm order), over the extended root set. -/
inductive DecompJ : CoreExpr → context → CoreExpr → Prop where
  | root {r : CoreExpr} : RedexJ r → DecompJ r CTX r
  | sseq {pa : List annot} {bty : core_base_type} {e1 e2 : CoreExpr}
      {ctx : context} {r : CoreExpr} :
      DecompJ e1 ctx r →
      DecompJ (Expr [] (Esseq (Pattern pa (CaseBase (none, bty))) e1 e2))
             (Csseq [] (Pattern pa (CaseBase (none, bty))) ctx e2) r
  | sseq_spec {pa pb : List annot} {x : sym} {bty : core_base_type}
      {e1 e2 : CoreExpr} {ctx : context} {r : CoreExpr} :
      DecompJ e1 ctx r →
      DecompJ (Expr [] (Esseq (specPat pa pb x bty) e1 e2))
             (Csseq [] (specPat pa pb x bty) ctx e2) r
  | sseq_sym {pa : List annot} {x : sym} {bty : core_base_type}
      {e1 e2 : CoreExpr} {ctx : context} {r : CoreExpr} :
      DecompJ e1 ctx r →
      DecompJ (Expr [] (Esseq (symPat pa x bty) e1 e2))
             (Csseq [] (symPat pa x bty) ctx e2) r
  | annot {ds : List dyn_annotation} {b : CoreExpr} {ctx : context}
      {r : CoreExpr}
      (hroot : annotRooted b = false)
      (hirr : is_irreducible (Expr [] (Eannot ds b)) = false)
      (hmap : ∀ n : Nat,
        get_ctx_lemFuel (n+1) (Expr [] (Eannot ds b)) =
          List.map (fun p => (Cannot [] ds p.1, p.2)) (get_ctx_lemFuel n b)) :
      DecompJ b ctx r → DecompJ (Expr [] (Eannot ds b)) (Cannot [] ds ctx) r

/-- The phase-1 decompositions embed. -/
theorem Decomp.toJ {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (h : Decomp e ctx r) : DecompJ e ctx r := by
  induction h with
  | root hr => exact .root (.base hr)
  | sseq _ ih => exact .sseq ih
  | annot hroot hirr hmap _ ih => exact .annot hroot hirr hmap ih

theorem RedexJ.not_irreducible {r : CoreExpr} (h : RedexJ r) :
    is_irreducible r = false := by
  cases h with
  | base hr =>
    cases hr with
    | store hlib => rfl
    | load hlib => rfl
    | create hlib => rfl
    | beta_pure => rfl
    | beta_annot => rfl
    | merge hirr => exact hirr
  | save sb ps body => rfl
  | if_ g e2 e3 => rfl
  | case_ pe pats => rfl
  | run ra l pes => rfl
  | @pure_e pe hnv =>
    rcases pe with ⟨b, u, pe_⟩
    cases u
    cases pe_ <;>
      first
      | rfl
      | (rw [valueFromPexpr_val] at hnv; cases hnv)
  | load_op loc ann ty mo hnv2 => rfl
  | beta_spec => rfl
  | memop mop pes => rfl
  | store_op loc ann ty mo hnv2 => rfl
  | beta_sym => rfl

theorem DecompJ.not_irreducible {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (h : DecompJ e ctx r) : is_irreducible e = false := by
  induction h with
  | root hr => exact hr.not_irreducible
  | sseq _ _ => rfl
  | sseq_spec _ _ => rfl
  | sseq_sym _ _ => rfl
  | annot _ hirr _ _ _ => exact hirr

theorem DecompJ.unseq_ccall_false {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (h : DecompJ e ctx r) : is_unseq_with_ccall ctx = false := by
  have aux : ∀ {e' : CoreExpr} {ctx' : context} {r' : CoreExpr},
      DecompJ e' ctx' r' → ∀ b : Bool, is_unseq_with_ccall_aux b ctx' = b := by
    intro e' ctx' r' h'
    induction h' with
    | root _ => intro b; rfl
    | sseq _ ih => intro b; simpa [is_unseq_with_ccall_aux] using ih b
    | sseq_spec _ ih => intro b; simpa [is_unseq_with_ccall_aux] using ih b
    | sseq_sym _ ih => intro b; simpa [is_unseq_with_ccall_aux] using ih b
    | annot _ _ _ _ ih => intro b; simpa [is_unseq_with_ccall_aux] using ih b
  unfold is_unseq_with_ccall
  exact aux h false

theorem DecompJ.apply_eq {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (h : DecompJ e ctx r) : apply_ctx ctx r = e := by
  induction h with
  | root _ => rfl
  | sseq _ ih => simpa [apply_ctx] using ih
  | sseq_spec _ ih => simpa [apply_ctx] using ih
  | sseq_sym _ ih => simpa [apply_ctx] using ih
  | annot _ _ _ _ ih => simpa [apply_ctx] using ih

/-- get_ctx roots at the new redexes (Core_reduction.lean:375 — Eif/
    Ecase/Esave/Erun all return `[(CTX, expr1)]`). -/
theorem get_ctx_save {sb : sym × core_base_type}
    {ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
    {body : CoreExpr} (n : Nat) :
    get_ctx_lemFuel (n+1) (saveRedex sb ps body) =
      [(CTX, saveRedex sb ps body)] := rfl

theorem get_ctx_if {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr} (n : Nat) :
    get_ctx_lemFuel (n+1) (ifRedex g e2 e3) = [(CTX, ifRedex g e2 e3)] := rfl

theorem get_ctx_case {pe : generic_pexpr Unit sym}
    {pats : List (pattern × CoreExpr)} (n : Nat) :
    get_ctx_lemFuel (n+1) (caseRedex pe pats) = [(CTX, caseRedex pe pats)] := rfl

theorem get_ctx_run {ra : core_run_annotation} {l : sym}
    {pes : List (generic_pexpr Unit sym)} (n : Nat) :
    get_ctx_lemFuel (n+1) (runRedex ra l pes) = [(CTX, runRedex ra l pes)] := rfl

theorem get_ctx_pure {pe : generic_pexpr Unit sym} (n : Nat) :
    get_ctx_lemFuel (n+1) (pureRedex pe) = [(CTX, pureRedex pe)] := by
  rcases pe with ⟨b, u, pe_⟩
  cases u
  cases pe_ <;> rfl

theorem get_ctx_memop {mop : memop} {pes : List (generic_pexpr Unit sym)}
    (n : Nat) :
    get_ctx_lemFuel (n+1) (memopRedex mop pes) =
      [(CTX, memopRedex mop pes)] := rfl

/-- The engine's singleton decomposition, extended roots. -/
theorem DecompJ.get_ctx_at {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (h : DecompJ e ctx r) :
    ∀ n : Nat, esize e ≤ n → get_ctx_lemFuel n e = [(ctx, r)] := by
  induction h with
  | @root r0 hr =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
      ⟨n - 1, by have := esize_pos r0; omega⟩
    cases hr with
    | base hb =>
      cases hb with
      | store hlib => exact get_ctx_action m
      | load hlib => exact get_ctx_action m
      | create hlib => exact get_ctx_action m
      | beta_pure => exact get_ctx_sseq_val m
      | beta_annot => exact get_ctx_sseq_val m
      | merge hirr => exact get_ctx_merge m
    | save sb ps body => exact get_ctx_save m
    | if_ g e2 e3 => exact get_ctx_if m
    | case_ pe pats => exact get_ctx_case m
    | run ra l pes => exact get_ctx_run m
    | pure_e hnv => exact get_ctx_pure m
    | load_op loc ann ty mo hnv2 => exact get_ctx_action m
    | beta_spec => exact get_ctx_sseq_val m
    | memop mop pes => exact get_ctx_memop m
    | store_op loc ann ty mo hnv2 => exact get_ctx_action m
    | beta_sym => exact get_ctx_sseq_val m
  | sseq hd ih =>
    intro n hn
    rw [esize_sseq] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [get_ctx_sseq hd.not_irreducible m, ih m (by omega)]
    rfl
  | sseq_spec hd ih =>
    intro n hn
    rw [esize_sseq] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [get_ctx_sseq hd.not_irreducible m, ih m (by omega)]
    rfl
  | sseq_sym hd ih =>
    intro n hn
    rw [esize_sseq] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [get_ctx_sseq hd.not_irreducible m, ih m (by omega)]
    rfl
  | annot hroot hirr hmap hd ih =>
    intro n hn
    rw [esize_annot] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [hmap m, ih m (by omega)]
    rfl

theorem DecompJ.get_ctx_default {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (h : DecompJ e ctx r) (hsz : esize e ≤ lemDefaultFuel) :
    get_ctx e = [(ctx, r)] :=
  h.get_ctx_at lemDefaultFuel hsz

/-- `jumpRedex?` along an extended decomposition: `some` exactly at
    a run redex. -/
theorem DecompJ.jumpRedex?_eq {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (h : DecompJ e ctx r) : jumpRedex? e = jumpRedex? r := by
  induction h with
  | root _ => rfl
  | sseq _ ih => rw [jumpRedex?_sseq]; exact ih
  | sseq_spec _ ih => rw [jumpRedex?_sseq]; exact ih
  | sseq_sym _ ih => rw [jumpRedex?_sseq]; exact ih
  | annot hroot _ _ _ ih =>
    rw [jumpRedex?_annot_of_not_root _ _ hroot]; exact ih

theorem DecompJ.redexJ {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (h : DecompJ e ctx r) : RedexJ r := by
  induction h with
  | root hr => exact hr
  | sseq _ ih => exact ih
  | sseq_spec _ ih => exact ih
  | sseq_sym _ ih => exact ih
  | annot _ _ _ _ ih => exact ih

/-- A redex with a positive jump-redex answer IS the run redex. -/
theorem RedexJ.jumpRedex?_some_inv {r : CoreExpr} {l : sym}
    {pes : List (generic_pexpr Unit sym)} (h : RedexJ r)
    (hj : jumpRedex? r = some (l, pes)) :
    ∃ ra : core_run_annotation, r = runRedex ra l pes := by
  cases h with
  | base hb => rw [hb.jumpRedex?_none] at hj; cases hj
  | save sb ps body => cases hj
  | if_ g e2 e3 => cases hj
  | case_ pe pats => cases hj
  | pure_e hnv => cases hj
  | load_op loc ann ty mo hnv2 => cases hj
  | beta_spec => rw [jumpRedex?_sseq, jumpRedex?_ofVal] at hj; cases hj
  | memop mop pes => cases hj
  | store_op loc ann ty mo hnv2 => cases hj
  | beta_sym => rw [jumpRedex?_sseq, jumpRedex?_ofVal] at hj; cases hj
  | run ra l' pes' =>
    obtain ⟨rfl, rfl⟩ : l' = l ∧ pes' = pes := by
      have := Option.some.inj hj
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    exact ⟨ra, rfl⟩


/-- PROGRAM-DONE, context undisturbed: at a bare value the engine
    reports the value. Reads exactly stack0 (`hstack`: an empty call
    stack selects PROGRAM-DONE over RETURN) and the parent slot
    (`none` selects it over THREAD-DONE). -/
theorem step_ctx_done (v : value)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (th : thread_state)
    (harena : th.arena = ofVal (.pure v))
    (hstack : th.stack0 = Stack_empty) :
    step_ctx tds σ file ext tid (none, th) = [Step_done2 v] := by
  have hget : get_ctx th.arena =
      [(CTX, Expr [] (Epure (Pexpr [] () (PEval v))))] := by
    rw [harena]; exact get_ctx_ofVal (.pure v) 999999
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  rw [hstack]

/-- REMOVE-ANNOT, context undisturbed: the engine taus off the
    one-layer annotation of a value (a VALUE for Step — D1). Nothing
    else is read. -/
theorem step_ctx_remove_annot (ds : List dyn_annotation) (v : value)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = ofVal (.annot ds v)) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_tau2 "CTX, Eannot(value)" TSK_Misc
        { th with arena := ofVal (.pure v) }] := by
  have hget : get_ctx th.arena =
      [(CTX, Expr [] (Eannot ds (Expr [] (Epure (Pexpr [] () (PEval v))))))] := by
    rw [harena]; exact get_ctx_ofVal (.annot ds v) 999999
  unfold step_ctx
  dsimp only
  rw [hget]
  rfl

/-- Store, active shape, context undisturbed: one StoreRequest2, the
    continuation rebuilds `{DA_pos [] fp} unit` in context with the
    whole thread context verbatim. tagDefs is READ (the operand
    encoding premise `hmv` is stated at the quantified tagDefs);
    `hlib` keeps current_loc unread. -/
theorem step_ctx_store {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
    {ty : ctype} {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
    {mv : CerbMem.MemValue}
    (hd : DecompJ e ctx (storeRedex loc ann lk ty pv cv mo))
    (hsz : esize e ≤ lemDefaultFuel)
    (hlib : CerbLocation.isLibraryLocation loc = false)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition))
    (hmv : memValueFromValue tds (Ctype [] (unatomic_ ty)) cv = some mv)
    (σ : Mem) (file : generic_file Unit core_run_annotation)
    (ext : Fmap sym sym) (tid : Nat) (parent : Option Nat)
    (th : thread_state) (harena : th.arena = e) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_action_request2 "StoreRequest" loc tid (is_unseq_with_ccall ctx)
        (stExceptUndef_return (StoreRequest2 mo ty lk pv mv
          (fun (_ : Nat) (fp : CerbMem.Footprint) =>
            { th with arena := apply_ctx ctx (Expr [] (Eannot [DA_pos [] fp]
                (Expr [] (Epure (Pexpr [] () (PEval Vunit)))))) })))] := by
  have hget : get_ctx th.arena = [(ctx, storeRedex loc ann lk ty pv cv mo)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold storeRedex
  cases ctx <;>
    (dsimp only [step_action, act_valueFromPexpr, valueFromPexpr]
     rw [hmv]
     dsimp only
     rw [hlib]
     rfl)

/-- Store, non-encoding shape, context undisturbed: ILLTYPED refusal
    (Step_error2). -/
theorem step_ctx_store_illtyped {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
    {ty : ctype} {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
    (hd : DecompJ e ctx (storeRedex loc ann lk ty pv cv mo))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition))
    (hmv : memValueFromValue tds (Ctype [] (unatomic_ ty)) cv = none)
    (σ : Mem) (file : generic_file Unit core_run_annotation)
    (ext : Fmap sym sym) (tid : Nat) (parent : Option Nat)
    (th : thread_state) (harena : th.arena = e) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_error2 (String.append (CerbLocation.stringFromLocation loc)
        (String.append "the value of a store("
          (String.append (CerbPP.stringFromCore_ctype (Ctype [] (unatomic_ ty)))
            (String.append ") didn't match the lvalue type: "
              (CerbPP.stringFromCore_value cv)))))] := by
  have hget : get_ctx th.arena = [(ctx, storeRedex loc ann lk ty pv cv mo)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold storeRedex
  cases ctx <;>
    (dsimp only [step_action, act_valueFromPexpr, valueFromPexpr]
     try rw [hmv]
     try rfl)

/-- Load, context undisturbed: one LoadRequest2; the continuation
    rebuilds the annotated decoded value in context, thread context
    verbatim. tagDefs is unread (Load0's operands classify without
    it; valueFromMemValue takes none). -/
theorem step_ctx_load {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pv : CerbMem.PointerValue} {mo : memory_order}
    (hd : DecompJ e ctx (loadRedex loc ann ty pv mo))
    (hsz : esize e ≤ lemDefaultFuel)
    (hlib : CerbLocation.isLibraryLocation loc = false)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat)
    (th : thread_state) (harena : th.arena = e) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_action_request2 "LoadRequest" loc tid (is_unseq_with_ccall ctx)
        (stExceptUndef_return (LoadRequest2 mo ty pv
          (fun (_ : Nat) (fp : CerbMem.Footprint) (mval : CerbMem.MemValue) =>
            { th with arena := apply_ctx ctx (Expr [] (Eannot [DA_pos [] fp]
                (Expr [] (Epure (Pexpr [] () (PEval
                  (valueFromMemValue mval).2)))))) })))] := by
  have hget : get_ctx th.arena = [(ctx, loadRedex loc ann ty pv mo)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold loadRedex
  cases ctx <;>
    (dsimp only [step_action, act_valueFromPexpr, valueFromPexpr]
     rw [hlib]
     rfl)

/-- Create, context undisturbed (Extension D): one CreateRequest2 with
    the canonical operands (which always classify — no ILLTYPED arm
    exists for this shape); the continuation rebuilds the BARE pointer
    value in context (mk_value_e, no Eannot residue — step_action
    Create arm, Core_reduction.lean:424), thread context verbatim.
    tagDefs is unread; `hlib` keeps current_loc unread. The request
    carries `get_with_address []` (the fragment's `[]` node annots) as
    the requested address — an opaque `partial def` value that
    `allocateObject` discards (CerbMem.lean:1473). -/
theorem step_ctx_create {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {align : CerbMem.IntegerValue} {ty : ctype} {pref : prefix0}
    (hd : DecompJ e ctx (createRedex loc ann align ty pref))
    (hsz : esize e ≤ lemDefaultFuel)
    (hlib : CerbLocation.isLibraryLocation loc = false)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat)
    (th : thread_state) (harena : th.arena = e) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_action_request2 "CreateRequest" loc tid (is_unseq_with_ccall ctx)
        (stExceptUndef_return (CreateRequest2 pref align ty
          (get_with_address []) none
          (fun (_ : Nat) (pv : CerbMem.PointerValue) =>
            { th with arena := apply_ctx ctx (Expr [] (Epure (Pexpr [] ()
                (PEval (Vobject (OVpointer pv)))))) })))] := by
  have hget : get_ctx th.arena = [(ctx, createRedex loc ann align ty pref)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold createRedex
  cases ctx <;>
    (dsimp only [step_action, act_valueFromPexpr, valueFromPexpr]
     rw [hlib]
     rfl)

/-- LETS-PURE, context undisturbed: env is READ-ONLY-UNDER-WF — the
    engine's update_env fails loudly on an empty stack (`henv`
    nonemptiness), and the wildcard update returns it verbatim
    (Core_aux.lean:861 first arm). -/
theorem step_ctx_beta_pure {e : CoreExpr} {ctx : context}
    {pa : List _root_.annot} {bty : core_base_type} {v : value} {e2 : CoreExpr}
    (hd : DecompJ e ctx
      (Expr [] (Esseq (Pattern pa (CaseBase (none, bty))) (ofVal (.pure v)) e2)))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    (henv : th.env = ev0 :: evs) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_tau2 "Esseq" TSK_Misc { th with arena := apply_ctx ctx e2 }] := by
  have hget : get_ctx th.arena =
      [(ctx, Expr [] (Esseq (Pattern pa (CaseBase (none, bty)))
        (ofVal (.pure v)) e2))] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  cases ctx <;>
    (simp only [one_step0, ofVal, is_irreducible_sseq, Bool.false_eq_true,
       if_false, valueFromPexpr]
     simp only [get_loc]
     dsimp only [update_env]
     rw [henv]
     dsimp only
     try rw [show ∀ cval, update_env_aux (a := sym)
         (Pattern pa (CaseBase (none, bty))) cval ev0 = ev0 from fun _ => rfl]
     try rw [← henv]
     try rfl)

/-- LETS-ANNOT, context undisturbed (same env discipline). -/
theorem step_ctx_beta_annot {e : CoreExpr} {ctx : context}
    {pa : List _root_.annot} {bty : core_base_type}
    {ds : List dyn_annotation} {v : value} {e2 : CoreExpr}
    (hd : DecompJ e ctx
      (Expr [] (Esseq (Pattern pa (CaseBase (none, bty)))
        (ofVal (.annot ds v)) e2)))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    (henv : th.env = ev0 :: evs) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_tau2 "Esseq Eannot" TSK_Misc
        { th with arena := apply_ctx ctx (Expr [] (Eannot ds e2)) }] := by
  have hget : get_ctx th.arena =
      [(ctx, Expr [] (Esseq (Pattern pa (CaseBase (none, bty)))
        (ofVal (.annot ds v)) e2))] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  cases ctx <;>
    (simp only [one_step0, ofVal, is_irreducible_sseq, Bool.false_eq_true,
       if_false, valueFromPexpr]
     simp only [get_loc]
     dsimp only [update_env]
     rw [henv]
     dsimp only
     try rw [show ∀ cval, update_env_aux (a := sym)
         (Pattern pa (CaseBase (none, bty))) cval ev0 = ev0 from fun _ => rfl]
     try rw [← henv]
     try rfl)

/-- ANNOTS merge, context undisturbed: env is returned verbatim with
    NO premise (one_step0's Eannot arm never touches it). -/
theorem step_ctx_merge {e : CoreExpr} {ctx : context}
    {ds1 ds2 : List dyn_annotation} {b : CoreExpr}
    (hd : DecompJ e ctx (Expr [] (Eannot ds1 (Expr [] (Eannot ds2 b)))))
    (hirr : is_irreducible (Expr [] (Eannot ds1 (Expr [] (Eannot ds2 b)))) = false)
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_tau2 "Eannot" TSK_Misc
        { th with arena := apply_ctx ctx (Expr [] (Eannot (ds1 ++ ds2) b)) }] := by
  have hget : get_ctx th.arena =
      [(ctx, Expr [] (Eannot ds1 (Expr [] (Eannot ds2 b))))] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  cases ctx <;>
    (dsimp only [one_step0]
     rw [hirr]
     rfl)

/-! ### The frozen-context corollaries (the adequacy drive's launch
profile: empty tagDefs/extern, default file, tid 0, no parent,
spikeThread) -/

theorem engineSteps_done (v : value) (ρ : EnvStack) (σ : Mem) :
    engineSteps (ofVal (.pure v)) ρ σ = [Step_done2 v] :=
  step_ctx_done v fmapEmpty σ spikeFile fmapEmpty 0 _ rfl rfl

theorem engineSteps_remove_annot (ds : List dyn_annotation) (v : value)
    (ρ : EnvStack) (σ : Mem) :
    engineSteps (ofVal (.annot ds v)) ρ σ =
      [Step_tau2 "CTX, Eannot(value)" TSK_Misc (envThread (ofVal (.pure v)) ρ)] :=
  step_ctx_remove_annot ds v fmapEmpty σ spikeFile fmapEmpty 0 none _ rfl

theorem engineSteps_store {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
    {ty : ctype} {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
    {mv : CerbMem.MemValue}
    (hd : DecompJ e ctx (storeRedex loc ann lk ty pv cv mo))
    (hsz : esize e ≤ lemDefaultFuel)
    (hlib : CerbLocation.isLibraryLocation loc = false)
    (hmv : memValueFromValue fmapEmpty (Ctype [] (unatomic_ ty)) cv = some mv)
    (ρ : EnvStack) (σ : Mem) :
    engineSteps e ρ σ =
      [Step_action_request2 "StoreRequest" loc 0 (is_unseq_with_ccall ctx)
        (stExceptUndef_return (StoreRequest2 mo ty lk pv mv
          (fun (_ : Nat) (fp : CerbMem.Footprint) =>
            envThread (apply_ctx ctx (Expr [] (Eannot [DA_pos [] fp]
              (Expr [] (Epure (Pexpr [] () (PEval Vunit))))))) ρ)))] :=
  step_ctx_store hd hsz hlib fmapEmpty hmv σ spikeFile fmapEmpty 0 none _ rfl

theorem engineSteps_store_illtyped {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
    {ty : ctype} {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
    (hd : DecompJ e ctx (storeRedex loc ann lk ty pv cv mo))
    (hsz : esize e ≤ lemDefaultFuel)
    (hmv : memValueFromValue fmapEmpty (Ctype [] (unatomic_ ty)) cv = none)
    (ρ : EnvStack) (σ : Mem) :
    engineSteps e ρ σ =
      [Step_error2 (String.append (CerbLocation.stringFromLocation loc)
        (String.append "the value of a store("
          (String.append (CerbPP.stringFromCore_ctype (Ctype [] (unatomic_ ty)))
            (String.append ") didn't match the lvalue type: "
              (CerbPP.stringFromCore_value cv)))))] :=
  step_ctx_store_illtyped hd hsz fmapEmpty hmv σ spikeFile fmapEmpty 0 none _ rfl

theorem engineSteps_load {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pv : CerbMem.PointerValue} {mo : memory_order}
    (hd : DecompJ e ctx (loadRedex loc ann ty pv mo))
    (hsz : esize e ≤ lemDefaultFuel)
    (hlib : CerbLocation.isLibraryLocation loc = false)
    (ρ : EnvStack) (σ : Mem) :
    engineSteps e ρ σ =
      [Step_action_request2 "LoadRequest" loc 0 (is_unseq_with_ccall ctx)
        (stExceptUndef_return (LoadRequest2 mo ty pv
          (fun (_ : Nat) (fp : CerbMem.Footprint) (mval : CerbMem.MemValue) =>
            envThread (apply_ctx ctx (Expr [] (Eannot [DA_pos [] fp]
              (Expr [] (Epure (Pexpr [] () (PEval
                (valueFromMemValue mval).2))))))) ρ)))] :=
  step_ctx_load hd hsz hlib fmapEmpty σ spikeFile fmapEmpty 0 none _ rfl

theorem engineSteps_create {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {align : CerbMem.IntegerValue} {ty : ctype} {pref : prefix0}
    (hd : DecompJ e ctx (createRedex loc ann align ty pref))
    (hsz : esize e ≤ lemDefaultFuel)
    (hlib : CerbLocation.isLibraryLocation loc = false)
    (ρ : EnvStack) (σ : Mem) :
    engineSteps e ρ σ =
      [Step_action_request2 "CreateRequest" loc 0 (is_unseq_with_ccall ctx)
        (stExceptUndef_return (CreateRequest2 pref align ty
          (get_with_address []) none
          (fun (_ : Nat) (pv : CerbMem.PointerValue) =>
            envThread (apply_ctx ctx
              (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer pv))))))) ρ))) ] :=
  step_ctx_create hd hsz hlib fmapEmpty σ spikeFile fmapEmpty 0 none _ rfl

theorem engineSteps_beta_pure {e : CoreExpr} {ctx : context}
    {pa : List _root_.annot} {bty : core_base_type} {v : value} {e2 : CoreExpr}
    (hd : DecompJ e ctx
      (Expr [] (Esseq (Pattern pa (CaseBase (none, bty))) (ofVal (.pure v)) e2)))
    (hsz : esize e ≤ lemDefaultFuel) (ev0 : Fmap sym value)
    (evs : List (Fmap sym value)) (σ : Mem) :
    engineSteps e (ev0 :: evs) σ =
      [Step_tau2 "Esseq" TSK_Misc (envThread (apply_ctx ctx e2) (ev0 :: evs))] :=
  step_ctx_beta_pure hd hsz fmapEmpty σ spikeFile fmapEmpty 0 none _ rfl rfl

theorem engineSteps_beta_annot {e : CoreExpr} {ctx : context}
    {pa : List _root_.annot} {bty : core_base_type} {ds : List dyn_annotation}
    {v : value} {e2 : CoreExpr}
    (hd : DecompJ e ctx
      (Expr [] (Esseq (Pattern pa (CaseBase (none, bty))) (ofVal (.annot ds v)) e2)))
    (hsz : esize e ≤ lemDefaultFuel) (ev0 : Fmap sym value)
    (evs : List (Fmap sym value)) (σ : Mem) :
    engineSteps e (ev0 :: evs) σ =
      [Step_tau2 "Esseq Eannot" TSK_Misc
        (envThread (apply_ctx ctx (Expr [] (Eannot ds e2))) (ev0 :: evs))] :=
  step_ctx_beta_annot hd hsz fmapEmpty σ spikeFile fmapEmpty 0 none _ rfl rfl

theorem engineSteps_merge {e : CoreExpr} {ctx : context}
    {ds1 ds2 : List dyn_annotation} {b : CoreExpr}
    (hd : DecompJ e ctx (Expr [] (Eannot ds1 (Expr [] (Eannot ds2 b)))))
    (hirr : is_irreducible (Expr [] (Eannot ds1 (Expr [] (Eannot ds2 b)))) = false)
    (hsz : esize e ≤ lemDefaultFuel) (ρ : EnvStack) (σ : Mem) :
    engineSteps e ρ σ =
      [Step_tau2 "Eannot" TSK_Misc
        (envThread (apply_ctx ctx (Expr [] (Eannot (ds1 ++ ds2) b))) ρ)] :=
  step_ctx_merge hd hirr hsz fmapEmpty σ spikeFile fmapEmpty 0 none _ rfl

/-! ## Discharge computation (the applyMemM bridge)

`dischargeStep` and Step's action rules consume the same one-level
memM application (`applyMemM`, Step.lean; sound for the fragment ops
because storeM/loadM are single-layer state transformers, recon
§2.3). These lemmas compute the discharge from the applyMemM verdict. -/

theorem dischargeStep_store_active {aid : Nat} {rs : core_run_state}
    {σ σ' : Mem} {str : String}
    {loc : CerbLocation.Loc} {tid : thread_id} {uw : Bool} {mo : memory_order}
    {ty : ctype} {lk : Bool} {pv : CerbMem.PointerValue} {mv : CerbMem.MemValue}
    {k : Nat → CerbMem.Footprint → thread_state} {fp : CerbMem.Footprint}
    (h : applyMemM (CerbMem.storeM loc ty lk pv mv) σ = some (fp, σ')) :
    dischargeStep aid rs σ (Step_action_request2 str loc tid uw
      (stExceptUndef_return (StoreRequest2 mo ty lk pv mv k))) =
      .next (k aid fp) σ' := by
  rcases hm : CerbMem.storeM loc ty lk pv mv with ⟨f⟩
  rcases hf : f σ with ⟨act, st⟩
  unfold applyMemM at h
  rw [hm] at h
  simp only [hf] at h
  unfold dischargeStep
  dsimp only [stExceptUndef_return, stExpect_return, return1, except_return]
  rw [hm]
  dsimp only
  rw [hf]
  cases act <;> simp only [] at h ⊢
  case NDactive x =>
    obtain ⟨rfl, rfl⟩ : x = fp ∧ st = σ' := by
      cases h; exact ⟨rfl, rfl⟩
    rfl
  all_goals cases h

theorem dischargeStep_store_refusal {aid : Nat} {rs : core_run_state}
    {σ : Mem} {str : String}
    {loc : CerbLocation.Loc} {tid : thread_id} {uw : Bool} {mo : memory_order}
    {ty : ctype} {lk : Bool} {pv : CerbMem.PointerValue} {mv : CerbMem.MemValue}
    {k : Nat → CerbMem.Footprint → thread_state}
    (h : applyMemM (CerbMem.storeM loc ty lk pv mv) σ = none) :
    (dischargeStep aid rs σ (Step_action_request2 str loc tid uw
      (stExceptUndef_return (StoreRequest2 mo ty lk pv mv k)))).isRefusal := by
  rcases hm : CerbMem.storeM loc ty lk pv mv with ⟨f⟩
  rcases hf : f σ with ⟨act, st⟩
  unfold applyMemM at h
  rw [hm] at h
  simp only [hf] at h
  unfold dischargeStep
  dsimp only [stExceptUndef_return, stExpect_return, return1, except_return]
  rw [hm]
  dsimp only
  rw [hf]
  cases act <;> simp only [] at h ⊢ <;> first | exact True.intro | cases h

theorem dischargeStep_load_active {aid : Nat} {rs : core_run_state}
    {σ σ' : Mem} {str : String}
    {loc : CerbLocation.Loc} {tid : thread_id} {uw : Bool} {mo : memory_order}
    {ty : ctype} {pv : CerbMem.PointerValue}
    {k : Nat → CerbMem.Footprint → CerbMem.MemValue → thread_state}
    {fp : CerbMem.Footprint} {mval : CerbMem.MemValue}
    (h : applyMemM (CerbMem.loadM loc ty pv) σ = some ((fp, mval), σ')) :
    dischargeStep aid rs σ (Step_action_request2 str loc tid uw
      (stExceptUndef_return (LoadRequest2 mo ty pv k))) =
      .next (k aid fp mval) σ' := by
  rcases hm : CerbMem.loadM loc ty pv with ⟨f⟩
  rcases hf : f σ with ⟨act, st⟩
  unfold applyMemM at h
  rw [hm] at h
  simp only [hf] at h
  unfold dischargeStep
  dsimp only [stExceptUndef_return, stExpect_return, return1, except_return]
  rw [hm]
  dsimp only
  rw [hf]
  cases act <;> simp only [] at h ⊢
  case NDactive x =>
    obtain ⟨rfl, rfl⟩ : x = (fp, mval) ∧ st = σ' := by
      cases h; exact ⟨rfl, rfl⟩
    rfl
  all_goals cases h

theorem dischargeStep_load_refusal {aid : Nat} {rs : core_run_state}
    {σ : Mem} {str : String}
    {loc : CerbLocation.Loc} {tid : thread_id} {uw : Bool} {mo : memory_order}
    {ty : ctype} {pv : CerbMem.PointerValue}
    {k : Nat → CerbMem.Footprint → CerbMem.MemValue → thread_state}
    (h : applyMemM (CerbMem.loadM loc ty pv) σ = none) :
    (dischargeStep aid rs σ (Step_action_request2 str loc tid uw
      (stExceptUndef_return (LoadRequest2 mo ty pv k)))).isRefusal := by
  rcases hm : CerbMem.loadM loc ty pv with ⟨f⟩
  rcases hf : f σ with ⟨act, st⟩
  unfold applyMemM at h
  rw [hm] at h
  simp only [hf] at h
  unfold dischargeStep
  dsimp only [stExceptUndef_return, stExpect_return, return1, except_return]
  rw [hm]
  dsimp only
  rw [hf]
  cases act <;> simp only [] at h ⊢ <;> first | exact True.intro | cases h

/-- allocateObject discards its thread-id and requested-address
    arguments (CerbMem.lean:1470-1474, `_`-binders): any two choices
    are definitionally the same operation. (The cheap SYMBOLIC bridge:
    at a concrete memory state, letting the elaborator discover this
    by whnf would evaluate the whole allocation — this equation keeps
    that off every proof path.) -/
theorem allocateObject_arg_irrel (tid tid' : Nat) (pref : prefix0)
    (align : CerbMem.IntegerValue) (ty : ctype) (r r' : Option Int)
    (init : Option CerbMem.MemValue) :
    CerbMem.allocateObject tid pref align ty r init =
      CerbMem.allocateObject tid' pref align ty r' init := rfl

theorem dischargeStep_create_active {aid : Nat} {rs : core_run_state}
    {σ σ' : Mem} {str : String}
    {loc : CerbLocation.Loc} {tid : thread_id} {uw : Bool}
    {pref : prefix0} {align : CerbMem.IntegerValue} {ty : ctype}
    {reqAddr : Option Int} {k : Nat → CerbMem.PointerValue → thread_state}
    {pv : CerbMem.PointerValue}
    (h : applyMemM (CerbMem.allocateObject 0 pref align ty reqAddr none) σ =
      some (pv, σ')) :
    dischargeStep aid rs σ (Step_action_request2 str loc tid uw
      (stExceptUndef_return (CreateRequest2 pref align ty reqAddr none k))) =
      .next (k aid pv) σ' := by
  rcases hm : CerbMem.allocateObject 0 pref align ty reqAddr none with ⟨f⟩
  rcases hf : f σ with ⟨act, st⟩
  unfold applyMemM at h
  rw [hm] at h
  simp only [hf] at h
  unfold dischargeStep
  dsimp only [stExceptUndef_return, stExpect_return, return1, except_return]
  rw [hm]
  dsimp only
  rw [hf]
  cases act <;> simp only [] at h ⊢
  case NDactive x =>
    obtain ⟨rfl, rfl⟩ : x = pv ∧ st = σ' := by
      cases h; exact ⟨rfl, rfl⟩
    rfl
  all_goals cases h

theorem dischargeStep_create_refusal {aid : Nat} {rs : core_run_state}
    {σ : Mem} {str : String}
    {loc : CerbLocation.Loc} {tid : thread_id} {uw : Bool}
    {pref : prefix0} {align : CerbMem.IntegerValue} {ty : ctype}
    {reqAddr : Option Int} {k : Nat → CerbMem.PointerValue → thread_state}
    (h : applyMemM (CerbMem.allocateObject 0 pref align ty reqAddr none) σ = none) :
    (dischargeStep aid rs σ (Step_action_request2 str loc tid uw
      (stExceptUndef_return (CreateRequest2 pref align ty reqAddr none k)))).isRefusal := by
  rcases hm : CerbMem.allocateObject 0 pref align ty reqAddr none with ⟨f⟩
  rcases hf : f σ with ⟨act, st⟩
  unfold applyMemM at h
  rw [hm] at h
  simp only [hf] at h
  unfold dischargeStep
  dsimp only [stExceptUndef_return, stExpect_return, return1, except_return]
  rw [hm]
  dsimp only
  rw [hf]
  cases act <;> simp only [] at h ⊢ <;> first | exact True.intro | cases h

/-! ## More esize equations -/

@[simp] theorem esize_pure {a : List annot} {pe : pexpr} :
    esize (Expr a (Epure pe)) = 1 := rfl

@[simp] theorem esize_action {a : List annot}
    {p : generic_paction core_run_annotation Unit sym} :
    esize (Expr a (Eaction p)) = 1 := rfl

@[simp] theorem esize_memop {a : List annot} {mop : memop}
    {pes : List (generic_pexpr Unit sym)} :
    esize (Expr a (Ememop mop pes)) = 1 := rfl

@[simp] theorem esize_ofVal_pure {v : value} : esize (ofVal (.pure v)) = 1 := rfl

@[simp] theorem esize_ofVal_annot {ds : List dyn_annotation} {v : value} :
    esize (ofVal (.annot ds v)) = 2 := rfl

/-- One Step grows the spine measure by at most one ON THE PHASE-1
    CONE (only the action rules grow it: a 1-node redex becomes a
    2-node annotated value). S3 RESTATEMENT (forced): the
    unconditional form is FALSE for the extended relation — a jump's
    successor is the registered continuation (arbitrary size; the R3
    reset), and the branch/entry rules surface subterms the phase-1
    `esize` did not measure. The FragP hypothesis scopes the lemma
    to its only use (the phase-1 drive classification); the
    jump-profile accounting is the J-lane's per-label bound. -/
theorem Step.esize_succ {Q : LabelMap} {e : CoreExpr} {ρ : EnvStack} {σ : Mem}
    {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem} (hf : FragP e)
    (h : Step Q (e, ρ, σ) (e', ρ', σ')) :
    esize e' ≤ esize e + 1 := by
  induction hf generalizing e' ρ' σ' with
  | val_pure v => exact (Step.val_elim (w := .pure v) h).elim
  | store hlib =>
    obtain ⟨mv, fp, σ'', hmv, hmem, hout⟩ := h.store_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    simp
  | load hlib =>
    obtain ⟨fp, mval, σ'', hmem, hout⟩ := h.load_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    simp
  | create hlib =>
    obtain ⟨pv, σ'', hmem, hout⟩ := h.create_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    simp
  | sseq hf1 hf2 ih1 ih2 =>
    rcases h.sseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
        ⟨_, _, v, _, _, _, _, _, hout⟩ | ⟨_, _, ds', v, _, _, _, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, hpat, _, _, _⟩
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      have := ih1 hstep
      simp at this ⊢
      omega
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      simp
      omega
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      simp
      omega
    · rw [hf1.jumpRedex?_none] at hj
      cases hj
    · exact (specPat_ne_base hpat).elim
    · exact (specPat_ne_base hpat).elim
    · exact (symPat_ne_base hpat).elim
  | annot hfb ihb =>
    rcases h.annot_inv with ⟨hg, hnj, b', ρ'', σ'', hstep, hout⟩ |
        ⟨a2, ds2, c, hb, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, _, hj, _, _, _, _⟩
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      have := ihb hstep
      simp at this ⊢
      omega
    · subst hb
      obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      simp
      omega
    · rw [hfb.jumpRedex?_none] at hj
      cases hj

/-! ## Existence of the decomposition on the fragment -/

theorem Decomp.redex {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (h : Decomp e ctx r) : Redex r := by
  induction h with
  | root hr => exact hr
  | sseq _ ih => exact ih
  | annot _ _ _ _ ih => exact ih

theorem Decomp.toVal_none {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (h : Decomp e ctx r) : toVal e = none := by
  cases hv : toVal e with
  | none => rfl
  | some w =>
    have := is_irreducible_of_toVal hv
    rw [h.not_irreducible] at this
    cases this

/-- Every non-value fragment configuration decomposes. -/
theorem FragP.decomp {e : CoreExpr} (hf : FragP e) (hnv : toVal e = none) :
    ∃ ctx r, Decomp e ctx r := by
  induction hf with
  | val_pure v =>
    rw [show toVal (Expr ([] : List _root_.annot) (Epure (Pexpr [] () (PEval v)))) =
      some (.pure v) from rfl] at hnv
    cases hnv
  | store hlib => exact ⟨_, _, Decomp.root (.store hlib)⟩
  | load hlib => exact ⟨_, _, Decomp.root (.load hlib)⟩
  | create hlib => exact ⟨_, _, Decomp.root (.create hlib)⟩
  | @sseq pa bty e1 e2 hf1 hf2 ih1 ih2 =>
    cases hv1 : toVal e1 with
    | some w =>
      have he1 := ofVal_of_toVal hv1
      subst he1
      cases w with
      | pure v => exact ⟨_, _, Decomp.root .beta_pure⟩
      | annot ds v => exact ⟨_, _, Decomp.root .beta_annot⟩
    | none =>
      obtain ⟨ctx, r, hd⟩ := ih1 hv1
      exact ⟨_, _, Decomp.sseq hd⟩
  | @annot ds b hfb ihb =>
    by_cases hr : annotRooted b = true
    · -- annot-rooted body: the whole node is the ANNOTS-merge redex
      cases hfb with
      | val_pure v => simp [annotRooted] at hr
      | store hlib => simp [annotRooted] at hr
      | load hlib => simp [annotRooted] at hr
      | create hlib => simp [annotRooted] at hr
      | sseq hf1 hf2 => simp [annotRooted] at hr
      | @annot ds2 c hfc =>
        -- irreducibility of the double-annot node: by the head shape
        -- of c (a fragment term)
        cases hfc with
        | val_pure v => exact ⟨_, _, Decomp.root (.merge rfl)⟩
        | store hlib => exact ⟨_, _, Decomp.root (.merge rfl)⟩
        | load hlib => exact ⟨_, _, Decomp.root (.merge rfl)⟩
        | create hlib => exact ⟨_, _, Decomp.root (.merge rfl)⟩
        | sseq hf1 hf2 => exact ⟨_, _, Decomp.root (.merge rfl)⟩
        | annot hfc' => exact ⟨_, _, Decomp.root (.merge rfl)⟩
    · have hr' : annotRooted b = false := by simpa using hr
      cases hvb : toVal b with
      | some w =>
        have hb := ofVal_of_toVal hvb
        subst hb
        cases w with
        | pure v =>
          rw [show toVal (Expr ([] : List _root_.annot) (Eannot ds (ofVal (.pure v)))) =
            some (.annot ds v) from rfl] at hnv
          cases hnv
        | annot ds2 v => simp [annotRooted, ofVal] at hr'
      | none =>
        obtain ⟨ctx, r, hd⟩ := ihb hvb
        -- the head of b is a non-value fragment shape: discharge the
        -- annot layer's matcher facts per shape
        cases hfb with
        | val_pure v =>
          rw [show toVal (Expr ([] : List _root_.annot) (Epure (Pexpr [] () (PEval v)))) =
            some (.pure v) from rfl] at hvb
          cases hvb
        | store hlib => exact ⟨_, _, Decomp.annot hr' rfl (fun n => rfl) hd⟩
        | load hlib => exact ⟨_, _, Decomp.annot hr' rfl (fun n => rfl) hd⟩
        | create hlib => exact ⟨_, _, Decomp.annot hr' rfl (fun n => rfl) hd⟩
        | sseq hf1 hf2 => exact ⟨_, _, Decomp.annot hr' rfl (fun n => rfl) hd⟩
        | annot hfc => simp [annotRooted] at hr'

/-! ## THE CERTIFICATION: engine-completeness on the fragment -/

/-- How one discharged engine behavior is matched by Step: a
    Step-transition, the value protocol (done / the D1 REMOVE-ANNOT
    tau), or a refusal at a provably Step-stuck configuration.
    S1: configurations carry the live env; the value protocol and
    refusals leave it untouched. -/
inductive EngineMatch (e : CoreExpr) (ρ : EnvStack) (σ : Mem) :
    EngineOutcome → Prop where
  | step {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem} :
      Step spikeLbl (e, ρ, σ) (e', ρ', σ') →
      EngineMatch e ρ σ (.next (envThread e' ρ') σ')
  | removeAnnot {ds : List dyn_annotation} {v : value} :
      e = ofVal (.annot ds v) →
      EngineMatch e ρ σ (.next (envThread (ofVal (.pure v)) ρ) σ)
  | done {v : value} : e = ofVal (.pure v) → EngineMatch e ρ σ (.done v)
  | refused {o : EngineOutcome} : o.isRefusal →
      (∀ out, ¬ Step spikeLbl (e, ρ, σ) out) → toVal e = none →
      EngineMatch e ρ σ o

/-- ENGINE-COMPLETENESS ON THE FRAGMENT (the artifact-4 theorem):
    at every fragment configuration, at any aid, memory state, and
    NONEMPTY env stack (the beta rules' one read — the empty-env
    channel is an engine panic, excluded by the cons shape), the
    engine has EXACTLY ONE behavior, and it is matched by Step. -/
theorem engine_complete (aid : Nat) (σ : Mem) (ev0 : Fmap sym value)
    (evs : List (Fmap sym value)) {e : CoreExpr}
    (hf : FragP e) (hsz : esize e ≤ lemDefaultFuel) :
    ∃ o, engineOutcomes aid e (ev0 :: evs) σ = [o] ∧
      EngineMatch e (ev0 :: evs) σ o := by
  cases hv : toVal e with
  | some w =>
    have he := ofVal_of_toVal hv
    subst he
    cases w with
    | pure v =>
      refine ⟨.done v, ?_, .done rfl⟩
      unfold engineOutcomes
      rw [engineSteps_done]
      rfl
    | annot ds v =>
      refine ⟨_, ?_, EngineMatch.removeAnnot rfl⟩
      unfold engineOutcomes
      rw [engineSteps_remove_annot]
      rfl
  | none =>
    obtain ⟨ctx, r, hd⟩ := hf.decomp hv
    have hred := hd.redex
    cases hred with
    | @store loc ann lk ty pv cv mo hlib =>
      cases hmv : memValueFromValue fmapEmpty (Ctype [] (unatomic_ ty)) cv with
      | none =>
        have heq := engineSteps_store_illtyped hd.toJ hsz hmv (ev0 :: evs) σ
        have hns : ∀ out, ¬ Step spikeLbl (e, ev0 :: evs, σ) out := by
          intro out hstep
          obtain ⟨r', ρ', σ', hr, _⟩ := hd.step_factor hstep
          obtain ⟨mv', _, _, hmv', _, _⟩ := hr.store_inv
          rw [hmv] at hmv'
          cases hmv'
        have hlist : engineOutcomes aid e (ev0 :: evs) σ =
            [EngineOutcome.error (String.append (CerbLocation.stringFromLocation loc)
              (String.append "the value of a store("
                (String.append (CerbPP.stringFromCore_ctype (Ctype [] (unatomic_ ty)))
                  (String.append ") didn't match the lvalue type: "
                    (CerbPP.stringFromCore_value cv)))))] := by
          unfold engineOutcomes
          rw [heq]
          rfl
        exact ⟨_, hlist, EngineMatch.refused True.intro hns hv⟩
      | some mv =>
        have heq := engineSteps_store hd.toJ hsz hlib hmv (ev0 :: evs) σ
        cases happ : applyMemM (CerbMem.storeM loc ty lk pv mv) σ with
        | some p =>
          rcases p with ⟨fp, σ'⟩
          refine ⟨_, ?_, EngineMatch.step (hd.rebuild
            (Step.store_canonical hmv happ))⟩
          unfold engineOutcomes
          rw [heq]
          simp only [List.map_cons, List.map_nil]
          rw [dischargeStep_store_active happ]
        | none =>
          have hns : ∀ out, ¬ Step spikeLbl (e, ev0 :: evs, σ) out := by
            intro out hstep
            obtain ⟨r', ρ', σ', hr, _⟩ := hd.step_factor hstep
            obtain ⟨mv', fp', σ'', hmv', happ', _⟩ := hr.store_inv
            rw [hmv] at hmv'
            obtain rfl : mv = mv' := Option.some.inj hmv'
            rw [happ] at happ'
            cases happ'
          refine ⟨dischargeStep aid spikeRunState σ (Step_action_request2 "StoreRequest" loc 0
              (is_unseq_with_ccall ctx) (stExceptUndef_return
                (StoreRequest2 mo ty lk pv mv
                  (fun (_ : Nat) (fp : CerbMem.Footprint) =>
                    envThread (apply_ctx ctx (Expr [] (Eannot [DA_pos [] fp]
                      (Expr [] (Epure (Pexpr [] () (PEval Vunit)))))))
                      (ev0 :: evs))))), ?_,
            EngineMatch.refused (dischargeStep_store_refusal happ) hns hv⟩
          unfold engineOutcomes
          rw [heq]
          rfl
    | @load loc ann ty pv mo hlib =>
      have heq := engineSteps_load hd.toJ hsz hlib (ev0 :: evs) σ
      cases happ : applyMemM (CerbMem.loadM loc ty pv) σ with
      | some p =>
        rcases p with ⟨⟨fp, mval⟩, σ'⟩
        refine ⟨_, ?_, EngineMatch.step (hd.rebuild (Step.load_canonical happ))⟩
        unfold engineOutcomes
        rw [heq]
        simp only [List.map_cons, List.map_nil]
        rw [dischargeStep_load_active happ]
      | none =>
        have hns : ∀ out, ¬ Step spikeLbl (e, ev0 :: evs, σ) out := by
          intro out hstep
          obtain ⟨r', ρ', σ', hr, _⟩ := hd.step_factor hstep
          obtain ⟨fp', mval', σ'', happ', _⟩ := hr.load_inv
          rw [happ] at happ'
          cases happ'
        refine ⟨dischargeStep aid spikeRunState σ (Step_action_request2 "LoadRequest" loc 0
            (is_unseq_with_ccall ctx) (stExceptUndef_return (LoadRequest2 mo ty pv
              (fun (_ : Nat) (fp : CerbMem.Footprint) (mval : CerbMem.MemValue) =>
                envThread (apply_ctx ctx (Expr [] (Eannot [DA_pos [] fp]
                  (Expr [] (Epure (Pexpr [] () (PEval
                    (valueFromMemValue mval).2)))))))
                  (ev0 :: evs))))), ?_,
          EngineMatch.refused (dischargeStep_load_refusal happ) hns hv⟩
        unfold engineOutcomes
        rw [heq]
        rfl
    | @create loc ann align ty pref hlib =>
      have heq := engineSteps_create hd.toJ hsz hlib (ev0 :: evs) σ
      cases happ : applyMemM (CerbMem.allocateObject 0 pref align ty none none) σ with
      | some p =>
        rcases p with ⟨pv, σ'⟩
        refine ⟨_, ?_, EngineMatch.step (hd.rebuild
          (Step.create_canonical happ))⟩
        unfold engineOutcomes
        rw [heq]
        simp only [List.map_cons, List.map_nil]
        rw [dischargeStep_create_active (reqAddr := get_with_address []) happ]
      | none =>
        have hns : ∀ out, ¬ Step spikeLbl (e, ev0 :: evs, σ) out := by
          intro out hstep
          obtain ⟨r', ρ', σ', hr, _⟩ := hd.step_factor hstep
          obtain ⟨pv', σ'', happ', _⟩ := hr.create_inv
          rw [happ] at happ'
          cases happ'
        refine ⟨dischargeStep aid spikeRunState σ (Step_action_request2 "CreateRequest" loc 0
            (is_unseq_with_ccall ctx) (stExceptUndef_return (CreateRequest2 pref align ty
              (get_with_address []) none
              (fun (_ : Nat) (pv : CerbMem.PointerValue) =>
                envThread (apply_ctx ctx (Expr [] (Epure
                  (Pexpr [] () (PEval (Vobject (OVpointer pv)))))))
                  (ev0 :: evs))))), ?_,
          EngineMatch.refused (dischargeStep_create_refusal (reqAddr := get_with_address []) happ)
            hns hv⟩
        unfold engineOutcomes
        rw [heq]
        rfl
    | @beta_pure pa bty v e2 =>
      have heq := engineSteps_beta_pure hd.toJ hsz ev0 evs σ
      refine ⟨_, ?_, EngineMatch.step (hd.rebuild Step.sseq_pure)⟩
      unfold engineOutcomes
      rw [heq]
      rfl
    | @beta_annot pa bty ds v e2 =>
      have heq := engineSteps_beta_annot hd.toJ hsz ev0 evs σ
      refine ⟨_, ?_, EngineMatch.step (hd.rebuild Step.sseq_annot)⟩
      unfold engineOutcomes
      rw [heq]
      rfl
    | @merge ds1 ds2 b hirr =>
      have heq := engineSteps_merge hd.toJ hirr hsz (ev0 :: evs) σ
      refine ⟨_, ?_, EngineMatch.step (hd.rebuild Step.annot_merge)⟩
      unfold engineOutcomes
      rw [heq]
      rfl

/-! ## S3 — THE JUMP-PROFILE CERTIFICATION

Everything below certifies the S3 mirror rules (Step.lean header
notes 3-5) against the engine: the pure-evaluator bridge into
`full_eval_pexpr` (the state-threaded evaluator all guard/argument
premises are certified against), the extended redex/decomposition
layer (`RedexJ`/`DecompJ` — the factor theorem WITH the jump
disjunct), the proc-carrying frozen profile (`procThread` — the
`current_proc_opt`/`labeled` reads Erun makes), the
`Step_with_runstate2` discharge arm (the sequential driver's
`liftCore_run` protocol, Driver.lean:245/336, projected), and the
per-construct engine equations. -/

/-! ### The pure-evaluator bridge

`PePure` is the operand sub-grammar the mirror evaluator covers
(value leaves, symbols, integer/boolean binops). `evalPexpr` success
implies membership (`evalPexpr_shape`), and on the sub-grammar the
engine's evaluation tower — `pull_constrained` (identity modulo
annotation renormalization), `step_eval_pexpr` (one full-depth
evaluation), `eval_pexpr_aux2` (one iteration), `full_eval_pexpr`
(one iteration, `runEU`-lifted, STATE-VERBATIM) — computes exactly
the mirror's answer. Fuel honesty: `peDepth` bounds every fuelled
layer; the side condition `peDepth pe ≤ lemDefaultFuel` is carried
explicitly (the engine's own budget; exhaustion is the opaque
`fuelExhausted` leaf). -/

/-- The covered operand sub-grammar. -/
inductive PePure : generic_pexpr Unit sym → Prop where
  | val (a : List annot) (v : value) : PePure (Pexpr a () (PEval v))
  | sym (a : List annot) (x : sym) : PePure (Pexpr a () (PEsym x))
  | op (a : List annot) (op : binop) {pe1 pe2 : generic_pexpr Unit sym} :
      PePure pe1 → PePure pe2 → PePure (Pexpr a () (PEop op pe1 pe2))
  | arrayShift (a : List annot) (ty : ctype)
      {pe1 pe2 : generic_pexpr Unit sym} :
      PePure pe1 → PePure pe2 → PePure (Pexpr a () (PEarray_shift pe1 ty pe2))

/-- Depth measure (bounds the per-level fuel draw of
    `step_eval_pexpr`/`pull_constrained`). -/
def peDepth : generic_pexpr Unit sym → Nat
  | Pexpr _ _ (PEop _ pe1 pe2) => 1 + max (peDepth pe1) (peDepth pe2)
  | Pexpr _ _ (PEarray_shift pe1 _ pe2) => 1 + max (peDepth pe1) (peDepth pe2)
  | _ => 1

@[simp] theorem peDepth_op (a : List annot) (op : binop)
    (pe1 pe2 : generic_pexpr Unit sym) :
    peDepth (Pexpr a () (PEop op pe1 pe2)) =
      1 + max (peDepth pe1) (peDepth pe2) := rfl

@[simp] theorem peDepth_array_shift (a : List annot) (ty : ctype)
    (pe1 pe2 : generic_pexpr Unit sym) :
    peDepth (Pexpr a () (PEarray_shift pe1 ty pe2)) =
      1 + max (peDepth pe1) (peDepth pe2) := rfl

theorem peDepth_pos (pe : generic_pexpr Unit sym) : 1 ≤ peDepth pe := by
  rcases pe with ⟨a, u, pe_⟩
  cases pe_ <;> simp [peDepth] <;> omega

theorem peDepth_sym_le (pb : List annot) (x : sym) :
    peDepth (Pexpr pb () (PEsym x)) ≤ lemDefaultFuel := by
  rw [show peDepth (Pexpr pb () (PEsym x)) = 1 from rfl,
    show lemDefaultFuel = 999999 + 1 from rfl]
  omega

theorem peDepth_val_le (a : List annot) (v : value) :
    peDepth (Pexpr a () (PEval v)) ≤ lemDefaultFuel := by
  rw [show peDepth (Pexpr a () (PEval v)) = 1 from rfl,
    show lemDefaultFuel = 999999 + 1 from rfl]
  omega

/-- Off-grammar shapes evaluate to nothing (fail-closed). -/
theorem evalPexpr_none_of_shape {ρ : EnvStack} {pe : generic_pexpr Unit sym}
    (hne1 : ∀ (a : List annot) (u : Unit) (v : value),
      pe = Pexpr a u (PEval v) → False)
    (hne2 : ∀ (a : List annot) (u : Unit) (x : sym),
      pe = Pexpr a u (PEsym x) → False)
    (hne3 : ∀ (a : List annot) (u : Unit) (op : binop)
      (pe1 pe2 : generic_pexpr Unit sym),
      pe = Pexpr a u (PEop op pe1 pe2) → False)
    (hne4 : ∀ (a : List annot) (u : Unit)
      (pe1 : generic_pexpr Unit sym) (ty : ctype)
      (pe2 : generic_pexpr Unit sym),
      pe = Pexpr a u (PEarray_shift pe1 ty pe2) → False) :
    evalPexpr ρ pe = none := by
  unfold evalPexpr
  split
  · exact absurd rfl (hne1 _ _ _)
  · exact absurd rfl (hne2 _ _ _)
  · exact absurd rfl (hne3 _ _ _ _ _)
  · exact absurd rfl (hne4 _ _ _ _ _)
  · rfl

/-- Mirror success implies the covered shape. -/
theorem evalPexpr_shape {ρ : EnvStack} {pe : generic_pexpr Unit sym} {v : value}
    (h : evalPexpr ρ pe = some v) : PePure pe := by
  revert h
  revert v
  induction pe using evalPexpr.induct with
  | case1 a u v' => intro v h; exact .val a v'
  | case2 a u x => intro v h; exact .sym a x
  | case3 a u op pe1 pe2 ih1 ih2 =>
    intro v h
    rw [evalPexpr_op] at h
    cases h1 : evalPexpr ρ pe1 with
    | none => rw [h1] at h; cases h
    | some v1 =>
      cases h2 : evalPexpr ρ pe2 with
      | none => rw [h1, h2] at h; cases h
      | some v2 => exact .op a op (ih1 h1) (ih2 h2)
  | case4 a u pe1 ty pe2 ih1 ih2 =>
    intro v h
    rw [evalPexpr_array_shift] at h
    cases h1 : evalPexpr ρ pe1 with
    | none => rw [h1] at h; cases h
    | some v1 =>
      cases h2 : evalPexpr ρ pe2 with
      | none => rw [h1, h2] at h; cases h
      | some v2 => exact .arrayShift a ty (ih1 h1) (ih2 h2)
  | case5 pe hne1 hne2 hne3 hne4 =>
    intro v h
    rw [evalPexpr_none_of_shape hne1 hne2 hne3 hne4] at h
    cases h

/-- LEVEL 1 of the bridge: `step_eval_pexpr` (Core_eval.lean:142)
    computes the mirror's answer in ONE call — it recurses full-depth
    through `PEop` operands itself. Quantified over the level counter
    `n` (the engine ticks it per operand level), tagDefs, locations,
    the memory state, and the file (all UNREAD on the covered
    grammar); the extern map is pinned to the frozen `fmapEmpty`
    (`PEsym`'s indirection is then the identity fallback). -/
theorem step_eval_bridge {ρ : EnvStack} {pe : generic_pexpr Unit sym}
    {v : value} (hp : PePure pe) (hv : evalPexpr ρ pe = some v) :
    ∀ (fuel : Nat), peDepth pe ≤ fuel →
    ∀ (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (n : Nat)
      (loc : CerbLocation.Loc) (cloc : Option CerbLocation.Loc)
      (mem : Option CerbMem.MemState)
      (file : generic_file Unit core_run_annotation),
    step_eval_pexpr_lemFuel fuel tds n loc cloc fmapEmpty ρ mem file false pe =
      exception_undef_return (Pexpr [] () (PEval v)) := by
  induction hp generalizing v with
  | val a v' =>
    intro fuel hfuel tds n loc cloc mem file
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 :=
      ⟨fuel - 1, by have := peDepth_pos (Pexpr a () (PEval v')); omega⟩
    obtain rfl : v' = v := by simpa using hv
    rfl
  | sym a x =>
    intro fuel hfuel tds n loc cloc mem file
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 :=
      ⟨fuel - 1, by have := peDepth_pos (Pexpr a () (PEsym x)); omega⟩
    have hx : lookup_env x ρ = some v := by simpa using hv
    show exception_undef_fmap (Pexpr [] ()) _ = _
    dsimp only
    rw [show (fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
        Lem_Basic_classes.ordCompare s1 s2) x
        (fmapEmpty (α := sym) (β := sym))) = none from rfl]
    dsimp only
    rw [hx]
    rfl
  | @op a op pe1 pe2 hp1 hp2 ih1 ih2 =>
    intro fuel hfuel tds n loc cloc mem file
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    rw [evalPexpr_op] at hv
    obtain ⟨v1, h1, v2, h2, hb⟩ : ∃ v1, evalPexpr ρ pe1 = some v1 ∧
        ∃ v2, evalPexpr ρ pe2 = some v2 ∧ evalBinop op v1 v2 = some v := by
      cases h1 : evalPexpr ρ pe1 with
      | none => rw [h1] at hv; cases hv
      | some v1 =>
        cases h2 : evalPexpr ρ pe2 with
        | none => rw [h1, h2] at hv; cases hv
        | some v2 =>
          rw [h1, h2] at hv
          exact ⟨v1, rfl, v2, rfl, hv⟩
    have hd1 : peDepth pe1 ≤ f := by simp at hfuel; omega
    have hd2 : peDepth pe2 ≤ f := by simp at hfuel; omega
    show exception_undef_fmap (Pexpr [] ()) _ = _
    dsimp only [step_eval_peop]
    rw [ih1 h1 f hd1 tds (n+1) loc cloc mem file,
      ih2 h2 f hd2 tds (n+1) loc cloc mem file]
    dsimp only [exception_undef_bind, exception_undef_return,
      exception_undef_fmap, valueFromPexpr]
    -- the binop dispatch: split the MIRROR's equation into its
    -- compiled arms; in each arm operands and operator are concrete
    -- and the ENGINE's dispatch computes
    unfold evalBinop at hb
    split at hb <;>
      first
      | (cases hb; rfl)
      | (rename_i hlt
         first
         | (cases hcmp : CerbMem.eqIval _ _ <;> rw [hcmp] at hb <;>
             simp only [Option.map_some, Option.map_none] at hb <;>
             first
             | cases hb
             | (obtain rfl := hb.symm; rfl))
         | (cases hcmp : CerbMem.ltIval _ _ <;> rw [hcmp] at hb <;>
             simp only [Option.map_some, Option.map_none] at hb <;>
             first
             | cases hb
             | (obtain rfl := hb.symm; rfl))
         | (cases hcmp : CerbMem.leIval _ _ <;> rw [hcmp] at hb <;>
             simp only [Option.map_some, Option.map_none] at hb <;>
             first
             | cases hb
             | (obtain rfl := hb.symm; rfl)))
      | cases hb
  | @arrayShift a ty pe1 pe2 hp1 hp2 ih1 ih2 =>
    intro fuel hfuel tds n loc cloc mem file
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    rw [evalPexpr_array_shift] at hv
    obtain ⟨v1, h1, v2, h2, hb⟩ : ∃ v1, evalPexpr ρ pe1 = some v1 ∧
        ∃ v2, evalPexpr ρ pe2 = some v2 ∧ evalArrayShift ty v1 v2 = some v := by
      cases h1 : evalPexpr ρ pe1 with
      | none => rw [h1] at hv; cases hv
      | some v1 =>
        cases h2 : evalPexpr ρ pe2 with
        | none => rw [h1, h2] at hv; cases hv
        | some v2 =>
          rw [h1, h2] at hv
          exact ⟨v1, rfl, v2, rfl, hv⟩
    have hd1 : peDepth pe1 ≤ f := by simp at hfuel; omega
    have hd2 : peDepth pe2 ≤ f := by simp at hfuel; omega
    show exception_undef_fmap (Pexpr [] ()) _ = _
    dsimp only
    rw [ih1 h1 f hd1 tds (n+1) loc cloc mem file,
      ih2 h2 f hd2 tds (n+1) loc cloc mem file]
    dsimp only [exception_undef_bind, exception_undef_return,
      exception_undef_fmap, valueFromPexpr]
    unfold evalArrayShift at hb
    split at hb
    · cases hb; rfl
    · cases hb

/-- The constrained-pull's image on the covered grammar: annotation
    renormalization only (`pull_constrained` rebuilds every node
    with `[]` annots; no `PEconstrained` exists to pull). -/
def peStrip : generic_pexpr Unit sym → generic_pexpr Unit sym
  | Pexpr _ _ (PEop op pe1 pe2) => Pexpr [] () (PEop op (peStrip pe1) (peStrip pe2))
  | Pexpr _ _ (PEarray_shift pe1 ty pe2) =>
      Pexpr [] () (PEarray_shift (peStrip pe1) ty (peStrip pe2))
  | Pexpr _ _ pex => Pexpr [] () pex

theorem PePure.strip {pe : generic_pexpr Unit _root_.sym} (hp : PePure pe) :
    PePure (peStrip pe) := by
  induction hp with
  | val a v => exact .val [] v
  | sym a x => exact .sym [] x
  | op a op hp1 hp2 ih1 ih2 => exact .op [] op ih1 ih2
  | arrayShift a ty hp1 hp2 ih1 ih2 => exact .arrayShift [] ty ih1 ih2

theorem evalPexpr_peStrip {ρ : EnvStack} {pe : generic_pexpr Unit sym}
    (hp : PePure pe) : evalPexpr ρ (peStrip pe) = evalPexpr ρ pe := by
  induction hp with
  | val a v => rfl
  | sym a x => rfl
  | op a op hp1 hp2 ih1 ih2 =>
    show evalPexpr ρ (Pexpr [] () (PEop op _ _)) = _
    rw [evalPexpr_op, evalPexpr_op, ih1, ih2]
  | arrayShift a ty hp1 hp2 ih1 ih2 =>
    show evalPexpr ρ (Pexpr [] () (PEarray_shift _ ty _)) = _
    rw [evalPexpr_array_shift, evalPexpr_array_shift, ih1, ih2]

theorem peDepth_peStrip {pe : generic_pexpr Unit sym} (hp : PePure pe) :
    peDepth (peStrip pe) = peDepth pe := by
  induction hp with
  | val a v => rfl
  | sym a x => rfl
  | op a op hp1 hp2 ih1 ih2 =>
    show peDepth (Pexpr [] () (PEop op _ _)) = _
    rw [peDepth_op, peDepth_op, ih1, ih2]
  | arrayShift a ty hp1 hp2 ih1 ih2 =>
    show peDepth (Pexpr [] () (PEarray_shift _ ty _)) = _
    rw [peDepth_array_shift, peDepth_array_shift, ih1, ih2]

/-- LEVEL 2: `pull_constrained` (Core_eval.lean:126) is annotation
    renormalization on the covered grammar. -/
theorem pull_bridge {pe : generic_pexpr Unit sym} (hp : PePure pe) :
    ∀ (fuel : Nat), peDepth pe ≤ fuel → ∀ (n : Nat),
    pull_constrained_lemFuel fuel n pe = peStrip pe := by
  induction hp with
  | val a v =>
    intro fuel hfuel n
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 :=
      ⟨fuel - 1, by have := peDepth_pos (Pexpr a () (PEval v)); omega⟩
    rfl
  | sym a x =>
    intro fuel hfuel n
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 :=
      ⟨fuel - 1, by have := peDepth_pos (Pexpr a () (PEsym x)); omega⟩
    rfl
  | @op a op pe1 pe2 hp1 hp2 ih1 ih2 =>
    intro fuel hfuel n
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hd1 : peDepth pe1 ≤ f := by simp at hfuel; omega
    have hd2 : peDepth pe2 ≤ f := by simp at hfuel; omega
    show Pexpr [] () _ = _
    dsimp only
    rw [ih1 f hd1 (n+1), ih2 f hd2 (n+1)]
    cases hp1 <;> cases hp2 <;> rfl
  | @arrayShift a ty pe1 pe2 hp1 hp2 ih1 ih2 =>
    intro fuel hfuel n
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hd1 : peDepth pe1 ≤ f := by simp at hfuel; omega
    have hd2 : peDepth pe2 ≤ f := by simp at hfuel; omega
    show Pexpr [] () _ = _
    dsimp only
    rw [ih1 f hd1 (n+1), ih2 f hd2 (n+1)]
    cases hp1 <;> cases hp2 <;> rfl

/-- LEVEL 3a: `eval_pexpr_aux2` (Core_eval.lean:152) computes the
    mirror's answer in ONE iteration on the covered grammar (pull,
    then one full-depth `step_eval`, then the value test succeeds).
    The engine's own budget: `peDepth pe ≤ lemDefaultFuel` (the
    interior `pull_constrained`/`step_eval_pexpr` run at the default
    budget; the iteration fuel needs only one unfold). -/
theorem aux2_bridge {ρ : EnvStack} {pe : generic_pexpr Unit sym} {v : value}
    (hp : PePure pe) (hv : evalPexpr ρ pe = some v)
    (hd : peDepth pe ≤ lemDefaultFuel) :
    ∀ (fuel : Nat)
      (tds : Fmap sym (CerbLocation.Loc × tag_definition))
      (loc : CerbLocation.Loc) (cloc : Option CerbLocation.Loc)
      (mem : Option CerbMem.MemState)
      (file : generic_file Unit core_run_annotation),
    eval_pexpr_aux2_lemFuel (fuel + 1) tds loc cloc fmapEmpty ρ mem file pe =
      exception_undef_return (Sum.inr v) := by
  intro fuel tds loc cloc mem file
  have hpull : pull_constrained 0 pe = peStrip pe :=
    pull_bridge hp lemDefaultFuel hd 0
  have hstep := step_eval_bridge hp.strip
    (by rw [evalPexpr_peStrip hp]; exact hv) lemDefaultFuel
    (by rw [peDepth_peStrip hp]; exact hd) tds 0 loc cloc mem file
  unfold eval_pexpr_aux2_lemFuel
  dsimp only [CerbDebug.print_debug_pure]
  rw [hpull]
  cases hp with
  | val a v' =>
    rw [show peStrip (Pexpr a () (PEval v')) = Pexpr [] () (PEval v') from rfl]
    rw [show peStrip (Pexpr a () (PEval v')) = Pexpr [] () (PEval v')
      from rfl] at hstep
    dsimp only
    rw [show step_eval_pexpr = step_eval_pexpr_lemFuel lemDefaultFuel from rfl,
      hstep]
    dsimp only [exception_undef_bind, exception_undef_return, valueFromPexpr]
    obtain rfl : v' = v := by simpa using hv
    rfl
  | sym a x =>
    rw [show peStrip (Pexpr a () (PEsym x)) = Pexpr [] () (PEsym x) from rfl]
    rw [show peStrip (Pexpr a () (PEsym x)) = Pexpr [] () (PEsym x)
      from rfl] at hstep
    dsimp only
    rw [show step_eval_pexpr = step_eval_pexpr_lemFuel lemDefaultFuel from rfl,
      hstep]
    rfl
  | @op a op pe1 pe2 hp1 hp2 =>
    rw [show peStrip (Pexpr a () (PEop op pe1 pe2)) =
      Pexpr [] () (PEop op (peStrip pe1) (peStrip pe2)) from rfl]
    rw [show peStrip (Pexpr a () (PEop op pe1 pe2)) =
      Pexpr [] () (PEop op (peStrip pe1) (peStrip pe2)) from rfl] at hstep
    dsimp only
    rw [show step_eval_pexpr = step_eval_pexpr_lemFuel lemDefaultFuel from rfl,
      hstep]
    rfl
  | @arrayShift a ty pe1 pe2 hp1 hp2 =>
    rw [show peStrip (Pexpr a () (PEarray_shift pe1 ty pe2)) =
      Pexpr [] () (PEarray_shift (peStrip pe1) ty (peStrip pe2)) from rfl]
    rw [show peStrip (Pexpr a () (PEarray_shift pe1 ty pe2)) =
      Pexpr [] () (PEarray_shift (peStrip pe1) ty (peStrip pe2)) from rfl]
      at hstep
    dsimp only
    rw [show step_eval_pexpr = step_eval_pexpr_lemFuel lemDefaultFuel from rfl,
      hstep]
    rfl

/-- LEVEL 3b: `full_eval_pexpr` — the state-threaded evaluator the
    Erun/Eif certification runs against — computes the mirror's
    answer in one iteration, STATE-VERBATIM (`runEU`'s shape: the
    whole tower is a pure `exceptM` computation lifted pointwise).
    Extern pinned at the frozen `fmapEmpty`; tagDefs/memory/file
    quantified (unread). -/
theorem full_eval_bridge {b : Type} {th : thread_state}
    {pe : generic_pexpr Unit sym} {v : value}
    (hv : evalPexpr th.env pe = some v)
    (hd : peDepth pe ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition))
    (σ : CerbMem.MemState) (file : generic_file Unit core_run_annotation) :
    full_eval_pexpr (b := b) tds th fmapEmpty σ file pe =
      stExceptUndef_return v := by
  have hp := evalPexpr_shape hv
  rw [show (full_eval_pexpr (b := b) tds th fmapEmpty σ file pe) =
    full_eval_pexpr_lemFuel (b := b) (999999 + 1) tds th fmapEmpty σ file pe
    from rfl]
  show stExceptUndef_bind _ _ = _
  funext st
  show (match E.eval_pexpr20 tds th fmapEmpty σ file pe st with
    | _ => _ : exceptM _ _) = _
  rw [show E.eval_pexpr20 (a := b) tds th fmapEmpty σ file pe =
    runEU ((eval_pexpr_aux2 tds) th.current_loc
      (match th.exec_loc with
        | ELoc_globals => none
        | ELoc_normal [] => none
        | ELoc_normal ((_, loc1) :: _) => some loc1)
      fmapEmpty th.env (some σ) file pe) from rfl]
  rw [show (eval_pexpr_aux2 (tds)) = eval_pexpr_aux2_lemFuel (999999 + 1) tds
    from rfl]
  rw [aux2_bridge hp hv hd 999999 tds th.current_loc _ (some σ) file]
  rfl

/-- THE FACTOR THEOREM WITH THE JUMP DISJUNCT (readiness R1: "the
    factor theorem gains one disjunct"): a step of a decomposed term
    is EITHER a step of its redex REBUILT in context (the phase-1
    shape), OR the redex is a registered jump and the step is the
    redex's OWN step — the context is DISCARDED, and the successor
    does not mention it. -/
theorem DecompJ.step_factor {Q : LabelMap} {e : CoreExpr} {ctx : context}
    {r : CoreExpr} {ρ : EnvStack} {σ : Mem}
    {out : CoreExpr × EnvStack × Mem}
    (h : DecompJ e ctx r) (hs : Step Q (e, ρ, σ) out) :
    (∃ r' ρ' σ', (∀ (ra : core_run_annotation) (l : sym)
        (pes : List (generic_pexpr Unit sym)), r ≠ runRedex ra l pes) ∧
      Step Q (r, ρ, σ) (r', ρ', σ') ∧
      out = (apply_ctx ctx r', ρ', σ')) ∨
    (∃ (ra : core_run_annotation) (l : sym)
      (pes : List (generic_pexpr Unit sym)),
      r = runRedex ra l pes ∧ Step Q (r, ρ, σ) out) := by
  induction h generalizing out with
  | @root r hr =>
    by_cases hrun : ∃ (ra : core_run_annotation) (l : sym)
        (pes : List (generic_pexpr Unit sym)), r = runRedex ra l pes
    · obtain ⟨ra, l, pes, rfl⟩ := hrun
      exact .inr ⟨ra, l, pes, rfl, hs⟩
    · exact .inl ⟨out.1, out.2.1, out.2.2,
        fun ra l pes hr => hrun ⟨ra, l, pes, hr⟩, hs, rfl⟩
  | @sseq pa bty e1 e2 ctx' r' hd ih =>
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
        ⟨_, _, v, _, _, _, he1, _, _⟩ | ⟨_, _, ds, v, _, _, _, he1, _, _⟩ |
        ⟨l, pes, params, cont, vs, ev0, evs, hj, hρ, hl, hvs, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, hpat, _, _, _⟩
    · rcases ih hstep with ⟨r2, ρr, σr, hnr2, hr2, heq⟩ | ⟨ra, l, pes, rfl, hr2⟩
      · obtain ⟨he, hρ2, hσ2⟩ : e1' = apply_ctx _ r2 ∧ ρ'' = ρr ∧
            σ'' = σr := by
          simpa [Prod.mk.injEq] using heq
        subst he hρ2 hσ2
        exact .inl ⟨r2, _, _, hnr2, hr2, by rw [hout]; rfl⟩
      · rw [hd.jumpRedex?_eq] at hnj
        rw [show jumpRedex? (runRedex ra l pes) = some (l, pes) from rfl]
          at hnj
        cases hnj
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
    · -- the node's step IS the jump: the decomposed redex must be
      -- the run redex, and its own step has the SAME successor
      have hje : jumpRedex? r' = some (l, pes) := by
        rw [← hd.jumpRedex?_eq]; exact hj
      obtain ⟨ra, rfl⟩ := hd.redexJ.jumpRedex?_some_inv hje
      subst hρ
      rw [hout]
      exact .inr ⟨ra, l, pes, rfl, Step.run (by rfl) hl hvs⟩
    · exact (specPat_ne_base hpat).elim
    · exact (specPat_ne_base hpat).elim
    · exact (symPat_ne_base hpat).elim
  | @sseq_spec pa pb x bty e1 e2 ctx' r' hd ih =>
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
        ⟨_, _, v, _, _, _, he1, _, _⟩ | ⟨_, _, ds, v, _, _, _, he1, _, _⟩ |
        ⟨l, pes, params, cont, vs, ev0, evs, hj, hρ, hl, hvs, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, he1, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, he1, _, _⟩ |
        ⟨_, _, _, _, _, _, _, he1, _, _⟩
    · rcases ih hstep with ⟨r2, ρr, σr, hnr2, hr2, heq⟩ | ⟨ra, l, pes, rfl, hr2⟩
      · obtain ⟨he, hρ2, hσ2⟩ : e1' = apply_ctx _ r2 ∧ ρ'' = ρr ∧
            σ'' = σr := by
          simpa [Prod.mk.injEq] using heq
        subst he hρ2 hσ2
        exact .inl ⟨r2, _, _, hnr2, hr2, by rw [hout]; rfl⟩
      · rw [hd.jumpRedex?_eq] at hnj
        rw [show jumpRedex? (runRedex ra l pes) = some (l, pes) from rfl]
          at hnj
        cases hnj
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
    · have hje : jumpRedex? r' = some (l, pes) := by
        rw [← hd.jumpRedex?_eq]; exact hj
      obtain ⟨ra, rfl⟩ := hd.redexJ.jumpRedex?_some_inv hje
      subst hρ
      rw [hout]
      exact .inr ⟨ra, l, pes, rfl, Step.run (by rfl) hl hvs⟩
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
  | @sseq_sym pa x bty e1 e2 ctx' r' hd ih =>
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
        ⟨_, _, v, _, _, _, he1, _, _⟩ | ⟨_, _, ds, v, _, _, _, he1, _, _⟩ |
        ⟨l, pes, params, cont, vs, ev0, evs, hj, hρ, hl, hvs, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, he1, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, he1, _, _⟩ |
        ⟨_, _, _, _, _, _, _, he1, _, _⟩
    · rcases ih hstep with ⟨r2, ρr, σr, hnr2, hr2, heq⟩ | ⟨ra, l, pes, rfl, hr2⟩
      · obtain ⟨he, hρ2, hσ2⟩ : e1' = apply_ctx _ r2 ∧ ρ'' = ρr ∧
            σ'' = σr := by
          simpa [Prod.mk.injEq] using heq
        subst he hρ2 hσ2
        exact .inl ⟨r2, _, _, hnr2, hr2, by rw [hout]; rfl⟩
      · rw [hd.jumpRedex?_eq] at hnj
        rw [show jumpRedex? (runRedex ra l pes) = some (l, pes) from rfl]
          at hnj
        cases hnj
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
    · have hje : jumpRedex? r' = some (l, pes) := by
        rw [← hd.jumpRedex?_eq]; exact hj
      obtain ⟨ra, rfl⟩ := hd.redexJ.jumpRedex?_some_inv hje
      subst hρ
      rw [hout]
      exact .inr ⟨ra, l, pes, rfl, Step.run (by rfl) hl hvs⟩
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
  | @annot ds b ctx' r' hroot hirr hmap hd ih =>
    rcases hs.annot_inv with ⟨_, hnj, b', ρ'', σ'', hstep, hout⟩ |
        ⟨a2, ds2, c, hb, _⟩ |
        ⟨l, pes, params, cont, vs, ev0, evs, hg, hj, hρ, hl, hvs, hout⟩
    · rcases ih hstep with ⟨r2, ρr, σr, hnr2, hr2, heq⟩ | ⟨ra, l, pes, rfl, hr2⟩
      · obtain ⟨he, hρ2, hσ2⟩ : b' = apply_ctx _ r2 ∧ ρ'' = ρr ∧
            σ'' = σr := by
          simpa [Prod.mk.injEq] using heq
        subst he hρ2 hσ2
        exact .inl ⟨r2, _, _, hnr2, hr2, by rw [hout]; rfl⟩
      · rw [hd.jumpRedex?_eq] at hnj
        rw [show jumpRedex? (runRedex ra l pes) = some (l, pes) from rfl]
          at hnj
        cases hnj
    · rw [hb] at hroot
      simp [annotRooted] at hroot
    · have hje : jumpRedex? r' = some (l, pes) := by
        rw [← hd.jumpRedex?_eq]; exact hj
      obtain ⟨ra, rfl⟩ := hd.redexJ.jumpRedex?_some_inv hje
      subst hρ
      rw [hout]
      exact .inr ⟨ra, l, pes, rfl, Step.run (by rfl) hl hvs⟩

/-! ### The jump-profile frozen context and the per-construct engine
equations (context undisturbed — the [USER 2026-08-30] theorem
shape, extended to the S3 constructs)

`procThread` is the proc-CARRYING thread profile: identical to
`envThread` except `current_proc_opt := some p` — the read step_ctx's
Erun arm makes before building its monad (the no-current-proc
failwithI PANIC channel is excluded by the profile). The Q↔labeled
tie is the pure equation `fmapLookupBy ord p rs.labeled = some Q` on
the QUANTIFIED run state (the donor's `⌜Q = rf.f_code⌝` analog); the
frozen `extern = fmapEmpty` makes the proc redirect the identity
fallback. -/

/-- The proc-carrying thread profile (S3's frozen-context
    restatement — readiness §2.1 item 3). -/
def procThread (p : sym) (e : CoreExpr) (ρ : EnvStack) : thread_state :=
  { arena := e, stack0 := Stack_empty, errno := default, env := ρ,
    current_proc_opt := some p, exec_loc := default, current_loc := default }

@[simp] theorem procThread_arena (p : sym) (e : CoreExpr) (ρ : EnvStack) :
    (procThread p e ρ).arena = e := rfl

@[simp] theorem procThread_env (p : sym) (e : CoreExpr) (ρ : EnvStack) :
    (procThread p e ρ).env = ρ := rfl

/-- One engine step at the jump profile. -/
def engineStepsP (p : sym) (e : CoreExpr) (ρ : EnvStack) (σ : Mem) :
    List core_step2 :=
  step_ctx fmapEmpty σ spikeFile fmapEmpty 0 (none, procThread p e ρ)

/-- ... discharged (the run state is now a PARAMETER — Erun reads
    `labeled` through it). -/
def engineOutcomesP (p : sym) (aid : Nat) (rs : core_run_state)
    (e : CoreExpr) (ρ : EnvStack) (σ : Mem) : List EngineOutcome :=
  (engineStepsP p e ρ σ).map (dischargeStep aid rs σ)

/-- The Q↔labeled tie (the donor's `⌜Q = rf.f_code⌝`,
    lifting.v:1002): the run state's two-level `labeled` map has
    fiber `Q` at the current procedure. Pure, stated in the engine's
    own lookup spelling. -/
def LabeledAt (rs : core_run_state) (p : sym) (Q : LabelMap) : Prop :=
  fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
    Lem_Basic_classes.ordCompare s1 s2) p rs.labeled = some Q

/-- Esave ENTRY, context undisturbed (one_step0's Esave
    valueFromPexprs fast-path TAU, Core_reduction.lean:353): env is
    READ-AND-REBOUND (the parameter fold — the D14 partition's env
    row moves to TOUCHED for this rule; nonemptiness is the
    update_env panic exclusion), everything else verbatim. -/
theorem step_ctx_save {e : CoreExpr} {ctx : context}
    {sb : sym × core_base_type}
    {ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
    {body : CoreExpr} {cvals : List value}
    (hd : DecompJ e ctx (saveRedex sb ps body))
    (hsz : esize e ≤ lemDefaultFuel)
    (hvals : valueFromPexprs (saveParamPexprs ps) = some cvals)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    (henv : th.env = ev0 :: evs) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_tau2 "Esave" TSK_Misc
        { th with env := bindSaveParams ps cvals (ev0 :: evs),
                  arena := apply_ctx ctx body }] := by
  have hget : get_ctx th.arena = [(ctx, saveRedex sb ps body)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  have hvals' : valueFromPexprs
      (List.map (fun p => match p with | (_, (_, z)) => z) ps) = some cvals := by
    rw [show (List.map (fun (p : sym × ((core_base_type ×
        Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))
        => match p with | (_, (_, z)) => z) ps) = saveParamPexprs ps from rfl]
    exact hvals
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold saveRedex
  cases ctx <;>
    (dsimp only [one_step0]
     rw [show is_irreducible (Expr [] (Esave sb ps body)) = false from rfl]
     dsimp only [get_loc]
     rw [hvals']
     dsimp only
     rw [henv]
     rfl)

/-- Ecase at a VALUE scrutinee, context undisturbed (one_step0's
    Ecase value arm — TAU into the substituted branch; the
    PEconstrained PANIC pre-arm is bypassed by the canonical value
    scrutinee's shape, the no-match ILLTYPED channel by the
    selection premise). Env verbatim, no premise. -/
theorem step_ctx_case_value {e : CoreExpr} {ctx : context}
    {a : List annot} {cval : value} {pats : List (pattern × CoreExpr)}
    {e' : CoreExpr}
    (hd : DecompJ e ctx (caseRedex (Pexpr a () (PEval cval)) pats))
    (hsz : esize e ≤ lemDefaultFuel)
    (hsel : select_case subst_sym_expr cval pats = some e')
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_tau2 "Ecase" TSK_Misc
        { th with arena := apply_ctx ctx e' }] := by
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

/-- Eif (TRUE), context undisturbed, DISCHARGED (one_step0's Eif
    TAU_WITH_RUNSTATE + the liftCore_run protocol arm): ONE engine
    step big-step-evaluating the guard through `full_eval_pexpr`
    (certified by the bridge — the non-boolean failwithI PANIC
    channel is excluded because the evaluator RETURNS `Vtrue`), run
    state returned VERBATIM (∀ rs — the guard evaluation is
    `runEU`-lifted), env verbatim, memory verbatim. Extern pinned at
    the frozen `fmapEmpty` (the bridge's PEsym indirection). -/
theorem stepDischarge_if_true {e : CoreExpr} {ctx : context}
    {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
    (hd : DecompJ e ctx (ifRedex g e2 e3))
    (hsz : esize e ≤ lemDefaultFuel)
    (hdg : peDepth g ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hg : evalPexpr th.env g = some Vtrue)
    (aid : Nat) (rs : core_run_state) :
    (step_ctx tds σ file fmapEmpty tid (parent, th)).map
        (dischargeStep aid rs σ) =
      [.next { th with arena := apply_ctx ctx e2 } σ] := by
  have hget : get_ctx th.arena = [(ctx, ifRedex g e2 e3)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold ifRedex
  cases ctx <;>
    (dsimp only [one_step0]
     rw [show is_irreducible (Expr ([] : List annot) (Eif g e2 e3)) = false
       from rfl]
     dsimp only [get_loc, dischargeStep]
     rw [full_eval_bridge hg hdg tds σ file]
     dsimp only [stExceptUndef_bind, stExceptUndef_return, stExpect_return,
       return1, except_return]
     rfl)

/-- Eif (FALSE) — symmetric. -/
theorem stepDischarge_if_false {e : CoreExpr} {ctx : context}
    {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
    (hd : DecompJ e ctx (ifRedex g e2 e3))
    (hsz : esize e ≤ lemDefaultFuel)
    (hdg : peDepth g ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hg : evalPexpr th.env g = some Vfalse)
    (aid : Nat) (rs : core_run_state) :
    (step_ctx tds σ file fmapEmpty tid (parent, th)).map
        (dischargeStep aid rs σ) =
      [.next { th with arena := apply_ctx ctx e3 } σ] := by
  have hget : get_ctx th.arena = [(ctx, ifRedex g e2 e3)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold ifRedex
  cases ctx <;>
    (dsimp only [one_step0]
     rw [show is_irreducible (Expr ([] : List annot) (Eif g e2 e3)) = false
       from rfl]
     dsimp only [get_loc, dischargeStep]
     rw [full_eval_bridge hg hdg tds σ file]
     dsimp only [stExceptUndef_bind, stExceptUndef_return, stExpect_return,
       return1, except_return]
     rfl)

/-- PURE, context undisturbed, DISCHARGED (S4 — one_step0's Epure
    EVAL arm + step_ctx's EVAL wrap + the liftCore_run protocol):
    ONE engine step big-step-evaluating the pure expression through
    `full_eval_pexpr` (certified by the bridge; the PURE-UNDEF
    channel is excluded because the evaluator RETURNS a value), run
    state returned VERBATIM (∀ rs), env/memory verbatim; the
    successor rebuilds the canonical value injection in context.
    Extern pinned at the frozen `fmapEmpty` (the bridge's PEsym
    indirection). -/
theorem stepDischarge_pure_sym {e : CoreExpr} {ctx : context}
    {pb : List _root_.annot} {x : sym} {v : value}
    (hd : DecompJ e ctx (pureRedex (Pexpr pb () (PEsym x))))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hv : evalPexpr th.env (Pexpr pb () (PEsym x)) = some v)
    (aid : Nat) (rs : core_run_state) :
    (step_ctx tds σ file fmapEmpty tid (parent, th)).map
        (dischargeStep aid rs σ) =
      [.next ({ th with arena := apply_ctx ctx (Expr [] (Epure (Pexpr [] () (PEval v)))) }) σ] := by
  have hget : get_ctx th.arena =
      [(ctx, pureRedex (Pexpr pb () (PEsym x)))] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold pureRedex
  cases ctx <;>
    (dsimp only [one_step0, is_irreducible, valueFromPexpr]
     simp only [Bool.false_eq_true, if_false]
     dsimp only [get_loc, dischargeStep]
     rw [full_eval_bridge hv (peDepth_sym_le pb x) tds σ file]
     dsimp only [stExceptUndef_bind, stExceptUndef_return, stExpect_return,
       return1, except_return]
     rfl)

/-- `act_valueFromPexpr` on a covered non-value operand: the
    PEconstrained PANIC pre-arm is bypassed by the grammar, the
    value test fails (Core_reduction.lean:393). -/
theorem act_valueFromPexpr_none {pe : generic_pexpr Unit sym}
    (hp : PePure pe) (hnv : valueFromPexpr pe = none) :
    act_valueFromPexpr pe = none := by
  cases hp with
  | val a v => rw [valueFromPexpr_val] at hnv; cases hnv
  | sym a x => rfl
  | op a op hp1 hp2 => rfl
  | arrayShift a ty hp1 hp2 => rfl

/-- Load ACTION_EVAL, context undisturbed, DISCHARGED (S4 —
    step_action's Load0 `_, _` arm + process_action's ACTION_EVAL
    wrap): ONE engine step big-step-evaluating the operands (the
    canonical type operand's re-evaluation is the identity; the
    pointer operand through the certified evaluator), run state
    VERBATIM (∀ rs), env/memory verbatim; the successor rebuilds the
    CANONICAL LOAD REDEX in context — the certified load equation
    takes over at the next step. -/
theorem stepDischarge_load_eval {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pe2 : generic_pexpr Unit sym} {mo : memory_order}
    {pv : CerbMem.PointerValue}
    (hd : DecompJ e ctx (loadOpRedex loc ann ty pe2 mo))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv2 : valueFromPexpr pe2 = none)
    (hp2 : PePure pe2)
    (hd2 : peDepth pe2 ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hv2 : evalPexpr th.env pe2 = some (Vobject (OVpointer pv)))
    (aid : Nat) (rs : core_run_state) :
    (step_ctx tds σ file fmapEmpty tid (parent, th)).map
        (dischargeStep aid rs σ) =
      [.next { th with arena := apply_ctx ctx (loadRedex loc ann ty pv mo) }
        σ] := by
  have hget : get_ctx th.arena = [(ctx, loadOpRedex loc ann ty pe2 mo)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold loadOpRedex
  cases ctx <;>
    (dsimp only [get_loc]
     dsimp only [step_action]
     rw [act_valueFromPexpr_none hp2 hnv2]
     dsimp only [act_valueFromPexpr, valueFromPexpr]
     dsimp only [dischargeStep]
     rw [full_eval_bridge (v := Vctype ty) rfl (peDepth_val_le _ _) tds σ file,
       full_eval_bridge hv2 hd2 tds σ file]
     dsimp only [stExceptUndef_bind, stExceptUndef_return, stExpect_return,
       return1, except_return]
     rfl)

/-- LETS-PURE at the Specified-binder pattern, context undisturbed
    (S4): the engine's beta TAU with the parameter fold — the env is
    READ-AND-REBOUND (`update_env` at the Specified pattern binds the
    payload object value; nonemptiness is the panic exclusion),
    everything else verbatim. -/
theorem step_ctx_beta_spec_pure {e : CoreExpr} {ctx : context}
    {pa pb : List _root_.annot} {x : sym} {bty : core_base_type}
    {ov : object_value} {e2 : CoreExpr}
    (hd : DecompJ e ctx
      (Expr [] (Esseq (specPat pa pb x bty)
        (ofVal (.pure (Vloaded (LVspecified ov)))) e2)))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    (henv : th.env = ev0 :: evs) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_tau2 "Esseq" TSK_Misc
        ({ th with
            env := update_env (specPat pa pb x bty)
              (Vloaded (LVspecified ov)) (ev0 :: evs),
            arena := apply_ctx ctx e2 })] := by
  have hget : get_ctx th.arena =
      [(ctx, Expr [] (Esseq (specPat pa pb x bty)
        (ofVal (.pure (Vloaded (LVspecified ov)))) e2))] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  cases ctx <;>
    (simp only [one_step0, ofVal, is_irreducible_sseq, Bool.false_eq_true,
       if_false, valueFromPexpr]
     simp only [get_loc]
     dsimp only [update_env]
     rw [henv]
     try rfl)

/-- LETS-ANNOT at the Specified-binder pattern, context
    undisturbed (S4). -/
theorem step_ctx_beta_spec_annot {e : CoreExpr} {ctx : context}
    {pa pb : List _root_.annot} {x : sym} {bty : core_base_type}
    {ds : List dyn_annotation} {ov : object_value} {e2 : CoreExpr}
    (hd : DecompJ e ctx
      (Expr [] (Esseq (specPat pa pb x bty)
        (ofVal (.annot ds (Vloaded (LVspecified ov)))) e2)))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    (henv : th.env = ev0 :: evs) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_tau2 "Esseq Eannot" TSK_Misc
        ({ th with
            env := update_env (specPat pa pb x bty)
              (Vloaded (LVspecified ov)) (ev0 :: evs),
            arena := apply_ctx ctx (Expr [] (Eannot ds e2)) })] := by
  have hget : get_ctx th.arena =
      [(ctx, Expr [] (Esseq (specPat pa pb x bty)
        (ofVal (.annot ds (Vloaded (LVspecified ov)))) e2))] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  cases ctx <;>
    (simp only [one_step0, ofVal, is_irreducible_sseq, Bool.false_eq_true,
       if_false, valueFromPexpr]
     simp only [get_loc]
     dsimp only [update_env]
     rw [henv]
     try rfl)

/-- Top-level application equations for the state-except monad (the
    binder-safe computation chain: `rw` never descends under the
    binding-fold lambda, so the engine's own spellings survive
    verbatim until each redex surfaces at the top level). -/
theorem stExceptUndef_bind_apply {a b c d e : Type}
    (m : e → exceptM ((t0 d × a)) c) (f : d → a → exceptM ((t0 b × a)) c)
    (st : e) :
    stExceptUndef_bind m f st =
      match m st with
      | Result (Defined z, st') => f z st'
      | Result (Undef loc1 ubs, st') => stExpect_return (undef loc1 ubs) st'
      | Result (Error loc1 str, st') => stExpect_return (error0 loc1 str) st'
      | Exception err => fail0 err := by
  unfold stExceptUndef_bind
  rcases m st with ⟨⟨z | ⟨loc1, ubs⟩ | ⟨loc1, str⟩, st'⟩⟩ | err <;> rfl

theorem stExceptUndef_return_apply {a b c : Type} (z : a) (st : b) :
    stExceptUndef_return (c := c) z st = Result (Defined z, st) := rfl

theorem runSE_read_apply {a b msg : Type} (f : a → b) (st : a) :
    runSE (msg := msg) (state_except_read f) st =
      Result (Defined (f st), st) := rfl

theorem bind0_some {a b : Type} (x : a) (f : a → Option b) :
    Lem_Maybe.bind0 (some x) f = f x := rfl

theorem stExceptUndef_foldM_cons {a b c e : Type}
    (f : a → e → c → exceptM ((t0 a × c)) b) (acc : a) (x : e) (xs : List e) :
    stExceptUndef_foldM f acc (x :: xs) =
      stExceptUndef_bind (f acc x) (fun z => stExceptUndef_foldM f z xs) := rfl

/-- The Erun argument fold (step_ctx's `stExceptUndef_foldM` over
    `zip sym_bTys pes`) computes the mirror's `bindArgs`,
    STATE-VERBATIM: each argument evaluates against the FIXED
    `th.env` (the engine's `full_eval_pexpr'` closure) while the
    binding accumulator threads. The fold body is ABSTRACT with a
    pointwise characterization `hf` (spelling-independent: the
    engine's match-lambda and its normalized forms all satisfy it by
    `rfl`). -/
theorem foldM_args_bridge {th : thread_state}
    {tds : Fmap sym (CerbLocation.Loc × tag_definition)} {σ : Mem}
    {file : generic_file Unit core_run_annotation}
    (f : EnvStack → (sym × core_base_type) × generic_pexpr Unit sym →
      core_run_state → exceptM ((t0 EnvStack × core_run_state)) core_run_cause)
    (hf : ∀ (acc : EnvStack) (s : sym) (bTy : core_base_type)
      (pe : generic_pexpr Unit sym) (rs' : core_run_state),
      f acc ((s, bTy), pe) rs' =
        stExceptUndef_bind (full_eval_pexpr tds th fmapEmpty σ file pe)
          (fun cval =>
            stExceptUndef_return (update_env (mk_sym_pat s bTy) cval acc)) rs') :
    ∀ (params : List (sym × core_base_type))
      (pes : List (generic_pexpr Unit sym)) (vs : List value)
      (acc : EnvStack) (rs : core_run_state),
      evalPexprs th.env pes = some vs →
      (∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel) →
      stExceptUndef_foldM f acc (List.zip params pes) rs =
        Result (Defined (bindArgs params vs acc), rs) := by
  intro params
  induction params with
  | nil =>
    intro pes vs acc rs hvs hdep
    rfl
  | cons p params ih =>
    intro pes vs acc rs hvs hdep
    cases pes with
    | nil =>
      obtain rfl : vs = [] := by
        have : some ([] : List value) = some vs := by simpa using hvs
        exact (Option.some.inj this).symm
      rw [List.zip_nil_right]
      rfl
    | cons pe pes =>
      rw [evalPexprs_cons] at hvs
      obtain ⟨v, hv, vs', hvs', rfl⟩ : ∃ v, evalPexpr th.env pe = some v ∧
          ∃ vs', evalPexprs th.env pes = some vs' ∧ vs = v :: vs' := by
        cases h1 : evalPexpr th.env pe with
        | none => rw [h1] at hvs; cases hvs
        | some v =>
          cases h2 : evalPexprs th.env pes with
          | none => rw [h1, h2] at hvs; cases hvs
          | some vs' =>
            rw [h1, h2] at hvs
            cases hvs
            exact ⟨v, rfl, vs', rfl, rfl⟩
      obtain ⟨p1, p2⟩ := p
      rw [List.zip_cons_cons, stExceptUndef_foldM_cons,
        stExceptUndef_bind_apply, hf acc p1 p2 pe rs,
        stExceptUndef_bind_apply,
        full_eval_bridge hv (hdep pe (by simp)) tds σ file,
        stExceptUndef_return_apply]
      dsimp only []
      rw [stExceptUndef_return_apply]
      dsimp only []
      rw [ih pes vs' (update_env (mk_sym_pat p1 p2) v acc) rs hvs'
        (fun pe' hpe' => hdep pe' (by simp [hpe']))]
      rfl

/-- THE JUMP, context DISCARDED, DISCHARGED — the headline S3
    certification (step_ctx's Erun arm, Core_reduction.lean:484 +
    the liftCore_run discharge): at a proc-carrying thread whose
    arena decomposes to a registered `run l pes`, the engine takes
    EXACTLY ONE step, whose successor REPLACES THE WHOLE ARENA by
    the registered continuation with the parameters rebound — the
    evaluation context `ctx` appears NOWHERE in the successor. The
    run state is read (the `labeled` fiber at the current procedure,
    through the frozen extern's identity fallback — the pure
    Q↔labeled tie `LabeledAt`) and returned VERBATIM
    (`state_except_read` + `runEU`-lifted argument evaluation); the
    unresolvable-label and no-current-proc failwithI PANIC channels
    are excluded by `hl`/`hproc`. -/
theorem stepDischarge_run {e : CoreExpr} {ctx : context}
    {ra : core_run_annotation} {l : sym}
    {pes : List (generic_pexpr Unit sym)}
    (hd : DecompJ e ctx (runRedex ra l pes))
    (hsz : esize e ≤ lemDefaultFuel)
    {Q : LabelMap} {params : List (sym × core_base_type)} {cont : CoreExpr}
    {vs : List value}
    (hl : lookupLabel Q l = some (params, cont))
    (hdep : ∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation)
    (tid : Nat) (parent : Option Nat) (p : sym) (th : thread_state)
    (harena : th.arena = e)
    (hproc : th.current_proc_opt = some p)
    (hvs : evalPexprs th.env pes = some vs)
    (aid : Nat) (rs : core_run_state) (hQ : LabeledAt rs p Q) :
    (step_ctx tds σ file fmapEmpty tid (parent, th)).map
        (dischargeStep aid rs σ) =
      [.next { th with env := bindArgs params vs th.env, arena := cont } σ] := by
  have hget : get_ctx th.arena = [(ctx, runRedex ra l pes)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  have hQ' : (fmapLookupBy (fun (sym1 : sym) (sym2 : sym) =>
      Lem_Basic_classes.ordCompare sym1 sym2) p rs.labeled) = some Q := hQ
  have hl' : (fmapLookupBy (fun (sym1 : sym) (sym2 : sym) =>
      Lem_Basic_classes.ordCompare sym1 sym2) l Q) = some (params, cont) := hl
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold runRedex
  cases ctx <;>
    (dsimp only [get_loc]
     rw [hproc]
     dsimp only [dischargeStep]
     rw [stExceptUndef_bind_apply, runSE_read_apply]
     dsimp only []
     rw [show (fmapLookupBy (fun (sym1 : sym) (sym2 : sym) =>
         Lem_Basic_classes.ordCompare sym1 sym2) p
         (fmapEmpty (α := sym) (β := sym))) = none from rfl]
     dsimp only []
     rw [hQ', bind0_some, hl']
     dsimp only []
     rw [stExceptUndef_bind_apply,
       foldM_args_bridge _ (fun _ _ _ _ _ => rfl) params pes vs th.env rs
         hvs hdep]
     dsimp only []
     rw [stExceptUndef_return_apply])

/-! ### The memop protocol and the store ACTION_EVAL (list-reverse
phase A)

The pointer-test certification: (1) `step_ctx_memop` — at a
decomposed value-operand memop the engine takes exactly one
`Step_memop_request2` (one_step0's Ememop MEMOP arm +
step_ctx's dispatch, Core_reduction.lean:353/484); (2)
`dischargeStep_memop_active` — the sequential driver's PtrEq
discharge (perform_memop_request2, Driver.lean:288) computed from
the `applyMemM` verdict; (3) the memop-operand EVAL step and the
store ACTION_EVAL, both discharged through the certified evaluator
tower (`eval1_bridge` — one application of step_ctx's `eval_pexpr1`
fully evaluates a covered operand, exactly like `full_eval_pexpr`;
the state-monad plumbing mirrors `foldM_args_bridge`'s
abstract-body-with-pointwise-characterization pattern). -/

/-- eqPtrval discards its location argument (CerbMem.lean:1731,
    `_ : CerbLocation.Loc`): any two locations are definitionally
    the same operation (the `allocateObject_arg_irrel` precedent). -/
theorem eqPtrval_loc_irrel (l l' : CerbLocation.Loc)
    (pv1 pv2 : CerbMem.PointerValue) :
    CerbMem.eqPtrval l pv1 pv2 = CerbMem.eqPtrval l' pv1 pv2 := rfl

/-- MEMOP at value operands, context undisturbed: one
    `Step_memop_request2` carrying the operand values and the
    context-rebuilding continuation (a BARE pure value —
    `mk_pure_e (mk_value_pe cval)`, no Eannot residue). The request
    carries `th.current_loc` (the memop has no loc of its own);
    the fragment's `[]` node annotations keep the current_loc
    rebinding off (get_loc = none). -/
theorem step_ctx_memop {e : CoreExpr} {ctx : context} {mop : memop}
    {pe1 pe2 : generic_pexpr Unit sym} {v1 v2 : value}
    (hd : DecompJ e ctx (memopRedex mop [pe1, pe2]))
    (hsz : esize e ≤ lemDefaultFuel)
    (hv1 : valueFromPexpr pe1 = some v1)
    (hv2 : valueFromPexpr pe2 = some v2)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_memop_request2 th.current_loc mop [v1, v2] tid
        (is_unseq_with_ccall ctx)
        (fun cval => { th with
          arena :=
            apply_ctx ctx (Expr [] (Epure (Pexpr [] () (PEval cval)))) })] := by
  have hget : get_ctx th.arena = [(ctx, memopRedex mop [pe1, pe2])] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold memopRedex
  cases ctx <;>
    (dsimp only [one_step0]
     rw [show is_irreducible (Expr ([] : List annot) (Ememop mop [pe1, pe2]))
       = false from rfl]
     dsimp only [get_loc]
     rw [valueFromPexprs_pair, hv1, hv2]
     rfl)

/-- The sequential driver's PtrEq discharge computed from the
    `applyMemM` verdict (perform_memop_request2's PtrEq arm,
    Driver.lean:288 — `liftMem (CerbMem.eqPtrval loc …)` then
    `mk_th_st (if is_eq then Vtrue else Vfalse)`); the request's loc
    bridges to the rule's `default` by `eqPtrval_loc_irrel`. -/
theorem dischargeStep_memop_active {aid : Nat} {rs : core_run_state}
    {σ σ' : Mem} {loc : CerbLocation.Loc} {tid : thread_id} {uw : Bool}
    {pv1 pv2 : CerbMem.PointerValue} {k : value → thread_state} {b : Bool}
    (h : applyMemM (CerbMem.eqPtrval default pv1 pv2) σ = some (b, σ')) :
    dischargeStep aid rs σ (Step_memop_request2 loc PtrEq
      [Vobject (OVpointer pv1), Vobject (OVpointer pv2)] tid uw k) =
      .next (k (boolValue b)) σ' := by
  rcases hm : CerbMem.eqPtrval default pv1 pv2 with ⟨f⟩
  rcases hf : f σ with ⟨act, st⟩
  unfold applyMemM at h
  rw [hm] at h
  simp only [hf] at h
  unfold dischargeStep
  dsimp only
  rw [eqPtrval_loc_irrel loc default pv1 pv2, hm]
  dsimp only
  rw [hf]
  cases act <;> simp only [] at h ⊢
  case NDactive x =>
    obtain ⟨rfl, rfl⟩ : x = b ∧ st = σ' := by
      cases h; exact ⟨rfl, rfl⟩
    rfl
  all_goals cases h

/-- One application of step_ctx's `eval_pexpr1` (the let-bound
    one-iteration evaluator, Core_reduction.lean:484: `eval_pexpr20`
    + the Sum readout into `mk_value_pe`) computes the mirror's
    answer, STATE-VERBATIM, on the covered operand grammar — the
    one-step analog of `full_eval_bridge` (the tower iterates once;
    on the covered grammar one iteration completes). -/
theorem eval1_bridge {th : thread_state} {pe : generic_pexpr Unit sym}
    {v : value} (hv : evalPexpr th.env pe = some v)
    (hdp : peDepth pe ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition))
    (σ : CerbMem.MemState) (file : generic_file Unit core_run_annotation)
    (rs : core_run_state) :
    stExceptUndef_bind
      (E.eval_pexpr20 (a := core_run_state) tds th fmapEmpty σ file pe)
      (fun x => match x with
        | Sum.inl pe' => stExceptUndef_return pe'
        | Sum.inr cval => stExceptUndef_return (mk_value_pe cval)) rs =
      Result (Defined (mk_value_pe v), rs) := by
  have hp := evalPexpr_shape hv
  rw [stExceptUndef_bind_apply]
  rw [show E.eval_pexpr20 (a := core_run_state) tds th fmapEmpty σ file pe =
    runEU ((eval_pexpr_aux2 tds) th.current_loc
      (match th.exec_loc with
        | ELoc_globals => none
        | ELoc_normal [] => none
        | ELoc_normal ((_, loc1) :: _) => some loc1)
      fmapEmpty th.env (some σ) file pe) from rfl]
  rw [show (eval_pexpr_aux2 (tds)) = eval_pexpr_aux2_lemFuel (999999 + 1) tds
    from rfl]
  rw [aux2_bridge hp hv hdp 999999 tds th.current_loc _ (some σ) file]
  rfl

/-- Top-level application equation for the plain state-except bind
    (the `stExceptUndef_bind_apply` analog one layer down). -/
theorem stExpect_bind_apply {a b msg s : Type}
    (m : s → exceptM ((a × s)) msg) (f : a → s → exceptM ((b × s)) msg)
    (st : s) :
    stExpect_bind m f st =
      (match m st with
       | Result (a1, s') => f a1 s'
       | Exception err => Exception err) := by
  unfold stExpect_bind except_bind
  rcases m st with ⟨⟨a1, s'⟩⟩ | err <;> rfl

/-- ... and its Result-valued instance (the computation form the
    mapM bridge chains). -/
theorem stExpect_bind_result {a b msg s : Type}
    (m : s → exceptM ((a × s)) msg) (f : a → s → exceptM ((b × s)) msg)
    (st st' : s) (x : a) (h : m st = Result (x, st')) :
    stExpect_bind m f st = f x st' := by
  rw [stExpect_bind_apply, h]

/-- The Ememop EVAL arm's operand map (`stExceptUndef_mapM
    eval_pexpr1 [pe1, pe2]`, one_step0's Ememop non-value arm)
    computes the fully evaluated canonical operands, STATE-VERBATIM.
    The fold body is ABSTRACT with a pointwise characterization `hf`
    (the `foldM_args_bridge` pattern — the engine's lambda and its
    normalized forms all satisfy it by `rfl`). -/
theorem mapM_eval1_bridge {th : thread_state}
    {tds : Fmap sym (CerbLocation.Loc × tag_definition)} {σ : Mem}
    {file : generic_file Unit core_run_annotation}
    (f : generic_pexpr Unit sym → core_run_state →
      exceptM ((t0 (generic_pexpr Unit sym) × core_run_state)) core_run_cause)
    (hf : ∀ (pe : generic_pexpr Unit sym) (rs' : core_run_state),
      f pe rs' = stExceptUndef_bind
        (E.eval_pexpr20 (a := core_run_state) tds th fmapEmpty σ file pe)
        (fun x => match x with
          | Sum.inl pe' => stExceptUndef_return pe'
          | Sum.inr cval => stExceptUndef_return (mk_value_pe cval)) rs')
    {pe1 pe2 : generic_pexpr Unit sym} {v1 v2 : value}
    (hv1 : evalPexpr th.env pe1 = some v1)
    (hd1 : peDepth pe1 ≤ lemDefaultFuel)
    (hv2 : evalPexpr th.env pe2 = some v2)
    (hd2 : peDepth pe2 ≤ lemDefaultFuel)
    (rs : core_run_state) :
    stExceptUndef_mapM f [pe1, pe2] rs =
      Result (Defined [mk_value_pe v1, mk_value_pe v2], rs) := by
  have h1 : f pe1 rs = Result (Defined (mk_value_pe v1), rs) :=
    (hf pe1 rs).trans (eval1_bridge hv1 hd1 tds σ file rs)
  have h2 : f pe2 rs = Result (Defined (mk_value_pe v2), rs) :=
    (hf pe2 rs).trans (eval1_bridge hv2 hd2 tds σ file rs)
  have hb2 : stExpect_bind (f pe2) (fun y =>
      stExpect_bind (stExpect_return
        ([] : List (t0 (generic_pexpr Unit sym)))) (fun ys =>
        stExpect_return (y :: ys))) rs =
      Result ([Defined (mk_value_pe v2)], rs) :=
    (stExpect_bind_result _ _ _ _ _ h2).trans rfl
  have hb1 : stExpect_mapM f [pe1, pe2] rs =
      Result ([Defined (mk_value_pe v1), Defined (mk_value_pe v2)], rs) := by
    rw [show stExpect_mapM f [pe1, pe2] =
      stExpect_bind (f pe1) (fun x =>
        stExpect_bind (stExpect_bind (f pe2) (fun y =>
          stExpect_bind (stExpect_return
              ([] : List (t0 (generic_pexpr Unit sym)))) (fun ys =>
            stExpect_return (y :: ys)))) (fun xs =>
          stExpect_return (x :: xs))) from rfl]
    rw [stExpect_bind_result _ _ _ _ _ h1]
    show stExpect_bind (stExpect_bind (f pe2) _) _ rs = _
    rw [stExpect_bind_result _ _ _ _ _ hb2]
    rfl
  unfold stExceptUndef_mapM
  rw [stExpect_bind_result _ _ _ _ _ hb1]
  rfl

/-- MEMOP-OPERAND EVALUATION, context undisturbed, DISCHARGED
    (one_step0's Ememop EVAL arm + step_ctx's EVAL wrap + the
    liftCore_run protocol): ONE engine step mapping `eval_pexpr1`
    over the operands (one full evaluator iteration each —
    `eval1_bridge`/`mapM_eval1_bridge`), run state VERBATIM,
    env/memory verbatim; the successor rebuilds the value-operand
    memop redex in context. -/
theorem stepDischarge_memop_eval {e : CoreExpr} {ctx : context}
    {mop : memop} {pe1 pe2 : generic_pexpr Unit sym} {v1 v2 : value}
    (hd : DecompJ e ctx (memopRedex mop [pe1, pe2]))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (hd1 : peDepth pe1 ≤ lemDefaultFuel)
    (hd2 : peDepth pe2 ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hv1 : evalPexpr th.env pe1 = some v1)
    (hv2 : evalPexpr th.env pe2 = some v2)
    (aid : Nat) (rs : core_run_state) :
    (step_ctx tds σ file fmapEmpty tid (parent, th)).map
        (dischargeStep aid rs σ) =
      [.next { th with arena := apply_ctx ctx (Expr [] (Ememop mop
        [Pexpr [] () (PEval v1), Pexpr [] () (PEval v2)])) } σ] := by
  have hget : get_ctx th.arena = [(ctx, memopRedex mop [pe1, pe2])] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold memopRedex
  cases ctx <;>
    (dsimp only [one_step0]
     rw [show is_irreducible (Expr ([] : List annot) (Ememop mop [pe1, pe2]))
       = false from rfl]
     dsimp only [get_loc]
     rw [hnv]
     simp only [Bool.false_eq_true, if_false]
     dsimp only [dischargeStep]
     rw [stExceptUndef_bind_apply, stExceptUndef_bind_apply,
       mapM_eval1_bridge (tds := tds) (σ := σ) (file := file)
         _ ?_ hv1 hd1 hv2 hd2 rs] <;>
       first
         | rfl
         | (intro pe rs'
            rfl))

/-- Store ACTION_EVAL, context undisturbed, DISCHARGED (step_action's
    Store0 `_, _, _` arm + process_action's ACTION_EVAL wrap): ONE
    engine step big-step-evaluating the three operands (the canonical
    type operand's re-evaluation is the identity; pointer and value
    operands through the certified evaluator), run state VERBATIM
    (∀ rs), env/memory verbatim; the successor rebuilds the CANONICAL
    STORE REDEX in context. `hp3` cases the value operand's head
    constructor so the engine's `Store0 … PEconstrained` failwithI
    pre-arm reduces past (the covered grammar has no PEconstrained). -/
theorem stepDischarge_store_eval {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pe2 pe3 : generic_pexpr Unit sym} {mo : memory_order}
    {pv : CerbMem.PointerValue} {cv : value}
    (hd : DecompJ e ctx (storeOpRedex loc ann ty pe2 pe3 mo))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv2 : valueFromPexpr pe2 = none)
    (hnv3 : valueFromPexpr pe3 = none)
    (hp2 : PePure pe2) (hp3 : PePure pe3)
    (hd2 : peDepth pe2 ≤ lemDefaultFuel)
    (hd3 : peDepth pe3 ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hv2 : evalPexpr th.env pe2 = some (Vobject (OVpointer pv)))
    (hv3 : evalPexpr th.env pe3 = some cv)
    (aid : Nat) (rs : core_run_state) :
    (step_ctx tds σ file fmapEmpty tid (parent, th)).map
        (dischargeStep aid rs σ) =
      [.next { th with arena := apply_ctx ctx (storeRedex loc ann false ty
        pv cv mo) } σ] := by
  have hget : get_ctx th.arena = [(ctx, storeOpRedex loc ann ty pe2 pe3 mo)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold storeOpRedex
  cases hp3 <;> try (rw [valueFromPexpr_val] at hnv3; cases hnv3)
  all_goals
    cases ctx <;>
      (dsimp only [get_loc]
       dsimp only [step_action]
       rw [act_valueFromPexpr_none hp2 hnv2]
       dsimp only [act_valueFromPexpr, valueFromPexpr]
       dsimp only [dischargeStep]
       rw [full_eval_bridge (v := Vctype ty) rfl (peDepth_val_le _ _) tds σ file,
         full_eval_bridge hv2 hd2 tds σ file,
         full_eval_bridge hv3 hd3 tds σ file]
       dsimp only [stExceptUndef_bind, stExceptUndef_return, stExpect_return,
         return1, except_return]
       rfl)

/-- LETS-PURE at the plain-symbol binder, context undisturbed: the
    engine's beta TAU with the one-binding env update (`update_env`
    at the symbol pattern binds the value verbatim,
    Core_aux.lean:861; nonemptiness is the panic exclusion),
    everything else verbatim. -/
theorem step_ctx_beta_sym_pure {e : CoreExpr} {ctx : context}
    {pa : List _root_.annot} {x : sym} {bty : core_base_type}
    {v : value} {e2 : CoreExpr}
    (hd : DecompJ e ctx
      (Expr [] (Esseq (symPat pa x bty) (ofVal (.pure v)) e2)))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    (henv : th.env = ev0 :: evs) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_tau2 "Esseq" TSK_Misc
        ({ th with
            env := update_env (symPat pa x bty) v (ev0 :: evs),
            arena := apply_ctx ctx e2 })] := by
  have hget : get_ctx th.arena =
      [(ctx, Expr [] (Esseq (symPat pa x bty) (ofVal (.pure v)) e2))] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  cases ctx <;>
    (simp only [one_step0, ofVal, is_irreducible_sseq, Bool.false_eq_true,
       if_false, valueFromPexpr]
     simp only [get_loc]
     dsimp only [update_env]
     rw [henv]
     try rfl)

/-! ### The extended fragment cone and the step-match completeness

`FragJ` is the S3 syntactic cone: the phase-1 shapes plus Esave,
Eif (with the guard's fuel-honesty side condition), and Erun (with
the arguments'). Ecase stays OUT (its cone needs the
substitution-closure lemmas — the registered S4 item); registered
continuations enter through the SIDE hypothesis `hQf` (the label
map's own cone membership), which breaks the circularity a
Q-indexed cone would have.

The completeness shape CHANGES from phase 1 (recorded finding): the
old `engine_complete` classified every engine behavior including
refusals-at-stuck; the J-lane instead certifies MATCH-GIVEN-STEP
(`engine_step_matchJ`): wherever the MIRROR steps, the engine's
behavior is the singleton discharged match. That suffices for the
WP-driven adequacy lane (NotStuck supplies a mirror step at every
reachable configuration) and dissolves the WF-threading problem:
the panic-exclusion facts live as RULE PREMISES, extracted by the
inversions from the given step — the WP is the well-formedness
oracle. -/

inductive FragJ : CoreExpr → Prop where
  | val_pure (v : value) : FragJ (Expr [] (Epure (Pexpr [] () (PEval v))))
  | store {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
      {ty : ctype} {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
      (hlib : CerbLocation.isLibraryLocation loc = false) :
      FragJ (storeRedex loc ann lk ty pv cv mo)
  | load {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
      {pv : CerbMem.PointerValue} {mo : memory_order}
      (hlib : CerbLocation.isLibraryLocation loc = false) :
      FragJ (loadRedex loc ann ty pv mo)
  | create {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {align : CerbMem.IntegerValue} {ty : ctype} {pref : prefix0}
      (hlib : CerbLocation.isLibraryLocation loc = false) :
      FragJ (createRedex loc ann align ty pref)
  | sseq {pa : List annot} {bty : core_base_type} {e1 e2 : CoreExpr} :
      FragJ e1 → FragJ e2 →
      FragJ (Expr [] (Esseq (Pattern pa (CaseBase (none, bty))) e1 e2))
  | annot {ds : List dyn_annotation} {b : CoreExpr} :
      FragJ b → FragJ (Expr [] (Eannot ds b))
  | save {sb : sym × core_base_type}
      {ps : List (sym × ((core_base_type ×
        Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
      {body : CoreExpr} :
      FragJ body → FragJ (saveRedex sb ps body)
  | if_ {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
      (hdg : peDepth g ≤ lemDefaultFuel) :
      FragJ e2 → FragJ e3 → FragJ (ifRedex g e2 e3)
  | run {ra : core_run_annotation} {l : sym}
      {pes : List (generic_pexpr Unit sym)}
      (hdep : ∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel) :
      FragJ (runRedex ra l pes)
  | sseq_spec {pa pb : List annot} {x : sym} {bty : core_base_type}
      {e1 e2 : CoreExpr} :
      FragJ e1 → FragJ e2 →
      FragJ (Expr [] (Esseq (specPat pa pb x bty) e1 e2))
  | pure_sym {pb : List annot} {x : sym} :
      FragJ (pureRedex (Pexpr pb () (PEsym x)))
  | load_op {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {ty : ctype} {pe2 : generic_pexpr Unit sym} {mo : memory_order}
      (hlib : CerbLocation.isLibraryLocation loc = false)
      (hnv2 : valueFromPexpr pe2 = none) (hp2 : PePure pe2)
      (hd2 : peDepth pe2 ≤ lemDefaultFuel) :
      FragJ (loadOpRedex loc ann ty pe2 mo)
  | sseq_sym {pa : List annot} {x : sym} {bty : core_base_type}
      {e1 e2 : CoreExpr} :
      FragJ e1 → FragJ e2 →
      FragJ (Expr [] (Esseq (symPat pa x bty) e1 e2))
  | memop_vals (v1 v2 : value) :
      FragJ (memopPtrEqVals v1 v2)
  | memop_op {pe1 pe2 : generic_pexpr Unit sym}
      (hnv : valueFromPexprs [pe1, pe2] = none)
      (hp1 : PePure pe1) (hp2 : PePure pe2)
      (hd1 : peDepth pe1 ≤ lemDefaultFuel)
      (hd2 : peDepth pe2 ≤ lemDefaultFuel) :
      FragJ (memopRedex PtrEq [pe1, pe2])
  | store_op {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {ty : ctype} {pe2 pe3 : generic_pexpr Unit sym} {mo : memory_order}
      (hlib : CerbLocation.isLibraryLocation loc = false)
      (hnv2 : valueFromPexpr pe2 = none) (hnv3 : valueFromPexpr pe3 = none)
      (hp2 : PePure pe2) (hp3 : PePure pe3)
      (hd2 : peDepth pe2 ≤ lemDefaultFuel)
      (hd3 : peDepth pe3 ≤ lemDefaultFuel) :
      FragJ (storeOpRedex loc ann ty pe2 pe3 mo)

/-- The phase-1 cone embeds. -/
theorem FragP.toJ {e : CoreExpr} (hf : FragP e) : FragJ e := by
  induction hf with
  | val_pure v => exact .val_pure v
  | store hlib => exact .store hlib
  | load hlib => exact .load hlib
  | create hlib => exact .create hlib
  | sseq hf1 hf2 ih1 ih2 => exact .sseq ih1 ih2
  | annot hfb ihb => exact .annot ihb

theorem fragJ_ofVal (w : SpikeVal) : FragJ (ofVal w) := by
  cases w with
  | pure v => exact .val_pure v
  | annot ds v => exact .annot (.val_pure v)

/-! matcher facts for the pure-redex shapes (the fuelled matchers
examine the pexpr's head constructor; a non-value premise dismisses
the value arms) -/

theorem is_irreducible_annot_pure {ds : List dyn_annotation}
    {pe : generic_pexpr Unit sym} (hnv : valueFromPexpr pe = none) :
    is_irreducible (Expr ([] : List _root_.annot)
      (Eannot ds (pureRedex pe))) = false := by
  rcases pe with ⟨b, u, pe_⟩
  cases u
  cases pe_ <;>
    first
    | rfl
    | (rw [valueFromPexpr_val] at hnv; cases hnv)

theorem get_ctx_annot_pure {ds : List dyn_annotation}
    {pe : generic_pexpr Unit sym} (hnv : valueFromPexpr pe = none) :
    ∀ n : Nat,
    get_ctx_lemFuel (n+1) (Expr ([] : List _root_.annot)
        (Eannot ds (pureRedex pe))) =
      List.map (fun p => (Cannot [] ds p.1, p.2))
        (get_ctx_lemFuel n (pureRedex pe)) := by
  intro n
  rcases pe with ⟨b, u, pe_⟩
  cases u
  cases pe_ <;>
    first
    | rfl
    | (rw [valueFromPexpr_val] at hnv; cases hnv)

theorem is_irreducible_merge_pure {ds1 ds2 : List dyn_annotation}
    {pe : generic_pexpr Unit sym} :
    is_irreducible (Expr ([] : List _root_.annot) (Eannot ds1
      (Expr [] (Eannot ds2 (pureRedex pe))))) = false := by
  rcases pe with ⟨b, u, pe_⟩
  cases u
  cases pe_ <;> rfl

/-- Every non-value FragJ configuration decomposes (extended
    roots). -/
theorem FragJ.decompJ {e : CoreExpr} (hf : FragJ e) (hnv : toVal e = none) :
    ∃ ctx r, DecompJ e ctx r ∧ FragJ r := by
  induction hf with
  | val_pure v =>
    rw [show toVal (Expr ([] : List _root_.annot) (Epure (Pexpr [] () (PEval v)))) =
      some (.pure v) from rfl] at hnv
    cases hnv
  | store hlib => exact ⟨_, _, DecompJ.root (.base (.store hlib)), .store hlib⟩
  | load hlib => exact ⟨_, _, DecompJ.root (.base (.load hlib)), .load hlib⟩
  | create hlib => exact ⟨_, _, DecompJ.root (.base (.create hlib)), .create hlib⟩
  | @sseq pa bty e1 e2 hf1 hf2 ih1 ih2 =>
    cases hv1 : toVal e1 with
    | some w =>
      have he1 := ofVal_of_toVal hv1
      subst he1
      cases w with
      | pure v => exact ⟨_, _, DecompJ.root (.base .beta_pure),
          .sseq (fragJ_ofVal (.pure v)) hf2⟩
      | annot ds v => exact ⟨_, _, DecompJ.root (.base .beta_annot),
          .sseq (fragJ_ofVal (.annot ds v)) hf2⟩
    | none =>
      obtain ⟨ctx, r, hd, hfr⟩ := ih1 hv1
      exact ⟨_, _, DecompJ.sseq hd, hfr⟩
  | @annot ds b hfb ihb =>
    by_cases hr : annotRooted b = true
    · cases hfb with
      | val_pure v => simp [annotRooted] at hr
      | store hlib => simp [annotRooted, storeRedex] at hr
      | load hlib => simp [annotRooted, loadRedex] at hr
      | create hlib => simp [annotRooted, createRedex] at hr
      | sseq hf1 hf2 => simp [annotRooted] at hr
      | sseq_spec hf1 hf2 => simp [annotRooted] at hr
      | save hb => simp [annotRooted, saveRedex] at hr
      | if_ hdg hf2 hf3 => simp [annotRooted, ifRedex] at hr
      | run hdep => simp [annotRooted, runRedex] at hr
      | pure_sym => simp [annotRooted, pureRedex] at hr
      | load_op hlib hnv2 hp2 hd2 => simp [annotRooted, loadOpRedex] at hr
      | sseq_sym hf1 hf2 => simp [annotRooted] at hr
      | memop_vals v1 v2 => simp [annotRooted, memopPtrEqVals, memopRedex] at hr
      | memop_op hnv hp1 hp2 hpd1 hpd2 => simp [annotRooted, memopRedex] at hr
      | store_op hlib hnv2 hnv3 hp2 hp3 hpd2 hpd3 =>
        simp [annotRooted, storeOpRedex] at hr
      | @annot ds2 c hfc =>
        have hwit : FragJ (Expr ([] : List _root_.annot)
            (Eannot ds (Expr [] (Eannot ds2 c)))) := .annot (.annot hfc)
        cases hfc with
        | val_pure v => exact ⟨_, _, DecompJ.root (.base (.merge rfl)), hwit⟩
        | store hlib => exact ⟨_, _, DecompJ.root (.base (.merge rfl)), hwit⟩
        | load hlib => exact ⟨_, _, DecompJ.root (.base (.merge rfl)), hwit⟩
        | create hlib => exact ⟨_, _, DecompJ.root (.base (.merge rfl)), hwit⟩
        | sseq hf1 hf2 => exact ⟨_, _, DecompJ.root (.base (.merge rfl)), hwit⟩
        | sseq_spec hf1 hf2 =>
          exact ⟨_, _, DecompJ.root (.base (.merge rfl)), hwit⟩
        | annot hfc' => exact ⟨_, _, DecompJ.root (.base (.merge rfl)), hwit⟩
        | save hb => exact ⟨_, _, DecompJ.root (.base (.merge rfl)), hwit⟩
        | if_ hdg hf2 hf3 => exact ⟨_, _, DecompJ.root (.base (.merge rfl)), hwit⟩
        | run hdep => exact ⟨_, _, DecompJ.root (.base (.merge rfl)), hwit⟩
        | pure_sym =>
          exact ⟨_, _, DecompJ.root (.base (.merge rfl)), hwit⟩
        | load_op hlib hnv2 hp2 hd2 =>
          exact ⟨_, _, DecompJ.root (.base (.merge rfl)), hwit⟩
        | sseq_sym hf1 hf2 =>
          exact ⟨_, _, DecompJ.root (.base (.merge rfl)), hwit⟩
        | memop_vals v1 v2 =>
          exact ⟨_, _, DecompJ.root (.base (.merge rfl)), hwit⟩
        | memop_op hnv hp1 hp2 hpd1 hpd2 =>
          exact ⟨_, _, DecompJ.root (.base (.merge rfl)), hwit⟩
        | store_op hlib hnv2 hnv3 hp2 hp3 hpd2 hpd3 =>
          exact ⟨_, _, DecompJ.root (.base (.merge rfl)), hwit⟩
    · have hr' : annotRooted b = false := by simpa using hr
      cases hvb : toVal b with
      | some w =>
        have hb := ofVal_of_toVal hvb
        subst hb
        cases w with
        | pure v =>
          rw [show toVal (Expr ([] : List _root_.annot)
            (Eannot ds (ofVal (.pure v)))) = some (.annot ds v) from rfl] at hnv
          cases hnv
        | annot ds2 v => simp [annotRooted, ofVal] at hr'
      | none =>
        obtain ⟨ctx, r, hd, hfr⟩ := ihb hvb
        cases hfb with
        | val_pure v =>
          rw [show toVal (Expr ([] : List _root_.annot)
            (Epure (Pexpr [] () (PEval v)))) = some (.pure v) from rfl] at hvb
          cases hvb
        | store hlib => exact ⟨_, _, DecompJ.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | load hlib => exact ⟨_, _, DecompJ.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | create hlib => exact ⟨_, _, DecompJ.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | sseq hf1 hf2 => exact ⟨_, _, DecompJ.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | sseq_spec hf1 hf2 =>
          exact ⟨_, _, DecompJ.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | save hb => exact ⟨_, _, DecompJ.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | if_ hdg hf2 hf3 => exact ⟨_, _, DecompJ.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | run hdep => exact ⟨_, _, DecompJ.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | annot hfc => simp [annotRooted] at hr'
        | pure_sym =>
          exact ⟨_, _, DecompJ.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | load_op hlib hnv2 hp2 hd2 =>
          exact ⟨_, _, DecompJ.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | sseq_sym hf1 hf2 =>
          exact ⟨_, _, DecompJ.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | memop_vals v1 v2 =>
          exact ⟨_, _, DecompJ.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | memop_op hnv hp1 hp2 hpd1 hpd2 =>
          exact ⟨_, _, DecompJ.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | store_op hlib hnv2 hnv3 hp2 hp3 hpd2 hpd3 =>
          exact ⟨_, _, DecompJ.annot hr' rfl (fun n => rfl) hd, hfr⟩
  | save hb ih => exact ⟨_, _, DecompJ.root (.save _ _ _), .save hb⟩
  | if_ hdg hf2 hf3 ih2 ih3 =>
    exact ⟨_, _, DecompJ.root (.if_ _ _ _), .if_ hdg hf2 hf3⟩
  | run hdep => exact ⟨_, _, DecompJ.root (.run _ _ _), .run hdep⟩
  | @sseq_spec pa pb x bty e1 e2 hf1 hf2 ih1 ih2 =>
    cases hv1 : toVal e1 with
    | some w =>
      have he1 := ofVal_of_toVal hv1
      subst he1
      exact ⟨_, _, DecompJ.root .beta_spec, .sseq_spec (fragJ_ofVal w) hf2⟩
    | none =>
      obtain ⟨ctx, r, hd, hfr⟩ := ih1 hv1
      exact ⟨_, _, DecompJ.sseq_spec hd, hfr⟩
  | pure_sym =>
    exact ⟨_, _, DecompJ.root (.pure_e rfl), .pure_sym⟩
  | load_op hlib hnv2 hp2 hd2 =>
    exact ⟨_, _, DecompJ.root (.load_op _ _ _ _ hnv2),
      .load_op hlib hnv2 hp2 hd2⟩
  | @sseq_sym pa x bty e1 e2 hf1 hf2 ih1 ih2 =>
    cases hv1 : toVal e1 with
    | some w =>
      have he1 := ofVal_of_toVal hv1
      subst he1
      exact ⟨_, _, DecompJ.root .beta_sym, .sseq_sym (fragJ_ofVal w) hf2⟩
    | none =>
      obtain ⟨ctx, r, hd, hfr⟩ := ih1 hv1
      exact ⟨_, _, DecompJ.sseq_sym hd, hfr⟩
  | memop_vals v1 v2 =>
    exact ⟨_, _, DecompJ.root (.memop _ _), .memop_vals v1 v2⟩
  | memop_op hnvF hp1 hp2 hpd1 hpd2 =>
    exact ⟨_, _, DecompJ.root (.memop _ _), .memop_op hnvF hp1 hp2 hpd1 hpd2⟩
  | store_op hlib hnv2F hnv3 hp2 hp3 hpd2 hpd3 =>
    exact ⟨_, _, DecompJ.root (.store_op _ _ _ _ hnv2F),
      .store_op hlib hnv2F hnv3 hp2 hp3 hpd2 hpd3⟩

/-! S4 RETIREMENT NOTE: S3's `DecompJ.toDecomp` (an extended
    decomposition holding a phase-1 redex is a phase-1
    decomposition) is FALSIFIED by the S4 `sseq_spec` frame (a
    phase-1 redex can now sit under a Specified-binder frame, which
    `Decomp` cannot represent). Its one consumer — the jump-profile
    step-match's reuse of the phase-1 step_ctx equations — is served
    instead by the GENERALIZED equations (their `hd` premises are
    now `DecompJ`; phase-1 callers embed via `Decomp.toJ`). -/

/-- The value protocol at the jump profile (PROGRAM-DONE /
    REMOVE-ANNOT — the strong forms quantify the thread, so the
    proc-carrying corollaries are instances). -/
theorem engineOutcomesP_done (p : sym) (aid : Nat) (rs : core_run_state)
    (v : value) (ρ : EnvStack) (σ : Mem) :
    engineOutcomesP p aid rs (ofVal (.pure v)) ρ σ = [.done v] := by
  unfold engineOutcomesP engineStepsP
  rw [step_ctx_done v fmapEmpty σ spikeFile fmapEmpty 0 _ rfl rfl]
  rfl

theorem engineOutcomesP_remove_annot (p : sym) (aid : Nat)
    (rs : core_run_state) (ds : List dyn_annotation) (v : value)
    (ρ : EnvStack) (σ : Mem) :
    engineOutcomesP p aid rs (ofVal (.annot ds v)) ρ σ =
      [.next (procThread p (ofVal (.pure v)) ρ) σ] := by
  unfold engineOutcomesP engineStepsP
  rw [step_ctx_remove_annot ds v fmapEmpty σ spikeFile fmapEmpty 0 none _ rfl]
  rfl

/-- The extended cone is closed under Step, GIVEN the label map's
    own cone membership (`hQf` — the registered continuations are
    fragment terms; the side hypothesis breaks the circularity a
    Q-indexed cone would have). -/
theorem FragJ.step {Q : LabelMap}
    (hQf : ∀ l params cont, lookupLabel Q l = some (params, cont) → FragJ cont)
    {e : CoreExpr} {ρ : EnvStack} {σ : Mem}
    {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    (hf : FragJ e) (hs : Step Q (e, ρ, σ) (e', ρ', σ')) : FragJ e' := by
  induction hf generalizing e' ρ' σ' with
  | val_pure v => exact (Step.val_elim (w := .pure v) hs).elim
  | store hlib =>
    obtain ⟨mv, fp, σ'', hmv, hmem, hout⟩ := hs.store_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact .annot (.val_pure Vunit)
  | load hlib =>
    obtain ⟨fp, mval, σ'', hmem, hout⟩ := hs.load_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact .annot (.val_pure _)
  | create hlib =>
    obtain ⟨pv, σ'', hmem, hout⟩ := hs.create_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact .val_pure _
  | sseq hf1 hf2 ih1 ih2 =>
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
        ⟨_, _, v, _, _, _, _, _, hout⟩ | ⟨_, _, ds', v, _, _, _, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, hpat, _, _, _⟩
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact .sseq (ih1 hstep) hf2
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact hf2
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact .annot hf2
    · obtain ⟨h1, -, -⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      rw [h1]
      exact hQf l params cont hl
    · exact (specPat_ne_base hpat).elim
    · exact (specPat_ne_base hpat).elim
    · exact (symPat_ne_base hpat).elim
  | annot hfb ihb =>
    rcases hs.annot_inv with ⟨hg, hnj, b', ρ'', σ'', hstep, hout⟩ |
        ⟨a2, ds2, c, hb, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hg, hj, _, hl, _, hout⟩
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact .annot (ihb hstep)
    · subst hb
      obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      cases hfb with
      | annot hfc => exact .annot hfc
    · obtain ⟨h1, -, -⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      rw [h1]
      exact hQf l params cont hl
  | save hb ih =>
    obtain ⟨cvals, ev0', evs', hρeq, hvals, hout⟩ := hs.save_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = _ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact hb
  | if_ hdg hf2 hf3 ih2 ih3 =>
    rcases hs.if_inv with ⟨-, hout⟩ | ⟨-, hout⟩ <;>
      (obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout)
    · subst h1; exact hf2
    · subst h1; exact hf3
  | run hdep =>
    obtain ⟨params, cont, vs, ev0', evs', hρeq, hl, hvs, hout⟩ :=
      hs.jump_inv (by rfl)
    obtain ⟨h1, -, -⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    rw [h1]
    exact hQf _ params cont hl
  | sseq_spec hf1 hf2 ih1 ih2 =>
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
        ⟨_, _, v, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, ds', v, _, _, hpat, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, hpat, _, _, hout⟩
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact .sseq_spec (ih1 hstep) hf2
    · exact (specPat_ne_base hpat.symm).elim
    · exact (specPat_ne_base hpat.symm).elim
    · obtain ⟨h1, -, -⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      rw [h1]
      exact hQf l params cont hl
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact hf2
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact .annot hf2
    · exact (symPat_ne_spec hpat).elim
  | sseq_sym hf1 hf2 ih1 ih2 =>
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
        ⟨_, _, v, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, ds', v, _, _, hpat, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, hpat, _, _, hout⟩
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact .sseq_sym (ih1 hstep) hf2
    · exact (symPat_ne_base hpat.symm).elim
    · exact (symPat_ne_base hpat.symm).elim
    · obtain ⟨h1, -, -⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      rw [h1]
      exact hQf l params cont hl
    · exact (symPat_ne_spec hpat.symm).elim
    · exact (symPat_ne_spec hpat.symm).elim
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact hf2
  | memop_vals v1 v2 =>
    rw [show memopPtrEqVals v1 v2 = Expr [] (Ememop PtrEq
      [Pexpr [] () (PEval v1), Pexpr [] () (PEval v2)]) from rfl] at hs
    cases hs with
    | run hj hl hvs => simp at hj
    | memop_ptreq h1 h2 hmem => exact .val_pure _
    | memop_eval hnv hv1 hv2 =>
      rw [valueFromPexprs_pair, valueFromPexpr_val, valueFromPexpr_val] at hnv
      cases hnv
  | memop_op hnv hp1 hp2 hpd1 hpd2 =>
    obtain ⟨v1, v2, hv1, hv2, hout⟩ := hs.memop_op_inv hnv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact .memop_vals v1 v2
  | store_op hlib hnv2 hnv3 hp2 hp3 hpd2 hpd3 =>
    obtain ⟨pv, cv, hv2', hv3', -, hout⟩ := hs.store_op_inv hnv2
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact .store hlib
  | pure_sym =>
    obtain ⟨v, -, -, hout⟩ := hs.pure_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact .val_pure v
  | load_op hlib hnv2 hp2 hd2 =>
    obtain ⟨pv, -, hout⟩ := hs.load_op_inv hnv2
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact .load hlib

/-- Step growth on the extended cone: additive except at a jump,
    which RESETS to a registered continuation (the R3 reset — the
    J-lane accounting's second budget). -/
theorem FragJ.esize_step_bound {Q : LabelMap} {e : CoreExpr} {ρ : EnvStack}
    {σ : Mem} {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    (hf : FragJ e) (hs : Step Q (e, ρ, σ) (e', ρ', σ')) :
    esize e' ≤ esize e + 1 ∨
    ∃ l pes params cont, jumpRedex? e = some (l, pes) ∧
      lookupLabel Q l = some (params, cont) ∧ e' = cont := by
  induction hf generalizing e' ρ' σ' with
  | val_pure v => exact (Step.val_elim (w := .pure v) hs).elim
  | store hlib =>
    obtain ⟨mv, fp, σ'', hmv, hmem, hout⟩ := hs.store_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left; simp [esize, storeRedex]
  | load hlib =>
    obtain ⟨fp, mval, σ'', hmem, hout⟩ := hs.load_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left; simp [esize, loadRedex]
  | create hlib =>
    obtain ⟨pv, σ'', hmem, hout⟩ := hs.create_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left; simp [esize, createRedex]
  | sseq hf1 hf2 ih1 ih2 =>
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
        ⟨_, _, v, _, _, _, _, _, hout⟩ | ⟨_, _, ds', v, _, _, _, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, hpat, _, _, hout⟩
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      rcases ih1 hstep with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · left
        simp only [esize_sseq] at *
        omega
      · -- a jump of e1 under the frame is excluded by the congruence
        -- guard
        rw [hnj] at hj1
        cases hj1
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      left
      simp only [esize_sseq]
      omega
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      left
      simp only [esize_sseq, esize_annot]
      omega
    · obtain ⟨h1, -, -⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      exact .inr ⟨l, pes, params, cont, by rw [jumpRedex?_sseq, hj], hl, h1⟩
    · exact (specPat_ne_base hpat).elim
    · exact (specPat_ne_base hpat).elim
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      left
      simp only [esize_sseq]
      omega
  | annot hfb ihb =>
    rcases hs.annot_inv with ⟨hg, hnj, b', ρ'', σ'', hstep, hout⟩ |
        ⟨a2, ds2, c, hb, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hg, hj, _, hl, _, hout⟩
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      rcases ihb hstep with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · left
        simp only [esize_annot] at *
        omega
      · rw [hnj] at hj1
        cases hj1
    · subst hb
      obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      left
      simp only [esize_annot]
      omega
    · obtain ⟨h1, -, -⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      exact .inr ⟨l, pes, params, cont,
        by rw [jumpRedex?_annot_of_not_root _ _ hg, hj], hl, h1⟩
  | save hb ih =>
    obtain ⟨cvals, ev0', evs', hρeq, hvals, hout⟩ := hs.save_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = _ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left
    simp only [show ∀ sb ps b, esize (saveRedex sb ps b) = 1 + esize b
      from fun _ _ _ => rfl]
    omega
  | if_ hdg hf2 hf3 ih2 ih3 =>
    rcases hs.if_inv with ⟨-, hout⟩ | ⟨-, hout⟩ <;>
      (obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout)
    · subst h1
      left
      simp only [show ∀ g e2 e3, esize (ifRedex g e2 e3) =
        1 + max (esize e2) (esize e3) from fun _ _ _ => rfl]
      omega
    · subst h1
      left
      simp only [show ∀ g e2 e3, esize (ifRedex g e2 e3) =
        1 + max (esize e2) (esize e3) from fun _ _ _ => rfl]
      omega
  | run hdep =>
    obtain ⟨params, cont, vs, ev0', evs', hρeq, hl, hvs, hout⟩ :=
      hs.jump_inv (by rfl)
    obtain ⟨h1, -, -⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    exact .inr ⟨_, _, params, cont, rfl, hl, h1⟩
  | sseq_spec hf1 hf2 ih1 ih2 =>
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
        ⟨_, _, v, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, ds', v, _, _, hpat, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, hpat, _, _, hout⟩
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      rcases ih1 hstep with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · left
        simp only [esize_sseq] at *
        omega
      · rw [hnj] at hj1
        cases hj1
    · exact (specPat_ne_base hpat.symm).elim
    · exact (specPat_ne_base hpat.symm).elim
    · obtain ⟨h1, -, -⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      exact .inr ⟨l, pes, params, cont, by rw [jumpRedex?_sseq, hj], hl, h1⟩
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      left
      simp only [esize_sseq]
      omega
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      left
      simp only [esize_sseq, esize_annot]
      omega
    · exact (symPat_ne_spec hpat).elim
  | pure_sym =>
    obtain ⟨v, -, -, hout⟩ := hs.pure_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left
    simp [esize, pureRedex]
  | load_op hlib hnv2 hp2 hd2 =>
    obtain ⟨pv, -, hout⟩ := hs.load_op_inv hnv2
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left
    simp [esize, loadOpRedex]
  | sseq_sym hf1 hf2 ih1 ih2 =>
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
        ⟨_, _, v, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, ds', v, _, _, hpat, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, hpat, _, _, hout⟩
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      rcases ih1 hstep with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · left
        simp only [esize_sseq] at *
        omega
      · rw [hnj] at hj1
        cases hj1
    · exact (symPat_ne_base hpat.symm).elim
    · exact (symPat_ne_base hpat.symm).elim
    · obtain ⟨h1, -, -⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      exact .inr ⟨l, pes, params, cont, by rw [jumpRedex?_sseq, hj], hl, h1⟩
    · exact (symPat_ne_spec hpat.symm).elim
    · exact (symPat_ne_spec hpat.symm).elim
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      left
      simp only [esize_sseq]
      omega
  | memop_vals v1 v2 =>
    rw [show memopPtrEqVals v1 v2 = Expr [] (Ememop PtrEq
      [Pexpr [] () (PEval v1), Pexpr [] () (PEval v2)]) from rfl] at hs
    cases hs with
    | run hj hl hvs => simp at hj
    | memop_ptreq h1 h2 hmem =>
      left
      simp [esize, memopPtrEqVals, memopRedex]
    | memop_eval hnv hv1 hv2 =>
      rw [valueFromPexprs_pair, valueFromPexpr_val, valueFromPexpr_val] at hnv
      cases hnv
  | memop_op hnv hp1 hp2 hpd1 hpd2 =>
    obtain ⟨v1, v2, hv1, hv2, hout⟩ := hs.memop_op_inv hnv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left
    simp [esize, memopRedex]
  | store_op hlib hnv2 hnv3 hp2 hp3 hpd2 hpd3 =>
    obtain ⟨pv, cv, hv2', hv3', -, hout⟩ := hs.store_op_inv hnv2
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left
    simp [esize, storeOpRedex]

/-- THE STEP-MATCH COMPLETENESS AT THE JUMP PROFILE: wherever the
    MIRROR steps at a FragJ configuration (labels tied by
    `LabeledAt`), the engine's discharged behavior list is EXACTLY
    the matching singleton. The WP's NotStuck supplies the step at
    every reachable configuration, so this is the certification the
    J-lane drive classification consumes; the rule premises
    extracted by the inversions are precisely the panic-exclusion
    facts (guard boolean, label registered, proc set, env
    nonempty) — the WP is the well-formedness oracle. -/
theorem engine_step_matchJ {Q : LabelMap} {p : sym} (aid : Nat)
    {rs : core_run_state} (hQ : LabeledAt rs p Q)
    {e e' : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    {ρ' : EnvStack} {σ σ' : Mem}
    (hf : FragJ e) (hsz : esize e ≤ lemDefaultFuel)
    (hs : Step Q (e, ev0 :: evs, σ) (e', ρ', σ')) :
    engineOutcomesP p aid rs e (ev0 :: evs) σ =
      [.next (procThread p e' ρ') σ'] := by
  have hnv : toVal e = none := hs.toVal_none
  obtain ⟨ctx, r, hd, hfr⟩ := hf.decompJ hnv
  rcases hd.step_factor hs with ⟨r', ρr, σr, hnr, hr, heq⟩ | ⟨ra, l, pes, rfl, hr⟩
  · obtain ⟨he', hρ', hσ'⟩ : e' = apply_ctx ctx r' ∧ ρ' = ρr ∧ σ' = σr := by
      simpa [Prod.mk.injEq] using heq
    subst he' hρ' hσ'
    have hrj := hd.redexJ
    cases hrj with
    | base hb =>
      have hdOld : DecompJ e ctx r := hd
      cases hb with
      | @store loc ann lk ty pv cv mo hlib =>
        obtain ⟨mv, fp, σ'', hmv, hmem, hout⟩ := hr.store_inv
        obtain ⟨h1, h2, h3⟩ : r' = Expr [] (Eannot [DA_pos [] fp]
            (Expr [] (Epure (Pexpr [] () (PEval Vunit))))) ∧
            ρ' = ev0 :: evs ∧ σ' = σ'' := by
          simpa [Prod.mk.injEq] using hout
        subst h1 h2 h3
        unfold engineOutcomesP engineStepsP
        rw [step_ctx_store hdOld hsz hlib fmapEmpty hmv σ spikeFile fmapEmpty
          0 none _ rfl]
        simp only [List.map_cons, List.map_nil]
        rw [dischargeStep_store_active hmem]
        rfl
      | @load loc ann ty pv mo hlib =>
        obtain ⟨fp, mval, σ'', hmem, hout⟩ := hr.load_inv
        obtain ⟨h1, h2, h3⟩ : r' = Expr [] (Eannot [DA_pos [] fp]
            (Expr [] (Epure (Pexpr [] () (PEval
              (valueFromMemValue mval).2))))) ∧
            ρ' = ev0 :: evs ∧ σ' = σ'' := by
          simpa [Prod.mk.injEq] using hout
        subst h1 h2 h3
        unfold engineOutcomesP engineStepsP
        rw [step_ctx_load hdOld hsz hlib fmapEmpty σ spikeFile fmapEmpty
          0 none _ rfl]
        simp only [List.map_cons, List.map_nil]
        rw [dischargeStep_load_active hmem]
        rfl
      | @create loc ann align ty pref hlib =>
        obtain ⟨pv, σ'', hmem, hout⟩ := hr.create_inv
        obtain ⟨h1, h2, h3⟩ : r' = Expr [] (Epure (Pexpr [] ()
            (PEval (Vobject (OVpointer pv))))) ∧
            ρ' = ev0 :: evs ∧ σ' = σ'' := by
          simpa [Prod.mk.injEq] using hout
        subst h1 h2 h3
        unfold engineOutcomesP engineStepsP
        rw [step_ctx_create hdOld hsz hlib fmapEmpty σ spikeFile fmapEmpty
          0 none _ rfl]
        simp only [List.map_cons, List.map_nil]
        rw [dischargeStep_create_active (reqAddr := get_with_address []) hmem]
        rfl
      | @beta_pure pa bty v e2 =>
        rcases hr.sseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
            ⟨_, _, v', _, _, _, he1, _, hout⟩ |
            ⟨_, _, ds', v', _, _, _, he1, _, hout⟩ |
            ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
            ⟨_, _, _, _, _, _, _, hpat, _, _, _⟩ |
            ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
            ⟨_, _, _, _, _, _, hpat, _, _, _⟩
        · exact absurd hstep (fun h => Step.val_elim h)
        · obtain rfl : v' = v := by
            have : ofVal (.pure v') = ofVal (.pure v) := he1.symm
            simpa [ofVal] using this
          obtain ⟨h1, h2, h3⟩ : r' = e2 ∧ ρ' = ev0 :: evs ∧ σ' = σ := by
            simpa [Prod.mk.injEq] using hout
          subst h2
          obtain rfl : σ = σ' := h3.symm
          obtain rfl : e2 = r' := h1.symm
          unfold engineOutcomesP engineStepsP
          rw [step_ctx_beta_pure hdOld hsz fmapEmpty σ spikeFile fmapEmpty
            0 none _ rfl rfl]
          rfl
        · exact absurd he1 (by simp [ofVal])
        · rw [jumpRedex?_ofVal] at hj; cases hj
        · exact (specPat_ne_base hpat).elim
        · exact (specPat_ne_base hpat).elim
        · exact (symPat_ne_base hpat).elim
      | @beta_annot pa bty ds v e2 =>
        rcases hr.sseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
            ⟨_, _, v', _, _, _, he1, _, hout⟩ |
            ⟨_, _, ds', v', _, _, _, he1, _, hout⟩ |
            ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
            ⟨_, _, _, _, _, _, _, hpat, _, _, _⟩ |
            ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
            ⟨_, _, _, _, _, _, hpat, _, _, _⟩
        · exact absurd hstep (fun h => Step.val_elim h)
        · exact absurd he1 (by simp [ofVal])
        · obtain ⟨hds, hv⟩ : ds = ds' ∧ v = v' := by simpa [ofVal] using he1
          subst hds hv
          obtain ⟨h1, h2, h3⟩ : r' = Expr [] (Eannot ds e2) ∧
              ρ' = ev0 :: evs ∧ σ' = σ := by
            simpa [Prod.mk.injEq] using hout
          subst h1 h2
          obtain rfl : σ = σ' := h3.symm
          unfold engineOutcomesP engineStepsP
          rw [step_ctx_beta_annot hdOld hsz fmapEmpty σ spikeFile fmapEmpty
            0 none _ rfl rfl]
          rfl
        · rw [jumpRedex?_ofVal] at hj; cases hj
        · exact (specPat_ne_base hpat).elim
        · exact (specPat_ne_base hpat).elim
        · exact (symPat_ne_base hpat).elim
      | @merge ds1 ds2 b hirr =>
        rcases hr.annot_inv with ⟨hg, hnj, b', ρ'', σ'', hstep, hout⟩ |
            ⟨a2, ds2', c, hbeq, hout⟩ |
            ⟨l, pes, params, cont, vs, _, _, hg, hj, _, _, _, _⟩
        · rw [show annotRooted (Expr ([] : List annot) (Eannot ds2 b)) = true
            from rfl] at hg
          cases hg
        · injection hbeq with hb1 hb2
          injection hb2 with hb3 hb4
          subst hb1 hb3 hb4
          obtain ⟨h1, h2, h3⟩ : r' = Expr ([] ++ []) (Eannot (ds1 ++ ds2) b) ∧
              ρ' = ev0 :: evs ∧ σ' = σ := by
            simpa [Prod.mk.injEq] using hout
          subst h1 h2
          obtain rfl : σ = σ' := h3.symm
          unfold engineOutcomesP engineStepsP
          rw [step_ctx_merge hdOld hirr hsz fmapEmpty σ spikeFile fmapEmpty
            0 none _ rfl]
          rfl
        · rw [show annotRooted (Expr ([] : List annot) (Eannot ds2 b)) = true
            from rfl] at hg
          cases hg
    | save sb ps body =>
      obtain ⟨cvals, ev0', evs', hρeq, hvals, hout⟩ := hr.save_inv
      obtain ⟨h1, h2, h3⟩ : r' = body ∧
          ρ' = bindSaveParams ps cvals (ev0 :: evs) ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h2
      obtain rfl : σ = σ' := h3.symm
      obtain rfl : body = r' := h1.symm
      unfold engineOutcomesP engineStepsP
      rw [step_ctx_save hd hsz hvals fmapEmpty σ spikeFile fmapEmpty
        0 none _ rfl rfl]
      rfl
    | if_ g e2 e3 =>
      have hdg : peDepth g ≤ lemDefaultFuel := by
        cases hfr with
        | if_ hdg _ _ => exact hdg
      rcases hr.if_inv with ⟨hg, hout⟩ | ⟨hg, hout⟩
      · obtain ⟨h1, h2, h3⟩ : r' = e2 ∧ ρ' = ev0 :: evs ∧ σ' = σ := by
          simpa [Prod.mk.injEq] using hout
        subst h2
        obtain rfl : σ = σ' := h3.symm
        obtain rfl : e2 = r' := h1.symm
        exact stepDischarge_if_true hd hsz hdg fmapEmpty σ spikeFile
          0 none _ rfl hg aid rs
      · obtain ⟨h1, h2, h3⟩ : r' = e3 ∧ ρ' = ev0 :: evs ∧ σ' = σ := by
          simpa [Prod.mk.injEq] using hout
        subst h2
        obtain rfl : σ = σ' := h3.symm
        obtain rfl : e3 = r' := h1.symm
        exact stepDischarge_if_false hd hsz hdg fmapEmpty σ spikeFile
          0 none _ rfl hg aid rs
    | case_ pe pats =>
      -- Ecase is outside the J cone (the registered S4 item); no
      -- FragJ constructor produces the case shape, so the redex's
      -- cone membership refutes.
      cases hfr
    | run ra l pes =>
      -- unreachable: the factor theorem's LEFT disjunct certifies
      -- its redex is NOT a run redex
      exact absurd rfl (hnr ra l pes)
    | @pure_e pe hnv =>
      obtain ⟨pb, x, rfl⟩ : ∃ pb x, pe = Pexpr pb () (PEsym x) := by
        cases hfr with
        | val_pure v => rw [valueFromPexpr_val] at hnv; cases hnv
        | pure_sym => exact ⟨_, _, rfl⟩
      obtain ⟨v, -, hv, hout⟩ := hr.pure_inv
      obtain ⟨h1, h2, h3⟩ : r' = Expr [] (Epure (Pexpr [] () (PEval v))) ∧
          ρ' = ev0 :: evs ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1 h2
      obtain rfl : σ = σ' := h3.symm
      unfold engineOutcomesP engineStepsP
      exact stepDischarge_pure_sym hd hsz fmapEmpty σ spikeFile
        0 none _ rfl hv aid rs
    | @load_op loc ann ty pe2 mo hnv2 =>
      obtain ⟨hp2, hd2⟩ : PePure pe2 ∧ peDepth pe2 ≤ lemDefaultFuel := by
        cases hfr with
        | load hlib =>
          rw [show valueFromPexpr (Pexpr [] () (PEval
            (Vobject (OVpointer _)))) = some _ from rfl] at hnv2
          cases hnv2
        | load_op hlib hnv2' hp2 hd2 => exact ⟨hp2, hd2⟩
      obtain ⟨pv, hv2, hout⟩ := hr.load_op_inv hnv2
      obtain ⟨h1, h2, h3⟩ : r' = loadRedex loc ann ty pv mo ∧
          ρ' = ev0 :: evs ∧ σ' = σ := by
        simpa [Prod.mk.injEq, loadRedex] using hout
      subst h1 h2
      obtain rfl : σ = σ' := h3.symm
      unfold engineOutcomesP engineStepsP
      exact stepDischarge_load_eval hd hsz hnv2 hp2 hd2 fmapEmpty σ spikeFile
        0 none _ rfl hv2 aid rs
    | @beta_spec pa pb x bty w e2 =>
      rcases hr.sseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
          ⟨_, _, v', _, _, hpat, he1, _, hout⟩ |
          ⟨_, _, ds', v', _, _, hpat, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨pa', pb', x', bty', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', pb', x', bty', ds', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', x', bty', v', _, _, hpat, he1, _, hout⟩
      · exact absurd hstep (fun h => Step.val_elim h)
      · exact (specPat_ne_base hpat.symm).elim
      · exact (specPat_ne_base hpat.symm).elim
      · rw [jumpRedex?_ofVal] at hj; cases hj
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := specPat_inj hpat
        obtain rfl : w = .pure (Vloaded (LVspecified ov')) := by
          have := ofVal_of_toVal (toVal_ofVal w) -- placeholder; use he1
          cases w with
          | pure v0 =>
            obtain rfl : v0 = Vloaded (LVspecified ov') := by
              simpa [ofVal] using he1
            rfl
          | annot ds0 v0 => exact absurd he1 (by simp [ofVal])
        obtain ⟨h1, h2, h3⟩ : r' = e2 ∧
            ρ' = update_env (specPat pa pb x bty)
              (Vloaded (LVspecified ov')) (ev0 :: evs) ∧ σ' = σ := by
          simpa [Prod.mk.injEq] using hout
        subst h2
        obtain rfl : e2 = r' := h1.symm
        obtain rfl : σ = σ' := h3.symm
        unfold engineOutcomesP engineStepsP
        rw [step_ctx_beta_spec_pure hd hsz fmapEmpty σ spikeFile fmapEmpty
          0 none _ rfl rfl]
        rfl
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := specPat_inj hpat
        obtain rfl : w = .annot ds' (Vloaded (LVspecified ov')) := by
          cases w with
          | pure v0 => exact absurd he1 (by simp [ofVal])
          | annot ds0 v0 =>
            obtain ⟨rfl, rfl⟩ : ds0 = ds' ∧ v0 = Vloaded (LVspecified ov') := by
              simpa [ofVal] using he1
            rfl
        obtain ⟨h1, h2, h3⟩ : r' = Expr [] (Eannot ds' e2) ∧
            ρ' = update_env (specPat pa pb x bty)
              (Vloaded (LVspecified ov')) (ev0 :: evs) ∧ σ' = σ := by
          simpa [Prod.mk.injEq] using hout
        subst h1 h2
        obtain rfl : σ = σ' := h3.symm
        unfold engineOutcomesP engineStepsP
        rw [step_ctx_beta_spec_annot hd hsz fmapEmpty σ spikeFile fmapEmpty
          0 none _ rfl rfl]
        rfl
      · exact (symPat_ne_spec hpat).elim
    | @memop mop pes =>
      cases hfr with
      | memop_vals v1 v2 =>
        cases hr with
        | run hj hl hvs => simp [memopRedex] at hj
        | memop_eval hnv hv1' hv2' =>
          rw [valueFromPexprs_pair, valueFromPexpr_val,
            valueFromPexpr_val] at hnv
          cases hnv
        | @memop_ptreq _ _ _ pv1 pv2 b _ _ _ h1 h2 hmem =>
          rw [valueFromPexpr_val] at h1 h2
          obtain rfl : v1 = Vobject (OVpointer pv1) := Option.some.inj h1
          obtain rfl : v2 = Vobject (OVpointer pv2) := Option.some.inj h2
          unfold engineOutcomesP engineStepsP
          rw [step_ctx_memop hd hsz rfl rfl fmapEmpty σ spikeFile fmapEmpty
            0 none _ rfl]
          simp only [List.map_cons, List.map_nil]
          rw [dischargeStep_memop_active hmem]
          rfl
      | memop_op hnvF hp1 hp2 hpd1 hpd2 =>
        obtain ⟨v1, v2, hv1', hv2', hout⟩ := hr.memop_op_inv hnvF
        obtain ⟨h1, h2, h3⟩ : r' = Expr [] (Ememop PtrEq
            [Pexpr [] () (PEval v1), Pexpr [] () (PEval v2)]) ∧
            ρ' = ev0 :: evs ∧ σ' = σ := by
          simpa [Prod.mk.injEq] using hout
        subst h1 h2
        obtain rfl : σ = σ' := h3.symm
        unfold engineOutcomesP engineStepsP
        exact stepDischarge_memop_eval hd hsz hnvF hpd1 hpd2 fmapEmpty σ
          spikeFile 0 none _ rfl hv1' hv2' aid rs
    | @store_op loc ann ty pe2 pe3 mo hnv2R =>
      obtain ⟨hnv3, hp2, hp3, hpd2, hpd3⟩ :
          valueFromPexpr pe3 = none ∧ PePure pe2 ∧ PePure pe3 ∧
          peDepth pe2 ≤ lemDefaultFuel ∧ peDepth pe3 ≤ lemDefaultFuel := by
        cases hfr with
        | store hlib =>
          rw [valueFromPexpr_val] at hnv2R
          cases hnv2R
        | store_op hlib hnv2' hnv3 hp2 hp3 hpd2 hpd3 =>
          exact ⟨hnv3, hp2, hp3, hpd2, hpd3⟩
      obtain ⟨pv, cv, hv2, hv3, hnv3', hout⟩ := hr.store_op_inv hnv2R
      obtain ⟨h1, h2, h3⟩ : r' = storeRedex loc ann false ty pv cv mo ∧
          ρ' = ev0 :: evs ∧ σ' = σ := by
        simpa [Prod.mk.injEq, storeRedex] using hout
      subst h1 h2
      obtain rfl : σ = σ' := h3.symm
      unfold engineOutcomesP engineStepsP
      exact stepDischarge_store_eval hd hsz hnv2R hnv3 hp2 hp3 hpd2 hpd3
        fmapEmpty σ spikeFile 0 none _ rfl hv2 hv3 aid rs
    | @beta_sym pa x bty w e2 =>
      rcases hr.sseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
          ⟨_, _, v', _, _, hpat, he1, _, hout⟩ |
          ⟨_, _, ds', v', _, _, hpat, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨pa', pb', x', bty', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', pb', x', bty', ds', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', x', bty', v', _, _, hpat, he1, _, hout⟩
      · exact absurd hstep (fun h => Step.val_elim h)
      · exact (symPat_ne_base hpat.symm).elim
      · exact (symPat_ne_base hpat.symm).elim
      · rw [jumpRedex?_ofVal] at hj; cases hj
      · exact (symPat_ne_spec hpat.symm).elim
      · exact (symPat_ne_spec hpat.symm).elim
      · obtain ⟨rfl, rfl, rfl⟩ := symPat_inj hpat
        obtain rfl : w = .pure v' := by
          cases w with
          | pure v0 =>
            obtain rfl : v0 = v' := by simpa [ofVal] using he1
            rfl
          | annot ds0 v0 => exact absurd he1 (by simp [ofVal])
        obtain ⟨h1, h2, h3⟩ : r' = e2 ∧
            ρ' = update_env (symPat pa x bty) v' (ev0 :: evs) ∧ σ' = σ := by
          simpa [Prod.mk.injEq] using hout
        subst h2
        obtain rfl : e2 = r' := h1.symm
        obtain rfl : σ = σ' := h3.symm
        unfold engineOutcomesP engineStepsP
        rw [step_ctx_beta_sym_pure hd hsz fmapEmpty σ spikeFile fmapEmpty
          0 none _ rfl rfl]
        rfl
  · obtain ⟨params, cont, vs, ev0', evs', hρeq, hl, hvs, hout⟩ :=
      hr.jump_inv (by rfl)
    have hdep : ∀ pe' ∈ pes, peDepth pe' ≤ lemDefaultFuel := by
      cases hfr with
      | run hdep => exact hdep
    obtain ⟨h1, h2, h3⟩ : e' = cont ∧
        ρ' = bindArgs params vs (ev0 :: evs) ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1 h2
    obtain rfl : σ = σ' := h3.symm
    unfold engineOutcomesP engineStepsP
    exact stepDischarge_run hd hsz hl hdep fmapEmpty σ spikeFile 0 none p
      _ rfl rfl hvs aid rs hQ

end CerberusHeapLang
