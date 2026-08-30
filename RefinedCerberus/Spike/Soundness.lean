/-
RefinedCerberus.Spike.Soundness — spike artifact 4: THE BOUNDARY
MODULE. The only spike module that references the engine's step
machinery (`step_ctx`, Core_reduction.lean:484); everything here
certifies the hand-written `Step` (Step.lean) against the engine at
the frozen minimal context (recon §3.2).

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
    Core_reduction.lean:424; slice-A note D2) — the per-rule lemmas
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
import RefinedCerberus.Spike.Step
import Core_reduction

set_option autoImplicit false

namespace RefinedCerberus.Spike

/-! ## The frozen minimal context (recon §3.2, measured by probe)

tagDefs/extern empty (no structs, no linked externs in the
fragment), default file (only proc/impl lookups read it — the
fragment has none), tid 0, no parent thread, empty environment stack
(wildcard patterns never look anything up), and a hand-built
core_run_state (NEVER initial_core_run_state — that draws sym_supply
through an effectful seam, Core_run_aux.lean:395). -/

/-- The default (empty) Core file. Only proc/impl/funinfo lookups
    read it; the fragment performs none. -/
def spikeFile : generic_file Unit core_run_annotation := default

/-- The frozen thread state around an arena: empty stack, empty env
    frame, no current procedure. An explicit literal so that record
    updates of it reduce definitionally. -/
def spikeThread (e : CoreExpr) : thread_state :=
  { arena := e, stack0 := Stack_empty, errno := default, env := [fmapEmpty],
    current_proc_opt := none, exec_loc := default, current_loc := default }

@[simp] theorem spikeThread_arena (e : CoreExpr) :
    (spikeThread e).arena = e := rfl

/-- The frozen core_run_state (Core_run_aux.lean:353-358). The
    fragment's request monads thread it; only the aid would reach a
    continuation, and the fragment's continuations ignore it (D2). -/
def spikeRunState : core_run_state :=
  { tid_supply := 1, aid_supply := 0, excluded_supply := 0, sym_supply := 0,
    labeled := fmapEmpty }

/-- THE ENGINE ENTRY: one expression-level step of the engine at the
    frozen context — `step_ctx` (Core_reduction.lean:484) verbatim. -/
def engineSteps (e : CoreExpr) (σ : Mem) : List core_step2 :=
  step_ctx fmapEmpty σ spikeFile fmapEmpty 0 (none, spikeThread e)

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
  | _ => .offFragment

/-- The engine's discharged behavior list at a configuration. -/
def engineOutcomes (aid : Nat) (e : CoreExpr) (σ : Mem) : List EngineOutcome :=
  (engineSteps e σ).map (dischargeStep aid spikeRunState σ)

/-! ## The size measure (fuel accounting; see FUEL HONESTY above) -/

/-- Nesting depth of the sequencing/annotation spine — an upper
    bound for get_ctx's fuel use on the fragment. -/
def esize : CoreExpr → Nat
  | Expr _ (Esseq _ e1 e2) => 1 + max (esize e1) (esize e2)
  | Expr _ (Eannot _ b) => 1 + esize b
  | _ => 1

/-! ## The fragment cone -/

/-- The syntactic fragment (canonical shapes, closed under Step —
    `FragP.step`): pure values, positive non-library store/load with
    canonical value operands, wildcard strong sequencing, and the
    run-time Eannot residue. Node annotation lists are pinned `[]`
    (what authored programs and every engine successor produce);
    `isLibraryLocation loc = false` freezes step_ctx's
    library-location current_loc substitution out of the fragment
    (slice-A D5). -/
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

/-- Rebuild of a redex-step through the decomposition — certifies
    Step's two congruence rules (sseq_ctx / annot_ctx) against
    get_ctx-descent + apply_ctx-rebuild. -/
theorem Decomp.rebuild {e : CoreExpr} {ctx : context} {r r' : CoreExpr}
    {σ σ' : Mem} (h : Decomp e ctx r) (hs : Step (r, σ) (r', σ')) :
    Step (e, σ) (apply_ctx ctx r', σ') := by
  induction h with
  | root _ => exact hs
  | sseq _ ih => exact Step.sseq_ctx (ih hs)
  | annot hroot _ _ _ ih => exact Step.annot_ctx hroot (ih hs)

/-- Factorization: every Step of a decomposed term is a Step of its
    redex, rebuilt. (The inversion direction of the congruence
    certification; with the per-redex inversions it converts engine
    refusals into global Step-stuckness.) -/
theorem Decomp.step_factor {e : CoreExpr} {ctx : context} {r : CoreExpr}
    {σ : Mem} {out : CoreExpr × Mem} (h : Decomp e ctx r)
    (hs : Step (e, σ) out) :
    ∃ r' σ', Step (r, σ) (r', σ') ∧ out = (apply_ctx ctx r', σ') := by
  induction h generalizing out with
  | root _ => exact ⟨out.1, out.2, hs, rfl⟩
  | sseq hd ih =>
    rcases hs.sseq_inv with ⟨e1', σ'', hstep, hout⟩ | ⟨_, _, v, _, he1, _⟩ |
        ⟨_, _, ds, v, _, he1, _⟩
    · obtain ⟨r', σr, hr, heq⟩ := ih hstep
      injection heq with he hσ
      subst he hσ
      exact ⟨r', _, hr, by rw [hout]; rfl⟩
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
  | annot hroot _ _ hd ih =>
    rcases hs.annot_inv with ⟨_, b', σ'', hstep, hout⟩ | ⟨a2, ds2, c, hb, _⟩
    · obtain ⟨r', σr, hr, heq⟩ := ih hstep
      injection heq with he hσ
      subst he hσ
      exact ⟨r', _, hr, by rw [hout]; rfl⟩
    · rw [hb] at hroot
      simp [annotRooted] at hroot

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
    (hd : Decomp e ctx (storeRedex loc ann lk ty pv cv mo))
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
    (hd : Decomp e ctx (storeRedex loc ann lk ty pv cv mo))
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
    (hd : Decomp e ctx (loadRedex loc ann ty pv mo))
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
    (hd : Decomp e ctx (createRedex loc ann align ty pref))
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
    (hd : Decomp e ctx
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
    (hd : Decomp e ctx
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
    (hd : Decomp e ctx (Expr [] (Eannot ds1 (Expr [] (Eannot ds2 b)))))
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

theorem engineSteps_done (v : value) (σ : Mem) :
    engineSteps (ofVal (.pure v)) σ = [Step_done2 v] :=
  step_ctx_done v fmapEmpty σ spikeFile fmapEmpty 0 _ rfl rfl

theorem engineSteps_remove_annot (ds : List dyn_annotation) (v : value)
    (σ : Mem) :
    engineSteps (ofVal (.annot ds v)) σ =
      [Step_tau2 "CTX, Eannot(value)" TSK_Misc (spikeThread (ofVal (.pure v)))] :=
  step_ctx_remove_annot ds v fmapEmpty σ spikeFile fmapEmpty 0 none _ rfl

theorem engineSteps_store {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
    {ty : ctype} {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
    {mv : CerbMem.MemValue}
    (hd : Decomp e ctx (storeRedex loc ann lk ty pv cv mo))
    (hsz : esize e ≤ lemDefaultFuel)
    (hlib : CerbLocation.isLibraryLocation loc = false)
    (hmv : memValueFromValue fmapEmpty (Ctype [] (unatomic_ ty)) cv = some mv)
    (σ : Mem) :
    engineSteps e σ =
      [Step_action_request2 "StoreRequest" loc 0 (is_unseq_with_ccall ctx)
        (stExceptUndef_return (StoreRequest2 mo ty lk pv mv
          (fun (_ : Nat) (fp : CerbMem.Footprint) =>
            spikeThread (apply_ctx ctx (Expr [] (Eannot [DA_pos [] fp]
              (Expr [] (Epure (Pexpr [] () (PEval Vunit))))))))))] :=
  step_ctx_store hd hsz hlib fmapEmpty hmv σ spikeFile fmapEmpty 0 none _ rfl

theorem engineSteps_store_illtyped {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
    {ty : ctype} {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
    (hd : Decomp e ctx (storeRedex loc ann lk ty pv cv mo))
    (hsz : esize e ≤ lemDefaultFuel)
    (hmv : memValueFromValue fmapEmpty (Ctype [] (unatomic_ ty)) cv = none)
    (σ : Mem) :
    engineSteps e σ =
      [Step_error2 (String.append (CerbLocation.stringFromLocation loc)
        (String.append "the value of a store("
          (String.append (CerbPP.stringFromCore_ctype (Ctype [] (unatomic_ ty)))
            (String.append ") didn't match the lvalue type: "
              (CerbPP.stringFromCore_value cv)))))] :=
  step_ctx_store_illtyped hd hsz fmapEmpty hmv σ spikeFile fmapEmpty 0 none _ rfl

theorem engineSteps_load {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pv : CerbMem.PointerValue} {mo : memory_order}
    (hd : Decomp e ctx (loadRedex loc ann ty pv mo))
    (hsz : esize e ≤ lemDefaultFuel)
    (hlib : CerbLocation.isLibraryLocation loc = false)
    (σ : Mem) :
    engineSteps e σ =
      [Step_action_request2 "LoadRequest" loc 0 (is_unseq_with_ccall ctx)
        (stExceptUndef_return (LoadRequest2 mo ty pv
          (fun (_ : Nat) (fp : CerbMem.Footprint) (mval : CerbMem.MemValue) =>
            spikeThread (apply_ctx ctx (Expr [] (Eannot [DA_pos [] fp]
              (Expr [] (Epure (Pexpr [] () (PEval
                (valueFromMemValue mval).2))))))))))] :=
  step_ctx_load hd hsz hlib fmapEmpty σ spikeFile fmapEmpty 0 none _ rfl

theorem engineSteps_create {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {align : CerbMem.IntegerValue} {ty : ctype} {pref : prefix0}
    (hd : Decomp e ctx (createRedex loc ann align ty pref))
    (hsz : esize e ≤ lemDefaultFuel)
    (hlib : CerbLocation.isLibraryLocation loc = false)
    (σ : Mem) :
    engineSteps e σ =
      [Step_action_request2 "CreateRequest" loc 0 (is_unseq_with_ccall ctx)
        (stExceptUndef_return (CreateRequest2 pref align ty
          (get_with_address []) none
          (fun (_ : Nat) (pv : CerbMem.PointerValue) =>
            spikeThread (apply_ctx ctx
              (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer pv)))))))))) ] :=
  step_ctx_create hd hsz hlib fmapEmpty σ spikeFile fmapEmpty 0 none _ rfl

theorem engineSteps_beta_pure {e : CoreExpr} {ctx : context}
    {pa : List _root_.annot} {bty : core_base_type} {v : value} {e2 : CoreExpr}
    (hd : Decomp e ctx
      (Expr [] (Esseq (Pattern pa (CaseBase (none, bty))) (ofVal (.pure v)) e2)))
    (hsz : esize e ≤ lemDefaultFuel) (σ : Mem) :
    engineSteps e σ = [Step_tau2 "Esseq" TSK_Misc (spikeThread (apply_ctx ctx e2))] :=
  step_ctx_beta_pure hd hsz fmapEmpty σ spikeFile fmapEmpty 0 none _ rfl rfl

theorem engineSteps_beta_annot {e : CoreExpr} {ctx : context}
    {pa : List _root_.annot} {bty : core_base_type} {ds : List dyn_annotation}
    {v : value} {e2 : CoreExpr}
    (hd : Decomp e ctx
      (Expr [] (Esseq (Pattern pa (CaseBase (none, bty))) (ofVal (.annot ds v)) e2)))
    (hsz : esize e ≤ lemDefaultFuel) (σ : Mem) :
    engineSteps e σ =
      [Step_tau2 "Esseq Eannot" TSK_Misc
        (spikeThread (apply_ctx ctx (Expr [] (Eannot ds e2))))] :=
  step_ctx_beta_annot hd hsz fmapEmpty σ spikeFile fmapEmpty 0 none _ rfl rfl

theorem engineSteps_merge {e : CoreExpr} {ctx : context}
    {ds1 ds2 : List dyn_annotation} {b : CoreExpr}
    (hd : Decomp e ctx (Expr [] (Eannot ds1 (Expr [] (Eannot ds2 b)))))
    (hirr : is_irreducible (Expr [] (Eannot ds1 (Expr [] (Eannot ds2 b)))) = false)
    (hsz : esize e ≤ lemDefaultFuel) (σ : Mem) :
    engineSteps e σ =
      [Step_tau2 "Eannot" TSK_Misc
        (spikeThread (apply_ctx ctx (Expr [] (Eannot (ds1 ++ ds2) b))))] :=
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

@[simp] theorem esize_ofVal_pure {v : value} : esize (ofVal (.pure v)) = 1 := rfl

@[simp] theorem esize_ofVal_annot {ds : List dyn_annotation} {v : value} :
    esize (ofVal (.annot ds v)) = 2 := rfl

/-- One Step grows the spine measure by at most one (only the action
    rules grow it: a 1-node redex becomes a 2-node annotated value). -/
theorem Step.esize_succ {c c' : CoreExpr × Mem} (h : Step c c') :
    esize c'.1 ≤ esize c.1 + 1 := by
  induction h with
  | store hmv hmem => simp
  | load hmem => simp
  | create hmem => simp
  | sseq_pure => simp; omega
  | sseq_annot => simp; omega
  | sseq_ctx hs ih => simp at ih ⊢; omega
  | annot_ctx hg hs ih => simp at ih ⊢; omega
  | annot_merge => simp; omega

/-- The fragment is closed under Step. -/
theorem FragP.step {e : CoreExpr} {σ : Mem} {e' : CoreExpr} {σ' : Mem}
    (hf : FragP e) (hs : Step (e, σ) (e', σ')) : FragP e' := by
  induction hf generalizing e' σ' with
  | val_pure v => exact (Step.val_elim (w := .pure v) hs).elim
  | store hlib =>
    obtain ⟨mv, fp, σ'', hmv, hmem, hout⟩ := hs.store_inv
    injection hout with h1 h2
    subst h1
    exact .annot (.val_pure Vunit)
  | load hlib =>
    obtain ⟨fp, mval, σ'', hmem, hout⟩ := hs.load_inv
    injection hout with h1 h2
    subst h1
    exact .annot (.val_pure _)
  | create hlib =>
    obtain ⟨pv, σ'', hmem, hout⟩ := hs.create_inv
    injection hout with h1 h2
    subst h1
    exact .val_pure _
  | sseq hf1 hf2 ih1 ih2 =>
    rcases hs.sseq_inv with ⟨e1', σ'', hstep, hout⟩ | ⟨_, _, v, _, _, hout⟩ |
        ⟨_, _, ds', v, _, _, hout⟩
    · injection hout with h1 h2
      subst h1
      exact .sseq (ih1 hstep) hf2
    · injection hout with h1 h2
      subst h1
      exact hf2
    · injection hout with h1 h2
      subst h1
      exact .annot hf2
  | annot hfb ihb =>
    rcases hs.annot_inv with ⟨hg, b', σ'', hstep, hout⟩ | ⟨a2, ds2, c, hb, hout⟩
    · injection hout with h1 h2
      subst h1
      exact .annot (ihb hstep)
    · subst hb
      injection hout with h1 h2
      subst h1
      cases hfb with
      | annot hfc => exact .annot hfc

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
    tau), or a refusal at a provably Step-stuck configuration. -/
inductive EngineMatch (e : CoreExpr) (σ : Mem) : EngineOutcome → Prop where
  | step {e' : CoreExpr} {σ' : Mem} :
      Step (e, σ) (e', σ') → EngineMatch e σ (.next (spikeThread e') σ')
  | removeAnnot {ds : List dyn_annotation} {v : value} :
      e = ofVal (.annot ds v) →
      EngineMatch e σ (.next (spikeThread (ofVal (.pure v))) σ)
  | done {v : value} : e = ofVal (.pure v) → EngineMatch e σ (.done v)
  | refused {o : EngineOutcome} : o.isRefusal →
      (∀ out, ¬ Step (e, σ) out) → toVal e = none → EngineMatch e σ o

/-- ENGINE-COMPLETENESS ON THE FRAGMENT (the artifact-4 theorem):
    at every fragment configuration, at any aid and memory state, the
    engine has EXACTLY ONE behavior, and it is matched by Step. -/
theorem engine_complete (aid : Nat) (σ : Mem) {e : CoreExpr}
    (hf : FragP e) (hsz : esize e ≤ lemDefaultFuel) :
    ∃ o, engineOutcomes aid e σ = [o] ∧ EngineMatch e σ o := by
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
        have heq := engineSteps_store_illtyped hd hsz hmv σ
        have hns : ∀ out, ¬ Step (e, σ) out := by
          intro out hstep
          obtain ⟨r', σ', hr, _⟩ := hd.step_factor hstep
          obtain ⟨mv', _, _, hmv', _, _⟩ := hr.store_inv
          rw [hmv] at hmv'
          cases hmv'
        have hlist : engineOutcomes aid e σ =
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
        have heq := engineSteps_store hd hsz hlib hmv σ
        cases happ : applyMemM (CerbMem.storeM loc ty lk pv mv) σ with
        | some p =>
          rcases p with ⟨fp, σ'⟩
          refine ⟨_, ?_, EngineMatch.step (hd.rebuild (Step.store hmv happ))⟩
          unfold engineOutcomes
          rw [heq]
          simp only [List.map_cons, List.map_nil]
          rw [dischargeStep_store_active happ]
        | none =>
          have hns : ∀ out, ¬ Step (e, σ) out := by
            intro out hstep
            obtain ⟨r', σ', hr, _⟩ := hd.step_factor hstep
            obtain ⟨mv', fp', σ'', hmv', happ', _⟩ := hr.store_inv
            rw [hmv] at hmv'
            obtain rfl : mv = mv' := Option.some.inj hmv'
            rw [happ] at happ'
            cases happ'
          refine ⟨dischargeStep aid spikeRunState σ (Step_action_request2 "StoreRequest" loc 0
              (is_unseq_with_ccall ctx) (stExceptUndef_return
                (StoreRequest2 mo ty lk pv mv
                  (fun (_ : Nat) (fp : CerbMem.Footprint) =>
                    spikeThread (apply_ctx ctx (Expr [] (Eannot [DA_pos [] fp]
                      (Expr [] (Epure (Pexpr [] () (PEval Vunit))))))))))), ?_,
            EngineMatch.refused (dischargeStep_store_refusal happ) hns hv⟩
          unfold engineOutcomes
          rw [heq]
          rfl
    | @load loc ann ty pv mo hlib =>
      have heq := engineSteps_load hd hsz hlib σ
      cases happ : applyMemM (CerbMem.loadM loc ty pv) σ with
      | some p =>
        rcases p with ⟨⟨fp, mval⟩, σ'⟩
        refine ⟨_, ?_, EngineMatch.step (hd.rebuild (Step.load happ))⟩
        unfold engineOutcomes
        rw [heq]
        simp only [List.map_cons, List.map_nil]
        rw [dischargeStep_load_active happ]
      | none =>
        have hns : ∀ out, ¬ Step (e, σ) out := by
          intro out hstep
          obtain ⟨r', σ', hr, _⟩ := hd.step_factor hstep
          obtain ⟨fp', mval', σ'', happ', _⟩ := hr.load_inv
          rw [happ] at happ'
          cases happ'
        refine ⟨dischargeStep aid spikeRunState σ (Step_action_request2 "LoadRequest" loc 0
            (is_unseq_with_ccall ctx) (stExceptUndef_return (LoadRequest2 mo ty pv
              (fun (_ : Nat) (fp : CerbMem.Footprint) (mval : CerbMem.MemValue) =>
                spikeThread (apply_ctx ctx (Expr [] (Eannot [DA_pos [] fp]
                  (Expr [] (Epure (Pexpr [] () (PEval
                    (valueFromMemValue mval).2))))))))))), ?_,
          EngineMatch.refused (dischargeStep_load_refusal happ) hns hv⟩
        unfold engineOutcomes
        rw [heq]
        rfl
    | @create loc ann align ty pref hlib =>
      have heq := engineSteps_create hd hsz hlib σ
      cases happ : applyMemM (CerbMem.allocateObject 0 pref align ty none none) σ with
      | some p =>
        rcases p with ⟨pv, σ'⟩
        refine ⟨_, ?_, EngineMatch.step (hd.rebuild (Step.create happ))⟩
        unfold engineOutcomes
        rw [heq]
        simp only [List.map_cons, List.map_nil]
        rw [dischargeStep_create_active (reqAddr := get_with_address []) happ]
      | none =>
        have hns : ∀ out, ¬ Step (e, σ) out := by
          intro out hstep
          obtain ⟨r', σ', hr, _⟩ := hd.step_factor hstep
          obtain ⟨pv', σ'', happ', _⟩ := hr.create_inv
          rw [happ] at happ'
          cases happ'
        refine ⟨dischargeStep aid spikeRunState σ (Step_action_request2 "CreateRequest" loc 0
            (is_unseq_with_ccall ctx) (stExceptUndef_return (CreateRequest2 pref align ty
              (get_with_address []) none
              (fun (_ : Nat) (pv : CerbMem.PointerValue) =>
                spikeThread (apply_ctx ctx (Expr [] (Epure
                  (Pexpr [] () (PEval (Vobject (OVpointer pv))))))))))), ?_,
          EngineMatch.refused (dischargeStep_create_refusal (reqAddr := get_with_address []) happ)
            hns hv⟩
        unfold engineOutcomes
        rw [heq]
        rfl
    | @beta_pure pa bty v e2 =>
      have heq := engineSteps_beta_pure hd hsz σ
      refine ⟨_, ?_, EngineMatch.step (hd.rebuild Step.sseq_pure)⟩
      unfold engineOutcomes
      rw [heq]
      rfl
    | @beta_annot pa bty ds v e2 =>
      have heq := engineSteps_beta_annot hd hsz σ
      refine ⟨_, ?_, EngineMatch.step (hd.rebuild Step.sseq_annot)⟩
      unfold engineOutcomes
      rw [heq]
      rfl
    | @merge ds1 ds2 b hirr =>
      have heq := engineSteps_merge hd hirr hsz σ
      refine ⟨_, ?_, EngineMatch.step (hd.rebuild Step.annot_merge)⟩
      unfold engineOutcomes
      rw [heq]
      rfl

end RefinedCerberus.Spike
