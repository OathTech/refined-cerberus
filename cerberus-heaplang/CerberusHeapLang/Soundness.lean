/-
CerberusHeapLang.Soundness — THE BOUNDARY MODULE: the only module
that references the engine's step machinery (`step_ctx`,
Core_reduction.lean:484); everything here certifies the hand-written
`Step` (Step.lean) against the engine, at any machine context.

WHAT IS PROVED (the certification direction, and why it suffices):

MATCH-GIVEN-STEP ON THE FRAGMENT, per construct, at ANY machine
context: wherever the mirror `Step M` steps at a `Frag` configuration
(cons-shaped environment, `esize e ≤ lemDefaultFuel`), the engine's
step list is a SINGLETON whose discharge (the Driver.lean:273 memM
protocol, projected to (thread_state, MemState)) is exactly that
step — `engine_step_matchU`, assembled from one `step_ctx_*` lemma
per `Step` rule (the redex fires under get_ctx's descent and
`apply_ctx` rebuilds the context: `Decomp.step_factor`) and the
per-action discharge computations (`dischargeStep_*`). The value
protocol is certified separately (`outcomesU_done`,
`outcomesU_remove_annot`: the engine taus `{A}v --> v` where Step
treats `{A}v` as a value, then reports `Step_done2 v`). Refusals are
classified where the engine's refusal channel is a value (Round.lean,
`cerberusRound_refused_*`), never assumed.

Why this direction suffices for adequacy (Adequacy.lean): the WP's
NotStuck obligation (proved against Step) guarantees every reachable
fragment configuration is a Step-value or Step-reducible; at such a
configuration the engine's one behaviour IS the matched step (or the
value protocol), so the engine can never kill and its final value is
the one the WP's postcondition speaks about. The soundness direction
(every Step is engine-realizable) is NOT needed for that statement
and is not claimed; the active-path equalities in the per-rule lemmas
are exact (iff-grade on the fragment: `step_iff_cerberusRound`), so
nothing here relies on Step over-approximating.

THE DISCHARGE MIRROR (`dischargeStep`): `Step_action_request2`'s
request monad is run on the context's core_run_state and the request
discharged against the REAL CerbMem.loadM/storeM/allocateObject
exactly as the sequential driver does (action_request_sequential2,
Driver.lean:273), with the following projections, each cited:
  - `prefixOfPointer` is dropped: it is `memReturn none`
    (CerbMem.lean:2064) — state-invariant and never-killing, its
    result only enters the driver's trace;
  - the driver_state wrapper (trace events, fs, concurrency,
    dr_step_counter) is projected away — the fragment reads and
    writes only the thread_state and the MemState;
  - the aid drawn by perform_action_request2 (Driver.lean:284) is an
    arbitrary parameter here: the fragment's positive non-excluded
    continuations build `DA_pos [] fp` and ignore it (step_action,
    Core_reduction.lean:424) — the per-rule lemmas hold for every aid.
`Step_with_runstate2` (the guard/argument evaluation and `Erun`
rounds) and `Step_memop_request2` (`PtrEq`) are discharged the same
way; the arms are documented at the definition.

FUEL HONESTY: the engine's get_ctx is fuel-bounded (get_ctx_lemFuel,
Core_reduction.lean:373, budget lemDefaultFuel = 10^6) and its
exhaustion leaf is opaque (LemLib fuelExhausted — deliberately not
provably equal to anything). Every statement about a symbolic
configuration therefore carries an `esize e ≤ lemDefaultFuel` side
condition. `esize` grows by at most 1 per straight-line step and is
reset by a jump to the registered body's own size
(`Frag.esize_step_bound`); the drive statements do NOT carry that
run-length-coupled form — Potential.lean's step-monotone potential
`pot` (`esize e ≤ pot e`; `pot` never increases along a step except
for the jump reset) turns it into the two STATIC premises `pot e₀ ≤
lemDefaultFuel` and `pot cont ≤ lemDefaultFuel` per registered label
body that Adequacy.lean and TotalAdequacy.lean carry, with the drive
length unbounded. The pure-expression evaluator is fuelled at the
same budget; its bound is the second static premise family, `peDepth
pe ≤ lemDefaultFuel` on the operands of `Frag.if_`/`run`/`save`/
`load_op`/`memop_op`/`store_op` (the pure-evaluator bridge section
below). Both are honest engine artifacts, not slack: past the budget
the engine really does bail.
-/
import CerberusHeapLang.Step
import CerberusHeapLang.EnvLaws
import Core_reduction

set_option autoImplicit false

namespace CerberusHeapLang

/-! ## The frozen minimal context (measured by probe —
docs/2026-08-30_spike-recon.md §3.2)

tagDefs/extern empty (no structs, no linked externs in the
fragment), default file (only proc/impl lookups read it — the
fragment has none), tid 0, no parent thread, empty environment stack
(wildcard patterns never look anything up), and a hand-built
core_run_state (NEVER initial_core_run_state — that seeds sym_supply
from the entry's supply argument, Core_run_aux.lean:406). -/

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

/-- The frozen profiles' thread literals are the context instances'
    threads, definitionally. -/
theorem spikeCtx_thread (e : CoreExpr) (ρ : EnvStack) :
    spikeCtx.thread e ρ spikeCtl = envThread e ρ := rfl

/-- THE ENGINE ENTRY AT A MACHINE CONTEXT (S1b, the unified
    configuration): one engine step at context `M` — `step_ctx`
    (Core_reduction.lean:484) with every immutable supplied by the
    context. -/
def engineStepsU (M : MachineCtx) (e : CoreExpr) (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    List core_step2 :=
  step_ctx M.tagDefs σ M.file M.extern M.tid (M.parent, M.thread e ρ ctl)

/-! ## The discharge (the Driver.lean:273 protocol, projected) -/

/-- One discharged engine behavior. `offFragment` marks core_step2
    forms the fragment never produces (`engine_step_matchU`: wherever
    the mirror steps, the engine's behavior is the matched `next`;
    the off-fragment forms can only arise where Step is stuck). -/
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
def dischargeStep (tds : CerbTags.TagDefsMap) (aid : Nat) (rs : core_run_state)
    (σ : Mem) : core_step2 → EngineOutcome
  | Step_tau2 _ _ th' => .next th' σ
  | Step_done2 v => .done v
  | Step_error2 s => .error s
  | Step_action_request2 _ loc _ _ m =>
    match m rs with
    | Result (Defined req, _) =>
      match req with
      | StoreRequest2 _mo ty lk pv mv k =>
        (match CerbMem.storeM tds loc ty lk pv mv with
         | ND f =>
           match f σ with
           | (NDactive fp, σ') => .next (k aid fp) σ'
           | (NDkilled r, _) => .killed r
           | _ => .offFragment)
      | LoadRequest2 _mo ty pv k =>
        (match CerbMem.loadM tds loc ty pv with
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
        (match CerbMem.allocateObject tds 0 pref align ty reqAddr initOpt with
         | ND f =>
           match f σ with
           | (NDactive pv, σ') => .next (k aid pv) σ'
           | (NDkilled r, _) => .killed r
           | _ => .offFragment)
      | KillRequest2 isDyn pv k =>
        -- kill/free arc K2: the driver's KillRequest discharge
        -- (Driver.lean:273, `liftMem (CerbMem.killM loc1 is_dynamic1
        -- ptr_val)`, continuation `mk_th_st' aid1`). Before K2 a kill
        -- request was `.offFragment` here; this arm is a PROOF DEVICE
        -- (the `driveU` lanes' discharge), not a statement referent.
        (match CerbMem.killM loc isDyn pv with
         | ND f =>
           match f σ with
           | (NDactive _, σ') => .next (k aid) σ'
           | (NDkilled r, _) => .killed r
           | _ => .offFragment)
      | AllocRequest2 pref align size k =>
        -- kill/free arc K3: the driver's AllocRequest discharge
        -- (Driver.lean:273, `liftMem (CerbMem.allocateRegion tid1 pref
        -- align_ival size_ival)`, continuation `mk_th_st' aid1 ptrval`).
        -- allocateRegion discards its tid argument (CerbMem.lean:1533,
        -- `_ : Nat`), so the projection passes 0 (`allocateRegion_arg_irrel`).
        -- Before K3 an alloc request was `.offFragment` here; the arm is a
        -- PROOF DEVICE (the `driveU` lanes' discharge), not a statement referent.
        (match CerbMem.allocateRegion 0 pref align size with
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

/-- The engine's discharged behavior list at a machine context
    (engine steps at `M`, discharged against `M`'s run state). -/
def outcomesU (M : MachineCtx) (aid : Nat) (e : CoreExpr) (ρ : EnvStack)
    (ctl : Ctl) (σ : Mem) : List EngineOutcome :=
  (engineStepsU M e ρ ctl σ).map (dischargeStep M.tagDefs aid M.runState σ)

/-! ## The size measure (fuel accounting; see FUEL HONESTY above) -/

/-! Nesting depth of the sequencing/annotation spine — an upper
    bound for get_ctx's fuel use on the fragment.

    S1b EXTENSION (sanctioned statement-change class (E), design
    record §5.3/§6): the `Ecase` arm — `1 + max over branch bodies`
    (the `Eif` precedent) — extends the fuel accounting to case
    branches; the S1a probe found `esize (Ecase …) = 1` made the
    additive accounting FALSE for case steps with non-flat branches
    (one more face of the F-01 cone gap). CONSERVATIVITY: on every
    pre-existing constructor the measure is provably unchanged — the
    per-constructor `rfl` equations below (`esize_sseq`,
    `esize_annot`, `esize_pure`, `esize_action`, `esize_memop`,
    `esize_if`, `esize_save`, `esize_other`) hold by `rfl` exactly as
    before; only Ecase-containing terms (none in the pre-S1b corpus)
    change value. -/
mutual
/-- The size measure (see the section comment above; the `Ewseq` arm
    is the S1b DRIFT-TEST extension — same conservativity discipline
    as the Ecase arm: every pre-existing constructor's equation still
    holds by `rfl`, only Ewseq-containing terms, none in the prior
    corpus, change value). -/
def esize : CoreExpr → Nat
  | Expr _ (Esseq _ e1 e2) => 1 + max (esize e1) (esize e2)
  | Expr _ (Ewseq _ e1 e2) => 1 + max (esize e1) (esize e2)
  | Expr _ (Eannot _ b) => 1 + esize b
  | Expr _ (Eif _ e2 e3) => 1 + max (esize e2) (esize e3)
  | Expr _ (Esave _ _ body) => 1 + esize body
  | Expr _ (Ecase _ pats) => 1 + esizeAlts pats
  | _ => 1

/-- Max branch-body size of a case alternative list (0 at nil — the
    empty case's step is a no-match refusal, never a branch entry). -/
def esizeAlts : List (pattern × CoreExpr) → Nat
  | [] => 0
  | (_, e) :: rest => max (esize e) (esizeAlts rest)
end

/-! ## Small facts about values and irreducibility -/

/-- Canonical redex spellings (the exact node shapes `Frag.store`/
    `Frag.load` range over; also the spellings Rules.lean's
    storeExpr/loadExpr produce). -/
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

@[simp] theorem is_irreducible_wseq {a : List annot} {pat : pattern}
    {e1 e2 : CoreExpr} :
    is_irreducible (Expr a (Ewseq pat e1 e2)) = false := rfl

@[simp] theorem is_irreducible_action {a : List annot}
    {p : generic_paction core_run_annotation Unit sym} :
    is_irreducible (Expr a (Eaction p)) = false := rfl

/-- A value form under `toVal` is irreducible in the engine's sense. -/
theorem is_irreducible_of_toVal {e : CoreExpr} {w : SpikeVal}
    (h : toVal e = some w) : is_irreducible e = true := by
  rw [← ofVal_of_toVal h]; exact is_irreducible_ofVal w

/-! ## The redex classification and the decomposition judgment

S1b UNIFICATION (design record §1/§8.3): ONE root-redex
classification (`Redex` — the migrated `Redex` with the phase-1
base shapes inlined) and ONE decomposition judgment (`Decomp` — the
migrated `Decomp`). The parallel phase-1 `Redex`/`Decomp` pair and
its lemma suite are DELETED (prune-don't-merge); the straight-line
two-sidedness island that outlived it (`StraightRoot`/`StraightFrag`/
`engine_complete`, a second collapse of the production pipeline with
no live consumer) was retired at QA-2 (docs/2026-09-02_qa2-notes.md).
The one cone is `Frag`. -/

/-! ## esize bookkeeping -/

@[simp] theorem esize_sseq {a : List annot} {pat : pattern} {e1 e2 : CoreExpr} :
    esize (Expr a (Esseq pat e1 e2)) = 1 + max (esize e1) (esize e2) := rfl

@[simp] theorem esize_wseq {a : List annot} {pat : pattern} {e1 e2 : CoreExpr} :
    esize (Expr a (Ewseq pat e1 e2)) = 1 + max (esize e1) (esize e2) := rfl

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

theorem get_ctx_wseq {a : List annot} {pat : pattern} {e1 e2 : CoreExpr}
    (h : is_irreducible e1 = false) (n : Nat) :
    get_ctx_lemFuel (n+1) (Expr a (Ewseq pat e1 e2)) =
      List.map (fun p => (Cwseq a pat p.1 e2, p.2)) (get_ctx_lemFuel n e1) := by
  rw [show get_ctx_lemFuel (n+1) (Expr a (Ewseq pat e1 e2)) =
      (if is_irreducible e1 = true then [(CTX, Expr a (Ewseq pat e1 e2))]
       else List.map (fun p => (Cwseq a pat p.1 e2, p.2)) (get_ctx_lemFuel n e1))
    from rfl, h]
  rfl

theorem get_ctx_wseq_val {a : List annot} {pat : pattern} {w : SpikeVal}
    {e2 : CoreExpr} (n : Nat) :
    get_ctx_lemFuel (n+1) (Expr a (Ewseq pat (ofVal w) e2)) =
      [(CTX, Expr a (Ewseq pat (ofVal w) e2))] := by
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
  stack (except PROGRAM-DONE), the parent tid (except PROGRAM-DONE),
  and the memory σ for the pure taus. current_loc is never WRITTEN
  (the fragment's `[]` node annotations keep get_loc = none) and is
  READ only into the action request's location (`requestLoc` — the
  engine's loc' let), where it reaches the kill payload and the
  driver's trace, never the active result or the memory
  (`storeM_loc_irrel`/`loadM_loc_irrel`, Step.lean).
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

The adequacy drive consumes these strong forms through
`engine_step_matchU`; no frozen-context corollaries exist. -/

/-! ### The extended redex/decomposition layer (S3)

`Redex`/`Decomp` extend the phase-1 `Redex`/`Decomp` with the four
new root shapes (Esave / Eif / Ecase / Erun — all singleton `get_ctx`
roots, readiness §3 ND-collapse row). The phase-1 `Decomp` and its
lemmas stay VERBATIM (their jump disjuncts are vacuous —
`Decomp.jumpRedex?_none`); the jump-carrying factor theorem is
`Decomp.step_factor` — the readiness's "factor theorem gains one
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

inductive Redex : CoreExpr → Prop where
  | store {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
      {ty : ctype} {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order} :
      Redex (storeRedex loc ann lk ty pv cv mo)
  | load {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
      {pv : CerbMem.PointerValue} {mo : memory_order} :
      Redex (loadRedex loc ann ty pv mo)
  | create {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {align : CerbMem.IntegerValue} {ty : ctype} {pref : prefix0} :
      Redex (createRedex loc ann align ty pref)
  /-- The kill redex at an evaluated pointer, any kind (kill/free arc K2). -/
  | kill {loc : CerbLocation.Loc} {ann : core_run_annotation} {kind : kill_kind}
      {pv : CerbMem.PointerValue} :
      Redex (killRedex loc ann kind pv)
  /-- The kill ACTION_EVAL redex (unevaluated pointer operand). -/
  | kill_op (loc : CerbLocation.Loc) (ann : core_run_annotation)
      (kind : kill_kind) {pe : generic_pexpr Unit sym}
      (hnv : valueFromPexpr pe = none) :
      Redex (killOpRedex loc ann kind pe)
  /-- The alloc redex at evaluated integer operands (kill/free arc K3). -/
  | alloc {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {align size : CerbMem.IntegerValue} {pref : prefix0} :
      Redex (allocRedex loc ann align size pref)
  /-- The alloc ACTION_EVAL redex (operands not all values). -/
  | alloc_op (loc : CerbLocation.Loc) (ann : core_run_annotation)
      (pref : prefix0) {pe1 pe2 : generic_pexpr Unit sym}
      (hnv : valueFromPexprs [pe1, pe2] = none) :
      Redex (allocOpRedex loc ann pe1 pe2 pref)
  | beta_pure {pa : List annot} {bty : core_base_type} {v : value}
      {e2 : CoreExpr} :
      Redex (Expr [] (Esseq (Pattern pa (CaseBase (none, bty)))
        (ofVal (.pure v)) e2))
  | beta_annot {pa : List annot} {bty : core_base_type}
      {ds : List dyn_annotation} {v : value} {e2 : CoreExpr} :
      Redex (Expr [] (Esseq (Pattern pa (CaseBase (none, bty)))
        (ofVal (.annot ds v)) e2))
  | merge {ds1 ds2 : List dyn_annotation} {b : CoreExpr}
      (hirr : is_irreducible
        (Expr [] (Eannot ds1 (Expr [] (Eannot ds2 b)))) = false) :
      Redex (Expr [] (Eannot ds1 (Expr [] (Eannot ds2 b))))
  | save (sb : sym × core_base_type)
      (ps : List (sym × ((core_base_type ×
        Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)))
      (body : CoreExpr) : Redex (saveRedex sb ps body)
  | if_ (g : generic_pexpr Unit sym) (e2 e3 : CoreExpr) :
      Redex (ifRedex g e2 e3)
  | case_ (pe : generic_pexpr Unit sym) (pats : List (pattern × CoreExpr)) :
      Redex (caseRedex pe pats)
  | run (ra : core_run_annotation) (l : sym)
      (pes : List (generic_pexpr Unit sym)) : Redex (runRedex ra l pes)
  | pure_e {pe : generic_pexpr Unit sym}
      (hnv : valueFromPexpr pe = none) : Redex (pureRedex pe)
  | load_op (loc : CerbLocation.Loc) (ann : core_run_annotation)
      (ty : ctype) {pe2 : generic_pexpr Unit sym} (mo : memory_order)
      (hnv2 : valueFromPexpr pe2 = none) :
      Redex (loadOpRedex loc ann ty pe2 mo)
  | beta_spec {pa pb : List annot} {x : sym} {bty : core_base_type}
      {w : SpikeVal} {e2 : CoreExpr} :
      Redex (Expr [] (Esseq (specPat pa pb x bty) (ofVal w) e2))
  | memop (mop : memop) (pes : List (generic_pexpr Unit sym)) :
      Redex (memopRedex mop pes)
  | store_op (loc : CerbLocation.Loc) (ann : core_run_annotation)
      (ty : ctype) {pe2 pe3 : generic_pexpr Unit sym} (mo : memory_order)
      (hnv : valueFromPexprs [pe2, pe3] = none) :
      Redex (storeOpRedex loc ann ty pe2 pe3 mo)
  | beta_sym {pa : List annot} {x : sym} {bty : core_base_type}
      {w : SpikeVal} {e2 : CoreExpr} :
      Redex (Expr [] (Esseq (symPat pa x bty) (ofVal w) e2))
  /-- S1b DRIFT TEST: the two Ewseq wildcard betas (LETW-PURE /
      LETW-ANNOT root shapes). -/
  | wbeta_pure {pa : List annot} {bty : core_base_type} {v : value}
      {e2 : CoreExpr} :
      Redex (Expr [] (Ewseq (Pattern pa (CaseBase (none, bty)))
        (ofVal (.pure v)) e2))
  | wbeta_annot {pa : List annot} {bty : core_base_type}
      {ds : List dyn_annotation} {v : value} {e2 : CoreExpr} :
      Redex (Expr [] (Ewseq (Pattern pa (CaseBase (none, bty)))
        (ofVal (.annot ds v)) e2))
  /-- The procedure-call redex (calls arc C2): `Eproc` at a Core
      identifier — get_ctx's `| Eproc _ _ _ => [(CTX, expr1)]` root
      (Core_reduction.lean:375). -/
  | call (ra : core_run_annotation) (f : sym)
      (pes : List (generic_pexpr Unit sym)) : Redex (callRedex ra f pes)

/-- The extended decomposition: the same three layers as `Decomp`
    (get_ctx's arm order), over the extended root set. -/
inductive Decomp : CoreExpr → context → CoreExpr → Prop where
  | root {r : CoreExpr} : Redex r → Decomp r CTX r
  | sseq {pa : List annot} {bty : core_base_type} {e1 e2 : CoreExpr}
      {ctx : context} {r : CoreExpr} :
      Decomp e1 ctx r →
      Decomp (Expr [] (Esseq (Pattern pa (CaseBase (none, bty))) e1 e2))
             (Csseq [] (Pattern pa (CaseBase (none, bty))) ctx e2) r
  | sseq_spec {pa pb : List annot} {x : sym} {bty : core_base_type}
      {e1 e2 : CoreExpr} {ctx : context} {r : CoreExpr} :
      Decomp e1 ctx r →
      Decomp (Expr [] (Esseq (specPat pa pb x bty) e1 e2))
             (Csseq [] (specPat pa pb x bty) ctx e2) r
  | sseq_sym {pa : List annot} {x : sym} {bty : core_base_type}
      {e1 e2 : CoreExpr} {ctx : context} {r : CoreExpr} :
      Decomp e1 ctx r →
      Decomp (Expr [] (Esseq (symPat pa x bty) e1 e2))
             (Csseq [] (symPat pa x bty) ctx e2) r
  | annot {ds : List dyn_annotation} {b : CoreExpr} {ctx : context}
      {r : CoreExpr}
      (hroot : annotRooted b = false)
      (hirr : is_irreducible (Expr [] (Eannot ds b)) = false)
      (hmap : ∀ n : Nat,
        get_ctx_lemFuel (n+1) (Expr [] (Eannot ds b)) =
          List.map (fun p => (Cannot [] ds p.1, p.2)) (get_ctx_lemFuel n b)) :
      Decomp b ctx r → Decomp (Expr [] (Eannot ds b)) (Cannot [] ds ctx) r
  /-- S1b DRIFT TEST: descent through the weak-sequencing frame
      (get_ctx's Ewseq arm / Cwseq, Core_reduction.lean:375;
      wildcard pattern only — the mirrored Ewseq fragment). -/
  | wseq {pa : List annot} {bty : core_base_type} {e1 e2 : CoreExpr}
      {ctx : context} {r : CoreExpr} :
      Decomp e1 ctx r →
      Decomp (Expr [] (Ewseq (Pattern pa (CaseBase (none, bty))) e1 e2))
             (Cwseq [] (Pattern pa (CaseBase (none, bty))) ctx e2) r

theorem Redex.not_irreducible {r : CoreExpr} (h : Redex r) :
    is_irreducible r = false := by
  cases h with
  | store => rfl
  | load => rfl
  | create => rfl
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
  | store_op loc ann ty mo hnv => rfl
  | beta_sym => rfl
  | wbeta_pure => rfl
  | wbeta_annot => rfl
  | kill => rfl
  | kill_op loc ann kind hnv => rfl
  | alloc => rfl
  | alloc_op loc ann pref hnv => rfl
  | call ra f pes => rfl

theorem Decomp.not_irreducible {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (h : Decomp e ctx r) : is_irreducible e = false := by
  induction h with
  | root hr => exact hr.not_irreducible
  | sseq _ _ => rfl
  | sseq_spec _ _ => rfl
  | sseq_sym _ _ => rfl
  | annot _ hirr _ _ _ => exact hirr
  | wseq _ _ => rfl

theorem Decomp.unseq_ccall_false {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (h : Decomp e ctx r) : is_unseq_with_ccall ctx = false := by
  have aux : ∀ {e' : CoreExpr} {ctx' : context} {r' : CoreExpr},
      Decomp e' ctx' r' → ∀ b : Bool, is_unseq_with_ccall_aux b ctx' = b := by
    intro e' ctx' r' h'
    induction h' with
    | root _ => intro b; rfl
    | sseq _ ih => intro b; simpa [is_unseq_with_ccall_aux] using ih b
    | sseq_spec _ ih => intro b; simpa [is_unseq_with_ccall_aux] using ih b
    | sseq_sym _ ih => intro b; simpa [is_unseq_with_ccall_aux] using ih b
    | annot _ _ _ _ ih => intro b; simpa [is_unseq_with_ccall_aux] using ih b
    | wseq _ ih => intro b; simpa [is_unseq_with_ccall_aux] using ih b
  unfold is_unseq_with_ccall
  exact aux h false

theorem Decomp.apply_eq {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (h : Decomp e ctx r) : apply_ctx ctx r = e := by
  induction h with
  | root _ => rfl
  | sseq _ ih => simpa [apply_ctx] using ih
  | sseq_spec _ ih => simpa [apply_ctx] using ih
  | sseq_sym _ ih => simpa [apply_ctx] using ih
  | annot _ _ _ _ ih => simpa [apply_ctx] using ih
  | wseq _ ih => simpa [apply_ctx] using ih

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

/-- get_ctx roots at the call redex (Core_reduction.lean:375, `| Eproc
    _ _ _ => [(CTX, expr1)]` — no descent into the arguments). -/
theorem get_ctx_call {ra : core_run_annotation} {f : sym}
    {pes : List (generic_pexpr Unit sym)} (n : Nat) :
    get_ctx_lemFuel (n+1) (callRedex ra f pes) = [(CTX, callRedex ra f pes)] := rfl

/-- The engine's singleton decomposition, extended roots. -/
theorem Decomp.get_ctx_at {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (h : Decomp e ctx r) :
    ∀ n : Nat, esize e ≤ n → get_ctx_lemFuel n e = [(ctx, r)] := by
  induction h with
  | @root r0 hr =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
      ⟨n - 1, by have := esize_pos r0; omega⟩
    cases hr with
    | store => exact get_ctx_action m
    | load => exact get_ctx_action m
    | create => exact get_ctx_action m
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
    | store_op loc ann ty mo hnv => exact get_ctx_action m
    | beta_sym => exact get_ctx_sseq_val m
    | wbeta_pure => exact get_ctx_wseq_val m
    | wbeta_annot => exact get_ctx_wseq_val m
    | kill => exact get_ctx_action m
    | kill_op loc ann kind hnv => exact get_ctx_action m
    | alloc => exact get_ctx_action m
    | alloc_op loc ann pref hnv => exact get_ctx_action m
    | call ra f pes => exact get_ctx_call m
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
  | wseq hd ih =>
    intro n hn
    rw [esize_wseq] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [get_ctx_wseq hd.not_irreducible m, ih m (by omega)]
    rfl

theorem Decomp.get_ctx_default {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (h : Decomp e ctx r) (hsz : esize e ≤ lemDefaultFuel) :
    get_ctx e = [(ctx, r)] :=
  h.get_ctx_at lemDefaultFuel hsz

/-- `jumpRedex?` along an extended decomposition: `some` exactly at
    a run redex. -/
theorem Decomp.jumpRedex?_eq {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (h : Decomp e ctx r) : jumpRedex? e = jumpRedex? r := by
  induction h with
  | root _ => rfl
  | sseq _ ih => rw [jumpRedex?_sseq]; exact ih
  | sseq_spec _ ih => rw [jumpRedex?_sseq]; exact ih
  | sseq_sym _ ih => rw [jumpRedex?_sseq]; exact ih
  | annot hroot _ _ _ ih =>
    rw [jumpRedex?_annot_of_not_root _ _ hroot]; exact ih
  | wseq _ ih => rw [jumpRedex?_wseq]; exact ih

theorem Decomp.redex {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (h : Decomp e ctx r) : Redex r := by
  induction h with
  | root hr => exact hr
  | sseq _ ih => exact ih
  | sseq_spec _ ih => exact ih
  | sseq_sym _ ih => exact ih
  | annot _ _ _ _ ih => exact ih
  | wseq _ ih => exact ih

/-- A redex with a positive jump-redex answer IS the run redex. -/
theorem Redex.jumpRedex?_some_inv {r : CoreExpr} {l : sym}
    {pes : List (generic_pexpr Unit sym)} (h : Redex r)
    (hj : jumpRedex? r = some (l, pes)) :
    ∃ ra : core_run_annotation, r = runRedex ra l pes := by
  cases h with
  | store => cases hj
  | load => cases hj
  | create => cases hj
  | beta_pure => rw [jumpRedex?_sseq, jumpRedex?_ofVal] at hj; cases hj
  | beta_annot => rw [jumpRedex?_sseq, jumpRedex?_ofVal] at hj; cases hj
  | merge hirr => rw [jumpRedex?_annot_of_root _ _ rfl] at hj; cases hj
  | save sb ps body => cases hj
  | if_ g e2 e3 => cases hj
  | case_ pe pats => cases hj
  | pure_e hnv => cases hj
  | load_op loc ann ty mo hnv2 => cases hj
  | beta_spec => rw [jumpRedex?_sseq, jumpRedex?_ofVal] at hj; cases hj
  | memop mop pes => cases hj
  | store_op loc ann ty mo hnv => cases hj
  | beta_sym => rw [jumpRedex?_sseq, jumpRedex?_ofVal] at hj; cases hj
  | wbeta_pure => rw [jumpRedex?_wseq, jumpRedex?_ofVal] at hj; cases hj
  | wbeta_annot => rw [jumpRedex?_wseq, jumpRedex?_ofVal] at hj; cases hj
  | kill => cases hj
  | kill_op loc ann kind hnv => cases hj
  | alloc => cases hj
  | alloc_op loc ann pref hnv => cases hj
  | call ra f pes => cases hj
  | run ra l' pes' =>
    obtain ⟨rfl, rfl⟩ : l' = l ∧ pes' = pes := by
      have := Option.some.inj hj
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    exact ⟨ra, rfl⟩


/-- A redex with a positive call-redex answer IS the call redex, at the
    root context (the `jumpRedex?_some_inv` twin). -/
theorem Redex.callRedex?_some_inv {r : CoreExpr} {ctx : context} {f : sym}
    {pes : List (generic_pexpr Unit sym)} (h : Redex r)
    (hc : callRedex? r = some (ctx, f, pes)) :
    ctx = CTX ∧ ∃ ra : core_run_annotation, r = callRedex ra f pes := by
  cases h with
  | store => cases hc
  | load => cases hc
  | create => cases hc
  | beta_pure => rw [callRedex?_sseq, callRedex?_ofVal] at hc; cases hc
  | beta_annot => rw [callRedex?_sseq, callRedex?_ofVal] at hc; cases hc
  | merge hirr => rw [callRedex?_annot_of_root _ _ rfl] at hc; cases hc
  | save sb ps body => cases hc
  | if_ g e2 e3 => cases hc
  | case_ pe pats => cases hc
  | run ra l pes' => cases hc
  | pure_e hnv => cases hc
  | load_op loc ann ty mo hnv2 => cases hc
  | beta_spec => rw [callRedex?_sseq, callRedex?_ofVal] at hc; cases hc
  | memop mop pes' => cases hc
  | store_op loc ann ty mo hnv => cases hc
  | beta_sym => rw [callRedex?_sseq, callRedex?_ofVal] at hc; cases hc
  | wbeta_pure => rw [callRedex?_wseq, callRedex?_ofVal] at hc; cases hc
  | wbeta_annot => rw [callRedex?_wseq, callRedex?_ofVal] at hc; cases hc
  | kill => cases hc
  | kill_op loc ann kind hnv => cases hc
  | alloc => cases hc
  | alloc_op loc ann pref hnv => cases hc
  | call ra f' pes' =>
    rw [callRedex?_callRedex] at hc
    obtain ⟨rfl, rfl, rfl⟩ : CTX = ctx ∧ f' = f ∧ pes' = pes := by
      have := Option.some.inj hc
      exact ⟨congrArg Prod.fst this, congrArg (fun q => q.2.1) this,
        congrArg (fun q => q.2.2) this⟩
    exact ⟨rfl, ra, rfl⟩

/-- `callRedex?` along an extended decomposition: `some` exactly at a call
    redex, and then the CAPTURED context is the decomposition's context —
    the syntactic search computes what get_ctx pairs the redex with. -/
theorem Decomp.callRedex?_inv {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (hd : Decomp e ctx r) {ctx' : context} {f : sym} {pes : List (generic_pexpr Unit sym)}
    (hc : callRedex? e = some (ctx', f, pes)) :
    ctx' = ctx ∧ ∃ ra : core_run_annotation, r = callRedex ra f pes := by
  induction hd generalizing ctx' with
  | root hr => exact hr.callRedex?_some_inv hc
  | sseq _ ih =>
    rw [callRedex?_sseq, Option.map_eq_some_iff] at hc
    obtain ⟨⟨c1, f1, pes1⟩, hc1, hq⟩ := hc
    obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
      exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq,
        congrArg (fun q => q.2.2) hq⟩
    obtain ⟨rfl, ra, rfl⟩ := ih hc1
    exact ⟨rfl, ra, rfl⟩
  | sseq_spec _ ih =>
    rw [callRedex?_sseq, Option.map_eq_some_iff] at hc
    obtain ⟨⟨c1, f1, pes1⟩, hc1, hq⟩ := hc
    obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
      exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq,
        congrArg (fun q => q.2.2) hq⟩
    obtain ⟨rfl, ra, rfl⟩ := ih hc1
    exact ⟨rfl, ra, rfl⟩
  | sseq_sym _ ih =>
    rw [callRedex?_sseq, Option.map_eq_some_iff] at hc
    obtain ⟨⟨c1, f1, pes1⟩, hc1, hq⟩ := hc
    obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
      exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq,
        congrArg (fun q => q.2.2) hq⟩
    obtain ⟨rfl, ra, rfl⟩ := ih hc1
    exact ⟨rfl, ra, rfl⟩
  | annot hroot _ _ _ ih =>
    rw [callRedex?_annot_of_not_root _ _ hroot, Option.map_eq_some_iff] at hc
    obtain ⟨⟨c1, f1, pes1⟩, hc1, hq⟩ := hc
    obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
      exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq,
        congrArg (fun q => q.2.2) hq⟩
    obtain ⟨rfl, ra, rfl⟩ := ih hc1
    exact ⟨rfl, ra, rfl⟩
  | wseq _ ih =>
    rw [callRedex?_wseq, Option.map_eq_some_iff] at hc
    obtain ⟨⟨c1, f1, pes1⟩, hc1, hq⟩ := hc
    obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
      exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq,
        congrArg (fun q => q.2.2) hq⟩
    obtain ⟨rfl, ra, rfl⟩ := ih hc1
    exact ⟨rfl, ra, rfl⟩

/-- At a decomposed CALL redex the search answers the decomposition's
    context (the certification of `callRedex?` against get_ctx: the
    captured frame IS get_ctx's). -/
theorem Decomp.callRedex?_some' {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (hd : Decomp e ctx r) {ra : core_run_annotation} {f : sym}
    {pes : List (generic_pexpr Unit sym)} (hr : r = callRedex ra f pes) :
    callRedex? e = some (ctx, f, pes) := by
  induction hd with
  | root _ => subst hr; rfl
  | sseq _ ih => rw [callRedex?_sseq, ih hr]; rfl
  | sseq_spec _ ih => rw [callRedex?_sseq, ih hr]; rfl
  | sseq_sym _ ih => rw [callRedex?_sseq, ih hr]; rfl
  | annot hroot _ _ _ ih => rw [callRedex?_annot_of_not_root _ _ hroot, ih hr]; rfl
  | wseq _ ih => rw [callRedex?_wseq, ih hr]; rfl

theorem Decomp.callRedex?_some {e : CoreExpr} {ctx : context}
    {ra : core_run_annotation} {f : sym} {pes : List (generic_pexpr Unit sym)}
    (hd : Decomp e ctx (callRedex ra f pes)) :
    callRedex? e = some (ctx, f, pes) :=
  hd.callRedex?_some' rfl

/-- At a decomposed NON-call redex the search answers `none`. -/
theorem Decomp.callRedex?_none {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (hd : Decomp e ctx r)
    (hnr : ∀ (ra : core_run_annotation) (f : sym) (pes : List (generic_pexpr Unit sym)),
      r ≠ callRedex ra f pes) :
    callRedex? e = none := by
  cases hc : callRedex? e with
  | none => rfl
  | some q =>
    obtain ⟨ctx', f, pes⟩ := q
    obtain ⟨-, ra, hr⟩ := hd.callRedex?_inv hc
    exact absurd hr (hnr ra f pes)

/-- A decomposed term is not a value (values are irreducible;
    `Decomp.not_irreducible`). -/
theorem Decomp.toVal_none {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (hd : Decomp e ctx r) : toVal e = none := by
  cases hv : toVal e with
  | none => rfl
  | some w =>
    have he := ofVal_of_toVal hv
    subst he
    have h1 := hd.not_irreducible
    rw [is_irreducible_ofVal] at h1
    cases h1

/-- THE FACTOR THEOREM WITH THE JUMP DISJUNCT (readiness R1: "the
    factor theorem gains one disjunct"): a step of a decomposed term
    is EITHER a step of its redex REBUILT in context (the phase-1
    shape), OR the redex is a registered jump and the step is the
    redex's OWN step — the context is DISCARDED, and the successor
    does not mention it. -/
theorem Decomp.step_factor {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {r : CoreExpr} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config}
    (h : Decomp e ctx r) (hs : Step M (e, ρ, ctl, σ) out) :
    (∃ r' ρ' σ', (∀ (ra : core_run_annotation) (l : sym)
        (pes : List (generic_pexpr Unit sym)), r ≠ runRedex ra l pes) ∧
      (∀ (ra : core_run_annotation) (f : sym)
        (pes : List (generic_pexpr Unit sym)), r ≠ callRedex ra f pes) ∧
      Step M (r, ρ, ctl, σ) (r', ρ', ctl, σ') ∧
      out = (apply_ctx ctx r', ρ', ctl, σ')) ∨
    (∃ (ra : core_run_annotation) (l : sym)
      (pes : List (generic_pexpr Unit sym)),
      r = runRedex ra l pes ∧ Step M (r, ρ, ctl, σ) out) ∨
    (∃ (ra : core_run_annotation) (f : sym) (pes : List (generic_pexpr Unit sym))
      (params : List (sym × core_base_type)) (body : CoreExpr) (vs : List value),
      r = callRedex ra f pes ∧
      evalPexprs M.tagDefs M.extern ρ pes = some vs ∧
      lookupProc M.file M.extern f = some (params, body) ∧ params.length = vs.length ∧
      out = (body, procEnv params vs :: ρ,
        ⟨(ctl.proc, ctx) :: ctl.κ, some f, push_exec_loc f M.currentLoc ctl.execLoc⟩, σ)) := by
  induction h generalizing out with
  | @root r hr =>
    by_cases hrun : ∃ (ra : core_run_annotation) (l : sym)
        (pes : List (generic_pexpr Unit sym)), r = runRedex ra l pes
    · obtain ⟨ra, l, pes, rfl⟩ := hrun
      exact .inr (.inl ⟨ra, l, pes, rfl, hs⟩)
    by_cases hcall : ∃ (ra : core_run_annotation) (f : sym)
        (pes : List (generic_pexpr Unit sym)), r = callRedex ra f pes
    · obtain ⟨ra, f, pes, rfl⟩ := hcall
      obtain ⟨params, body, vs, hvs, hf, hlen, rfl⟩ := hs.call_inv (callRedex?_callRedex ra f pes)
      exact .inr (.inr ⟨ra, f, pes, params, body, vs, rfl, hvs, hf, hlen, rfl⟩)
    · obtain ⟨oe, oρ, octl, oσ⟩ := out
      have hnc : callRedex? r = none :=
        (Decomp.root hr).callRedex?_none (fun ra f pes hr' => hcall ⟨ra, f, pes, hr'⟩)
      obtain rfl : ctl = octl := (hs.ctl_eq hnc (Decomp.root hr).toVal_none).symm
      exact .inl ⟨oe, oρ, oσ, fun ra l pes hr => hrun ⟨ra, l, pes, hr⟩,
        fun ra f pes hr => hcall ⟨ra, f, pes, hr⟩, hs, rfl⟩
  | @sseq pa bty e1 e2 ctx' r' hd ih =>
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hnv, hstep, hout⟩ |
        ⟨_, _, v, _, _, _, he1, _, _⟩ | ⟨_, _, ds, v, _, _, _, he1, _, _⟩ |
        ⟨l, pes, params, cont, vs, ev0, evs, hj, hρ, hl, hvs, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, hpat, _, _, _⟩ |
        hcall
    · rcases ih hstep with ⟨r2, ρr, σr, hnr2, hnc2, hr2, heq⟩ | ⟨ra, l, pes, rfl, hr2⟩ |
          ⟨ra, f, pes, params, body, vs, rfl, -, -, -, hcout⟩
      · obtain ⟨he, hρ2, hσ2⟩ : e1' = apply_ctx _ r2 ∧ ρ'' = ρr ∧
            σ'' = σr := by
          simpa [Prod.mk.injEq] using heq
        subst he hρ2 hσ2
        exact .inl ⟨r2, _, _, hnr2, hnc2, hr2, by rw [hout]; rfl⟩
      · rw [hd.jumpRedex?_eq] at hnj
        rw [show jumpRedex? (runRedex ra l pes) = some (l, pes) from rfl]
          at hnj
        cases hnj
      · exact absurd (congrArg (fun c : Config => c.2.2.1.κ) hcout) (by simp)
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
    · -- the node's step IS the jump: the decomposed redex must be
      -- the run redex, and its own step has the SAME successor
      have hje : jumpRedex? r' = some (l, pes) := by
        rw [← hd.jumpRedex?_eq]; exact hj
      obtain ⟨ra, rfl⟩ := hd.redex.jumpRedex?_some_inv hje
      subst hρ
      rw [hout]
      exact .inr (.inl ⟨ra, l, pes, rfl, Step.run (by rfl) hl hvs⟩)
    · exact (specPat_ne_base hpat).elim
    · exact (specPat_ne_base hpat).elim
    · exact (symPat_ne_base hpat).elim
    · obtain ⟨ctx1, f, pes, params, body, vs, hc1, hvs, hf, hlen, rfl⟩ := hcall
      obtain ⟨rfl, ra, rfl⟩ := hd.callRedex?_inv hc1
      exact .inr (.inr ⟨ra, f, pes, params, body, vs, rfl, hvs, hf, hlen, rfl⟩)
  | @sseq_spec pa pb x bty e1 e2 ctx' r' hd ih =>
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hnv, hstep, hout⟩ |
        ⟨_, _, v, _, _, _, he1, _, _⟩ | ⟨_, _, ds, v, _, _, _, he1, _, _⟩ |
        ⟨l, pes, params, cont, vs, ev0, evs, hj, hρ, hl, hvs, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, he1, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, he1, _, _⟩ |
        ⟨_, _, _, _, _, _, _, he1, _, _⟩ |
        hcall
    · rcases ih hstep with ⟨r2, ρr, σr, hnr2, hnc2, hr2, heq⟩ | ⟨ra, l, pes, rfl, hr2⟩ |
          ⟨ra, f, pes, params, body, vs, rfl, -, -, -, hcout⟩
      · obtain ⟨he, hρ2, hσ2⟩ : e1' = apply_ctx _ r2 ∧ ρ'' = ρr ∧
            σ'' = σr := by
          simpa [Prod.mk.injEq] using heq
        subst he hρ2 hσ2
        exact .inl ⟨r2, _, _, hnr2, hnc2, hr2, by rw [hout]; rfl⟩
      · rw [hd.jumpRedex?_eq] at hnj
        rw [show jumpRedex? (runRedex ra l pes) = some (l, pes) from rfl]
          at hnj
        cases hnj
      · exact absurd (congrArg (fun c : Config => c.2.2.1.κ) hcout) (by simp)
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
    · have hje : jumpRedex? r' = some (l, pes) := by
        rw [← hd.jumpRedex?_eq]; exact hj
      obtain ⟨ra, rfl⟩ := hd.redex.jumpRedex?_some_inv hje
      subst hρ
      rw [hout]
      exact .inr (.inl ⟨ra, l, pes, rfl, Step.run (by rfl) hl hvs⟩)
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
    · obtain ⟨ctx1, f, pes, params, body, vs, hc1, hvs, hf, hlen, rfl⟩ := hcall
      obtain ⟨rfl, ra, rfl⟩ := hd.callRedex?_inv hc1
      exact .inr (.inr ⟨ra, f, pes, params, body, vs, rfl, hvs, hf, hlen, rfl⟩)
  | @sseq_sym pa x bty e1 e2 ctx' r' hd ih =>
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hnv, hstep, hout⟩ |
        ⟨_, _, v, _, _, _, he1, _, _⟩ | ⟨_, _, ds, v, _, _, _, he1, _, _⟩ |
        ⟨l, pes, params, cont, vs, ev0, evs, hj, hρ, hl, hvs, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, he1, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, he1, _, _⟩ |
        ⟨_, _, _, _, _, _, _, he1, _, _⟩ |
        hcall
    · rcases ih hstep with ⟨r2, ρr, σr, hnr2, hnc2, hr2, heq⟩ | ⟨ra, l, pes, rfl, hr2⟩ |
          ⟨ra, f, pes, params, body, vs, rfl, -, -, -, hcout⟩
      · obtain ⟨he, hρ2, hσ2⟩ : e1' = apply_ctx _ r2 ∧ ρ'' = ρr ∧
            σ'' = σr := by
          simpa [Prod.mk.injEq] using heq
        subst he hρ2 hσ2
        exact .inl ⟨r2, _, _, hnr2, hnc2, hr2, by rw [hout]; rfl⟩
      · rw [hd.jumpRedex?_eq] at hnj
        rw [show jumpRedex? (runRedex ra l pes) = some (l, pes) from rfl]
          at hnj
        cases hnj
      · exact absurd (congrArg (fun c : Config => c.2.2.1.κ) hcout) (by simp)
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
    · have hje : jumpRedex? r' = some (l, pes) := by
        rw [← hd.jumpRedex?_eq]; exact hj
      obtain ⟨ra, rfl⟩ := hd.redex.jumpRedex?_some_inv hje
      subst hρ
      rw [hout]
      exact .inr (.inl ⟨ra, l, pes, rfl, Step.run (by rfl) hl hvs⟩)
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
    · obtain ⟨ctx1, f, pes, params, body, vs, hc1, hvs, hf, hlen, rfl⟩ := hcall
      obtain ⟨rfl, ra, rfl⟩ := hd.callRedex?_inv hc1
      exact .inr (.inr ⟨ra, f, pes, params, body, vs, rfl, hvs, hf, hlen, rfl⟩)
  | @wseq pa bty e1 e2 ctx' r' hd ih =>
    rcases hs.wseq_inv with ⟨e1', ρ'', σ'', hnj, hnv, hstep, hout⟩ |
        ⟨_, _, v, _, _, _, he1, _, _⟩ | ⟨_, _, ds, v, _, _, _, he1, _, _⟩ |
        ⟨l, pes, params, cont, vs, ev0, evs, hj, hρ, hl, hvs, hout⟩ |
        hcall
    · rcases ih hstep with ⟨r2, ρr, σr, hnr2, hnc2, hr2, heq⟩ | ⟨ra, l, pes, rfl, hr2⟩ |
          ⟨ra, f, pes, params, body, vs, rfl, -, -, -, hcout⟩
      · obtain ⟨he, hρ2, hσ2⟩ : e1' = apply_ctx _ r2 ∧ ρ'' = ρr ∧
            σ'' = σr := by
          simpa [Prod.mk.injEq] using heq
        subst he hρ2 hσ2
        exact .inl ⟨r2, _, _, hnr2, hnc2, hr2, by rw [hout]; rfl⟩
      · rw [hd.jumpRedex?_eq] at hnj
        rw [show jumpRedex? (runRedex ra l pes) = some (l, pes) from rfl]
          at hnj
        cases hnj
      · exact absurd (congrArg (fun c : Config => c.2.2.1.κ) hcout) (by simp)
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by simp [is_irreducible_ofVal])
    · have hje : jumpRedex? r' = some (l, pes) := by
        rw [← hd.jumpRedex?_eq]; exact hj
      obtain ⟨ra, rfl⟩ := hd.redex.jumpRedex?_some_inv hje
      subst hρ
      rw [hout]
      exact .inr (.inl ⟨ra, l, pes, rfl, Step.run (by rfl) hl hvs⟩)
    · obtain ⟨ctx1, f, pes, params, body, vs, hc1, hvs, hf, hlen, rfl⟩ := hcall
      obtain ⟨rfl, ra, rfl⟩ := hd.callRedex?_inv hc1
      exact .inr (.inr ⟨ra, f, pes, params, body, vs, rfl, hvs, hf, hlen, rfl⟩)
  | @annot ds b ctx' r' hroot hirr hmap hd ih =>
    rcases hs.annot_inv with ⟨_, hnj, b', ρ'', σ'', hstep, hout⟩ |
        ⟨a2, ds2, c, hb, _⟩ |
        ⟨l, pes, params, cont, vs, ev0, evs, hg, hj, hρ, hl, hvs, hout⟩ |
        ⟨-, hcall⟩ | ⟨v, pc, κ, -, hb, -, -⟩
    · rcases ih hstep with ⟨r2, ρr, σr, hnr2, hnc2, hr2, heq⟩ | ⟨ra, l, pes, rfl, hr2⟩ |
          ⟨ra, f, pes, params, body, vs, rfl, -, -, -, hcout⟩
      · obtain ⟨he, hρ2, hσ2⟩ : b' = apply_ctx _ r2 ∧ ρ'' = ρr ∧
            σ'' = σr := by
          simpa [Prod.mk.injEq] using heq
        subst he hρ2 hσ2
        exact .inl ⟨r2, _, _, hnr2, hnc2, hr2, by rw [hout]; rfl⟩
      · rw [hd.jumpRedex?_eq] at hnj
        rw [show jumpRedex? (runRedex ra l pes) = some (l, pes) from rfl]
          at hnj
        cases hnj
      · exact absurd (congrArg (fun c : Config => c.2.2.1.κ) hcout) (by simp)
    · rw [hb] at hroot
      simp [annotRooted] at hroot
    · have hje : jumpRedex? r' = some (l, pes) := by
        rw [← hd.jumpRedex?_eq]; exact hj
      obtain ⟨ra, rfl⟩ := hd.redex.jumpRedex?_some_inv hje
      subst hρ
      rw [hout]
      exact .inr (.inl ⟨ra, l, pes, rfl, Step.run (by rfl) hl hvs⟩)
    · obtain ⟨ctx1, f, pes, params, body, vs, hc1, hvs, hf, hlen, rfl⟩ := hcall
      obtain ⟨rfl, ra, rfl⟩ := hd.callRedex?_inv hc1
      exact .inr (.inr ⟨ra, f, pes, params, body, vs, rfl, hvs, hf, hlen, rfl⟩)
    · rw [hb] at hd
      have h1 := hd.not_irreducible
      rw [show is_irreducible (Expr ([] : List _root_.annot)
        (Epure (Pexpr [] () (PEval v)))) = true from rfl] at h1
      cases h1

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

/-- RETURN, in the engine's own terms (calls arc C2): at a BARE value
    arena over a NON-EMPTY call stack with a cons-shaped env, step_ctx's
    value arm takes its `Stack_cons2 parent_proc_opt caller_ctx sk'` branch
    (Core_reduction.lean:484, col 2276): ONE `Step_tau2 "end of procedure"
    tsk` whose successor restores the caller's procedure, POPS the env
    frame, pops the stack and plugs the value into the caller's saved
    context. `tsk` (`TSK_Return psym (memValueFromValue …)` when
    `file1.funinfo` has the current procedure, `TSK_Misc` otherwise)
    reaches only the driver's trace — existential here; `exec_loc` is
    untouched; the parent slot is not read (the branch is selected by the
    stack alone). -/
theorem step_ctx_ret (v : value)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = Expr [] (Epure (Pexpr [] () (PEval v))))
    {p : Option sym} {ctx : context} {sk' : _root_.stack core_run_annotation}
    (hstack : th.stack0 = Stack_cons2 p ctx sk')
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)} (henv : th.env = ev0 :: evs) :
    ∃ tsk : core_tau_step_kind,
      step_ctx tds σ file ext tid (parent, th) =
        [Step_tau2 "end of procedure" tsk
          { th with
            current_proc_opt := p
            env := evs
            stack0 := sk'
            arena := apply_ctx ctx (Expr [] (Epure (Pexpr [] () (PEval v)))) }] := by
  have hget : get_ctx th.arena =
      [(CTX, Expr [] (Epure (Pexpr [] () (PEval v))))] := by
    rw [harena]; exact get_ctx_ofVal (.pure v) 999999
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  rw [hstack, henv]
  exact ⟨_, rfl⟩

/-- The location the engine attaches to an action request: the redex's
    own, unless it is a library location, in which case the thread's
    `current_loc` (`step_ctx`'s process_action, Core_reduction.lean:484:
    `let loc' := if isLibraryLocation loc1 then th_st.current_loc else
    loc1`). It reaches only the kill payload and the driver's trace —
    never the active result or the memory (`storeM_loc_irrel`,
    `loadM_loc_irrel`, Step.lean). -/
def requestLoc (th : thread_state) (loc : CerbLocation.Loc) : CerbLocation.Loc :=
  if CerbLocation.isLibraryLocation loc then th.current_loc else loc

/-- Store, active shape, context undisturbed: one StoreRequest2 at the
    engine's `requestLoc th loc`, the continuation rebuilds
    `{DA_pos [] fp} unit` in context with the whole thread context
    verbatim. tagDefs is READ (the operand encoding premise `hmv` is
    stated at the quantified tagDefs); `current_loc` is read into the
    request location only. -/
theorem step_ctx_store {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
    {ty : ctype} {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
    {mv : CerbMem.MemValue}
    (hd : Decomp e ctx (storeRedex loc ann lk ty pv cv mo))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition))
    (hmv : memValueFromValue tds (Ctype [] (unatomic_ ty)) cv = some mv)
    (σ : Mem) (file : generic_file Unit core_run_annotation)
    (ext : Fmap sym sym) (tid : Nat) (parent : Option Nat)
    (th : thread_state) (harena : th.arena = e) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_action_request2 "StoreRequest" (requestLoc th loc) tid (is_unseq_with_ccall ctx)
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
     first | rfl | (unfold requestLoc; rfl))

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
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat)
    (th : thread_state) (harena : th.arena = e) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_action_request2 "LoadRequest" (requestLoc th loc) tid (is_unseq_with_ccall ctx)
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
     first | rfl | (unfold requestLoc; rfl))

/-- Create, context undisturbed (Extension D): one CreateRequest2 with
    the canonical operands (which always classify — no ILLTYPED arm
    exists for this shape); the continuation rebuilds the BARE pointer
    value in context (mk_value_e, no Eannot residue — step_action
    Create arm, Core_reduction.lean:424), thread context verbatim.
    tagDefs is unread; `current_loc` is read into the request location
    (`requestLoc th loc`) only. The request carries `get_with_address []` (the fragment's `[]` node annots) as
    the requested address — an opaque `partial def` value that
    `allocateObject` discards (CerbMem.lean:1473). -/
theorem step_ctx_create {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {align : CerbMem.IntegerValue} {ty : ctype} {pref : prefix0}
    (hd : Decomp e ctx (createRedex loc ann align ty pref))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat)
    (th : thread_state) (harena : th.arena = e) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_action_request2 "CreateRequest" (requestLoc th loc) tid (is_unseq_with_ccall ctx)
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
     first | rfl | (unfold requestLoc; rfl))

/-- Kill, context undisturbed (kill/free arc K2): one `KillRequest2` at
    the canonical evaluated pointer operand — step_action's Kill arm
    (Core_reduction.lean:424): `KillRequest2 (is_dynamic kind1) ptrval
    (fun (aid1 : Nat) => mk_value_e Vunit)`, rewrapped by
    process_action into the thread continuation; the continuation
    rebuilds the BARE unit value in context (`mk_value_e Vunit`, no
    Eannot residue — like create, unlike store/load), thread context
    verbatim. tagDefs is unread; `current_loc` is read into the request
    location (`requestLoc th loc`) only; the `Static0 ty` payload is
    discarded — only `is_dynamic kind` reaches the request. -/
theorem step_ctx_kill {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {kind : kill_kind} {pv : CerbMem.PointerValue}
    (hd : Decomp e ctx (killRedex loc ann kind pv))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat)
    (th : thread_state) (harena : th.arena = e) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_action_request2 "KillRequest" (requestLoc th loc) tid (is_unseq_with_ccall ctx)
        (stExceptUndef_return (KillRequest2 (is_dynamic kind) pv
          (fun (_ : Nat) =>
            { th with arena := apply_ctx ctx (Expr [] (Epure (Pexpr [] ()
                (PEval Vunit)))) })))] := by
  have hget : get_ctx th.arena = [(ctx, killRedex loc ann kind pv)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold killRedex
  cases ctx <;>
    (dsimp only [step_action, act_valueFromPexpr, valueFromPexpr]
     first | rfl | (unfold requestLoc; rfl))

/-- Alloc, context undisturbed (kill/free arc K3): one `AllocRequest2` at
    the canonical evaluated integer operands — step_action's Alloc0 arm
    (Core_reduction.lean:424): `AllocRequest2 pref ival1 ival2 (fun aid1
    ptrval => mk_value_e (Vobject (OVpointer ptrval)))`, rewrapped by
    process_action into the thread continuation; the continuation
    rebuilds the BARE pointer value in context (`mk_value_e`, no Eannot
    residue — create's shape), thread context verbatim. tagDefs is unread;
    `current_loc` is read into the request location (`requestLoc th loc`)
    only. -/
theorem step_ctx_alloc {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {align size : CerbMem.IntegerValue} {pref : prefix0}
    (hd : Decomp e ctx (allocRedex loc ann align size pref))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat)
    (th : thread_state) (harena : th.arena = e) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_action_request2 "AllocRequest" (requestLoc th loc) tid (is_unseq_with_ccall ctx)
        (stExceptUndef_return (AllocRequest2 pref align size
          (fun (_ : Nat) (pv : CerbMem.PointerValue) =>
            { th with arena := apply_ctx ctx (Expr [] (Epure (Pexpr [] ()
                (PEval (Vobject (OVpointer pv)))))) })))] := by
  have hget : get_ctx th.arena = [(ctx, allocRedex loc ann align size pref)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold allocRedex
  cases ctx <;>
    (dsimp only [step_action, act_valueFromPexpr, valueFromPexpr]
     first | rfl | (unfold requestLoc; rfl))

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

/-- LETW-PURE, context undisturbed (S1b DRIFT TEST — the
    `step_ctx_beta_pure` clone at the Ewseq wildcard redex; one_step0
    Ewseq bare-value arm, Core_reduction.lean:353 "reduction:
    LETW-PURE", tau label "Ewseq"). Same env discipline. -/
theorem step_ctx_wseq_pure {e : CoreExpr} {ctx : context}
    {pa : List _root_.annot} {bty : core_base_type} {v : value} {e2 : CoreExpr}
    (hd : Decomp e ctx
      (Expr [] (Ewseq (Pattern pa (CaseBase (none, bty))) (ofVal (.pure v)) e2)))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    (henv : th.env = ev0 :: evs) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_tau2 "Ewseq" TSK_Misc { th with arena := apply_ctx ctx e2 }] := by
  have hget : get_ctx th.arena =
      [(ctx, Expr [] (Ewseq (Pattern pa (CaseBase (none, bty)))
        (ofVal (.pure v)) e2))] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  cases ctx <;>
    (simp only [one_step0, ofVal, is_irreducible_wseq, Bool.false_eq_true,
       if_false, valueFromPexpr]
     simp only [get_loc]
     dsimp only [update_env]
     rw [henv]
     dsimp only
     try rw [show ∀ cval, update_env_aux (a := sym)
         (Pattern pa (CaseBase (none, bty))) cval ev0 = ev0 from fun _ => rfl]
     try rw [← henv]
     try rfl)

/-- LETW-ANNOT, context undisturbed (S1b DRIFT TEST; tau label
    "Ewseq Eannot"). -/
theorem step_ctx_wseq_annot {e : CoreExpr} {ctx : context}
    {pa : List _root_.annot} {bty : core_base_type}
    {ds : List dyn_annotation} {v : value} {e2 : CoreExpr}
    (hd : Decomp e ctx
      (Expr [] (Ewseq (Pattern pa (CaseBase (none, bty)))
        (ofVal (.annot ds v)) e2)))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    (henv : th.env = ev0 :: evs) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_tau2 "Ewseq Eannot" TSK_Misc
        { th with arena := apply_ctx ctx (Expr [] (Eannot ds e2)) }] := by
  have hget : get_ctx th.arena =
      [(ctx, Expr [] (Ewseq (Pattern pa (CaseBase (none, bty)))
        (ofVal (.annot ds v)) e2))] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  cases ctx <;>
    (simp only [one_step0, ofVal, is_irreducible_wseq, Bool.false_eq_true,
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

/-! ## Discharge computation (the applyMemM bridge)

`dischargeStep` and Step's action rules consume the same one-level
memM application (`applyMemM`, Step.lean; sound for the fragment ops
because storeM/loadM are single-layer state transformers, recon
§2.3). These lemmas compute the discharge from the applyMemM verdict. -/

theorem dischargeStep_store_active {tds : CerbTags.TagDefsMap} {aid : Nat} {rs : core_run_state}
    {σ σ' : Mem} {str : String}
    {loc loc₀ : CerbLocation.Loc} {tid : thread_id} {uw : Bool} {mo : memory_order}
    {ty : ctype} {lk : Bool} {pv : CerbMem.PointerValue} {mv : CerbMem.MemValue}
    {k : Nat → CerbMem.Footprint → thread_state} {fp : CerbMem.Footprint}
    (h : applyMemM (CerbMem.storeM tds loc₀ ty lk pv mv) σ = some (fp, σ')) :
    dischargeStep tds aid rs σ (Step_action_request2 str loc tid uw
      (stExceptUndef_return (StoreRequest2 mo ty lk pv mv k))) =
      .next (k aid fp) σ' := by
  replace h := (storeM_loc_irrel loc₀ loc).trans h
  rcases hm : CerbMem.storeM tds loc ty lk pv mv with ⟨f⟩
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

theorem dischargeStep_store_refusal {tds : CerbTags.TagDefsMap} {aid : Nat} {rs : core_run_state}
    {σ : Mem} {str : String}
    {loc loc₀ : CerbLocation.Loc} {tid : thread_id} {uw : Bool} {mo : memory_order}
    {ty : ctype} {lk : Bool} {pv : CerbMem.PointerValue} {mv : CerbMem.MemValue}
    {k : Nat → CerbMem.Footprint → thread_state}
    (h : applyMemM (CerbMem.storeM tds loc₀ ty lk pv mv) σ = none) :
    (dischargeStep tds aid rs σ (Step_action_request2 str loc tid uw
      (stExceptUndef_return (StoreRequest2 mo ty lk pv mv k)))).isRefusal := by
  replace h := (storeM_loc_irrel loc₀ loc).trans h
  rcases hm : CerbMem.storeM tds loc ty lk pv mv with ⟨f⟩
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

theorem dischargeStep_load_active {tds : CerbTags.TagDefsMap} {aid : Nat} {rs : core_run_state}
    {σ σ' : Mem} {str : String}
    {loc loc₀ : CerbLocation.Loc} {tid : thread_id} {uw : Bool} {mo : memory_order}
    {ty : ctype} {pv : CerbMem.PointerValue}
    {k : Nat → CerbMem.Footprint → CerbMem.MemValue → thread_state}
    {fp : CerbMem.Footprint} {mval : CerbMem.MemValue}
    (h : applyMemM (CerbMem.loadM tds loc₀ ty pv) σ = some ((fp, mval), σ')) :
    dischargeStep tds aid rs σ (Step_action_request2 str loc tid uw
      (stExceptUndef_return (LoadRequest2 mo ty pv k))) =
      .next (k aid fp mval) σ' := by
  replace h := (loadM_loc_irrel loc₀ loc).trans h
  rcases hm : CerbMem.loadM tds loc ty pv with ⟨f⟩
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

theorem dischargeStep_load_refusal {tds : CerbTags.TagDefsMap} {aid : Nat} {rs : core_run_state}
    {σ : Mem} {str : String}
    {loc loc₀ : CerbLocation.Loc} {tid : thread_id} {uw : Bool} {mo : memory_order}
    {ty : ctype} {pv : CerbMem.PointerValue}
    {k : Nat → CerbMem.Footprint → CerbMem.MemValue → thread_state}
    (h : applyMemM (CerbMem.loadM tds loc₀ ty pv) σ = none) :
    (dischargeStep tds aid rs σ (Step_action_request2 str loc tid uw
      (stExceptUndef_return (LoadRequest2 mo ty pv k)))).isRefusal := by
  replace h := (loadM_loc_irrel loc₀ loc).trans h
  rcases hm : CerbMem.loadM tds loc ty pv with ⟨f⟩
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
theorem allocateObject_arg_irrel (tds : CerbTags.TagDefsMap) (tid tid' : Nat) (pref : prefix0)
    (align : CerbMem.IntegerValue) (ty : ctype) (r r' : Option Int)
    (init : Option CerbMem.MemValue) :
    CerbMem.allocateObject tds tid pref align ty r init =
      CerbMem.allocateObject tds tid' pref align ty r' init := rfl

theorem dischargeStep_create_active {tds : CerbTags.TagDefsMap} {aid : Nat} {rs : core_run_state}
    {σ σ' : Mem} {str : String}
    {loc : CerbLocation.Loc} {tid : thread_id} {uw : Bool}
    {pref : prefix0} {align : CerbMem.IntegerValue} {ty : ctype}
    {reqAddr : Option Int} {k : Nat → CerbMem.PointerValue → thread_state}
    {pv : CerbMem.PointerValue}
    (h : applyMemM (CerbMem.allocateObject tds 0 pref align ty reqAddr none) σ =
      some (pv, σ')) :
    dischargeStep tds aid rs σ (Step_action_request2 str loc tid uw
      (stExceptUndef_return (CreateRequest2 pref align ty reqAddr none k))) =
      .next (k aid pv) σ' := by
  rcases hm : CerbMem.allocateObject tds 0 pref align ty reqAddr none with ⟨f⟩
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

theorem dischargeStep_create_refusal {tds : CerbTags.TagDefsMap} {aid : Nat} {rs : core_run_state}
    {σ : Mem} {str : String}
    {loc : CerbLocation.Loc} {tid : thread_id} {uw : Bool}
    {pref : prefix0} {align : CerbMem.IntegerValue} {ty : ctype}
    {reqAddr : Option Int} {k : Nat → CerbMem.PointerValue → thread_state}
    (h : applyMemM (CerbMem.allocateObject tds 0 pref align ty reqAddr none) σ = none) :
    (dischargeStep tds aid rs σ (Step_action_request2 str loc tid uw
      (stExceptUndef_return (CreateRequest2 pref align ty reqAddr none k)))).isRefusal := by
  rcases hm : CerbMem.allocateObject tds 0 pref align ty reqAddr none with ⟨f⟩
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

theorem dischargeStep_kill_active {tds : CerbTags.TagDefsMap} {aid : Nat} {rs : core_run_state}
    {σ σ' : Mem} {str : String}
    {loc loc₀ : CerbLocation.Loc} {tid : thread_id} {uw : Bool}
    {isDyn : Bool} {pv : CerbMem.PointerValue} {k : Nat → thread_state}
    (h : applyMemM (CerbMem.killM loc₀ isDyn pv) σ = some ((), σ')) :
    dischargeStep tds aid rs σ (Step_action_request2 str loc tid uw
      (stExceptUndef_return (KillRequest2 isDyn pv k))) =
      .next (k aid) σ' := by
  replace h := (killM_loc_irrel loc₀ loc).trans h
  rcases hm : CerbMem.killM loc isDyn pv with ⟨f⟩
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
    obtain rfl : st = σ' := by
      cases h; rfl
    rfl
  all_goals cases h

theorem dischargeStep_kill_refusal {tds : CerbTags.TagDefsMap} {aid : Nat} {rs : core_run_state}
    {σ : Mem} {str : String}
    {loc loc₀ : CerbLocation.Loc} {tid : thread_id} {uw : Bool}
    {isDyn : Bool} {pv : CerbMem.PointerValue} {k : Nat → thread_state}
    (h : applyMemM (CerbMem.killM loc₀ isDyn pv) σ = none) :
    (dischargeStep tds aid rs σ (Step_action_request2 str loc tid uw
      (stExceptUndef_return (KillRequest2 isDyn pv k)))).isRefusal := by
  replace h := (killM_loc_irrel loc₀ loc).trans h
  rcases hm : CerbMem.killM loc isDyn pv with ⟨f⟩
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

/-- `allocateRegion` reads none of its discarded arguments (kill/free arc
    K3): the thread id is `_ : Nat` (CerbMem.lean:1533), so the mirror's `0`
    and the driver's `tid1` are one term. -/
theorem allocateRegion_arg_irrel (tid tid' : Nat) (pref : prefix0)
    (align size : CerbMem.IntegerValue) :
    CerbMem.allocateRegion tid pref align size =
      CerbMem.allocateRegion tid' pref align size := rfl

theorem dischargeStep_alloc_active {tds : CerbTags.TagDefsMap} {aid : Nat} {rs : core_run_state}
    {σ σ' : Mem} {str : String}
    {loc : CerbLocation.Loc} {tid : thread_id} {uw : Bool}
    {pref : prefix0} {align size : CerbMem.IntegerValue}
    {k : Nat → CerbMem.PointerValue → thread_state}
    {pv : CerbMem.PointerValue}
    (h : applyMemM (CerbMem.allocateRegion 0 pref align size) σ = some (pv, σ')) :
    dischargeStep tds aid rs σ (Step_action_request2 str loc tid uw
      (stExceptUndef_return (AllocRequest2 pref align size k))) =
      .next (k aid pv) σ' := by
  rcases hm : CerbMem.allocateRegion 0 pref align size with ⟨f⟩
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

theorem dischargeStep_alloc_refusal {tds : CerbTags.TagDefsMap} {aid : Nat} {rs : core_run_state}
    {σ : Mem} {str : String}
    {loc : CerbLocation.Loc} {tid : thread_id} {uw : Bool}
    {pref : prefix0} {align size : CerbMem.IntegerValue}
    {k : Nat → CerbMem.PointerValue → thread_state}
    (h : applyMemM (CerbMem.allocateRegion 0 pref align size) σ = none) :
    (dischargeStep tds aid rs σ (Step_action_request2 str loc tid uw
      (stExceptUndef_return (AllocRequest2 pref align size k)))).isRefusal := by
  rcases hm : CerbMem.allocateRegion 0 pref align size with ⟨f⟩
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

/-! ## S3 — THE JUMP-PROFILE CERTIFICATION

Everything below certifies the S3 mirror rules (Step.lean header
notes 3-5) against the engine: the pure-evaluator bridge into
`full_eval_pexpr` (the state-threaded evaluator all guard/argument
premises are certified against), the extended redex/decomposition
layer (`Redex`/`Decomp` — the factor theorem WITH the jump
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

/-- The binops the mirror evaluator covers (`evalBinop`): integer
    arithmetic `Add`/`Sub`/`Mul` and the comparisons
    `Eq`/`Lt`/`Le`/`Gt`/`Ge`. `Div`/`Rem_t`/`Rem_f`/`Exp`/`And`/`Or` are
    outside (fragment closure, 2026-09-02: the operand grammar is
    declared as exactly what the mirror covers). -/
def isMirroredOp : binop → Bool
  | .OpAdd | .OpSub | .OpMul | .OpEq | .OpLt | .OpLe | .OpGt | .OpGe => true
  | _ => false

/-- The covered operand sub-grammar: value leaves, symbols, the eight
    mirrored binops, array shifts. -/
inductive PePure : generic_pexpr Unit sym → Prop where
  | val (a : List annot) (v : value) : PePure (Pexpr a () (PEval v))
  | sym (a : List annot) (x : sym) : PePure (Pexpr a () (PEsym x))
  | op (a : List annot) (op : binop) (hop : isMirroredOp op = true)
      {pe1 pe2 : generic_pexpr Unit sym} :
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

/-- Boolean membership in the covered grammar (kernel-decidable at
    authored operands: `PePure.of_isPePure rfl`). -/
def isPePure : generic_pexpr Unit sym → Bool
  | Pexpr _ _ (PEval _) => true
  | Pexpr _ _ (PEsym _) => true
  | Pexpr _ _ (PEop op pe1 pe2) => isMirroredOp op && isPePure pe1 && isPePure pe2
  | Pexpr _ _ (PEarray_shift pe1 _ pe2) => isPePure pe1 && isPePure pe2
  | _ => false

theorem PePure.of_isPePure {pe : generic_pexpr Unit _root_.sym} (h : isPePure pe = true) :
    PePure pe := by
  induction pe using isPePure.induct with
  | case1 a u v => cases u; exact .val a v
  | case2 a u x => cases u; exact .sym a x
  | case3 a u op pe1 pe2 ih1 ih2 =>
    cases u
    simp only [isPePure, Bool.and_eq_true] at h
    exact .op a op h.1.1 (ih1 h.1.2) (ih2 h.2)
  | case4 a u pe1 ty pe2 ih1 ih2 =>
    cases u
    simp only [isPePure, Bool.and_eq_true] at h
    exact .arrayShift a ty (ih1 h.1) (ih2 h.2)
  | case5 pe _ _ _ _ => simp [isPePure] at h

theorem PePure.all_of_isPePure {pes : List (generic_pexpr Unit _root_.sym)}
    (h : pes.all isPePure = true) : ∀ pe ∈ pes, PePure pe := by
  intro pe hpe
  exact PePure.of_isPePure (List.all_eq_true.mp h pe hpe)

/-- A binop the mirror evaluates is a mirrored one. -/
theorem evalBinop_mirrored {op : binop} {v1 v2 v : value}
    (h : evalBinop op v1 v2 = some v) : isMirroredOp op = true := by
  unfold evalBinop at h
  split at h <;> first | rfl | cases h

/-- Off-grammar shapes evaluate to nothing (fail-closed). -/
theorem evalPexpr_none_of_shape {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym} {ρ : EnvStack}
    {pe : generic_pexpr Unit sym}
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
    evalPexpr tds ext ρ pe = none := by
  unfold evalPexpr
  split
  · exact absurd rfl (hne1 _ _ _)
  · exact absurd rfl (hne2 _ _ _)
  · exact absurd rfl (hne3 _ _ _ _ _)
  · exact absurd rfl (hne4 _ _ _ _ _)
  · rfl

/-- Mirror success implies the covered shape. -/
theorem evalPexpr_shape {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym} {ρ : EnvStack}
    {pe : generic_pexpr Unit sym} {v : value}
    (h : evalPexpr tds ext ρ pe = some v) : PePure pe := by
  revert h
  revert v
  induction pe using evalPexpr.induct with
  | case1 a u v' => intro v h; exact .val a v'
  | case2 a u x => intro v h; exact .sym a x
  | case3 a u op pe1 pe2 ih1 ih2 =>
    intro v h
    rw [evalPexpr_op] at h
    cases h1 : evalPexpr tds ext ρ pe1 with
    | none => rw [h1] at h; cases h
    | some v1 =>
      cases h2 : evalPexpr tds ext ρ pe2 with
      | none => rw [h1, h2] at h; cases h
      | some v2 =>
        rw [h1, h2] at h
        exact .op a op (evalBinop_mirrored h) (ih1 h1) (ih2 h2)
  | case4 a u pe1 ty pe2 ih1 ih2 =>
    intro v h
    rw [evalPexpr_array_shift] at h
    cases h1 : evalPexpr tds ext ρ pe1 with
    | none => rw [h1] at h; cases h
    | some v1 =>
      cases h2 : evalPexpr tds ext ρ pe2 with
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
    grammar); the extern map is QUANTIFIED (S1b′) — the engine's
    `PEsym` indirection is the mirror's `resolveExtern`, matched
    case by case on the lookup. -/
theorem step_eval_bridge {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {ext : Fmap sym sym} {ρ : EnvStack}
    {pe : generic_pexpr Unit sym}
    {v : value} (hp : PePure pe) (hv : evalPexpr tds ext ρ pe = some v) :
    ∀ (fuel : Nat), peDepth pe ≤ fuel →
    ∀ (n : Nat)
      (loc : CerbLocation.Loc) (cloc : Option CerbLocation.Loc)
      (mem : Option CerbMem.MemState)
      (file : generic_file Unit core_run_annotation),
    step_eval_pexpr_lemFuel fuel tds n loc cloc ext ρ mem file false pe =
      exception_undef_return (Pexpr [] () (PEval v)) := by
  induction hp generalizing v with
  | val a v' =>
    intro fuel hfuel n loc cloc mem file
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 :=
      ⟨fuel - 1, by have := peDepth_pos (Pexpr a () (PEval v')); omega⟩
    obtain rfl : v' = v := by simpa using hv
    rfl
  | sym a x =>
    intro fuel hfuel n loc cloc mem file
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 :=
      ⟨fuel - 1, by have := peDepth_pos (Pexpr a () (PEsym x)); omega⟩
    have hx : lookup_env (resolveExtern ext x) ρ = some v := by simpa using hv
    show exception_undef_fmap (Pexpr [] ()) _ = _
    dsimp only
    -- the engine's extern indirection is the mirror's `resolveExtern`,
    -- case by case on the lookup
    cases hres : fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
        Lem_Basic_classes.ordCompare s1 s2) x ext with
    | none =>
      rw [show resolveExtern ext x = x by unfold resolveExtern; rw [hres]]
        at hx
      dsimp only
      rw [hx]
      rfl
    | some y =>
      rw [show resolveExtern ext x = y by unfold resolveExtern; rw [hres]]
        at hx
      dsimp only
      rw [hx]
      rfl
  | @op a op hop pe1 pe2 hp1 hp2 ih1 ih2 =>
    intro fuel hfuel n loc cloc mem file
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    rw [evalPexpr_op] at hv
    obtain ⟨v1, h1, v2, h2, hb⟩ : ∃ v1, evalPexpr tds ext ρ pe1 = some v1 ∧
        ∃ v2, evalPexpr tds ext ρ pe2 = some v2 ∧ evalBinop op v1 v2 = some v := by
      cases h1 : evalPexpr tds ext ρ pe1 with
      | none => rw [h1] at hv; cases hv
      | some v1 =>
        cases h2 : evalPexpr tds ext ρ pe2 with
        | none => rw [h1, h2] at hv; cases hv
        | some v2 =>
          rw [h1, h2] at hv
          exact ⟨v1, rfl, v2, rfl, hv⟩
    have hd1 : peDepth pe1 ≤ f := by simp at hfuel; omega
    have hd2 : peDepth pe2 ≤ f := by simp at hfuel; omega
    show exception_undef_fmap (Pexpr [] ()) _ = _
    dsimp only [step_eval_peop]
    rw [ih1 h1 f hd1 (n+1) loc cloc mem file,
      ih2 h2 f hd2 (n+1) loc cloc mem file]
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
    intro fuel hfuel n loc cloc mem file
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    rw [evalPexpr_array_shift] at hv
    obtain ⟨v1, h1, v2, h2, hb⟩ : ∃ v1, evalPexpr tds ext ρ pe1 = some v1 ∧
        ∃ v2, evalPexpr tds ext ρ pe2 = some v2 ∧
          evalArrayShift tds ty v1 v2 = some v := by
      cases h1 : evalPexpr tds ext ρ pe1 with
      | none => rw [h1] at hv; cases hv
      | some v1 =>
        cases h2 : evalPexpr tds ext ρ pe2 with
        | none => rw [h1, h2] at hv; cases hv
        | some v2 =>
          rw [h1, h2] at hv
          exact ⟨v1, rfl, v2, rfl, hv⟩
    have hd1 : peDepth pe1 ≤ f := by simp at hfuel; omega
    have hd2 : peDepth pe2 ≤ f := by simp at hfuel; omega
    show exception_undef_fmap (Pexpr [] ()) _ = _
    dsimp only
    rw [ih1 h1 f hd1 (n+1) loc cloc mem file,
      ih2 h2 f hd2 (n+1) loc cloc mem file]
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
  | op a op hop hp1 hp2 ih1 ih2 => exact .op [] op hop ih1 ih2
  | arrayShift a ty hp1 hp2 ih1 ih2 => exact .arrayShift [] ty ih1 ih2

theorem evalPexpr_peStrip {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym} {ρ : EnvStack}
    {pe : generic_pexpr Unit sym}
    (hp : PePure pe) : evalPexpr tds ext ρ (peStrip pe) = evalPexpr tds ext ρ pe := by
  induction hp with
  | val a v => rfl
  | sym a x => rfl
  | op a op hop hp1 hp2 ih1 ih2 =>
    show evalPexpr tds ext ρ (Pexpr [] () (PEop op _ _)) = _
    rw [evalPexpr_op, evalPexpr_op, ih1, ih2]
  | arrayShift a ty hp1 hp2 ih1 ih2 =>
    show evalPexpr tds ext ρ (Pexpr [] () (PEarray_shift _ ty _)) = _
    rw [evalPexpr_array_shift, evalPexpr_array_shift, ih1, ih2]

theorem peDepth_peStrip {pe : generic_pexpr Unit sym} (hp : PePure pe) :
    peDepth (peStrip pe) = peDepth pe := by
  induction hp with
  | val a v => rfl
  | sym a x => rfl
  | op a op hop hp1 hp2 ih1 ih2 =>
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
  | @op a op hop pe1 pe2 hp1 hp2 ih1 ih2 =>
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
theorem aux2_bridge {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {ext : Fmap sym sym} {ρ : EnvStack}
    {pe : generic_pexpr Unit sym} {v : value}
    (hp : PePure pe) (hv : evalPexpr tds ext ρ pe = some v)
    (hd : peDepth pe ≤ lemDefaultFuel) :
    ∀ (fuel : Nat)
      (loc : CerbLocation.Loc) (cloc : Option CerbLocation.Loc)
      (mem : Option CerbMem.MemState)
      (file : generic_file Unit core_run_annotation),
    eval_pexpr_aux2_lemFuel (fuel + 1) tds loc cloc ext ρ mem file pe =
      exception_undef_return (Sum.inr v) := by
  intro fuel loc cloc mem file
  have hpull : pull_constrained 0 pe = peStrip pe :=
    pull_bridge hp lemDefaultFuel hd 0
  have hstep := step_eval_bridge hp.strip
    (by rw [evalPexpr_peStrip hp]; exact hv) lemDefaultFuel
    (by rw [peDepth_peStrip hp]; exact hd) 0 loc cloc mem file
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
  | @op a op hop pe1 pe2 hp1 hp2 =>
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
    Extern QUANTIFIED (S1b′); tagDefs/memory/file quantified
    (unread). -/
theorem full_eval_bridge {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {b : Type} {ext : Fmap sym sym} {th : thread_state}
    {pe : generic_pexpr Unit sym} {v : value}
    (hv : evalPexpr tds ext th.env pe = some v)
    (hd : peDepth pe ≤ lemDefaultFuel)
    (σ : CerbMem.MemState) (file : generic_file Unit core_run_annotation) :
    full_eval_pexpr (b := b) tds th ext σ file pe =
      stExceptUndef_return v := by
  have hp := evalPexpr_shape hv
  rw [show (full_eval_pexpr (b := b) tds th ext σ file pe) =
    full_eval_pexpr_lemFuel (b := b) (999999 + 1) tds th ext σ file pe
    from rfl]
  show stExceptUndef_bind _ _ = _
  funext st
  show (match E.eval_pexpr20 tds th ext σ file pe st with
    | _ => _ : exceptM _ _) = _
  rw [show E.eval_pexpr20 (a := b) tds th ext σ file pe =
    runEU ((eval_pexpr_aux2 tds) th.current_loc
      (match th.exec_loc with
        | ELoc_globals => none
        | ELoc_normal [] => none
        | ELoc_normal ((_, loc1) :: _) => some loc1)
      ext th.env (some σ) file pe) from rfl]
  rw [show (eval_pexpr_aux2 (tds)) = eval_pexpr_aux2_lemFuel (999999 + 1) tds
    from rfl]
  rw [aux2_bridge hp hv hd 999999 th.current_loc _ (some σ) file]
  rfl

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

/-- The proc-carrying profile's thread literal is the `procCtx`
    instance's thread, definitionally. -/
theorem procCtx_thread (p : sym) (rs : core_run_state) (e : CoreExpr)
    (ρ : EnvStack) : (procCtx rs).thread e ρ (procCtl p) = procThread p e ρ := rfl

/-- The Q↔labeled tie (the donor's `⌜Q = rf.f_code⌝`,
    lifting.v:1002): the run state's two-level `labeled` map has
    fiber `Q` at the current procedure. Pure, stated in the engine's
    own lookup spelling. -/
def LabeledAt (rs : core_run_state) (p : sym) (Q : LabelMap) : Prop :=
  fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
    Lem_Basic_classes.ordCompare s1 s2) p rs.labeled = some Q

/-- A successful label lookup in a DERIVED label map certifies the
    whole read path: there IS a current procedure and its resolved
    fiber IS `M.labelsAt ctl.proc` (the old `LabeledAt` tie hypothesis, now a
    derived fact — the S1a probe's `labels_lookup_some`). -/
theorem MachineCtx.labels_lookup_some {M : MachineCtx} {ctl : Ctl} {l : sym}
    {pc : List (sym × core_base_type) × CoreExpr}
    (h : lookupLabel (M.labelsAt ctl.proc) l = some pc) :
    ∃ p, ctl.proc = some p ∧
      LabeledAt M.runState (M.resolveProc p) (M.labelsAt ctl.proc) := by
  cases hp : ctl.proc with
  | none =>
    rw [hp, MachineCtx.labelsAt_none, lookupLabel_empty] at h
    cases h
  | some p =>
    rw [hp] at h
    cases hQ : fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
        Lem_Basic_classes.ordCompare s1 s2)
        (M.resolveProc p) M.runState.labeled with
    | none =>
      rw [show M.labelsAt (some p) = fmapEmpty by
        rw [MachineCtx.labelsAt_some, hQ], lookupLabel_empty] at h
      cases h
    | some Q =>
      have hlab' : M.labelsAt (some p) = Q := by
        rw [MachineCtx.labelsAt_some, hQ]
      exact ⟨p, rfl, show fmapLookupBy _ _ _ = some (M.labelsAt (some p)) by
        rw [hlab']; exact hQ⟩

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
    (hd : Decomp e ctx (saveRedex sb ps body))
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
    (hd : Decomp e ctx (caseRedex (Pexpr a () (PEval cval)) pats))
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
    `runEU`-lifted), env verbatim, memory verbatim. Extern QUANTIFIED
    (S1b′ — the bridge threads the PEsym indirection). -/
theorem stepDischarge_if_true {e : CoreExpr} {ctx : context}
    {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
    (hd : Decomp e ctx (ifRedex g e2 e3))
    (hsz : esize e ≤ lemDefaultFuel)
    (hdg : peDepth g ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hg : evalPexpr tds ext th.env g = some Vtrue)
    (aid : Nat) (rs : core_run_state) :
    (step_ctx tds σ file ext tid (parent, th)).map
        (dischargeStep tds aid rs σ) =
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
     rw [full_eval_bridge hg hdg σ file]
     dsimp only [stExceptUndef_bind, stExceptUndef_return, stExpect_return,
       return1, except_return]
     rfl)

/-- Eif (FALSE) — symmetric. -/
theorem stepDischarge_if_false {e : CoreExpr} {ctx : context}
    {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
    (hd : Decomp e ctx (ifRedex g e2 e3))
    (hsz : esize e ≤ lemDefaultFuel)
    (hdg : peDepth g ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hg : evalPexpr tds ext th.env g = some Vfalse)
    (aid : Nat) (rs : core_run_state) :
    (step_ctx tds σ file ext tid (parent, th)).map
        (dischargeStep tds aid rs σ) =
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
     rw [full_eval_bridge hg hdg σ file]
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
    Extern QUANTIFIED (S1b′ — the bridge threads the PEsym
    indirection). -/
theorem stepDischarge_pure_sym {e : CoreExpr} {ctx : context}
    {pb : List _root_.annot} {x : sym} {v : value}
    (hd : Decomp e ctx (pureRedex (Pexpr pb () (PEsym x))))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hv : evalPexpr tds ext th.env (Pexpr pb () (PEsym x)) = some v)
    (aid : Nat) (rs : core_run_state) :
    (step_ctx tds σ file ext tid (parent, th)).map
        (dischargeStep tds aid rs σ) =
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
     rw [full_eval_bridge hv (peDepth_sym_le pb x) σ file]
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
  | op a op hop hp1 hp2 => rfl
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
    (hd : Decomp e ctx (loadOpRedex loc ann ty pe2 mo))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv2 : valueFromPexpr pe2 = none)
    (hp2 : PePure pe2)
    (hd2 : peDepth pe2 ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hv2 : evalPexpr tds ext th.env pe2 = some (Vobject (OVpointer pv)))
    (aid : Nat) (rs : core_run_state) :
    (step_ctx tds σ file ext tid (parent, th)).map
        (dischargeStep tds aid rs σ) =
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
     rw [full_eval_bridge (v := Vctype ty) rfl (peDepth_val_le _ _) σ file,
       full_eval_bridge hv2 hd2 σ file]
     dsimp only [stExceptUndef_bind, stExceptUndef_return, stExpect_return,
       return1, except_return]
     rfl)

/-- Kill ACTION_EVAL, context undisturbed, DISCHARGED (kill/free arc
    K2 — step_action's Kill `none` arm + process_action's ACTION_EVAL
    wrap): ONE engine step big-step-evaluating the pointer operand
    through the certified evaluator, run state VERBATIM (∀ rs),
    env/memory verbatim; the successor rebuilds the CANONICAL KILL
    REDEX in context. -/
theorem stepDischarge_kill_eval {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {kind : kill_kind}
    {pe : generic_pexpr Unit sym} {pv : CerbMem.PointerValue}
    (hd : Decomp e ctx (killOpRedex loc ann kind pe))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexpr pe = none)
    (hp : PePure pe)
    (hdp : peDepth pe ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hv : evalPexpr tds ext th.env pe = some (Vobject (OVpointer pv)))
    (aid : Nat) (rs : core_run_state) :
    (step_ctx tds σ file ext tid (parent, th)).map
        (dischargeStep tds aid rs σ) =
      [.next { th with arena := apply_ctx ctx (killRedex loc ann kind pv) }
        σ] := by
  have hget : get_ctx th.arena = [(ctx, killOpRedex loc ann kind pe)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold killOpRedex
  cases ctx <;>
    (dsimp only [get_loc]
     dsimp only [step_action]
     rw [act_valueFromPexpr_none hp hnv]
     dsimp only [act_valueFromPexpr, valueFromPexpr]
     dsimp only [dischargeStep]
     rw [full_eval_bridge hv hdp σ file]
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
    (hd : Decomp e ctx
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
    (hd : Decomp e ctx
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
    {file : generic_file Unit core_run_annotation} {ext : Fmap sym sym}
    (f : EnvStack → (sym × core_base_type) × generic_pexpr Unit sym →
      core_run_state → exceptM ((t0 EnvStack × core_run_state)) core_run_cause)
    (hf : ∀ (acc : EnvStack) (s : sym) (bTy : core_base_type)
      (pe : generic_pexpr Unit sym) (rs' : core_run_state),
      f acc ((s, bTy), pe) rs' =
        stExceptUndef_bind (full_eval_pexpr tds th ext σ file pe)
          (fun cval =>
            stExceptUndef_return (update_env (mk_sym_pat s bTy) cval acc)) rs') :
    ∀ (params : List (sym × core_base_type))
      (pes : List (generic_pexpr Unit sym)) (vs : List value)
      (acc : EnvStack) (rs : core_run_state),
      evalPexprs tds ext th.env pes = some vs →
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
      obtain ⟨v, hv, vs', hvs', rfl⟩ : ∃ v, evalPexpr tds ext th.env pe = some v ∧
          ∃ vs', evalPexprs tds ext th.env pes = some vs' ∧ vs = v :: vs' := by
        cases h1 : evalPexpr tds ext th.env pe with
        | none => rw [h1] at hvs; cases hvs
        | some v =>
          cases h2 : evalPexprs tds ext th.env pes with
          | none => rw [h1, h2] at hvs; cases hvs
          | some vs' =>
            rw [h1, h2] at hvs
            cases hvs
            exact ⟨v, rfl, vs', rfl, rfl⟩
      obtain ⟨p1, p2⟩ := p
      rw [List.zip_cons_cons, stExceptUndef_foldM_cons,
        stExceptUndef_bind_apply, hf acc p1 p2 pe rs,
        stExceptUndef_bind_apply,
        full_eval_bridge hv (hdep pe (by simp)) σ file,
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
    run state is read (the `labeled` fiber at the EXTERN-RESOLVED
    current procedure — `resolveExtern`'s identity fallback, S1b′
    quantified — the pure Q↔labeled tie `LabeledAt`) and returned
    VERBATIM (`state_except_read` + `runEU`-lifted argument
    evaluation); the unresolvable-label and no-current-proc
    failwithI PANIC channels are excluded by `hl`/`hproc`. -/
theorem stepDischarge_run {e : CoreExpr} {ctx : context}
    {ra : core_run_annotation} {l : sym}
    {pes : List (generic_pexpr Unit sym)}
    (hd : Decomp e ctx (runRedex ra l pes))
    (hsz : esize e ≤ lemDefaultFuel)
    {Q : LabelMap} {params : List (sym × core_base_type)} {cont : CoreExpr}
    {vs : List value}
    (hl : lookupLabel Q l = some (params, cont))
    (hdep : ∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (p : sym) (th : thread_state)
    (harena : th.arena = e)
    (hproc : th.current_proc_opt = some p)
    (hvs : evalPexprs tds ext th.env pes = some vs)
    (aid : Nat) (rs : core_run_state)
    (hQ : LabeledAt rs (resolveExtern ext p) Q) :
    (step_ctx tds σ file ext tid (parent, th)).map
        (dischargeStep tds aid rs σ) =
      [.next { th with env := bindArgs params vs th.env, arena := cont } σ] := by
  have hget : get_ctx th.arena = [(ctx, runRedex ra l pes)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  have hQ' : (fmapLookupBy (fun (sym1 : sym) (sym2 : sym) =>
      Lem_Basic_classes.ordCompare sym1 sym2) (resolveExtern ext p)
      rs.labeled) = some Q := hQ
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
     -- the engine's proc indirection is the mirror's `resolveExtern`,
     -- case by case on the lookup (S1b′ — the sym-arm precedent)
     cases hres : fmapLookupBy (fun (sym1 : sym) (sym2 : sym) =>
         Lem_Basic_classes.ordCompare sym1 sym2) p ext with
     | none =>
       rw [show resolveExtern ext p = p by
         unfold resolveExtern; rw [hres]] at hQ'
       dsimp only []
       rw [hQ', bind0_some, hl']
       dsimp only []
       rw [stExceptUndef_bind_apply,
         foldM_args_bridge _ (fun _ _ _ _ _ => rfl) params pes vs th.env rs
           hvs hdep]
       dsimp only []
       rw [stExceptUndef_return_apply]
     | some y =>
       rw [show resolveExtern ext p = y by
         unfold resolveExtern; rw [hres]] at hQ'
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
    (hd : Decomp e ctx (memopRedex mop [pe1, pe2]))
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
theorem dischargeStep_memop_active {tds : CerbTags.TagDefsMap} {aid : Nat} {rs : core_run_state}
    {σ σ' : Mem} {loc : CerbLocation.Loc} {tid : thread_id} {uw : Bool}
    {pv1 pv2 : CerbMem.PointerValue} {k : value → thread_state} {b : Bool}
    (h : applyMemM (CerbMem.eqPtrval default pv1 pv2) σ = some (b, σ')) :
    dischargeStep tds aid rs σ (Step_memop_request2 loc PtrEq
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
theorem eval1_bridge {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {ext : Fmap sym sym} {th : thread_state} {pe : generic_pexpr Unit sym}
    {v : value} (hv : evalPexpr tds ext th.env pe = some v)
    (hdp : peDepth pe ≤ lemDefaultFuel)
    (σ : CerbMem.MemState) (file : generic_file Unit core_run_annotation)
    (rs : core_run_state) :
    stExceptUndef_bind
      (E.eval_pexpr20 (a := core_run_state) tds th ext σ file pe)
      (fun x => match x with
        | Sum.inl pe' => stExceptUndef_return pe'
        | Sum.inr cval => stExceptUndef_return (mk_value_pe cval)) rs =
      Result (Defined (mk_value_pe v), rs) := by
  have hp := evalPexpr_shape hv
  rw [stExceptUndef_bind_apply]
  rw [show E.eval_pexpr20 (a := core_run_state) tds th ext σ file pe =
    runEU ((eval_pexpr_aux2 tds) th.current_loc
      (match th.exec_loc with
        | ELoc_globals => none
        | ELoc_normal [] => none
        | ELoc_normal ((_, loc1) :: _) => some loc1)
      ext th.env (some σ) file pe) from rfl]
  rw [show (eval_pexpr_aux2 (tds)) = eval_pexpr_aux2_lemFuel (999999 + 1) tds
    from rfl]
  rw [aux2_bridge hp hv hdp 999999 th.current_loc _ (some σ) file]
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
theorem mapM_eval1_bridge {ext : Fmap sym sym} {th : thread_state}
    {tds : Fmap sym (CerbLocation.Loc × tag_definition)} {σ : Mem}
    {file : generic_file Unit core_run_annotation}
    (f : generic_pexpr Unit sym → core_run_state →
      exceptM ((t0 (generic_pexpr Unit sym) × core_run_state)) core_run_cause)
    (hf : ∀ (pe : generic_pexpr Unit sym) (rs' : core_run_state),
      f pe rs' = stExceptUndef_bind
        (E.eval_pexpr20 (a := core_run_state) tds th ext σ file pe)
        (fun x => match x with
          | Sum.inl pe' => stExceptUndef_return pe'
          | Sum.inr cval => stExceptUndef_return (mk_value_pe cval)) rs')
    {pe1 pe2 : generic_pexpr Unit sym} {v1 v2 : value}
    (hv1 : evalPexpr tds ext th.env pe1 = some v1)
    (hd1 : peDepth pe1 ≤ lemDefaultFuel)
    (hv2 : evalPexpr tds ext th.env pe2 = some v2)
    (hd2 : peDepth pe2 ≤ lemDefaultFuel)
    (rs : core_run_state) :
    stExceptUndef_mapM f [pe1, pe2] rs =
      Result (Defined [mk_value_pe v1, mk_value_pe v2], rs) := by
  have h1 : f pe1 rs = Result (Defined (mk_value_pe v1), rs) :=
    (hf pe1 rs).trans (eval1_bridge hv1 hd1 σ file rs)
  have h2 : f pe2 rs = Result (Defined (mk_value_pe v2), rs) :=
    (hf pe2 rs).trans (eval1_bridge hv2 hd2 σ file rs)
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

/-- Literal initializers are within any fuel: a value pexpr has depth 1
    (`Frag.save`'s side condition at the pre-QA-1 literal shape). -/
theorem saveParams_depth_of_vals
    {ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
    {cvals : List value}
    (h : valueFromPexprs (saveParamPexprs ps) = some cvals) :
    ∀ pe ∈ saveParamPexprs ps, peDepth pe ≤ lemDefaultFuel := by
  generalize saveParamPexprs ps = pes at h ⊢
  induction pes generalizing cvals with
  | nil => intro pe hpe; cases hpe
  | cons pe pes ih =>
    rw [valueFromPexprs_cons] at h
    revert h
    cases hpe : valueFromPexpr pe with
    | none => intro h; cases h
    | some v =>
      cases hpes : valueFromPexprs pes with
      | none => intro h; cases h
      | some vs =>
        intro h pe' hpe'
        rcases List.mem_cons.mp hpe' with rfl | hmem
        · rcases pe' with ⟨a, u, pe_⟩
          cases u
          cases pe_ <;> simp only [valueFromPexpr] at hpe
          all_goals first
            | exact peDepth_val_le _ _
            | (cases hpe)
        · exact ih hpes pe' hmem

/-- The EVAL arm's re-formed initializers are literal, hence within fuel. -/
theorem saveParamsWithValues_depth
    (ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)))
    (cvals : List value) (hlen : (saveParamPexprs ps).length = cvals.length) :
    ∀ pe ∈ saveParamPexprs (saveParamsWithValues ps cvals),
      peDepth pe ≤ lemDefaultFuel :=
  saveParams_depth_of_vals (valueFromPexprs_withValues ps cvals
    ((List.length_map ..).symm.trans hlen))

/-- Literal initializers are in the covered grammar (a value pexpr). -/
theorem saveParams_pure_of_vals
    {ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
    {cvals : List value}
    (h : valueFromPexprs (saveParamPexprs ps) = some cvals) :
    ∀ pe ∈ saveParamPexprs ps, PePure pe := by
  generalize saveParamPexprs ps = pes at h ⊢
  induction pes generalizing cvals with
  | nil => intro pe hpe; cases hpe
  | cons pe pes ih =>
    rw [valueFromPexprs_cons] at h
    revert h
    cases hpe : valueFromPexpr pe with
    | none => intro h; cases h
    | some v =>
      cases hpes : valueFromPexprs pes with
      | none => intro h; cases h
      | some vs =>
        intro h pe' hpe'
        rcases List.mem_cons.mp hpe' with rfl | hmem
        · rcases pe' with ⟨a, u, pe_⟩
          cases u
          cases pe_ <;> simp only [valueFromPexpr] at hpe
          all_goals first
            | exact .val _ _
            | (cases hpe)
        · exact ih hpes pe' hmem

/-- The EVAL arm's re-formed initializers are literal, hence covered. -/
theorem saveParamsWithValues_pure
    (ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)))
    (cvals : List value) :
    ∀ pe ∈ saveParamPexprs (saveParamsWithValues ps cvals), PePure pe := by
  intro pe hpe
  simp only [saveParamPexprs, saveParamsWithValues, List.map_map, List.mem_map] at hpe
  obtain ⟨p, -, rfl⟩ := hpe
  exact .val _ _

/-- The t0-monad sequencing of an all-`Defined` list is `Defined`
    (the tail of `stExceptUndef_mapM`, State_exception_undefined.lean:55). -/
theorem mapM1_id_defined {α : Type} (vs : List α) :
    mapM1 (fun (x : t0 α) => x) (vs.map Defined) = Defined vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    show bind2 (Defined v) (fun x => bind2 (mapM1 (fun (x : t0 α) => x) (vs.map Defined))
      (fun xs => return1 (x :: xs))) = _
    rw [ih]
    rfl

/-- The Esave EVAL arm's parameter map (`stExceptUndef_mapM` over
    `sym_bTy_pes`, one_step0's Esave non-value arm, Core_reduction.lean:353)
    computes the RE-FORMED list `saveParamsWithValues ps cvals`,
    STATE-VERBATIM: every initializer evaluates through one full
    evaluator iteration (`eval1_bridge`), the symbol/base-type parts
    ride verbatim. Both fold bodies are ABSTRACT with pointwise
    characterizations (`hg` for the per-parameter lambda, `hf` for the
    evaluator — the `mapM_eval1_bridge` pattern; the engine's lambdas
    satisfy them by `rfl`). -/
theorem mapM_save_bridge {ext : Fmap sym sym} {th : thread_state}
    {tds : Fmap sym (CerbLocation.Loc × tag_definition)} {σ : Mem}
    {file : generic_file Unit core_run_annotation}
    (f : generic_pexpr Unit sym → core_run_state →
      exceptM ((t0 (generic_pexpr Unit sym) × core_run_state)) core_run_cause)
    (hf : ∀ (pe : generic_pexpr Unit sym) (rs' : core_run_state),
      f pe rs' = stExceptUndef_bind
        (E.eval_pexpr20 (a := core_run_state) tds th ext σ file pe)
        (fun x => match x with
          | Sum.inl pe' => stExceptUndef_return pe'
          | Sum.inr cval => stExceptUndef_return (mk_value_pe cval)) rs')
    (g : (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)) →
      core_run_state → exceptM ((t0 (sym × ((core_base_type ×
        Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)) ×
        core_run_state)) core_run_cause)
    (hg : ∀ (p : sym × ((core_base_type ×
        Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))
        (rs' : core_run_state),
      g p rs' = stExceptUndef_bind (f p.2.2)
        (fun pe' => stExceptUndef_return (p.1, (p.2.1, pe'))) rs')
    (ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)))
    {cvals : List value}
    (hv : evalPexprs tds ext th.env (saveParamPexprs ps) = some cvals)
    (hd : ∀ pe ∈ saveParamPexprs ps, peDepth pe ≤ lemDefaultFuel)
    (rs : core_run_state) :
    stExceptUndef_mapM g ps rs =
      Result (Defined (saveParamsWithValues ps cvals), rs) := by
  have hmap : stExpect_mapM g ps rs =
      Result ((saveParamsWithValues ps cvals).map Defined, rs) := by
    induction ps generalizing cvals with
    | nil =>
      have hv' : evalPexprs tds ext th.env [] = some cvals := hv
      rw [evalPexprs_nil] at hv'
      obtain rfl : [] = cvals := Option.some.inj hv'
      rfl
    | cons p ps ih =>
      have hv' : evalPexprs tds ext th.env (p.2.2 :: saveParamPexprs ps) = some cvals := hv
      rw [evalPexprs_cons] at hv'
      revert hv'
      cases hvp : evalPexpr tds ext th.env p.2.2 with
      | none => intro hv'; cases hv'
      | some v =>
        cases hvs : evalPexprs tds ext th.env (saveParamPexprs ps) with
        | none => intro hv'; cases hv'
        | some vs =>
          intro hv'
          obtain rfl : v :: vs = cvals := Option.some.inj hv'
          have hdp : peDepth p.2.2 ≤ lemDefaultFuel :=
            hd _ (List.mem_cons_self ..)
          have hds : ∀ pe ∈ saveParamPexprs ps, peDepth pe ≤ lemDefaultFuel :=
            fun pe hpe => hd pe (List.mem_cons_of_mem _ hpe)
          have h1 : g p rs = Result (Defined (p.1, (p.2.1, mk_value_pe v)), rs) := by
            rw [hg, stExceptUndef_bind_apply, hf, eval1_bridge hvp hdp σ file rs]
            rfl
          show stExpect_bind (g p) (fun x => stExpect_bind (stExpect_mapM g ps)
            (fun xs => stExpect_return (x :: xs))) rs = _
          rw [stExpect_bind_result _ _ _ _ _ h1, stExpect_bind_result _ _ _ _ _ (ih hvs hds)]
          rfl
  unfold stExceptUndef_mapM
  rw [stExpect_bind_result _ _ _ _ _ hmap]
  show Result (mapM1 (fun (x : t0 _) => x) ((saveParamsWithValues ps cvals).map Defined), rs) = _
  rw [mapM1_id_defined]

/-! ### The procedure call (calls arc C2): the PCALL round in the engine's
own terms — the argument map, `call_proc`, the thread update -/

/-- The PCALL arm's argument map (`stExceptUndef_mapM full_eval_pexpr'
    pes`, step_ctx's Eproc arm, Core_reduction.lean:484 col 18133)
    computes the mirror's argument values, STATE-VERBATIM: every argument
    evaluates against the FIXED `th.env` (the `full_eval_pexpr'` closure)
    through the certified evaluator (`full_eval_bridge`). The per-argument
    body is abstract with a pointwise characterization (`mapM_save_bridge`'s
    pattern). -/
theorem mapM_full_eval_bridge {th : thread_state}
    {tds : Fmap sym (CerbLocation.Loc × tag_definition)} {σ : Mem}
    {file : generic_file Unit core_run_annotation} {ext : Fmap sym sym}
    (f : generic_pexpr Unit sym → core_run_state →
      exceptM ((t0 value × core_run_state)) core_run_cause)
    (hf : ∀ (pe : generic_pexpr Unit sym) (rs' : core_run_state),
      f pe rs' = full_eval_pexpr tds th ext σ file pe rs') :
    ∀ (pes : List (generic_pexpr Unit sym)) {vs : List value},
      evalPexprs tds ext th.env pes = some vs →
      (∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel) →
      ∀ rs, stExceptUndef_mapM f pes rs = Result (Defined vs, rs) := by
  intro pes vs hvs hd rs
  have hmap : stExpect_mapM f pes rs = Result (vs.map Defined, rs) := by
    induction pes generalizing vs with
    | nil =>
      rw [evalPexprs_nil] at hvs
      obtain rfl : [] = vs := Option.some.inj hvs
      rfl
    | cons pe pes ih =>
      rw [evalPexprs_cons] at hvs
      revert hvs
      cases hvp : evalPexpr tds ext th.env pe with
      | none => intro hvs; cases hvs
      | some v =>
        cases hvs' : evalPexprs tds ext th.env pes with
        | none => intro hvs; cases hvs
        | some vs' =>
          intro hvs
          obtain rfl : v :: vs' = vs := Option.some.inj hvs
          have hdp : peDepth pe ≤ lemDefaultFuel := hd _ (List.mem_cons_self ..)
          have hds : ∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel :=
            fun pe hpe => hd pe (List.mem_cons_of_mem _ hpe)
          have h1 : f pe rs = Result (Defined v, rs) := by
            rw [hf, full_eval_bridge hvp hdp σ file]
            rfl
          show stExpect_bind (f pe) (fun x => stExpect_bind (stExpect_mapM f pes)
            (fun xs => stExpect_return (x :: xs))) rs = _
          rw [stExpect_bind_result _ _ _ _ _ h1, stExpect_bind_result _ _ _ _ _ (ih hvs' hds)]
          rfl
  unfold stExceptUndef_mapM
  rw [stExpect_bind_result _ _ _ _ _ hmap]
  show Result (mapM1 (fun (x : t0 _) => x) (vs.map Defined), rs) = _
  rw [mapM1_id_defined]

/-- `call_proc` (Core_run.lean:93) in the mirror's terms: the lookup half
    is `lookupProc`, then the arity check, then the fresh frame
    `procEnv`; the two failures are the `Illformed_program` kills with
    the engine's own messages (quoted verbatim). -/
theorem call_proc_eq (ext : Fmap sym sym) (file : generic_file Unit core_run_annotation)
    (f : sym) (vs : List value) :
    call_proc ext file f vs =
      match lookupProc file ext f with
      | some (params, body) =>
        if not (@BEq.beq Nat (@Lem_Basic_classes.instBEqOfEq0 Nat Lem_Num.instEq0Nat_1)
            params.length vs.length) then
          fail0 (Illformed_program (String.append "calling procedure `"
            (String.append (show_symbol f)
              (String.append "' with the wrong number of args: |args|="
                (String.append (Lem_String_extra.stringFromNat vs.length)
                  (String.append "expecting: "
                    (Lem_String_extra.stringFromNat params.length)))))))
        else except_return (procEnv params vs, body)
      | none => fail0 (Illformed_program
          (String.append "calling an unknown procedure: " (show_symbol f))) := by
  unfold call_proc lookupProc procEnv resolveExtern
  cases hx : fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
      f ext with
  | some y =>
    simp only []
    cases h1 : fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
        f file.stdlib with
    | none =>
      simp only []
      cases h2 : fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
          y file.funs with
      | none => rfl
      | some d => cases d <;> rfl
    | some d =>
      cases d <;> simp only [] <;> first
        | rfl
        | (cases h2 : fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
              Lem_Basic_classes.ordCompare s1 s2) y file.funs with
           | none => rfl
           | some d' => cases d' <;> rfl)
  | none =>
    simp only []
    cases h1 : fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
        f file.stdlib with
    | none =>
      simp only []
      cases h2 : fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
          f file.funs with
      | none => rfl
      | some d => cases d <;> rfl
    | some d =>
      cases d <;> simp only [] <;> first
        | rfl
        | (cases h2 : fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
              Lem_Basic_classes.ordCompare s1 s2) f file.funs with
           | none => rfl
           | some d' => cases d' <;> rfl)

/-- `call_proc` SUCCEEDS exactly at a found procedure of matching arity. -/
theorem call_proc_of_lookupProc {file : generic_file Unit core_run_annotation}
    {ext : Fmap sym sym} {f : sym} {params : List (sym × core_base_type)}
    {body : CoreExpr} {vs : List value}
    (hf : lookupProc file ext f = some (params, body)) (hlen : params.length = vs.length) :
    call_proc ext file f vs = except_return (procEnv params vs, body) := by
  rw [call_proc_eq, hf]
  dsimp only
  have hb : (@BEq.beq Nat (@Lem_Basic_classes.instBEqOfEq0 Nat Lem_Num.instEq0Nat_1)
      params.length vs.length) = true := (lemNatBeq_iff _ _).mpr hlen
  rw [hb]
  rfl

/-- `call_proc` at an UNKNOWN procedure: the engine's kill, verbatim. -/
theorem call_proc_unknown {file : generic_file Unit core_run_annotation}
    {ext : Fmap sym sym} {f : sym} {vs : List value}
    (hf : lookupProc file ext f = none) :
    call_proc ext file f vs = fail0 (Illformed_program
      (String.append "calling an unknown procedure: " (show_symbol f))) := by
  rw [call_proc_eq, hf]

/-- `call_proc` at an ARITY MISMATCH: the engine's kill, verbatim. -/
theorem call_proc_arity {file : generic_file Unit core_run_annotation}
    {ext : Fmap sym sym} {f : sym} {params : List (sym × core_base_type)}
    {body : CoreExpr} {vs : List value}
    (hf : lookupProc file ext f = some (params, body)) (hlen : params.length ≠ vs.length) :
    call_proc ext file f vs = fail0 (Illformed_program (String.append "calling procedure `"
      (String.append (show_symbol f)
        (String.append "' with the wrong number of args: |args|="
          (String.append (Lem_String_extra.stringFromNat vs.length)
            (String.append "expecting: "
              (Lem_String_extra.stringFromNat params.length))))))) := by
  rw [call_proc_eq, hf]
  dsimp only
  have hb : (@BEq.beq Nat (@Lem_Basic_classes.instBEqOfEq0 Nat Lem_Num.instEq0Nat_1)
      params.length vs.length) = false := by
    cases hb : (@BEq.beq Nat (@Lem_Basic_classes.instBEqOfEq0 Nat Lem_Num.instEq0Nat_1)
        params.length vs.length) with
    | false => rfl
    | true => exact absurd ((lemNatBeq_iff _ _).mp hb) hlen
  rw [hb]
  rfl

/-- THE PROCEDURE CALL, in the engine's own terms (calls arc C2): at a
    thread whose arena decomposes to a call redex with arguments in the
    certified grammar, step_ctx takes EXACTLY ONE step — the PCALL arm's
    `Step_with_runstate2 (RSK_eval "Eproc") m` (Core_reduction.lean:484
    col 18133) — and, at a found procedure of matching arity, `m` at ANY
    run state is the thread with the callee installed, the fresh frame
    pushed, the current procedure set, the caller's procedure and the
    REDEX'S CONTEXT `ctx` pushed on the stack, the execution location
    pushed, the run state returned VERBATIM (the map and `runEU` are
    state-verbatim: no `labeled` write). The two `call_proc` failures are
    `step_ctx_call_unknown`/`step_ctx_call_arity` (Round.lean). -/
theorem step_ctx_call_ws {e : CoreExpr} {ctx : context}
    {ra : core_run_annotation} {f : sym} {pes : List (generic_pexpr Unit sym)}
    (hd : Decomp e ctx (callRedex ra f pes))
    (hsz : esize e ≤ lemDefaultFuel)
    (hdep : ∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    {vs : List value} (hvs : evalPexprs tds ext th.env pes = some vs)
    {params : List (sym × core_base_type)} {body : CoreExpr}
    (hf : lookupProc file ext f = some (params, body)) (hlen : params.length = vs.length) :
    ∃ m : core_runM thread_state,
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval "Eproc") m] ∧
      ∀ rs, m rs = Result (Defined
        { th with
          current_proc_opt := some f
          env := procEnv params vs :: th.env
          exec_loc := push_exec_loc f th.current_loc th.exec_loc
          stack0 := Stack_cons2 th.current_proc_opt ctx th.stack0
          arena := body }, rs) := by
  have hget : get_ctx th.arena = [(ctx, callRedex ra f pes)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold callRedex
  cases ctx <;>
    (dsimp only [get_loc]
     refine ⟨_, rfl, fun rs => ?_⟩
     rw [stExceptUndef_bind_apply,
       mapM_full_eval_bridge _ (fun _ _ => rfl) pes hvs hdep rs]
     dsimp only []
     rw [stExceptUndef_bind_apply, call_proc_of_lookupProc hf hlen]
     rfl)

/-- The PCALL round's SHAPE alone (any lookup outcome, any arguments):
    one `RSK_eval "Eproc"` with-runstate step. -/
theorem step_ctx_call_shape {e : CoreExpr} {ctx : context}
    {ra : core_run_annotation} {f : sym} {pes : List (generic_pexpr Unit sym)}
    (hd : Decomp e ctx (callRedex ra f pes))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e) :
    ∃ m : core_runM thread_state,
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval "Eproc") m] := by
  have hget : get_ctx th.arena = [(ctx, callRedex ra f pes)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold callRedex
  cases ctx <;>
    (dsimp only [get_loc]
     exact ⟨_, rfl⟩)

/-- The PCALL round at an UNKNOWN procedure (arguments evaluating): the
    monad RAISES `Illformed_program "calling an unknown procedure: …"` —
    the driver's transparent kill `Other (DErr_core_run …)`
    (`liftCore_run`, Driver.lean:245). -/
theorem step_ctx_call_unknown {e : CoreExpr} {ctx : context}
    {ra : core_run_annotation} {f : sym} {pes : List (generic_pexpr Unit sym)}
    (hd : Decomp e ctx (callRedex ra f pes))
    (hsz : esize e ≤ lemDefaultFuel)
    (hdep : ∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    {vs : List value} (hvs : evalPexprs tds ext th.env pes = some vs)
    (hf : lookupProc file ext f = none) :
    ∃ m : core_runM thread_state,
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval "Eproc") m] ∧
      ∀ rs, m rs = Exception (Illformed_program
        (String.append "calling an unknown procedure: " (show_symbol f))) := by
  have hget : get_ctx th.arena = [(ctx, callRedex ra f pes)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold callRedex
  cases ctx <;>
    (dsimp only [get_loc]
     refine ⟨_, rfl, fun rs => ?_⟩
     rw [stExceptUndef_bind_apply,
       mapM_full_eval_bridge _ (fun _ _ => rfl) pes hvs hdep rs]
     dsimp only []
     rw [stExceptUndef_bind_apply, call_proc_unknown hf]
     rfl)

/-- The PCALL round at an ARITY MISMATCH (arguments evaluating): the
    monad RAISES `Illformed_program "calling procedure `f' with the wrong
    number of args: …"` — the driver's transparent kill. -/
theorem step_ctx_call_arity {e : CoreExpr} {ctx : context}
    {ra : core_run_annotation} {f : sym} {pes : List (generic_pexpr Unit sym)}
    (hd : Decomp e ctx (callRedex ra f pes))
    (hsz : esize e ≤ lemDefaultFuel)
    (hdep : ∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    {vs : List value} (hvs : evalPexprs tds ext th.env pes = some vs)
    {params : List (sym × core_base_type)} {body : CoreExpr}
    (hf : lookupProc file ext f = some (params, body)) (hlen : params.length ≠ vs.length) :
    ∃ m : core_runM thread_state,
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval "Eproc") m] ∧
      ∀ rs, m rs = Exception (Illformed_program (String.append "calling procedure `"
        (String.append (show_symbol f)
          (String.append "' with the wrong number of args: |args|="
            (String.append (Lem_String_extra.stringFromNat vs.length)
              (String.append "expecting: "
                (Lem_String_extra.stringFromNat params.length))))))) := by
  have hget : get_ctx th.arena = [(ctx, callRedex ra f pes)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold callRedex
  cases ctx <;>
    (dsimp only [get_loc]
     refine ⟨_, rfl, fun rs => ?_⟩
     rw [stExceptUndef_bind_apply,
       mapM_full_eval_bridge _ (fun _ _ => rfl) pes hvs hdep rs]
     dsimp only []
     rw [stExceptUndef_bind_apply, call_proc_arity hf hlen]
     rfl)

/-- Esave PARAMETER EVALUATION, context undisturbed, DISCHARGED
    (one_step0's Esave EVAL arm + step_ctx's EVAL wrap + the
    liftCore_run protocol): ONE engine step mapping `eval_pexpr1` over
    the initializers (`mapM_save_bridge`), run state VERBATIM,
    env/memory verbatim; the successor rebuilds the Esave node with
    the evaluated initializers in context. -/
theorem stepDischarge_save_eval {e : CoreExpr} {ctx : context}
    {sb : sym × core_base_type}
    {ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
    {body : CoreExpr} {cvals : List value}
    (hd : Decomp e ctx (saveRedex sb ps body))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs (saveParamPexprs ps) = none)
    (hdep : ∀ pe ∈ saveParamPexprs ps, peDepth pe ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hv : evalPexprs tds ext th.env (saveParamPexprs ps) = some cvals)
    (aid : Nat) (rs : core_run_state) :
    (step_ctx tds σ file ext tid (parent, th)).map
        (dischargeStep tds aid rs σ) =
      [.next { th with
        arena := apply_ctx ctx (saveRedex sb (saveParamsWithValues ps cvals) body) } σ] := by
  have hget : get_ctx th.arena = [(ctx, saveRedex sb ps body)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  have hnv' : valueFromPexprs
      (List.map (fun p => match p with | (_, (_, z)) => z) ps) = none := by
    rw [show (List.map (fun (p : sym × ((core_base_type ×
        Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))
        => match p with | (_, (_, z)) => z) ps) = saveParamPexprs ps from rfl]
    exact hnv
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold saveRedex
  cases ctx <;>
    (dsimp only [one_step0]
     rw [show is_irreducible (Expr [] (Esave sb ps body)) = false from rfl]
     dsimp only [get_loc]
     rw [hnv']
     simp only [Bool.false_eq_true, if_false]
     dsimp only [dischargeStep]
     rw [stExceptUndef_bind_apply, stExceptUndef_bind_apply,
       mapM_save_bridge (tds := tds) (σ := σ) (file := file)
         (fun pe => stExceptUndef_bind
           (E.eval_pexpr20 (a := core_run_state) tds th ext σ file pe)
           (fun x => match x with
             | Sum.inl pe' => stExceptUndef_return pe'
             | Sum.inr cval => stExceptUndef_return (mk_value_pe cval)))
         (fun _ _ => rfl) _ ?_ ps hv hdep rs] <;>
       first
         | rfl
         | (intro p rs'
            rfl))

/-- MEMOP-OPERAND EVALUATION, context undisturbed, DISCHARGED
    (one_step0's Ememop EVAL arm + step_ctx's EVAL wrap + the
    liftCore_run protocol): ONE engine step mapping `eval_pexpr1`
    over the operands (one full evaluator iteration each —
    `eval1_bridge`/`mapM_eval1_bridge`), run state VERBATIM,
    env/memory verbatim; the successor rebuilds the value-operand
    memop redex in context. -/
theorem stepDischarge_memop_eval {e : CoreExpr} {ctx : context}
    {mop : memop} {pe1 pe2 : generic_pexpr Unit sym} {v1 v2 : value}
    (hd : Decomp e ctx (memopRedex mop [pe1, pe2]))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (hd1 : peDepth pe1 ≤ lemDefaultFuel)
    (hd2 : peDepth pe2 ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hv1 : evalPexpr tds ext th.env pe1 = some v1)
    (hv2 : evalPexpr tds ext th.env pe2 = some v2)
    (aid : Nat) (rs : core_run_state) :
    (step_ctx tds σ file ext tid (parent, th)).map
        (dischargeStep tds aid rs σ) =
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
    (hd : Decomp e ctx (storeOpRedex loc ann ty pe2 pe3 mo))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs [pe2, pe3] = none)
    (hp2 : PePure pe2) (hp3 : PePure pe3)
    (hd2 : peDepth pe2 ≤ lemDefaultFuel)
    (hd3 : peDepth pe3 ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hv2 : evalPexpr tds ext th.env pe2 = some (Vobject (OVpointer pv)))
    (hv3 : evalPexpr tds ext th.env pe3 = some cv)
    (aid : Nat) (rs : core_run_state) :
    (step_ctx tds σ file ext tid (parent, th)).map
        (dischargeStep tds aid rs σ) =
      [.next { th with arena := apply_ctx ctx (storeRedex loc ann false ty
        pv cv mo) } σ] := by
  have hget : get_ctx th.arena = [(ctx, storeOpRedex loc ann ty pe2 pe3 mo)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold storeOpRedex
  rw [valueFromPexprs_pair] at hnv
  cases hp2 <;> cases hp3 <;>
    try (rw [valueFromPexpr_val, valueFromPexpr_val] at hnv; cases hnv)
  all_goals try (obtain rfl := Option.some.inj ((evalPexpr_val _ _ _ _ _).symm.trans hv2))
  all_goals
    cases ctx <;>
      (dsimp only [get_loc]
       dsimp only [step_action]
       dsimp only [act_valueFromPexpr, valueFromPexpr]
       dsimp only [dischargeStep]
       rw [full_eval_bridge (v := Vctype ty) rfl (peDepth_val_le _ _) σ file,
         full_eval_bridge hv2 hd2 σ file,
         full_eval_bridge hv3 hd3 σ file]
       dsimp only [stExceptUndef_bind, stExceptUndef_return, stExpect_return,
         return1, except_return]
       rfl)

/-- Alloc ACTION_EVAL, context undisturbed, DISCHARGED (kill/free arc K3
    — step_action's Alloc0 `_, _` arm + process_action's ACTION_EVAL
    wrap): ONE engine step big-step-evaluating the two operands
    (alignment first; an already-evaluated operand re-evaluates to
    itself) through the certified evaluator, run state VERBATIM (∀ rs),
    env/memory verbatim; the successor rebuilds the CANONICAL ALLOC
    REDEX in context. -/
theorem stepDischarge_alloc_eval {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0}
    {align size : CerbMem.IntegerValue}
    (hd : Decomp e ctx (allocOpRedex loc ann pe1 pe2 pref))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (hp1 : PePure pe1) (hp2 : PePure pe2)
    (hd1 : peDepth pe1 ≤ lemDefaultFuel)
    (hd2 : peDepth pe2 ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hv1 : evalPexpr tds ext th.env pe1 = some (Vobject (OVinteger align)))
    (hv2 : evalPexpr tds ext th.env pe2 = some (Vobject (OVinteger size)))
    (aid : Nat) (rs : core_run_state) :
    (step_ctx tds σ file ext tid (parent, th)).map
        (dischargeStep tds aid rs σ) =
      [.next { th with arena := apply_ctx ctx (allocRedex loc ann align size pref) } σ] := by
  have hget : get_ctx th.arena = [(ctx, allocOpRedex loc ann pe1 pe2 pref)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold allocOpRedex
  rw [valueFromPexprs_pair] at hnv
  cases hp1 <;> cases hp2 <;>
    try (rw [valueFromPexpr_val, valueFromPexpr_val] at hnv; cases hnv)
  all_goals try (obtain rfl := Option.some.inj ((evalPexpr_val _ _ _ _ _).symm.trans hv1))
  all_goals try (obtain rfl := Option.some.inj ((evalPexpr_val _ _ _ _ _).symm.trans hv2))
  all_goals
    cases ctx <;>
      (dsimp only [get_loc]
       dsimp only [step_action]
       dsimp only [act_valueFromPexpr, valueFromPexpr]
       dsimp only [dischargeStep]
       rw [full_eval_bridge hv1 hd1 σ file, full_eval_bridge hv2 hd2 σ file]
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
    (hd : Decomp e ctx
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

/-! ### The plain-symbol binder's head grammar (fragment closure, 2026-09-02)

`BareHead e1` is the set of head shapes admitted under the plain-symbol
binder `lets x = e1 in e2` (`Frag.sseq_sym`): the shapes whose every
mirror successor is again a `BareHead` and whose terminal value is a
BARE value — never `{A}v`. The engine binds a plain symbol at an
annotated value too (one_step0's Esseq Eannot arm, "reduction:
LETS-ANNOT", `step_ctx_beta_sym_annot` in Round.lean), and the mirror
has no rule for that beta (`Step.sseq_sym_pure` only — the recorded
divergence in Step.lean). Rather than add the rule, the fragment is
declared as exactly what the mirror covers ([USER 2026-09-02], "fail-
closed if we've achieved complete coverage" — DECISIONS.md, fragment-
closure ruling): the binder's head is restricted to the producers of
bare values the fragment's programs actually bind — a literal value
(`val_pure`), `create` (its continuation is `mk_value_e`, a bare
pointer value — step_action's Create arm), and the pointer-equality
memop at values or at operands to evaluate (the memop protocol's
`mk_pure_e (mk_value_pe cval)`, a bare boolean). Closure under the
mirror step is `BareHead.step`; the annotated value is not a
`BareHead` (`BareHead.not_annot`), so the LETS-ANNOT beta at the
symbol binder is unreachable in `Frag`. -/
inductive BareHead : CoreExpr → Prop where
  | val_pure (v : value) : BareHead (Expr [] (Epure (Pexpr [] () (PEval v))))
  | create {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {align : CerbMem.IntegerValue} {ty : ctype} {pref : prefix0} :
      BareHead (createRedex loc ann align ty pref)
  | memop_vals (v1 v2 : value) : BareHead (memopPtrEqVals v1 v2)
  | memop_op {pe1 pe2 : generic_pexpr Unit sym}
      (hnv : valueFromPexprs [pe1, pe2] = none)
      (hp1 : PePure pe1) (hp2 : PePure pe2)
      (hd1 : peDepth pe1 ≤ lemDefaultFuel)
      (hd2 : peDepth pe2 ≤ lemDefaultFuel) :
      BareHead (memopRedex PtrEq [pe1, pe2])
  /-- `alloc` (kill/free arc K3): its continuation is `mk_value_e`, a bare
      pointer value — step_action's Alloc0 arm; the program `lets p =
      alloc(al, n) in …` binds it. -/
  | alloc {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {align size : CerbMem.IntegerValue} {pref : prefix0} :
      BareHead (allocRedex loc ann align size pref)
  /-- `alloc` at operands to evaluate (its successor is the alloc at values). -/
  | alloc_op {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0}
      (hnv : valueFromPexprs [pe1, pe2] = none)
      (hp1 : PePure pe1) (hp2 : PePure pe2)
      (hd1 : peDepth pe1 ≤ lemDefaultFuel)
      (hd2 : peDepth pe2 ≤ lemDefaultFuel) :
      BareHead (allocOpRedex loc ann pe1 pe2 pref)

/-- An annotated value is never a `BareHead` (the LETS-ANNOT beta at
    the symbol binder is unreachable in the fragment). -/
theorem BareHead.not_annot {ds : List dyn_annotation} {v : value}
    (h : BareHead (ofVal (.annot ds v))) : False := by
  generalize he : ofVal (.annot ds v) = e at h
  cases h with
  | val_pure v' => cases he
  | create => simp [createRedex, ofVal] at he
  | memop_vals v1 v2 => simp [memopPtrEqVals, memopRedex, ofVal] at he
  | memop_op hnv hp1 hp2 hd1 hd2 => simp [memopRedex, ofVal] at he
  | alloc => simp [allocRedex, ofVal] at he
  | alloc_op hnv hp1 hp2 hd1 hd2 => simp [allocOpRedex, ofVal] at he

/-- A non-value `BareHead` is itself a root redex. -/
theorem BareHead.redex {e : CoreExpr} (h : BareHead e) (hnv : toVal e = none) :
    Redex e := by
  cases h with
  | val_pure v =>
    rw [show toVal (Expr ([] : List _root_.annot) (Epure (Pexpr [] () (PEval v)))) =
      some (.pure v) from rfl] at hnv
    cases hnv
  | create => exact .create
  | memop_vals v1 v2 => exact .memop _ _
  | memop_op hnv hp1 hp2 hd1 hd2 => exact .memop _ _
  | alloc => exact .alloc
  | alloc_op hnvA hp1 hp2 hd1 hd2 => exact .alloc_op _ _ _ hnvA

/-- Closure under the mirror step: a `BareHead` steps only to a
    `BareHead` (create → its bare pointer value; memop-operand
    evaluation → the memop at values; the memop at values → its bare
    boolean). -/
theorem BareHead.step {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    (h : BareHead e) (hs : Step M (e, ρ, ctl, σ) (e', ρ', ctl, σ')) : BareHead e' := by
  cases h with
  | val_pure v => exact (Step.pure_val_elim hs rfl).elim
  | create =>
    obtain ⟨pv, σ'', hmem, hout⟩ := hs.create_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact .val_pure _
  | memop_vals v1 v2 =>
    obtain ⟨pv1, pv2, b, σ'', -, -, -, hout⟩ := hs.memop_vals_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact .val_pure _
  | memop_op hnv hp1 hp2 hd1 hd2 =>
    obtain ⟨v1, v2, hv1, hv2, hout⟩ := hs.memop_op_inv hnv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact .memop_vals v1 v2
  | alloc =>
    obtain ⟨pv, σ'', hmem, hout⟩ := hs.alloc_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact .val_pure _
  | alloc_op hnv hp1 hp2 hd1 hd2 =>
    obtain ⟨al, sz, hv1, hv2, hout⟩ := hs.alloc_op_inv hnv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact .alloc

/-! ### The fragment `Frag` and the step-match

`Frag` is the per-construct authority of every adequacy theorem: the
straight-line shapes plus Esave, Eif (with the guard's static
evaluator-fuel bound), Erun (with the arguments'), value-scrutinee
Ecase (`Frag.case_value` below, with explicit branch-closure and
branch-size premises) and wildcard Ewseq. Registered continuations
enter through the SIDE hypothesis `hQf` (the label map's own
membership), which breaks the circularity a label-indexed fragment
would have.

The certification shape is MATCH-GIVEN-STEP (`engine_step_matchU`):
wherever the MIRROR steps, the engine's behaviour is the singleton
discharged match. That suffices for the WP-driven adequacy (NotStuck
supplies a mirror step at every reachable configuration) and avoids
threading well-formedness through the engine: the panic-exclusion
facts live as RULE PREMISES, extracted by the inversions from the
given step — the WP is the well-formedness oracle.

THE SECOND FUEL BOUND, AND THE OPERAND GRAMMAR. The engine's
pure-expression evaluator is fuelled at `lemDefaultFuel` too (the
pure-evaluator bridge above), so every constructor that evaluates a
pure operand carries `peDepth pe ≤ lemDefaultFuel` per operand (`if_`,
`run`, `save`, `load_op`, `memop_op`, `store_op`), and EVERY such
constructor restricts its operands to the covered sub-grammar `PePure`
(values, symbols, the eight mirrored binops, array shifts) — the mirror
evaluator's exact domain (fragment closure, 2026-09-02: before it,
`if_`/`run`/`save` took any operand and `PePure` admitted every binop).
Both are `rfl` for authored programs (`peDepth_sym_le`, `peDepth_val_le`,
`PePure.of_isPePure rfl`). Where the mirror evaluator answers `none` on
a `PePure` operand, the engine's outcome is classified (EvalClass.lean,
Round.lean): a proved engine KILL where the classifier `evalClass`
rejects the operand, the residual `OpenRound.eval_uncovered` where the
classifier leaves it uncovered — decided at the first uncovered LEAF,
so the whole operand's outcome there is NOT characterized (the residual
is a superset of the engine-accepted shapes; EvalClass.lean header).

THE FRAGMENT IS ANNOTATION-FREE: every constructor below, and every
redex spelling it
ranges over (`storeRedex`/`loadRedex`/`createRedex` above,
`loadOpRedex`/`storeOpRedex`/`killRedex`/`killOpRedex`/`memopRedex`/
`pureRedex` in Step.lean,
`saveRedex`/`ifRedex`/`runRedex`/`caseRedex` above, and the
`Esseq`/`Ewseq`/`Eannot` constructors), is stated at the empty static
annotation list `Expr []` — so every node of a fragment program is
annotation-free. The forcing fact: in the general arm of the engine's
`step_ctx` (Core_reduction.lean, the `Expr e_annots expr_` match),
`get_loc e_annots` reads a source location from the redex node's
annotations and, unless it is a library location, rewrites the
thread's `current_loc`; this package keeps `currentLoc` in the
immutable `MachineCtx`, and `engine_step_matchU` equates the engine's
successor thread with `M.thread e' ρ' ctl`, whose `current_loc` is
`M.currentLoc`. A located node would falsify that equation. Located
Core — in particular every Core program the C elaborator produces — is
therefore outside `Frag`. The mover: make `current_loc` live state,
part of the runtime tuple as `env` is. -/

inductive Frag : CoreExpr → Prop where
  | val_pure (v : value) : Frag (Expr [] (Epure (Pexpr [] () (PEval v))))
  /-- Store at canonical evaluated operands, at EITHER locking mode:
      `lk` is unconstrained, so the fragment ADMITS the locking store
      `Store0 true …`, whose engine success flips the allocation's
      `isReadonly` (CerbMem.lean:1687-1693). No rule of this package
      covers `lk = true` (`storeExpr` is `Store0 false`; `store_atomic`,
      `wps_store`, `wpt_store` and the subrange rules are stated at it),
      so no derivation traverses a locking store and the coupling is
      never asserted across one; any rule "over any live cell" that
      involves a store fixes `lk = false` (K1 audit N-2). The kill rules
      (K2) involve no store, so `lk` does not arise there. -/
  | store {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
      {ty : ctype} {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order} :
      Frag (storeRedex loc ann lk ty pv cv mo)
  | load {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
      {pv : CerbMem.PointerValue} {mo : memory_order} :
      Frag (loadRedex loc ann ty pv mo)
  | create {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {align : CerbMem.IntegerValue} {ty : ctype} {pref : prefix0} :
      Frag (createRedex loc ann align ty pref)
  /-- THE KILL at the canonical evaluated pointer operand, EITHER KIND
      (kill/free arc K2 static, K3 dynamic): `kill(static ty, p)` — C's
      end of automatic storage — and `free(p)` (`Kill Dynamic0`, the
      pair of `Alloc0`). K2 carried `is_dynamic kind = false` here; K3
      LIFTED it (a strict generalization of the fragment: the mirror
      `Step.kill` was generic in the kind from the start, and
      `complete_kill` classifies every kind). The engine DISCARDS the
      `Static0 ty` payload — only `is_dynamic kind` reaches `killM`
      (Core_reduction.lean:424) — so no relation between the kill type
      and the allocation's type is a premise anywhere. The RULES are
      kind-specific: `kill_atomic` (static, over the OBJECT bundle
      `pointsToCell`) and `free_atomic` (dynamic, over the REGION bundle
      `regionOwn`); the engine-ACCEPTED cross case `kill(static ty, p)`
      at a live REGION (the dynamic check is short-circuited at
      `isDynamic = false`, CerbMem.lean:1573) is in the fragment and
      mirrored, and has NO rule — the K2 range audit's N-2, decided at
      K3 (README "Scope, exactly"). -/
  | kill {loc : CerbLocation.Loc} {ann : core_run_annotation} {kind : kill_kind}
      {pv : CerbMem.PointerValue} :
      Frag (killRedex loc ann kind pv)
  /-- The kill of either kind at an operand in the covered grammar
      `PePure`, within the evaluator's fuel (the ACTION_EVAL form). -/
  | kill_op {loc : CerbLocation.Loc} {ann : core_run_annotation} {kind : kill_kind}
      {pe : generic_pexpr Unit sym}
      (hnv : valueFromPexpr pe = none) (hp : PePure pe)
      (hdp : peDepth pe ≤ lemDefaultFuel) :
      Frag (killOpRedex loc ann kind pe)
  /-- DYNAMIC ALLOCATION at canonical evaluated INTEGER operands
      (kill/free arc K3): `alloc(al, n)` — Core's `Alloc0`, C's `malloc`
      (the region is untyped, of raw size `n.toNat` — ZERO admitted —
      and dynamic). -/
  | alloc {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {align size : CerbMem.IntegerValue} {pref : prefix0} :
      Frag (allocRedex loc ann align size pref)
  /-- Dynamic allocation at operands in the covered grammar `PePure`
      that are not all values, within the evaluator's fuel (the
      ACTION_EVAL form; mixed shapes included, as `store_op`). -/
  | alloc_op {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0}
      (hnv : valueFromPexprs [pe1, pe2] = none)
      (hp1 : PePure pe1) (hp2 : PePure pe2)
      (hd1 : peDepth pe1 ≤ lemDefaultFuel)
      (hd2 : peDepth pe2 ≤ lemDefaultFuel) :
      Frag (allocOpRedex loc ann pe1 pe2 pref)
  | sseq {pa : List annot} {bty : core_base_type} {e1 e2 : CoreExpr} :
      Frag e1 → Frag e2 →
      Frag (Expr [] (Esseq (Pattern pa (CaseBase (none, bty))) e1 e2))
  | annot {ds : List dyn_annotation} {b : CoreExpr} :
      Frag b → Frag (Expr [] (Eannot ds b))
  /-- Esave at ANY initializers within the evaluator's fuel (the
      engine's TAU arm at value initializers, its EVAL arm otherwise —
      `Step.save`/`Step.save_eval`). `hd` is the same static
      evaluator-fuel bound `if_`/`run` carry for their pure operands;
      literal initializers satisfy it trivially
      (`saveParams_depth_of_vals`). -/
  | save {sb : sym × core_base_type}
      {ps : List (sym × ((core_base_type ×
        Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
      {body : CoreExpr}
      (hp : ∀ pe ∈ saveParamPexprs ps, PePure pe)
      (hd : ∀ pe ∈ saveParamPexprs ps, peDepth pe ≤ lemDefaultFuel) :
      Frag body → Frag (saveRedex sb ps body)
  /-- Eif at a guard in the covered operand grammar `PePure`, within the
      evaluator's fuel (fragment closure, 2026-09-02: the operand grammar
      of every evaluating constructor is `PePure` — the mirror evaluator's
      exact domain — so an operand the mirror cannot evaluate is
      classified in the engine, `complete_if`). -/
  | if_ {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
      (hpg : PePure g) (hdg : peDepth g ≤ lemDefaultFuel) :
      Frag e2 → Frag e3 → Frag (ifRedex g e2 e3)
  /-- Erun at arguments in `PePure`, within the evaluator's fuel. -/
  | run {ra : core_run_annotation} {l : sym}
      {pes : List (generic_pexpr Unit sym)}
      (hpes : ∀ pe ∈ pes, PePure pe)
      (hdep : ∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel) :
      Frag (runRedex ra l pes)
  | sseq_spec {pa pb : List annot} {x : sym} {bty : core_base_type}
      {e1 e2 : CoreExpr} :
      Frag e1 → Frag e2 →
      Frag (Expr [] (Esseq (specPat pa pb x bty) e1 e2))
  | pure_sym {pb : List annot} {x : sym} :
      Frag (pureRedex (Pexpr pb () (PEsym x)))
  | load_op {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {ty : ctype} {pe2 : generic_pexpr Unit sym} {mo : memory_order}
      (hnv2 : valueFromPexpr pe2 = none) (hp2 : PePure pe2)
      (hd2 : peDepth pe2 ≤ lemDefaultFuel) :
      Frag (loadOpRedex loc ann ty pe2 mo)
  /-- Strong sequencing at the plain-symbol binder, the head restricted
      to the bare-value producers `BareHead` (fragment closure,
      2026-09-02: the LETS-ANNOT beta at this binder has no mirror rule
      and is unreachable from these heads — `BareHead.step`,
      `BareHead.not_annot`). -/
  | sseq_sym {pa : List annot} {x : sym} {bty : core_base_type}
      {e1 e2 : CoreExpr} (hb : BareHead e1) :
      Frag e1 → Frag e2 →
      Frag (Expr [] (Esseq (symPat pa x bty) e1 e2))
  | memop_vals (v1 v2 : value) :
      Frag (memopPtrEqVals v1 v2)
  | memop_op {pe1 pe2 : generic_pexpr Unit sym}
      (hnv : valueFromPexprs [pe1, pe2] = none)
      (hp1 : PePure pe1) (hp2 : PePure pe2)
      (hd1 : peDepth pe1 ≤ lemDefaultFuel)
      (hd2 : peDepth pe2 ≤ lemDefaultFuel) :
      Frag (memopRedex PtrEq [pe1, pe2])
  | store_op {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {ty : ctype} {pe2 pe3 : generic_pexpr Unit sym} {mo : memory_order}
      (hnv : valueFromPexprs [pe2, pe3] = none)
      (hp2 : PePure pe2) (hp3 : PePure pe3)
      (hd2 : peDepth pe2 ≤ lemDefaultFuel)
      (hd3 : peDepth pe3 ≤ lemDefaultFuel) :
      Frag (storeOpRedex loc ann ty pe2 pe3 mo)
  /-- Value-scrutinee Ecase, with the selected branch's fragment
      membership (`hbr`) and size bound (`hbsz`) as explicit premises.
      `hbsz` is carried, not proved: the equation that would discharge
      it is `esize (subst_sym_expr x v e) = esize e` (with its mutual
      twin for `esizeAlts`) — true because `esize` inspects only
      expression constructors and `subst_sym_expr` substitutes only
      into pure expressions — but the engine's `subst_sym_expr` is
      `subst_sym_expr_lemFuel lemDefaultFuel`, a fuel-indexed recursion
      over the whole generated Core AST, so the proof is a fuel-indexed
      induction over that mutual recursion; registered (README,
      "Registered divergences and limitations"). For authored programs
      both premises are `rfl` (CaseExhibit.lean, `caseProg_select`). -/
  | case_value {b : List annot} {cval : value}
      {pats : List (pattern × CoreExpr)}
      (hbr : ∀ e', select_case subst_sym_expr cval pats = some e' → Frag e')
      (hbsz : ∀ e', select_case subst_sym_expr cval pats = some e' →
        esize e' ≤ esize (caseRedex (Pexpr b () (PEval cval)) pats)) :
      Frag (caseRedex (Pexpr b () (PEval cval)) pats)
  /-- Weak sequencing at the wildcard pattern (the `sseq` clone). -/
  | wseq {pa : List annot} {bty : core_base_type} {e1 e2 : CoreExpr} :
      Frag e1 → Frag e2 →
      Frag (Expr [] (Ewseq (Pattern pa (CaseBase (none, bty))) e1 e2))
  /-- THE PROCEDURE CALL (calls arc C2): `Eproc` at a Core identifier,
      arguments in the covered grammar `PePure` within the evaluator's
      fuel (the engine evaluates ALL of them by `full_eval_pexpr'` in the
      PCALL round, Core_reduction.lean:484 col 18133). Any `f`: the
      unknown procedure and the arity mismatch are the engine's two
      `Illformed_program` KILLS, classified in Round.lean (`complete_call`),
      not narrowed here. The callee's BODY is not a `Frag` premise — `Frag`
      is a predicate on the expression, the body lives in the FILE — so
      adequacy through a call carries `MachineCtx.FragProcs` (Adequacy.lean:
      every procedure the file declares has a `Frag` body within the
      potential bound and `Frag` label bodies), the twin of `hQf`/`hQpot`. -/
  | call {ra : core_run_annotation} {f : sym} {pes : List (generic_pexpr Unit sym)}
      (hpes : ∀ pe ∈ pes, PePure pe)
      (hdep : ∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel) :
      Frag (callRedex ra f pes)

theorem frag_ofVal (w : SpikeVal) : Frag (ofVal w) := by
  cases w with
  | pure v => exact .val_pure v
  | annot ds v => exact .annot (.val_pure v)

/-- Every `BareHead` is in the fragment. -/
theorem BareHead.frag {e : CoreExpr} (h : BareHead e) : Frag e := by
  cases h with
  | val_pure v => exact .val_pure v
  | create => exact .create
  | memop_vals v1 v2 => exact .memop_vals v1 v2
  | memop_op hnv hp1 hp2 hd1 hd2 => exact .memop_op hnv hp1 hp2 hd1 hd2
  | alloc => exact .alloc
  | alloc_op hnv hp1 hp2 hd1 hd2 => exact .alloc_op hnv hp1 hp2 hd1 hd2

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

/-- Every non-value Frag configuration decomposes (extended
    roots). -/
theorem Frag.decomp {e : CoreExpr} (hf : Frag e) (hnv : toVal e = none) :
    ∃ ctx r, Decomp e ctx r ∧ Frag r := by
  induction hf with
  | val_pure v =>
    rw [show toVal (Expr ([] : List _root_.annot) (Epure (Pexpr [] () (PEval v)))) =
      some (.pure v) from rfl] at hnv
    cases hnv
  | store => exact ⟨_, _, Decomp.root (.store), .store⟩
  | load => exact ⟨_, _, Decomp.root (.load), .load⟩
  | create => exact ⟨_, _, Decomp.root (.create), .create⟩
  | kill => exact ⟨_, _, Decomp.root (.kill), .kill⟩
  | kill_op hnvK hpK hdK =>
    exact ⟨_, _, Decomp.root (.kill_op _ _ _ hnvK), .kill_op hnvK hpK hdK⟩
  | alloc => exact ⟨_, _, Decomp.root (.alloc), .alloc⟩
  | alloc_op hnvA hp1 hp2 hd1 hd2 =>
    exact ⟨_, _, Decomp.root (.alloc_op _ _ _ hnvA), .alloc_op hnvA hp1 hp2 hd1 hd2⟩
  | call hpes hdep => exact ⟨_, _, Decomp.root (.call _ _ _), .call hpes hdep⟩
  | @sseq pa bty e1 e2 hf1 hf2 ih1 ih2 =>
    cases hv1 : toVal e1 with
    | some w =>
      have he1 := ofVal_of_toVal hv1
      subst he1
      cases w with
      | pure v => exact ⟨_, _, Decomp.root (.beta_pure),
          .sseq (frag_ofVal (.pure v)) hf2⟩
      | annot ds v => exact ⟨_, _, Decomp.root (.beta_annot),
          .sseq (frag_ofVal (.annot ds v)) hf2⟩
    | none =>
      obtain ⟨ctx, r, hd, hfr⟩ := ih1 hv1
      exact ⟨_, _, Decomp.sseq hd, hfr⟩
  | @wseq pa bty e1 e2 hf1 hf2 ih1 ih2 =>
    cases hv1 : toVal e1 with
    | some w =>
      have he1 := ofVal_of_toVal hv1
      subst he1
      cases w with
      | pure v => exact ⟨_, _, Decomp.root (.wbeta_pure),
          .wseq (frag_ofVal (.pure v)) hf2⟩
      | annot ds v => exact ⟨_, _, Decomp.root (.wbeta_annot),
          .wseq (frag_ofVal (.annot ds v)) hf2⟩
    | none =>
      obtain ⟨ctx, r, hd, hfr⟩ := ih1 hv1
      exact ⟨_, _, Decomp.wseq hd, hfr⟩
  | @annot ds b hfb ihb =>
    by_cases hr : annotRooted b = true
    · cases hfb with
      | val_pure v => simp [annotRooted] at hr
      | store => simp [annotRooted, storeRedex] at hr
      | load => simp [annotRooted, loadRedex] at hr
      | create => simp [annotRooted, createRedex] at hr
      | sseq hf1 hf2 => simp [annotRooted] at hr
      | wseq hf1 hf2 => simp [annotRooted] at hr
      | sseq_spec hf1 hf2 => simp [annotRooted] at hr
      | save hp hd hb => simp [annotRooted, saveRedex] at hr
      | if_ hpg hdg hf2 hf3 => simp [annotRooted, ifRedex] at hr
      | run hpes hdep => simp [annotRooted, runRedex] at hr
      | pure_sym => simp [annotRooted, pureRedex] at hr
      | load_op hnv2 hp2 hd2 => simp [annotRooted, loadOpRedex] at hr
      | sseq_sym hb hf1 hf2 => simp [annotRooted] at hr
      | memop_vals v1 v2 => simp [annotRooted, memopPtrEqVals, memopRedex] at hr
      | memop_op hnv hp1 hp2 hpd1 hpd2 => simp [annotRooted, memopRedex] at hr
      | store_op hnv hp2 hp3 hpd2 hpd3 =>
        simp [annotRooted, storeOpRedex] at hr
      | case_value hbr hbsz => simp [annotRooted, caseRedex] at hr
      | kill => simp [annotRooted, killRedex] at hr
      | kill_op hnvK hpK hdK => simp [annotRooted, killOpRedex] at hr
      | alloc => simp [annotRooted, allocRedex] at hr
      | alloc_op hnvA hp1 hp2 hd1 hd2 => simp [annotRooted, allocOpRedex] at hr
      | call hpes hdep => simp [annotRooted, callRedex] at hr
      | @annot ds2 c hfc =>
        have hwit : Frag (Expr ([] : List _root_.annot)
            (Eannot ds (Expr [] (Eannot ds2 c)))) := .annot (.annot hfc)
        cases hfc with
        | val_pure v => exact ⟨_, _, Decomp.root (.merge rfl), hwit⟩
        | store => exact ⟨_, _, Decomp.root (.merge rfl), hwit⟩
        | load => exact ⟨_, _, Decomp.root (.merge rfl), hwit⟩
        | create => exact ⟨_, _, Decomp.root (.merge rfl), hwit⟩
        | sseq hf1 hf2 => exact ⟨_, _, Decomp.root (.merge rfl), hwit⟩
        | wseq hf1 hf2 => exact ⟨_, _, Decomp.root (.merge rfl), hwit⟩
        | sseq_spec hf1 hf2 =>
          exact ⟨_, _, Decomp.root (.merge rfl), hwit⟩
        | annot hfc' => exact ⟨_, _, Decomp.root (.merge rfl), hwit⟩
        | save hp hd hb => exact ⟨_, _, Decomp.root (.merge rfl), hwit⟩
        | if_ hpg hdg hf2 hf3 => exact ⟨_, _, Decomp.root (.merge rfl), hwit⟩
        | run hpes hdep => exact ⟨_, _, Decomp.root (.merge rfl), hwit⟩
        | pure_sym =>
          exact ⟨_, _, Decomp.root (.merge rfl), hwit⟩
        | load_op hnv2 hp2 hd2 =>
          exact ⟨_, _, Decomp.root (.merge rfl), hwit⟩
        | sseq_sym hb hf1 hf2 =>
          exact ⟨_, _, Decomp.root (.merge rfl), hwit⟩
        | memop_vals v1 v2 =>
          exact ⟨_, _, Decomp.root (.merge rfl), hwit⟩
        | memop_op hnv hp1 hp2 hpd1 hpd2 =>
          exact ⟨_, _, Decomp.root (.merge rfl), hwit⟩
        | store_op hnv hp2 hp3 hpd2 hpd3 =>
          exact ⟨_, _, Decomp.root (.merge rfl), hwit⟩
        | case_value hbr hbsz =>
          exact ⟨_, _, Decomp.root (.merge rfl), hwit⟩
        | kill => exact ⟨_, _, Decomp.root (.merge rfl), hwit⟩
        | kill_op hnvK hpK hdK =>
          exact ⟨_, _, Decomp.root (.merge rfl), hwit⟩
        | alloc => exact ⟨_, _, Decomp.root (.merge rfl), hwit⟩
        | alloc_op hnvA hp1 hp2 hd1 hd2 =>
          exact ⟨_, _, Decomp.root (.merge rfl), hwit⟩
        | call hpes hdep => exact ⟨_, _, Decomp.root (.merge rfl), hwit⟩
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
        | store => exact ⟨_, _, Decomp.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | load => exact ⟨_, _, Decomp.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | create => exact ⟨_, _, Decomp.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | sseq hf1 hf2 => exact ⟨_, _, Decomp.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | wseq hf1 hf2 =>
          exact ⟨_, _, Decomp.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | sseq_spec hf1 hf2 =>
          exact ⟨_, _, Decomp.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | save hp' hd' hb => exact ⟨_, _, Decomp.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | if_ hpg hdg hf2 hf3 => exact ⟨_, _, Decomp.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | run hpes hdep => exact ⟨_, _, Decomp.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | annot hfc => simp [annotRooted] at hr'
        | pure_sym =>
          exact ⟨_, _, Decomp.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | load_op hnv2 hp2 hd2 =>
          exact ⟨_, _, Decomp.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | sseq_sym hb hf1 hf2 =>
          exact ⟨_, _, Decomp.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | memop_vals v1 v2 =>
          exact ⟨_, _, Decomp.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | memop_op hnv hp1 hp2 hpd1 hpd2 =>
          exact ⟨_, _, Decomp.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | store_op hnv hp2 hp3 hpd2 hpd3 =>
          exact ⟨_, _, Decomp.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | case_value hbr hbsz =>
          exact ⟨_, _, Decomp.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | kill => exact ⟨_, _, Decomp.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | kill_op hnvK hpK hdK =>
          exact ⟨_, _, Decomp.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | alloc => exact ⟨_, _, Decomp.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | alloc_op hnvA hp1 hp2 hd1 hd2 =>
          exact ⟨_, _, Decomp.annot hr' rfl (fun n => rfl) hd, hfr⟩
        | call hpes hdep => exact ⟨_, _, Decomp.annot hr' rfl (fun n => rfl) hd, hfr⟩
  | save hp hd hb ih => exact ⟨_, _, Decomp.root (.save _ _ _), .save hp hd hb⟩
  | if_ hpg hdg hf2 hf3 ih2 ih3 =>
    exact ⟨_, _, Decomp.root (.if_ _ _ _), .if_ hpg hdg hf2 hf3⟩
  | run hpes hdep => exact ⟨_, _, Decomp.root (.run _ _ _), .run hpes hdep⟩
  | @sseq_spec pa pb x bty e1 e2 hf1 hf2 ih1 ih2 =>
    cases hv1 : toVal e1 with
    | some w =>
      have he1 := ofVal_of_toVal hv1
      subst he1
      exact ⟨_, _, Decomp.root .beta_spec, .sseq_spec (frag_ofVal w) hf2⟩
    | none =>
      obtain ⟨ctx, r, hd, hfr⟩ := ih1 hv1
      exact ⟨_, _, Decomp.sseq_spec hd, hfr⟩
  | pure_sym =>
    exact ⟨_, _, Decomp.root (.pure_e rfl), .pure_sym⟩
  | load_op hnv2 hp2 hd2 =>
    exact ⟨_, _, Decomp.root (.load_op _ _ _ _ hnv2),
      .load_op hnv2 hp2 hd2⟩
  | @sseq_sym pa x bty e1 e2 hb hf1 hf2 ih1 ih2 =>
    cases hv1 : toVal e1 with
    | some w =>
      have he1 := ofVal_of_toVal hv1
      subst he1
      cases w with
      | pure v =>
        exact ⟨_, _, Decomp.root .beta_sym, .sseq_sym hb (frag_ofVal (.pure v)) hf2⟩
      | annot ds v => exact hb.not_annot.elim
    | none =>
      obtain ⟨ctx, r, hd, hfr⟩ := ih1 hv1
      exact ⟨_, _, Decomp.sseq_sym hd, hfr⟩
  | memop_vals v1 v2 =>
    exact ⟨_, _, Decomp.root (.memop _ _), .memop_vals v1 v2⟩
  | memop_op hnvF hp1 hp2 hpd1 hpd2 =>
    exact ⟨_, _, Decomp.root (.memop _ _), .memop_op hnvF hp1 hp2 hpd1 hpd2⟩
  | store_op hnvF hp2 hp3 hpd2 hpd3 =>
    exact ⟨_, _, Decomp.root (.store_op _ _ _ _ hnvF),
      .store_op hnvF hp2 hp3 hpd2 hpd3⟩
  | case_value hbr hbsz =>
    exact ⟨_, _, Decomp.root (.case_ _ _), .case_value hbr hbsz⟩

/-! S4 RETIREMENT NOTE: S3's `Decomp.toDecomp` (an extended
    decomposition holding a phase-1 redex is a phase-1
    decomposition) is FALSIFIED by the S4 `sseq_spec` frame (a
    phase-1 redex can now sit under a Specified-binder frame, which
    `Decomp` cannot represent). Its one consumer — the jump-profile
    step-match's reuse of the phase-1 step_ctx equations — is served
    instead by the GENERALIZED equations (their `hd` premises are
    now `Decomp`; phase-1 callers embed via `Decomp.toJ`). -/

/-! ## The value protocol at a machine context, and the frozen-profile
value corollaries -/

/-- PROGRAM-DONE at a bare value (reads exactly the two selectors of
    step_ctx's value arm: the EMPTY STACK of the live control selects
    PROGRAM-DONE over RETURN, `SeqWF`'s no-parent selects it over
    THREAD-DONE). -/
theorem outcomesU_done {M : MachineCtx} (hwf : M.SeqWF) {ctl : Ctl} (hκ : ctl.κ = [])
    (aid : Nat) (v : value) (ρ : EnvStack) (σ : Mem) :
    outcomesU M aid (ofVal (.pure v)) ρ ctl σ = [.done v] := by
  unfold outcomesU engineStepsU
  rw [hwf.parent,
    step_ctx_done v M.tagDefs σ M.file M.extern M.tid
      (M.thread (ofVal (.pure v)) ρ ctl) rfl (Ctl.toStack_of_κ_nil hκ)]
  rfl

/-- REMOVE-ANNOT at an annotated value (no context field read). -/
theorem outcomesU_remove_annot (M : MachineCtx) (aid : Nat)
    (ds : List dyn_annotation) (v : value) (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    outcomesU M aid (ofVal (.annot ds v)) ρ ctl σ =
      [.next (M.thread (ofVal (.pure v)) ρ ctl) σ] := by
  unfold outcomesU engineStepsU
  rw [step_ctx_remove_annot ds v M.tagDefs σ M.file M.extern M.tid M.parent
      (M.thread (ofVal (.annot ds v)) ρ ctl) rfl]
  rfl

/-- The extended cone is closed under Step, GIVEN the label map's
    own cone membership (`hQf` — the registered continuations are
    fragment terms; the side hypothesis breaks the circularity a
    Q-indexed cone would have). -/
theorem Frag.step {M : MachineCtx} {ctl : Ctl}
    (hQf : ∀ l params cont, lookupLabel (M.labelsAt ctl.proc) l = some (params, cont) →
      Frag cont)
    {e : CoreExpr} {ρ : EnvStack} {σ : Mem}
    {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    (hf : Frag e) (hs : Step M (e, ρ, ctl, σ) (e', ρ', ctl, σ')) : Frag e' := by
  induction hf generalizing e' ρ' σ' with
  | call hpes hdep => exact (Step.call_ne_same_ctl (callRedex?_callRedex _ _ _) hs).elim
  | val_pure v => exact (Step.pure_val_elim hs rfl).elim
  | store =>
    obtain ⟨mv, fp, σ'', hmv, hmem, hout⟩ := hs.store_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact .annot (.val_pure Vunit)
  | load =>
    obtain ⟨fp, mval, σ'', hmem, hout⟩ := hs.load_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact .annot (.val_pure _)
  | create =>
    obtain ⟨pv, σ'', hmem, hout⟩ := hs.create_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact .val_pure _
  | kill =>
    obtain ⟨σ'', hmem, hout⟩ := hs.kill_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact .val_pure _
  | kill_op hnvK hpK hdK =>
    obtain ⟨pv, -, hout⟩ := hs.kill_op_inv hnvK
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact .kill
  | alloc =>
    obtain ⟨pv, σ'', hmem, hout⟩ := hs.alloc_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact .val_pure _
  | alloc_op hnvA hp1 hp2 hd1 hd2 =>
    obtain ⟨al, sz, -, -, hout⟩ := hs.alloc_op_inv hnvA
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact .alloc
  | sseq hf1 hf2 ih1 ih2 =>
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hnv', hstep, hout⟩ |
        ⟨_, _, v, _, _, _, _, _, hout⟩ | ⟨_, _, ds', v, _, _, _, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, hpat, _, _, _⟩ |
        hcall
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
    · exact hcall.ne_same_ctl.elim
  | wseq hf1 hf2 ih1 ih2 =>
    rcases hs.wseq_inv with ⟨e1', ρ'', σ'', hnj, hnv', hstep, hout⟩ |
        ⟨_, _, v, _, _, _, _, _, hout⟩ | ⟨_, _, ds', v, _, _, _, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        hcall
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact .wseq (ih1 hstep) hf2
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
    · exact hcall.ne_same_ctl.elim
  | annot hfb ihb =>
    rcases hs.annot_inv with ⟨hg, hnj, b', ρ'', σ'', hstep, hout⟩ |
        ⟨a2, ds2, c, hb, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hg, hj, _, hl, _, hout⟩ |
        ⟨-, hcall⟩ | ⟨v', pc', κ', ha', hb', hκ', hout'⟩
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
    · exact hcall.ne_same_ctl.elim
    · obtain ⟨rfl, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by simpa [Prod.mk.injEq] using hout'
      exact .val_pure _
  | @save sb ps body hp hd hb ih =>
    rcases hs.save_inv with ⟨cvals, ev0', evs', hρeq, hvals, hout⟩ |
        ⟨cvals, hnv, hvals, hout⟩
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact hb
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact .save (saveParamsWithValues_pure ps cvals)
        (saveParamsWithValues_depth ps cvals (evalPexprs_length _ _ _ hvals)) hb
  | if_ hpg hdg hf2 hf3 ih2 ih3 =>
    rcases hs.if_inv with ⟨-, hout⟩ | ⟨-, hout⟩ <;>
      (obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout)
    · subst h1; exact hf2
    · subst h1; exact hf3
  | run hpes hdep =>
    obtain ⟨params, cont, vs, ev0', evs', hρeq, hl, hvs, hout⟩ :=
      hs.jump_inv (by rfl)
    obtain ⟨h1, -, -⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    rw [h1]
    exact hQf _ params cont hl
  | sseq_spec hf1 hf2 ih1 ih2 =>
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hnv', hstep, hout⟩ |
        ⟨_, _, v, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, ds', v, _, _, hpat, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, hpat, _, _, hout⟩ |
        hcall
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
    · exact hcall.ne_same_ctl.elim
  | sseq_sym hb hf1 hf2 ih1 ih2 =>
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hnv', hstep, hout⟩ |
        ⟨_, _, v, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, ds', v, _, _, hpat, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, hpat, _, _, hout⟩ |
        hcall
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact .sseq_sym (hb.step hstep) (ih1 hstep) hf2
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
    · exact hcall.ne_same_ctl.elim
  | memop_vals v1 v2 =>
    obtain ⟨pv1, pv2, b, σ'', -, -, -, hout⟩ := hs.memop_vals_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact .val_pure _
  | memop_op hnv hp1 hp2 hpd1 hpd2 =>
    obtain ⟨v1, v2, hv1, hv2, hout⟩ := hs.memop_op_inv hnv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact .memop_vals v1 v2
  | store_op hnv hp2 hp3 hpd2 hpd3 =>
    obtain ⟨pv, cv, hv2', hv3', hout⟩ := hs.store_op_inv hnv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact .store
  | pure_sym =>
    obtain ⟨v, -, -, hout⟩ := hs.pure_inv rfl
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact .val_pure v
  | load_op hnv2 hp2 hd2 =>
    obtain ⟨pv, -, hout⟩ := hs.load_op_inv hnv2
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact .load
  | case_value hbr hbsz =>
    obtain ⟨cval', e'', hv, hsel, hout⟩ := hs.case_inv
    obtain rfl : _ = cval' := Option.some.inj (valueFromPexpr_val _ _ ▸ hv)
    obtain ⟨h1, -, -⟩ : e' = e'' ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact hbr e' hsel

/-- Step growth on the extended cone: additive except at a jump,
    which RESETS to a registered continuation (the R3 reset — the
    J-lane accounting's second budget). -/
theorem Frag.esize_step_bound {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack}
    {ctl : Ctl} {σ : Mem} {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    (hf : Frag e) (hs : Step M (e, ρ, ctl, σ) (e', ρ', ctl, σ')) :
    esize e' ≤ esize e + 1 ∨
    ∃ l pes params cont, jumpRedex? e = some (l, pes) ∧
      lookupLabel (M.labelsAt ctl.proc) l = some (params, cont) ∧ e' = cont := by
  induction hf generalizing e' ρ' σ' with
  | call hpes hdep => exact (Step.call_ne_same_ctl (callRedex?_callRedex _ _ _) hs).elim
  | val_pure v => exact (Step.pure_val_elim hs rfl).elim
  | store =>
    obtain ⟨mv, fp, σ'', hmv, hmem, hout⟩ := hs.store_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left; simp [esize, storeRedex]
  | load =>
    obtain ⟨fp, mval, σ'', hmem, hout⟩ := hs.load_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left; simp [esize, loadRedex]
  | create =>
    obtain ⟨pv, σ'', hmem, hout⟩ := hs.create_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left; simp [esize, createRedex]
  | kill =>
    obtain ⟨σ'', hmem, hout⟩ := hs.kill_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left; simp [esize, killRedex]
  | kill_op hnvK hpK hdK =>
    obtain ⟨pv, -, hout⟩ := hs.kill_op_inv hnvK
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left; simp [esize, killOpRedex]
  | alloc =>
    obtain ⟨pv, σ'', hmem, hout⟩ := hs.alloc_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left; simp [esize, allocRedex]
  | alloc_op hnvA hp1 hp2 hd1 hd2 =>
    obtain ⟨al, sz, -, -, hout⟩ := hs.alloc_op_inv hnvA
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left; simp [esize, allocOpRedex]
  | sseq hf1 hf2 ih1 ih2 =>
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hnv', hstep, hout⟩ |
        ⟨_, _, v, _, _, _, _, _, hout⟩ | ⟨_, _, ds', v, _, _, _, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, hpat, _, _, hout⟩ |
        hcall
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
    · exact hcall.ne_same_ctl.elim
  | wseq hf1 hf2 ih1 ih2 =>
    rcases hs.wseq_inv with ⟨e1', ρ'', σ'', hnj, hnv', hstep, hout⟩ |
        ⟨_, _, v, _, _, _, _, _, hout⟩ | ⟨_, _, ds', v, _, _, _, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        hcall
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      rcases ih1 hstep with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · left
        simp only [esize_wseq] at *
        omega
      · rw [hnj] at hj1
        cases hj1
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      left
      simp only [esize_wseq]
      omega
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      left
      simp only [esize_wseq, esize_annot]
      omega
    · obtain ⟨h1, -, -⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      exact .inr ⟨l, pes, params, cont, by rw [jumpRedex?_wseq, hj], hl, h1⟩
    · exact hcall.ne_same_ctl.elim
  | annot hfb ihb =>
    rcases hs.annot_inv with ⟨hg, hnj, b', ρ'', σ'', hstep, hout⟩ |
        ⟨a2, ds2, c, hb, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hg, hj, _, hl, _, hout⟩ |
        ⟨-, hcall⟩ | ⟨v', pc', κ', ha', hb', hκ', hout'⟩
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
    · exact hcall.ne_same_ctl.elim
    · obtain ⟨rfl, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by simpa [Prod.mk.injEq] using hout'
      left
      simp only [esize_annot, esize_pure]
      omega
  | @save sb ps body hp hd hb ih =>
    rcases hs.save_inv with ⟨cvals, ev0', evs', hρeq, hvals, hout⟩ |
        ⟨cvals, hnv, hvals, hout⟩
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      left
      simp only [show ∀ sb ps b, esize (saveRedex sb ps b) = 1 + esize b
        from fun _ _ _ => rfl]
      omega
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      left
      rw [show esize (Expr [] (Esave sb (saveParamsWithValues ps cvals) body)) =
          1 + esize body from rfl,
        show esize (saveRedex sb ps body) = 1 + esize body from rfl]
      omega
  | if_ hpg hdg hf2 hf3 ih2 ih3 =>
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
  | run hpes hdep =>
    obtain ⟨params, cont, vs, ev0', evs', hρeq, hl, hvs, hout⟩ :=
      hs.jump_inv (by rfl)
    obtain ⟨h1, -, -⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    exact .inr ⟨_, _, params, cont, rfl, hl, h1⟩
  | sseq_spec hf1 hf2 ih1 ih2 =>
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hnv', hstep, hout⟩ |
        ⟨_, _, v, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, ds', v, _, _, hpat, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, hpat, _, _, hout⟩ |
        hcall
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
    · exact hcall.ne_same_ctl.elim
  | pure_sym =>
    obtain ⟨v, -, -, hout⟩ := hs.pure_inv rfl
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left
    simp [esize, pureRedex]
  | load_op hnv2 hp2 hd2 =>
    obtain ⟨pv, -, hout⟩ := hs.load_op_inv hnv2
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left
    simp [esize, loadOpRedex]
  | sseq_sym hb hf1 hf2 ih1 ih2 =>
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hnv', hstep, hout⟩ |
        ⟨_, _, v, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, ds', v, _, _, hpat, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, hpat, _, _, hout⟩ |
        hcall
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
    · exact hcall.ne_same_ctl.elim
  | memop_vals v1 v2 =>
    obtain ⟨pv1, pv2, b, σ'', -, -, -, hout⟩ := hs.memop_vals_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left
    simp [esize, memopPtrEqVals, memopRedex]
  | memop_op hnv hp1 hp2 hpd1 hpd2 =>
    obtain ⟨v1, v2, hv1, hv2, hout⟩ := hs.memop_op_inv hnv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left
    simp [esize, memopRedex]
  | store_op hnv hp2 hp3 hpd2 hpd3 =>
    obtain ⟨pv, cv, hv2', hv3', hout⟩ := hs.store_op_inv hnv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left
    simp [esize, storeOpRedex]
  | case_value hbr hbsz =>
    obtain ⟨cval', e'', hv, hsel, hout⟩ := hs.case_inv
    obtain rfl : _ = cval' := Option.some.inj (valueFromPexpr_val _ _ ▸ hv)
    obtain ⟨h1, -, -⟩ : e' = e'' ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left
    have := hbsz e' hsel
    omega

/-- THE UNIFIED STEP-MATCH AT THE DISCHARGE DEVICE (S1b — the old
    `engine_step_matchJ` over the full cone at ANY machine context;
    2026-09-02 mirror-completeness slice: renamed from
    `engine_step_matchU`, which is now the SHIPPED-driver statement in
    Round.lean — this `outcomesU` form is a PROOF DEVICE consumed by
    the `driveU` lane, Adequacy/TotalAdequacy, not an export): wherever
    the mirror steps at a cone configuration, the engine's discharged
    behavior list is EXACTLY the matching singleton. GONE relative to
    the J form:
    the separate label-map index and the `LabeledAt` tie hypothesis
    (derived from the context by `labels_lookup_some`); the frozen
    profile (the context is ARBITRARY — S1b′ threaded extern through
    the evaluator bridge tower and deleted the registered probe
    restriction, design record §5.2). The WP's NotStuck
    supplies the step at every reachable configuration; the rule
    premises extracted by the inversions are precisely the
    panic-exclusion facts — the WP is the well-formedness oracle. -/
theorem outcomesU_of_step {M : MachineCtx} (aid : Nat)
    {e e' : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    {ρ' : EnvStack} {ctl : Ctl} {σ σ' : Mem}
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel)
    (hs : Step M (e, ev0 :: evs, ctl, σ) (e', ρ', ctl, σ')) :
    outcomesU M aid e (ev0 :: evs) ctl σ =
      [.next (M.thread e' ρ' ctl) σ'] := by
  cases hv : toVal e with
  | some w =>
    have he := ofVal_of_toVal hv
    subst he
    cases w with
    | pure v => exact (Step.pure_val_elim hs rfl).elim
    | annot ds v =>
      obtain ⟨rfl, rfl, rfl, -⟩ := Step.annot_val_inv hs rfl
      exact outcomesU_remove_annot M aid ds v (ev0 :: evs) ctl _
  | none =>
  have hnv : toVal e = none := hv
  obtain ⟨ctx, r, hd, hfr⟩ := hf.decomp hnv
  rcases hd.step_factor hs with ⟨r', ρr, σr, hnr, hnc, hr, heq⟩ | ⟨ra, l, pes, rfl, hr⟩ |
    ⟨ra, f, pes, params, body, vs, rfl, -, -, -, hcout⟩
  · obtain ⟨he', hρ', hσ'⟩ : e' = apply_ctx ctx r' ∧ ρ' = ρr ∧ σ' = σr := by
      simpa [Prod.mk.injEq] using heq
    subst he' hρ' hσ'
    have hdOld : Decomp e ctx r := hd
    have hrj := hd.redex
    cases hrj with
    | call ra f pes => exact absurd rfl (hnc ra f pes)
    | @store loc ann lk ty pv cv mo =>
      obtain ⟨mv, fp, σ'', hmv, hmem, hout⟩ := hr.store_inv
      obtain ⟨h1, h2, h3⟩ : r' = Expr [] (Eannot [DA_pos [] fp]
          (Expr [] (Epure (Pexpr [] () (PEval Vunit))))) ∧
          ρ' = ev0 :: evs ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1 h2 h3
      unfold outcomesU engineStepsU
      rw [step_ctx_store hdOld hsz M.tagDefs hmv σ M.file M.extern M.tid M.parent _ rfl]
      simp only [List.map_cons, List.map_nil]
      rw [dischargeStep_store_active hmem]
      rfl
    | @load loc ann ty pv mo =>
      obtain ⟨fp, mval, σ'', hmem, hout⟩ := hr.load_inv
      obtain ⟨h1, h2, h3⟩ : r' = Expr [] (Eannot [DA_pos [] fp]
          (Expr [] (Epure (Pexpr [] () (PEval
            (valueFromMemValue mval).2))))) ∧
          ρ' = ev0 :: evs ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1 h2 h3
      unfold outcomesU engineStepsU
      rw [step_ctx_load hdOld hsz M.tagDefs σ M.file M.extern M.tid M.parent _ rfl]
      simp only [List.map_cons, List.map_nil]
      rw [dischargeStep_load_active hmem]
      rfl
    | @create loc ann align ty pref =>
      obtain ⟨pv, σ'', hmem, hout⟩ := hr.create_inv
      obtain ⟨h1, h2, h3⟩ : r' = Expr [] (Epure (Pexpr [] ()
          (PEval (Vobject (OVpointer pv))))) ∧
          ρ' = ev0 :: evs ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1 h2 h3
      unfold outcomesU engineStepsU
      rw [step_ctx_create hdOld hsz M.tagDefs σ M.file M.extern M.tid M.parent _ rfl]
      simp only [List.map_cons, List.map_nil]
      rw [dischargeStep_create_active (reqAddr := get_with_address []) hmem]
      rfl
    | @kill loc ann kind pv =>
      obtain ⟨σ'', hmem, hout⟩ := hr.kill_inv
      obtain ⟨h1, h2, h3⟩ : r' = Expr [] (Epure (Pexpr [] () (PEval Vunit))) ∧
          ρ' = ev0 :: evs ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1 h2 h3
      unfold outcomesU engineStepsU
      rw [step_ctx_kill hdOld hsz M.tagDefs σ M.file M.extern M.tid M.parent _ rfl]
      simp only [List.map_cons, List.map_nil]
      rw [dischargeStep_kill_active hmem]
      rfl
    | @kill_op loc ann kind pe hnvK =>
      obtain ⟨hpK, hdK⟩ : PePure pe ∧ peDepth pe ≤ lemDefaultFuel := by
        cases hfr with
        | kill =>
          rw [show valueFromPexpr (Pexpr [] () (PEval
            (Vobject (OVpointer _)))) = some _ from rfl] at hnvK
          cases hnvK
        | kill_op hnvK' hpK hdK => exact ⟨hpK, hdK⟩
      obtain ⟨pv, hv, hout⟩ := hr.kill_op_inv hnvK
      obtain ⟨h1, h2, h3⟩ : r' = killRedex loc ann kind pv ∧
          ρ' = ev0 :: evs ∧ σ' = σ := by
        simpa [Prod.mk.injEq, killRedex] using hout
      subst h1 h2
      obtain rfl : σ = σ' := h3.symm
      unfold outcomesU engineStepsU
      exact stepDischarge_kill_eval hdOld hsz hnvK hpK hdK M.tagDefs σ M.file
        M.extern M.tid M.parent _ rfl hv aid M.runState
    | @alloc loc ann align size pref =>
      obtain ⟨pv, σ'', hmem, hout⟩ := hr.alloc_inv
      obtain ⟨h1, h2, h3⟩ : r' = Expr [] (Epure (Pexpr [] ()
          (PEval (Vobject (OVpointer pv))))) ∧
          ρ' = ev0 :: evs ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1 h2 h3
      unfold outcomesU engineStepsU
      rw [step_ctx_alloc hdOld hsz M.tagDefs σ M.file M.extern M.tid M.parent _ rfl]
      simp only [List.map_cons, List.map_nil]
      rw [dischargeStep_alloc_active hmem]
      rfl
    | @alloc_op loc ann pref pe1 pe2 hnvA =>
      obtain ⟨hp1, hp2, hd1, hd2⟩ : PePure pe1 ∧ PePure pe2 ∧
          peDepth pe1 ≤ lemDefaultFuel ∧ peDepth pe2 ≤ lemDefaultFuel := by
        cases hfr with
        | alloc =>
          rw [valueFromPexprs_pair, valueFromPexpr_val, valueFromPexpr_val] at hnvA
          cases hnvA
        | alloc_op hnvA' hp1 hp2 hd1 hd2 => exact ⟨hp1, hp2, hd1, hd2⟩
      obtain ⟨al, sz, hv1, hv2, hout⟩ := hr.alloc_op_inv hnvA
      obtain ⟨h1, h2, h3⟩ : r' = allocRedex loc ann al sz pref ∧
          ρ' = ev0 :: evs ∧ σ' = σ := by
        simpa [Prod.mk.injEq, allocRedex] using hout
      subst h1 h2
      obtain rfl : σ = σ' := h3.symm
      unfold outcomesU engineStepsU
      exact stepDischarge_alloc_eval hdOld hsz hnvA hp1 hp2 hd1 hd2 M.tagDefs σ M.file
        M.extern M.tid M.parent _ rfl hv1 hv2 aid M.runState
    | @beta_pure pa bty v e2 =>
      rcases hr.sseq_inv with ⟨e1', ρ'', σ'', hnj, hnv', hstep, hout⟩ |
          ⟨_, _, v', _, _, _, he1, _, hout⟩ |
          ⟨_, _, ds', v', _, _, _, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, hpat, _, _, _⟩ |
          hcall
      · rw [toVal_ofVal] at hnv'; cases hnv'
      · obtain rfl : v' = v := by
          have : ofVal (.pure v') = ofVal (.pure v) := he1.symm
          simpa [ofVal] using this
        obtain ⟨h1, h2, h3⟩ : r' = e2 ∧ ρ' = ev0 :: evs ∧ σ' = σ := by
          simpa [Prod.mk.injEq] using hout
        subst h2
        obtain rfl : σ = σ' := h3.symm
        obtain rfl : e2 = r' := h1.symm
        unfold outcomesU engineStepsU
        rw [step_ctx_beta_pure hdOld hsz M.tagDefs σ M.file M.extern M.tid M.parent _ rfl rfl]
        rfl
      · exact absurd he1 (by simp [ofVal])
      · rw [jumpRedex?_ofVal] at hj; cases hj
      · exact (specPat_ne_base hpat).elim
      · exact (specPat_ne_base hpat).elim
      · exact (symPat_ne_base hpat).elim
      · exact hcall.ne_same_ctl.elim
    | @beta_annot pa bty ds v e2 =>
      rcases hr.sseq_inv with ⟨e1', ρ'', σ'', hnj, hnv', hstep, hout⟩ |
          ⟨_, _, v', _, _, _, he1, _, hout⟩ |
          ⟨_, _, ds', v', _, _, _, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, hpat, _, _, _⟩ |
          hcall
      · rw [toVal_ofVal] at hnv'; cases hnv'
      · exact absurd he1 (by simp [ofVal])
      · obtain ⟨hds, hv⟩ : ds = ds' ∧ v = v' := by simpa [ofVal] using he1
        subst hds hv
        obtain ⟨h1, h2, h3⟩ : r' = Expr [] (Eannot ds e2) ∧
            ρ' = ev0 :: evs ∧ σ' = σ := by
          simpa [Prod.mk.injEq] using hout
        subst h1 h2
        obtain rfl : σ = σ' := h3.symm
        unfold outcomesU engineStepsU
        rw [step_ctx_beta_annot hdOld hsz M.tagDefs σ M.file M.extern M.tid M.parent _ rfl rfl]
        rfl
      · rw [jumpRedex?_ofVal] at hj; cases hj
      · exact (specPat_ne_base hpat).elim
      · exact (specPat_ne_base hpat).elim
      · exact (symPat_ne_base hpat).elim
      · exact hcall.ne_same_ctl.elim
    | @wbeta_pure pa bty v e2 =>
      rcases hr.wseq_inv with ⟨e1', ρ'', σ'', hnj, hnv', hstep, hout⟩ |
          ⟨_, _, v', _, _, _, he1, _, hout⟩ |
          ⟨_, _, ds', v', _, _, _, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          hcall
      · rw [toVal_ofVal] at hnv'; cases hnv'
      · obtain rfl : v' = v := by
          have : ofVal (.pure v') = ofVal (.pure v) := he1.symm
          simpa [ofVal] using this
        obtain ⟨h1, h2, h3⟩ : r' = e2 ∧ ρ' = ev0 :: evs ∧ σ' = σ := by
          simpa [Prod.mk.injEq] using hout
        subst h2
        obtain rfl : σ = σ' := h3.symm
        obtain rfl : e2 = r' := h1.symm
        unfold outcomesU engineStepsU
        rw [step_ctx_wseq_pure hdOld hsz M.tagDefs σ M.file M.extern M.tid M.parent _ rfl rfl]
        rfl
      · exact absurd he1 (by simp [ofVal])
      · rw [jumpRedex?_ofVal] at hj; cases hj
      · exact hcall.ne_same_ctl.elim
    | @wbeta_annot pa bty ds v e2 =>
      rcases hr.wseq_inv with ⟨e1', ρ'', σ'', hnj, hnv', hstep, hout⟩ |
          ⟨_, _, v', _, _, _, he1, _, hout⟩ |
          ⟨_, _, ds', v', _, _, _, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          hcall
      · rw [toVal_ofVal] at hnv'; cases hnv'
      · exact absurd he1 (by simp [ofVal])
      · obtain ⟨hds, hv⟩ : ds = ds' ∧ v = v' := by simpa [ofVal] using he1
        subst hds hv
        obtain ⟨h1, h2, h3⟩ : r' = Expr [] (Eannot ds e2) ∧
            ρ' = ev0 :: evs ∧ σ' = σ := by
          simpa [Prod.mk.injEq] using hout
        subst h1 h2
        obtain rfl : σ = σ' := h3.symm
        unfold outcomesU engineStepsU
        rw [step_ctx_wseq_annot hdOld hsz M.tagDefs σ M.file M.extern M.tid M.parent _ rfl rfl]
        rfl
      · rw [jumpRedex?_ofVal] at hj; cases hj
      · exact hcall.ne_same_ctl.elim
    | @merge ds1 ds2 b hirr =>
      rcases hr.annot_inv with ⟨hg, hnj, b', ρ'', σ'', hstep, hout⟩ |
          ⟨a2, ds2', c, hbeq, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hg, hj, _, _, _, _⟩ |
          ⟨-, hcall⟩ | ⟨v', pc', κ', ha', hb', hκ', hout'⟩
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
        unfold outcomesU engineStepsU
        rw [step_ctx_merge hdOld hirr hsz M.tagDefs σ M.file M.extern M.tid M.parent _ rfl]
        rfl
      · rw [show annotRooted (Expr ([] : List annot) (Eannot ds2 b)) = true
          from rfl] at hg
        cases hg
      · exact hcall.ne_same_ctl.elim
      · cases hb'
    | save sb ps body =>
      have hdep : ∀ pe ∈ saveParamPexprs ps, peDepth pe ≤ lemDefaultFuel := by
        cases hfr with
        | save _ hdep _ => exact hdep
      rcases hr.save_inv with ⟨cvals, ev0', evs', hρeq, hvals, hout⟩ |
          ⟨cvals, hnvS, hvals, hout⟩
      · obtain ⟨h1, h2, h3⟩ : r' = body ∧
            ρ' = bindSaveParams ps cvals (ev0 :: evs) ∧ σ' = σ := by
          simpa [Prod.mk.injEq] using hout
        subst h2
        obtain rfl : σ = σ' := h3.symm
        obtain rfl : body = r' := h1.symm
        unfold outcomesU engineStepsU
        rw [step_ctx_save hd hsz hvals M.tagDefs σ M.file M.extern M.tid M.parent _ rfl rfl]
        rfl
      · obtain ⟨h1, h2, h3⟩ : r' = saveRedex sb (saveParamsWithValues ps cvals) body ∧
            ρ' = ev0 :: evs ∧ σ' = σ := by
          simpa [Prod.mk.injEq, saveRedex] using hout
        subst h1 h2
        obtain rfl : σ = σ' := h3.symm
        unfold outcomesU engineStepsU
        exact stepDischarge_save_eval hd hsz hnvS hdep M.tagDefs σ M.file M.extern
          M.tid M.parent _ rfl hvals aid M.runState
    | if_ g e2 e3 =>
      have hdg : peDepth g ≤ lemDefaultFuel := by
        cases hfr with
        | if_ _ hdg _ _ => exact hdg
      rcases hr.if_inv with ⟨hg, hout⟩ | ⟨hg, hout⟩
      · obtain ⟨h1, h2, h3⟩ : r' = e2 ∧ ρ' = ev0 :: evs ∧ σ' = σ := by
          simpa [Prod.mk.injEq] using hout
        subst h2
        obtain rfl : σ = σ' := h3.symm
        obtain rfl : e2 = r' := h1.symm
        unfold outcomesU engineStepsU
        exact stepDischarge_if_true hd hsz hdg M.tagDefs σ M.file M.extern
          M.tid M.parent _ rfl hg aid M.runState
      · obtain ⟨h1, h2, h3⟩ : r' = e3 ∧ ρ' = ev0 :: evs ∧ σ' = σ := by
          simpa [Prod.mk.injEq] using hout
        subst h2
        obtain rfl : σ = σ' := h3.symm
        obtain rfl : e3 = r' := h1.symm
        unfold outcomesU engineStepsU
        exact stepDischarge_if_false hd hsz hdg M.tagDefs σ M.file M.extern
          M.tid M.parent _ rfl hg aid M.runState
    | case_ pe pats =>
      -- S1b: value-scrutinee Ecase is IN the cone (F-01 export).
      cases hfr with
      | case_value hbr hbsz =>
        obtain ⟨cval', e'', hv, hsel, hout⟩ := hr.case_inv
        obtain rfl : _ = cval' := Option.some.inj (valueFromPexpr_val _ _ ▸ hv)
        obtain ⟨h1, h2, h3⟩ : r' = e'' ∧ ρ' = ev0 :: evs ∧ σ' = σ := by
          simpa [Prod.mk.injEq] using hout
        subst h1 h2
        obtain rfl : σ = σ' := h3.symm
        unfold outcomesU engineStepsU
        rw [step_ctx_case_value hd hsz hsel
          M.tagDefs σ M.file M.extern M.tid M.parent _ rfl]
        rfl
    | run ra l pes =>
      -- unreachable: the factor theorem's LEFT disjunct certifies
      -- its redex is NOT a run redex
      exact absurd rfl (hnr ra l pes)
    | @pure_e pe hnv =>
      obtain ⟨pb, x, rfl⟩ : ∃ pb x, pe = Pexpr pb () (PEsym x) := by
        cases hfr with
        | val_pure v => rw [valueFromPexpr_val] at hnv; cases hnv
        | pure_sym => exact ⟨_, _, rfl⟩
      obtain ⟨v, -, hv, hout⟩ := hr.pure_inv hnv
      obtain ⟨h1, h2, h3⟩ : r' = Expr [] (Epure (Pexpr [] () (PEval v))) ∧
          ρ' = ev0 :: evs ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1 h2
      obtain rfl : σ = σ' := h3.symm
      unfold outcomesU engineStepsU
      exact stepDischarge_pure_sym hd hsz M.tagDefs σ M.file M.extern
        M.tid M.parent _ rfl hv aid M.runState
    | @load_op loc ann ty pe2 mo hnv2 =>
      obtain ⟨hp2, hd2⟩ : PePure pe2 ∧ peDepth pe2 ≤ lemDefaultFuel := by
        cases hfr with
        | load =>
          rw [show valueFromPexpr (Pexpr [] () (PEval
            (Vobject (OVpointer _)))) = some _ from rfl] at hnv2
          cases hnv2
        | load_op hnv2' hp2 hd2 => exact ⟨hp2, hd2⟩
      obtain ⟨pv, hv2, hout⟩ := hr.load_op_inv hnv2
      obtain ⟨h1, h2, h3⟩ : r' = loadRedex loc ann ty pv mo ∧
          ρ' = ev0 :: evs ∧ σ' = σ := by
        simpa [Prod.mk.injEq, loadRedex] using hout
      subst h1 h2
      obtain rfl : σ = σ' := h3.symm
      unfold outcomesU engineStepsU
      exact stepDischarge_load_eval hd hsz hnv2 hp2 hd2 M.tagDefs σ M.file
        M.extern M.tid M.parent _ rfl hv2 aid M.runState
    | @beta_spec pa pb x bty w e2 =>
      rcases hr.sseq_inv with ⟨e1', ρ'', σ'', hnj, hnv', hstep, hout⟩ |
          ⟨_, _, v', _, _, hpat, he1, _, hout⟩ |
          ⟨_, _, ds', v', _, _, hpat, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨pa', pb', x', bty', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', pb', x', bty', ds', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', x', bty', v', _, _, hpat, he1, _, hout⟩ |
          hcall
      · rw [toVal_ofVal] at hnv'; cases hnv'
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
        unfold outcomesU engineStepsU
        rw [step_ctx_beta_spec_pure hd hsz M.tagDefs σ M.file M.extern M.tid M.parent _ rfl rfl]
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
        unfold outcomesU engineStepsU
        rw [step_ctx_beta_spec_annot hd hsz M.tagDefs σ M.file M.extern M.tid M.parent _ rfl rfl]
        rfl
      · exact (symPat_ne_spec hpat).elim
      · exact hcall.ne_same_ctl.elim
    | @memop mop pes =>
      cases hfr with
      | memop_vals v1 v2 =>
        obtain ⟨pv1, pv2, b, σ'', rfl, rfl, hmem, hout⟩ := hr.memop_vals_inv
        obtain ⟨h1, h2, h3⟩ : r' = Expr [] (Epure (Pexpr [] () (PEval (boolValue b)))) ∧
            ρ' = ev0 :: evs ∧ σ' = σ'' := by
          simpa [Prod.mk.injEq] using hout
        subst h1 h2 h3
        unfold outcomesU engineStepsU
        rw [step_ctx_memop hd hsz rfl rfl M.tagDefs σ M.file M.extern M.tid M.parent _ rfl]
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
        unfold outcomesU engineStepsU
        exact stepDischarge_memop_eval hd hsz hnvF hpd1 hpd2 M.tagDefs σ
          M.file M.extern M.tid M.parent _ rfl hv1' hv2' aid M.runState
    | @store_op loc ann ty pe2 pe3 mo hnvR =>
      obtain ⟨hp2, hp3, hpd2, hpd3⟩ :
          PePure pe2 ∧ PePure pe3 ∧
          peDepth pe2 ≤ lemDefaultFuel ∧ peDepth pe3 ≤ lemDefaultFuel := by
        cases hfr with
        | store =>
          rw [valueFromPexprs_pair, valueFromPexpr_val, valueFromPexpr_val] at hnvR
          cases hnvR
        | store_op hnv' hp2 hp3 hpd2 hpd3 =>
          exact ⟨hp2, hp3, hpd2, hpd3⟩
      obtain ⟨pv, cv, hv2, hv3, hout⟩ := hr.store_op_inv hnvR
      obtain ⟨h1, h2, h3⟩ : r' = storeRedex loc ann false ty pv cv mo ∧
          ρ' = ev0 :: evs ∧ σ' = σ := by
        simpa [Prod.mk.injEq, storeRedex] using hout
      subst h1 h2
      obtain rfl : σ = σ' := h3.symm
      unfold outcomesU engineStepsU
      exact stepDischarge_store_eval hd hsz hnvR hp2 hp3 hpd2 hpd3
        M.tagDefs σ M.file M.extern M.tid M.parent _ rfl hv2 hv3 aid
        M.runState
    | @beta_sym pa x bty w e2 =>
      rcases hr.sseq_inv with ⟨e1', ρ'', σ'', hnj, hnv', hstep, hout⟩ |
          ⟨_, _, v', _, _, hpat, he1, _, hout⟩ |
          ⟨_, _, ds', v', _, _, hpat, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨pa', pb', x', bty', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', pb', x', bty', ds', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', x', bty', v', _, _, hpat, he1, _, hout⟩ |
          hcall
      · rw [toVal_ofVal] at hnv'; cases hnv'
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
        unfold outcomesU engineStepsU
        rw [step_ctx_beta_sym_pure hd hsz M.tagDefs σ M.file M.extern M.tid M.parent _ rfl rfl]
        rfl
      · exact hcall.ne_same_ctl.elim
  · obtain ⟨params, cont, vs, ev0', evs', hρeq, hl, hvs, hout⟩ :=
      hr.jump_inv (by rfl)
    have hdep : ∀ pe' ∈ pes, peDepth pe' ≤ lemDefaultFuel := by
      cases hfr with
      | run _ hdep => exact hdep
    obtain ⟨p, hproc, hQ⟩ := MachineCtx.labels_lookup_some hl
    obtain ⟨h1, h2, h3⟩ : e' = cont ∧
        ρ' = bindArgs params vs (ev0 :: evs) ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1 h2
    obtain rfl : σ = σ' := h3.symm
    unfold outcomesU engineStepsU
    exact stepDischarge_run hd hsz hl hdep M.tagDefs σ M.file M.extern M.tid
      M.parent p _ rfl hproc hvs aid M.runState hQ
  · exact absurd (congrArg (fun c : Config => c.2.2.1.κ) hcout) (by simp)


/-! ## Engine-completeness, per construct, at any machine context
(S1a-demonstrated two-sidedness — store and value-scrutinee case;
the refusal channels of run/if/save/eval shapes are failwithI
panics, deliberately unmodeled: those constructs are ONE-SIDED
(match-given-step, `engine_step_matchU`), the audit-sanctioned
outcome documented per-construct in the capability manifest). -/

/-- One matched engine behavior at a machine context (`refused`
    requires provable mirror stuckness, so refusals contradict
    NotStuck). -/
inductive EngineMatchU (M : MachineCtx) (e : CoreExpr) (ρ : EnvStack) (ctl : Ctl)
    (σ : Mem) : EngineOutcome → Prop where
  | step {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem} :
      Step M (e, ρ, ctl, σ) (e', ρ', ctl, σ') →
      EngineMatchU M e ρ ctl σ (.next (M.thread e' ρ' ctl) σ')
  | removeAnnot {ds : List dyn_annotation} {v : value} :
      e = ofVal (.annot ds v) →
      EngineMatchU M e ρ ctl σ (.next (M.thread (ofVal (.pure v)) ρ ctl) σ)
  | done {v : value} : e = ofVal (.pure v) → EngineMatchU M e ρ ctl σ (.done v)
  | refused {o : EngineOutcome} : o.isRefusal →
      (∀ out, ¬ Step M (e, ρ, ctl, σ) out) → toVal e = none →
      EngineMatchU M e ρ ctl σ o

/-- STORE IS TWO-SIDED at any context: the engine's behavior at a
    store redex is a singleton, and it is a mirror step exactly when
    the mirror can step (encoding + active memM); the ILLTYPED and
    killed channels arise only where the mirror is provably stuck. -/
theorem engine_complete_storeU (M : MachineCtx) (aid : Nat)
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
    {ty : ctype} {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
    (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    ∃ o, outcomesU M aid (storeRedex loc ann lk ty pv cv mo) ρ ctl σ = [o] ∧
      EngineMatchU M (storeRedex loc ann lk ty pv cv mo) ρ ctl σ o := by
  have hsz : esize (storeRedex loc ann lk ty pv cv mo) ≤ lemDefaultFuel := by
    rw [show esize (storeRedex loc ann lk ty pv cv mo) = 1 from rfl]
    unfold lemDefaultFuel
    omega
  cases hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv with
  | none =>
    refine ⟨.error (String.append (CerbLocation.stringFromLocation loc)
        (String.append "the value of a store("
          (String.append (CerbPP.stringFromCore_ctype (Ctype [] (unatomic_ ty)))
            (String.append ") didn't match the lvalue type: "
              (CerbPP.stringFromCore_value cv))))), ?_, ?_⟩
    · unfold outcomesU engineStepsU storeRedex
      rw [step_ctx_store_illtyped
        (Decomp.root (Redex.store)) hsz M.tagDefs hmv
        σ M.file M.extern M.tid M.parent (M.thread _ ρ ctl) rfl]
      rfl
    · refine .refused trivial (fun out hstep => ?_) rfl
      obtain ⟨mv', -, -, hmv', -, -⟩ := hstep.store_inv
      rw [hmv] at hmv'
      cases hmv'
  | some mv =>
    cases hmem : applyMemM (CerbMem.storeM M.tagDefs loc ty lk pv mv) σ with
    | some fpσ =>
      obtain ⟨fp, σ'⟩ := fpσ
      refine ⟨_, ?_, .step (Step.store_canonical hmv hmem)⟩
      unfold outcomesU engineStepsU storeRedex
      rw [step_ctx_store (Decomp.root (Redex.store)) hsz M.tagDefs hmv σ M.file M.extern M.tid M.parent (M.thread _ ρ ctl) rfl]
      simp only [List.map_cons, List.map_nil]
      rw [dischargeStep_store_active hmem]
      rfl
    | none =>
      refine ⟨dischargeStep M.tagDefs aid M.runState σ (Step_action_request2
          "StoreRequest" (requestLoc (M.thread (storeRedex loc ann lk ty pv cv mo) ρ ctl) loc) M.tid
          (is_unseq_with_ccall CTX)
          (stExceptUndef_return (StoreRequest2 mo ty lk pv mv (fun _ fp =>
            { M.thread (storeRedex loc ann lk ty pv cv mo) ρ ctl with
              arena := apply_ctx CTX (Expr [] (Eannot [DA_pos [] fp]
                (Expr [] (Epure (Pexpr [] () (PEval Vunit)))))) })))),
        ?_, ?_⟩
      · unfold outcomesU engineStepsU storeRedex
        rw [step_ctx_store (Decomp.root (Redex.store)) hsz M.tagDefs hmv σ M.file M.extern M.tid M.parent
          (M.thread _ ρ ctl) rfl]
        rfl
      · refine .refused (dischargeStep_store_refusal hmem)
          (fun out hstep => ?_) rfl
        obtain ⟨mv', fp', σ'', hmv', hmem', -⟩ := hstep.store_inv
        rw [hmv] at hmv'
        obtain rfl : mv = mv' := Option.some.inj hmv'
        rw [hmem] at hmem'
        cases hmem'

/-- Ecase (value scrutinee), NO-MATCH shape: the engine's ILLTYPED
    refusal (one_step0's Ecase value arm, `select_case = none` —
    Core_reduction.lean:353), context undisturbed. The engine
    equation the case export needs for its refusal side. -/
theorem step_ctx_case_illtyped {e : CoreExpr} {ctx : context}
    {a : List annot} {cval : value} {pats : List (pattern × CoreExpr)}
    (hd : Decomp e ctx (caseRedex (Pexpr a () (PEval cval)) pats))
    (hsz : esize e ≤ lemDefaultFuel)
    (hsel : select_case subst_sym_expr cval pats = none)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_error2 (String.append "Ecase, mismatched ==> "
        (CerbPP.stringFromCore_expr
          (caseRedex (Pexpr a () (PEval cval)) pats)))] := by
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

/-- CASE (value scrutinee) IS TWO-SIDED at any context: TAU into the
    selected branch when a branch matches (= exactly when the mirror
    steps), the ILLTYPED refusal when none does (mirror provably
    stuck). The F-01 RED row's engine-facing pair. -/
theorem engine_complete_caseU (M : MachineCtx) (aid : Nat)
    {b : List annot} {cval : value} {pats : List (pattern × CoreExpr)}
    (hsz : esize (caseRedex (Pexpr b () (PEval cval)) pats)
      ≤ lemDefaultFuel)
    (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    ∃ o, outcomesU M aid (caseRedex (Pexpr b () (PEval cval)) pats) ρ ctl σ = [o] ∧
      EngineMatchU M (caseRedex (Pexpr b () (PEval cval)) pats) ρ ctl σ o := by
  cases hsel : select_case subst_sym_expr cval pats with
  | some e' =>
    refine ⟨_, ?_, .step (Step.case_value (valueFromPexpr_val _ _) hsel)⟩
    unfold outcomesU engineStepsU caseRedex
    rw [step_ctx_case_value (Decomp.root (Redex.case_ _ _)) hsz hsel
      M.tagDefs σ M.file M.extern M.tid M.parent (M.thread _ ρ ctl) rfl]
    rfl
  | none =>
    refine ⟨.error (String.append "Ecase, mismatched ==> "
        (CerbPP.stringFromCore_expr
          (caseRedex (Pexpr b () (PEval cval)) pats))), ?_, ?_⟩
    · unfold outcomesU engineStepsU caseRedex
      rw [step_ctx_case_illtyped (Decomp.root (Redex.case_ _ _)) hsz hsel
        M.tagDefs σ M.file M.extern M.tid M.parent (M.thread _ ρ ctl) rfl]
      rfl
    · refine .refused trivial (fun out hstep => ?_) rfl
      obtain ⟨cval', e'', hv, hsel', -⟩ := hstep.case_inv
      obtain rfl : _ = cval' := Option.some.inj (valueFromPexpr_val _ _ ▸ hv)
      rw [hsel] at hsel'
      cases hsel'

end CerberusHeapLang
