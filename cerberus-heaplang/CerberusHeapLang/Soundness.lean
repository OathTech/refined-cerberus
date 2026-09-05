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
protocol (the engine taus `{A}v --> v` where Step treats `{A}v` as a
value, then reports `Step_done2 v`) is certified at the shipped round
(`shipped_done`, Round.lean). Refusals are
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
        -- (the discharge projection Round.lean classifies), not a statement referent.
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
        -- PROOF DEVICE (the discharge projection Round.lean classifies), not a statement referent.
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
  | Expr _ (Ebound b) => 1 + esize b
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
def storeRedex (an : List _root_.annot) (loc : CerbLocation.Loc) (ann : core_run_annotation) (lk : Bool)
    (ty : ctype) (pv : CerbMem.PointerValue) (cv : value) (mo : memory_order) :
    CoreExpr :=
  Expr an (Eaction (Paction polarity.Pos (Action loc ann
    (Store0 lk (Pexpr [] () (PEval (Vctype ty)))
               (Pexpr [] () (PEval (Vobject (OVpointer pv))))
               (Pexpr [] () (PEval cv)) mo))))

def loadRedex (an : List _root_.annot) (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (mo : memory_order) : CoreExpr :=
  Expr an (Eaction (Paction polarity.Pos (Action loc ann
    (Load0 (Pexpr [] () (PEval (Vctype ty)))
           (Pexpr [] () (PEval (Vobject (OVpointer pv)))) mo))))

def createRedex (an : List _root_.annot) (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (align : CerbMem.IntegerValue) (ty : ctype) (pref : prefix0) : CoreExpr :=
  Expr an (Eaction (Paction polarity.Pos (Action loc ann
    (Create (Pexpr [] () (PEval (Vobject (OVinteger align))))
            (Pexpr [] () (PEval (Vctype ty))) pref))))

/-- `is_irreducible` (Core_reduction.lean:293) holds on both value
    forms. -/
theorem is_irreducible_ofVal (w : SpikeVal) : is_irreducible (ofVal w) = true := by
  cases w <;> rfl

/-- E1: … at every annotation placement (`is_irreducible` reads shapes
    only, Core_reduction.lean:293). -/
theorem is_irreducible_ofValA (w : SpikeValA) : is_irreducible (ofValA w) = true := by
  cases w <;> rfl

/-- A doubly-annotated node is reducible whatever sits inside (the
    ANNOTS-merge root; `is_irreducible`'s first arm is the only one that
    inspects the inner node and answers `false`). -/
theorem is_irreducible_merge {a a2 : List _root_.annot} {ds ds2 : List dyn_annotation}
    (c : CoreExpr) :
    is_irreducible (Expr a (Eannot ds (Expr a2 (Eannot ds2 c)))) = false := by
  rcases c with ⟨a3, c_⟩
  cases c_ <;> try rfl
  rename_i pe
  rcases pe with ⟨pb, u, pe_⟩
  cases u
  cases pe_ <;> rfl

/-- E1: `bound` is never irreducible. -/
@[simp] theorem is_irreducible_bound {a : List _root_.annot} {b : CoreExpr} :
    is_irreducible (Expr a (Ebound b)) = false := rfl

@[simp] theorem is_irreducible_sseq {a : List _root_.annot} {pat : pattern}
    {e1 e2 : CoreExpr} :
    is_irreducible (Expr a (Esseq pat e1 e2)) = false := rfl

@[simp] theorem is_irreducible_wseq {a : List _root_.annot} {pat : pattern}
    {e1 e2 : CoreExpr} :
    is_irreducible (Expr a (Ewseq pat e1 e2)) = false := rfl

@[simp] theorem is_irreducible_action {a : List _root_.annot}
    {p : generic_paction core_run_annotation Unit sym} :
    is_irreducible (Expr a (Eaction p)) = false := rfl

/-- A value form under `toVal` is irreducible in the engine's sense. -/
theorem is_irreducible_of_toVal {e : CoreExpr} {w : SpikeVal}
    (h : toVal e = some w) : is_irreducible e = true := by
  obtain ⟨wa, -, rfl⟩ := ofValA_of_toVal h; exact is_irreducible_ofValA wa

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

@[simp] theorem esize_sseq {a : List _root_.annot} {pat : pattern} {e1 e2 : CoreExpr} :
    esize (Expr a (Esseq pat e1 e2)) = 1 + max (esize e1) (esize e2) := rfl

@[simp] theorem esize_wseq {a : List _root_.annot} {pat : pattern} {e1 e2 : CoreExpr} :
    esize (Expr a (Ewseq pat e1 e2)) = 1 + max (esize e1) (esize e2) := rfl

@[simp] theorem esize_bound {a : List _root_.annot} {b : CoreExpr} :
    esize (Expr a (Ebound b)) = 1 + esize b := rfl

@[simp] theorem esize_annot {a : List _root_.annot} {ds : List dyn_annotation}
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

theorem get_ctx_ofValA (w : SpikeValA) (n : Nat) :
    get_ctx_lemFuel (n+1) (ofValA w) = [(CTX, ofValA w)] := by
  cases w <;> rfl

theorem get_ctx_sseq {a : List _root_.annot} {pat : pattern} {e1 e2 : CoreExpr}
    (h : is_irreducible e1 = false) (n : Nat) :
    get_ctx_lemFuel (n+1) (Expr a (Esseq pat e1 e2)) =
      List.map (fun p => (Csseq a pat p.1 e2, p.2)) (get_ctx_lemFuel n e1) := by
  rw [show get_ctx_lemFuel (n+1) (Expr a (Esseq pat e1 e2)) =
      (if is_irreducible e1 = true then [(CTX, Expr a (Esseq pat e1 e2))]
       else List.map (fun p => (Csseq a pat p.1 e2, p.2)) (get_ctx_lemFuel n e1))
    from rfl, h]
  rfl

theorem get_ctx_sseq_val {a : List _root_.annot} {pat : pattern} {w : SpikeValA}
    {e2 : CoreExpr} (n : Nat) :
    get_ctx_lemFuel (n+1) (Expr a (Esseq pat (ofValA w) e2)) =
      [(CTX, Expr a (Esseq pat (ofValA w) e2))] := by
  cases w <;> rfl

theorem get_ctx_wseq {a : List _root_.annot} {pat : pattern} {e1 e2 : CoreExpr}
    (h : is_irreducible e1 = false) (n : Nat) :
    get_ctx_lemFuel (n+1) (Expr a (Ewseq pat e1 e2)) =
      List.map (fun p => (Cwseq a pat p.1 e2, p.2)) (get_ctx_lemFuel n e1) := by
  rw [show get_ctx_lemFuel (n+1) (Expr a (Ewseq pat e1 e2)) =
      (if is_irreducible e1 = true then [(CTX, Expr a (Ewseq pat e1 e2))]
       else List.map (fun p => (Cwseq a pat p.1 e2, p.2)) (get_ctx_lemFuel n e1))
    from rfl, h]
  rfl

theorem get_ctx_wseq_val {a : List _root_.annot} {pat : pattern} {w : SpikeValA}
    {e2 : CoreExpr} (n : Nat) :
    get_ctx_lemFuel (n+1) (Expr a (Ewseq pat (ofValA w) e2)) =
      [(CTX, Expr a (Ewseq pat (ofValA w) e2))] := by
  cases w <;> rfl

theorem get_ctx_action {a : List _root_.annot}
    {p : generic_paction core_run_annotation Unit sym} (n : Nat) :
    get_ctx_lemFuel (n+1) (Expr a (Eaction p)) = [(CTX, Expr a (Eaction p))] := rfl

theorem get_ctx_merge {a a2 : List _root_.annot} {ds1 ds2 : List dyn_annotation}
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
def saveRedex (an : List _root_.annot) (sb : sym × core_base_type)
    (ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)))
    (body : CoreExpr) : CoreExpr :=
  Expr an (Esave sb ps body)

def ifRedex (an : List _root_.annot) (g : generic_pexpr Unit sym) (e2 e3 : CoreExpr) : CoreExpr :=
  Expr an (Eif g e2 e3)

def caseRedex (an : List _root_.annot) (pe : generic_pexpr Unit sym)
    (pats : List (pattern × CoreExpr)) : CoreExpr :=
  Expr an (Ecase pe pats)

def runRedex (an : List _root_.annot) (ra : core_run_annotation) (l : sym)
    (pes : List (generic_pexpr Unit sym)) : CoreExpr :=
  Expr an (Erun ra l pes)

inductive Redex : CoreExpr → Prop where
  | store {an : List _root_.annot} {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
      {ty : ctype} {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order} :
      Redex (storeRedex an loc ann lk ty pv cv mo)
  | load {an : List _root_.annot} {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
      {pv : CerbMem.PointerValue} {mo : memory_order} :
      Redex (loadRedex an loc ann ty pv mo)
  | create {an : List _root_.annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {align : CerbMem.IntegerValue} {ty : ctype} {pref : prefix0} :
      Redex (createRedex an loc ann align ty pref)
  /-- E1: the create ACTION_EVAL redex (operands not all values —
      `Ivalignof(ty)` in the alignment slot is the emitted shape). -/
  | create_op {an : List _root_.annot} (loc : CerbLocation.Loc) (ann : core_run_annotation)
      (pref : prefix0) {pe1 pe2 : generic_pexpr Unit sym}
      (hnv : valueFromPexprs [pe1, pe2] = none) :
      Redex (createOpRedex an loc ann pe1 pe2 pref)
  /-- The kill redex at an evaluated pointer, any kind (kill/free arc K2). -/
  | kill {an : List _root_.annot} {loc : CerbLocation.Loc} {ann : core_run_annotation} {kind : kill_kind}
      {pv : CerbMem.PointerValue} :
      Redex (killRedex an loc ann kind pv)
  /-- The kill ACTION_EVAL redex (unevaluated pointer operand). -/
  | kill_op {an : List _root_.annot} (loc : CerbLocation.Loc) (ann : core_run_annotation)
      (kind : kill_kind) {pe : generic_pexpr Unit sym}
      (hnv : valueFromPexpr pe = none) :
      Redex (killOpRedex an loc ann kind pe)
  /-- The alloc redex at evaluated integer operands (kill/free arc K3). -/
  | alloc {an : List _root_.annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {align size : CerbMem.IntegerValue} {pref : prefix0} :
      Redex (allocRedex an loc ann align size pref)
  /-- The alloc ACTION_EVAL redex (operands not all values). -/
  | alloc_op {an : List _root_.annot} (loc : CerbLocation.Loc) (ann : core_run_annotation)
      (pref : prefix0) {pe1 pe2 : generic_pexpr Unit sym}
      (hnv : valueFromPexprs [pe1, pe2] = none) :
      Redex (allocOpRedex an loc ann pe1 pe2 pref)
  | beta_pure {an pa a1 b1 : List _root_.annot} {bty : core_base_type} {v : value}
      {e2 : CoreExpr} :
      Redex (Expr an (Esseq (Pattern pa (CaseBase (none, bty)))
        (ofValA (.pure a1 b1 v)) e2))
  | beta_annot {an pa a1 a2 b1 : List _root_.annot} {bty : core_base_type}
      {ds : List dyn_annotation} {v : value} {e2 : CoreExpr} :
      Redex (Expr an (Esseq (Pattern pa (CaseBase (none, bty)))
        (ofValA (.annot a1 a2 b1 ds v)) e2))
  | merge {an a2 : List _root_.annot} {ds1 ds2 : List dyn_annotation} {b : CoreExpr}
      (hirr : is_irreducible
        (Expr an (Eannot ds1 (Expr a2 (Eannot ds2 b)))) = false) :
      Redex (Expr an (Eannot ds1 (Expr a2 (Eannot ds2 b))))
  | save {an : List _root_.annot} (sb : sym × core_base_type)
      (ps : List (sym × ((core_base_type ×
        Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)))
      (body : CoreExpr) : Redex (saveRedex an sb ps body)
  | if_ {an : List _root_.annot} (g : generic_pexpr Unit sym) (e2 e3 : CoreExpr) :
      Redex (ifRedex an g e2 e3)
  | case_ {an : List _root_.annot} (pe : generic_pexpr Unit sym) (pats : List (pattern × CoreExpr)) :
      Redex (caseRedex an pe pats)
  | run {an : List _root_.annot} (ra : core_run_annotation) (l : sym)
      (pes : List (generic_pexpr Unit sym)) : Redex (runRedex an ra l pes)
  | pure_e {an : List _root_.annot} {pe : generic_pexpr Unit sym}
      (hnv : valueFromPexpr pe = none) : Redex (pureRedex an pe)
  | load_op {an : List _root_.annot} (loc : CerbLocation.Loc) (ann : core_run_annotation)
      (ty : ctype) {pe2 : generic_pexpr Unit sym} (mo : memory_order)
      (hnv2 : valueFromPexpr pe2 = none) :
      Redex (loadOpRedex an loc ann ty pe2 mo)
  | beta_spec {an pa pb : List _root_.annot} {x : sym} {bty : core_base_type}
      {wa : SpikeValA} {e2 : CoreExpr} :
      Redex (Expr an (Esseq (specPat pa pb x bty) (ofValA wa) e2))
  | memop {an : List _root_.annot} (mop : memop) (pes : List (generic_pexpr Unit sym)) :
      Redex (memopRedex an mop pes)
  | store_op {an : List _root_.annot} (loc : CerbLocation.Loc) (ann : core_run_annotation)
      (ty : ctype) {pe2 pe3 : generic_pexpr Unit sym} (mo : memory_order)
      (hnv : valueFromPexprs [pe2, pe3] = none) :
      Redex (storeOpRedex an loc ann ty pe2 pe3 mo)
  | beta_sym {an pa : List _root_.annot} {x : sym} {bty : core_base_type}
      {wa : SpikeValA} {e2 : CoreExpr} :
      Redex (Expr an (Esseq (symPat pa x bty) (ofValA wa) e2))
  /-- S1b DRIFT TEST: the two Ewseq wildcard betas (LETW-PURE /
      LETW-ANNOT root shapes). -/
  | wbeta_pure {an pa a1 b1 : List _root_.annot} {bty : core_base_type} {v : value}
      {e2 : CoreExpr} :
      Redex (Expr an (Ewseq (Pattern pa (CaseBase (none, bty)))
        (ofValA (.pure a1 b1 v)) e2))
  | wbeta_annot {an pa a1 a2 b1 : List _root_.annot} {bty : core_base_type}
      {ds : List dyn_annotation} {v : value} {e2 : CoreExpr} :
      Redex (Expr an (Ewseq (Pattern pa (CaseBase (none, bty)))
        (ofValA (.annot a1 a2 b1 ds v)) e2))
  /-- The procedure-call redex (calls arc C2): `Eproc` at a Core
      identifier — get_ctx's `| Eproc _ _ _ => [(CTX, expr1)]` root
      (Core_reduction.lean:375). -/
  | call {an : List _root_.annot} (ra : core_run_annotation) (f : sym)
      (pes : List (generic_pexpr Unit sym)) : Redex (callRedex an ra f pes)
  /-- E1: the two REMOVE-BOUND roots (`bound(v)` / `bound({A}v)`,
      core_reduction.lem:1214–1226) — get_ctx's `Ebound` arm roots at
      an irreducible body (Core_reduction.lean:375). -/
  | bound_pure {an a1 b1 : List _root_.annot} {v : value} :
      Redex (Expr an (Ebound (ofValA (.pure a1 b1 v))))
  | bound_annot {an a1 a2 b1 : List _root_.annot} {ds : List dyn_annotation} {v : value} :
      Redex (Expr an (Ebound (ofValA (.annot a1 a2 b1 ds v))))

/-- The extended decomposition: the same layers as get_ctx's arm order
    (Core_reduction.lean:373–381), over the extended root set. Every
    frame carries its node's annotation list (E1: emitted Core annotates
    every node; the annotations are inert for get_ctx). -/
inductive Decomp : CoreExpr → context → CoreExpr → Prop where
  | root {r : CoreExpr} : Redex r → Decomp r CTX r
  | sseq {an pa : List _root_.annot} {bty : core_base_type} {e1 e2 : CoreExpr}
      {ctx : context} {r : CoreExpr} :
      Decomp e1 ctx r →
      Decomp (Expr an (Esseq (Pattern pa (CaseBase (none, bty))) e1 e2))
             (Csseq an (Pattern pa (CaseBase (none, bty))) ctx e2) r
  | sseq_spec {an pa pb : List _root_.annot} {x : sym} {bty : core_base_type}
      {e1 e2 : CoreExpr} {ctx : context} {r : CoreExpr} :
      Decomp e1 ctx r →
      Decomp (Expr an (Esseq (specPat pa pb x bty) e1 e2))
             (Csseq an (specPat pa pb x bty) ctx e2) r
  | sseq_sym {an pa : List _root_.annot} {x : sym} {bty : core_base_type}
      {e1 e2 : CoreExpr} {ctx : context} {r : CoreExpr} :
      Decomp e1 ctx r →
      Decomp (Expr an (Esseq (symPat pa x bty) e1 e2))
             (Csseq an (symPat pa x bty) ctx e2) r
  | annot {an : List _root_.annot} {ds : List dyn_annotation} {b : CoreExpr} {ctx : context}
      {r : CoreExpr}
      (hroot : annotRooted b = false)
      (hirr : is_irreducible (Expr an (Eannot ds b)) = false)
      (hmap : ∀ n : Nat,
        get_ctx_lemFuel (n+1) (Expr an (Eannot ds b)) =
          List.map (fun p => (Cannot an ds p.1, p.2)) (get_ctx_lemFuel n b)) :
      Decomp b ctx r → Decomp (Expr an (Eannot ds b)) (Cannot an ds ctx) r
  /-- S1b DRIFT TEST: descent through the weak-sequencing frame
      (get_ctx's Ewseq arm / Cwseq, Core_reduction.lean:375;
      wildcard pattern only — the mirrored Ewseq fragment). -/
  | wseq {an pa : List _root_.annot} {bty : core_base_type} {e1 e2 : CoreExpr}
      {ctx : context} {r : CoreExpr} :
      Decomp e1 ctx r →
      Decomp (Expr an (Ewseq (Pattern pa (CaseBase (none, bty))) e1 e2))
             (Cwseq an (Pattern pa (CaseBase (none, bty))) ctx e2) r
  /-- E1: descent through the `bound` frame (get_ctx's Ebound arm /
      `Cbound`, core_reduction.lem:563–568). -/
  | bound {an : List _root_.annot} {b : CoreExpr} {ctx : context} {r : CoreExpr} :
      Decomp b ctx r → Decomp (Expr an (Ebound b)) (Cbound an ctx) r

theorem Redex.not_irreducible {r : CoreExpr} (h : Redex r) :
    is_irreducible r = false := by
  cases h with
  | store => rfl
  | load => rfl
  | create => rfl
  | create_op loc ann pref hnv => rfl
  | beta_pure => rfl
  | beta_annot => rfl
  | merge hirr => exact hirr
  | save sb ps body => rfl
  | if_ g e2 e3 => rfl
  | case_ pe pats => rfl
  | run ra l pes => rfl
  | @pure_e an pe hnv =>
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
  | bound_pure => rfl
  | bound_annot => rfl

theorem Decomp.not_irreducible {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (h : Decomp e ctx r) : is_irreducible e = false := by
  induction h with
  | root hr => exact hr.not_irreducible
  | sseq _ _ => rfl
  | sseq_spec _ _ => rfl
  | sseq_sym _ _ => rfl
  | annot _ hirr _ _ _ => exact hirr
  | wseq _ _ => rfl
  | bound _ _ => rfl

/-- No decomposition frame is an unseq-with-ccall (E1: `Cbound` RESETS
    the accumulator — `is_unseq_with_ccall_aux false` at Cbound,
    core_reduction.lem:514 — so the statement is at the `false` start
    value only, which is all `is_unseq_with_ccall` uses). -/
theorem Decomp.unseq_ccall_false {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (h : Decomp e ctx r) : is_unseq_with_ccall ctx = false := by
  have aux : ∀ {e' : CoreExpr} {ctx' : context} {r' : CoreExpr},
      Decomp e' ctx' r' → is_unseq_with_ccall_aux false ctx' = false := by
    intro e' ctx' r' h'
    induction h' with
    | root _ => rfl
    | sseq _ ih => simpa [is_unseq_with_ccall_aux] using ih
    | sseq_spec _ ih => simpa [is_unseq_with_ccall_aux] using ih
    | sseq_sym _ ih => simpa [is_unseq_with_ccall_aux] using ih
    | annot _ _ _ _ ih => simpa [is_unseq_with_ccall_aux] using ih
    | wseq _ ih => simpa [is_unseq_with_ccall_aux] using ih
    | bound _ ih => simpa [is_unseq_with_ccall_aux] using ih
  unfold is_unseq_with_ccall
  exact aux h

theorem Decomp.apply_eq {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (h : Decomp e ctx r) : apply_ctx ctx r = e := by
  induction h with
  | root _ => rfl
  | sseq _ ih => simpa [apply_ctx] using ih
  | sseq_spec _ ih => simpa [apply_ctx] using ih
  | sseq_sym _ ih => simpa [apply_ctx] using ih
  | annot _ _ _ _ ih => simpa [apply_ctx] using ih
  | wseq _ ih => simpa [apply_ctx] using ih
  | bound _ ih => simpa [apply_ctx] using ih

/-- get_ctx roots at the new redexes (Core_reduction.lean:375 — Eif/
    Ecase/Esave/Erun all return `[(CTX, expr1)]`). -/
theorem get_ctx_save {an : List _root_.annot} {sb : sym × core_base_type}
    {ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
    {body : CoreExpr} (n : Nat) :
    get_ctx_lemFuel (n+1) (saveRedex an sb ps body) =
      [(CTX, saveRedex an sb ps body)] := rfl

theorem get_ctx_if {an : List _root_.annot} {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr} (n : Nat) :
    get_ctx_lemFuel (n+1) (ifRedex an g e2 e3) = [(CTX, ifRedex an g e2 e3)] := rfl

theorem get_ctx_case {an : List _root_.annot} {pe : generic_pexpr Unit sym}
    {pats : List (pattern × CoreExpr)} (n : Nat) :
    get_ctx_lemFuel (n+1) (caseRedex an pe pats) = [(CTX, caseRedex an pe pats)] := rfl

theorem get_ctx_run {an : List _root_.annot} {ra : core_run_annotation} {l : sym}
    {pes : List (generic_pexpr Unit sym)} (n : Nat) :
    get_ctx_lemFuel (n+1) (runRedex an ra l pes) = [(CTX, runRedex an ra l pes)] := rfl

theorem get_ctx_pure {an : List _root_.annot} {pe : generic_pexpr Unit sym} (n : Nat) :
    get_ctx_lemFuel (n+1) (pureRedex an pe) = [(CTX, pureRedex an pe)] := by
  rcases pe with ⟨b, u, pe_⟩
  cases u
  cases pe_ <;> rfl

theorem get_ctx_memop {an : List _root_.annot} {mop : memop} {pes : List (generic_pexpr Unit sym)}
    (n : Nat) :
    get_ctx_lemFuel (n+1) (memopRedex an mop pes) =
      [(CTX, memopRedex an mop pes)] := rfl

/-- get_ctx roots at the call redex (Core_reduction.lean:375, `| Eproc
    _ _ _ => [(CTX, expr1)]` — no descent into the arguments). -/
theorem get_ctx_call {an : List _root_.annot} {ra : core_run_annotation} {f : sym}
    {pes : List (generic_pexpr Unit sym)} (n : Nat) :
    get_ctx_lemFuel (n+1) (callRedex an ra f pes) = [(CTX, callRedex an ra f pes)] := rfl

/-- E1: get_ctx's Ebound arm (core_reduction.lem:563–568): descends
    through `bound` at a reducible body … -/
theorem get_ctx_bound {a : List _root_.annot} {b : CoreExpr}
    (h : is_irreducible b = false) (n : Nat) :
    get_ctx_lemFuel (n+1) (Expr a (Ebound b)) =
      List.map (fun p => (Cbound a p.1, p.2)) (get_ctx_lemFuel n b) := by
  rw [show get_ctx_lemFuel (n+1) (Expr a (Ebound b)) =
      (if is_irreducible b = true then [(CTX, Expr a (Ebound b))]
       else List.map (fun p => (Cbound a p.1, p.2)) (get_ctx_lemFuel n b))
    from rfl, h]
  rfl

/-- … and roots at an irreducible one (the REMOVE-BOUND redex). -/
theorem get_ctx_bound_val {a : List _root_.annot} {w : SpikeValA} (n : Nat) :
    get_ctx_lemFuel (n+1) (Expr a (Ebound (ofValA w))) =
      [(CTX, Expr a (Ebound (ofValA w)))] := by
  cases w <;> rfl

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
    | create_op loc ann pref hnv => exact get_ctx_action m
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
    | bound_pure => exact get_ctx_bound_val m
    | bound_annot => exact get_ctx_bound_val m
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
  | bound hd ih =>
    intro n hn
    rw [esize_bound] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [get_ctx_bound hd.not_irreducible m, ih m (by omega)]
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
  | bound _ ih => rw [jumpRedex?_bound]; exact ih

theorem Decomp.redex {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (h : Decomp e ctx r) : Redex r := by
  induction h with
  | root hr => exact hr
  | sseq _ ih => exact ih
  | sseq_spec _ ih => exact ih
  | sseq_sym _ ih => exact ih
  | annot _ _ _ _ ih => exact ih
  | wseq _ ih => exact ih
  | bound _ ih => exact ih

/-- A decomposed term is not a value (values are irreducible;
    `Decomp.not_irreducible`). -/
theorem Decomp.toVal_none {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (hd : Decomp e ctx r) : toVal e = none := by
  cases hv : toVal e with
  | none => rfl
  | some w =>
    obtain ⟨wa, -, rfl⟩ := ofValA_of_toVal hv
    have h1 := hd.not_irreducible
    rw [is_irreducible_ofValA] at h1
    cases h1

/-- E1: the mirror's `redexAnnots` (the annotation list step_ctx's
    general arm reads — `Expr e_annots _` is the REDEX get_ctx pairs
    with its context, Core_reduction.lean:484) is invariant along a
    decomposition: the whole term's redex annotations are the redex's
    own root annotations. -/
theorem Decomp.redexAnnots_eq {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (h : Decomp e ctx r) : redexAnnots e = redexAnnots r := by
  induction h with
  | root _ => rfl
  | sseq hd ih => rw [redexAnnots_sseq_of_nv _ _ _ hd.toVal_none]; exact ih
  | sseq_spec hd ih => rw [redexAnnots_sseq_of_nv _ _ _ hd.toVal_none]; exact ih
  | sseq_sym hd ih => rw [redexAnnots_sseq_of_nv _ _ _ hd.toVal_none]; exact ih
  | annot hroot _ _ _ ih => rw [redexAnnots_annot_of_not_root _ _ hroot]; exact ih
  | wseq hd ih => rw [redexAnnots_wseq_of_nv _ _ _ hd.toVal_none]; exact ih
  | bound hd ih => rw [redexAnnots_bound_of_nv _ hd.toVal_none]; exact ih

/-- A redex with a positive jump-redex answer IS the run redex. -/
theorem Redex.jumpRedex?_some_inv {r : CoreExpr} {l : sym}
    {pes : List (generic_pexpr Unit sym)} (h : Redex r)
    (hj : jumpRedex? r = some (l, pes)) :
    ∃ (an : List _root_.annot) (ra : core_run_annotation), r = runRedex an ra l pes := by
  cases h with
  | store => cases hj
  | load => cases hj
  | create => cases hj
  | create_op loc ann pref hnv => cases hj
  | beta_pure => rw [jumpRedex?_sseq, jumpRedex?_ofValA] at hj; cases hj
  | beta_annot => rw [jumpRedex?_sseq, jumpRedex?_ofValA] at hj; cases hj
  | merge hirr => rw [jumpRedex?_annot_of_root _ _ rfl] at hj; cases hj
  | save sb ps body => cases hj
  | if_ g e2 e3 => cases hj
  | case_ pe pats => cases hj
  | pure_e hnv => cases hj
  | load_op loc ann ty mo hnv2 => cases hj
  | beta_spec => rw [jumpRedex?_sseq, jumpRedex?_ofValA] at hj; cases hj
  | memop mop pes => cases hj
  | store_op loc ann ty mo hnv => cases hj
  | beta_sym => rw [jumpRedex?_sseq, jumpRedex?_ofValA] at hj; cases hj
  | wbeta_pure => rw [jumpRedex?_wseq, jumpRedex?_ofValA] at hj; cases hj
  | wbeta_annot => rw [jumpRedex?_wseq, jumpRedex?_ofValA] at hj; cases hj
  | kill => cases hj
  | kill_op loc ann kind hnv => cases hj
  | alloc => cases hj
  | alloc_op loc ann pref hnv => cases hj
  | call ra f pes => cases hj
  | bound_pure => rw [jumpRedex?_bound, jumpRedex?_ofValA] at hj; cases hj
  | bound_annot => rw [jumpRedex?_bound, jumpRedex?_ofValA] at hj; cases hj
  | @run an ra l' pes' =>
    obtain ⟨rfl, rfl⟩ : l' = l ∧ pes' = pes := by
      have := Option.some.inj hj
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    exact ⟨an, ra, rfl⟩

/-- A redex with a positive call-redex answer IS the call redex, at the
    root context (the `jumpRedex?_some_inv` twin). -/
theorem Redex.callRedex?_some_inv {r : CoreExpr} {ctx : context} {f : sym}
    {pes : List (generic_pexpr Unit sym)} (h : Redex r)
    (hc : callRedex? r = some (ctx, f, pes)) :
    ctx = CTX ∧ ∃ (an : List _root_.annot) (ra : core_run_annotation), r = callRedex an ra f pes := by
  cases h with
  | store => cases hc
  | load => cases hc
  | create => cases hc
  | create_op loc ann pref hnv => cases hc
  | beta_pure => rw [callRedex?_sseq, callRedex?_ofValA] at hc; cases hc
  | beta_annot => rw [callRedex?_sseq, callRedex?_ofValA] at hc; cases hc
  | merge hirr => rw [callRedex?_annot_of_root _ _ rfl] at hc; cases hc
  | save sb ps body => cases hc
  | if_ g e2 e3 => cases hc
  | case_ pe pats => cases hc
  | run ra l pes' => cases hc
  | pure_e hnv => cases hc
  | load_op loc ann ty mo hnv2 => cases hc
  | beta_spec => rw [callRedex?_sseq, callRedex?_ofValA] at hc; cases hc
  | memop mop pes' => cases hc
  | store_op loc ann ty mo hnv => cases hc
  | beta_sym => rw [callRedex?_sseq, callRedex?_ofValA] at hc; cases hc
  | wbeta_pure => rw [callRedex?_wseq, callRedex?_ofValA] at hc; cases hc
  | wbeta_annot => rw [callRedex?_wseq, callRedex?_ofValA] at hc; cases hc
  | kill => cases hc
  | kill_op loc ann kind hnv => cases hc
  | alloc => cases hc
  | alloc_op loc ann pref hnv => cases hc
  | bound_pure => rw [callRedex?_bound, callRedex?_ofValA] at hc; cases hc
  | bound_annot => rw [callRedex?_bound, callRedex?_ofValA] at hc; cases hc
  | @call an ra f' pes' =>
    rw [callRedex?_callRedex] at hc
    obtain ⟨rfl, rfl, rfl⟩ : CTX = ctx ∧ f' = f ∧ pes' = pes := by
      have := Option.some.inj hc
      exact ⟨congrArg Prod.fst this, congrArg (fun q => q.2.1) this,
        congrArg (fun q => q.2.2) this⟩
    exact ⟨rfl, an, ra, rfl⟩

/-- `callRedex?` along an extended decomposition: `some` exactly at a call
    redex, and then the CAPTURED context is the decomposition's context —
    the syntactic search computes what get_ctx pairs the redex with. -/
theorem Decomp.callRedex?_inv {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (hd : Decomp e ctx r) {ctx' : context} {f : sym} {pes : List (generic_pexpr Unit sym)}
    (hc : callRedex? e = some (ctx', f, pes)) :
    ctx' = ctx ∧ ∃ (an : List _root_.annot) (ra : core_run_annotation), r = callRedex an ra f pes := by
  induction hd generalizing ctx' with
  | root hr => exact hr.callRedex?_some_inv hc
  | sseq _ ih =>
    rw [callRedex?_sseq, Option.map_eq_some_iff] at hc
    obtain ⟨⟨c1, f1, pes1⟩, hc1, hq⟩ := hc
    obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
      exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq,
        congrArg (fun q => q.2.2) hq⟩
    obtain ⟨rfl, an, ra, rfl⟩ := ih hc1
    exact ⟨rfl, an, ra, rfl⟩
  | sseq_spec _ ih =>
    rw [callRedex?_sseq, Option.map_eq_some_iff] at hc
    obtain ⟨⟨c1, f1, pes1⟩, hc1, hq⟩ := hc
    obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
      exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq,
        congrArg (fun q => q.2.2) hq⟩
    obtain ⟨rfl, an, ra, rfl⟩ := ih hc1
    exact ⟨rfl, an, ra, rfl⟩
  | sseq_sym _ ih =>
    rw [callRedex?_sseq, Option.map_eq_some_iff] at hc
    obtain ⟨⟨c1, f1, pes1⟩, hc1, hq⟩ := hc
    obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
      exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq,
        congrArg (fun q => q.2.2) hq⟩
    obtain ⟨rfl, an, ra, rfl⟩ := ih hc1
    exact ⟨rfl, an, ra, rfl⟩
  | annot hroot _ _ _ ih =>
    rw [callRedex?_annot_of_not_root _ _ hroot, Option.map_eq_some_iff] at hc
    obtain ⟨⟨c1, f1, pes1⟩, hc1, hq⟩ := hc
    obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
      exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq,
        congrArg (fun q => q.2.2) hq⟩
    obtain ⟨rfl, an, ra, rfl⟩ := ih hc1
    exact ⟨rfl, an, ra, rfl⟩
  | wseq _ ih =>
    rw [callRedex?_wseq, Option.map_eq_some_iff] at hc
    obtain ⟨⟨c1, f1, pes1⟩, hc1, hq⟩ := hc
    obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
      exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq,
        congrArg (fun q => q.2.2) hq⟩
    obtain ⟨rfl, an, ra, rfl⟩ := ih hc1
    exact ⟨rfl, an, ra, rfl⟩
  | bound _ ih =>
    rw [callRedex?_bound, Option.map_eq_some_iff] at hc
    obtain ⟨⟨c1, f1, pes1⟩, hc1, hq⟩ := hc
    obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by
      exact ⟨congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq,
        congrArg (fun q => q.2.2) hq⟩
    obtain ⟨rfl, an, ra, rfl⟩ := ih hc1
    exact ⟨rfl, an, ra, rfl⟩

/-- At a decomposed CALL redex the search answers the decomposition's
    context (the certification of `callRedex?` against get_ctx: the
    captured frame IS get_ctx's). -/
theorem Decomp.callRedex?_some' {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (hd : Decomp e ctx r) {an : List _root_.annot} {ra : core_run_annotation} {f : sym}
    {pes : List (generic_pexpr Unit sym)} (hr : r = callRedex an ra f pes) :
    callRedex? e = some (ctx, f, pes) := by
  induction hd with
  | root _ => subst hr; rfl
  | sseq _ ih => rw [callRedex?_sseq, ih hr]; rfl
  | sseq_spec _ ih => rw [callRedex?_sseq, ih hr]; rfl
  | sseq_sym _ ih => rw [callRedex?_sseq, ih hr]; rfl
  | annot hroot _ _ _ ih => rw [callRedex?_annot_of_not_root _ _ hroot, ih hr]; rfl
  | wseq _ ih => rw [callRedex?_wseq, ih hr]; rfl
  | bound _ ih => rw [callRedex?_bound, ih hr]; rfl

theorem Decomp.callRedex?_some {e : CoreExpr} {ctx : context} {an : List _root_.annot}
    {ra : core_run_annotation} {f : sym} {pes : List (generic_pexpr Unit sym)}
    (hd : Decomp e ctx (callRedex an ra f pes)) :
    callRedex? e = some (ctx, f, pes) :=
  hd.callRedex?_some' rfl

/-- At a decomposed NON-call redex the search answers `none`. -/
theorem Decomp.callRedex?_none {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (hd : Decomp e ctx r)
    (hnr : ∀ (an : List _root_.annot) (ra : core_run_annotation) (f : sym)
      (pes : List (generic_pexpr Unit sym)), r ≠ callRedex an ra f pes) :
    callRedex? e = none := by
  cases hc : callRedex? e with
  | none => rfl
  | some q =>
    obtain ⟨ctx', f, pes⟩ := q
    obtain ⟨-, an, ra, hr⟩ := hd.callRedex?_inv hc
    exact absurd hr (hnr an ra f pes)

/-- THE FACTOR THEOREM WITH THE JUMP AND CALL DISJUNCTS (readiness R1):
    a step of a decomposed term is EITHER a step of its redex REBUILT in
    context (the phase-1 shape; E1: the control — current location
    included — is whatever the redex's own step produces), OR the redex
    is a registered jump and the step is the redex's OWN step (the
    context is DISCARDED), OR the redex is a procedure call and the
    decomposition's context is what gets PUSHED (`Ctl.callPush` at the
    redex's root annotations). -/
theorem Decomp.step_factor {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {r : CoreExpr} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    {out : Config}
    (h : Decomp e ctx r) (hs : Step M (e, ρ, ctl, σ) out) :
    (∃ r' ρ' ctl' σ', (∀ (an : List _root_.annot) (ra : core_run_annotation) (l : sym)
        (pes : List (generic_pexpr Unit sym)), r ≠ runRedex an ra l pes) ∧
      (∀ (an : List _root_.annot) (ra : core_run_annotation) (f : sym)
        (pes : List (generic_pexpr Unit sym)), r ≠ callRedex an ra f pes) ∧
      Step M (r, ρ, ctl, σ) (r', ρ', ctl', σ') ∧
      out = (apply_ctx ctx r', ρ', ctl', σ')) ∨
    (∃ (an : List _root_.annot) (ra : core_run_annotation) (l : sym)
      (pes : List (generic_pexpr Unit sym)),
      r = runRedex an ra l pes ∧ Step M (r, ρ, ctl, σ) out) ∨
    (∃ (an : List _root_.annot) (ra : core_run_annotation) (f : sym)
      (pes : List (generic_pexpr Unit sym))
      (params : List (sym × core_base_type)) (body : CoreExpr) (vs : List value),
      r = callRedex an ra f pes ∧
      evalPexprs M.tagDefs M.extern ρ pes = some vs ∧
      lookupProc M.file M.extern f = some (params, body) ∧ params.length = vs.length ∧
      out = (body, procEnv params vs :: ρ, ctl.callPush an ctx f, σ)) := by
  induction h generalizing out with
  | @root r hr =>
    by_cases hrun : ∃ (an : List _root_.annot) (ra : core_run_annotation) (l : sym)
        (pes : List (generic_pexpr Unit sym)), r = runRedex an ra l pes
    · obtain ⟨an, ra, l, pes, rfl⟩ := hrun
      exact .inr (.inl ⟨an, ra, l, pes, rfl, hs⟩)
    by_cases hcall : ∃ (an : List _root_.annot) (ra : core_run_annotation) (f : sym)
        (pes : List (generic_pexpr Unit sym)), r = callRedex an ra f pes
    · obtain ⟨an, ra, f, pes, rfl⟩ := hcall
      obtain ⟨params, body, vs, hvs, hf, hlen, hout⟩ :=
        hs.call_inv (callRedex?_callRedex an ra f pes)
      rw [redexAnnots_callRedex] at hout
      exact .inr (.inr ⟨an, ra, f, pes, params, body, vs, rfl, hvs, hf, hlen, hout⟩)
    · obtain ⟨oe, oρ, octl, oσ⟩ := out
      exact .inl ⟨oe, oρ, octl, oσ, fun an ra l pes hr => hrun ⟨an, ra, l, pes, hr⟩,
        fun an ra f pes hr => hcall ⟨an, ra, f, pes, hr⟩, hs, rfl⟩
  | @sseq an pa bty e1 e2 ctx' r' hd ih =>
    rcases hs.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv, hstep, hout⟩ |
        ⟨_, _, _, _, v, _, _, _, he1, _, _⟩ | ⟨_, _, _, _, _, ds, v, _, _, _, he1, _, _⟩ |
        ⟨l, pes, params, cont, vs, ev0, evs, hj, hρ, hl, hvs, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
        hcall
    · rcases ih hstep with ⟨r2, ρr, ctlr, σr, hnr2, hnc2, hr2, heq⟩ |
          ⟨an', ra, l, pes, rfl, hr2⟩ | ⟨an', ra, f, pes, params, body, vs, rfl, -, -, -, -⟩
      · obtain ⟨he, hρ2, hc2, hσ2⟩ : e1' = apply_ctx _ r2 ∧ ρ'' = ρr ∧ ctl'' = ctlr ∧
            σ'' = σr := by
          simpa [Prod.mk.injEq] using heq
        subst he hρ2 hc2 hσ2
        exact .inl ⟨r2, _, _, _, hnr2, hnc2, hr2, by rw [hout]; rfl⟩
      · rw [hd.jumpRedex?_eq] at hnj
        rw [show jumpRedex? (runRedex an' ra l pes) = some (l, pes) from rfl]
          at hnj
        cases hnj
      · rw [hd.callRedex?_some] at hnc'
        cases hnc'
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by rw [is_irreducible_ofValA]; simp)
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by rw [is_irreducible_ofValA]; simp)
    · -- the node's step IS the jump: the decomposed redex must be
      -- the run redex, and its own step has the SAME successor
      have hje : jumpRedex? r' = some (l, pes) := by
        rw [← hd.jumpRedex?_eq]; exact hj
      obtain ⟨an', ra, rfl⟩ := hd.redex.jumpRedex?_some_inv hje
      subst hρ
      rw [hout, hd.redexAnnots_eq]
      exact .inr (.inl ⟨an', ra, l, pes, rfl, Step.run (by rfl) hl hvs⟩)
    · exact (specPat_ne_base hpat).elim
    · exact (specPat_ne_base hpat).elim
    · exact (symPat_ne_base hpat).elim
    · exact (symPat_ne_base hpat).elim
    · exact (tuplePat_ne_base hpatT1).elim
    · exact (tuplePat_ne_base hpatT2).elim
    · obtain ⟨ctx1, f, pes, params, body, vs, hc1, hvs, hf, hlen, hout⟩ := hcall
      obtain ⟨rfl, an', ra, rfl⟩ := hd.callRedex?_inv hc1
      rw [hd.redexAnnots_eq,
        redexAnnots_callRedex] at hout
      exact .inr (.inr ⟨an', ra, f, pes, params, body, vs, rfl, hvs, hf, hlen, hout⟩)
  | @sseq_spec an pa pb x bty e1 e2 ctx' r' hd ih =>
    rcases hs.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv, hstep, hout⟩ |
        ⟨_, _, _, _, v, _, _, _, he1, _, _⟩ | ⟨_, _, _, _, _, ds, v, _, _, _, he1, _, _⟩ |
        ⟨l, pes, params, cont, vs, ev0, evs, hj, hρ, hl, hvs, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, he1, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, he1, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, he1, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, he1, _, _⟩ |
        ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
        hcall
    · rcases ih hstep with ⟨r2, ρr, ctlr, σr, hnr2, hnc2, hr2, heq⟩ |
          ⟨an', ra, l, pes, rfl, hr2⟩ | ⟨an', ra, f, pes, params, body, vs, rfl, -, -, -, -⟩
      · obtain ⟨he, hρ2, hc2, hσ2⟩ : e1' = apply_ctx _ r2 ∧ ρ'' = ρr ∧ ctl'' = ctlr ∧
            σ'' = σr := by
          simpa [Prod.mk.injEq] using heq
        subst he hρ2 hc2 hσ2
        exact .inl ⟨r2, _, _, _, hnr2, hnc2, hr2, by rw [hout]; rfl⟩
      · rw [hd.jumpRedex?_eq] at hnj
        rw [show jumpRedex? (runRedex an' ra l pes) = some (l, pes) from rfl]
          at hnj
        cases hnj
      · rw [hd.callRedex?_some] at hnc'
        cases hnc'
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by rw [is_irreducible_ofValA]; simp)
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by rw [is_irreducible_ofValA]; simp)
    · have hje : jumpRedex? r' = some (l, pes) := by
        rw [← hd.jumpRedex?_eq]; exact hj
      obtain ⟨an', ra, rfl⟩ := hd.redex.jumpRedex?_some_inv hje
      subst hρ
      rw [hout, hd.redexAnnots_eq]
      exact .inr (.inl ⟨an', ra, l, pes, rfl, Step.run (by rfl) hl hvs⟩)
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by rw [is_irreducible_ofValA]; simp)
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by rw [is_irreducible_ofValA]; simp)
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by rw [is_irreducible_ofValA]; simp)
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by rw [is_irreducible_ofValA]; simp)
    · exact (specPat_ne_tuple hpatT1).elim
    · exact (specPat_ne_tuple hpatT2).elim
    · obtain ⟨ctx1, f, pes, params, body, vs, hc1, hvs, hf, hlen, hout⟩ := hcall
      obtain ⟨rfl, an', ra, rfl⟩ := hd.callRedex?_inv hc1
      rw [hd.redexAnnots_eq,
        redexAnnots_callRedex] at hout
      exact .inr (.inr ⟨an', ra, f, pes, params, body, vs, rfl, hvs, hf, hlen, hout⟩)
  | @sseq_sym an pa x bty e1 e2 ctx' r' hd ih =>
    rcases hs.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv, hstep, hout⟩ |
        ⟨_, _, _, _, v, _, _, _, he1, _, _⟩ | ⟨_, _, _, _, _, ds, v, _, _, _, he1, _, _⟩ |
        ⟨l, pes, params, cont, vs, ev0, evs, hj, hρ, hl, hvs, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, he1, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, he1, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, he1, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, he1, _, _⟩ |
        ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
        hcall
    · rcases ih hstep with ⟨r2, ρr, ctlr, σr, hnr2, hnc2, hr2, heq⟩ |
          ⟨an', ra, l, pes, rfl, hr2⟩ | ⟨an', ra, f, pes, params, body, vs, rfl, -, -, -, -⟩
      · obtain ⟨he, hρ2, hc2, hσ2⟩ : e1' = apply_ctx _ r2 ∧ ρ'' = ρr ∧ ctl'' = ctlr ∧
            σ'' = σr := by
          simpa [Prod.mk.injEq] using heq
        subst he hρ2 hc2 hσ2
        exact .inl ⟨r2, _, _, _, hnr2, hnc2, hr2, by rw [hout]; rfl⟩
      · rw [hd.jumpRedex?_eq] at hnj
        rw [show jumpRedex? (runRedex an' ra l pes) = some (l, pes) from rfl]
          at hnj
        cases hnj
      · rw [hd.callRedex?_some] at hnc'
        cases hnc'
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by rw [is_irreducible_ofValA]; simp)
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by rw [is_irreducible_ofValA]; simp)
    · have hje : jumpRedex? r' = some (l, pes) := by
        rw [← hd.jumpRedex?_eq]; exact hj
      obtain ⟨an', ra, rfl⟩ := hd.redex.jumpRedex?_some_inv hje
      subst hρ
      rw [hout, hd.redexAnnots_eq]
      exact .inr (.inl ⟨an', ra, l, pes, rfl, Step.run (by rfl) hl hvs⟩)
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by rw [is_irreducible_ofValA]; simp)
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by rw [is_irreducible_ofValA]; simp)
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by rw [is_irreducible_ofValA]; simp)
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by rw [is_irreducible_ofValA]; simp)
    · exact (symPat_ne_tuple hpatT1).elim
    · exact (symPat_ne_tuple hpatT2).elim
    · obtain ⟨ctx1, f, pes, params, body, vs, hc1, hvs, hf, hlen, hout⟩ := hcall
      obtain ⟨rfl, an', ra, rfl⟩ := hd.callRedex?_inv hc1
      rw [hd.redexAnnots_eq,
        redexAnnots_callRedex] at hout
      exact .inr (.inr ⟨an', ra, f, pes, params, body, vs, rfl, hvs, hf, hlen, hout⟩)
  | @wseq an pa bty e1 e2 ctx' r' hd ih =>
    rcases hs.wseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv, hstep, hout⟩ |
        ⟨_, _, _, _, v, _, _, _, he1, _, _⟩ | ⟨_, _, _, _, _, ds, v, _, _, _, he1, _, _⟩ |
        ⟨l, pes, params, cont, vs, ev0, evs, hj, hρ, hl, hvs, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpatS1, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, hpatS2, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
        hcall
    · rcases ih hstep with ⟨r2, ρr, ctlr, σr, hnr2, hnc2, hr2, heq⟩ |
          ⟨an', ra, l, pes, rfl, hr2⟩ | ⟨an', ra, f, pes, params, body, vs, rfl, -, -, -, -⟩
      · obtain ⟨he, hρ2, hc2, hσ2⟩ : e1' = apply_ctx _ r2 ∧ ρ'' = ρr ∧ ctl'' = ctlr ∧
            σ'' = σr := by
          simpa [Prod.mk.injEq] using heq
        subst he hρ2 hc2 hσ2
        exact .inl ⟨r2, _, _, _, hnr2, hnc2, hr2, by rw [hout]; rfl⟩
      · rw [hd.jumpRedex?_eq] at hnj
        rw [show jumpRedex? (runRedex an' ra l pes) = some (l, pes) from rfl]
          at hnj
        cases hnj
      · rw [hd.callRedex?_some] at hnc'
        cases hnc'
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by rw [is_irreducible_ofValA]; simp)
    · rw [he1] at hd
      exact absurd hd.not_irreducible (by rw [is_irreducible_ofValA]; simp)
    · have hje : jumpRedex? r' = some (l, pes) := by
        rw [← hd.jumpRedex?_eq]; exact hj
      obtain ⟨an', ra, rfl⟩ := hd.redex.jumpRedex?_some_inv hje
      subst hρ
      rw [hout, hd.redexAnnots_eq]
      exact .inr (.inl ⟨an', ra, l, pes, rfl, Step.run (by rfl) hl hvs⟩)
    · exact (symPat_ne_base hpatS1).elim
    · exact (symPat_ne_base hpatS2).elim
    · exact (tuplePat_ne_base hpatT1).elim
    · exact (tuplePat_ne_base hpatT2).elim
    · obtain ⟨ctx1, f, pes, params, body, vs, hc1, hvs, hf, hlen, hout⟩ := hcall
      obtain ⟨rfl, an', ra, rfl⟩ := hd.callRedex?_inv hc1
      rw [hd.redexAnnots_eq,
        redexAnnots_callRedex] at hout
      exact .inr (.inr ⟨an', ra, f, pes, params, body, vs, rfl, hvs, hf, hlen, hout⟩)
  | @annot an ds b ctx' r' hroot hirr hmap hd ih =>
    rcases hs.annot_inv with ⟨_, hnj, hnc', hnv, b', ρ'', ctl'', σ'', hstep, hout⟩ |
        ⟨a2, ds2, c, hb, _⟩ |
        ⟨l, pes, params, cont, vs, ev0, evs, hg, hj, hρ, hl, hvs, hout⟩ |
        ⟨-, hcall⟩ | ⟨a2, b1, v, pc, κ, hb, -, -⟩
    · rcases ih hstep with ⟨r2, ρr, ctlr, σr, hnr2, hnc2, hr2, heq⟩ |
          ⟨an', ra, l, pes, rfl, hr2⟩ | ⟨an', ra, f, pes, params, body, vs, rfl, -, -, -, -⟩
      · obtain ⟨he, hρ2, hc2, hσ2⟩ : b' = apply_ctx _ r2 ∧ ρ'' = ρr ∧ ctl'' = ctlr ∧
            σ'' = σr := by
          simpa [Prod.mk.injEq] using heq
        subst he hρ2 hc2 hσ2
        exact .inl ⟨r2, _, _, _, hnr2, hnc2, hr2, by rw [hout]; rfl⟩
      · rw [hd.jumpRedex?_eq] at hnj
        rw [show jumpRedex? (runRedex an' ra l pes) = some (l, pes) from rfl]
          at hnj
        cases hnj
      · rw [hd.callRedex?_some] at hnc'
        cases hnc'
    · rw [hb] at hroot
      simp [annotRooted] at hroot
    · have hje : jumpRedex? r' = some (l, pes) := by
        rw [← hd.jumpRedex?_eq]; exact hj
      obtain ⟨an', ra, rfl⟩ := hd.redex.jumpRedex?_some_inv hje
      subst hρ
      rw [hout, hd.redexAnnots_eq]
      exact .inr (.inl ⟨an', ra, l, pes, rfl, Step.run (by rfl) hl hvs⟩)
    · obtain ⟨ctx1, f, pes, params, body, vs, hc1, hvs, hf, hlen, hout⟩ := hcall
      obtain ⟨rfl, an', ra, rfl⟩ := hd.callRedex?_inv hc1
      rw [hd.redexAnnots_eq,
        redexAnnots_callRedex] at hout
      exact .inr (.inr ⟨an', ra, f, pes, params, body, vs, rfl, hvs, hf, hlen, hout⟩)
    · rw [hb] at hd
      exact absurd hd.not_irreducible (by rw [is_irreducible_ofValA]; simp)
  | @bound an b ctx' r' hd ih =>
    rcases hs.bound_inv with ⟨b', ρ'', ctl'', σ'', hnj, hnc', hnv, hstep, hout⟩ |
        ⟨_, _, v, hb, _⟩ | ⟨_, _, _, ds, v, hb, _⟩ |
        ⟨l, pes, params, cont, vs, ev0, evs, hj, hρ, hl, hvs, hout⟩ |
        hcall
    · rcases ih hstep with ⟨r2, ρr, ctlr, σr, hnr2, hnc2, hr2, heq⟩ |
          ⟨an', ra, l, pes, rfl, hr2⟩ | ⟨an', ra, f, pes, params, body, vs, rfl, -, -, -, -⟩
      · obtain ⟨he, hρ2, hc2, hσ2⟩ : b' = apply_ctx _ r2 ∧ ρ'' = ρr ∧ ctl'' = ctlr ∧
            σ'' = σr := by
          simpa [Prod.mk.injEq] using heq
        subst he hρ2 hc2 hσ2
        exact .inl ⟨r2, _, _, _, hnr2, hnc2, hr2, by rw [hout]; rfl⟩
      · rw [hd.jumpRedex?_eq] at hnj
        rw [show jumpRedex? (runRedex an' ra l pes) = some (l, pes) from rfl]
          at hnj
        cases hnj
      · rw [hd.callRedex?_some] at hnc'
        cases hnc'
    · rw [hb] at hd
      exact absurd hd.not_irreducible (by rw [is_irreducible_ofValA]; simp)
    · rw [hb] at hd
      exact absurd hd.not_irreducible (by rw [is_irreducible_ofValA]; simp)
    · have hje : jumpRedex? r' = some (l, pes) := by
        rw [← hd.jumpRedex?_eq]; exact hj
      obtain ⟨an', ra, rfl⟩ := hd.redex.jumpRedex?_some_inv hje
      subst hρ
      rw [hout, hd.redexAnnots_eq]
      exact .inr (.inl ⟨an', ra, l, pes, rfl, Step.run (by rfl) hl hvs⟩)
    · obtain ⟨ctx1, f, pes, params, body, vs, hc1, hvs, hf, hlen, hout⟩ := hcall
      obtain ⟨rfl, an', ra, rfl⟩ := hd.callRedex?_inv hc1
      rw [hd.redexAnnots_eq,
        redexAnnots_callRedex] at hout
      exact .inr (.inr ⟨an', ra, f, pes, params, body, vs, rfl, hvs, hf, hlen, hout⟩)

/-- PROGRAM-DONE, context undisturbed: at a bare value the engine
    reports the value. Reads exactly stack0 (`hstack`: an empty call
    stack selects PROGRAM-DONE over RETURN) and the parent slot
    (`none` selects it over THREAD-DONE). -/
theorem step_ctx_done {a b : List _root_.annot} (v : value)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (th : thread_state)
    (harena : th.arena = ofValA (.pure a b v))
    (hstack : th.stack0 = Stack_empty) :
    step_ctx tds σ file ext tid (none, th) = [Step_done2 v] := by
  have hget : get_ctx th.arena = [(CTX, Expr a (Epure (Pexpr b () (PEval v))))] := by
    rw [harena]; exact get_ctx_ofValA (.pure a b v) 999999
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  rw [hstack]

/-- REMOVE-ANNOT, context undisturbed: the engine taus off the
    one-layer annotation of a value (a VALUE for Step — D1). Nothing
    else is read. -/
theorem step_ctx_remove_annot {a a2 b : List _root_.annot} (ds : List dyn_annotation) (v : value)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = ofValA (.annot a a2 b ds v)) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_tau2 "CTX, Eannot(value)" TSK_Misc
        { th with arena := ofValA (.pure a2 b v) }] := by
  have hget : get_ctx th.arena =
      [(CTX, Expr a (Eannot ds (Expr a2 (Epure (Pexpr b () (PEval v))))))] := by
    rw [harena]; exact get_ctx_ofValA (.annot a a2 b ds v) 999999
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
theorem step_ctx_ret {a b : List _root_.annot} (v : value)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = ofValA (.pure a b v))
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
            arena := apply_ctx ctx (ofValA (.pure a [] v)) }] := by
  have hget : get_ctx th.arena = [(CTX, Expr a (Epure (Pexpr b () (PEval v))))] := by
    rw [harena]; exact get_ctx_ofValA (.pure a b v) 999999
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  rw [hstack, henv]
  exact ⟨_, rfl⟩

/-- E1 PROOF DEVICE: split the general arm's location write. step_ctx's
    `let th_st := match get_loc e_annots with | none => th_st | some loc1 =>
    if isLibraryLocation loc1 then th_st else {th_st with current_loc :=
    loc1}` (Core_reduction.lean:484) is `locUpdTh an th` (Step.lean) —
    the same match, so both sides are split together: after the device
    the thread on both sides is `th` (no location / a library location)
    or `{ th with current_loc := loc1 }`. -/
theorem get_loc_cases (an : List _root_.annot) :
    (∃ l, get_loc an = some l ∧ CerbLocation.isLibraryLocation l = true) ∨
    (∃ l, get_loc an = some l ∧ CerbLocation.isLibraryLocation l = false) ∨
    (get_loc an = none ∧ (true : Bool) = true) := by
  cases h : get_loc an with
  | none => exact .inr (.inr ⟨rfl, rfl⟩)
  | some l =>
    cases hl : CerbLocation.isLibraryLocation l with
    | true => exact .inl ⟨l, rfl, hl⟩
    | false => exact .inr (.inl ⟨l, rfl, hl⟩)

syntax "loc_split" ident : tactic
macro_rules
  | `(tactic| loc_split $an:ident) =>
    `(tactic| (rcases get_loc_cases $an with ⟨loc1, hgl, hlib⟩ | ⟨loc1, hgl, hlib⟩ | ⟨hgl, hlib⟩ <;>
               simp only [locUpdTh, hgl, hlib, Bool.false_eq_true, ↓reduceIte]))

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
    engine's `requestLoc (locUpdTh an th) loc`, the continuation rebuilds
    `{DA_pos [] fp} unit` in context with the whole thread context
    verbatim. tagDefs is READ (the operand encoding premise `hmv` is
    stated at the quantified tagDefs); `current_loc` is read into the
    request location only. -/
theorem step_ctx_store {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
    {ty : ctype} {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
    {mv : CerbMem.MemValue}
    (hd : Decomp e ctx (storeRedex an loc ann lk ty pv cv mo))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition))
    (hmv : memValueFromValue tds (Ctype [] (unatomic_ ty)) cv = some mv)
    (σ : Mem) (file : generic_file Unit core_run_annotation)
    (ext : Fmap sym sym) (tid : Nat) (parent : Option Nat)
    (th : thread_state) (harena : th.arena = e) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_action_request2 "StoreRequest" (requestLoc (locUpdTh an th) loc) tid (is_unseq_with_ccall ctx)
        (stExceptUndef_return (StoreRequest2 mo ty lk pv mv
          (fun (_ : Nat) (fp : CerbMem.Footprint) =>
            { locUpdTh an th with arena := apply_ctx ctx (Expr [] (Eannot [DA_pos [] fp]
                (Expr [] (Epure (Pexpr [] () (PEval Vunit)))))) })))] := by
  have hget : get_ctx th.arena = [(ctx, storeRedex an loc ann lk ty pv cv mo)] := by
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
theorem step_ctx_store_illtyped {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
    {ty : ctype} {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
    (hd : Decomp e ctx (storeRedex an loc ann lk ty pv cv mo))
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
  have hget : get_ctx th.arena = [(ctx, storeRedex an loc ann lk ty pv cv mo)] := by
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
theorem step_ctx_load {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pv : CerbMem.PointerValue} {mo : memory_order}
    (hd : Decomp e ctx (loadRedex an loc ann ty pv mo))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat)
    (th : thread_state) (harena : th.arena = e) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_action_request2 "LoadRequest" (requestLoc (locUpdTh an th) loc) tid (is_unseq_with_ccall ctx)
        (stExceptUndef_return (LoadRequest2 mo ty pv
          (fun (_ : Nat) (fp : CerbMem.Footprint) (mval : CerbMem.MemValue) =>
            { locUpdTh an th with arena := apply_ctx ctx (Expr [] (Eannot [DA_pos [] fp]
                (Expr [] (Epure (Pexpr [] () (PEval
                  (valueFromMemValue mval).2)))))) })))] := by
  have hget : get_ctx th.arena = [(ctx, loadRedex an loc ann ty pv mo)] := by
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
    (`requestLoc (locUpdTh an th) loc`) only. The request carries `get_with_address []` (the fragment's `[]` node annots) as
    the requested address — an opaque `partial def` value that
    `allocateObject` discards (CerbMem.lean:1473). -/
theorem step_ctx_create {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {align : CerbMem.IntegerValue} {ty : ctype} {pref : prefix0}
    (hd : Decomp e ctx (createRedex an loc ann align ty pref))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat)
    (th : thread_state) (harena : th.arena = e) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_action_request2 "CreateRequest" (requestLoc (locUpdTh an th) loc) tid (is_unseq_with_ccall ctx)
        (stExceptUndef_return (CreateRequest2 pref align ty
          (get_with_address an) none
          (fun (_ : Nat) (pv : CerbMem.PointerValue) =>
            { locUpdTh an th with arena := apply_ctx ctx (Expr [] (Epure (Pexpr [] ()
                (PEval (Vobject (OVpointer pv)))))) })))] := by
  have hget : get_ctx th.arena = [(ctx, createRedex an loc ann align ty pref)] := by
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
    location (`requestLoc (locUpdTh an th) loc`) only; the `Static0 ty` payload is
    discarded — only `is_dynamic kind` reaches the request. -/
theorem step_ctx_kill {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {kind : kill_kind} {pv : CerbMem.PointerValue}
    (hd : Decomp e ctx (killRedex an loc ann kind pv))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat)
    (th : thread_state) (harena : th.arena = e) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_action_request2 "KillRequest" (requestLoc (locUpdTh an th) loc) tid (is_unseq_with_ccall ctx)
        (stExceptUndef_return (KillRequest2 (is_dynamic kind) pv
          (fun (_ : Nat) =>
            { locUpdTh an th with arena := apply_ctx ctx (Expr [] (Epure (Pexpr [] ()
                (PEval Vunit)))) })))] := by
  have hget : get_ctx th.arena = [(ctx, killRedex an loc ann kind pv)] := by
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
    `current_loc` is read into the request location (`requestLoc (locUpdTh an th) loc`)
    only. -/
theorem step_ctx_alloc {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {align size : CerbMem.IntegerValue} {pref : prefix0}
    (hd : Decomp e ctx (allocRedex an loc ann align size pref))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat)
    (th : thread_state) (harena : th.arena = e) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_action_request2 "AllocRequest" (requestLoc (locUpdTh an th) loc) tid (is_unseq_with_ccall ctx)
        (stExceptUndef_return (AllocRequest2 pref align size
          (fun (_ : Nat) (pv : CerbMem.PointerValue) =>
            { locUpdTh an th with arena := apply_ctx ctx (Expr [] (Epure (Pexpr [] ()
                (PEval (Vobject (OVpointer pv)))))) })))] := by
  have hget : get_ctx th.arena = [(ctx, allocRedex an loc ann align size pref)] := by
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
theorem step_ctx_beta_pure {an a1 b1 : List _root_.annot} {e : CoreExpr} {ctx : context}
    {pa : List _root_.annot} {bty : core_base_type} {v : value} {e2 : CoreExpr}
    (hd : Decomp e ctx
      (Expr an (Esseq (Pattern pa (CaseBase (none, bty))) (ofValA (.pure a1 b1 v)) e2)))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    (henv : th.env = ev0 :: evs) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_tau2 "Esseq" TSK_Misc { locUpdTh an th with arena := apply_ctx ctx e2 }] := by
  have hget : get_ctx th.arena =
      [(ctx, Expr an (Esseq (Pattern pa (CaseBase (none, bty)))
        (ofValA (.pure a1 b1 v)) e2))] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  cases ctx <;>
    (simp only [one_step0, ofValA, is_irreducible_sseq, Bool.false_eq_true,
       if_false, valueFromPexpr]
     loc_split an) <;>
    (dsimp only [update_env]
     rw [henv]
     try dsimp only
     try rw [show ∀ cval, update_env_aux (a := sym)
         (Pattern pa (CaseBase (none, bty))) cval ev0 = ev0 from fun _ => rfl]
     try rw [← henv]
     try rfl)

/-- LETS-ANNOT, context undisturbed (same env discipline). -/
theorem step_ctx_beta_annot {an a1 a2 b1 : List _root_.annot} {e : CoreExpr} {ctx : context}
    {pa : List _root_.annot} {bty : core_base_type}
    {ds : List dyn_annotation} {v : value} {e2 : CoreExpr}
    (hd : Decomp e ctx
      (Expr an (Esseq (Pattern pa (CaseBase (none, bty)))
        (ofValA (.annot a1 a2 b1 ds v)) e2)))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    (henv : th.env = ev0 :: evs) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_tau2 "Esseq Eannot" TSK_Misc
        { locUpdTh an th with arena := apply_ctx ctx (Expr [] (Eannot ds e2)) }] := by
  have hget : get_ctx th.arena =
      [(ctx, Expr an (Esseq (Pattern pa (CaseBase (none, bty)))
        (ofValA (.annot a1 a2 b1 ds v)) e2))] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  cases ctx <;>
    (simp only [one_step0, ofValA, is_irreducible_sseq, Bool.false_eq_true,
       if_false, valueFromPexpr]
     loc_split an) <;>
    (dsimp only [update_env]
     rw [henv]
     try dsimp only
     try rw [show ∀ cval, update_env_aux (a := sym)
         (Pattern pa (CaseBase (none, bty))) cval ev0 = ev0 from fun _ => rfl]
     try rw [← henv]
     try rfl)

/-- LETW-PURE, context undisturbed (S1b DRIFT TEST — the
    `step_ctx_beta_pure` clone at the Ewseq wildcard redex; one_step0
    Ewseq bare-value arm, Core_reduction.lean:353 "reduction:
    LETW-PURE", tau label "Ewseq"). Same env discipline. -/
theorem step_ctx_wseq_pure {an a1 b1 : List _root_.annot} {e : CoreExpr} {ctx : context}
    {pa : List _root_.annot} {bty : core_base_type} {v : value} {e2 : CoreExpr}
    (hd : Decomp e ctx
      (Expr an (Ewseq (Pattern pa (CaseBase (none, bty))) (ofValA (.pure a1 b1 v)) e2)))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    (henv : th.env = ev0 :: evs) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_tau2 "Ewseq" TSK_Misc { locUpdTh an th with arena := apply_ctx ctx e2 }] := by
  have hget : get_ctx th.arena =
      [(ctx, Expr an (Ewseq (Pattern pa (CaseBase (none, bty)))
        (ofValA (.pure a1 b1 v)) e2))] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  cases ctx <;>
    (simp only [one_step0, ofValA, is_irreducible_wseq, Bool.false_eq_true,
       if_false, valueFromPexpr]
     loc_split an) <;>
    (dsimp only [update_env]
     rw [henv]
     try dsimp only
     try rw [show ∀ cval, update_env_aux (a := sym)
         (Pattern pa (CaseBase (none, bty))) cval ev0 = ev0 from fun _ => rfl]
     try rw [← henv]
     try rfl)

/-- LETW-ANNOT, context undisturbed (S1b DRIFT TEST; tau label
    "Ewseq Eannot"). -/
theorem step_ctx_wseq_annot {an a1 a2 b1 : List _root_.annot} {e : CoreExpr} {ctx : context}
    {pa : List _root_.annot} {bty : core_base_type}
    {ds : List dyn_annotation} {v : value} {e2 : CoreExpr}
    (hd : Decomp e ctx
      (Expr an (Ewseq (Pattern pa (CaseBase (none, bty)))
        (ofValA (.annot a1 a2 b1 ds v)) e2)))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    (henv : th.env = ev0 :: evs) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_tau2 "Ewseq Eannot" TSK_Misc
        { locUpdTh an th with arena := apply_ctx ctx (Expr [] (Eannot ds e2)) }] := by
  have hget : get_ctx th.arena =
      [(ctx, Expr an (Ewseq (Pattern pa (CaseBase (none, bty)))
        (ofValA (.annot a1 a2 b1 ds v)) e2))] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  cases ctx <;>
    (simp only [one_step0, ofValA, is_irreducible_wseq, Bool.false_eq_true,
       if_false, valueFromPexpr]
     loc_split an) <;>
    (dsimp only [update_env]
     rw [henv]
     try dsimp only
     try rw [show ∀ cval, update_env_aux (a := sym)
         (Pattern pa (CaseBase (none, bty))) cval ev0 = ev0 from fun _ => rfl]
     try rw [← henv]
     try rfl)

/-- ANNOTS merge, context undisturbed: env is returned verbatim with
    NO premise (one_step0's Eannot arm never touches it). -/
theorem step_ctx_merge {an a2 : List _root_.annot} {e : CoreExpr} {ctx : context}
    {ds1 ds2 : List dyn_annotation} {b : CoreExpr}
    (hd : Decomp e ctx (Expr an (Eannot ds1 (Expr a2 (Eannot ds2 b)))))
    (hirr : is_irreducible (Expr an (Eannot ds1 (Expr a2 (Eannot ds2 b)))) = false)
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_tau2 "Eannot" TSK_Misc
        { locUpdTh an th with arena := apply_ctx ctx (Expr (an ++ a2) (Eannot (ds1 ++ ds2) b)) }] := by
  have hget : get_ctx th.arena =
      [(ctx, Expr an (Eannot ds1 (Expr a2 (Eannot ds2 b))))] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  cases ctx <;>
    (dsimp only [one_step0]
     rw [hirr]
     rfl)


/-- E1: REMOVE-BOUND at a bare value, context undisturbed (step_ctx's
    general-arm `Ebound (expr'@(Expr _ (Epure (Pexpr _ _ (PEval _)))))`
    arm, core_reduction.lem:1220–1226): one TAU "CTX, Ebound(value)"
    plugging the inner value node VERBATIM in context; the general
    arm's location write applies (`locUpdTh an th`). -/
theorem step_ctx_bound_pure {an a1 b1 : List _root_.annot} {e : CoreExpr} {ctx : context}
    {v : value}
    (hd : Decomp e ctx (Expr an (Ebound (ofValA (.pure a1 b1 v)))))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_tau2 "CTX, Ebound(value)" TSK_Misc
        { locUpdTh an th with arena := apply_ctx ctx (ofValA (.pure a1 b1 v)) }] := by
  have hget : get_ctx th.arena =
      [(ctx, Expr an (Ebound (Expr a1 (Epure (Pexpr b1 () (PEval v))))))] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  cases ctx <;> rfl

/-- E1: REMOVE-BOUND at an annotated value, context undisturbed
    (step_ctx's `Ebound (Expr _ (Eannot _ (expr'@(Expr _ (Epure (Pexpr
    _ _ (PEval _)))))))` arm, core_reduction.lem:1214–1219): one TAU
    "CTX, Ebound Eannot(value)" plugging the INNER value node — the
    dynamic annotations are DROPPED — in context; location write
    applies. -/
theorem step_ctx_bound_annot {an a1 a2 b1 : List _root_.annot} {e : CoreExpr} {ctx : context}
    {ds : List dyn_annotation} {v : value}
    (hd : Decomp e ctx (Expr an (Ebound (ofValA (.annot a1 a2 b1 ds v)))))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_tau2 "CTX, Ebound Eannot(value)" TSK_Misc
        { locUpdTh an th with arena := apply_ctx ctx (ofValA (.pure a2 b1 v)) }] := by
  have hget : get_ctx th.arena =
      [(ctx, Expr an (Ebound (Expr a1 (Eannot ds
        (Expr a2 (Epure (Pexpr b1 () (PEval v))))))))] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  cases ctx <;> rfl

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

@[simp] theorem esize_pure {a : List _root_.annot} {pe : pexpr} :
    esize (Expr a (Epure pe)) = 1 := rfl

@[simp] theorem esize_action {a : List _root_.annot}
    {p : generic_paction core_run_annotation Unit sym} :
    esize (Expr a (Eaction p)) = 1 := rfl

@[simp] theorem esize_memop {a : List _root_.annot} {mop : memop}
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

/-- The covered operand sub-grammar (the Prop form of `isPePure`,
    Step.lean): value leaves, symbols, the eight mirrored binops, array
    shifts, and (E2, the loaded-value dialect) the mirrored constructors at
    covered operands, `case` at a covered scrutinee with covered branch
    bodies, `not`, the pure `if`, and `undef`. Every constructor's operands
    are in the grammar, so the engine's one-pass evaluator and the mirror's
    agree pass by pass (`step_eval_bridge`). -/
inductive PePure : generic_pexpr Unit sym → Prop where
  | val (a : List _root_.annot) (v : value) : PePure (Pexpr a () (PEval v))
  | sym (a : List _root_.annot) (x : sym) : PePure (Pexpr a () (PEsym x))
  | op (a : List _root_.annot) (op : binop) (hop : isMirroredOp op = true)
      {pe1 pe2 : generic_pexpr Unit sym} :
      PePure pe1 → PePure pe2 → PePure (Pexpr a () (PEop op pe1 pe2))
  | arrayShift (a : List _root_.annot) (ty : ctype)
      {pe1 pe2 : generic_pexpr Unit sym} :
      PePure pe1 → PePure pe2 → PePure (Pexpr a () (PEarray_shift pe1 ty pe2))
  /-- E1: the constructor constants `Ivalignof(ty)` / `Ivsizeof(ty)` (and,
      E2, `Unspecified(ty)`) at a literal ctype (`isTyCtor`; the
      evaluator's `PEctor Civalignof [Vctype ty] → alignofIval`,
      core_eval.lem:648–651, `Cunspecified [Vctype ty] → Vloaded
      (LVunspecified ty)`, :682–683). An instance of `ctor`. -/
  | ctorTy (a : List _root_.annot) (c : ctor) (hc : isTyCtor c = true)
      (pb : List _root_.annot) (ty : ctype) :
      PePure (Pexpr a () (PEctor c [Pexpr pb () (PEval (Vctype ty))]))
  /-- E2: a mirrored constructor at covered operands — `Specified(e)`
      (`Cspecified [Vobject ov] ↦ Vloaded (LVspecified ov)`,
      core_eval.lem:680–681), the tuple `(e1, …, en)` (`Ctuple cvals ↦
      Vtuple cvals`, :614–615), and the type-argument constants at any
      covered operand. -/
  | ctor (a : List _root_.annot) (c : ctor) (hc : isMirroredCtor c = true)
      {pes : List (generic_pexpr Unit sym)} :
      (∀ pe ∈ pes, PePure pe) → PePure (Pexpr a () (PEctor c pes))
  /-- E2: `case e of | pat => body … end` at a covered scrutinee and
      covered BRANCH BODIES as written; the engine's `PEcase` arm selects
      through `select_case subst_sym_pexpr` at the scrutinee's value and
      returns the branch UNEVALUATED (core_eval.lem:725–745) — the
      substituted branch the engine evaluates next is covered exactly when
      the mirror's guarded pass on it succeeds (`stepPexpr_shape`). -/
  | case_ (a : List _root_.annot) {pe : generic_pexpr Unit sym}
      {pats : List (pattern × generic_pexpr Unit sym)} :
      PePure pe → (∀ q ∈ pats, PePure q.2) → PePure (Pexpr a () (PEcase pe pats))
  /-- E2: `not(e)` (core_eval.lem:794–815). -/
  | not_ (a : List _root_.annot) {pe : generic_pexpr Unit sym} :
      PePure pe → PePure (Pexpr a () (PEnot pe))
  /-- E2: the pure conditional `if e1 then e2 else e3` (core_eval.lem:1008–
      1047 — the chosen branch is evaluated IN THE SAME PASS, `strip <$> self
      pe2`). -/
  | if_ (a : List _root_.annot) {pe1 pe2 pe3 : generic_pexpr Unit sym} :
      PePure pe1 → PePure pe2 → PePure pe3 → PePure (Pexpr a () (PEif pe1 pe2 pe3))
  /-- E2: `undef(<<UB…>>)` — the engine's `Undefined.undef loc' [ub]`
      (core_eval.lem:596–604), an undefined-behaviour KILL through
      `liftCore_run` (driver.lem:171–185); the mirror evaluator answers
      `none` and the classifier `.undef` (EvalClass.lean). -/
  | undef (a : List _root_.annot) (loc : CerbLocation.Loc) (ub : undefined_behaviour) :
      PePure (Pexpr a () (PEundef loc ub))

theorem peDepth_sym_le (pb : List _root_.annot) (x : sym) :
    peDepth (Pexpr pb () (PEsym x)) ≤ lemDefaultFuel := by
  rw [show peDepth (Pexpr pb () (PEsym x)) = 1 from rfl,
    show lemDefaultFuel = 999999 + 1 from rfl]
  omega

theorem peDepth_val_le (a : List _root_.annot) (v : value) :
    peDepth (Pexpr a () (PEval v)) ≤ lemDefaultFuel := by
  rw [show peDepth (Pexpr a () (PEval v)) = 1 from rfl,
    show lemDefaultFuel = 999999 + 1 from rfl]
  omega

/-- The strong-induction principle over the depth measure the pass/value
    lemmas use. -/
theorem peDepth_strong_induction {P : generic_pexpr Unit sym → Prop}
    (ih : ∀ pe, (∀ q, peDepth q < peDepth pe → P q) → P pe) : ∀ pe, P pe := by
  intro pe
  induction hn : peDepth pe using Nat.strongRecOn generalizing pe with
  | ind n ihn =>
    subst hn
    exact ih pe (fun q hq => ihn _ hq q rfl)

/-- Element-wise relation between two lists (the shape the list-valued
    pass/value lemmas take; Lean core has no `PairAll`). -/
inductive PairAll {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : PairAll R [] []
  | cons {x : α} {y : β} {xs : List α} {ys : List β} :
      R x y → PairAll R xs ys → PairAll R (x :: xs) (y :: ys)

/-! ### The Bool and Prop grammars agree -/

@[simp] theorem isPePureList_nil : isPePureList [] = true := by rw [isPePureList]
@[simp] theorem isPePureList_cons (pe : generic_pexpr Unit sym) (pes : List (generic_pexpr Unit sym)) :
    isPePureList (pe :: pes) = (isPePure pe && isPePureList pes) := by rw [isPePureList]
@[simp] theorem isPePureAlts_nil : isPePureAlts [] = true := by rw [isPePureAlts]
@[simp] theorem isPePureAlts_cons (pat : pattern) (pe : generic_pexpr Unit sym)
    (rest : List (pattern × generic_pexpr Unit sym)) :
    isPePureAlts ((pat, pe) :: rest) = (isPePure pe && isPePureAlts rest) := by rw [isPePureAlts]

theorem isPePureList_iff {pes : List (generic_pexpr Unit sym)} :
    isPePureList pes = true ↔ ∀ pe ∈ pes, isPePure pe = true := by
  induction pes with
  | nil => simp
  | cons pe pes ih =>
    rw [isPePureList_cons, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact h1
      · exact h2 q hq'
    · intro h
      exact ⟨h pe List.mem_cons_self, fun q hq => h q (List.mem_cons_of_mem _ hq)⟩

theorem isPePureAlts_iff {pats : List (pattern × generic_pexpr Unit sym)} :
    isPePureAlts pats = true ↔ ∀ q ∈ pats, isPePure q.2 = true := by
  induction pats with
  | nil => simp
  | cons q qs ih =>
    obtain ⟨pat, pe⟩ := q
    rw [isPePureAlts_cons, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ q' hq'
      rcases List.mem_cons.mp hq' with rfl | hq''
      · exact h1
      · exact h2 q' hq''
    · intro h
      exact ⟨h (pat, pe) List.mem_cons_self, fun q' hq' => h q' (List.mem_cons_of_mem _ hq')⟩

theorem PePure.of_isPePure : ∀ {pe : generic_pexpr Unit _root_.sym}, isPePure pe = true → PePure pe := by
  intro pe
  induction pe using peDepth_strong_induction with
  | _ pe ih =>
  intro h
  rcases pe with ⟨a, u, pe_⟩
  cases u
  cases pe_
  case PEval v => exact .val a v
  case PEsym x => exact .sym a x
  case PEundef loc ub => exact .undef a loc ub
  case PEctor c pes =>
    rw [isPePure, Bool.and_eq_true, isPePureList_iff] at h
    refine .ctor a c h.1 fun q hq => ih q ?_ (h.2 q hq)
    simp only [peDepth_ctor]; have := peDepth_le_list_of_mem hq; omega
  case PEcase pe pats =>
    rw [isPePure, Bool.and_eq_true, isPePureAlts_iff] at h
    refine .case_ a (ih pe (by simp only [peDepth_case]; omega) h.1) fun q hq => ih q.2 ?_ (h.2 q hq)
    obtain ⟨qp, qe⟩ := q
    simp only [peDepth_case]; have := peDepth_le_alts_of_mem hq; omega
  case PEarray_shift pe1 ty pe2 =>
    rw [isPePure, Bool.and_eq_true] at h
    exact .arrayShift a ty (ih pe1 (by simp only [peDepth_array_shift]; omega) h.1)
      (ih pe2 (by simp only [peDepth_array_shift]; omega) h.2)
  case PEnot pe =>
    rw [isPePure] at h
    exact .not_ a (ih pe (by simp only [peDepth_not]; omega) h)
  case PEop op pe1 pe2 =>
    rw [isPePure, Bool.and_eq_true, Bool.and_eq_true] at h
    exact .op a op h.1.1 (ih pe1 (by simp only [peDepth_op]; omega) h.1.2)
      (ih pe2 (by simp only [peDepth_op]; omega) h.2)
  case PEif pe1 pe2 pe3 =>
    rw [isPePure, Bool.and_eq_true, Bool.and_eq_true] at h
    exact .if_ a (ih pe1 (by simp only [peDepth_if]; omega) h.1.1)
      (ih pe2 (by simp only [peDepth_if]; omega) h.1.2)
      (ih pe3 (by simp only [peDepth_if]; omega) h.2)
  all_goals (simp [isPePure] at h)

theorem isPePure_of_PePure {pe : generic_pexpr Unit _root_.sym} (hp : PePure pe) :
    isPePure pe = true := by
  induction hp with
  | val a v => rw [isPePure]
  | sym a x => rw [isPePure]
  | op a op hop _ _ ih1 ih2 => rw [isPePure, hop, ih1, ih2]; rfl
  | arrayShift a ty _ _ ih1 ih2 => rw [isPePure, ih1, ih2]; rfl
  | ctorTy a c hc pb ty =>
    rw [isPePure, isPePureList_cons, isPePureList_nil]
    rw [show isPePure (Pexpr pb () (PEval (Vctype ty))) = true by rw [isPePure]]
    cases c <;> first | rfl | (cases hc)
  | ctor a c hc _ ih => rw [isPePure, hc, isPePureList_iff.mpr ih]; rfl
  | case_ a _ _ ih ihs => rw [isPePure, ih, isPePureAlts_iff.mpr ihs]; rfl
  | not_ a _ ih => rw [isPePure, ih]
  | if_ a _ _ _ ih1 ih2 ih3 => rw [isPePure, ih1, ih2, ih3]; rfl
  | undef a loc ub => rw [isPePure]

theorem PePure.all_of_isPePure {pes : List (generic_pexpr Unit _root_.sym)}
    (h : pes.all isPePure = true) : ∀ pe ∈ pes, PePure pe := by
  intro pe hpe
  exact PePure.of_isPePure (List.all_eq_true.mp h pe hpe)

/-- A binop the mirror evaluates is a mirrored one. -/
theorem evalBinop_mirrored {op : binop} {v1 v2 v : value}
    (h : evalBinop op v1 v2 = some v) : isMirroredOp op = true := by
  unfold evalBinop at h
  split at h <;> first | rfl | cases h

/-- A constructor the mirror evaluates is a mirrored one. -/
theorem evalCtor_mirrored {tds : CerbTags.TagDefsMap} {c : ctor} {vs : List value} {v : value}
    (h : evalCtor tds c vs = some v) : isMirroredCtor c = true := by
  unfold evalCtor at h
  split at h <;> first | rfl | cases h

/-! ### The one-pass mirror: guard, lists, values -/

/-- At a covered term the guarded pass is the faithful pass. -/
theorem stepPexpr_of_PePure {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym} {ρ : EnvStack}
    {pe : generic_pexpr Unit sym} (hp : PePure pe) :
    stepPexpr tds ext ρ pe = stepPexprRaw tds ext ρ pe := by
  unfold stepPexpr; rw [isPePure_of_PePure hp]; rfl

/-- Mirror one-pass success implies the covered shape (the guard). -/
theorem stepPexpr_shape {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym} {ρ : EnvStack}
    {pe r : generic_pexpr Unit sym} (h : stepPexpr tds ext ρ pe = some r) : PePure pe := by
  unfold stepPexpr at h
  cases hg : isPePure pe with
  | false => rw [hg] at h; cases h
  | true => exact PePure.of_isPePure hg

theorem stepPexprsRaw_cons (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack)
    (pe : generic_pexpr Unit sym) (pes : List (generic_pexpr Unit sym)) :
    stepPexprsRaw tds ext ρ (pe :: pes) = (do
      let r ← stepPexprRaw tds ext ρ pe
      let rs ← stepPexprsRaw tds ext ρ pes
      some (r :: rs)) := by
  rw [stepPexprsRaw]

@[simp] theorem stepPexprsRaw_nil (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack) :
    stepPexprsRaw tds ext ρ [] = some [] := by
  rw [stepPexprsRaw]

theorem stepPexprsRaw_some_iff {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym} {ρ : EnvStack}
    {pes : List (generic_pexpr Unit sym)} {rs : List (generic_pexpr Unit sym)} :
    stepPexprsRaw tds ext ρ pes = some rs ↔
      PairAll (fun pe r => stepPexprRaw tds ext ρ pe = some r) pes rs := by
  induction pes generalizing rs with
  | nil =>
    rw [stepPexprsRaw_nil]
    constructor
    · intro h; cases h; exact .nil
    · intro h; cases h; rfl
  | cons pe pes ih =>
    rw [stepPexprsRaw_cons]
    constructor
    · intro h
      cases hr : stepPexprRaw tds ext ρ pe with
      | none => rw [hr] at h; cases h
      | some r =>
        cases hrs : stepPexprsRaw tds ext ρ pes with
        | none => rw [hr, hrs] at h; cases h
        | some rs' =>
          rw [hr, hrs] at h
          obtain rfl := Option.some.inj h
          exact .cons hr (ih.mp hrs)
    · intro h
      cases h with
      | cons hr hrs =>
        rw [hr, ih.mpr hrs]
        rfl

theorem evalPexprList_some_iff {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym} {ρ : EnvStack}
    {pes : List (generic_pexpr Unit sym)} {vs : List value} :
    evalPexprList tds ext ρ pes = some vs ↔
      PairAll (fun pe v => evalPexpr tds ext ρ pe = some v) pes vs := by
  induction pes generalizing vs with
  | nil =>
    rw [evalPexprList_nil]
    constructor
    · intro h; cases h; exact .nil
    · intro h; cases h; rfl
  | cons pe pes ih =>
    rw [evalPexprList_cons]
    constructor
    · intro h
      cases hr : evalPexpr tds ext ρ pe with
      | none => rw [hr] at h; cases h
      | some v =>
        cases hrs : evalPexprList tds ext ρ pes with
        | none => rw [hr, hrs] at h; cases h
        | some vs' =>
          rw [hr, hrs] at h
          obtain rfl := Option.some.inj h
          exact .cons hr (ih.mp hrs)
    · intro h
      cases h with
      | cons hr hrs =>
        rw [hr, ih.mpr hrs]
        rfl

/-- The value test on a pexpr. -/
theorem valueFromPexpr_some_iff {r : generic_pexpr Unit sym} {v : value} :
    valueFromPexpr r = some v ↔ ∃ a, r = Pexpr a () (PEval v) := by
  rcases r with ⟨a, u, r_⟩
  cases u
  cases r_ <;> simp [valueFromPexpr]

theorem valueFromPexprs_some_iff {rs : List (generic_pexpr Unit sym)} {vs : List value} :
    valueFromPexprs rs = some vs ↔ PairAll (fun r v => valueFromPexpr r = some v) rs vs := by
  induction rs generalizing vs with
  | nil =>
    rw [valueFromPexprs_nil]
    constructor
    · intro h; cases h; exact .nil
    · intro h; cases h; rfl
  | cons r rs ih =>
    rw [valueFromPexprs_cons]
    constructor
    · intro h
      cases hr : valueFromPexpr r with
      | none => rw [hr] at h; cases h
      | some v =>
        cases hrs : valueFromPexprs rs with
        | none => rw [hr, hrs] at h; cases h
        | some vs' =>
          rw [hr, hrs] at h
          obtain rfl := Option.some.inj h
          exact .cons hr (ih.mp hrs)
    · intro h
      cases h with
      | cons hr hrs => rw [hr, ih.mpr hrs]

/-! ### Passes and the big-step value

The one-pass mirror and the big-step value agree on successes: a
one-pass VALUE is the big-step value, a pass preserves the big-step value,
a big-step value has a successful first pass, and a pass on a term with a
big-step value strictly decreases `peDepth` unless it reaches the value.
The four are proved together (`stepPexprRaw_eval_joint`), by strong
induction on `peDepth` at a covered term. -/

@[simp] theorem peDepth_reannot0 (pe : generic_pexpr Unit sym) :
    peDepth (reannot0 pe) = peDepth pe := by
  rcases pe with ⟨a, u, pe_⟩; cases u; rw [reannot0_mk]; cases pe_ <;> rfl

@[simp] theorem peDepth_valPe (v : value) : peDepth (valPe v) = 1 := rfl

theorem isPePure_reannot0 (pe : generic_pexpr Unit sym) :
    isPePure (reannot0 pe) = isPePure pe := by
  rcases pe with ⟨a, u, pe_⟩; cases u; rw [reannot0_mk]; cases pe_ <;> rfl

theorem evalPexpr_reannot0 (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack)
    (pe : generic_pexpr Unit sym) :
    evalPexpr tds ext ρ (reannot0 pe) = evalPexpr tds ext ρ pe := by
  rcases pe with ⟨a, u, pe_⟩
  cases u
  rw [reannot0_mk]
  cases pe_ <;> first | rfl | (rw [evalPexpr.eq_def]; conv => rhs; rw [evalPexpr.eq_def])

theorem valueFromPexpr_reannot0 (pe : generic_pexpr Unit sym) :
    valueFromPexpr (reannot0 pe) = valueFromPexpr pe := by
  rcases pe with ⟨a, u, pe_⟩; cases u; rw [reannot0_mk]; cases pe_ <;> rfl

theorem PePure.reannot0 {pe : generic_pexpr Unit _root_.sym} (hp : PePure pe) : PePure (reannot0 pe) :=
  PePure.of_isPePure (by rw [isPePure_reannot0]; exact isPePure_of_PePure hp)

/-- Every result of the faithful pass carries the engine's reset outer
    annotations (`Pexpr [] () <$>`, Core_eval.lean:142). -/
theorem stepPexprRaw_annot0 {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym} {ρ : EnvStack}
    {pe r : generic_pexpr Unit sym} (h : stepPexprRaw tds ext ρ pe = some r) :
    reannot0 r = r := by
  rcases pe with ⟨a, u, pe_⟩
  cases u
  cases pe_
  case PEval v => rw [stepPexprRaw] at h; obtain rfl := Option.some.inj h; rfl
  case PEsym x =>
    rw [stepPexprRaw] at h
    cases hl : lookup_env (resolveExtern ext x) ρ <;> rw [hl] at h <;> (try dsimp only at h)
    · cases h
    · obtain rfl := Option.some.inj h; rfl
  case PEctor c pes =>
    rw [stepPexprRaw] at h
    cases hrs : stepPexprsRaw tds ext ρ pes <;> rw [hrs] at h
    · cases h
    · simp only [Option.bind_eq_bind, Option.bind_some] at h
      cases hvs : valueFromPexprs _ <;> rw [hvs] at h <;> (try dsimp only at h)
      · obtain rfl := Option.some.inj h; rfl
      · cases hc : evalCtor tds c _ <;> rw [hc] at h <;> (try dsimp only at h)
        · cases h
        · obtain rfl := Option.some.inj h; rfl
  case PEcase pe pats =>
    rw [stepPexprRaw] at h
    cases hr : stepPexprRaw tds ext ρ pe <;> rw [hr] at h
    · cases h
    · simp only [Option.bind_eq_bind, Option.bind_some] at h
      cases hv : valueFromPexpr _ <;> rw [hv] at h <;> (try dsimp only at h)
      · obtain rfl := Option.some.inj h; rfl
      · cases hsel : select_case subst_sym_pexpr _ pats <;> rw [hsel] at h <;> (try dsimp only at h)
        · cases h
        · simp only [Option.map_some] at h
          obtain rfl := Option.some.inj h
          rename_i pe''
          rcases pe'' with ⟨_, _, _⟩; rfl
  case PEarray_shift pe1 ty pe2 =>
    rw [stepPexprRaw] at h
    cases h1 : stepPexprRaw tds ext ρ pe1 <;> rw [h1] at h
    · cases h
    · cases h2 : stepPexprRaw tds ext ρ pe2 <;> rw [h2] at h
      · cases h
      · simp only [Option.bind_eq_bind, Option.bind_some] at h
        cases hv1 : valueFromPexpr _ <;> rw [hv1] at h <;> (try dsimp only at h)
        · obtain rfl := Option.some.inj h; rfl
        · cases hv2 : valueFromPexpr _ <;> rw [hv2] at h <;> (try dsimp only at h)
          · obtain rfl := Option.some.inj h; rfl
          · cases hb : evalArrayShift tds ty _ _ <;> rw [hb] at h <;> (try dsimp only at h)
            · cases h
            · obtain rfl := Option.some.inj h; rfl
  case PEnot pe =>
    rw [stepPexprRaw] at h
    cases hr : stepPexprRaw tds ext ρ pe <;> rw [hr] at h
    · cases h
    · simp only [Option.bind_eq_bind, Option.bind_some] at h
      cases hv : valueFromPexpr _ <;> rw [hv] at h <;> (try dsimp only at h)
      · obtain rfl := Option.some.inj h; rfl
      · rename_i w
        cases w <;> simp at h <;> (try subst h) <;> rfl
  case PEop op pe1 pe2 =>
    rw [stepPexprRaw] at h
    cases h1 : stepPexprRaw tds ext ρ pe1 <;> rw [h1] at h
    · cases h
    · cases h2 : stepPexprRaw tds ext ρ pe2 <;> rw [h2] at h
      · cases h
      · simp only [Option.bind_eq_bind, Option.bind_some] at h
        cases hv1 : valueFromPexpr _ <;> rw [hv1] at h <;> (try dsimp only at h)
        · obtain rfl := Option.some.inj h; rfl
        · cases hv2 : valueFromPexpr _ <;> rw [hv2] at h <;> (try dsimp only at h)
          · obtain rfl := Option.some.inj h; rfl
          · cases hb : evalBinop op _ _ <;> rw [hb] at h <;> (try dsimp only at h)
            · cases h
            · obtain rfl := Option.some.inj h; rfl
  case PEif pe1 pe2 pe3 =>
    rw [stepPexprRaw] at h
    cases h1 : stepPexprRaw tds ext ρ pe1 <;> rw [h1] at h
    · cases h
    · simp only [Option.bind_eq_bind, Option.bind_some] at h
      cases hv1 : valueFromPexpr _ <;> rw [hv1] at h <;> (try dsimp only at h)
      · obtain rfl := Option.some.inj h; rfl
      · rename_i w
        cases w <;> (try (cases h)) <;> (try dsimp only at h)
        all_goals first
          | (cases h2 : stepPexprRaw tds ext ρ pe2 <;> rw [h2] at h
             · simp only [Option.map_none] at h; cases h
             · simp only [Option.map_some] at h
               obtain rfl := Option.some.inj h
               rename_i r2
               rcases r2 with ⟨_, _, _⟩; rfl)
          | (cases h3 : stepPexprRaw tds ext ρ pe3 <;> rw [h3] at h
             · simp only [Option.map_none] at h; cases h
             · simp only [Option.map_some] at h
               obtain rfl := Option.some.inj h
               rename_i r3
               rcases r3 with ⟨_, _, _⟩; rfl)
  all_goals (simp [stepPexprRaw] at h)

/-- A value result of the faithful pass is the canonical value pexpr. -/
theorem stepPexprRaw_valPe_of_value {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym} {ρ : EnvStack}
    {pe r : generic_pexpr Unit sym} {v : value} (h : stepPexprRaw tds ext ρ pe = some r)
    (hv : valueFromPexpr r = some v) : r = valPe v := by
  obtain ⟨a, rfl⟩ := valueFromPexpr_some_iff.mp hv
  have := stepPexprRaw_annot0 h
  rw [reannot0_mk] at this
  exact this.symm

/-- A selecting alternative list is non-empty, so its bodies' depth
    bound is positive. -/
theorem peDepthAlts_pos_of_select {cval : value}
    {pats : List (pattern × generic_pexpr Unit sym)} {pe'' : generic_pexpr Unit sym}
    (h : select_case subst_sym_pexpr cval pats = some pe'') : 1 ≤ peDepthAlts pats := by
  cases pats with
  | nil => rw [select_case] at h; cases h
  | cons q qs =>
    obtain ⟨qp, qe⟩ := q
    rw [peDepthAlts_cons]
    have := peDepth_pos qe
    omega

/-- Sum of depths over a pass on a list: non-increasing, and strictly
    decreasing once some element's result is not a value. -/
theorem peDepthList_pairAll {pes rs : List (generic_pexpr Unit sym)}
    (h : PairAll (fun pe r => peDepth r ≤ peDepth pe ∧
      (valueFromPexpr r = none → peDepth r < peDepth pe)) pes rs) :
    peDepthList rs ≤ peDepthList pes ∧
      (valueFromPexprs rs = none → peDepthList rs < peDepthList pes) := by
  induction h with
  | nil => exact ⟨Nat.le_refl _, fun h => by rw [valueFromPexprs_nil] at h; cases h⟩
  | cons hpr hrest ih =>
    rename_i pe r pes rs
    obtain ⟨hle, hlt⟩ := hpr
    obtain ⟨ihle, ihlt⟩ := ih
    refine ⟨by simp only [peDepthList_cons]; omega, fun hnv => ?_⟩
    rw [valueFromPexprs_cons] at hnv
    simp only [peDepthList_cons]
    cases hr : valueFromPexpr r with
    | none => have := hlt hr; omega
    | some v =>
      rw [hr] at hnv
      cases hrs : valueFromPexprs rs with
      | none => have := ihlt hrs; omega
      | some vs => rw [hrs] at hnv; cases hnv

/-- The joint pass/value property at one term. -/
def PassJoint (tds : CerbTags.TagDefsMap) (ext : Fmap sym sym) (ρ : EnvStack)
    (pe : generic_pexpr Unit sym) : Prop :=
  (∀ v, stepPexprRaw tds ext ρ pe = some (valPe v) → evalPexpr tds ext ρ pe = some v) ∧
  (∀ v, evalPexpr tds ext ρ pe = some v →
    ∃ r, stepPexprRaw tds ext ρ pe = some r ∧ evalPexpr tds ext ρ r = some v ∧
      peDepth r ≤ peDepth pe ∧ (valueFromPexpr r = none → peDepth r < peDepth pe))


theorem PairAll.mem_left {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : PairAll R xs ys) {x : α} (hx : x ∈ xs) : ∃ y, R x y := by
  induction h with
  | nil => cases hx
  | cons hxy hrest ih =>
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨_, hxy⟩
    · exact ih hx'

/-- One-pass values on a list are the big-step values. -/
theorem pairAll_step_values {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym} {ρ : EnvStack}
    {pes rs : List (generic_pexpr Unit sym)} {vs : List value}
    (h1 : PairAll (fun pe r => stepPexprRaw tds ext ρ pe = some r) pes rs)
    (h2 : PairAll (fun r v => valueFromPexpr r = some v) rs vs)
    (ih : ∀ pe ∈ pes, PassJoint tds ext ρ pe) :
    PairAll (fun pe v => evalPexpr tds ext ρ pe = some v) pes vs := by
  induction h1 generalizing vs with
  | nil => cases h2; exact .nil
  | cons hpr hrest ihl =>
    rename_i pe r pes' rs'
    cases h2 with
    | cons hv hvs' =>
      refine .cons ?_ (ihl hvs' (fun q hq => ih q (List.mem_cons_of_mem _ hq)))
      have hr := stepPexprRaw_valPe_of_value hpr hv
      exact (ih pe List.mem_cons_self).1 _ (by rw [hpr, hr])

/-- Big-step values of one-pass value results are those values. -/
theorem pairAll_eval_values {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym} {ρ : EnvStack}
    {rs : List (generic_pexpr Unit sym)} {vs ws : List value}
    (h2 : PairAll (fun r v => evalPexpr tds ext ρ r = some v) rs vs)
    (h2' : PairAll (fun r v => valueFromPexpr r = some v) rs ws) : ws = vs := by
  induction h2 generalizing ws with
  | nil => cases h2'; rfl
  | cons hrv hrest ihl =>
    cases h2' with
    | cons hw hws' =>
      rename_i r v' rs' vs' w ws'
      obtain ⟨a1, rfl⟩ := valueFromPexpr_some_iff.mp hw
      rw [evalPexpr_val] at hrv
      obtain rfl := Option.some.inj hrv
      rw [ihl hws']

/-- The pass results of a big-step-evaluated list. -/
theorem pairAll_exists_steps {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym} {ρ : EnvStack}
    {pes : List (generic_pexpr Unit sym)} {vs : List value}
    (hall : PairAll (fun pe v => evalPexpr tds ext ρ pe = some v) pes vs)
    (ih : ∀ pe ∈ pes, PassJoint tds ext ρ pe) :
    ∃ rs, PairAll (fun pe r => stepPexprRaw tds ext ρ pe = some r) pes rs ∧
      PairAll (fun r v => evalPexpr tds ext ρ r = some v) rs vs ∧
      PairAll (fun pe r => peDepth r ≤ peDepth pe ∧
        (valueFromPexpr r = none → peDepth r < peDepth pe)) pes rs := by
  induction hall with
  | nil => exact ⟨[], .nil, .nil, .nil⟩
  | cons hpv hrest ihl =>
    rename_i pe v' pes' vs'
    obtain ⟨rs', h1, h2, h3⟩ := ihl (fun q hq => ih q (List.mem_cons_of_mem _ hq))
    obtain ⟨r, hr, he, hd, hs⟩ := (ih pe List.mem_cons_self).2 v' hpv
    exact ⟨r :: rs', .cons hr h1, .cons he h2, .cons ⟨hd, hs⟩ h3⟩

/-- The `ctor` arm of the joint pass/value lemma, factored (the `ctorTy`
    constructor is its instance): stated at the induction hypothesis for
    the operands. -/
theorem joint_ctor {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym} {ρ : EnvStack}
    {pes : List (generic_pexpr Unit sym)}
    (ih : ∀ q ∈ pes, PassJoint tds ext ρ q)
    (a : List _root_.annot) (c : ctor) :
    PassJoint tds ext ρ (Pexpr a () (PEctor c pes)) := by
  refine ⟨fun v h => ?_, fun v h => ?_⟩
  · rw [stepPexprRaw] at h
    cases hrs : stepPexprsRaw tds ext ρ pes with
    | none => rw [hrs] at h; cases h
    | some rs =>
      rw [hrs] at h
      simp only [Option.bind_eq_bind, Option.bind_some] at h
      cases hvs : valueFromPexprs rs with
      | none =>
        rw [hvs] at h; dsimp only at h
        exact absurd (Option.some.inj h).symm (by unfold valPe; simp)
      | some vs =>
        rw [hvs] at h; dsimp only at h
        cases hce : evalCtor tds c vs with
        | none => rw [hce] at h; cases h
        | some w =>
          rw [hce] at h
          obtain rfl : w = v := by have := Option.some.inj h; unfold valPe at this; cases this; rfl
          rw [evalPexpr_ctor, evalPexprList_some_iff.mpr
            (pairAll_step_values (stepPexprsRaw_some_iff.mp hrs) (valueFromPexprs_some_iff.mp hvs) ih)]
          simp only [Option.bind_eq_bind, Option.bind_some]
          exact hce
  · rw [evalPexpr_ctor] at h
    cases hm : evalPexprList tds ext ρ pes with
    | none => rw [hm] at h; cases h
    | some vs =>
      rw [hm] at h
      simp only [Option.bind_eq_bind, Option.bind_some] at h
      obtain ⟨rs, h1, h2, h3⟩ := pairAll_exists_steps (evalPexprList_some_iff.mp hm) ih
      rw [stepPexprRaw, stepPexprsRaw_some_iff.mpr h1]
      simp only [Option.bind_eq_bind, Option.bind_some]
      have hdl := peDepthList_pairAll h3
      cases hvs : valueFromPexprs rs with
      | none =>
        refine ⟨_, rfl, ?_, ?_, fun _ => ?_⟩
        · rw [evalPexpr_ctor, evalPexprList_some_iff.mpr h2]
          simp only [Option.bind_eq_bind, Option.bind_some]
          exact h
        · simp only [peDepth_ctor]; omega
        · have := hdl.2 hvs; simp only [peDepth_ctor]; omega
      | some ws =>
        obtain rfl := pairAll_eval_values h2 (valueFromPexprs_some_iff.mp hvs)
        dsimp only
        rw [h]
        simp only [Option.map_some]
        refine ⟨_, rfl, by rw [evalPexpr_valPe], ?_, fun hnv => by cases hnv⟩
        simp only [peDepth_ctor, peDepth_valPe]
        have := peDepth_pos (Pexpr a () (PEctor c pes))
        omega

/-- The joint statement (module section header). -/
theorem stepPexprRaw_eval_joint {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym} {ρ : EnvStack} :
    ∀ {pe : generic_pexpr Unit sym}, PePure pe → PassJoint tds ext ρ pe := by
  intro pe
  induction pe using peDepth_strong_induction with
  | _ pe ih =>
  intro hp
  cases hp with
  | val a v =>
    refine ⟨fun v' h => ?_, fun v' h => ?_⟩
    · rw [stepPexprRaw] at h
      obtain rfl : v = v' := by
        have := Option.some.inj h
        unfold valPe at this
        cases this; rfl
      rw [evalPexpr_val]
    · rw [evalPexpr_val] at h
      obtain rfl := Option.some.inj h
      exact ⟨valPe v, by rw [stepPexprRaw], by rw [evalPexpr_valPe],
        by simp [peDepth_valPe, peDepth_val], fun hnv => by cases hnv⟩
  | sym a x =>
    refine ⟨fun v h => ?_, fun v h => ?_⟩
    · rw [stepPexprRaw] at h
      rw [evalPexpr_sym]
      cases hl : lookup_env (resolveExtern ext x) ρ with
      | none => rw [hl] at h; cases h
      | some w =>
        rw [hl] at h <;> (try dsimp only at h)
        have := Option.some.inj h
        unfold valPe at this
        cases this; rfl
    · rw [evalPexpr_sym] at h
      refine ⟨valPe v, by rw [stepPexprRaw, h]; rfl, by rw [evalPexpr_valPe],
        by simp [peDepth_valPe, peDepth_sym], fun hnv => by cases hnv⟩
  | undef a loc ub =>
    refine ⟨fun v h => ?_, fun v h => ?_⟩
    · simp [stepPexprRaw] at h
    · rw [evalPexpr_undef] at h; cases h
  | @op a op hop pe1 pe2 hp1 hp2 =>
    have ih1 := ih pe1 (by simp only [peDepth_op]; omega) hp1
    have ih2 := ih pe2 (by simp only [peDepth_op]; omega) hp2
    refine ⟨fun v h => ?_, fun v h => ?_⟩
    · rw [stepPexprRaw] at h
      cases h1 : stepPexprRaw tds ext ρ pe1 with
      | none => rw [h1] at h; cases h
      | some r1 =>
        cases h2 : stepPexprRaw tds ext ρ pe2 with
        | none => rw [h1, h2] at h; cases h
        | some r2 =>
          rw [h1, h2] at h
          simp only [Option.bind_eq_bind, Option.bind_some] at h
          cases hv1 : valueFromPexpr r1 with
          | none => rw [hv1] at h; exact absurd (Option.some.inj h).symm (by unfold valPe; simp)
          | some v1 =>
            cases hv2 : valueFromPexpr r2 with
            | none => rw [hv1, hv2] at h; exact absurd (Option.some.inj h).symm (by unfold valPe; simp)
            | some v2 =>
              rw [hv1, hv2] at h <;> (try dsimp only at h)
              obtain rfl := stepPexprRaw_valPe_of_value h1 hv1
              obtain rfl := stepPexprRaw_valPe_of_value h2 hv2
              cases hb : evalBinop op v1 v2 with
              | none => rw [hb] at h; cases h
              | some w =>
                rw [hb] at h <;> (try dsimp only at h)
                obtain rfl : w = v := by
                  have := Option.some.inj h; unfold valPe at this; cases this; rfl
                rw [evalPexpr_op, ih1.1 v1 h1, ih2.1 v2 h2]
                exact hb
    · rw [evalPexpr_op] at h
      obtain ⟨v1, hv1, v2, hv2, hb⟩ : ∃ v1, evalPexpr tds ext ρ pe1 = some v1 ∧
          ∃ v2, evalPexpr tds ext ρ pe2 = some v2 ∧ evalBinop op v1 v2 = some v := by
        cases h1 : evalPexpr tds ext ρ pe1 with
        | none => rw [h1] at h; cases h
        | some v1 =>
          cases h2 : evalPexpr tds ext ρ pe2 with
          | none => rw [h1, h2] at h; cases h
          | some v2 => rw [h1, h2] at h; exact ⟨v1, rfl, v2, rfl, h⟩
      obtain ⟨r1, hr1, he1, hd1, hs1⟩ := ih1.2 v1 hv1
      obtain ⟨r2, hr2, he2, hd2, hs2⟩ := ih2.2 v2 hv2
      rw [stepPexprRaw, hr1, hr2]
      simp only [Option.bind_eq_bind, Option.bind_some]
      have hp1' := peDepth_pos pe1
      have hp2' := peDepth_pos pe2
      have hr1' := peDepth_pos r1
      have hr2' := peDepth_pos r2
      cases hw1 : valueFromPexpr r1 with
      | none =>
        have hs1' := hs1 hw1
        cases hw2 : valueFromPexpr r2 with
        | none =>
          have hs2' := hs2 hw2
          refine ⟨_, rfl, ?_, ?_, fun _ => ?_⟩
          · rw [evalPexpr_op, he1, he2]; simp only [Option.bind_eq_bind, Option.bind_some]; exact hb
          · simp only [peDepth_op]; omega
          · simp only [peDepth_op]; omega
        | some w2 =>
          obtain rfl := stepPexprRaw_valPe_of_value hr2 hw2
          refine ⟨_, rfl, ?_, ?_, fun _ => ?_⟩
          · rw [evalPexpr_op, he1, he2]; simp only [Option.bind_eq_bind, Option.bind_some]; exact hb
          · simp only [peDepth_op, peDepth_valPe]; omega
          · simp only [peDepth_op, peDepth_valPe]; omega
      | some w1 =>
        obtain rfl := stepPexprRaw_valPe_of_value hr1 hw1
        cases hw2 : valueFromPexpr r2 with
        | none =>
          have hs2' := hs2 hw2
          refine ⟨_, rfl, ?_, ?_, fun _ => ?_⟩
          · rw [evalPexpr_op, he1, he2]; simp only [Option.bind_eq_bind, Option.bind_some]; exact hb
          · simp only [peDepth_op, peDepth_valPe]; omega
          · simp only [peDepth_op, peDepth_valPe]; omega
        | some w2 =>
          obtain rfl := stepPexprRaw_valPe_of_value hr2 hw2
          rw [evalPexpr_valPe] at he1 he2
          obtain rfl := Option.some.inj he1
          obtain rfl := Option.some.inj he2
          simp only [hb, Option.map_some]
          refine ⟨_, rfl, by rw [evalPexpr_valPe], ?_, fun hnv => by cases hnv⟩
          simp only [peDepth_op, peDepth_valPe]; omega
  | @arrayShift a ty pe1 pe2 hp1 hp2 =>
    have ih1 := ih pe1 (by simp only [peDepth_array_shift]; omega) hp1
    have ih2 := ih pe2 (by simp only [peDepth_array_shift]; omega) hp2
    refine ⟨fun v h => ?_, fun v h => ?_⟩
    · rw [stepPexprRaw] at h
      cases h1 : stepPexprRaw tds ext ρ pe1 with
      | none => rw [h1] at h; cases h
      | some r1 =>
        cases h2 : stepPexprRaw tds ext ρ pe2 with
        | none => rw [h1, h2] at h; cases h
        | some r2 =>
          rw [h1, h2] at h
          simp only [Option.bind_eq_bind, Option.bind_some] at h
          cases hv1 : valueFromPexpr r1 with
          | none => rw [hv1] at h; exact absurd (Option.some.inj h).symm (by unfold valPe; simp)
          | some v1 =>
            cases hv2 : valueFromPexpr r2 with
            | none => rw [hv1, hv2] at h; exact absurd (Option.some.inj h).symm (by unfold valPe; simp)
            | some v2 =>
              rw [hv1, hv2] at h <;> (try dsimp only at h)
              obtain rfl := stepPexprRaw_valPe_of_value h1 hv1
              obtain rfl := stepPexprRaw_valPe_of_value h2 hv2
              cases hb : evalArrayShift tds ty v1 v2 with
              | none => rw [hb] at h; cases h
              | some w =>
                rw [hb] at h <;> (try dsimp only at h)
                obtain rfl : w = v := by
                  have := Option.some.inj h; unfold valPe at this; cases this; rfl
                rw [evalPexpr_array_shift, ih1.1 v1 h1, ih2.1 v2 h2]
                exact hb
    · rw [evalPexpr_array_shift] at h
      obtain ⟨v1, hv1, v2, hv2, hb⟩ : ∃ v1, evalPexpr tds ext ρ pe1 = some v1 ∧
          ∃ v2, evalPexpr tds ext ρ pe2 = some v2 ∧ evalArrayShift tds ty v1 v2 = some v := by
        cases h1 : evalPexpr tds ext ρ pe1 with
        | none => rw [h1] at h; cases h
        | some v1 =>
          cases h2 : evalPexpr tds ext ρ pe2 with
          | none => rw [h1, h2] at h; cases h
          | some v2 => rw [h1, h2] at h; exact ⟨v1, rfl, v2, rfl, h⟩
      obtain ⟨r1, hr1, he1, hd1, hs1⟩ := ih1.2 v1 hv1
      obtain ⟨r2, hr2, he2, hd2, hs2⟩ := ih2.2 v2 hv2
      rw [stepPexprRaw, hr1, hr2]
      simp only [Option.bind_eq_bind, Option.bind_some]
      have hp1' := peDepth_pos pe1
      have hp2' := peDepth_pos pe2
      have hr1' := peDepth_pos r1
      have hr2' := peDepth_pos r2
      cases hw1 : valueFromPexpr r1 with
      | none =>
        have hs1' := hs1 hw1
        cases hw2 : valueFromPexpr r2 with
        | none =>
          have hs2' := hs2 hw2
          refine ⟨_, rfl, ?_, ?_, fun _ => ?_⟩
          · rw [evalPexpr_array_shift, he1, he2]; simp only [Option.bind_eq_bind, Option.bind_some]; exact hb
          · simp only [peDepth_array_shift]; omega
          · simp only [peDepth_array_shift]; omega
        | some w2 =>
          obtain rfl := stepPexprRaw_valPe_of_value hr2 hw2
          refine ⟨_, rfl, ?_, ?_, fun _ => ?_⟩
          · rw [evalPexpr_array_shift, he1, he2]; simp only [Option.bind_eq_bind, Option.bind_some]; exact hb
          · simp only [peDepth_array_shift, peDepth_valPe]; omega
          · simp only [peDepth_array_shift, peDepth_valPe]; omega
      | some w1 =>
        obtain rfl := stepPexprRaw_valPe_of_value hr1 hw1
        cases hw2 : valueFromPexpr r2 with
        | none =>
          have hs2' := hs2 hw2
          refine ⟨_, rfl, ?_, ?_, fun _ => ?_⟩
          · rw [evalPexpr_array_shift, he1, he2]; simp only [Option.bind_eq_bind, Option.bind_some]; exact hb
          · simp only [peDepth_array_shift, peDepth_valPe]; omega
          · simp only [peDepth_array_shift, peDepth_valPe]; omega
        | some w2 =>
          obtain rfl := stepPexprRaw_valPe_of_value hr2 hw2
          rw [evalPexpr_valPe] at he1 he2
          obtain rfl := Option.some.inj he1
          obtain rfl := Option.some.inj he2
          simp only [hb, Option.map_some]
          refine ⟨_, rfl, by rw [evalPexpr_valPe], ?_, fun hnv => by cases hnv⟩
          simp only [peDepth_array_shift, peDepth_valPe]; omega
  | ctorTy a c hc pb ty =>
    exact joint_ctor (fun q hq => ih q (by simp only [peDepth_ctor]; have := peDepth_le_list_of_mem hq; omega)
      (by rw [List.mem_singleton] at hq; subst hq; exact .val pb _)) a c
  | @ctor a c hc pes hps =>
    exact joint_ctor (fun q hq => ih q (by simp only [peDepth_ctor]; have := peDepth_le_list_of_mem hq; omega)
      (hps q hq)) a c
  | @case_ a pe pats hpe hpats =>
    have ihs := ih pe (by simp only [peDepth_case]; omega) hpe
    have hg : isPePureAlts pats = true := isPePureAlts_iff.mpr fun q hq => isPePure_of_PePure (hpats q hq)
    refine ⟨fun v h => ?_, fun v h => ?_⟩
    · rw [stepPexprRaw] at h
      cases h1 : stepPexprRaw tds ext ρ pe with
      | none => rw [h1] at h; cases h
      | some r =>
        rw [h1] at h
        simp only [Option.bind_eq_bind, Option.bind_some] at h
        cases hv1 : valueFromPexpr r with
        | none => rw [hv1] at h; exact absurd (Option.some.inj h).symm (by unfold valPe; simp)
        | some cval =>
          rw [hv1] at h <;> (try dsimp only at h)
          obtain rfl := stepPexprRaw_valPe_of_value h1 hv1
          cases hsel : select_case subst_sym_pexpr cval pats with
          | none => rw [hsel] at h; cases h
          | some pe'' =>
            rw [hsel] at h <;> (try dsimp only at h)
            simp only [Option.map_some] at h
            have hr := Option.some.inj h
            rw [evalPexpr_case, if_pos hg, ihs.1 cval h1]
            simp only [Option.bind_eq_bind, Option.bind_some]
            rw [hsel]
            simp only [Option.bind_some, hr, peDepth_valPe]
            rw [if_pos (peDepthAlts_pos_of_select hsel), evalPexpr_valPe]
    · rw [evalPexpr_case] at h
      cases hgg : isPePureAlts pats with
      | false => rw [hgg] at h; cases h
      | true =>
        rw [hgg] at h
        simp only at h
        cases h1 : evalPexpr tds ext ρ pe with
        | none => rw [h1] at h; cases h
        | some cval =>
          rw [h1] at h
          simp only [Option.bind_eq_bind, Option.bind_some] at h
          cases hsel : select_case subst_sym_pexpr cval pats with
          | none => rw [hsel] at h; cases h
          | some pe'' =>
            rw [hsel] at h <;> (try dsimp only at h)
            simp only [Option.bind_some] at h
            by_cases hchk : peDepth (reannot0 pe'') ≤ peDepthAlts pats
            · rw [if_pos hchk] at h
              obtain ⟨r, hr, he, hd, hs⟩ := ihs.2 cval h1
              rw [stepPexprRaw, hr]
              simp only [Option.bind_eq_bind, Option.bind_some]
              cases hw : valueFromPexpr r with
              | none =>
                refine ⟨_, rfl, ?_, ?_, fun _ => ?_⟩
                · rw [evalPexpr_case, if_pos hgg, he]
                  simp only [Option.bind_eq_bind, Option.bind_some]
                  rw [hsel]
                  simp only [Option.bind_some]
                  rw [if_pos hchk]; exact h
                · simp only [peDepth_case]; omega
                · have := hs hw; simp only [peDepth_case]; omega
              | some w =>
                obtain rfl := stepPexprRaw_valPe_of_value hr hw
                rw [evalPexpr_valPe] at he
                obtain rfl := Option.some.inj he
                dsimp only
                rw [hsel]
                simp only [Option.map_some]
                refine ⟨_, rfl, h, ?_, fun _ => ?_⟩ <;>
                  (simp only [peDepth_case]; omega)
            · rw [if_neg hchk] at h; cases h
  | @not_ a pe hpe =>
    have ihs := ih pe (by simp only [peDepth_not]; omega) hpe
    refine ⟨fun v h => ?_, fun v h => ?_⟩
    · rw [stepPexprRaw] at h
      cases h1 : stepPexprRaw tds ext ρ pe with
      | none => rw [h1] at h; cases h
      | some r =>
        rw [h1] at h
        simp only [Option.bind_eq_bind, Option.bind_some] at h
        cases hv1 : valueFromPexpr r with
        | none => rw [hv1] at h; exact absurd (Option.some.inj h).symm (by unfold valPe; simp)
        | some w =>
          rw [hv1] at h <;> (try dsimp only at h)
          obtain rfl := stepPexprRaw_valPe_of_value h1 hv1
          rw [evalPexpr_not, ihs.1 w h1]
          simp only [Option.bind_eq_bind, Option.bind_some]
          cases w <;> (try (cases h)) <;> (try dsimp only at h) <;> rfl
    · rw [evalPexpr_not] at h
      cases h1 : evalPexpr tds ext ρ pe with
      | none => rw [h1] at h; cases h
      | some w =>
        rw [h1] at h
        simp only [Option.bind_eq_bind, Option.bind_some] at h
        obtain ⟨r, hr, he, hd, hs⟩ := ihs.2 w h1
        rw [stepPexprRaw, hr]
        simp only [Option.bind_eq_bind, Option.bind_some]
        cases hw : valueFromPexpr r with
        | none =>
          refine ⟨_, rfl, ?_, ?_, fun _ => ?_⟩
          · rw [evalPexpr_not, he]; simp only [Option.bind_eq_bind, Option.bind_some]; exact h
          · simp only [peDepth_not]; omega
          · have := hs hw; simp only [peDepth_not]; omega
        | some w' =>
          obtain rfl := stepPexprRaw_valPe_of_value hr hw
          rw [evalPexpr_valPe] at he
          obtain rfl := Option.some.inj he
          try dsimp only
          have hp' := peDepth_pos pe
          cases w' <;> (try (cases h)) <;> (try dsimp only at h) <;> (try obtain rfl := Option.some.inj h) <;>
            exact ⟨_, rfl, by rw [evalPexpr_valPe], by simp only [peDepth_not, peDepth_valPe]; omega,
              fun hnv => by cases hnv⟩
  | @if_ a pe1 pe2 pe3 hp1 hp2 hp3 =>
    have ih1 := ih pe1 (by simp only [peDepth_if]; omega) hp1
    have ih2 := ih pe2 (by simp only [peDepth_if]; omega) hp2
    have ih3 := ih pe3 (by simp only [peDepth_if]; omega) hp3
    have hg : (isPePure pe2 && isPePure pe3) = true := by
      rw [isPePure_of_PePure hp2, isPePure_of_PePure hp3]; rfl
    refine ⟨fun v h => ?_, fun v h => ?_⟩
    · rw [stepPexprRaw] at h
      cases h1 : stepPexprRaw tds ext ρ pe1 with
      | none => rw [h1] at h; cases h
      | some r1 =>
        rw [h1] at h
        simp only [Option.bind_eq_bind, Option.bind_some] at h
        cases hv1 : valueFromPexpr r1 with
        | none => rw [hv1] at h; exact absurd (Option.some.inj h).symm (by unfold valPe; simp)
        | some b =>
          rw [hv1] at h <;> (try dsimp only at h)
          obtain rfl := stepPexprRaw_valPe_of_value h1 hv1
          rw [evalPexpr_if, if_pos hg, ih1.1 b h1]
          simp only [Option.bind_eq_bind, Option.bind_some]
          cases b <;> (try (cases h)) <;> (try dsimp only at h)
          all_goals first
            | (cases h2 : stepPexprRaw tds ext ρ pe2 <;> rw [h2] at h
               · simp only [Option.map_none] at h; cases h
               · simp only [Option.map_some] at h
                 rename_i r2
                 have hr2 : r2 = valPe v := by
                   rw [← stepPexprRaw_annot0 h2]; exact Option.some.inj h
                 exact ih2.1 v (by rw [h2, hr2]))
            | (cases h3 : stepPexprRaw tds ext ρ pe3 <;> rw [h3] at h
               · simp only [Option.map_none] at h; cases h
               · simp only [Option.map_some] at h
                 rename_i r3
                 have hr3 : r3 = valPe v := by
                   rw [← stepPexprRaw_annot0 h3]; exact Option.some.inj h
                 exact ih3.1 v (by rw [h3, hr3]))
    · rw [evalPexpr_if, if_pos hg] at h
      cases h1 : evalPexpr tds ext ρ pe1 with
      | none => rw [h1] at h; cases h
      | some b =>
        rw [h1] at h
        simp only [Option.bind_eq_bind, Option.bind_some] at h
        obtain ⟨r1, hr1, he1, hd1, hs1⟩ := ih1.2 b h1
        rw [stepPexprRaw, hr1]
        simp only [Option.bind_eq_bind, Option.bind_some]
        cases hw : valueFromPexpr r1 with
        | none =>
          refine ⟨_, rfl, ?_, ?_, fun _ => ?_⟩
          · rw [evalPexpr_if, if_pos hg, he1]; simp only [Option.bind_eq_bind, Option.bind_some]; exact h
          · simp only [peDepth_if]; omega
          · have := hs1 hw; simp only [peDepth_if]; omega
        | some w =>
          obtain rfl := stepPexprRaw_valPe_of_value hr1 hw
          rw [evalPexpr_valPe] at he1
          obtain rfl := Option.some.inj he1
          try dsimp only
          cases w <;> (try (cases h)) <;> (try dsimp only at h)
          all_goals first
            | (obtain ⟨r2, hr2, he2, hd2, hs2⟩ := ih2.2 v h
               rw [hr2]
               try dsimp only
               simp only [Option.map_some]
               refine ⟨_, rfl, by rw [evalPexpr_reannot0]; exact he2, ?_, fun _ => ?_⟩ <;>
                 (simp only [peDepth_if, peDepth_reannot0]; omega))
            | (obtain ⟨r3, hr3, he3, hd3, hs3⟩ := ih3.2 v h
               rw [hr3]
               try dsimp only
               simp only [Option.map_some]
               refine ⟨_, rfl, by rw [evalPexpr_reannot0]; exact he3, ?_, fun _ => ?_⟩ <;>
                 (simp only [peDepth_if, peDepth_reannot0]; omega))

/-- A one-pass VALUE is the big-step value. -/
theorem stepPexpr_valPe {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym} {ρ : EnvStack}
    {pe : generic_pexpr Unit sym} {v : value} (h : stepPexpr tds ext ρ pe = some (valPe v)) :
    evalPexpr tds ext ρ pe = some v := by
  have hp := stepPexpr_shape h
  rw [stepPexpr_of_PePure hp] at h
  exact (stepPexprRaw_eval_joint hp).1 v h

/-- A big-step value has a successful first pass, which preserves the value
    and strictly decreases the depth unless it delivers the value. -/
theorem evalPexpr_step {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym} {ρ : EnvStack}
    {pe : generic_pexpr Unit sym} {v : value} (hp : PePure pe) (hv : evalPexpr tds ext ρ pe = some v) :
    ∃ r, stepPexpr tds ext ρ pe = some r ∧ evalPexpr tds ext ρ r = some v ∧
      peDepth r ≤ peDepth pe ∧ (valueFromPexpr r = none → peDepth r < peDepth pe) := by
  obtain ⟨r, hr, he, hd, hs⟩ := (stepPexprRaw_eval_joint hp).2 v hv
  exact ⟨r, by rw [stepPexpr_of_PePure hp]; exact hr, he, hd, hs⟩

/-- Mirror big-step success implies the covered shape (the guards on the
    alternatives of a `case` and both branches of an `if` make this hold
    for the WHOLE term, unselected branches included). -/
theorem evalPexpr_shape {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym} {ρ : EnvStack} :
    ∀ {pe : generic_pexpr Unit sym} {v : value},
      evalPexpr tds ext ρ pe = some v → PePure pe := by
  intro pe
  induction pe using peDepth_strong_induction with
  | _ pe ih =>
  intro v h
  rcases pe with ⟨a, u, pe_⟩
  cases u
  cases pe_
  case PEval v' => exact .val a _
  case PEsym x => exact .sym a _
  case PEctor c pes =>
    rw [evalPexpr_ctor] at h
    cases hm : evalPexprList tds ext ρ pes with
    | none => rw [hm] at h; cases h
    | some vs =>
      rw [hm] at h
      simp only [Option.bind_eq_bind, Option.bind_some] at h
      refine .ctor a c (evalCtor_mirrored h) fun q hq => ?_
      obtain ⟨w, hw⟩ := (evalPexprList_some_iff.mp hm).mem_left hq
      exact ih q (by simp only [peDepth_ctor]; have := peDepth_le_list_of_mem hq; omega) hw
  case PEcase pe pats =>
    rw [evalPexpr_case] at h
    cases hg : isPePureAlts pats with
    | false => rw [hg] at h; cases h
    | true =>
      rw [hg] at h
      simp only at h
      cases h1 : evalPexpr tds ext ρ pe with
      | none => rw [h1] at h; cases h
      | some cval =>
        refine .case_ a (ih pe (by simp only [peDepth_case]; omega) h1) ?_
        exact fun q hq => PePure.of_isPePure (isPePureAlts_iff.mp hg q hq)
  case PEarray_shift pe1 ty pe2 =>
    rw [evalPexpr_array_shift] at h
    cases h1 : evalPexpr tds ext ρ pe1 with
    | none => rw [h1] at h; cases h
    | some v1 =>
      cases h2 : evalPexpr tds ext ρ pe2 with
      | none => rw [h1, h2] at h; cases h
      | some v2 =>
        exact .arrayShift a ty (ih pe1 (by simp only [peDepth_array_shift]; omega) h1)
          (ih pe2 (by simp only [peDepth_array_shift]; omega) h2)
  case PEnot pe =>
    rw [evalPexpr_not] at h
    cases h1 : evalPexpr tds ext ρ pe with
    | none => rw [h1] at h; cases h
    | some w => exact .not_ a (ih pe (by simp only [peDepth_not]; omega) h1)
  case PEop op pe1 pe2 =>
    rw [evalPexpr_op] at h
    cases h1 : evalPexpr tds ext ρ pe1 with
    | none => rw [h1] at h; cases h
    | some v1 =>
      cases h2 : evalPexpr tds ext ρ pe2 with
      | none => rw [h1, h2] at h; cases h
      | some v2 =>
        rw [h1, h2] at h
        exact .op a op (evalBinop_mirrored h) (ih pe1 (by simp only [peDepth_op]; omega) h1)
          (ih pe2 (by simp only [peDepth_op]; omega) h2)
  case PEif pe1 pe2 pe3 =>
    rw [evalPexpr_if] at h
    cases hg : (isPePure pe2 && isPePure pe3) with
    | false => rw [hg] at h; cases h
    | true =>
      rw [hg] at h
      simp only at h
      cases h1 : evalPexpr tds ext ρ pe1 with
      | none => rw [h1] at h; cases h
      | some b =>
        rw [Bool.and_eq_true] at hg
        exact .if_ a (ih pe1 (by simp only [peDepth_if]; omega) h1)
          (PePure.of_isPePure hg.1) (PePure.of_isPePure hg.2)
  all_goals (rw [evalPexpr.eq_def] at h; simp at h)

/-! ### The constrained pull on the covered grammar -/

/-- The constrained-pull's image on the covered grammar: annotation
    renormalization only (`pull_constrained` rebuilds every node with `[]`
    annots and recurses into the operands of `PEop`/`PEarray_shift`/`PEnot`
    and the scrutinee of `PEcase`; the operands of `PEctor`/`PEif` and the
    alternatives of `PEcase` are kept VERBATIM by `pull_helper`
    (core_eval.lem:167–193 — the `Right` accumulator pushes the ORIGINAL
    `pe`); no `PEconstrained` exists to pull). -/
def peStrip : generic_pexpr Unit sym → generic_pexpr Unit sym
  | Pexpr _ _ (PEop op pe1 pe2) => Pexpr [] () (PEop op (peStrip pe1) (peStrip pe2))
  | Pexpr _ _ (PEarray_shift pe1 ty pe2) =>
      Pexpr [] () (PEarray_shift (peStrip pe1) ty (peStrip pe2))
  | Pexpr _ _ (PEcase pe pats) => Pexpr [] () (PEcase (peStrip pe) pats)
  | Pexpr _ _ (PEnot pe) => Pexpr [] () (PEnot (peStrip pe))
  | Pexpr _ _ pex => Pexpr [] () pex

theorem PePure.strip {pe : generic_pexpr Unit _root_.sym} (hp : PePure pe) :
    PePure (peStrip pe) := by
  induction hp with
  | val a v => exact .val [] v
  | sym a x => exact .sym [] x
  | op a op hop hp1 hp2 ih1 ih2 => exact .op [] op hop ih1 ih2
  | arrayShift a ty hp1 hp2 ih1 ih2 => exact .arrayShift [] ty ih1 ih2
  | ctorTy a c hc pb ty => exact .ctorTy [] c hc pb ty
  | ctor a c hc hps _ => exact .ctor [] c hc hps
  | case_ a hpe hpats ih _ => exact .case_ [] ih hpats
  | not_ a hpe ih => exact .not_ [] ih
  | if_ a hp1 hp2 hp3 _ _ _ => exact .if_ [] hp1 hp2 hp3
  | undef a loc ub => exact .undef [] loc ub

theorem isPePure_peStrip {pe : generic_pexpr Unit sym} (hp : PePure pe) :
    isPePure (peStrip pe) = isPePure pe := by
  rw [isPePure_of_PePure hp, isPePure_of_PePure hp.strip]

theorem peDepth_peStrip {pe : generic_pexpr Unit sym} (hp : PePure pe) :
    peDepth (peStrip pe) = peDepth pe := by
  induction hp with
  | val a v => show peDepth (Pexpr [] () (PEval v)) = _; rfl
  | sym a x => show peDepth (Pexpr [] () (PEsym x)) = _; rfl
  | op a op hop hp1 hp2 ih1 ih2 =>
    show peDepth (Pexpr [] () (PEop op _ _)) = _
    rw [peDepth_op, peDepth_op, ih1, ih2]
  | arrayShift a ty hp1 hp2 ih1 ih2 =>
    show peDepth (Pexpr [] () (PEarray_shift _ ty _)) = _
    rw [peDepth_array_shift, peDepth_array_shift, ih1, ih2]
  | ctorTy a c hc pb ty => show peDepth (Pexpr [] () (PEctor c _)) = _; rfl
  | ctor a c hc hps _ => show peDepth (Pexpr [] () (PEctor c _)) = _; rfl
  | case_ a hpe hpats ih _ =>
    show peDepth (Pexpr [] () (PEcase _ _)) = _
    rw [peDepth_case, peDepth_case, ih]
  | not_ a hpe ih =>
    show peDepth (Pexpr [] () (PEnot _)) = _
    rw [peDepth_not, peDepth_not, ih]
  | if_ a hp1 hp2 hp3 _ _ _ => show peDepth (Pexpr [] () (PEif _ _ _)) = _; rfl
  | undef a loc ub => show peDepth (Pexpr [] () (PEundef loc ub)) = _; rfl

/-- The faithful pass is invariant under the pull's renormalization. -/
theorem stepPexprRaw_peStrip {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym} {ρ : EnvStack}
    {pe : generic_pexpr Unit sym} (hp : PePure pe) :
    stepPexprRaw tds ext ρ (peStrip pe) = stepPexprRaw tds ext ρ pe := by
  induction hp with
  | val a v => show stepPexprRaw tds ext ρ (Pexpr [] () (PEval v)) = _; rw [stepPexprRaw, stepPexprRaw]
  | sym a x => show stepPexprRaw tds ext ρ (Pexpr [] () (PEsym x)) = _; rw [stepPexprRaw, stepPexprRaw]
  | op a op hop hp1 hp2 ih1 ih2 =>
    show stepPexprRaw tds ext ρ (Pexpr [] () (PEop op _ _)) = _
    rw [stepPexprRaw, stepPexprRaw, ih1, ih2]
  | arrayShift a ty hp1 hp2 ih1 ih2 =>
    show stepPexprRaw tds ext ρ (Pexpr [] () (PEarray_shift _ ty _)) = _
    rw [stepPexprRaw, stepPexprRaw, ih1, ih2]
  | ctorTy a c hc pb ty => show stepPexprRaw tds ext ρ (Pexpr [] () (PEctor c _)) = _; rw [stepPexprRaw, stepPexprRaw]
  | ctor a c hc hps _ => show stepPexprRaw tds ext ρ (Pexpr [] () (PEctor c _)) = _; rw [stepPexprRaw, stepPexprRaw]
  | case_ a hpe hpats ih _ =>
    show stepPexprRaw tds ext ρ (Pexpr [] () (PEcase _ _)) = _
    rw [stepPexprRaw, stepPexprRaw, ih]
  | not_ a hpe ih =>
    show stepPexprRaw tds ext ρ (Pexpr [] () (PEnot _)) = _
    rw [stepPexprRaw, stepPexprRaw, ih]
  | if_ a hp1 hp2 hp3 _ _ _ => show stepPexprRaw tds ext ρ (Pexpr [] () (PEif _ _ _)) = _; rw [stepPexprRaw, stepPexprRaw]
  | undef a loc ub => show stepPexprRaw tds ext ρ (Pexpr [] () (PEundef loc ub)) = _; simp [stepPexprRaw]

theorem stepPexpr_peStrip {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym} {ρ : EnvStack}
    {pe : generic_pexpr Unit sym} (hp : PePure pe) :
    stepPexpr tds ext ρ (peStrip pe) = stepPexpr tds ext ρ pe := by
  rw [stepPexpr_of_PePure hp, stepPexpr_of_PePure hp.strip, stepPexprRaw_peStrip hp]

theorem evalPexpr_peStrip {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym} {ρ : EnvStack}
    {pe : generic_pexpr Unit sym} (hp : PePure pe) :
    evalPexpr tds ext ρ (peStrip pe) = evalPexpr tds ext ρ pe := by
  induction hp with
  | val a v => show evalPexpr tds ext ρ (Pexpr [] () (PEval v)) = _; rw [evalPexpr_val, evalPexpr_val]
  | sym a x => show evalPexpr tds ext ρ (Pexpr [] () (PEsym x)) = _; rw [evalPexpr_sym, evalPexpr_sym]
  | op a op hop hp1 hp2 ih1 ih2 =>
    show evalPexpr tds ext ρ (Pexpr [] () (PEop op _ _)) = _
    rw [evalPexpr_op, evalPexpr_op, ih1, ih2]
  | arrayShift a ty hp1 hp2 ih1 ih2 =>
    show evalPexpr tds ext ρ (Pexpr [] () (PEarray_shift _ ty _)) = _
    rw [evalPexpr_array_shift, evalPexpr_array_shift, ih1, ih2]
  | ctorTy a c hc pb ty => show evalPexpr tds ext ρ (Pexpr [] () (PEctor c _)) = _; rw [evalPexpr_ctor, evalPexpr_ctor]
  | ctor a c hc hps _ => show evalPexpr tds ext ρ (Pexpr [] () (PEctor c _)) = _; rw [evalPexpr_ctor, evalPexpr_ctor]
  | case_ a hpe hpats ih _ =>
    show evalPexpr tds ext ρ (Pexpr [] () (PEcase _ _)) = _
    rw [evalPexpr_case, evalPexpr_case, ih]
  | not_ a hpe ih =>
    show evalPexpr tds ext ρ (Pexpr [] () (PEnot _)) = _
    rw [evalPexpr_not, evalPexpr_not, ih]
  | if_ a hp1 hp2 hp3 _ _ _ => show evalPexpr tds ext ρ (Pexpr [] () (PEif _ _ _)) = _; rw [evalPexpr_if, evalPexpr_if]
  | undef a loc ub => show evalPexpr tds ext ρ (Pexpr [] () (PEundef loc ub)) = _; rw [evalPexpr_undef, evalPexpr_undef]

/-- The pull's result on the covered grammar is never `PEconstrained`-rooted
    (the shape `eval_pexpr_aux2`'s `Left` arm tests). -/
theorem peStrip_root {pe : generic_pexpr Unit sym} (hp : PePure pe) :
    ∃ pex, peStrip pe = Pexpr [] () pex ∧ ∀ xs, pex ≠ PEconstrained xs := by
  cases hp <;> exact ⟨_, rfl, fun _ h => by cases h⟩

/-- `pull_helper` (Core_eval.lean:120) at a list whose every element pulls
    to a non-`PEconstrained` node: the fold's `Right` accumulator collects
    the ORIGINAL elements in reverse, and the result is `pe_cons ps`
    verbatim. -/
theorem foldl_inr_of_step {α β : Type} {F : Sum α (List β) → β → Sum α (List β)}
    {ps : List β} (hstep : ∀ acc p, p ∈ ps → F (Sum.inr acc) p = Sum.inr (p :: acc)) :
    ∀ acc, List.foldl F (Sum.inr acc) ps = Sum.inr (ps.reverse ++ acc) := by
  induction ps with
  | nil => intro acc; rfl
  | cons p ps ih =>
    intro acc
    rw [List.foldl_cons, hstep acc p List.mem_cons_self,
      ih (fun acc q hq => hstep acc q (List.mem_cons_of_mem _ hq))]
    simp

theorem pull_helper_unconstrained {a b : Type} (pull : generic_pexpr Unit sym → generic_pexpr Unit sym)
    (pe_cons : List (a × generic_pexpr Unit sym) → generic_pexpr_ Unit b)
    (ps : List (a × generic_pexpr Unit sym))
    (h : ∀ p ∈ ps, ∃ pex, pull p.2 = Pexpr [] () pex ∧ ∀ xs, pex ≠ PEconstrained xs) :
    pull_helper pull pe_cons ps = pe_cons ps := by
  unfold pull_helper
  rw [foldl_inr_of_step (ps := ps) (acc := [])]
  · simp
  · intro acc p hp
    obtain ⟨a1, pe⟩ := p
    obtain ⟨pex, hpull, hne⟩ := h (a1, pe) hp
    dsimp only
    rw [hpull]
    cases pex <;> first | rfl | (exfalso; apply hne; rfl)

/-- LEVEL 2 of the bridge: `pull_constrained` (Core_eval.lean:126) is
    annotation renormalization on the covered grammar. -/
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
  | undef a loc ub =>
    intro fuel hfuel n
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 :=
      ⟨fuel - 1, by have := peDepth_pos (Pexpr a () (PEundef loc ub)); omega⟩
    rfl
  | @op a op hop pe1 pe2 hp1 hp2 ih1 ih2 =>
    intro fuel hfuel n
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hd1 : peDepth pe1 ≤ f := by simp at hfuel; omega
    have hd2 : peDepth pe2 ≤ f := by simp at hfuel; omega
    show Pexpr [] () _ = Pexpr [] () (PEop op (peStrip pe1) (peStrip pe2))
    dsimp only
    rw [ih1 f hd1 (n+1), ih2 f hd2 (n+1)]
    obtain ⟨p1, e1, hn1⟩ := peStrip_root hp1
    obtain ⟨p2, e2, hn2⟩ := peStrip_root hp2
    rw [e1, e2]
    cases p1 <;> cases p2 <;> first | rfl | (exfalso; apply hn1; rfl) | (exfalso; apply hn2; rfl)
  | @arrayShift a ty pe1 pe2 hp1 hp2 ih1 ih2 =>
    intro fuel hfuel n
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hd1 : peDepth pe1 ≤ f := by simp at hfuel; omega
    have hd2 : peDepth pe2 ≤ f := by simp at hfuel; omega
    show Pexpr [] () _ = Pexpr [] () (PEarray_shift (peStrip pe1) ty (peStrip pe2))
    dsimp only
    rw [ih1 f hd1 (n+1), ih2 f hd2 (n+1)]
    obtain ⟨p1, e1, hn1⟩ := peStrip_root hp1
    obtain ⟨p2, e2, hn2⟩ := peStrip_root hp2
    rw [e1, e2]
    cases p1 <;> cases p2 <;> first | rfl | (exfalso; apply hn1; rfl) | (exfalso; apply hn2; rfl)
  | @not_ a pe hpe ih =>
    intro fuel hfuel n
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hd : peDepth pe ≤ f := by simp at hfuel; omega
    show Pexpr [] () _ = Pexpr [] () (PEnot (peStrip pe))
    dsimp only
    rw [ih f hd (n+1)]
    obtain ⟨p1, e1, hn1⟩ := peStrip_root hpe
    rw [e1]
    cases p1 <;> first | rfl | (exfalso; apply hn1; rfl)
  | ctorTy a c hc pb ty =>
    intro fuel hfuel n
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 :=
      ⟨fuel - 1, by
        have := peDepth_pos (Pexpr a () (PEctor c [Pexpr pb () (PEval (Vctype ty))])); omega⟩
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 :=
      ⟨f - 1, by simp only [peDepth_ctor1, peDepth_val] at hfuel; omega⟩
    rfl
  | @ctor a c hc pes hps ih =>
    intro fuel hfuel n
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    show Pexpr [] () _ = Pexpr [] () (PEctor c pes)
    dsimp only
    rw [pull_helper_unconstrained]
    · simp [Function.comp_def]
    · intro p hp'
      obtain ⟨pe, hpe⟩ : ∃ pe ∈ pes, p = ((), pe) := by
        rw [List.mem_map] at hp'
        obtain ⟨pe, hpe, rfl⟩ := hp'
        exact ⟨pe, hpe, rfl⟩
      obtain ⟨hpe, rfl⟩ := hpe
      have hd : peDepth pe ≤ f := by
        simp only [peDepth_ctor] at hfuel; have := peDepth_le_list_of_mem hpe; omega
      show ∃ pex, pull_constrained_lemFuel f (n + 1) pe = Pexpr [] () pex ∧ _
      rw [ih pe hpe f hd (n+1)]
      exact peStrip_root (hps pe hpe)
  | @case_ a pe pats hpe hpats ih ihs =>
    intro fuel hfuel n
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hd : peDepth pe ≤ f := by simp at hfuel; omega
    show Pexpr [] () _ = Pexpr [] () (PEcase (peStrip pe) pats)
    dsimp only
    rw [ih f hd (n+1)]
    obtain ⟨p1, e1, hn1⟩ := peStrip_root hpe
    rw [e1]
    have hpull : pull_helper (fun pe => pull_constrained_lemFuel f (n + 1) pe)
        (fun xs => PEcase (Pexpr [] () p1) xs) pats = PEcase (Pexpr [] () p1) pats := by
      apply pull_helper_unconstrained
      intro q hq
      obtain ⟨qp, qe⟩ := q
      have hd' : peDepth qe ≤ f := by
        simp only [peDepth_case] at hfuel
        have := peDepth_le_alts_of_mem hq
        omega
      rw [ihs (qp, qe) hq f hd' (n+1)]
      exact peStrip_root (hpats (qp, qe) hq)
    cases p1 <;> first | (exfalso; apply hn1; rfl) | (simp only []; rw [hpull])
  | @if_ a pe1 pe2 pe3 hp1 hp2 hp3 ih1 ih2 ih3 =>
    intro fuel hfuel n
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    show Pexpr [] () _ = Pexpr [] () (PEif pe1 pe2 pe3)
    dsimp only
    rw [pull_helper_unconstrained]
    · rfl
    · intro p hp'
      simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl
      · rw [ih1 f (by simp at hfuel; omega) (n+1)]; exact peStrip_root hp1
      · rw [ih2 f (by simp at hfuel; omega) (n+1)]; exact peStrip_root hp2
      · rw [ih3 f (by simp at hfuel; omega) (n+1)]; exact peStrip_root hp3

/-! ### LEVEL 1 of the bridge: one engine pass = one mirror pass -/

/-- The engine's argument map (`exception_undef_mapM self pes`,
    Exception_undefined.lean:53: `except_mapM` then `mapM1`) at
    arguments whose passes the mirror computes: the list of the passes. -/
theorem exception_undef_mapM_bridge
    {self : generic_pexpr Unit sym → exceptM (t0 (generic_pexpr Unit sym)) core_run_cause}
    {pes rs : List (generic_pexpr Unit sym)}
    (h : PairAll (fun pe r => self pe = exception_undef_return r) pes rs) :
    exception_undef_mapM self pes = exception_undef_return rs := by
  have hseq : except_sequence (List.map self pes) = Result (rs.map Defined) := by
    induction h with
    | nil => rfl
    | cons hpr hrest ih =>
      rename_i pe r pes' rs'
      show List.foldr _ _ (List.map self (pe :: pes')) = _
      rw [List.map_cons, List.foldr_cons]
      have ih' : List.foldr (fun (m : exceptM (t0 (generic_pexpr Unit sym)) core_run_cause)
          (ms' : exceptM (List (t0 (generic_pexpr Unit sym))) core_run_cause) =>
            except_bind m (fun x => except_bind ms' (fun xs => except_return (x :: xs))))
          (except_return []) (List.map self pes') = Result (rs'.map Defined) := ih
      rw [ih', hpr]
      rfl
  unfold exception_undef_mapM except_mapM
  rw [hseq]
  show except_return (mapM1 (fun x => x) (List.map Defined rs)) = _
  unfold mapM1
  rw [List.map_id']
  congr 1
  clear h hseq
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    show sequence0 (Defined r :: List.map Defined rs) = _
    unfold sequence0 at ih ⊢
    rw [List.foldr_cons, ih]
    rfl

/-- LEVEL 1: `step_eval_pexpr` (Core_eval.lean:142) performs ONE pass, the
    mirror's `stepPexpr` — VALUES where the pass reaches a value, the
    selected/rebuilt pexpr elsewhere. Quantified over the level counter
    `n` (the engine ticks it per operand level), tagDefs, locations, the
    memory state and the file (all UNREAD on the covered grammar); the
    extern map is QUANTIFIED — the engine's `PEsym` indirection is the
    mirror's `resolveExtern`, matched case by case on the lookup. -/
theorem step_eval_bridge {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {ext : Fmap sym sym} {ρ : EnvStack}
    {pe r : generic_pexpr Unit sym}
    (hp : PePure pe) (hs : stepPexpr tds ext ρ pe = some r) :
    ∀ (fuel : Nat), peDepth pe ≤ fuel →
    ∀ (n : Nat)
      (loc : CerbLocation.Loc) (cloc : Option CerbLocation.Loc)
      (mem : Option CerbMem.MemState)
      (file : generic_file Unit core_run_annotation),
    step_eval_pexpr_lemFuel fuel tds n loc cloc ext ρ mem file false pe =
      exception_undef_return r := by
  rw [stepPexpr_of_PePure hp] at hs
  induction hp generalizing r with
  | val a v' =>
    intro fuel hfuel n loc cloc mem file
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 :=
      ⟨fuel - 1, by have := peDepth_pos (Pexpr a () (PEval v')); omega⟩
    rw [stepPexprRaw] at hs
    obtain rfl := Option.some.inj hs
    rfl
  | sym a x =>
    intro fuel hfuel n loc cloc mem file
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 :=
      ⟨fuel - 1, by have := peDepth_pos (Pexpr a () (PEsym x)); omega⟩
    rw [stepPexprRaw] at hs
    cases hl : lookup_env (resolveExtern ext x) ρ with
    | none => rw [hl] at hs; cases hs
    | some v =>
      rw [hl] at hs
      obtain rfl := Option.some.inj hs
      show exception_undef_fmap (Pexpr [] ()) _ = _
      dsimp only
      cases hres : fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
          Lem_Basic_classes.ordCompare s1 s2) x ext with
      | none =>
        rw [show resolveExtern ext x = x by unfold resolveExtern; rw [hres]] at hl
        dsimp only
        rw [hl]
        rfl
      | some y =>
        rw [show resolveExtern ext x = y by unfold resolveExtern; rw [hres]] at hl
        dsimp only
        rw [hl]
        rfl
  | undef a loc ub =>
    intro fuel hfuel n loc' cloc mem file
    simp [stepPexprRaw] at hs
  | @op a op hop pe1 pe2 hp1 hp2 ih1 ih2 =>
    intro fuel hfuel n loc cloc mem file
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hd1 : peDepth pe1 ≤ f := by simp at hfuel; omega
    have hd2 : peDepth pe2 ≤ f := by simp at hfuel; omega
    rw [stepPexprRaw] at hs
    cases h1 : stepPexprRaw tds ext ρ pe1 with
    | none => rw [h1] at hs; cases hs
    | some r1 =>
      cases h2 : stepPexprRaw tds ext ρ pe2 with
      | none => rw [h1, h2] at hs; cases hs
      | some r2 =>
        rw [h1, h2] at hs
        simp only [Option.bind_eq_bind, Option.bind_some] at hs
        show exception_undef_fmap (Pexpr [] ()) _ = _
        dsimp only [step_eval_peop]
        rw [ih1 h1 f hd1 (n+1) loc cloc mem file,
          ih2 h2 f hd2 (n+1) loc cloc mem file]
        dsimp only [exception_undef_bind, exception_undef_return, exception_undef_fmap,
          except_return, return1]
        cases hv1 : valueFromPexpr r1 with
        | none =>
          rw [hv1] at hs
          obtain rfl := Option.some.inj hs
          cases op <;> cases valueFromPexpr r2 <;> rfl
        | some v1 =>
          obtain rfl := stepPexprRaw_valPe_of_value h1 hv1
          cases hv2 : valueFromPexpr r2 with
          | none =>
            rw [hv1, hv2] at hs
            obtain rfl := Option.some.inj hs
            -- the engine's operator match keys on the LEFT value's head
            -- constructor before the right operand's value test
            cases op <;> cases v1 <;> (try (rename_i ov; cases ov)) <;> rfl
          | some v2 =>
            obtain rfl := stepPexprRaw_valPe_of_value h2 hv2
            rw [hv1, hv2] at hs
            dsimp only at hs
            cases hb : evalBinop op v1 v2 with
            | none => rw [hb] at hs; cases hs
            | some w =>
              rw [hb] at hs
              obtain rfl := Option.some.inj hs
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
    have hd1 : peDepth pe1 ≤ f := by simp at hfuel; omega
    have hd2 : peDepth pe2 ≤ f := by simp at hfuel; omega
    rw [stepPexprRaw] at hs
    cases h1 : stepPexprRaw tds ext ρ pe1 with
    | none => rw [h1] at hs; cases hs
    | some r1 =>
      cases h2 : stepPexprRaw tds ext ρ pe2 with
      | none => rw [h1, h2] at hs; cases hs
      | some r2 =>
        rw [h1, h2] at hs
        simp only [Option.bind_eq_bind, Option.bind_some] at hs
        show exception_undef_fmap (Pexpr [] ()) _ = _
        dsimp only
        rw [ih1 h1 f hd1 (n+1) loc cloc mem file,
          ih2 h2 f hd2 (n+1) loc cloc mem file]
        dsimp only [exception_undef_bind, exception_undef_return, exception_undef_fmap,
          except_return, return1]
        cases hv1 : valueFromPexpr r1 with
        | none =>
          rw [hv1] at hs
          obtain rfl := Option.some.inj hs
          cases valueFromPexpr r2 <;> rfl
        | some v1 =>
          obtain rfl := stepPexprRaw_valPe_of_value h1 hv1
          cases hv2 : valueFromPexpr r2 with
          | none =>
            rw [hv1, hv2] at hs
            obtain rfl := Option.some.inj hs
            cases v1 <;> (try (rename_i ov; cases ov)) <;> rfl
          | some v2 =>
            obtain rfl := stepPexprRaw_valPe_of_value h2 hv2
            rw [hv1, hv2] at hs
            dsimp only at hs
            cases hb : evalArrayShift tds ty v1 v2 with
            | none => rw [hb] at hs; cases hs
            | some w =>
              rw [hb] at hs
              obtain rfl := Option.some.inj hs
              unfold evalArrayShift at hb
              split at hb
              · cases hb; rfl
              · cases hb
  | ctorTy a c hc pb ty =>
    intro fuel hfuel n loc cloc mem file
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 :=
      ⟨fuel - 1, by
        have := peDepth_pos (Pexpr a () (PEctor c [Pexpr pb () (PEval (Vctype ty))])); omega⟩
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 :=
      ⟨f - 1, by simp only [peDepth_ctor1, peDepth_val] at hfuel; omega⟩
    rw [stepPexprRaw, stepPexprsRaw_cons, stepPexprsRaw_nil, stepPexprRaw] at hs
    simp only [Option.bind_eq_bind, Option.bind_some, valueFromPexprs_cons, valueFromPexprs_nil,
      valueFromPexpr_valPe] at hs
    cases c <;> simp only [isTyCtor, Bool.false_eq_true] at hc <;>
      simp only [evalCtor, evalTyCtor, Option.map_some] at hs <;>
      obtain rfl := Option.some.inj hs <;> rfl
  | @ctor a c hc pes hps ih =>
    intro fuel hfuel n loc cloc mem file
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    rw [stepPexprRaw] at hs
    cases hrs : stepPexprsRaw tds ext ρ pes with
    | none => rw [hrs] at hs; cases hs
    | some rs =>
      rw [hrs] at hs
      simp only [Option.bind_eq_bind, Option.bind_some] at hs
      have hmap : exception_undef_mapM
          (fun pe => step_eval_pexpr_lemFuel f tds (n + 1) loc cloc ext ρ mem file false pe)
          pes = exception_undef_return rs := by
        apply exception_undef_mapM_bridge
        have h1 := stepPexprsRaw_some_iff.mp hrs
        clear hrs hs
        induction h1 with
        | nil => exact .nil
        | cons hpr hrest ihl =>
          rename_i pe r' pes' rs'
          refine .cons ?_ (ihl (fun q hq => hps q (List.mem_cons_of_mem _ hq))
            (fun q hq => ih q (List.mem_cons_of_mem _ hq))
            (by simp only [peDepth_ctor, peDepthList_cons] at hfuel ⊢; omega))
          exact ih pe List.mem_cons_self hpr f
            (by simp only [peDepth_ctor, peDepthList_cons] at hfuel; omega)
            (n+1) loc cloc mem file
      show exception_undef_fmap (Pexpr [] ()) _ = _
      dsimp only
      rw [hmap]
      dsimp only [exception_undef_bind, exception_undef_return, exception_undef_fmap,
        except_return, return1]
      cases hvs : valueFromPexprs rs with
      | none =>
        rw [hvs] at hs
        dsimp only at hs
        obtain rfl := Option.some.inj hs
        cases c <;> rfl
      | some vs =>
        rw [hvs] at hs
        dsimp only at hs
        cases hce : evalCtor tds c vs with
        | none => rw [hce] at hs; cases hs
        | some w =>
          rw [hce] at hs
          obtain rfl := Option.some.inj hs
          unfold evalCtor at hce
          split at hce
          · simp only [evalTyCtor] at hce; obtain rfl := Option.some.inj hce; rfl
          · simp only [evalTyCtor] at hce; obtain rfl := Option.some.inj hce; rfl
          · simp only [evalTyCtor] at hce; obtain rfl := Option.some.inj hce; rfl
          · obtain rfl := Option.some.inj hce; rfl
          · obtain rfl := Option.some.inj hce; rfl
          · cases hce
  | @case_ a pe pats hpe hpats ih ihs =>
    intro fuel hfuel n loc cloc mem file
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hd : peDepth pe ≤ f := by simp at hfuel; omega
    rw [stepPexprRaw] at hs
    cases h1 : stepPexprRaw tds ext ρ pe with
    | none => rw [h1] at hs; cases hs
    | some r1 =>
      rw [h1] at hs
      simp only [Option.bind_eq_bind, Option.bind_some] at hs
      show exception_undef_fmap (Pexpr [] ()) _ = _
      dsimp only
      rw [ih h1 f hd (n+1) loc cloc mem file]
      dsimp only [exception_undef_bind, exception_undef_return, exception_undef_fmap,
        except_return, return1]
      cases hv1 : valueFromPexpr r1 with
      | none =>
        rw [hv1] at hs
        dsimp only at hs
        obtain rfl := Option.some.inj hs
        rcases r1 with ⟨a1, u1, p1⟩
        cases u1
        cases p1 <;> first | rfl | (rw [valueFromPexpr_val] at hv1; cases hv1)
      | some cval =>
        obtain rfl := stepPexprRaw_valPe_of_value h1 hv1
        rw [hv1] at hs
        dsimp only at hs
        cases hsel : select_case subst_sym_pexpr cval pats with
        | none => rw [hsel] at hs; cases hs
        | some pe'' =>
          rw [hsel] at hs
          simp only [Option.map_some] at hs
          obtain rfl := Option.some.inj hs
          dsimp only [valPe]
          rw [hsel]
          rcases pe'' with ⟨_, _, _⟩
          rfl
  | @not_ a pe hpe ih =>
    intro fuel hfuel n loc cloc mem file
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hd : peDepth pe ≤ f := by simp at hfuel; omega
    rw [stepPexprRaw] at hs
    cases h1 : stepPexprRaw tds ext ρ pe with
    | none => rw [h1] at hs; cases hs
    | some r1 =>
      rw [h1] at hs
      simp only [Option.bind_eq_bind, Option.bind_some] at hs
      -- the engine's `PEnot (pe@(Pexpr annot pe_bTy _))` arm destructures the operand
      rcases pe with ⟨ap, up, pp⟩
      cases up
      show exception_undef_fmap (Pexpr [] ()) _ = _
      dsimp only
      rw [ih h1 f hd (n+1) loc cloc mem file]
      dsimp only [exception_undef_bind, exception_undef_return, exception_undef_fmap,
        except_return, return1]
      rcases r1 with ⟨a1, u1, p1⟩
      cases u1
      cases hv1 : valueFromPexpr (Pexpr a1 () p1) with
      | none =>
        rw [hv1] at hs
        dsimp only at hs
        obtain rfl := Option.some.inj hs
        cases p1 <;> first | rfl | (rw [valueFromPexpr_val] at hv1; cases hv1)
      | some w =>
        obtain ⟨a1', hp1⟩ := valueFromPexpr_some_iff.mp hv1
        injection hp1 with _ _ hp1'
        subst hp1'
        rw [hv1] at hs
        cases w <;> dsimp only at hs <;>
          first
          | (obtain rfl := Option.some.inj hs; rfl)
          | cases hs
  | @if_ a pe1 pe2 pe3 hp1 hp2 hp3 ih1 ih2 ih3 =>
    intro fuel hfuel n loc cloc mem file
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hd1 : peDepth pe1 ≤ f := by simp at hfuel; omega
    have hd2 : peDepth pe2 ≤ f := by simp at hfuel; omega
    have hd3 : peDepth pe3 ≤ f := by simp at hfuel; omega
    rw [stepPexprRaw] at hs
    cases h1 : stepPexprRaw tds ext ρ pe1 with
    | none => rw [h1] at hs; cases hs
    | some r1 =>
      rw [h1] at hs
      simp only [Option.bind_eq_bind, Option.bind_some] at hs
      show exception_undef_fmap (Pexpr [] ()) _ = _
      dsimp only
      rw [ih1 h1 f hd1 (n+1) loc cloc mem file]
      dsimp only [exception_undef_bind, exception_undef_return, exception_undef_fmap,
        except_return, return1]
      cases hv1 : valueFromPexpr r1 with
      | none =>
        rw [hv1] at hs
        dsimp only at hs
        obtain rfl := Option.some.inj hs
        rfl
      | some w =>
        rw [hv1] at hs
        cases w <;> dsimp only at hs <;> (try (cases hs))
        case Vtrue =>
          cases h2 : stepPexprRaw tds ext ρ pe2 with
          | none => rw [h2] at hs; cases hs
          | some r2 =>
            rw [h2] at hs
            simp only [Option.map_some] at hs
            obtain rfl := Option.some.inj hs
            rw [ih2 h2 f hd2 (n+1) loc cloc mem file]
            rcases r2 with ⟨_, _, _⟩
            rfl
        case Vfalse =>
          cases h3 : stepPexprRaw tds ext ρ pe3 with
          | none => rw [h3] at hs; cases hs
          | some r3 =>
            rw [h3] at hs
            simp only [Option.map_some] at hs
            obtain rfl := Option.some.inj hs
            rw [ih3 h3 f hd3 (n+1) loc cloc mem file]
            rcases r3 with ⟨_, _, _⟩
            rfl

/-- LEVEL 3a: `eval_pexpr_aux2` (Core_eval.lean:152) iterates {pull, one
    pass, value test} until a value: at a covered term with a big-step
    value it delivers that value within `peDepth pe` passes (each pass
    strictly decreases the depth until the value, `evalPexpr_step`). The
    engine's own budgets: `peDepth pe ≤ lemDefaultFuel` for the interior
    `pull_constrained`/`step_eval_pexpr` at the default budget, and
    `peDepth pe ≤ fuel + 1` passes. E2: the pass bound is new (the pre-E2
    grammar evaluated in one pass). -/
theorem aux2_bridge {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {ext : Fmap sym sym} {ρ : EnvStack}
    {pe : generic_pexpr Unit sym} {v : value}
    (hp : PePure pe) (hv : evalPexpr tds ext ρ pe = some v)
    (hd : peDepth pe ≤ lemDefaultFuel) :
    ∀ (fuel : Nat), peDepth pe ≤ fuel + 1 →
    ∀ (loc : CerbLocation.Loc) (cloc : Option CerbLocation.Loc)
      (mem : Option CerbMem.MemState)
      (file : generic_file Unit core_run_annotation),
    eval_pexpr_aux2_lemFuel (fuel + 1) tds loc cloc ext ρ mem file pe =
      exception_undef_return (Sum.inr v) := by
  induction pe using peDepth_strong_induction generalizing v with
  | _ pe ih =>
  intro fuel hfuel loc cloc mem file
  obtain ⟨r, hr, he, hdr, hs⟩ := evalPexpr_step hp hv
  have hpull : pull_constrained 0 pe = peStrip pe :=
    pull_bridge hp lemDefaultFuel hd 0
  have hstep := step_eval_bridge hp.strip (by rw [stepPexpr_peStrip hp]; exact hr) lemDefaultFuel
    (by rw [peDepth_peStrip hp]; exact hd) 0 loc cloc mem file
  unfold eval_pexpr_aux2_lemFuel
  dsimp only [CerbDebug.print_debug_pure]
  rw [hpull]
  obtain ⟨pex, hpex, hne⟩ := peStrip_root hp
  rw [hpex] at hstep ⊢
  have hnext : ∀ (m : exceptM (t0 (generic_pexpr Unit sym)) core_run_cause),
      m = exception_undef_return r →
      exception_undef_bind m (fun pe' => match valueFromPexpr pe' with
        | some cval => exception_undef_return (Sum.inr cval)
        | none => eval_pexpr_aux2_lemFuel fuel tds loc cloc ext ρ mem file pe') =
      exception_undef_return (Sum.inr v) := by
    intro m hm
    rw [hm]
    dsimp only [exception_undef_bind, exception_undef_return, except_return, return1]
    cases hvr : valueFromPexpr r with
    | some w =>
      obtain ⟨a', rfl⟩ := valueFromPexpr_some_iff.mp hvr
      rw [evalPexpr_val] at he
      obtain rfl := Option.some.inj he
      rfl
    | none =>
      have hlt := hs hvr
      obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by have := peDepth_pos r; omega⟩
      have hpr : PePure r := evalPexpr_shape he
      exact ih r hlt hpr he (by omega) f' (by omega) loc cloc mem file
  cases pex <;> first
    | (exfalso; apply hne; rfl)
    | (exact hnext _ (by rw [show step_eval_pexpr = step_eval_pexpr_lemFuel lemDefaultFuel from rfl]; exact hstep))

/-- LEVEL 3b: `full_eval_pexpr` — the state-threaded evaluator the
    Erun/Eif certification runs against — computes the mirror's
    answer, STATE-VERBATIM (`runEU`'s shape: the whole tower is a pure
    `exceptM` computation lifted pointwise). Extern QUANTIFIED (S1b′);
    tagDefs/memory/file quantified (unread). -/
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
  rw [aux2_bridge hp hv hd 999999 (by rw [show lemDefaultFuel = 999999 + 1 from rfl] at hd; exact hd)
    th.current_loc _ (some σ) file]
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
theorem step_ctx_save {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {sb : sym × core_base_type}
    {ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
    {body : CoreExpr} {cvals : List value}
    (hd : Decomp e ctx (saveRedex an sb ps body))
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
        { locUpdTh an th with
            env := bindSaveParams ps cvals (ev0 :: evs)
            arena := apply_ctx ctx body }] := by
  have hget : get_ctx th.arena = [(ctx, saveRedex an sb ps body)] := by
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
     rw [show is_irreducible (Expr an (Esave sb ps body)) = false from rfl]
     rw [hvals']
     loc_split an) <;>
    (try dsimp only
     rw [henv]
     rfl)

/-- Ecase at a VALUE scrutinee, context undisturbed (one_step0's
    Ecase value arm — TAU into the substituted branch; the
    PEconstrained PANIC pre-arm is bypassed by the canonical value
    scrutinee's shape, the no-match ILLTYPED channel by the
    selection premise). Env verbatim, no premise. -/
theorem step_ctx_case_value {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {a : List _root_.annot} {cval : value} {pats : List (pattern × CoreExpr)}
    {e' : CoreExpr}
    (hd : Decomp e ctx (caseRedex an (Pexpr a () (PEval cval)) pats))
    (hsz : esize e ≤ lemDefaultFuel)
    (hsel : select_case subst_sym_expr cval pats = some e')
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_tau2 "Ecase" TSK_Misc
        { locUpdTh an th with arena := apply_ctx ctx e' }] := by
  have hget : get_ctx th.arena =
      [(ctx, caseRedex an (Pexpr a () (PEval cval)) pats)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold caseRedex
  cases ctx <;>
    (dsimp only [one_step0]
     rw [show is_irreducible (Expr an
       (Ecase (Pexpr a () (PEval cval)) pats)) = false from rfl]
     dsimp only [valueFromPexpr]
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
theorem stepDischarge_if_true {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
    (hd : Decomp e ctx (ifRedex an g e2 e3))
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
      [.next { locUpdTh an th with arena := apply_ctx ctx e2 } σ] := by
  have hget : get_ctx th.arena = [(ctx, ifRedex an g e2 e3)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold ifRedex
  cases ctx <;>
    (dsimp only [one_step0]
     rw [show is_irreducible (Expr an (Eif g e2 e3)) = false
       from rfl]
     dsimp only [dischargeStep]
     rw [full_eval_bridge hg hdg σ file]
     dsimp only [stExceptUndef_bind, stExceptUndef_return, stExpect_return,
       return1, except_return]
     rfl)

/-- Eif (FALSE) — symmetric. -/
theorem stepDischarge_if_false {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
    (hd : Decomp e ctx (ifRedex an g e2 e3))
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
      [.next { locUpdTh an th with arena := apply_ctx ctx e3 } σ] := by
  have hget : get_ctx th.arena = [(ctx, ifRedex an g e2 e3)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold ifRedex
  cases ctx <;>
    (dsimp only [one_step0]
     rw [show is_irreducible (Expr an (Eif g e2 e3)) = false
       from rfl]
     dsimp only [dischargeStep]
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
theorem stepDischarge_pure_sym {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {pb : List _root_.annot} {x : sym} {v : value}
    (hd : Decomp e ctx (pureRedex an (Pexpr pb () (PEsym x))))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hv : evalPexpr tds ext th.env (Pexpr pb () (PEsym x)) = some v)
    (aid : Nat) (rs : core_run_state) :
    (step_ctx tds σ file ext tid (parent, th)).map
        (dischargeStep tds aid rs σ) =
      [.next ({ locUpdTh an th with arena := apply_ctx ctx (Expr an (Epure (Pexpr [] () (PEval v)))) }) σ] := by
  have hget : get_ctx th.arena =
      [(ctx, pureRedex an (Pexpr pb () (PEsym x)))] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold pureRedex
  cases ctx <;>
    (dsimp only [one_step0, is_irreducible, valueFromPexpr]
     simp only [Bool.false_eq_true, if_false]
     dsimp only [dischargeStep]
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
  | ctorTy a c hc pb ty => rfl
  | ctor a c hc hps => rfl
  | case_ a hpe hpats => rfl
  | not_ a hpe => rfl
  | if_ a hp1 hp2 hp3 => rfl
  | undef a loc ub => rfl

/-- E2: an action operand on the covered grammar is either a NON-VALUE
    (both value tests fail) or a literal value — the two shapes the
    engine's ACTION_EVAL/ACTION_STEP dispatch distinguishes; replaces
    the pre-E2 per-constructor casing (whose 10×10 product at two
    operands is a representation smell, not structure). -/
theorem act_valueFromPexpr_cases {pe : generic_pexpr Unit sym} (hp : PePure pe) :
    (valueFromPexpr pe = none ∧ act_valueFromPexpr pe = none) ∨
    (∃ a v, pe = Pexpr a () (PEval v)) := by
  cases hv : valueFromPexpr pe with
  | none => exact .inl ⟨rfl, act_valueFromPexpr_none hp hv⟩
  | some v =>
    obtain ⟨a, rfl⟩ := valueFromPexpr_some_iff.mp hv
    exact .inr ⟨a, v, rfl⟩

/-- A covered operand is never `PEconstrained` (step_action's Store0
    pre-arm, Core_reduction.lean:424). -/
theorem PePure.not_constrained {pe : generic_pexpr Unit _root_.sym} (hp : PePure pe) :
    ∀ (a : List _root_.annot) (u : Unit)
      (xs : List (mem_iv_constraint × generic_pexpr Unit _root_.sym)),
      pe ≠ Pexpr a u (PEconstrained xs) := by
  cases hp <;> intro a u xs h <;> cases h

/-- A covered operand pair that is not all values has a non-value member
    (the engine's per-operand value test). -/
theorem act_none_of_pair {pe1 pe2 : generic_pexpr Unit sym}
    (hp1 : PePure pe1) (hp2 : PePure pe2) (hnv : valueFromPexprs [pe1, pe2] = none) :
    act_valueFromPexpr pe1 = none ∨ act_valueFromPexpr pe2 = none := by
  rw [valueFromPexprs_pair] at hnv
  cases h1 : valueFromPexpr pe1 with
  | none => exact .inl (act_valueFromPexpr_none hp1 h1)
  | some v1 =>
    cases h2 : valueFromPexpr pe2 with
    | none => exact .inr (act_valueFromPexpr_none hp2 h2)
    | some v2 => rw [h1, h2] at hnv; cases hnv

/-! ### `step_action`'s ACTION_EVAL arms, once (Core_reduction.lean:424):
the dispatch on the operands' value tests falls to the EVAL arm whenever
some operand is not a value. Proved once per action kind by case analysis
on the value tests — the consumers (the `step_ctx_*_eval*` equations)
rewrite with these instead of unfolding `step_action` under every
context/operand-shape case (E2: the covered grammar's ten constructors
made that product a heartbeat smell). -/

theorem step_action_store_eval {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {e_annots : List _root_.annot}
    {fe : generic_pexpr Unit sym → core_run_state →
      exceptM ((t0 value × core_run_state)) core_run_cause}
    {excl : Option Nat} {loc1 : CerbLocation.Loc} {act_annots : core_run_annotation}
    {lk : Bool} {pe1 pe2 pe3 : generic_pexpr Unit sym} {mo : memory_order}
    (hnv : act_valueFromPexpr pe1 = none ∨ act_valueFromPexpr pe2 = none ∨
      act_valueFromPexpr pe3 = none)
    (hnc : ∀ (a : List _root_.annot) (u : Unit)
      (xs : List (mem_iv_constraint × generic_pexpr Unit sym)), pe3 ≠ Pexpr a u (PEconstrained xs)) :
    step_action tds e_annots fe excl (Action loc1 act_annots (Store0 lk pe1 pe2 pe3 mo)) =
      ACTION_EVAL "eval operands of Store" (stExceptUndef_bind (fe pe1) (fun cval1 =>
        stExceptUndef_bind (fe pe2) (fun cval2 => stExceptUndef_bind (fe pe3) (fun cval3 =>
          stExceptUndef_return (Action loc1 act_annots
            (Store0 lk (mk_value_pe cval1) (mk_value_pe cval2) (mk_value_pe cval3) mo)))))) := by
  rcases pe3 with ⟨a3, u3, p3⟩
  cases u3
  cases p3 <;> first
    | exact absurd rfl (hnc _ _ _)
    | (unfold step_action
       dsimp only
       split <;> first
         | rfl
         | (exfalso
            rcases hnv with h | h | h <;> simp only [h, reduceCtorEq] at *))

theorem step_action_load_eval {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {e_annots : List _root_.annot}
    {fe : generic_pexpr Unit sym → core_run_state →
      exceptM ((t0 value × core_run_state)) core_run_cause}
    {excl : Option Nat} {loc1 : CerbLocation.Loc} {act_annots : core_run_annotation}
    {pe1 pe2 : generic_pexpr Unit sym} {mo : memory_order}
    (hnv : act_valueFromPexpr pe1 = none ∨ act_valueFromPexpr pe2 = none) :
    step_action tds e_annots fe excl (Action loc1 act_annots (Load0 pe1 pe2 mo)) =
      ACTION_EVAL "eval operands of Load" (stExceptUndef_bind (fe pe1) (fun cval1 =>
        stExceptUndef_bind (fe pe2) (fun cval2 =>
          stExceptUndef_return (Action loc1 act_annots
            (Load0 (mk_value_pe cval1) (mk_value_pe cval2) mo))))) := by
  unfold step_action
  dsimp only
  split <;> first
    | rfl
    | (exfalso
       rcases hnv with h | h <;> simp only [h, reduceCtorEq] at *)

theorem step_action_create_eval {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {e_annots : List _root_.annot}
    {fe : generic_pexpr Unit sym → core_run_state →
      exceptM ((t0 value × core_run_state)) core_run_cause}
    {excl : Option Nat} {loc1 : CerbLocation.Loc} {act_annots : core_run_annotation}
    {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0}
    (hnv : act_valueFromPexpr pe1 = none ∨ act_valueFromPexpr pe2 = none) :
    step_action tds e_annots fe excl (Action loc1 act_annots (Create pe1 pe2 pref)) =
      ACTION_EVAL "eval operands of Create" (stExceptUndef_bind (fe pe1) (fun cval1 =>
        stExceptUndef_bind (fe pe2) (fun cval2 =>
          stExceptUndef_return (Action loc1 act_annots
            (Create (mk_value_pe cval1) (mk_value_pe cval2) pref))))) := by
  unfold step_action
  dsimp only
  split <;> first
    | rfl
    | (exfalso
       rcases hnv with h | h <;> simp only [h, reduceCtorEq] at *)

theorem step_action_alloc_eval {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {e_annots : List _root_.annot}
    {fe : generic_pexpr Unit sym → core_run_state →
      exceptM ((t0 value × core_run_state)) core_run_cause}
    {excl : Option Nat} {loc1 : CerbLocation.Loc} {act_annots : core_run_annotation}
    {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0}
    (hnv : act_valueFromPexpr pe1 = none ∨ act_valueFromPexpr pe2 = none) :
    step_action tds e_annots fe excl (Action loc1 act_annots (Alloc0 pe1 pe2 pref)) =
      ACTION_EVAL "eval operands of Alloc" (stExceptUndef_bind (fe pe1) (fun cval1 =>
        stExceptUndef_bind (fe pe2) (fun cval2 =>
          stExceptUndef_return (Action loc1 act_annots
            (Alloc0 (mk_value_pe cval1) (mk_value_pe cval2) pref))))) := by
  unfold step_action
  dsimp only
  split <;> first
    | rfl
    | (exfalso
       rcases hnv with h | h <;> simp only [h, reduceCtorEq] at *)

theorem step_action_kill_eval {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {e_annots : List _root_.annot}
    {fe : generic_pexpr Unit sym → core_run_state →
      exceptM ((t0 value × core_run_state)) core_run_cause}
    {excl : Option Nat} {loc1 : CerbLocation.Loc} {act_annots : core_run_annotation}
    {kind : kill_kind} {pe : generic_pexpr Unit sym}
    (hnv : act_valueFromPexpr pe = none) :
    step_action tds e_annots fe excl (Action loc1 act_annots (Kill kind pe)) =
      ACTION_EVAL "eval operand of Kill" (stExceptUndef_bind (fe pe) (fun cval =>
        stExceptUndef_return (Action loc1 act_annots (Kill kind (mk_value_pe cval))))) := by
  unfold step_action
  dsimp only
  rw [hnv]

/-- Load ACTION_EVAL, context undisturbed, DISCHARGED (S4 —
    step_action's Load0 `_, _` arm + process_action's ACTION_EVAL
    wrap): ONE engine step big-step-evaluating the operands (the
    canonical type operand's re-evaluation is the identity; the
    pointer operand through the certified evaluator), run state
    VERBATIM (∀ rs), env/memory verbatim; the successor rebuilds the
    CANONICAL LOAD REDEX in context — the certified load equation
    takes over at the next step. -/
theorem stepDischarge_load_eval {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pe2 : generic_pexpr Unit sym} {mo : memory_order}
    {pv : CerbMem.PointerValue}
    (hd : Decomp e ctx (loadOpRedex an loc ann ty pe2 mo))
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
      [.next { locUpdTh an th with arena := apply_ctx ctx (loadRedex an loc ann ty pv mo) }
        σ] := by
  have hget : get_ctx th.arena = [(ctx, loadOpRedex an loc ann ty pe2 mo)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold loadOpRedex
  cases ctx <;>
    (dsimp only [step_action]
     rw [act_valueFromPexpr_none hp2 hnv2]
     dsimp only [act_valueFromPexpr, valueFromPexpr]
     dsimp only [dischargeStep]
     rw [full_eval_bridge (v := Vctype ty) (evalPexpr_val _ _ _ _ _) (peDepth_val_le _ _) σ file,
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
theorem stepDischarge_kill_eval {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {kind : kill_kind}
    {pe : generic_pexpr Unit sym} {pv : CerbMem.PointerValue}
    (hd : Decomp e ctx (killOpRedex an loc ann kind pe))
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
      [.next { locUpdTh an th with arena := apply_ctx ctx (killRedex an loc ann kind pv) }
        σ] := by
  have hget : get_ctx th.arena = [(ctx, killOpRedex an loc ann kind pe)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold killOpRedex
  cases ctx <;>
    (dsimp only [step_action]
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
theorem step_ctx_beta_spec_pure {an a1 b1 : List _root_.annot} {e : CoreExpr} {ctx : context}
    {pa pb : List _root_.annot} {x : sym} {bty : core_base_type}
    {ov : object_value} {e2 : CoreExpr}
    (hd : Decomp e ctx
      (Expr an (Esseq (specPat pa pb x bty)
        (ofValA (.pure a1 b1 (Vloaded (LVspecified ov)))) e2)))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    (henv : th.env = ev0 :: evs) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_tau2 "Esseq" TSK_Misc
        ({ locUpdTh an th with
            env := update_env (specPat pa pb x bty)
              (Vloaded (LVspecified ov)) (ev0 :: evs),
            arena := apply_ctx ctx e2 })] := by
  have hget : get_ctx th.arena =
      [(ctx, Expr an (Esseq (specPat pa pb x bty)
        (ofValA (.pure a1 b1 (Vloaded (LVspecified ov)))) e2))] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  cases ctx <;>
    (simp only [one_step0, ofValA, is_irreducible_sseq, Bool.false_eq_true,
       if_false, valueFromPexpr]
     loc_split an) <;>
    (dsimp only [update_env]
     rw [henv]
     try rfl)

/-- LETS-ANNOT at the Specified-binder pattern, context
    undisturbed (S4). -/
theorem step_ctx_beta_spec_annot {an a1 a2 b1 : List _root_.annot} {e : CoreExpr} {ctx : context}
    {pa pb : List _root_.annot} {x : sym} {bty : core_base_type}
    {ds : List dyn_annotation} {ov : object_value} {e2 : CoreExpr}
    (hd : Decomp e ctx
      (Expr an (Esseq (specPat pa pb x bty)
        (ofValA (.annot a1 a2 b1 ds (Vloaded (LVspecified ov)))) e2)))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    (henv : th.env = ev0 :: evs) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_tau2 "Esseq Eannot" TSK_Misc
        ({ locUpdTh an th with
            env := update_env (specPat pa pb x bty)
              (Vloaded (LVspecified ov)) (ev0 :: evs),
            arena := apply_ctx ctx (Expr [] (Eannot ds e2)) })] := by
  have hget : get_ctx th.arena =
      [(ctx, Expr an (Esseq (specPat pa pb x bty)
        (ofValA (.annot a1 a2 b1 ds (Vloaded (LVspecified ov)))) e2))] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  cases ctx <;>
    (simp only [one_step0, ofValA, is_irreducible_sseq, Bool.false_eq_true,
       if_false, valueFromPexpr]
     loc_split an) <;>
    (dsimp only [update_env]
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
      try dsimp only []
      rw [stExceptUndef_return_apply]
      try dsimp only []
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
theorem stepDischarge_run {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {ra : core_run_annotation} {l : sym}
    {pes : List (generic_pexpr Unit sym)}
    (hd : Decomp e ctx (runRedex an ra l pes))
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
      [.next { locUpdTh an th with env := bindArgs params vs th.env, arena := cont } σ] := by
  have hget : get_ctx th.arena = [(ctx, runRedex an ra l pes)] := by
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
  cases ctx <;> (loc_split an) <;>
    (try dsimp only
     rw [hproc]
     dsimp only [dischargeStep]
     rw [stExceptUndef_bind_apply, runSE_read_apply]
     try dsimp only []
     -- the engine's proc indirection is the mirror's `resolveExtern`,
     -- case by case on the lookup (S1b′ — the sym-arm precedent)
     cases hres : fmapLookupBy (fun (sym1 : sym) (sym2 : sym) =>
         Lem_Basic_classes.ordCompare sym1 sym2) p ext with
     | none =>
       rw [show resolveExtern ext p = p by
         unfold resolveExtern; rw [hres]] at hQ'
       try dsimp only []
       rw [hQ', bind0_some, hl']
       try dsimp only []
       rw [stExceptUndef_bind_apply,
         foldM_args_bridge _ (fun _ _ _ _ _ => rfl) params pes vs th.env rs
           hvs hdep]
       try dsimp only []
       rw [stExceptUndef_return_apply]
     | some y =>
       rw [show resolveExtern ext p = y by
         unfold resolveExtern; rw [hres]] at hQ'
       try dsimp only []
       rw [hQ', bind0_some, hl']
       try dsimp only []
       rw [stExceptUndef_bind_apply,
         foldM_args_bridge _ (fun _ _ _ _ _ => rfl) params pes vs th.env rs
           hvs hdep]
       try dsimp only []
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
theorem step_ctx_memop {an : List _root_.annot} {e : CoreExpr} {ctx : context} {mop : memop}
    {pe1 pe2 : generic_pexpr Unit sym} {v1 v2 : value}
    (hd : Decomp e ctx (memopRedex an mop [pe1, pe2]))
    (hsz : esize e ≤ lemDefaultFuel)
    (hv1 : valueFromPexpr pe1 = some v1)
    (hv2 : valueFromPexpr pe2 = some v2)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_memop_request2 (locUpdTh an th).current_loc mop [v1, v2] tid
        (is_unseq_with_ccall ctx)
        (fun cval => { locUpdTh an th with
          arena :=
            apply_ctx ctx (Expr [] (Epure (Pexpr [] () (PEval cval)))) })] := by
  have hget : get_ctx th.arena = [(ctx, memopRedex an mop [pe1, pe2])] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold memopRedex
  cases ctx <;>
    (dsimp only [one_step0]
     rw [show is_irreducible (Expr an (Ememop mop [pe1, pe2]))
       = false from rfl]
     rw [valueFromPexprs_pair, hv1, hv2]
     loc_split an) <;> rfl

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
  rw [aux2_bridge hp hv hdp 999999
    (by rw [show lemDefaultFuel = 999999 + 1 from rfl] at hdp; exact hdp) th.current_loc _ (some σ) file]
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
theorem step_ctx_call_ws {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {ra : core_run_annotation} {f : sym} {pes : List (generic_pexpr Unit sym)}
    (hd : Decomp e ctx (callRedex an ra f pes))
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
        { locUpdTh an th with
          current_proc_opt := some f
          env := procEnv params vs :: th.env
          exec_loc := push_exec_loc f (locUpdTh an th).current_loc th.exec_loc
          stack0 := Stack_cons2 th.current_proc_opt ctx th.stack0
          arena := body }, rs) := by
  have hget : get_ctx th.arena = [(ctx, callRedex an ra f pes)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold callRedex
  cases ctx <;>
    (refine ⟨_, rfl, fun rs => ?_⟩
     rw [stExceptUndef_bind_apply,
       mapM_full_eval_bridge _ (fun _ _ => rfl) pes hvs hdep rs]
     try dsimp only []
     rw [stExceptUndef_bind_apply, call_proc_of_lookupProc hf hlen]
     loc_split an) <;> rfl

/-- The PCALL round's SHAPE alone (any lookup outcome, any arguments):
    one `RSK_eval "Eproc"` with-runstate step. -/
theorem step_ctx_call_shape {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {ra : core_run_annotation} {f : sym} {pes : List (generic_pexpr Unit sym)}
    (hd : Decomp e ctx (callRedex an ra f pes))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e) :
    ∃ m : core_runM thread_state,
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval "Eproc") m] := by
  have hget : get_ctx th.arena = [(ctx, callRedex an ra f pes)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold callRedex
  cases ctx <;>
    (exact ⟨_, rfl⟩)

/-- The PCALL round at an UNKNOWN procedure (arguments evaluating): the
    monad RAISES `Illformed_program "calling an unknown procedure: …"` —
    the driver's transparent kill `Other (DErr_core_run …)`
    (`liftCore_run`, Driver.lean:245). -/
theorem step_ctx_call_unknown {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {ra : core_run_annotation} {f : sym} {pes : List (generic_pexpr Unit sym)}
    (hd : Decomp e ctx (callRedex an ra f pes))
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
  have hget : get_ctx th.arena = [(ctx, callRedex an ra f pes)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold callRedex
  cases ctx <;>
    (refine ⟨_, rfl, fun rs => ?_⟩
     rw [stExceptUndef_bind_apply,
       mapM_full_eval_bridge _ (fun _ _ => rfl) pes hvs hdep rs]
     try dsimp only []
     rw [stExceptUndef_bind_apply, call_proc_unknown hf]
     rfl)

/-- The PCALL round at an ARITY MISMATCH (arguments evaluating): the
    monad RAISES `Illformed_program "calling procedure `f' with the wrong
    number of args: …"` — the driver's transparent kill. -/
theorem step_ctx_call_arity {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {ra : core_run_annotation} {f : sym} {pes : List (generic_pexpr Unit sym)}
    (hd : Decomp e ctx (callRedex an ra f pes))
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
  have hget : get_ctx th.arena = [(ctx, callRedex an ra f pes)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold callRedex
  cases ctx <;>
    (refine ⟨_, rfl, fun rs => ?_⟩
     rw [stExceptUndef_bind_apply,
       mapM_full_eval_bridge _ (fun _ _ => rfl) pes hvs hdep rs]
     try dsimp only []
     rw [stExceptUndef_bind_apply, call_proc_arity hf hlen]
     rfl)

/-- Esave PARAMETER EVALUATION, context undisturbed, DISCHARGED
    (one_step0's Esave EVAL arm + step_ctx's EVAL wrap + the
    liftCore_run protocol): ONE engine step mapping `eval_pexpr1` over
    the initializers (`mapM_save_bridge`), run state VERBATIM,
    env/memory verbatim; the successor rebuilds the Esave node with
    the evaluated initializers in context. -/
theorem stepDischarge_save_eval {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {sb : sym × core_base_type}
    {ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
    {body : CoreExpr} {cvals : List value}
    (hd : Decomp e ctx (saveRedex an sb ps body))
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
      [.next { locUpdTh an th with
        arena := apply_ctx ctx (saveRedex an sb (saveParamsWithValues ps cvals) body) } σ] := by
  have hget : get_ctx th.arena = [(ctx, saveRedex an sb ps body)] := by
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
     rw [show is_irreducible (Expr an (Esave sb ps body)) = false from rfl]
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
theorem stepDischarge_memop_eval {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {mop : memop} {pe1 pe2 : generic_pexpr Unit sym} {v1 v2 : value}
    (hd : Decomp e ctx (memopRedex an mop [pe1, pe2]))
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
      [.next { locUpdTh an th with arena := apply_ctx ctx (Expr an (Ememop mop
        [Pexpr [] () (PEval v1), Pexpr [] () (PEval v2)])) } σ] := by
  have hget : get_ctx th.arena = [(ctx, memopRedex an mop [pe1, pe2])] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold memopRedex
  cases ctx <;>
    (dsimp only [one_step0]
     rw [show is_irreducible (Expr an (Ememop mop [pe1, pe2]))
       = false from rfl]
     rw [hnv]
     simp only [Bool.false_eq_true, if_false]
     dsimp only [dischargeStep]
     rw [stExceptUndef_bind_apply, stExceptUndef_bind_apply,
       mapM_eval1_bridge (tds := tds) (σ := σ) (file := file)
         _ ?_ hv1 hd1 hv2 hd2 rs] <;>
       first
         | (intro pe rs'
            rfl)
         | (loc_split an <;> rfl))

/-- Store ACTION_EVAL, context undisturbed, DISCHARGED (step_action's
    Store0 `_, _, _` arm + process_action's ACTION_EVAL wrap): ONE
    engine step big-step-evaluating the three operands (the canonical
    type operand's re-evaluation is the identity; pointer and value
    operands through the certified evaluator), run state VERBATIM
    (∀ rs), env/memory verbatim; the successor rebuilds the CANONICAL
    STORE REDEX in context. `hp3` cases the value operand's head
    constructor so the engine's `Store0 … PEconstrained` failwithI
    pre-arm reduces past (the covered grammar has no PEconstrained). -/
theorem stepDischarge_store_eval {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pe2 pe3 : generic_pexpr Unit sym} {mo : memory_order}
    {pv : CerbMem.PointerValue} {cv : value}
    (hd : Decomp e ctx (storeOpRedex an loc ann ty pe2 pe3 mo))
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
      [.next { locUpdTh an th with arena := apply_ctx ctx (storeRedex an loc ann false ty
        pv cv mo) } σ] := by
  have hget : get_ctx th.arena = [(ctx, storeOpRedex an loc ann ty pe2 pe3 mo)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold storeOpRedex
  rw [valueFromPexprs_pair] at hnv
  rcases act_valueFromPexpr_cases hp2 with ⟨hn2, ha2⟩ | ⟨a2, v2', rfl⟩ <;>
  cases hp3
  all_goals try (rw [valueFromPexpr_val, valueFromPexpr_val] at hnv; cases hnv)
  all_goals try (obtain rfl := Option.some.inj ((evalPexpr_val _ _ _ _ _).symm.trans hv2))
  all_goals
    cases ctx <;>
      (dsimp only [step_action]
       try rw [ha2]
       dsimp only [act_valueFromPexpr, valueFromPexpr]
       dsimp only [dischargeStep]
       rw [full_eval_bridge (v := Vctype ty) (evalPexpr_val _ _ _ _ _) (peDepth_val_le _ _) σ file,
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
theorem stepDischarge_alloc_eval {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0}
    {align size : CerbMem.IntegerValue}
    (hd : Decomp e ctx (allocOpRedex an loc ann pe1 pe2 pref))
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
      [.next { locUpdTh an th with arena := apply_ctx ctx (allocRedex an loc ann align size pref) } σ] := by
  have hget : get_ctx th.arena = [(ctx, allocOpRedex an loc ann pe1 pe2 pref)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold allocOpRedex
  rw [valueFromPexprs_pair] at hnv
  rcases act_valueFromPexpr_cases hp1 with ⟨hn1, ha1⟩ | ⟨a1, v1', rfl⟩ <;>
  rcases act_valueFromPexpr_cases hp2 with ⟨hn2, ha2⟩ | ⟨a2, v2', rfl⟩
  all_goals try (rw [valueFromPexpr_val, valueFromPexpr_val] at hnv; cases hnv)
  all_goals try (obtain rfl := Option.some.inj ((evalPexpr_val _ _ _ _ _).symm.trans hv1))
  all_goals try (obtain rfl := Option.some.inj ((evalPexpr_val _ _ _ _ _).symm.trans hv2))
  all_goals
    cases ctx <;>
      (dsimp only [step_action]
       try rw [ha1]
       try rw [ha2]
       try dsimp only [act_valueFromPexpr, valueFromPexpr]
       dsimp only [dischargeStep]
       rw [full_eval_bridge hv1 hd1 σ file, full_eval_bridge hv2 hd2 σ file]
       dsimp only [stExceptUndef_bind, stExceptUndef_return, stExpect_return,
         return1, except_return]
       rfl)


/-- E1: Create ACTION_EVAL, context undisturbed, DISCHARGED (step_action's
    Create `_, _` arm + process_action's ACTION_EVAL wrap,
    Core_reduction.lean:424): ONE engine step big-step-evaluating the two
    operands (alignment first — the emitted `Ivalignof(ty)` — then the
    ctype) through the certified evaluator, run state VERBATIM (∀ rs),
    env/memory verbatim; the successor rebuilds the CANONICAL CREATE
    REDEX in context. -/
theorem stepDischarge_create_eval {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0}
    {align : CerbMem.IntegerValue} {ty : ctype}
    (hd : Decomp e ctx (createOpRedex an loc ann pe1 pe2 pref))
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
    (hv2 : evalPexpr tds ext th.env pe2 = some (Vctype ty))
    (aid : Nat) (rs : core_run_state) :
    (step_ctx tds σ file ext tid (parent, th)).map
        (dischargeStep tds aid rs σ) =
      [.next { locUpdTh an th with arena := apply_ctx ctx (createRedex an loc ann align ty pref) } σ] := by
  have hget : get_ctx th.arena = [(ctx, createOpRedex an loc ann pe1 pe2 pref)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold createOpRedex
  rw [valueFromPexprs_pair] at hnv
  rcases act_valueFromPexpr_cases hp1 with ⟨hn1, ha1⟩ | ⟨a1, v1', rfl⟩ <;>
  rcases act_valueFromPexpr_cases hp2 with ⟨hn2, ha2⟩ | ⟨a2, v2', rfl⟩
  all_goals try (rw [valueFromPexpr_val, valueFromPexpr_val] at hnv; cases hnv)
  all_goals try (obtain rfl := Option.some.inj ((evalPexpr_val _ _ _ _ _).symm.trans hv1))
  all_goals try (obtain rfl := Option.some.inj ((evalPexpr_val _ _ _ _ _).symm.trans hv2))
  all_goals
    cases ctx <;>
      (dsimp only [step_action]
       try rw [ha1]
       try rw [ha2]
       try dsimp only [act_valueFromPexpr, valueFromPexpr]
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
theorem step_ctx_beta_sym_pure {an a1 b1 : List _root_.annot} {e : CoreExpr} {ctx : context}
    {pa : List _root_.annot} {x : sym} {bty : core_base_type}
    {v : value} {e2 : CoreExpr}
    (hd : Decomp e ctx
      (Expr an (Esseq (symPat pa x bty) (ofValA (.pure a1 b1 v)) e2)))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    (henv : th.env = ev0 :: evs) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_tau2 "Esseq" TSK_Misc
        ({ locUpdTh an th with
            env := update_env (symPat pa x bty) v (ev0 :: evs),
            arena := apply_ctx ctx e2 })] := by
  have hget : get_ctx th.arena =
      [(ctx, Expr an (Esseq (symPat pa x bty) (ofValA (.pure a1 b1 v)) e2))] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  cases ctx <;>
    (simp only [one_step0, ofValA, is_irreducible_sseq, Bool.false_eq_true,
       if_false, valueFromPexpr]
     loc_split an) <;>
    (dsimp only [update_env]
     rw [henv]
     try rfl)


/-- E1: LETS-ANNOT at the plain-symbol binder, context undisturbed
    (one_step0's Esseq Eannot arm, "reduction: LETS-ANNOT" — the shape
    the pre-E1 mirror did not cover; now `Step.sseq_sym_annot`): the
    engine's tau with the one-binding env update, the dynamic
    annotations re-wrapped around the continuation. -/
theorem step_ctx_beta_sym_annot {an a1 a2 b1 : List _root_.annot} {e : CoreExpr} {ctx : context}
    {pa : List _root_.annot} {x : sym} {bty : core_base_type}
    {ds : List dyn_annotation} {v : value} {e2 : CoreExpr}
    (hd : Decomp e ctx
      (Expr an (Esseq (symPat pa x bty) (ofValA (.annot a1 a2 b1 ds v)) e2)))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    (henv : th.env = ev0 :: evs) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_tau2 "Esseq Eannot" TSK_Misc
        ({ locUpdTh an th with
            env := update_env (symPat pa x bty) v (ev0 :: evs),
            arena := apply_ctx ctx (Expr [] (Eannot ds e2)) })] := by
  have hget : get_ctx th.arena =
      [(ctx, Expr an (Esseq (symPat pa x bty) (ofValA (.annot a1 a2 b1 ds v)) e2))] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  cases ctx <;>
    (simp only [one_step0, ofValA, is_irreducible_sseq, Bool.false_eq_true,
       if_false, valueFromPexpr]
     loc_split an) <;>
    (dsimp only [update_env]
     rw [henv]
     try rfl)

/-! ### The fragment `Frag` and the step-match

`Frag` is the per-construct authority of every adequacy theorem: the
straight-line shapes plus Esave, Eif (with the guard's static
evaluator-fuel bound), Erun (with the arguments'), value-scrutinee
Ecase (`Frag.case_value` below, with explicit branch-closure and
branch-size premises), wildcard Ewseq and (E1) `bound`. Registered
continuations enter through the SIDE hypothesis `hQf` (the label map's
own membership), which breaks the circularity a label-indexed fragment
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
`run`, `save`, `load_op`, `memop_op`, `store_op`, `create_op`), and
EVERY such constructor restricts its operands to the covered sub-grammar
`PePure` (values, symbols, the eight mirrored binops, array shifts, and
— E1 — the constructor constants `Ivalignof(ty)`/`Ivsizeof(ty)` at a
literal ctype) — the mirror evaluator's exact domain (fragment closure,
2026-09-02: before it, `if_`/`run`/`save` took any operand and `PePure`
admitted every binop). Both are `rfl` for authored programs
(`peDepth_sym_le`, `peDepth_val_le`, `PePure.of_isPePure rfl`). Where
the mirror evaluator answers `none` on a `PePure` operand, the engine's
outcome is classified (EvalClass.lean, Round.lean): a proved engine KILL
where the classifier `evalClass` rejects the operand, the residual
`OpenRound.eval_uncovered` where the classifier leaves it uncovered —
decided at the first uncovered LEAF, so the whole operand's outcome
there is NOT characterized (the residual is a superset of the
engine-accepted shapes; EvalClass.lean header).

THE FRAGMENT IS ANNOTATED (E1, docs/2026-09-04_e1-notes.md): every
constructor below and every redex spelling it ranges over carries the
node's static annotation list `an : List _root_.annot` (`Expr an …`). The
engine reads them in exactly one place — the general arm of `step_ctx`
(Core_reduction.lean:484, `let maybe_loc := get_loc e_annots`) rewrites
the thread's `current_loc` from the REDEX node's first `Aloc`, unless it
is a library location — and the mirror mirrors that write as
`Ctl.upd a` (Step.lean) on the live control's `curLoc`; the value arms
(PROGRAM-DONE / RETURN / REMOVE-ANNOT / REMOVE-BOUND-at-value's
successor) and get_ctx are annotation-inert. The pre-E1 fragment was
annotation-free (`Expr []` everywhere) because `currentLoc` lived in the
immutable `MachineCtx`; that forcing fact is gone.

THE PLAIN-SYMBOL BINDER (E1): `Frag.sseq_sym` admits ANY fragment head.
The pre-E1 `BareHead` restriction excluded the LETS-ANNOT beta (the
engine binds a plain symbol at an annotated value too — one_step0's
Esseq Eannot arm, "reduction: LETS-ANNOT") because the mirror lacked the
rule; E1 mirrors it (`Step.sseq_sym_annot`, certified by
`step_ctx_beta_sym_annot`), so the head grammar is the fragment itself
and `BareHead` is retired. -/

inductive Frag : CoreExpr → Prop where
  | val_pure {a b : List _root_.annot} (v : value) : Frag (Expr a (Epure (Pexpr b () (PEval v))))
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
  | store {an : List _root_.annot} {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
      {ty : ctype} {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order} :
      Frag (storeRedex an loc ann lk ty pv cv mo)
  | load {an : List _root_.annot} {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
      {pv : CerbMem.PointerValue} {mo : memory_order} :
      Frag (loadRedex an loc ann ty pv mo)
  | create {an : List _root_.annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {align : CerbMem.IntegerValue} {ty : ctype} {pref : prefix0} :
      Frag (createRedex an loc ann align ty pref)
  /-- E1: `create` at operands in the covered grammar `PePure` that are
      not all values (the emitted `create(Ivalignof(ty), ty)`), within
      the evaluator's fuel — the ACTION_EVAL form (step_action's Create
      `_, _` arm, Core_reduction.lean:424 region). -/
  | create_op {an : List _root_.annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0}
      (hnv : valueFromPexprs [pe1, pe2] = none)
      (hp1 : PePure pe1) (hp2 : PePure pe2)
      (hd1 : peDepth pe1 ≤ lemDefaultFuel)
      (hd2 : peDepth pe2 ≤ lemDefaultFuel) :
      Frag (createOpRedex an loc ann pe1 pe2 pref)
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
  | kill {an : List _root_.annot} {loc : CerbLocation.Loc} {ann : core_run_annotation} {kind : kill_kind}
      {pv : CerbMem.PointerValue} :
      Frag (killRedex an loc ann kind pv)
  /-- The kill of either kind at an operand in the covered grammar
      `PePure`, within the evaluator's fuel (the ACTION_EVAL form). -/
  | kill_op {an : List _root_.annot} {loc : CerbLocation.Loc} {ann : core_run_annotation} {kind : kill_kind}
      {pe : generic_pexpr Unit sym}
      (hnv : valueFromPexpr pe = none) (hp : PePure pe)
      (hdp : peDepth pe ≤ lemDefaultFuel) :
      Frag (killOpRedex an loc ann kind pe)
  /-- DYNAMIC ALLOCATION at canonical evaluated INTEGER operands
      (kill/free arc K3): `alloc(al, n)` — Core's `Alloc0`, C's `malloc`
      (the region is untyped, of raw size `n.toNat` — ZERO admitted —
      and dynamic). -/
  | alloc {an : List _root_.annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {align size : CerbMem.IntegerValue} {pref : prefix0} :
      Frag (allocRedex an loc ann align size pref)
  /-- Dynamic allocation at operands in the covered grammar `PePure`
      that are not all values, within the evaluator's fuel (the
      ACTION_EVAL form; mixed shapes included, as `store_op`). -/
  | alloc_op {an : List _root_.annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0}
      (hnv : valueFromPexprs [pe1, pe2] = none)
      (hp1 : PePure pe1) (hp2 : PePure pe2)
      (hd1 : peDepth pe1 ≤ lemDefaultFuel)
      (hd2 : peDepth pe2 ≤ lemDefaultFuel) :
      Frag (allocOpRedex an loc ann pe1 pe2 pref)
  | sseq {an pa : List _root_.annot} {bty : core_base_type} {e1 e2 : CoreExpr} :
      Frag e1 → Frag e2 →
      Frag (Expr an (Esseq (Pattern pa (CaseBase (none, bty))) e1 e2))
  | annot {an : List _root_.annot} {ds : List dyn_annotation} {b : CoreExpr} :
      Frag b → Frag (Expr an (Eannot ds b))
  /-- E1: `bound(e)` — the emitted wrapper around every full-expression
      statement (`Ebound`; get_ctx's Ebound arm / `Cbound` frame,
      REMOVE-BOUND at a value, core_reduction.lem:563–568, 1214–1226). -/
  | bound {an : List _root_.annot} {b : CoreExpr} :
      Frag b → Frag (Expr an (Ebound b))
  /-- Esave at ANY initializers within the evaluator's fuel (the
      engine's TAU arm at value initializers, its EVAL arm otherwise —
      `Step.save`/`Step.save_eval`). `hd` is the same static
      evaluator-fuel bound `if_`/`run` carry for their pure operands;
      literal initializers satisfy it trivially
      (`saveParams_depth_of_vals`). -/
  | save {an : List _root_.annot} {sb : sym × core_base_type}
      {ps : List (sym × ((core_base_type ×
        Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
      {body : CoreExpr}
      (hp : ∀ pe ∈ saveParamPexprs ps, PePure pe)
      (hd : ∀ pe ∈ saveParamPexprs ps, peDepth pe ≤ lemDefaultFuel) :
      Frag body → Frag (saveRedex an sb ps body)
  /-- Eif at a guard in the covered operand grammar `PePure`, within the
      evaluator's fuel (fragment closure, 2026-09-02: the operand grammar
      of every evaluating constructor is `PePure` — the mirror evaluator's
      exact domain — so an operand the mirror cannot evaluate is
      classified in the engine, `complete_if`). -/
  | if_ {an : List _root_.annot} {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
      (hpg : PePure g) (hdg : peDepth g ≤ lemDefaultFuel) :
      Frag e2 → Frag e3 → Frag (ifRedex an g e2 e3)
  /-- Erun at arguments in `PePure`, within the evaluator's fuel. -/
  | run {an : List _root_.annot} {ra : core_run_annotation} {l : sym}
      {pes : List (generic_pexpr Unit sym)}
      (hpes : ∀ pe ∈ pes, PePure pe)
      (hdep : ∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel) :
      Frag (runRedex an ra l pes)
  | sseq_spec {an pa pb : List _root_.annot} {x : sym} {bty : core_base_type}
      {e1 e2 : CoreExpr} :
      Frag e1 → Frag e2 →
      Frag (Expr an (Esseq (specPat pa pb x bty) e1 e2))
  | pure_sym {an pb : List _root_.annot} {x : sym} :
      Frag (pureRedex an (Pexpr pb () (PEsym x)))
  | load_op {an : List _root_.annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {ty : ctype} {pe2 : generic_pexpr Unit sym} {mo : memory_order}
      (hnv2 : valueFromPexpr pe2 = none) (hp2 : PePure pe2)
      (hd2 : peDepth pe2 ≤ lemDefaultFuel) :
      Frag (loadOpRedex an loc ann ty pe2 mo)
  /-- Strong sequencing at the plain-symbol binder, ANY fragment head
      (E1: both LETS betas at this binder are mirrored —
      `Step.sseq_sym_pure`, `Step.sseq_sym_annot`). -/
  | sseq_sym {an pa : List _root_.annot} {x : sym} {bty : core_base_type}
      {e1 e2 : CoreExpr} :
      Frag e1 → Frag e2 →
      Frag (Expr an (Esseq (symPat pa x bty) e1 e2))
  | memop_vals {an : List _root_.annot} (v1 v2 : value) :
      Frag (memopPtrEqVals an v1 v2)
  | memop_op {an : List _root_.annot} {pe1 pe2 : generic_pexpr Unit sym}
      (hnv : valueFromPexprs [pe1, pe2] = none)
      (hp1 : PePure pe1) (hp2 : PePure pe2)
      (hd1 : peDepth pe1 ≤ lemDefaultFuel)
      (hd2 : peDepth pe2 ≤ lemDefaultFuel) :
      Frag (memopRedex an PtrEq [pe1, pe2])
  | store_op {an : List _root_.annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {ty : ctype} {pe2 pe3 : generic_pexpr Unit sym} {mo : memory_order}
      (hnv : valueFromPexprs [pe2, pe3] = none)
      (hp2 : PePure pe2) (hp3 : PePure pe3)
      (hd2 : peDepth pe2 ≤ lemDefaultFuel)
      (hd3 : peDepth pe3 ≤ lemDefaultFuel) :
      Frag (storeOpRedex an loc ann ty pe2 pe3 mo)
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
  | case_value {an b : List _root_.annot} {cval : value}
      {pats : List (pattern × CoreExpr)}
      (hbr : ∀ e', select_case subst_sym_expr cval pats = some e' → Frag e')
      (hbsz : ∀ e', select_case subst_sym_expr cval pats = some e' →
        esize e' ≤ esize (caseRedex an (Pexpr b () (PEval cval)) pats)) :
      Frag (caseRedex an (Pexpr b () (PEval cval)) pats)
  /-- Weak sequencing at the wildcard pattern (the `sseq` clone). -/
  | wseq {an pa : List _root_.annot} {bty : core_base_type} {e1 e2 : CoreExpr} :
      Frag e1 → Frag e2 →
      Frag (Expr an (Ewseq (Pattern pa (CaseBase (none, bty))) e1 e2))
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
  | call {an : List _root_.annot} {ra : core_run_annotation} {f : sym} {pes : List (generic_pexpr Unit sym)}
      (hpes : ∀ pe ∈ pes, PePure pe)
      (hdep : ∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel) :
      Frag (callRedex an ra f pes)

theorem frag_ofValA (w : SpikeValA) : Frag (ofValA w) := by
  cases w with
  | pure a b v => exact .val_pure v
  | annot a a2 b ds v => exact .annot (.val_pure v)

theorem frag_ofVal (w : SpikeVal) : Frag (ofVal w) := frag_ofValA w.canon

/-- Configuration-tuple injectivity (the four components). -/
theorem Config.mk_inj {e e' : CoreExpr} {ρ ρ' : EnvStack} {ctl ctl' : Ctl} {σ σ' : Mem}
    (h : ((e, ρ, ctl, σ) : Config) = (e', ρ', ctl', σ')) :
    e = e' ∧ ρ = ρ' ∧ ctl = ctl' ∧ σ = σ' := by
  simpa [Prod.mk.injEq] using h

/-! matcher facts for the annotation frame (the fuelled matchers examine
the body's head constructor; a non-value premise dismisses the value
arms — `is_irreducible`, Core_reduction.lean:293; get_ctx's Eannot arms,
Core_reduction.lean:375) -/

/-- `{ds} b` is reducible whenever `b` is not a value. -/
theorem is_irreducible_annot_of_nv {a : List _root_.annot} {ds : List dyn_annotation}
    {b : CoreExpr} (hnv : toVal b = none) :
    is_irreducible (Expr a (Eannot ds b)) = false := by
  rcases b with ⟨a', b_⟩
  cases b_ <;> try rfl
  · rename_i pe
    rcases pe with ⟨pb, u, pe_⟩
    cases u
    cases pe_ <;> first | rfl | (simp [toVal] at hnv)
  · rename_i ds' c
    rcases c with ⟨a'', c_⟩
    cases c_ <;> try rfl
    rename_i pe
    rcases pe with ⟨pb, u, pe_⟩
    cases u
    cases pe_ <;> rfl

/-- get_ctx descends through `{ds} b` at a non-value, non-annotation-
    rooted body (the `Eannot xs e` arm, after the `Eannot _ (Expr _
    (Eannot _ e))` merge root is dismissed). -/
theorem get_ctx_annot_map {a : List _root_.annot} {ds : List dyn_annotation}
    {b : CoreExpr} (hnv : toVal b = none) (hroot : annotRooted b = false) (n : Nat) :
    get_ctx_lemFuel (n+1) (Expr a (Eannot ds b)) =
      List.map (fun p => (Cannot a ds p.1, p.2)) (get_ctx_lemFuel n b) := by
  rcases b with ⟨a', b_⟩
  cases b_ <;> try rfl
  · rename_i pe
    rcases pe with ⟨pb, u, pe_⟩
    cases u
    cases pe_ <;> first | rfl | (simp [toVal] at hnv)
  · simp [annotRooted] at hroot

/-- An annotation-rooted term is an annotation node. -/
theorem annotRooted_true {b : CoreExpr} (h : annotRooted b = true) :
    ∃ (a2 : List _root_.annot) (ds2 : List dyn_annotation) (c : CoreExpr),
      b = Expr a2 (Eannot ds2 c) := by
  rcases b with ⟨a', b_⟩
  cases b_ <;> first | exact ⟨_, _, _, rfl⟩ | (simp [annotRooted] at h)

/-- Every non-value Frag configuration decomposes (extended
    roots). -/
theorem Frag.decomp {e : CoreExpr} (hf : Frag e) (hnv : toVal e = none) :
    ∃ ctx r, Decomp e ctx r ∧ Frag r := by
  induction hf with
  | val_pure v => simp [toVal] at hnv
  | store => exact ⟨_, _, Decomp.root (.store), .store⟩
  | load => exact ⟨_, _, Decomp.root (.load), .load⟩
  | create => exact ⟨_, _, Decomp.root (.create), .create⟩
  | create_op hnvC hp1 hp2 hd1 hd2 =>
    exact ⟨_, _, Decomp.root (.create_op _ _ _ hnvC), .create_op hnvC hp1 hp2 hd1 hd2⟩
  | kill => exact ⟨_, _, Decomp.root (.kill), .kill⟩
  | kill_op hnvK hpK hdK =>
    exact ⟨_, _, Decomp.root (.kill_op _ _ _ hnvK), .kill_op hnvK hpK hdK⟩
  | alloc => exact ⟨_, _, Decomp.root (.alloc), .alloc⟩
  | alloc_op hnvA hp1 hp2 hd1 hd2 =>
    exact ⟨_, _, Decomp.root (.alloc_op _ _ _ hnvA), .alloc_op hnvA hp1 hp2 hd1 hd2⟩
  | call hpes hdep => exact ⟨_, _, Decomp.root (.call _ _ _), .call hpes hdep⟩
  | @sseq an pa bty e1 e2 hf1 hf2 ih1 ih2 =>
    cases hv1 : toVal e1 with
    | some w =>
      obtain ⟨wa, -, rfl⟩ := ofValA_of_toVal hv1
      cases wa with
      | pure a1 b1 v => exact ⟨_, _, Decomp.root (.beta_pure), .sseq (frag_ofValA _) hf2⟩
      | annot a1 a2 b1 ds v =>
        exact ⟨_, _, Decomp.root (.beta_annot), .sseq (frag_ofValA _) hf2⟩
    | none =>
      obtain ⟨ctx, r, hd, hfr⟩ := ih1 hv1
      exact ⟨_, _, Decomp.sseq hd, hfr⟩
  | @wseq an pa bty e1 e2 hf1 hf2 ih1 ih2 =>
    cases hv1 : toVal e1 with
    | some w =>
      obtain ⟨wa, -, rfl⟩ := ofValA_of_toVal hv1
      cases wa with
      | pure a1 b1 v => exact ⟨_, _, Decomp.root (.wbeta_pure), .wseq (frag_ofValA _) hf2⟩
      | annot a1 a2 b1 ds v =>
        exact ⟨_, _, Decomp.root (.wbeta_annot), .wseq (frag_ofValA _) hf2⟩
    | none =>
      obtain ⟨ctx, r, hd, hfr⟩ := ih1 hv1
      exact ⟨_, _, Decomp.wseq hd, hfr⟩
  | @annot an ds b hfb ihb =>
    by_cases hr : annotRooted b = true
    · obtain ⟨a2, ds2, c, rfl⟩ := annotRooted_true hr
      exact ⟨_, _, Decomp.root (.merge (is_irreducible_merge c)), .annot hfb⟩
    · have hr' : annotRooted b = false := by simpa using hr
      cases hvb : toVal b with
      | some w =>
        obtain ⟨wa, -, rfl⟩ := ofValA_of_toVal hvb
        cases wa with
        | pure a1 b1 v => simp [toVal, ofValA] at hnv
        | annot a1 a2 b1 ds2 v => simp [annotRooted, ofValA] at hr'
      | none =>
        obtain ⟨ctx, r, hd, hfr⟩ := ihb hvb
        exact ⟨_, _, Decomp.annot hr' (is_irreducible_annot_of_nv hvb)
          (get_ctx_annot_map hvb hr') hd, hfr⟩
  | @bound an b hfb ihb =>
    cases hvb : toVal b with
    | some w =>
      obtain ⟨wa, -, rfl⟩ := ofValA_of_toVal hvb
      cases wa with
      | pure a1 b1 v => exact ⟨_, _, Decomp.root (.bound_pure), .bound (frag_ofValA _)⟩
      | annot a1 a2 b1 ds v => exact ⟨_, _, Decomp.root (.bound_annot), .bound (frag_ofValA _)⟩
    | none =>
      obtain ⟨ctx, r, hd, hfr⟩ := ihb hvb
      exact ⟨_, _, Decomp.bound hd, hfr⟩
  | save hp hd hb ih => exact ⟨_, _, Decomp.root (.save _ _ _), .save hp hd hb⟩
  | if_ hpg hdg hf2 hf3 ih2 ih3 =>
    exact ⟨_, _, Decomp.root (.if_ _ _ _), .if_ hpg hdg hf2 hf3⟩
  | run hpes hdep => exact ⟨_, _, Decomp.root (.run _ _ _), .run hpes hdep⟩
  | @sseq_spec an pa pb x bty e1 e2 hf1 hf2 ih1 ih2 =>
    cases hv1 : toVal e1 with
    | some w =>
      obtain ⟨wa, -, rfl⟩ := ofValA_of_toVal hv1
      exact ⟨_, _, Decomp.root .beta_spec, .sseq_spec (frag_ofValA wa) hf2⟩
    | none =>
      obtain ⟨ctx, r, hd, hfr⟩ := ih1 hv1
      exact ⟨_, _, Decomp.sseq_spec hd, hfr⟩
  | pure_sym =>
    exact ⟨_, _, Decomp.root (.pure_e rfl), .pure_sym⟩
  | load_op hnv2 hp2 hd2 =>
    exact ⟨_, _, Decomp.root (.load_op _ _ _ _ hnv2),
      .load_op hnv2 hp2 hd2⟩
  | @sseq_sym an pa x bty e1 e2 hf1 hf2 ih1 ih2 =>
    cases hv1 : toVal e1 with
    | some w =>
      obtain ⟨wa, -, rfl⟩ := ofValA_of_toVal hv1
      exact ⟨_, _, Decomp.root .beta_sym, .sseq_sym (frag_ofValA wa) hf2⟩
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

/-! ## The value protocol: certified at the SHIPPED round

The discharge-device readings of the value protocol (`outcomesU_done`,
`outcomesU_remove_annot`) and the unified step-match `outcomesU_of_step`
over `outcomesU` were DELETED on 2026-09-04 (hygiene slice H1a,
docs/2026-09-04_h1-notes.md; KNOWN-OPEN-ITEMS C3): consumerless since the
fuel-lane restatement of 2026-09-03 — the value protocol is certified at
the shipped round (`shipped_done`, Round.lean) and both adequacy lanes
iterate the shipped round `loop_step_frag` (DriverCollapse.lean). The
per-action discharge computations `stepDischarge_*` (below) and the
discharge device `dischargeStep`/`outcomesU` itself stay: Round.lean's
discharge-device readings consume the device. -/

/-- The extended cone is closed under Step, GIVEN the label map's
    own cone membership (`hQf` — the registered continuations are
    fragment terms; the side hypothesis breaks the circularity a
    Q-indexed cone would have). E1: the successor control is whatever
    the step produces (`Ctl.upd` at every leaf); the premise `hκ`
    (the call stack is kept) excludes the CALL and RETURN rounds,
    whose successors leave the expression's own cone. -/
theorem Frag.step {M : MachineCtx} {ctl : Ctl}
    (hQf : ∀ l params cont, lookupLabel (M.labelsAt ctl.proc) l = some (params, cont) →
      Frag cont)
    {e : CoreExpr} {ρ : EnvStack} {σ : Mem}
    {e' : CoreExpr} {ρ' : EnvStack} {ctl' : Ctl} {σ' : Mem}
    (hf : Frag e) (hs : Step M (e, ρ, ctl, σ) (e', ρ', ctl', σ'))
    (hκ : ctl'.κ = ctl.κ) : Frag e' := by
  induction hf generalizing e' ρ' ctl' σ' with
  | call hpes hdep => exact (Step.call_ne_same_κ (callRedex?_callRedex _ _ _ _) hs hκ).elim
  | val_pure v => exact (Step.pure_val_elim hs hκ).elim
  | store =>
    obtain ⟨mv, fp, σ'', hmv, hmem, hout⟩ := hs.store_inv
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    exact .annot (.val_pure Vunit)
  | load =>
    obtain ⟨fp, mval, σ'', hmem, hout⟩ := hs.load_inv
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    exact .annot (.val_pure _)
  | create =>
    obtain ⟨pv, σ'', hmem, hout⟩ := hs.create_inv
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    exact .val_pure _
  | create_op hnvC hp1 hp2 hd1 hd2 =>
    obtain ⟨al, ty, -, -, hout⟩ := hs.create_op_inv hnvC
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    exact .create
  | kill =>
    obtain ⟨σ'', hmem, hout⟩ := hs.kill_inv
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    exact .val_pure _
  | kill_op hnvK hpK hdK =>
    obtain ⟨pv, -, hout⟩ := hs.kill_op_inv hnvK
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    exact .kill
  | alloc =>
    obtain ⟨pv, σ'', hmem, hout⟩ := hs.alloc_inv
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    exact .val_pure _
  | alloc_op hnvA hp1 hp2 hd1 hd2 =>
    obtain ⟨al, sz, -, -, hout⟩ := hs.alloc_op_inv hnvA
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    exact .alloc
  | sseq hf1 hf2 ih1 ih2 =>
    rcases hs.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
        ⟨_, _, _, _, v, _, _, _, _, _, hout⟩ | ⟨_, _, _, _, _, ds', v, _, _, _, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
        hcall
    · obtain ⟨h1, -, h3, -⟩ := Config.mk_inj hout
      subst h1 h3
      exact .sseq (ih1 hstep hκ) hf2
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      exact hf2
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      exact .annot hf2
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      rw [h1]
      exact hQf l params cont hl
    · exact (specPat_ne_base hpat).elim
    · exact (specPat_ne_base hpat).elim
    · exact (symPat_ne_base hpat).elim
    · exact (symPat_ne_base hpat).elim
    · exact (tuplePat_ne_base hpatT1).elim
    · exact (tuplePat_ne_base hpatT2).elim
    · exact (hcall.ne_same_κ hκ).elim
  | wseq hf1 hf2 ih1 ih2 =>
    rcases hs.wseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
        ⟨_, _, _, _, v, _, _, _, _, _, hout⟩ | ⟨_, _, _, _, _, ds', v, _, _, _, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpatS1, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, hpatS2, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
        hcall
    · obtain ⟨h1, -, h3, -⟩ := Config.mk_inj hout
      subst h1 h3
      exact .wseq (ih1 hstep hκ) hf2
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      exact hf2
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      exact .annot hf2
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      rw [h1]
      exact hQf l params cont hl
    · exact (symPat_ne_base hpatS1).elim
    · exact (symPat_ne_base hpatS2).elim
    · exact (tuplePat_ne_base hpatT1).elim
    · exact (tuplePat_ne_base hpatT2).elim
    · exact (hcall.ne_same_κ hκ).elim
  | annot hfb ihb =>
    rcases hs.annot_inv with ⟨hg, hnj, hnc', hnv', b', ρ'', ctl'', σ'', hstep, hout⟩ |
        ⟨a2, ds2, c, hb, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hg, hj, _, hl, _, hout⟩ |
        ⟨-, hcall⟩ | ⟨a2, b1, v, pc', κ', hb', -, hout'⟩
    · obtain ⟨h1, -, h3, -⟩ := Config.mk_inj hout
      subst h1 h3
      exact .annot (ihb hstep hκ)
    · subst hb
      obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      cases hfb with
      | annot hfc => exact .annot hfc
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      rw [h1]
      exact hQf l params cont hl
    · exact (hcall.ne_same_κ hκ).elim
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout'
      subst h1
      exact .val_pure _
  | bound hfb ihb =>
    rcases hs.bound_inv with ⟨b', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
        ⟨a1, b1, v, hb, hout⟩ | ⟨a1, a2, b1, ds, v, hb, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        hcall
    · obtain ⟨h1, -, h3, -⟩ := Config.mk_inj hout
      subst h1 h3
      exact .bound (ihb hstep hκ)
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      exact .val_pure _
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      exact .val_pure _
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      rw [h1]
      exact hQf l params cont hl
    · exact (hcall.ne_same_κ hκ).elim
  | @save an sb ps body hp hd hb ih =>
    rcases hs.save_inv with ⟨cvals, ev0', evs', hρeq, hvals, hout⟩ |
        ⟨cvals, hnv, hvals, hout⟩
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      exact hb
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      exact .save (saveParamsWithValues_pure ps cvals)
        (saveParamsWithValues_depth ps cvals (evalPexprs_length _ _ _ hvals)) hb
  | if_ hpg hdg hf2 hf3 ih2 ih3 =>
    rcases hs.if_inv with ⟨-, hout⟩ | ⟨-, hout⟩ <;>
      obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    · subst h1; exact hf2
    · subst h1; exact hf3
  | run hpes hdep =>
    obtain ⟨params, cont, vs, ev0', evs', hρeq, hl, hvs, hout⟩ :=
      hs.jump_inv (by rfl)
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    rw [h1]
    exact hQf _ params cont hl
  | sseq_spec hf1 hf2 ih1 ih2 =>
    rcases hs.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
        ⟨_, _, _, _, v, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, ds', v, _, _, hpat, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
        hcall
    · obtain ⟨h1, -, h3, -⟩ := Config.mk_inj hout
      subst h1 h3
      exact .sseq_spec (ih1 hstep hκ) hf2
    · exact (specPat_ne_base hpat.symm).elim
    · exact (specPat_ne_base hpat.symm).elim
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      rw [h1]
      exact hQf l params cont hl
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      exact hf2
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      exact .annot hf2
    · exact (symPat_ne_spec hpat).elim
    · exact (symPat_ne_spec hpat).elim
    · exact (specPat_ne_tuple hpatT1).elim
    · exact (specPat_ne_tuple hpatT2).elim
    · exact (hcall.ne_same_κ hκ).elim
  | sseq_sym hf1 hf2 ih1 ih2 =>
    rcases hs.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
        ⟨_, _, _, _, v, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, ds', v, _, _, hpat, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
        hcall
    · obtain ⟨h1, -, h3, -⟩ := Config.mk_inj hout
      subst h1 h3
      exact .sseq_sym (ih1 hstep hκ) hf2
    · exact (symPat_ne_base hpat.symm).elim
    · exact (symPat_ne_base hpat.symm).elim
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      rw [h1]
      exact hQf l params cont hl
    · exact (symPat_ne_spec hpat.symm).elim
    · exact (symPat_ne_spec hpat.symm).elim
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      exact hf2
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      exact .annot hf2
    · exact (symPat_ne_tuple hpatT1).elim
    · exact (symPat_ne_tuple hpatT2).elim
    · exact (hcall.ne_same_κ hκ).elim
  | memop_vals v1 v2 =>
    obtain ⟨pv1, pv2, b, σ'', -, -, -, hout⟩ := hs.memop_vals_inv
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    exact .val_pure _
  | memop_op hnv hp1 hp2 hpd1 hpd2 =>
    obtain ⟨v1, v2, hv1, hv2, hout⟩ := hs.memop_op_inv hnv
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    exact .memop_vals v1 v2
  | store_op hnv hp2 hp3 hpd2 hpd3 =>
    obtain ⟨pv, cv, hv2', hv3', hout⟩ := hs.store_op_inv hnv
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    exact .store
  | pure_sym =>
    obtain ⟨v, -, -, hout⟩ := hs.pure_inv rfl
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    exact .val_pure v
  | load_op hnv2 hp2 hd2 =>
    obtain ⟨pv, -, hout⟩ := hs.load_op_inv hnv2
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    exact .load
  | case_value hbr hbsz =>
    obtain ⟨e'', hsel, hout⟩ := hs.case_value_inv (valueFromPexpr_val _ _)
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    exact hbr e' hsel

/-! `Frag.esize_step_bound` (the additive step-growth bound) was DELETED
    in E1: consumerless since the potential lane (Potential.lean) took
    over the fuel accounting. -/

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
  | step {e' : CoreExpr} {ρ' : EnvStack} {ctl' : Ctl} {σ' : Mem} :
      Step M (e, ρ, ctl, σ) (e', ρ', ctl', σ') →
      EngineMatchU M e ρ ctl σ (.next (M.thread e' ρ' ctl') σ')
  | removeAnnot {a a2 b : List _root_.annot} {ds : List dyn_annotation} {v : value} :
      e = ofValA (.annot a a2 b ds v) →
      EngineMatchU M e ρ ctl σ (.next (M.thread (ofValA (.pure a2 b v)) ρ ctl) σ)
  | done {a b : List _root_.annot} {v : value} :
      e = ofValA (.pure a b v) → EngineMatchU M e ρ ctl σ (.done v)
  | refused {o : EngineOutcome} : o.isRefusal →
      (∀ out, ¬ Step M (e, ρ, ctl, σ) out) → toVal e = none →
      EngineMatchU M e ρ ctl σ o

/-- STORE IS TWO-SIDED at any context: the engine's behavior at a
    store redex is a singleton, and it is a mirror step exactly when
    the mirror can step (encoding + active memM); the ILLTYPED and
    killed channels arise only where the mirror is provably stuck. -/
theorem engine_complete_storeU {an : List _root_.annot} (M : MachineCtx) (aid : Nat)
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
    {ty : ctype} {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
    (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    ∃ o, outcomesU M aid (storeRedex an loc ann lk ty pv cv mo) ρ ctl σ = [o] ∧
      EngineMatchU M (storeRedex an loc ann lk ty pv cv mo) ρ ctl σ o := by
  have hsz : esize (storeRedex an loc ann lk ty pv cv mo) ≤ lemDefaultFuel := by
    rw [show esize (storeRedex an loc ann lk ty pv cv mo) = 1 from rfl]
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
      rw [dischargeStep_store_active hmem, MachineCtx.thread_upd_arena]
      rfl
    | none =>
      refine ⟨dischargeStep M.tagDefs aid M.runState σ (Step_action_request2
          "StoreRequest" (requestLoc (locUpdTh an (M.thread (storeRedex an loc ann lk ty pv cv mo) ρ ctl)) loc) M.tid
          (is_unseq_with_ccall CTX)
          (stExceptUndef_return (StoreRequest2 mo ty lk pv mv (fun _ fp =>
            { locUpdTh an (M.thread (storeRedex an loc ann lk ty pv cv mo) ρ ctl) with
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
theorem step_ctx_case_illtyped {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {a : List _root_.annot} {cval : value} {pats : List (pattern × CoreExpr)}
    (hd : Decomp e ctx (caseRedex an (Pexpr a () (PEval cval)) pats))
    (hsz : esize e ≤ lemDefaultFuel)
    (hsel : select_case subst_sym_expr cval pats = none)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e) :
    step_ctx tds σ file ext tid (parent, th) =
      [Step_error2 (String.append "Ecase, mismatched ==> "
        (CerbPP.stringFromCore_expr
          (caseRedex an (Pexpr a () (PEval cval)) pats)))] := by
  have hget : get_ctx th.arena =
      [(ctx, caseRedex an (Pexpr a () (PEval cval)) pats)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold caseRedex
  cases ctx <;>
    (dsimp only [one_step0]
     rw [show is_irreducible (Expr an
       (Ecase (Pexpr a () (PEval cval)) pats)) = false from rfl]
     dsimp only [valueFromPexpr]
     rw [hsel]
     rfl)

/-- CASE (value scrutinee) IS TWO-SIDED at any context: TAU into the
    selected branch when a branch matches (= exactly when the mirror
    steps), the ILLTYPED refusal when none does (mirror provably
    stuck). The F-01 RED row's engine-facing pair. -/
theorem engine_complete_caseU {an : List _root_.annot} (M : MachineCtx) (aid : Nat)
    {b : List _root_.annot} {cval : value} {pats : List (pattern × CoreExpr)}
    (hsz : esize (caseRedex an (Pexpr b () (PEval cval)) pats)
      ≤ lemDefaultFuel)
    (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    ∃ o, outcomesU M aid (caseRedex an (Pexpr b () (PEval cval)) pats) ρ ctl σ = [o] ∧
      EngineMatchU M (caseRedex an (Pexpr b () (PEval cval)) pats) ρ ctl σ o := by
  cases hsel : select_case subst_sym_expr cval pats with
  | some e' =>
    refine ⟨_, ?_, .step (Step.case_value (valueFromPexpr_val _ _) hsel)⟩
    unfold outcomesU engineStepsU caseRedex
    rw [step_ctx_case_value (Decomp.root (Redex.case_ _ _)) hsz hsel
      M.tagDefs σ M.file M.extern M.tid M.parent (M.thread _ ρ ctl) rfl, MachineCtx.thread_upd_arena]
    rfl
  | none =>
    refine ⟨.error (String.append "Ecase, mismatched ==> "
        (CerbPP.stringFromCore_expr
          (caseRedex an (Pexpr b () (PEval cval)) pats))), ?_, ?_⟩
    · unfold outcomesU engineStepsU caseRedex
      rw [step_ctx_case_illtyped (Decomp.root (Redex.case_ _ _)) hsz hsel
        M.tagDefs σ M.file M.extern M.tid M.parent (M.thread _ ρ ctl) rfl]
      rfl
    · refine .refused trivial (fun out hstep => ?_) rfl
      obtain ⟨e'', hsel', -⟩ := hstep.case_value_inv (valueFromPexpr_val _ _)
      rw [hsel] at hsel'
      cases hsel'

end CerberusHeapLang
